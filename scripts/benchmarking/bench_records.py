#!/usr/bin/env python3
"""The benchmark report entrypoint: migrate the history, render it and check it.

`migrate`, `report` and `check` are this file's commands. `render` is the one
pure function that turns stored measurements into `docs/performance.md`, and
`check` is the standalone gate `doccheck` runs over those exact bytes.

The store is `benchmarking.records`, the artifact adapters and their import
transactions are `benchmarking.legacy`, and the keyed TLC baseline cache is
`benchmarking.baselines`. This module is the entrypoint over them (HARNESS-03),
and re-exports the library names that callers outside it still import from here.
The `migrate` *command* is `migrate_command`: the library's `migrate` is one
step of it and stays a library entry, because a caller that drives the
transaction on a root of its own (a fixture) is not the command.
"""

if __package__ in (None, ""):
    import sys
    from pathlib import Path
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

import argparse
import hashlib
import json
from pathlib import Path
import statistics

from benchmarking import machine as bench_machine, models as bench_models

# The store, its adapters and the keyed baseline cache are the library modules
# under `benchmarking/`. `cached_tlc`, `content_digest` and `ingest` are also
# re-exported through this module: the disk/liveness/profile/ttfr lanes and
# `test_storage` still import them from the entrypoint. The library is
# authoritative for each of them.
from benchmarking.baselines import cached_tlc, content_digest, historical_match
from benchmarking.legacy import (LEGACY_MARKDOWN, ingest, json_sources, measurement_rows, migrate, missing_input,
                                 source_bytes, source_measurements)
from benchmarking.records import (COMPLETE, KEY_IDENTITY, METRICS, ROOT, VERSION, ArchiveError, digest, dump,
                                  evidence, exit_ok, load_records, measurement_key, normalize, peak_rss, record_path,
                                  store_stem, validate)


def loose_key(r):
    """A row's key without the input digest: the dimensions that decide which
    measurement a row is, for a reader that has to recognise a row whose digest
    migration completed by adopting the current model bytes."""
    k = measurement_key(r)
    return json.dumps({d: k[d] for d in KEY_IDENTITY[r['tool']] if d != 'content_digest'},
                      sort_keys=True, default=str)
from harness.git import run as run_git


SECTIONS = ('Summary', 'Default mode end-to-end vs TLC (whole corpus)', 'Compiled tier per model',
            'External industrial models', 'Liveness', 'Trace validation', 'Multi-core scaling',
            'Beyond memory (-maxmem / cgroup)', 'Interpreter (-interp vs TLC 1w)', 'Coverage and gaps')


def store_file(r):
    """The store file a row lives in, as text, relative to the report.

    The current store ships with the sources. Each link resolves from the
    report's directory to the canonical record for this measurement key.
    """
    return f"[record](../{record_path(r)})"


def ref(r, label=None):
    """A record as the report names it: its provenance and its store file."""
    label = label or f"{r['revision'] or 'unknown revision'}; {r['instance']['type'] or 'unknown instance'}; {r['date'] or 'unknown date'}"
    return f"{label} ({store_file(r)})"


def number(value, suffix=''):
    return '—' if value is None else f'{value:.2f}{suffix}'


def rss_ratio(r, tc):
    """TLC / tlx peak-RSS ratio of a matched pair, or None when either is unknown.

    Both sides are read with the store's own `peak_rss`, so the report, the
    import and `history-report` name the same statistic: the median of the
    finite positive peak-RSS samples. TLC's footprint is often larger than
    tlx's, so a value above one means tlx used less memory.
    """
    if not tc:
        return None
    tlx_rss, tlc_rss = peak_rss(r['metrics']), peak_rss(tc['metrics'])
    return tlc_rss / tlx_rss if tlx_rss and tlc_rss else None


def optimizations(r):
    """The optimizations the row's own samples name, in record order.

    A run that reduced its search says so in its `Optimizations:` line
    (docs/usage.md section 6.3), and the samples carry that line; a reduced
    row's ratio compares a reduced search with TLC's unreduced one, so the
    report has to label it. The label is that statement and nothing else: a
    count difference is not a substitute, because the default-mode contract
    permits one for reasons the record does not state (docs/compat.md section
    0), and a row that names no optimization is never marked for it.
    """
    raw = r.get('raw_result') or {}
    named = []
    for sample in [*(raw.get('samples') or []), *(raw.get('warmups') or [])]:
        for name in sample.get('optimizations') or []:
            if name not in named:
                named.append(name)
    return tuple(named)


def reduction_note(r):
    """One row's `tlx optimizations` cell: what the record states, or why not.

    `none` requires every recorded sample to state its optimization list and
    name nothing. A sample without the key leaves the cell `unknown`: the
    record does not say what that run used, and the older compatible samples
    have exactly that shape, so absence must not read as "no optimization".
    """
    named = optimizations(r)
    if named:
        return '; '.join(named)
    raw = r.get('raw_result') or {}
    samples = [*(raw.get('samples') or []), *(raw.get('warmups') or [])]
    return 'none' if samples and all('optimizations' in s for s in samples) else 'unknown'


def eligible(r):
    if r['provenance'].get('count_problems'):
        return False
    if 'diagnostic' in r.get('category', []):
        return False
    c = r.get('configuration', {})
    repetitions = r['provenance'].get('repetitions')
    if repetitions and repetitions['completed'] < repetitions['requested']:
        return False
    sample_results = r['provenance'].get('sample_results')
    if sample_results and any(not exit_ok(e.get('result'), e.get('exit')) for e in sample_results):
        return False
    return (r.get('tool') != 'tlc' and r['revision'] and r['counts']['result'] in COMPLETE
            and r['metrics']['wall_s'] and not c.get('hogs')
            and c.get('variant') in (None, '', 'new', 'after', 'fix')
            and not any((c.get('env') or {}).values()))


def scaling_identity(r):
    args = r['configuration'].get('args', [])
    stripped, i = [], 0
    while i < len(args):
        if args[i] == '-workers':
            i += 2
        else:
            stripped.append(args[i])
            i += 1
    return (r['model'], r['revision'], r['instance']['type'], r['instance']['arch'], r['mode'],
            r['provenance']['source'], tuple(stripped), r['configuration'].get('cgroup_mib'))


def render(records, suite, *, stale_after=20, ages=None, baseline_inputs=None, report_note=None):
    """Pure deterministic rendering. Git ages are recorded in report-policy.json."""
    records = sorted(records, key=lambda r: (r['date'] or '', r['id']))
    by_id = {r['id']: r for r in records}
    # Latest per model/mode/workers/machine/category/config; never pool machines.
    latest = {}
    for r in records:
        if eligible(r):
            key = (r['model'], r['mode'], r['workers'], r['instance']['type'], r['instance']['arch'],
                   tuple(r['category']), tuple(r['configuration'].get('args', [])), r['configuration'].get('cgroup_mib'))
            latest[key] = r
    rows = sorted(latest.values(), key=lambda r: (r['model'], r['mode'], r['workers'], r['instance']['type'] or '', r['id']))
    def baseline(r):
        tc = by_id.get(r.get('baseline'))
        return tc if tc and historical_match(r, tc) else None
    def ratio(r):
        tc = baseline(r)
        return tc['metrics']['wall_s'] / r['metrics']['wall_s'] if tc else None
    out = ['# Performance', '',
           'Generated by `python3 scripts/bench.py report` from the current canonical measurement store in this repository. Do not edit numbers by hand.', '',
           'Times are median process wall/CPU seconds; RSS is MiB. Ratios use the same model, instance, architecture, worker count, '
           'verdict (also distinct count outside default mode). The memory ratios pair the TLC baseline\'s peak RSS with the tlx run\'s, '
           'so a value above one means tlx used less peak memory; a missing or zero measurement stays unknown (`—`) rather than being '
           'read as a zero-byte footprint. Historical matches without a content digest are provisional; they cannot satisfy the current baseline cache. '
           'Unknown metadata stays unknown. Diagnostic samples, loaded or experimental A/B variants are excluded from headlines. '
           'Each number is named by the record it came from: the Evidence column carries that record\'s revision, instance, date and '
           'store file. The current measurement store ships with the sources ([benchmarking.md](benchmarking.md) section 6); '
           'the record links can be inspected in a fresh clone.',
           'A tlx time is the median of the timed samples, and each timed sample is a separate process run that follows a discarded '
           'warm-up. The native library a timed run uses may already be in the cache the warm-up filled, and that cache is shared '
           'by the configurations of one batch instead of being isolated per configuration, so the discarded run is not a '
           'cold-cache measurement ([benchmarking.md](benchmarking.md) section 1 owns the protocol); a cold-cache number needs the '
           'fresh-cache conditions the `ttfr` lane states. A TLC time is its one process, including its own start-up.',
           'A row whose record names optimizations (`tlx optimizations` below: the run\'s own `Optimizations:` line, '
           '[usage.md](usage.md) section 6.3) ran with them, so the counts are those of that reduced search. The column states '
           'what the record says about the tlx run; it does not claim the TLC baseline was unreduced, and the default-mode '
           'contract does not make a count difference a substitute for the record\'s own line ([compat.md](compat.md) section 0). '
           '`none` means every recorded sample states its optimization list and names none; `unknown` means the record does not '
           'state it for every sample.',
           'See [benchmark inputs and evidence](../bench/README.md) for verification and reproduction. '
           'Superseded measurements and backup archives are kept outside the published tree.', '']
    if report_note:
        if not isinstance(report_note, str):
            raise ValueError('report_note must be a string')
        out += [report_note, '']
    for section in SECTIONS:
        out += ['## ' + section, '']
        if section == 'Summary':
            out += ['| Category / instance / mode / workers | Models | Median TLC / tlx | Range | Median TLC / tlx RSS | RSS range | Models with recorded optimizations | Evidence |',
                    '|---|---:|---:|---:|---:|---:|---:|---|']
            groups = {}
            for r in rows:
                if ratio(r) is not None:
                    for c in r['category']:
                        if 'beyond-memory' in r['category'] and c != 'beyond-memory':
                            continue
                        group = groups.setdefault((c, r['instance']['type'], r['mode'], r['workers']), {})
                        if r['model'] not in group or (r['date'] or '') > (group[r['model']]['date'] or ''):
                            group[r['model']] = r
            for key, models in sorted(groups.items()):
                rs = list(models.values())
                vals = [ratio(r) for r in rs]
                rss_vals = [x for x in (rss_ratio(r, baseline(r)) for r in rs) if x is not None]
                rss_median = f'{statistics.median(rss_vals):.2f}×' if rss_vals else '—'
                rss_range = f'{min(rss_vals):.2f}–{max(rss_vals):.2f}×' if rss_vals else '—'
                reduced = sum(1 for r in rs if optimizations(r))
                refs = ', '.join(ref(r, r['model']) + ' / ' + ref(baseline(r), 'TLC') for r in rs)
                out.append(f"| {' / '.join(map(str, key))} | {len(rs)} | {statistics.median(vals):.2f}× | "
                           f"{min(vals):.2f}–{max(vals):.2f}× | {rss_median} | {rss_range} | {reduced} | {refs} |")
            if not groups:
                out += ['No eligible records with a matching TLC baseline.']
        elif section == 'Coverage and gaps':
            out += [f"Stale threshold: {stale_after} revisions, relative to the pinned report reference in `bench/report-policy.json`. "
                    'Unknown/unreachable revisions are not recent. Baselines expire only when a key changes, never because time passes.', '',
                    '| Model | Measurement coverage | TLC baseline coverage | Evidence |', '|---|---|---|---|']
            mids = sorted({m['id'] for m in suite.get('models', [])} | {r['model'] for r in records})
            for mid in mids:
                rr = [r for r in rows if r['model'] == mid]
                tc = [r for r in records if r['model'] == mid and r.get('tool') == 'tlc']
                recent = [r for r in rr if ages is not None and ages.get(r['revision']) is not None and ages[r['revision']] <= stale_after]
                missing = sorted({'default', '-compile', '-interp'} - {r['mode'] for r in rr})
                status = 'missing record' if not rr else 'recent record' if recent else 'stale or unknown revision age'
                status += '; missing modes: ' + ', '.join(missing) if missing else ''
                base_status = ('missing baseline' if not tc else 'historical/unverified baseline (missing key provenance)' if not any(r['content_digest'] and r['tlc_version'] for r in tc) else 'baseline key recorded; validate against current inputs')
                current = (baseline_inputs or {}).get(mid)
                if current:
                    valid = [r for r in tc if r['content_digest'] == current.get('content_digest') and r['tlc_version'] == current.get('tlc_version') and r['counts']['result'] in COMPLETE and r['metrics']['wall_s'] and not r['provenance'].get('count_problems')]
                    if not valid:
                        base_status = 'missing/stale baseline key (current content/TLC version differs or unverified)'
                    else:
                        required = {run['workers'] for m in suite.get('models', []) if m['id'] == mid for run in m.get('runs', [])}
                        instances = sorted({r['instance']['type'] for r in rr + tc if r['instance']['type']})
                        gaps = []
                        for instance in instances:
                            missing_workers = sorted(required - {r['workers'] for r in valid if r['instance']['type'] == instance})
                            if missing_workers:
                                gaps.append(instance + ': ' + ', '.join(map(str, missing_workers)))
                        base_status = 'current input key recorded' + ('; missing worker keys by instance: ' + '; '.join(gaps) if gaps else '')
                rejected = [r for r in records if r['model'] == mid and r['provenance'].get('count_problems')]
                if rejected:
                    status += '; excluded expectation mismatches: ' + str(len(rejected))
                refs = ', '.join(ref(r) for r in (rr[-1:] + tc[-1:] + rejected)) or '—'
                out.append(f'| {mid} | {status} | {base_status} | {refs} |')
        elif section == 'Multi-core scaling':
            out += ['Efficiency is T(1) / (workers × T(workers)); only the same revision, mode, model, instance and arguments are compared. '
                    'Unmeasured worker counts between one and the maximum remain gaps.', '',
                    '| Model | Workers | Wall s | Efficiency | tlx optimizations | Evidence |', '|---|---:|---:|---:|---|---|']
            grouped = {}
            for r in rows:
                if 'scaling' in r['category'] or r['workers'] == 1:
                    grouped.setdefault(scaling_identity(r), {})[r['workers']] = r
            found = False
            for key, ws in sorted(grouped.items(), key=lambda item: json.dumps(item[0])):
                if len(ws) < 2 or 1 not in ws:
                    continue
                found = True
                for w, r in sorted(ws.items()):
                    eff = ws[1]['metrics']['wall_s'] / (w * r['metrics']['wall_s'])
                    out.append(f"| {r['model']} | {w} | {number(r['metrics']['wall_s'])} | {number(100 * eff, '%')} | "
                               f"{reduction_note(r)} | {ref(r)} / {ref(ws[1], '1w')} |")
                gaps = sorted(set(range(1, max(ws) + 1)) - set(ws))
                if gaps:
                    out.append(f"| {key[0]} | unmeasured: {', '.join(map(str, gaps))} | — | — | — | — |")
            if not found:
                out += ['No eligible records with a comparable one-worker measurement.']
        else:
            predicates = {
                SECTIONS[1]: lambda r: r['mode'] == 'default' and 'corpus' in r['category'],
                SECTIONS[2]: lambda r: r['mode'] == '-compile',
                SECTIONS[3]: lambda r: 'external' in r['category'] or any(s in r['model'] for s in ('Raft', 'Zab', 'Mongo')),
                SECTIONS[4]: lambda r: 'liveness' in r['category'],
                SECTIONS[5]: lambda r: 'trace-validation' in r['category'],
                SECTIONS[7]: lambda r: 'beyond-memory' in r['category'],
                SECTIONS[8]: lambda r: r['mode'] == '-interp' and r['workers'] == 1,
            }
            rs = [r for r in rows if predicates[section](r)]
            if section == SECTIONS[1]:
                out += ['Corpus coverage is the manifest selection, including missing records. A partial selection is not a whole-corpus speedup. '
                            'Each ratio here is the timed tlx run (after the discarded warm-up) against TLC\'s single process; the '
                        '`tlx optimizations` column names the optimization the tlx record states, so a row whose tlx run was '
                        'reduced says so.', '']
            if not rs:
                out += ['No eligible records. See Coverage and gaps.', '']
                continue
            out += ['| Model / mode | Workers | Result / distinct / generated / depth | Wall s | CPU s | RSS MiB | Instructions | TLC wall / CPU s | TLC RSS MiB | TLC / tlx | TLC / tlx RSS | tlx optimizations | Evidence |',
                    '|---|---:|---|---:|---:|---:|---:|---:|---:|---:|---:|---|---|']
            for r in rs:
                tc = baseline(r)
                counts = r['counts']
                count_text = ' / '.join(str(counts.get(k) if counts.get(k) is not None else '—') for k in ('result', 'distinct', 'generated', 'depth'))
                baseline_text = (number(tc['metrics']['wall_s']) + ' / ' + number(tc['metrics']['cpu_s'])) if tc else '—'
                tlc_rss_text = number(peak_rss(tc['metrics'])) if tc else '—'
                evidence = ref(r) + (' / ' + ref(tc, 'TLC ' + (tc['tlc_version'] or 'unknown version')) if tc else '')
                configuration = r['configuration']
                label = r['model'] + ' / ' + r['mode']
                args = configuration.get('args', [])
                if '-maxmem' in args and args.index('-maxmem') + 1 < len(args):
                    label += ' / -maxmem ' + args[args.index('-maxmem') + 1]
                if configuration.get('cgroup_mib'):
                    label += f" / cgroup {configuration['cgroup_mib']} MiB"
                out.append(f"| {label} | {r['workers']} | {count_text} | "
                           + ' | '.join(number(peak_rss(r['metrics'])) if k == 'rss_mib' else number(r['metrics'][k])
                                        for k in METRICS)
                           + f" | {baseline_text} | {tlc_rss_text} | {number(ratio(r), '×')} | "
                           + f"{number(rss_ratio(r, tc), '×')} | {reduction_note(r)} | {evidence} |")
        out += ['']
    return '\n'.join(out)


def store_text(root, name):
    """The text of the store file `name` under `root`, or the refusal naming it.

    The report is rendered *from* the store, so a checkout of the published
    sources - which has no store (docs/benchmarking.md section 6.2) - has
    nothing to render from: the refusal names the file this checkout lacks and
    exits non-zero instead of raising `FileNotFoundError` out of `read_text`.
    Rendering an empty report instead is not an option, and it is why `check`
    may report "0 problems" for the same absent file while this may not: a
    report that renders nothing reads exactly like one that found nothing.

    The words are `benchmarking.legacy.missing_input`'s, which is what every
    reader of the store reaches, so this reader and the suite commands name a
    missing file in the same sentence rather than in two that drift.
    """
    try:
        return (root / name).read_text()
    except FileNotFoundError:
        raise SystemExit(missing_input(root / name, root))


def require_store(root=ROOT):
    """Read the versioned suite manifest, or name the missing checkout input."""
    return json.loads(store_text(root, 'bench/suite.json'))


def migrate_command(root=ROOT):
    """The `migrate` command: the store's manifest first, then the transaction.

    Migration re-derives the store and the command renders the report from it
    straight after, so a checkout without the store has nothing to migrate and
    nothing to render. The refusal is the command's, not the transaction's:
    `benchmarking.legacy.migrate` writes `bench/migration.json` and realigns
    `bench/records`, so a check after it leaves a store behind a command that
    failed - a tree the user did not choose. A caller that drives the
    transaction on a root of its own (a fixture) imports it from
    `benchmarking.legacy` and keeps the library's behaviour, which is why this
    is a name of its own rather than the re-exported `migrate`.
    """
    require_store(root)
    return migrate(root)


def policy(root=ROOT, refresh=False):
    root = Path(root)
    path = root / 'bench/report-policy.json'
    records = load_records(root)
    h = json.loads(path.read_text()) if path.exists() else {'schema_version': VERSION, 'stale_after_revisions': 20, 'ages': {}}
    if refresh or not path.exists():
        p = run_git('rev-parse', 'HEAD', cwd=root)
        h['reference_revision'] = p.stdout.strip() if p.returncode == 0 else None
        h['ages'] = {}
        for rev in sorted({r['revision'] for r in records if r['revision']}):
            rev = rev.removesuffix('-dirty')
            p = run_git('merge-base', '--is-ancestor', rev, 'HEAD', cwd=root, text=False)
            if p.returncode == 0:
                p = run_git('rev-list', '--count', rev + '..HEAD', cwd=root)
                h['ages'][rev] = int(p.stdout) if p.returncode == 0 else None
            else:
                h['ages'][rev] = None
        if root.resolve() == ROOT.resolve():
            suite = require_store(root)
            mids = [m['id'] for m in suite['models']]
            current = bench_models.oracle(mids)
            version = bench_machine.tla2tools_info().get('revision')
            h['baseline_inputs'] = {mid: {'content_digest': content_digest(m), 'tlc_version': version}
                                    for mid, m in current.items() if mid in mids and m.get('tla') and m.get('cfg')}
        dump(path, h)
    return h


def generate(root=ROOT, refresh=False):
    root = Path(root)
    if not load_records(root) and require_store(root).get("models"):
        raise SystemExit("no benchmark measurements: restore a verified data snapshot before generating the report")
    h = policy(root, refresh)
    suite = require_store(root)
    text = render(load_records(root), suite, stale_after=h['stale_after_revisions'], ages=h['ages'],
                  baseline_inputs=h.get('baseline_inputs'), report_note=h.get('report_note'))
    p = root / 'docs/performance.md'
    p.parent.mkdir(parents=True, exist_ok=True)
    if not p.exists() or p.read_text() != text:
        p.write_text(text)
    return text


def check(root=ROOT, *, sources=True):
    """Standalone gate, called by doccheck (therefore merge_gate and done_check)."""
    root = Path(root)
    if not (root / 'bench/suite.json').exists():
        return []  # small doccheck test fixtures do not contain a benchmark suite
    if (not sources and not any((root / "bench" / directory).exists() for directory in ("records", "tlc-baselines"))
            and not json_sources(root) and not (root / "bench/migration.json").exists()):
        print("benchmark report evidence: measurement data absent; report reproduction not checked")
        return []
    problems = []
    try:
        h = json.loads((root / 'bench/report-policy.json').read_text())
        records = load_records(root)
        known = {r['id']: r for r in records}
        want = render(load_records(root), json.loads((root / 'bench/suite.json').read_text()),
                      stale_after=h['stale_after_revisions'], ages=h['ages'],
                      baseline_inputs=h.get('baseline_inputs'), report_note=h.get('report_note'))
        if not (root / 'docs/performance.md').exists() or (root / 'docs/performance.md').read_text() != want:
            problems.append('performance report differs from records; regenerate with python3 scripts/bench.py report')
        if not sources:
            return problems
        # `load_records` above already refused a store file whose envelope, key,
        # filename and measurement disagree, so what is left to check is that
        # the store is exactly the store the sources derive.
        by_stem, by_source = {}, {}
        for r in records:
            by_stem[store_stem(r)] = r
            by_source.setdefault(r['provenance']['source'], []).append(r)
        kept_loose = {}
        for r in records:
            kept_loose.setdefault(loose_key(r), []).append(r)
        for source in json_sources(root):
            data = source_bytes(root, source)
            if data is None:
                continue
            raw = json.loads(data)
            for row, ptr, kw in measurement_rows(raw):
                normalized = normalize(raw, row, source, ptr, **kw)
                old = known.get(normalized['id'])
                if (old is not None and 'count_problems' in normalized['provenance']
                        and old['provenance'].get('count_problems') != normalized['provenance']['count_problems']):
                    problems.append(f'{source}{ptr}: expectation diagnostics differ; run python3 scripts/bench.py migrate')
                    continue
                if old is not None and all(old[k] == normalized[k] for k in ('model', 'mode', 'workers', 'metrics', 'counts', 'configuration')):
                    continue
                # A row the store does not hold by id is fine when a stronger
                # measurement of the same key is stored instead: that is what
                # "one file per key" means, and the superseded row stays
                # readable in its own source. The key is compared without the
                # input digest, because migration completes a legacy row's key
                # by adopting the current model bytes when the verdict and the
                # counts match the oracle exactly.
                if any(evidence(x) >= evidence(normalized) for x in kept_loose.get(loose_key(normalized), [])):
                    continue
                problems.append(f'{source}{ptr}: unimported/changed measurement; run python3 scripts/bench.py migrate')
        # Reverse direction: every stored row must still be produced by its
        # source, so clearing a source never keeps stale live records.
        for source, stored in sorted(by_source.items()):
            try:
                produced = source_measurements(root, source)
            except ArchiveError as e:
                # HARNESS-18: a retired artifact is only resolved provenance when
                # its pinned revision and SHA-256 check out; a locator that does
                # not resolve is refused by name, never read as "source absent".
                problems.append(f'{source}: archived provenance does not resolve ({e})')
                continue
            if produced is None:
                problems.append(f'{source}: source file is missing but its stored measurements remain; re-ingest or run python3 scripts/bench.py migrate')
                continue
            produced_ids = {r['id'] for r in produced}
            for r in stored:
                if r['id'] not in produced_ids:
                    problems.append(f'{source}: stored measurement {r["id"]} is no longer produced by its source; re-ingest or run python3 scripts/bench.py migrate')
    except (OSError, ValueError, KeyError, TypeError) as e:
        problems.append(f'performance records/report invalid: {e}')
    inventory_path = root / 'bench/migration.json'
    inventory = json.loads(inventory_path.read_text()) if inventory_path.exists() else {}
    frozen = inventory.get('legacy_markdown_sha256', {})
    # The frozen documents are retired from the tree and read at the pinned
    # revision, so this loop now only ever sees Markdown that should not exist:
    # a new ad hoc report, or a restored copy whose bytes drifted from the
    # recorded hash.
    for p in (root / 'bench').rglob('*.md'):
        rel = p.relative_to(root / 'bench').as_posix()
        if rel == 'README.md':
            continue  # versioned input/backup documentation, not measurement evidence
        if rel.removeprefix('archive/') not in LEGACY_MARKDOWN:
            problems.append(f'bench/{rel}: new ad hoc performance markdown; record via the suite')
        elif rel.removeprefix('archive/') in frozen and hashlib.sha256(p.read_bytes()).hexdigest() != frozen[rel.removeprefix('archive/')]:
            problems.append(f'bench/{rel}: historical performance markdown is frozen; record via the suite')
    return problems


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('command', choices=['migrate', 'report', 'check'])
    p.add_argument('--root', type=Path, default=ROOT)
    a = p.parse_args()
    if a.command == 'migrate':
        # Migration is a re-derivation of the store, not a re-dating of the
        # report: it must leave the report policy and the generated report
        # untouched when nothing about the measurements changed, or every fold
        # produces a noise commit (BENCH-01).
        rs = migrate_command(a.root)
        generate(a.root)
        print(f'{len(rs)} canonical measurements migrated; archived sources read at the pinned revision')
    elif a.command == 'report':
        generate(a.root)
    else:
        errors = check(a.root)
        print('\n'.join(errors) if errors else 'performance report: 0 problems')
        return bool(errors)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
