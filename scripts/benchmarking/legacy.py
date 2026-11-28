
"""Readers and import transactions that turn benchmark artifacts into canonical rows.

Every historical artifact family has an explicit adapter here — a corpus
history, an A/B or scaling campaign, a disk or profile run, the original
rectangular Markdown tables — and an unrecognized layout is refused rather than
silently imported as nothing (`measurement_rows`). The adapters are also the
readers `check` re-derives a source's rows through, so a stored row that its
source no longer produces is visible (HARNESS-18).

`migrate` and `ingest` are the two transactions that write them: `migrate`
re-imports the tracked history as a whole, `ingest` replaces the container of
the one source a runner just produced. `LEGACY_MARKDOWN` is the frozen
allowlist of documents whose bytes stay as provenance; they are never the
source of a reported number (DOC-06).

The current store ships with the released tree (docs/benchmarking.md section
6.2), so `missing_input` - what a command says when an input of this module is
not here - lives here too: every reader of the store reaches this module, and
one owner is what keeps the readers that never import each other from keeping
their own copy of the sentence.
"""
import hashlib
import json
import os
from pathlib import Path
import re

from benchmarking import machine as bench_machine, models as bench_models
from benchmarking.baselines import attach_baselines, content_digest, reusable, same_tlc_key, seed_baselines, store_entry
from benchmarking.records import (CONTAINER, ROOT, STORE, VERSION, apply_receipt, archive_inventory, archived_bytes,
                                  digest, dump, evidence, load_records, load_store, measurement_key, normalize,
                                  realign_store, receipt_revisions, record_path, store_lock, store_stem, validate,
                                  write_records)


# Frozen allowlist of historical documents. They are retired from the tree at the
# revision `bench/migration.json` pins and are read back from there; new reports
# belong only in docs/performance.md.
LEGACY_MARKDOWN = {'results.md', 'trend.md', 'liveness-scaling.md', 'disk-scale.md',
                   'flexible-raft-profile.md', 'memo-inputs/README.md', 'ttfr.md'}

# Containers and generated files that are not measurement sources.
NOT_SOURCES = ('suite.json', 'schema.json', 'report-policy.json', 'migration.json')

#: Missing baseline files indicate an incomplete checkout. Name the missing
#: file and the publication contract instead of leaking a filesystem traceback.
STORE_NOTE = ("benchmark inputs and current baseline records ship with the sources "
              "(docs/benchmarking.md section 6.2)")


def missing_input(path, root=ROOT):
    """The refusal for a store input this checkout does not have.

    The file is named the way the checkout sees it - relative to the repository
    root when it is inside it - and the store note is added for a file under
    `bench/`. A path the caller gave itself (a `--manifest` fixture, say) is
    named as it was given and without the note: it is not the store's absence.
    `root` is the caller's repository root, so the name is relative to the tree
    the command read the path from.
    """
    relative = os.path.relpath(path, root)
    shown = relative if not relative.startswith(os.pardir + os.sep) else str(path)
    if shown.startswith("bench/") or shown == "bench":
        return f"No such file: {shown}: {STORE_NOTE}"
    return f"No such file: {shown}"


def source_bytes(root, source):
    """The bytes of one benchmark artifact: the working-tree file, else the archive.

    A source retired from the tree is read at the revision and SHA-256 the
    migration inventory pins, so removing a file does not remove its provenance
    or its canonical rows; `None` means it is neither present nor archived, and
    an `ArchiveError` means the locator itself does not resolve (HARNESS-18)."""
    path = Path(root) / source
    if path.is_file():
        return path.read_bytes()
    return archived_bytes(root, source)


def json_sources(root):
    """Measurement sources for the canonical store, including archived sources.

    Post-fix validation artifacts have separate sampling and interpretation;
    they are published evidence but never implicitly promoted into the frozen store.
    """
    found = [p.relative_to(root).as_posix() for p in sorted((root / 'bench').rglob('*.json'))
             if p.parts[-2] not in ('records', 'tlc-baselines') and p.name not in NOT_SOURCES
             and p.relative_to(root).parts[:2] != ('bench', 'validation')]
    _, archived = archive_inventory(root)
    found += [s for s in sorted(archived)
              if s.endswith('.json') and s.count('/') >= 1 and not s.startswith('bench/validation/')
              and s.rsplit('/', 2)[-2] not in ('records', 'tlc-baselines')
              and s.rsplit('/', 1)[-1] not in NOT_SOURCES and s not in found]
    return found


def markdown_sources(root):
    """Every Markdown artifact the store imports: the top level of `bench/` and the archive."""
    found = [p.relative_to(root).as_posix() for p in sorted((root / 'bench').glob('*.md'))]
    _, archived = archive_inventory(root)
    return found + [s for s in sorted(archived) if s.endswith('.md') and s.count('/') == 1 and s not in found]


def legacy_rows(h):
    """Explicit adapters for history, A/B, scaling, disk, profile and microbench files."""
    def emit(raw, pointer, evidence=None, **kw):
        if isinstance(raw, list):
            if not raw:
                return
            # A/B arrays are repeated samples of the same run configuration.
            last = raw[-1]
            if not isinstance(last, dict):
                return
            raw = {**last, 'walls': [x.get('wall', x.get('wall_s')) for x in raw],
                   'cpu': [x.get('cpu', x.get('cpu_s')) for x in raw],
                   'rss_mib': [x.get('rss', x.get('rss_mib')) for x in raw],
                   **(evidence or {})}
        if not isinstance(raw, dict):
            return
        if isinstance(raw.get('result'), dict):
            raw = {**raw, **raw['result']}
        if any(k in raw for k in ('wall', 'walls', 'wall_s', 'median', 'min')):
            yield raw, pointer, kw

    for campaign, models in h.get('series', {}).items():
        rev = re.match(r'^([a-f0-9]{7,40})\b', campaign)
        workers = re.search(r'-w(\d+)\b', campaign)
        env = dict(re.findall(r'\b(TLX_\w+)=(\S+)', campaign))
        for mid, samples in models.items():
            yield from emit({'walls': samples, 'env': env or None}, f'/series/{campaign}/{mid}',
                            model=mid, mode='-interp' if 'corpus-interp' in campaign else '-compile' if 'corpus-compile' in campaign else 'legacy-unknown',
                            workers=int(workers[1]) if workers else 1,
                            revision=rev[1] if rev else None, variant=campaign)
    if isinstance(h.get('base'), dict) and h['base'].get('runs'):
        for raw, ptr, kw in legacy_rows(h['base']):
            yield raw, '/base' + ptr, {**kw, 'revision': h['base'].get('commit'), 'variant': 'base'}
    runs = h.get('runs', {})
    if isinstance(runs, list):  # bounded ClockSettles/model and automaton sizes
        for i, r in enumerate(runs):
            yield from emit(r, f'/runs/{i}', model=f"bench/ClockSettles/{r.get('phase', 'model')}/{r.get('size', '?')}",
                            mode='-interp' if r.get('phase') == 'model' else 'legacy-unknown', variant=r.get('binary'), revision=h.get(r.get('binary')))
    else:
        for key, r in runs.items():
            model, _, variant = key.partition('#')
            if isinstance(r, dict) and r.get('model'):
                yield from emit(r, '/runs/' + key)
            elif isinstance(r, list):
                entry = (h.get('summary') or {}).get(key)
                # Only a source that actually records exits or a completeness
                # verdict has per-sample evidence to keep; a historical A/B
                # without either stays unknown (never refuted by absence).
                declared = any(isinstance(x, dict) and 'exit' in x for x in r)
                declared = declared or (isinstance(entry, dict) and 'complete' in entry)
                evidence = {'sample_result_exits': [{'result': x.get('result'), 'exit': x.get('exit')}
                                                    for x in r if isinstance(x, dict)],
                            'completed_samples': entry.get('completed_samples')} if declared else None
                yield from emit(r, '/runs/' + key, evidence=evidence, model=model, variant=variant)
            elif isinstance(r, dict):
                for label, run in r.items():
                    yield from emit(run, '/runs/' + key + '/' + label, model=key, variant=label)
    for mid, raw in (h.get('tlc_baseline') or {}).get('runs', {}).items():
        yield from emit(raw, f'/tlc_baseline/runs/{mid}', model=mid, mode='-tlc', workers=raw.get('workers', 1))
    for mid, rec in h.get('models', {}).items():
        if 'bins' in rec:  # adaptive default tier: cold and warm cache campaigns
            tc = rec.get('tlc') or {}
            yield from emit({**tc, 'measurement_revision': tc.get('measurement_revision'),
                             'measurement_date': tc.get('date') if tc.get('content_digest') else
                                 h.get('date') if tc.get('source') == 'measured' else None},
                            f'/models/{mid}/tlc', model=mid, mode='-tlc', workers=1)
            for binary, part in rec['bins'].items():
                for cache in ('cold', 'warm'):
                    raw = part.get(cache)
                    if raw:
                        # Historical warm summaries used minima; do not relabel them as medians.
                        raw = {**raw, 'aggregation': 'minimum' if cache == 'warm' else 'single-or-legacy-scalar'}
                        yield from emit(raw, f'/models/{mid}/bins/{binary}/{cache}', model=mid,
                                        mode='default', workers=1, revision=h.get('commit') if binary == 'new' else h.get(binary),
                                        variant='new' if binary == 'new' and cache == 'cold' else f'{binary}-{cache}')
            continue
        for tool in ('tlc', 'tlx'):
            for w, raw in rec.get(tool, {}).items():
                yield from emit(raw, f'/models/{mid}/{tool}/{w}', model=mid, mode='-tlc' if tool == 'tlc' else '-compile', workers=int(w))
        for label, raw in rec.get('runs', {}).items():
            mode = '-tlc' if h.get('kind') == 'tlc-baseline' or label.startswith('TLC') else '-compile'
            w = int(label) if label.isdigit() else h.get('workers', 1)
            yield from emit(raw, f'/models/{mid}/runs/{label}', model=mid, mode=mode, workers=w,
                            variant=label.split()[0] if not label.isdigit() else None)
        for variant in ('before', 'after'):
            part = rec.get(variant, {})
            if part.get('ordinary_timings'):
                timings = part['ordinary_timings']
                combined = {**timings[-1], 'walls': [x.get('wall') for x in timings],
                            'cpu': [x.get('cpu') for x in timings], 'rss_mib': [x.get('rss') for x in timings],
                            'instructions': (part.get('normal_counts') or {}).get('instructions'),
                            'metric_sources': {'instructions': f'/models/{mid}/{variant}/normal_counts/instructions'}}
                yield from emit(combined, f'/models/{mid}/{variant}/ordinary_timings', model=mid,
                                mode='-compile', revision=h.get(variant), variant=variant)
        if isinstance(rec.get('tlc_baseline'), dict):
            yield from emit(rec['tlc_baseline'], f'/models/{mid}/tlc_baseline', model=mid, mode='-tlc', workers=1)


def measurement_rows(h):
    # Full -stats JSON is diagnostic attribution, not a benchmark sample.
    # Its timing sample belongs to the adjacent profile summary.
    if isinstance(h, dict) and {"sample_every", "phases", "counters", "time_est_s", "actions"}.issubset(h):
        return iter(())
    if not isinstance(h, dict) or not any(k in h for k in ('runs', 'models', 'series', 'tlc_baseline', 'base')):
        raise ValueError('unrecognized benchmark layout; add a migration adapter instead of silently omitting measurements')
    return legacy_rows(h)


def markdown_rows(name, text):
    """Import the original rectangular table; prose/profile diagnostics remain archived.

    Only explicit measurement columns are imported, never speedup summaries.
    The original reports used minima, so these scalar records carry that label.
    """
    machine = re.search(r'^Machine: (.*?). Date: (.*?), commit ([\w-]+)\.', text, re.M)
    if not machine:
        return
    header = {'machine': machine[1], 'date': machine[2], 'commit': machine[3]}
    columns = None
    for i, line in enumerate(text.splitlines(), 1):
        if line.startswith('| model | distinct | TLC'):
            columns = [x.strip() for x in line.strip('|').split('|')]
            continue
        if columns is None:
            continue
        if not line.startswith('|'):
            break
        cells = [x.strip() for x in line.strip('|').split('|')]
        if len(cells) != len(columns) or '/' not in cells[0]:
            continue
        for c, value in zip(columns[2:], cells[2:]):
            if not re.fullmatch(r'[0-9]+(?:\.[0-9]+)?', value):
                continue
            match = re.match(r'(TLC|tlx) (.*?)?(\d+)w', c)
            if not match:
                continue
            tool, label, w = match.groups()
            mode = '-tlc' if tool == 'TLC' else '-interp' if 'interp' in label else '-compile'
            raw = {'wall_s': float(value), 'distinct': int(cells[1]) if cells[1].isdigit() else None,
                   'result': None, 'tool': 'tlc' if tool == 'TLC' else 'tlx', 'aggregation': 'minimum',
                   'mode': mode, 'workers': int(w), 'model': cells[0]}
            variant = 'cold' if 'cold' in c else label.strip() if label.strip() not in ('compile', 'interp') else None
            # Counts tick is not a verdict. Missing verdict remains unknown.
            yield header if tool == 'tlx' else {**header, 'commit': None, 'date': None}, raw, f'/line/{i}/{c}', {'variant': variant}


def source_measurements(root, source):
    """The canonical rows a source produces now, or None if it is neither in the
    tree nor archived.

    A retired source is read at the archive's pinned revision, so a stored row
    keeps a reader that can still tell a live source from a vanished one; a
    locator that does not resolve raises `ArchiveError` instead of reading as an
    absent source. Baselines are independent evidence: their container is the
    baseline file, so read the stored measurement back instead of re-deriving
    history rows.
    """
    data = source_bytes(root, source)
    if data is None:
        return None
    if source.rsplit('/', 1)[0] in set(CONTAINER.values()):
        # The row's source is the store file itself: a measurement of record
        # collected directly (a fresh TLC baseline), not imported from an
        # artifact. Read it back rather than re-deriving it from history.
        return [validate(json.loads(data)['measurement'])]
    if source.endswith('.md'):
        return [normalize(h, raw, source, ptr, **kw)
                for h, raw, ptr, kw in markdown_rows(source, data.decode())]
    raw_header = json.loads(data)
    return [normalize(raw_header, raw, source, ptr, **kw) for raw, ptr, kw in measurement_rows(raw_header)]


def adopt_legacy(records, models, oracles, version):
    """Coordinator-approved migration: exact oracle verdict/distinct/depth match.

    Missing TLC version cannot be inferred merely because one jar exists today.
    No stored historical jar digest means no proof its bytes stayed unchanged.
    """
    for r in records:
        if r.get('tool') != 'tlc' or r['content_digest'] or not r['tlc_version']:
            continue
        if not version or not version.startswith(r['tlc_version']):
            continue
        m, oracle = models.get(r['model']), oracles.get(r['model'])
        if not m or not oracle:
            continue
        expected = oracle.get('tlc', oracle)
        fields = ('result', 'distinct', 'depth')
        if any(expected.get(f) is None or r['counts'].get(f) != expected[f] for f in fields):
            continue
        content = content_digest(m)
        if content is None:
            continue
        r['content_digest'], r['tlc_version'] = content, version
        r['provenance']['adoption'] = {
            'method': 'migration snapshot with exact current TLC oracle verdict/distinct/depth match',
            'content_digest': content, 'matched_counts': {f: expected[f] for f in fields},
            'oracle': oracle.get('oracle_file', 'corpus/out/tlc*.json'),
            'tlc_revision_basis': 'recorded TLC revision matches current jar manifest; no inference from jar presence'}
    return records


def _referenced_baseline(record, baselines):
    """Return the stored TLC row `record` references when it is at least as strong, else None."""
    if record.get('tool') != 'tlc':
        return None
    original = baselines.get(record['provenance'].get('reused_from'))
    if original is None or not same_tlc_key(measurement_key(original), measurement_key(record)):
        return None
    if reusable(store_entry(original)) or evidence(original) >= evidence(record):
        return original
    return None


def repoint_to_store(record):
    """A measurement whose source is the store file that holds it keeps that
    pointer current: the file a key names moves when the key's identity changes
    (the container of its tool, the dimensions that name it), and a pointer at a
    file that no longer exists would make the row's provenance unresolvable."""
    source = f'{record_path(record)}'
    if source == record['provenance']['source']:
        return record
    r = {**record, 'provenance': {**record['provenance'], 'source': source}}
    r['id'] = digest([source, record['provenance']['pointer']])[:24]
    return validate(r)


def migrate(root=ROOT):
    root = Path(root)
    receipts = receipt_revisions(root)
    out = []
    for source in json_sources(root):
        data = source_bytes(root, source)
        if data is None:  # an unarchived source that vanished is `check`'s finding, not migration's
            continue
        h = json.loads(data)
        if not isinstance(h, dict):
            continue
        h = apply_receipt(h, source, receipts)
        for raw, pointer, kw in measurement_rows(h):
            r = normalize(h, raw, source, pointer, **kw)
            out.append(r)
    for source in markdown_sources(root):
        data = source_bytes(root, source)
        if data is None:
            continue
        for h, raw, pointer, kw in markdown_rows(source, data.decode()):
            out.append(normalize(h, raw, source, pointer, **kw))
    # Preserve native canonical metadata when re-importing a history file.
    from benchmarking import records as _records
    del _records.UNREADABLE[:]
    existing = {r['id']: r for r in load_store(root)}
    if _records.UNREADABLE:
        print(f'migrate: {len(_records.UNREADABLE)} store file(s) predate the schema and were rewritten or dropped')
    store_containers = set(CONTAINER.values())
    baselines = {r['id']: r for r in existing.values() if r['tool'] == 'tlc'}
    live_ids = {r['id'] for r in out} | {r['id'] for r in existing.values()
                                         if r['provenance']['source'].rsplit('/', 1)[0] in store_containers}
    retained, retained_ids = [], set()
    for fresh in out:
        original = _referenced_baseline(fresh, baselines)
        if original is not None and (original['provenance']['source'] == fresh['provenance']['source']
                                     or original['id'] in live_ids):
            if original['provenance']['source'] == fresh['provenance']['source'] and original['id'] not in retained_ids:
                retained.append(original)
                retained_ids.add(original['id'])
            continue
        old = existing.get(fresh['id'])
        keep_identity = old and (not old['provenance'].get('legacy', True) or old['provenance'].get('adoption'))
        same_measurement = old and all(old[k] == fresh[k] for k in ('model', 'mode', 'workers', 'metrics', 'counts', 'configuration'))
        record = old if keep_identity and same_measurement else fresh
        for field in ('repetitions', 'count_problems'):
            if field in fresh['provenance']:
                record['provenance'][field] = fresh['provenance'][field]
        retained.append(record)
        retained_ids.add(record['id'])
    out = retained
    # A measurement collected straight into the store (a fresh TLC baseline, whose
    # source is its own store file) has no other artifact to be re-derived from,
    # so migration carries it forward; without this every baseline would be
    # dropped by the store realignment below.
    for record in existing.values():
        if record['provenance']['source'].rsplit('/', 1)[0] in store_containers \
                and record['id'] not in retained_ids:
            record = repoint_to_store(record)
            out.append(record)
            retained_ids.add(record['id'])
    if root.resolve() == ROOT.resolve():
        mids = sorted({r['model'] for r in out if r.get('tool') == 'tlc'})
        current = bench_models.oracle(mids)
        for mid in mids:
            if mid not in current:
                try:
                    current[mid] = bench_models.scale_models([mid])[mid]
                except (KeyError, SystemExit, OSError):
                    pass
        # The oracle resolver rejects stale external digests. Missing oracles
        # remain unadopted, even for a completed historical measurement.
        version = bench_machine.tla2tools_info().get('revision')
        adopt_legacy(out, current, current, version)
    out = attach_baselines(out)
    with store_lock(root):
        # The store is derived, so the transaction publishes the whole derived
        # set: a key that stopped being produced loses its file too.
        realign_store(out, root)
        sources = {}
        for r in out:
            sources[r['provenance']['source']] = sources.get(r['provenance']['source'], 0) + 1
        inventory_path = root / 'bench/migration.json'
        previous_inventory = json.loads(inventory_path.read_text()) if inventory_path.exists() else {}
        frozen_markdown = previous_inventory.get('legacy_markdown_sha256')
        if frozen_markdown is None:
            frozen_markdown = {name: hashlib.sha256((root / 'bench' / name).read_bytes()).hexdigest()
                               for name in sorted(LEGACY_MARKDOWN) if (root / 'bench' / name).is_file()}
        # The archive locator is the one thing migration cannot re-derive from
        # the tree (it names what is no longer there), so it is carried forward
        # as a transaction record rather than recomputed.
        archived = previous_inventory.get('archived_sources')
        if not isinstance(archived, dict):
            archived = {'revision': None, 'sha256': {}}
        dump(inventory_path, {'schema_version': VERSION, 'sources': sources, 'legacy_markdown_sha256': frozen_markdown,
             'archived_sources': archived,
             'notes': ['Historical artifacts are retained as provenance; a retired one is read at `archived_sources.revision`, '
                       'and `archived_sources.sha256` pins the bytes of each, including the counters, prose and per-sample '
                       'detail the canonical schema does not carry.',
                       'Unknown historical revision, date, verdict, TLC version and input digest stay null.',
                       'Minimum-only markdown timings are imported without inventing a verdict; excluded from headlines.']})
    return sorted(out, key=lambda r: r['id'])


def ingest(path, root=ROOT):
    """Record newly produced legacy-compatible runner output in the canonical store.

    The source's owned container is replaced as a unit, including with no rows,
    so a cleared source never keeps stale live measurements. Independent
    baselines live in their own containers and are left untouched.
    """
    root, path = Path(root), Path(path).resolve()
    if not path.is_relative_to(root.resolve()):
        return  # scratch output is not a committed measurement of record
    source = path.relative_to(root.resolve()).as_posix()
    h = json.loads(path.read_text())
    receipts = receipt_revisions(root)
    h = apply_receipt(h, source, receipts)
    rs = [normalize(h, raw, source, ptr, **kw) for raw, ptr, kw in measurement_rows(h)]
    with store_lock(root):
        stored = load_records(root)
        # A history copy of a cached baseline is a reference, not new evidence.
        # Resolve it to the existing stored row when at least as strong so
        # canonical evidence (including bounded timeouts/errors) stays intact
        # without deleting a row owned by this same source.
        baselines = {r['id']: r for r in stored if r['tool'] == 'tlc'}
        resolved, seen = [], set()
        for r in rs:
            original = _referenced_baseline(r, baselines)
            if original is not None:
                if original['provenance']['source'] == source and original['id'] not in seen:
                    resolved.append(original)
                    seen.add(original['id'])
                continue
            resolved.append(r)
        rs = resolved
        # The files this source owned before are replaced as a unit, including
        # with no rows: a cleared source never keeps stale live measurements.
        owned = {record_path(r) for r in stored if r['provenance']['source'] == source}
        all_records = [r for r in stored if r['provenance']['source'] != source] + rs
        attach_baselines(all_records)
        write_records(all_records, root, replace=owned - {record_path(r) for r in rs})
    return rs
