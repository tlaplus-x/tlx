
"""The canonical measurement store: schema, normalization and source transactions.

The benchmark entrypoints (`bench.py`, `bench_suite.py`, the disk/liveness/
profile/ttfr lanes, `doccheck.py`) record through this library; the command
entrypoint over it is `bench_records.py`. Keeping the store free of that
entrypoint is what lets a measurement be written without loading the CLI
(HARNESS-03).

Three responsibilities live here and nowhere else:

* the schema — `VERSION`, the mode/metric/count vocabularies and the verdict
  exit certification — with the two functions that enforce it (`normalize`,
  `validate`), including the one key computation both tools use
  (`measurement_key`);
* the raw provenance readers that read an artifact's own bytes
  (`supplied_revision`, `receipt_revisions`, `archived_bytes`): an artifact that
  states no revision, date or verdict keeps it unknown instead of having one
  inferred from a label (HARNESS-19), and an artifact retired from the tree is
  read at the revision the migration inventory pins rather than treated as
  gone (HARNESS-18);
* the source transactions — one container per source, written as a unit under
  the store lock, including an empty replacement — so a source that stops
  producing measurements cannot leave stale live rows behind (HARNESS-18,
  HARNESS-04).

The artifact-to-row adapters and the import transactions over them are
`benchmarking.legacy`; the keyed TLC baseline cache is `benchmarking.baselines`.
"""
import hashlib
import json
import math
from pathlib import Path
import re
import shlex
import statistics
import subprocess

from harness.storage import atomic_json_replace, file_lock


# The checkout this store belongs to: records.py is one level below the
# benchmark entrypoints it serves, so the repository root is two parents up.
ROOT = Path(__file__).resolve().parents[2]

# One store, one file per key, one envelope. A TLC baseline has its own
# lifecycle (collected once per key, replaced wholesale when the TLC revision
# changes - docs/benchmarking.md sections 3 and 5) and keeps its own container;
# both containers hold the same shape, whichever tool wrote the row.
STORE = 'bench/records'
BASELINES = 'bench/tlc-baselines'
CONTAINER = {'tlx': STORE, 'tlc': BASELINES}


VERSION = 2
MODES = ('default', '-tlc', '-interp', '-compile', 'legacy-unknown')
METRICS = ('wall_s', 'cpu_s', 'rss_mib', 'instructions')
COUNTS = ('generated', 'distinct', 'depth', 'result')
COMPLETE = ('success', 'deadlock', 'safety failure', 'liveness failure', 'assumption failure')

# The dimensions a measurement is identified by: two rows with the same key are
# two measurements of the same thing, and the store keeps one of them (the
# record of record). A TLC row has no revision and only one mode - TLC is run
# one way - so those dimensions are the constants of that tool; a tlx row
# carries the commit it was built from. `content_digest` and `tlc_version` are
# dimensions of both tools because both a model's bytes and the TLC build a
# timing was taken against decide whether two rows are the same measurement.
KEY_DIMENSIONS = ('tool', 'model', 'revision', 'instance_type', 'instance_arch', 'mode',
                  'args', 'variant', 'env', 'cgroup_mib', 'hogs', 'workers',
                  'tlc_version', 'content_digest')

# A key is complete when every dimension its tool needs for a reusable
# baseline is known. A row whose key is incomplete is still stored - it is the
# record of why that measurement exists - but only under its own identity:
# collapsing two incompletely keyed rows could drop the only record of one of
# them, which is why the filename stops being the key there.
KEY_REQUIRED = {'tlc': ('tool', 'model', 'instance_type', 'workers', 'tlc_version', 'content_digest'),
                'tlx': ('tool', 'model', 'instance_type', 'workers', 'mode')}

# Which of a key's dimensions give a file its name. A name only has to tell two
# measurements apart, and for TLC the mode, the arguments, the variant, the
# environment and the revision are constants of how TLC is run - they are in the
# key, and they distinguish nothing. A tlx measurement is named by all of them.
KEY_IDENTITY = {'tlc': ('tlc_version', 'model', 'content_digest', 'workers', 'instance_type'),
                'tlx': KEY_DIMENSIONS}

# The measurement envelope; nothing else belongs at the top level of a store
# file. `key` is `measurement_key`'s value and `measurement` the row.
ENVELOPE = ('schema_version', 'key', 'measurement')

# A row's own fields. `coverage` and the coverage attributes are absent when the
# run carried no coverage census - absent, not null, so that "unmeasured" is
# distinguishable from "measured as nothing".
FIELDS = ('schema_version', 'id', 'tool', 'model', 'mode', 'workers', 'category', 'revision', 'instance', 'date',
          'content_digest', 'tlc_version', 'counts', 'metrics', 'aggregation', 'samples', 'configuration',
          'baseline', 'provenance', 'raw_result',
          'native_share', 'host_time_share', 'host_s', 'host_calls', 'evaluations', 'fully_native',
          'search_thread_s_est', 'coverage')
COVERAGE_FIELDS = ('native_share', 'host_time_share', 'host_s', 'host_calls', 'evaluations',
                   'fully_native', 'search_thread_s_est')
CONFIGURATION_FIELDS = ('args', 'env', 'hogs', 'cgroup_mib', 'variant', 'compatibility')
PROVENANCE_FIELDS = ('source', 'pointer', 'legacy', 'adoption', 'repetitions', 'sample_results',
                     'measurement_source', 'reused_from', 'metric_sources', 'revision_source', 'count_problems', 'cache', 'sample_spread')
INSTANCE_FIELDS = ('type', 'arch', 'description')


# A temporal violation found during BFS uses EXIT_INVARIANT; post-search
# liveness checking and simulation use EXIT_LIVENESS. Tests check source drift.
_NORMAL_EXITS = {
    "success": (0,),
    "safety failure": (12,),
    "liveness failure": (12, 13),
    "property failure": (13,),
    "init property failure": (13,),
    "deadlock": (11,),
    "postcondition failure": (10,),
}


def normal_exits():
    """Verdict exit codes from crates/tlx-cli/src/report.rs, shared by producers
    and record adoption so crashes cannot become benchmark evidence.
    """
    return _NORMAL_EXITS


def exit_ok(result, exit_code):
    """Whether `exit_code` certifies a sample the parser called `result`; a
    missing exit (`None`) and the booleans JSON can put where an int belongs
    are never an exit (HARNESS-19)."""
    return (isinstance(exit_code, int) and not isinstance(exit_code, bool)
            and exit_code in normal_exits().get(result, ()))


def dump(path, value):
    """Publish `value` at `path`, leaving the file (and its mtime) alone when the
    bytes it would hold are already there: re-running a transaction that changed
    nothing must not dirty a tracked file, or every fold produces a noise
    commit."""
    path = Path(path)
    body = json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True, allow_nan=False) + '\n'
    try:
        if path.read_text() == body:
            return False
    except (OSError, UnicodeDecodeError):
        pass
    atomic_json_replace(path, value, indent=2, sort_keys=True, ensure_ascii=True,
                        allow_nan=False, trailing_newline=True)
    return True


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


# --------------------------------------------------------------- the one key

def measurement_key(r):
    """The key a measurement is stored under, as a JSON-ready dict.

    The key is the measurement's identity: `model`, the revision it was built
    from (tlx only - TLC has no revision dimension), the machine it is only
    valid on (type and architecture), how it was run (`mode`, `args`, the
    configuration `variant`/`env` and its limits) and by `tool`, how many
    `workers` ran it, and the input identity (`content_digest` plus the
    `tlc_version` a TLC row was measured with or a tlx row was compared
    against). A dimension the row does not state stays null - it is part of the
    key that way, so "measured with an unknown TLC" is not the same key as
    "measured with 1813307"."""
    c = r.get('configuration') or {}
    i = r.get('instance') or {}
    return {'tool': r.get('tool'), 'model': r.get('model'), 'revision': r.get('revision') or None,
            'instance_type': i.get('type'), 'instance_arch': i.get('arch'), 'mode': r.get('mode'),
            'args': list(c.get('args') or []), 'variant': c.get('variant'), 'env': c.get('env') or None,
            'cgroup_mib': c.get('cgroup_mib'), 'hogs': c.get('hogs') or 0, 'workers': r.get('workers'),
            'tlc_version': r.get('tlc_version'), 'content_digest': r.get('content_digest')}


def key_complete(key):
    """Whether every dimension this tool needs for a reusable baseline is known."""
    return all(key.get(d) is not None for d in KEY_REQUIRED.get(key.get('tool'), ()))


def key_id(key):
    """The key's identity: a digest of its distinguishing dimensions, or `None`
    when the key is incomplete (the caller keeps the row under its own identity
    then)."""
    if not key_complete(key):
        return None
    return digest({k: key[k] for k in KEY_IDENTITY[key['tool']]})


def store_stem(r):
    """The store file name of a row: its key, or `legacy-<row id>` when the key
    is not fully determined."""
    return key_id(measurement_key(r)) or 'legacy-' + r['id']


def evidence(r):
    """How much a row proves about its key, as a comparable tuple.

    A completed measurement is the key's measurement; among those the newest is
    the current one (a re-measurement supersedes the run it repeats). A row
    whose search did not finish is not a measurement of the key but the record
    of why the key has none, and the strongest such record is the current
    evidence - except between two timeouts, where the bound that was measured,
    not the date, states how much the tool needed: 14400 s says more than
    1800 s of it.
    """
    if (r.get('provenance') or {}).get('count_problems'):
        return (0, 0.0, r.get('date') or '')
    result = (r.get('counts') or {}).get('result')
    wall = (r.get('metrics') or {}).get('wall_s')
    if result in COMPLETE and wall:
        return (2, 0.0, r.get('date') or '')
    if result == 'timeout':
        return (1, wall or 0.0, r.get('date') or '')
    return (0, 0.0, r.get('date') or '')


def record_of_record(rows):
    """The one row a key stores: the strongest evidence, newest first on a tie."""
    return max(rows, key=lambda r: (evidence(r), r['id']))


def instance_info(machine, explicit=None):
    machine = machine or ''
    match = re.search(r'\b(SA\d+\.[A-Z0-9]+|ecs\.[\w.]+)\b', machine, re.I)
    arch = 'aarch64' if re.search(r'aarch64|arm64', machine, re.I) else 'x86_64' if re.search(r'x86[_-]64', machine, re.I) else None
    return {'type': explicit or (match.group(1) if match else None), 'arch': arch, 'description': machine or None}


def scalar(value):
    if isinstance(value, list):
        value = [x for x in value if isinstance(x, (float, int)) and not isinstance(x, bool) and math.isfinite(x)]
        return statistics.median(value) if value else None
    return value if isinstance(value, (int, float)) and not isinstance(value, bool) and math.isfinite(value) else None


def peak_rss(row):
    """A measurement's peak-RSS median in MiB, or None when it has none.

    Prefers a repeated TLC baseline's retained `tlc_samples`, whose per-run
    measurements are the evidence a stored aggregate may have summarised with
    an unknown sample; then the aggregate `rss_mib`/`maxrss_mib`/`rss` scalar or
    flat list; then the timed `samples` of a history written before `run` kept
    an aggregate RSS. Under `samples` and `tlc_samples`, only named RSS fields
    of sample dictionaries count: the disk lane reuses `samples` for telemetry
    vectors whose elapsed time and byte counts are not MiB. Peak RSS is a
    positive quantity, so zero, missing and non-finite entries are unknown -
    never a zero-byte footprint - and are dropped before the median. The median
    of what remains is the statistic the store publishes over the samples.
    """
    values = _named_rss(row.get('tlc_samples'))
    if values:
        return statistics.median(values)
    for key in ('rss_mib', 'maxrss_mib', 'rss'):
        values = _rss_numbers(row.get(key))
        if values:
            return statistics.median(values)
    values = _named_rss(row.get('samples'))
    return statistics.median(values) if values else None


def _rss_numbers(value):
    """The finite positive numbers of an explicit RSS scalar or flat list."""
    if isinstance(value, bool) or not isinstance(value, (int, float, list, tuple)):
        return []
    if isinstance(value, (int, float)):
        return [value] if math.isfinite(value) and value > 0 else []
    return [x for x in value if isinstance(x, (int, float)) and not isinstance(x, bool)
            and math.isfinite(x) and x > 0]


def _named_rss(samples):
    """The named RSS fields of timed sample dictionaries, never telemetry."""
    if not isinstance(samples, (list, tuple)):
        return []
    values = []
    for sample in samples:
        if not isinstance(sample, dict):
            continue
        for key in ('maxrss_mib', 'rss_mib', 'rss'):
            value = _rss_numbers(sample.get(key))
            if value:
                values.append(value[0])
                break
    return values


def args_of(value):
    return shlex.split(value) if isinstance(value, str) else value if isinstance(value, list) else []


def mode_of(args):
    return '-compile' if '-compile' in args else '-interp' if '-interp' in args else '-tlc' if '-tlc' in args else 'default'


def category_of(model, source, mode, workers, args=()):
    cats = ['external' if model.startswith('ext/') else 'corpus']
    if mode == '-compile':
        cats.append('compiled')
    if mode == '-interp':
        cats.append('interpreter')
    if 'live' in (source + model).lower() or 'ClockSettles' in model or 'RaftMongoT4' in model:
        cats.append('liveness')
    if workers > 1 or 'scal' in source or 'profile-' in source:
        cats.append('scaling')
    if 'disk' in source or '-maxmem' in args or 'maxmem' in source:
        cats.append('beyond-memory')
    if 'trace' in (source + model).lower():
        cats.append('trace-validation')
    return cats


def supplied_revision(header, variant):
    """The revision an artifact states for `variant`, or None when it states
    none: `(revision, source)`.

    HARNESS-19: the label of an external binary ("new", "after", "fix") and the
    runner checkout's own commit never identify the executable that was
    measured. A revision is adopted only when the artifact states it, through
    `bin_revs` (written by `bench ab --bin-rev`, or merged in from a cloud
    receipt) or the legacy top-level string keyed by the variant that a
    `base`/`before` comparison carries. The returned source names where the
    revision came from; a revision the receipt's `bench_bins` states is recorded
    as such."""
    revs = header.get('bin_revs')
    if isinstance(revs, dict) and isinstance(revs.get(variant), str):
        receipt = header.get('bin_revs_receipt')
        return revs[variant], f'cloud receipt {receipt}' if isinstance(receipt, str) else 'artifact'
    if isinstance(header.get(variant), str):
        return header[variant], 'artifact'
    return None, None


def receipt_revisions(root=ROOT):
    """The external-binary revisions a cloud receipt proves for the bench
    artifacts the launch ran, as `{source: (receipt name, {variant: revision})}`.

    A receipt names the artifact it wrote with `--out`, and its `bench_bins`
    state the revision of each external binary the launch fetched. An artifact's
    `--bin LABEL=PATH` whose PATH sits under `bench-bins/<name>/` is that
    binary, so LABEL adopts <name>'s revision. Only a revision the receipt's
    `bench_bins` carries is adopted, never the runner checkout's own revision:
    a variant the receipt does not pin stays unknown (HARNESS-19)."""
    found = {}
    for receipt in sorted((Path(root) / 'target' / 'bench').glob('*/cloud.json')):
        try:
            h = json.loads(receipt.read_text())
        except (OSError, ValueError):
            continue
        pinned = {b.get('name'): b.get('rev') for b in h.get('bench_bins') or []
                  if isinstance(b, dict) and isinstance(b.get('rev'), str)}
        for command in h.get('bench') or []:
            if not isinstance(command, str):
                continue
            tokens = shlex.split(command)
            target = None
            for i, token in enumerate(tokens):
                if token == '--out' and i + 1 < len(tokens):
                    target = tokens[i + 1]
                elif token.startswith('--out='):
                    target = token.partition('=')[2]
            if not target:
                continue
            revs = {}
            for i, token in enumerate(tokens):
                if token != '--bin' or i + 1 >= len(tokens):
                    continue
                label, _, path = tokens[i + 1].partition('=')
                name = re.search(r'(?:^|/)bench-bins/([^/]+)/', path)
                if label and name and name.group(1) in pinned:
                    revs[label] = pinned[name.group(1)]
            if revs:
                found[target] = (receipt.parent.name, revs)
    return found


# The archive locator: an artifact removed from the working tree stays readable
# through the revision and the per-file SHA-256 the migration inventory pins, so
# `bench/migration.json` is a citation a reader can check without this checkout
# (DOC-06, DOC-05). The digest covers the artifact's own bytes, including the
# profile counters, prose and per-sample detail the canonical schema does not
# carry, so nothing that was recorded only in the raw file is lost with it.
ARCHIVE_INVENTORY = 'bench/migration.json'
_PINNED_REVISION = re.compile(r'^[0-9a-f]{40}$')
_ARCHIVED_PATH = re.compile(r'^bench/[A-Za-z0-9._/-]+$')


class ArchiveError(Exception):
    """A source the inventory records as archived does not resolve to its bytes."""


def archive_inventory(root=ROOT):
    """`(revision, {source: sha256})` pinned for archived artifacts.

    `(None, {})` when the inventory pins no archive, which is not an error: it
    only means no artifact has been retired yet. A malformed entry is reported
    by `archived_bytes` when that source is actually asked for."""
    try:
        h = json.loads((Path(root) / ARCHIVE_INVENTORY).read_text())
    except (OSError, ValueError):
        return None, {}
    a = h.get('archived_sources')
    if not isinstance(a, dict) or not isinstance(a.get('sha256'), dict):
        return None, {}
    revision = a.get('revision')
    return (revision if isinstance(revision, str) else None,
            dict(a['sha256']))


def archived_bytes(root, source, run=subprocess.run):
    """The bytes `source` had at the archive's pinned revision.

    `None` when the inventory does not pin `source`: an artifact that was never
    archived is the caller's own missing-file problem, not a locator failure.
    Raises `ArchiveError` when it does pin it and the revision does not resolve
    or the bytes differ from the recorded SHA-256 - a locator that does not
    resolve is refused, never silently downgraded to "source absent"
    (HARNESS-18, HARNESS-21).

    `git show` needs no working-tree file, so the archive resolves the same way
    in a checkout, inside a merge gate and on an instance fetched with
    `git archive`."""
    revision, pinned = archive_inventory(root)
    if source not in pinned:
        return None
    if not revision or not _PINNED_REVISION.match(revision) or not _ARCHIVED_PATH.match(source):
        raise ArchiveError(f'malformed pinned revision or path in {ARCHIVE_INVENTORY}')
    p = run(['git', 'show', f'{revision}:{source}'], cwd=str(root),
            capture_output=True, stdin=subprocess.DEVNULL)
    if p.returncode != 0:
        raise ArchiveError(f'not readable at the pinned revision {revision}')
    if hashlib.sha256(p.stdout).hexdigest() != pinned[source]:
        raise ArchiveError(f'bytes at the pinned revision {revision} do not match the recorded SHA-256')
    return p.stdout


def normalize(header, raw, source, pointer, *, model=None, mode=None, workers=None, revision=None, variant=None):
    """Normalize one sample or aggregate; all aggregates use medians, not minima."""
    args = args_of(raw.get('args', header.get('args')))
    # Disk histories record limits in the actual command rather than `args`.
    command = raw.get('cmd', '')
    if isinstance(command, str):
        for limit in re.findall(r'(?<!\S)(-maxmem\s+\S+|-Xmx\S+|-XX:MaxDirectMemorySize=\S+)', command):
            tokens = shlex.split(limit)
            if tokens[0] not in args:
                args = [*args, *tokens]
    model = model or raw.get('model') or raw.get('id')
    mode = mode or raw.get('mode') or (mode_of(args) if args else 'legacy-unknown')
    mode = {'compile': '-compile', 'interp': '-interp', 'tlc': '-tlc'}.get(mode, mode)
    if workers is None:
        workers = raw.get('workers')
        if not isinstance(workers, int):
            workers = int(args[args.index('-workers') + 1]) if '-workers' in args else header.get('workers', 1)
        if not isinstance(workers, int):
            workers = 1
    cpu = raw.get('cpu_s', raw.get('cpu'))
    wall = raw.get('walls', raw.get('wall_s', raw.get('wall', raw.get('median', raw.get('min')))))
    if 'tlc_samples' in raw:
        wall = [s.get('wall_s') for s in raw['tlc_samples']]
        cpu = [s.get('cpu_s') for s in raw['tlc_samples']]
    diagnostic = (header.get('diagnostic') or header.get('kind') == 'profile'
                  or raw.get('raw_stats') or '-stats' in args)
    r = {'schema_version': VERSION, 'tool': raw.get('tool', 'tlc' if mode == '-tlc' else 'tlx'), 'model': model, 'mode': mode, 'workers': workers,
         'category': list(dict.fromkeys([*(raw.get('category') or []), *(['diagnostic'] if diagnostic else []),
                                        *category_of(model or '', source, mode, workers, args)])),
         'revision': revision if revision is not None else header.get('commit'),
         'instance': instance_info(header.get('machine'), header.get('instance_type')),
         'date': raw.get('date') or header.get('date'),
         'content_digest': raw.get('content_digest'), 'tlc_version': raw.get('tlc_version') or
             (header.get('tla2tools') or {}).get('revision') or (header.get('tla2tools') or {}).get('short'),
         'counts': {k: raw.get(k) for k in COUNTS},
         'metrics': {'wall_s': scalar(wall), 'cpu_s': scalar(cpu), 'rss_mib': peak_rss(raw),
                     'instructions': scalar(raw.get('instructions', (raw.get('perf') or {}).get('instructions')))},
         'aggregation': raw.get('aggregation', 'median' if isinstance(wall, list) else 'single-or-legacy-scalar'),
         'samples': {'wall_s': wall if isinstance(wall, list) else [wall], 'cpu_s': cpu if isinstance(cpu, list) else [cpu]},
         'configuration': {'args': args, 'variant': variant, 'cgroup_mib': raw.get('cgroup_mib'),
                           'env': raw.get('env', header.get('env')), 'hogs': header.get('hogs', 0)},
         'baseline': None, 'provenance': {'source': source, 'pointer': pointer, 'legacy': not bool(raw.get('content_digest'))}}
    # Preserve the producer's mode-contract check, including earlier samples
    # and warm-ups. COMPLETE only describes termination, not correctness.
    # Absence means unchecked legacy evidence; [] means checked and matched.
    if 'tlc_samples' in raw:
        if raw.get('count_problems'):
            # Rejected repetitions are attempts, not a timing distribution.
            # Preserve the final attempt's timeout bound for slice ranking.
            r['metrics']['wall_s'] = scalar(raw.get('wall_s'))
            r['metrics']['cpu_s'] = scalar(raw.get('cpu_s'))
        elif any(s.get('cpu_s') is None for s in raw['tlc_samples']):
            r['metrics']['cpu_s'] = None
    for field in ('cache', 'sample_spread'):
        if field in raw:
            r['provenance'][field] = raw[field]
    if 'tlc_samples' in raw:
        r['provenance']['repetitions'] = {
            'requested': raw['tlc_repetitions'],
            'completed': sum(s.get('result') in COMPLETE for s in raw['tlc_samples'])}
    if 'count_problems' in raw:
        r['provenance']['count_problems'] = raw['count_problems']
    if 'compatibility' in raw:
        r['configuration']['compatibility'] = raw['compatibility']
    if header.get('suite') and type(header.get('repeat')) is int and header['repeat'] > 0:
        r['provenance']['repetitions'] = {
            'requested': header['repeat'],
            'completed': sum(scalar(x) is not None for x in r['samples']['wall_s'])}
    # An A/B row carries per-sample evidence (M05 keeps every child exit). When
    # the source records it, keep it: a sample the producer's guard rejected
    # (missing or verdict-mismatched exit, or an incompletely repeated set) must
    # not be adopted here either, so a canonical comparison cannot outrun the
    # raw guard (HARNESS-19, HARNESS-21).
    sample_results = raw.get('sample_result_exits')
    if isinstance(sample_results, list) and sample_results:
        r['provenance']['sample_results'] = sample_results
        completed = raw.get('completed_samples')
        if type(completed) is not int:
            completed = sum(1 for e in sample_results if exit_ok(e.get('result'), e.get('exit')))
        r['provenance']['repetitions'] = {'requested': len(sample_results), 'completed': completed}
    if 'measurement_revision' in raw and r['tool'] == 'tlc':
        r['revision'] = raw['measurement_revision']
    if 'measurement_date' in raw:
        r['date'] = raw['measurement_date']
    if raw.get('source'):
        r['provenance']['measurement_source'] = raw['source']
    if raw.get('baseline_id'):
        r['provenance']['reused_from'] = raw['baseline_id']
    if raw.get('metric_sources'):
        r['provenance']['metric_sources'] = raw['metric_sources']
    if isinstance(raw.get('raw_result'), dict):
        r['raw_result'] = raw['raw_result']
    elif 'tlc_samples' in raw:
        r['raw_result'] = {k: v for k, v in raw.items() if k != 'raw_result'}
    # Coverage attributes belong in the same row as the timing they describe:
    # they are only comparable for the run that produced them. A run without a
    # census leaves them absent, so that "unmeasured" never reads as a share of
    # zero (BENCH-01/6.4).
    cov = {k: raw[k] for k in COVERAGE_FIELDS if raw.get(k) is not None}
    native = raw.get('native_coverage') if raw.get('native_coverage') is not None else raw.get('coverage')
    if isinstance(native, dict):
        for k in COVERAGE_FIELDS:
            v = native.get(k)
            if v is None and k == 'host_s':
                v = native.get('host_time_s')
            if v is not None:
                cov.setdefault(k, v)
    for k, v in cov.items():
        r[k] = v
    ops = (raw.get('coverage') or {}).get('ops') if isinstance(raw.get('coverage'), dict) else None
    if isinstance(ops, list) and ops:
        r['coverage'] = {'ops': ops}
    # HARNESS-19: a variant label never identifies the measured binary. A
    # revision is adopted only when the artifact states it (`bin_revs`, or a
    # legacy top-level key); otherwise it stays unknown, however the row is
    # labelled.
    supplied, source_of = supplied_revision(header, variant)
    if variant and r['tool'] == 'tlx' and source.endswith('.json') and revision is None:
        r['revision'] = supplied
    if variant in ('base', 'before'):
        r['revision'] = supplied if supplied is not None else (
            header['base'].get('commit') if isinstance(header.get('base'), dict) else None)
    if supplied is not None and r['revision'] == supplied:
        r['provenance']['revision_source'] = source_of
    r['id'] = digest([source, pointer])[:24]
    validate(r)
    return r


def _fields(obj, allowed, where):
    """Refuse a field the schema does not define, and a defined-but-optional
    field carrying null instead of being absent: `null` means "unknown or
    unmeasured" for a dimension, and an attribute that does not apply to a row
    is absent, so the two cannot be confused by a reader."""
    if not isinstance(obj, dict):
        raise ValueError(f'{where} must be an object')
    unknown = sorted(set(obj) - set(allowed))
    if unknown:
        raise ValueError(f'unknown {where} field(s): {", ".join(unknown)}')


def validate(r):
    """The single validator every reader goes through (docs/benchmarking.md 6.1).

    Strict on purpose: `null` is a value ("unknown or unmeasured"), a field the
    row does not have is absent, and anything the schema does not name is
    refused rather than carried along unread.
    """
    if not isinstance(r, dict) or r.get('schema_version') != VERSION:
        raise ValueError('unsupported measurement schema_version')
    _fields(r, FIELDS, 'measurement')
    if not isinstance(r.get('model'), str) or not r['model']:
        raise ValueError('measurement needs model id')
    if r.get('tool') not in ('tlx', 'tlc'):
        raise ValueError('unknown measurement tool')
    if r.get('mode') not in MODES:
        raise ValueError('unknown measurement mode')
    if type(r.get('workers')) is not int or r['workers'] < 1:
        raise ValueError('workers must be a positive integer')
    # `configuration`, `aggregation` and `samples` are absent on rows written
    # before they existed, and an absent field means the row does not state it -
    # not that it states nothing. Requiring them would drop those measurements
    # from the store, which no schema change may do.
    for k in ('id', 'category', 'revision', 'date', 'instance', 'content_digest', 'tlc_version', 'counts',
              'metrics', 'provenance', 'baseline'):
        if k not in r:
            raise ValueError(f'missing measurement {k}')
    if not isinstance(r['id'], str) or not r['id']:
        raise ValueError('measurement needs an id')
    if not isinstance(r['category'], list) or not all(isinstance(c, str) for c in r['category']):
        raise ValueError('category must be a list of strings')
    for k in ('metrics', 'counts', 'instance', 'provenance', 'configuration', 'samples'):
        if k in r and not isinstance(r[k], dict):
            raise ValueError(f'{k} must be an object')
    _fields(r['instance'], INSTANCE_FIELDS, 'instance')
    _fields(r.get('configuration') or {}, CONFIGURATION_FIELDS, 'configuration')
    _fields(r['provenance'], PROVENANCE_FIELDS, 'provenance')
    if 'cache' in r['provenance']:
        cache = r['provenance']['cache']
        if (not isinstance(cache, dict) or cache.get('mode') not in ('fresh-per-model', 'shared-batch', 'inherited')
                or cache.get('initial_state') != ('empty' if cache['mode'] == 'fresh-per-model' else 'unknown')
                or type(cache.get('warmup')) is not bool):
            raise ValueError('invalid cache provenance')
    if 'sample_spread' in r['provenance']:
        spread = r['provenance']['sample_spread']
        if (not isinstance(spread, dict) or set(spread) != {'wall_s', 'cpu_s'}
                or any(v is not None and (type(v) not in (int, float) or not math.isfinite(v) or v < 0)
                       for v in spread.values())):
            raise ValueError('invalid sample spread')
    if 'count_problems' in r['provenance']:
        problems = r['provenance']['count_problems']
        if not isinstance(problems, list) or not all(isinstance(p, str) and p for p in problems):
            raise ValueError('provenance.count_problems must be a list of nonempty strings')
    raw = r.get('raw_result')
    if isinstance(raw, dict) and 'count_problems' in raw:
        if raw['count_problems'] != r['provenance'].get('count_problems'):
            raise ValueError('raw_result and provenance expectation diagnostics disagree')
    _fields(r['metrics'], METRICS, 'metrics')
    _fields(r['counts'], COUNTS, 'counts')
    for k in INSTANCE_FIELDS:
        if k not in r['instance']:
            raise ValueError(f'missing instance {k}')
    for k in ('source', 'pointer', 'legacy'):
        if k not in r['provenance']:
            raise ValueError(f'missing provenance {k}')
    for k in METRICS:
        if k not in r['metrics']:
            raise ValueError(f'missing metric {k}')
        x = r['metrics'][k]
        if x is not None and (not isinstance(x, (float, int)) or isinstance(x, bool) or not math.isfinite(x) or x < 0):
            raise ValueError(f'invalid metric {k}')
    for k in COUNTS:
        if k not in r['counts']:
            raise ValueError(f'missing count {k}')
    for k in ('generated', 'distinct', 'depth'):
        if r['counts'][k] is not None and (type(r['counts'][k]) is not int or r['counts'][k] < 0):
            raise ValueError(f'invalid count {k}')
    for k in COVERAGE_FIELDS:
        if k in r:
            x = r[k]
            if not isinstance(x, (float, int)) or isinstance(x, bool) or not math.isfinite(x) or x < 0:
                raise ValueError(f'invalid coverage attribute {k}')
    if 'coverage' in r:
        ops = r['coverage'].get('ops') if isinstance(r['coverage'], dict) else None
        _fields(r['coverage'], ('ops',), 'coverage')
        if not isinstance(ops, list) or not all(isinstance(o, dict) for o in ops):
            raise ValueError('coverage.ops must be a list of objects')
    return r


def record_path(r):
    """The one store file a row belongs in: the container of its tool, named by
    its key, or by its own identity when the key is not fully determined."""
    return f'{CONTAINER[r["tool"]]}/{store_stem(r)}.json'


def store_files(root=ROOT):
    """Every file of the store, in both of its containers."""
    return sorted(p for d in sorted(set(CONTAINER.values()))
                  for p in (Path(root) / d).glob('*.json'))


def _entry(r):
    return {'schema_version': VERSION, 'key': measurement_key(r), 'measurement': r}


def write_records(records, root=ROOT, *, replace=()):
    """Publish these rows' store files, and clear the named files that lost them.

    A transaction that stops producing a row must name its file in `replace`
    (as `tool/stem`); skipping it leaves a stale live measurement behind an
    empty source.
    """
    groups = {}
    for r in records:
        validate(r)
        groups.setdefault(record_path(r), []).append(r)
    for path in sorted(set(groups).union(replace)):
        rows = groups.get(path)
        target = Path(root) / path
        if not rows:
            if target.exists():
                target.unlink()
            continue
        dump(target, _entry(record_of_record(rows)))


def realign_store(records, root=ROOT):
    """Publish the whole derived store and remove every file it no longer holds.

    Migration's transaction: the store is derived, so a container that no
    source produces any more is removed rather than left as a live row. Returns
    the number of files written or removed.
    """
    root = Path(root)
    wanted = {record_path(r) for r in records}
    changed = 0
    groups = {}
    for r in records:
        validate(r)
        groups.setdefault(record_path(r), []).append(r)
    for path, rows in sorted(groups.items()):
        if dump(root / path, _entry(record_of_record(rows))):
            changed += 1
    for p in store_files(root):
        if p.relative_to(root).as_posix() not in wanted:
            p.unlink()
            changed += 1
    return changed


def store_lock(root=ROOT):
    """Serialize a whole store read-modify-write on its established lock path."""
    return file_lock(Path(root) / 'target/bench-records-locks/store.lock')


def load_store(root=ROOT):
    """Every stored row, in whichever of the store's file shapes it is in.

    Migration reads the store it is about to rewrite, so it must be able to read
    the previous container shape too (`{schema_version, records: [...]}`, and the
    retired baseline directory's `{key, measurement}`): refusing the store it is
    migrating is a deadlock. Every other reader uses `load_records`, which is
    strict about the one current shape.
    """
    out = []
    for p in store_files(root):
        h = json.loads(p.read_text())
        if 'records' in h:
            rows = h['records']
        elif 'measurement' in h and 'key' in h:
            rows = [h['measurement']]
        else:
            raise ValueError(f'{p.name}: unrecognized store file shape')
        for r in rows:
            # A row written under an older schema is read as the current one:
            # every field it has was carried forward unchanged, so the versions
            # differ in what a new row may also carry, not in what this one says.
            try:
                out.append(validate({**r, 'schema_version': VERSION}))
            except ValueError:
                # A file left behind by a schema older still than the fields it
                # lacks: never a measurement of record any more, and the
                # realignment that follows replaces or drops it. It is counted,
                # not read as a row.
                UNREADABLE.append(p.name)
    return out


# Store files the tolerant reader could not read (migration reports them).
UNREADABLE = []


def load_records(root=ROOT):
    """Every stored measurement, each file checked against its own key.

    A file whose key, filename and measurement disagree is refused: the store's
    identity is the key, so a file that drifts from it is not readable under the
    contract the store claims.
    """
    out = []
    for p in store_files(root):
        h = json.loads(p.read_text())
        if tuple(sorted(h)) != tuple(sorted(ENVELOPE)):
            raise ValueError(f'{p.name}: a store file holds exactly {", ".join(ENVELOPE)}')
        if h['schema_version'] != VERSION:
            raise ValueError(f'{p.name}: unsupported container version')
        r = validate(h['measurement'])
        if h['key'] != measurement_key(r):
            raise ValueError(f'{p.name}: key differs from its measurement')
        if p.stem != store_stem(r):
            raise ValueError(f'{p.name}: file name does not identify its key')
        out.append(r)
    ids = [r['id'] for r in out]
    if len(ids) != len(set(ids)):
        raise ValueError('duplicate measurement ids')
    return out
