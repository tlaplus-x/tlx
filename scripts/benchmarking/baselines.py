
"""The TLC side of the measurement store: reuse a valid TLC timing instead of recollecting it.

A TLC timing is a keyed artifact — TLC version, model, input digest, worker
count and instance type — and the cache is the only place a new one is
collected: `cached_tlc` holds the key's lock across collect-and-store, so two
concurrent lanes of one configuration share a single measurement rather than
racing for the same key (HARNESS-04, HARNESS-20). Equality of the model's
inputs is re-checked after collection, so a run that measured a changed model
cannot enter the cache under the old key.

`historical_match` and `attach_baselines` decide which stored TLC timing a
measurement may be compared against at all; a comparison that cannot state the
same hardware, verdict and input digest stays unattached instead of becoming a
number in the report (HARNESS-19, DOC-06).
"""
import hashlib
import json
from pathlib import Path
import re
import statistics
import time

from benchmarking import machine as bench_machine
from benchmarking.records import (BASELINES, COMPLETE, ROOT, STORE, VERSION, digest, dump, evidence, instance_info,
                                  exit_ok, key_complete, key_id, measurement_key, normalize, scalar, record_of_record, record_path,
                                  store_files, store_stem, write_records)
from harness.storage import file_lock
from tlxlib import CORPUS_ROOT_CWD, model_cwd


# The digest's name for a run that starts in the model's corpus root rather than
# next to its spec file (a logical location, never an absolute path). Only the
# deviation from the default enters the digest, so every model that runs where
# its inputs already are keeps the digest it was measured under.
ROOT_CWD_TOKEN = "corpus-root"


def _repetitions_complete(record):
    reps = record['provenance'].get('repetitions')
    return not reps or reps.get('completed', 0) >= reps.get('requested', 0)


def historical_match(tx, tc):
    """Historical comparison requires same hardware, workers, verdict and complete counts.

    A missing content digest remains visible as historical/unverified provenance;
    it does not make a reusable current baseline.
    """
    return (not tx['provenance'].get('count_problems') and not tc['provenance'].get('count_problems')
            and _repetitions_complete(tx)
            and tc.get('tool') == 'tlc' and tx['model'] == tc['model'] and tx['workers'] == tc['workers']
            and bool(tx['instance']['type']) and tx['instance']['type'] == tc['instance']['type']
            and tx['instance']['arch'] == tc['instance']['arch']
            and tx['configuration'].get('cgroup_mib') == tc['configuration'].get('cgroup_mib')
            and (not tx['tlc_version'] or not tc['tlc_version'] or tx['tlc_version'] == tc['tlc_version'])
            and tx['counts']['result'] in COMPLETE and tx['counts']['result'] == tc['counts']['result']
            and tx['counts']['distinct'] is not None and (tx['mode'] == 'default'
                or tx['configuration'].get('compatibility') is False or tx['counts']['distinct'] == tc['counts']['distinct'])
            and (not tx['content_digest'] or not tc['content_digest'] or tx['content_digest'] == tc['content_digest'])
            and tx['metrics']['wall_s'] and tc['metrics']['wall_s'])


def attach_baselines(records):
    baselines = [r for r in records if r.get('tool') == 'tlc']
    for tx in records:
        if tx.get('tool') == 'tlc':
            continue
        # Re-import can discover a mismatch in a previously paired row.
        # Recompute the link so rejected evidence cannot keep an old baseline.
        tx['baseline'] = None
        candidates = [tc for tc in baselines if historical_match(tx, tc)]
        if candidates:
            # Prefer a paired baseline, then the most recent known provenance.
            tc = max(candidates, key=lambda r: (r['provenance']['source'] == tx['provenance']['source'], r['date'] or '', r['id']))
            tx['baseline'] = tc['id']
    return records


def input_layout(model):
    """The layout component of a model's input identity, or `None` (fail closed).

    `cwd` states the directory a run starts in when it is not the spec's own -
    a model the corpus manifest marks `cwd: root` resolves its inputs from the
    corpus root (`tlxlib.model_cwd`). `inputs` keeps, under the relative names
    the model declares, the bytes staging resolves there: a changed trace file
    is a changed input. Both are relative, so a relocated but identical input
    keeps its identity, while a marked model without its root, an unknown `cwd`
    or a declared input that is not there has no identity at all instead of
    silently reusing another staging's evidence.

    Empty for a model that runs next to its spec and declares no inputs, which
    keeps every other model's digest - and the frozen report that cites it -
    unchanged.
    """
    cwd = model.get('cwd')
    if cwd is not None and cwd != CORPUS_ROOT_CWD:
        return None
    try:
        run_dir = model_cwd(model)
    except ValueError:
        return None
    if not run_dir:
        return {}
    layout = {}
    if cwd == CORPUS_ROOT_CWD:
        # The manifest names a run that does not start next to its spec: encode
        # its directory as a logical location, never an absolute path, so two
        # identical inputs hash alike wherever the checkout lives.
        layout['cwd'] = ROOT_CWD_TOKEN
    declared = model.get('inputs') or ()
    if declared:
        resolved = {}
        for name in declared:
            path = Path(run_dir) / name
            if not path.is_file():
                return None
            resolved[Path(name).as_posix()] = hashlib.sha256(path.read_bytes()).hexdigest()
        layout['inputs'] = resolved
    return layout


def content_digest(model):
    """Hash spec, config, local module dependency closure, semantic flags and layout.

    Relative names, never absolute checkout paths, enter the digest. Missing
    inputs fail closed. Standard/community jar bytes are part of the key. The
    run's effective working directory and the input files staging resolves from
    it are part of the identity too (`input_layout`): a run started somewhere
    else, or against a different trace, is a different measurement. So are the
    extra TLC arguments the oracle is collected with (`-fp 0`): they decide
    TLC's own counts, so two argument sets cannot share a key.
    """
    cfg, tla = Path(model['cfg']), Path(model['tla'])
    if not cfg.is_file() or not tla.is_file():
        return None
    layout = input_layout(model)
    if layout is None:
        return None
    files = {'config': hashlib.sha256(cfg.read_bytes()).hexdigest()}
    pending, seen = [tla], set()
    while pending:
        p = pending.pop()
        if p in seen:
            continue
        seen.add(p)
        text = p.read_text()
        files[p.name] = hashlib.sha256(p.read_bytes()).hexdigest()
        text = re.sub(r'\\\*[^\n]*|\(\*.*?\*\)', '', text, flags=re.S)
        names = re.findall(r'\bINSTANCE\s+(\w+)', text)
        for clause in re.findall(r'\bEXTENDS\s+([\w\s,]+)', text):
            names.extend(re.findall(r'\w+', clause.split('\n\n')[0]))
        for name in names:
            child = p.parent / (name + '.tla')
            if child.is_file():
                pending.append(child)
    community = ROOT / 'third_party/community/modules.jar'
    if community.is_file():
        files['community_modules'] = hashlib.sha256(community.read_bytes()).hexdigest()
    if model.get('scratch'):
        for sidecar in sorted(tla.parent.rglob('*')):
            if sidecar.is_file() and sidecar.suffix in ('.json', '.jsonl', '.ndjson', '.csv', '.txt') and 'states' not in sidecar.parts:
                files['data/' + sidecar.relative_to(tla.parent).as_posix()] = hashlib.sha256(sidecar.read_bytes()).hexdigest()
    body = {'files': files, 'flags': model.get('flags') or [], 'features': model.get('features') or [],
            'constraints': model.get('measurement_constraints')}
    if layout:
        body['layout'] = layout
    if tlc_args := [str(a) for a in model.get('tlc_args') or ()]:
        body['tlc_args'] = tlc_args
    return digest(body)


def baseline_key(model, workers, version, instance, content, arch=None):
    """The unified key of a TLC measurement.

    TLC is run one way, so the dimensions tlx adds are its constants: no
    revision, mode `-tlc`, no arguments, no variant and no environment.
    """
    return measurement_key({'tool': 'tlc', 'model': model, 'mode': '-tlc', 'workers': workers, 'revision': None,
                            'instance': {'type': instance, 'arch': arch}, 'content_digest': content,
                            'tlc_version': version, 'configuration': {}})


def reusable(entry):
    """Whether a stored entry is the key's baseline: a finished search with a
    wall time, under a key that states every dimension (6.5)."""
    key, m = entry['key'], entry['measurement']
    return (not m['provenance'].get('count_problems')
            and all(key.get(x) for x in ('tlc_version', 'model', 'content_digest', 'workers', 'instance_type'))
            and m['counts']['result'] in COMPLETE and bool(m['metrics']['wall_s']))


def baseline_file(record, root=ROOT):
    """The store file and key a TLC record belongs to.

    A key that cannot be fully determined (a historical row with no TLC version
    or no input digest) still keeps its own file, named after the measurement:
    two such rows must not collapse into one, because each is the only record
    of why that measurement exists at all.
    """
    key = measurement_key(record)
    return Path(root) / record_path(record), key


def store_entry(record):
    """The store row a record would be written as."""
    return {'schema_version': VERSION, 'key': measurement_key(record), 'measurement': record}


def stronger(entry, stored):
    """True when `entry` states at least as much about its key as `stored` does.

    A reusable measurement is the key's baseline and never yields to another
    row. Everything else is a record of why the key has no measurement, and the
    strongest such record is the current evidence - see `records.evidence`.
    """
    return not reusable(stored) and (evidence(entry['measurement']), entry['measurement']['id']) \
        > (evidence(stored['measurement']), stored['measurement']['id'])


def seeded_store(records, root=ROOT):
    """The store `seed_baselines` would leave behind for these records, unread and unwritten."""
    store = {}
    for r in records:
        if r.get('tool') != 'tlc':
            continue
        path, _ = baseline_file(r, root)
        entry = store_entry(r)
        if path not in store or stronger(entry, store[path]):
            store[path] = entry
    return store


def seed_baselines(records, root=ROOT):
    """Import every TLC timing, including incomplete runs, without laundering provenance."""
    for r in records:
        if r.get('tool') != 'tlc':
            continue
        path, _ = baseline_file(r, root)
        entry = store_entry(r)
        if not path.exists():
            dump(path, entry)
            continue
        stored = json.loads(path.read_text())
        # A stored row that is not reusable (timeout, error, skipped) is not a
        # measurement, and the key already pins the model digest, TLC version,
        # workers and instance. A stronger record for that same key therefore
        # supersedes it - a reusable measurement always, and otherwise the newer
        # record of the same kind: without this the store is first-write-wins,
        # `find_baseline` keeps reporting the key as missing, no re-measurement
        # can replace the stale row, and a key that was re-run at a longer
        # timeout keeps reporting the shorter bound it outgrew.
        if stronger(entry, stored):
            dump(path, entry)


def instance_arches(root=ROOT):
    """`{instance_type: {arch}}` as recorded in the store, read once per process.

    A TLC key names the machine type and its architecture; a lookup that only
    knows the type (a coverage report for a cloud instance type this checkout
    was not collected on) resolves the architecture the store recorded rather
    than guessing this machine's.
    """
    global _ARCHES
    if _ARCHES is None or _ARCHES[0] != str(root):
        found = {}
        for p in store_files(root):
            try:
                k = json.loads(p.read_text())['key']
            except (OSError, ValueError, KeyError):
                continue
            if k.get('tool') == 'tlc' and k.get('instance_type'):
                found.setdefault(k['instance_type'], set()).add(k.get('instance_arch'))
        _ARCHES = (str(root), found)
    return _ARCHES[1]


_ARCHES = None


# TLC lookup honors TLC's distinguishing key dimensions plus tool and hardware
# invariants, ignoring historical tlx-side metadata (revision, args, env,
# variant) carried by frozen legacy records at the same TLC filename.
TLC_KEY_FIELDS = ('tool', 'mode', 'tlc_version', 'model', 'content_digest', 'workers',
                  'instance_type', 'instance_arch', 'cgroup_mib', 'hogs')


def same_tlc_key(a, b):
    return all(a.get(k) == b.get(k) for k in TLC_KEY_FIELDS)


def stored_baseline(model, workers, *, version, instance, root=ROOT, arch=None):
    """The stored entry of a key as written, reusable or not (None if never stored).

    `find_baseline` answers only for a reusable measurement; coverage and cause
    reporting also need the unreusable rows (timeout, error, skipped) that the
    store keeps, so both readers share this one path and key rule.
    """
    content = content_digest(model)
    arches = [arch] if arch is not None else sorted(instance_arches(root).get(instance) or {None}, key=str)
    for a in arches:
        key = baseline_key(model['id'], workers, version, instance, content, arch=a)
        if not key_complete(key):
            continue
        p = Path(root) / (BASELINES + '/' + key_id(key) + '.json')
        if p.exists():
            b = json.loads(p.read_text())
            if b.get('schema_version') == VERSION and same_tlc_key(b['key'], key):
                return b
    return None


def find_baseline(model, workers, *, version, instance, root=ROOT, arch=None):
    b = stored_baseline(model, workers, version=version, instance=instance, root=root, arch=arch)
    return b if b is not None and reusable(b) else None


def raw_baseline(b):
    r = b['measurement']
    return {**r.get('raw_result', {}), **r['counts'], 'wall_s': r['metrics']['wall_s'], 'cpu_s': r['metrics']['cpu_s'],
            'maxrss_mib': r['metrics']['rss_mib'], 'baseline_id': r['id'], 'content_digest': r['content_digest'],
            'tlc_version': r['tlc_version'], 'date': r['date'], 'measurement_revision': r['revision']}


def collect_samples(collect, repetitions, workers):
    """Retain every attempt; only a complete, consistent set is a timing."""
    samples = []
    problems = []
    for i in range(repetitions):
        sample = collect()
        samples.append(sample)
        if (sample.get('result') not in COMPLETE or (scalar(sample.get('wall_s')) or 0) <= 0
                or not exit_ok(sample.get('result'), sample.get('exit'))):
            problems.append(f'sample {i + 1}: incomplete TLC timing')
            break
        fields = ['result', 'violated']
        if workers == 1 or sample['result'] == 'success':
            fields += ['distinct', 'generated', 'depth']
        if any(sample.get(k) != samples[0].get(k) for k in fields):
            problems.append(f'sample {i + 1}: TLC results disagree')
    raw = {**samples[-1], 'tlc_samples': samples, 'aggregation': 'median',
           'count_problems': problems, 'tlc_repetitions': repetitions}
    if problems:
        raw['aggregation'] = 'last-attempt'
        raw['result'] = samples[-1].get('result') if samples[-1].get('result') not in COMPLETE else 'error'
        return raw
    for field in ('wall_s', 'cpu_s', 'maxrss_mib'):
        values = [r.get(field) for r in samples]
        raw[field] = statistics.median(values) if all(v is not None for v in values) else None
    raw['sample_spread'] = {
        field: (max(values) - min(values)) / raw[field] if raw[field] else None
        for field in ('wall_s', 'cpu_s')
        for values in [[r.get(field) for r in samples]]}
    return raw


def cached_tlc(model, workers, collect, *, root=ROOT, version=None, instance=None, repetitions=1):
    """The sole performance-TLC collection boundary; a valid key never invokes collect."""
    if type(repetitions) is not int or repetitions < 1:
        raise ValueError("TLC repetitions must be a positive integer")
    if version is None or instance is None:
        version = version or bench_machine.tla2tools_info().get('revision') or bench_machine.tla2tools_info().get('short')
        instance = instance or instance_info(bench_machine.machine_desc())['type']
    machine = __import__('platform').machine()
    arch = instance_info(machine, instance)['arch']
    content = content_digest(model)
    lockpath = Path(root) / 'target/tlc-baseline-locks' / (digest(baseline_key(model['id'], workers, version, instance, content, arch=arch)) + '.lock')
    with file_lock(lockpath):
        if b := find_baseline(model, workers, root=root, version=version, instance=instance, arch=arch):
            return raw_baseline(b)
        raw = collect_samples(collect, repetitions, workers) if repetitions > 1 else collect()
        if content_digest(model) != content:
            raise ValueError('benchmark model inputs changed during TLC baseline collection')
        h = {'date': time.strftime('%Y-%m-%d %H:%M:%S'), 'instance_type': instance,
             'tla2tools': {'revision': version}, 'machine': machine}
        key = baseline_key(model['id'], workers, version, instance, content, arch=arch)
        if not key_complete(key):
            raise ValueError('a collected TLC baseline needs a complete key')
        stem = key_id(key)
        # (The measurement carries the key's TLC version, not the version
        # string TLC printed, which `raw_result` keeps.)
        r = normalize(h, {**raw, 'content_digest': content, 'tlc_version': version, 'raw_result': raw},
                      f'{BASELINES}/{stem}.json', '/measurement', model=model['id'], mode='-tlc', workers=workers)
        r['provenance']['legacy'] = False
        b = store_entry(r)
        if reusable(b):
            write_records([r], root)
        return raw_baseline(b)
