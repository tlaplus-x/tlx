#!/usr/bin/env python3
"""Native coverage census (static IR and optional measured search evaluations).

coverage.py --dynamic --source corpus --max-runtime 1 --timeout 20 -j 3 --out target/native-small.json
coverage.py --dynamic --source all --sizes all --timeout 120 --deadline-min 50 --out bench/native-census.json

The second command belongs on the cloud. Selection uses manifests, including
missing inputs and unsupported models, rather than successful TLC oracle rows.
No TLC process is launched. Instrumented host times are diagnostic elapsed time,
not CPU timings or an additive partition of search time.
"""
import argparse
import collections
import concurrent.futures
import contextlib
import json
import os
import re
import shutil
import time

import tempdirs
from tlxlib import (ROOT, ACTION_REPORT, NATIVE_REPORT, PRED_REPORT, mode_args, model_cwd,
                    add_profile_args, build_tlx, profile_of, tlx_env, run_proc)
from tlc import DEFAULT_JOBS

KINDS = ('actions', 'invariants', 'action_properties')
GRACE = 1.0
TIMEOUT_GRACE = 5.0


def dynamic_report(stats):
    """Exact evaluation counts; time share uses sampled search thread-seconds.

    Include every layout/escape version, once. Native calls can contain native
    runtime helpers; only interpreter/closure IR/host region entry disqualifies
    an evaluation. Init and liveness graph reconstruction are outside this metric.
    """
    by_kind = {}
    known = bool(stats)
    for kind in KINDS:
        rows = stats.get(kind, [])
        calls = sum(sum(r.get('calls', {}).values()) for r in rows)
        native = sum(r.get('fully_native', 0) for r in rows)
        known = known and all('fully_native' in r for r in rows)
        by_kind[kind] = {'evaluations': calls, 'fully_native': native, 'functions': rows}
    total = sum(r['evaluations'] for r in by_kind.values())
    native = sum(r['fully_native'] for r in by_kind.values())
    regions = [r for k, rows in stats.items() if k.startswith('native_regions_') for r in rows
               if r.get('context') != 'Init']
    host_s = sum(r['time_s'] for r in regions)
    units_s = stats.get('units_time_est_s', 0)
    return {'evaluations': total, 'fully_native': native,
            'native_share': native / total if known and total else None,
            'host_calls': sum(r['calls'] for r in regions), 'host_time_s': host_s,
            'host_time_share': host_s / units_s if units_s and stats else None,
            'search_thread_s_est': units_s, 'by_kind': by_kind, 'regions': regions,
            'adaptive_tiers': [row for key, row in stats.items() if key.startswith('adaptive_tiers_')],
            'interrupted': stats.get('interrupted', False)}


def static_report(out):
    nodes = collections.Counter()
    histogram = []
    for m in re.finditer(r'(?:compile|coverage): node (typed|boxed|interpreted)\s+(\d+) (.*?) \| (.*)', out):
        cls, n, kind, args = m.groups()
        nodes[cls] += int(n)
        histogram.append({'representation': cls, 'kind': kind, 'arguments': args, 'nodes': int(n),
                          'reason': {'typed': 'typed representation (backend support independent)',
                                     'boxed': 'boxed operation or value', 'interpreted': 'unsupported lowering'}[cls]})
    closure = [{'function': m.group(1), 'reason': m.group(2)} for m in
               re.finditer(r'cgen: ((?:function|action|invariant|action property) .*?) not native: (.*)', out)]
    a = ACTION_REPORT.search(out)
    native = NATIVE_REPORT.search(out)
    return {'reported': bool(a), 'nodes': {k: nodes[k] for k in ('typed', 'boxed', 'interpreted')},
            'histogram': histogram, 'closure_functions': closure,
            'action_summary': list(map(int, a.groups())) if a else None,
            'native_summary': list(map(int, native.groups())) if native else None,
            'predicate_summary': {m.group(1): list(map(int, m.groups()[1:])) for m in PRED_REPORT.finditer(out)}}


def lowering_family(operation):
    op = operation.lower()
    if op.startswith('unattributed execution path:'):
        return 'Execution tier selection or runtime fallback (inspect function)'
    if any(x in op for x in ('sort', 'selectseq')):
        return 'Sequence sorting and filtering'
    if any(x in op for x in ('cardinality', 'finiteset', 'bag')):
        return 'FiniteSets and Bags'
    if any(x in op for x in ('choose', 'quant', 'exists', 'forall')):
        return 'Quantifiers and CHOOSE'
    symbol = op.removeprefix('valop ').removeprefix('interp builtin ')
    if any(x in op for x in ('\\in', '\\notin', '\\subseteq', 'compare')) or symbol in ('eq', 'ne', 'lt', 'le', 'gt', 'ge', '=', '#', '<', '<=', '>', '>='):
        return 'Heterogeneous comparison and membership'
    if symbol in ('domain', '@@', ':>'):
        return 'Functions and records with dynamic values'
    if any(x in op for x in ('\\cup', '\\cap', 'union', 'set', '\\\\')):
        return 'Set algebra and construction on dynamic elements'
    if any(x in op for x in ('seq', 'tuple', 'append', 'head', 'tail', 'subseq', 'valop len')):
        return 'Sequences with dynamic elements'
    if any(x in op for x in ('fcn', 'fnapp', 'map', 'apply', 'field', 'record', 'except')):
        return 'Functions and records with dynamic values'
    if 'str' in op:
        return 'Strings'
    return 'Other operations (inspect IR root)'


def rank_operations(models):
    ranked = {}
    for m in models:
        for r in m.get('dynamic', {}).get('regions', []):
            key = (r['operation'], tuple(r['arguments']), 'host_region')
            row = ranked.setdefault(key, {'operation': key[0], 'arguments': list(key[1]), 'models': set(),
                                          'calls': 0, 'time_s': 0, 'attribution': 'host_region', 'executed_models': set(), 'family': lowering_family(key[0])})
            row['models'].add(m['id'])
            if r['calls']:
                row['executed_models'].add(m['id'])
            row['calls'] += r['calls']
            row['time_s'] += r['time_s']
        for f in m.get('dynamic', {}).get('closure_evaluations', []):
            blockers = f.get('blockers') or ['unattributed execution path: ' + f['function']]
            # A function's evaluation count is attributed to its complete
            # rejection reason, never multiplied by the number of IR nodes.
            reason = '; '.join(sorted(set(blockers)))
            key = (reason, (), 'closure_function')
            row = ranked.setdefault(key, {'operation': reason, 'arguments': [], 'models': set(),
                                          'calls': 0, 'time_s': None, 'attribution': 'closure_function',
                                          'executed_models': set(), 'family': lowering_family(reason)})
            row['models'].add(m['id'])
            calls = sum(f['calls'].values())
            if calls:
                row['executed_models'].add(m['id'])
            row['calls'] += calls
    return [{**r, 'models': sorted(r['models']), 'executed_models': sorted(r['executed_models'])} for r in sorted(ranked.values(), key=lambda r: (-(r['time_s'] or 0), -r['calls'], r['operation']))]



def select_models(a):
    import corpus
    selected = {}
    if a.source in ('corpus', 'all'):
        selected.update((m['id'], m) for m in corpus.models(a.max_runtime))
    if a.source in ('external', 'all'):
        sizes = corpus.EXTERNAL_TIERS if a.sizes == 'all' else a.sizes.split(',')
        selected.update((m['id'], m) for m in corpus.external_models(sizes))
    if a.source in ('suite', 'all'):
        import bench
        from benchmarking import bench_suite
        for m in bench_suite.load_manifest()['models']:
            if a.sizes != 'all' and m['size'] not in a.sizes.split(','):
                continue
            mid = m['id']
            try:
                selected[mid] = bench_suite.resolve_model(bench, mid)
            except (KeyError, ValueError, OSError) as e:
                selected[mid] = {'id': mid, 'selection_error': str(e)}
    rows = [m for k, m in sorted(selected.items()) if a.filter in k]
    priorities = [p for p in a.prioritize.split(',') if p]
    return sorted(rows, key=lambda m: (next((i for i, p in enumerate(priorities) if p in m['id']), len(priorities)), m['id']))


def run(m, timeout, binary, dynamic=False):
    """A bounded subprocess, with scratch copies for models that write files."""
    if m.get('selection_error') or any(not os.path.isfile(m.get(k, '')) for k in ('tla', 'cfg')):
        return {'id': m['id'], 'status': 'missing input', 'error': m.get('selection_error'),
                'static': static_report(''), 'dynamic': dynamic_report({})}
    with tempdirs.TemporaryDirectory(prefix='tlx-coverage-', owner_root=ROOT) as tmp:
        run_cwd = model_cwd(m)
        if m.get('scratch'):
            model_dir = os.path.join(tmp, 'spec')
            shutil.copytree(os.path.dirname(m['tla']), model_dir)
            shutil.copyfile(m['cfg'], os.path.join(model_dir, os.path.basename(m['cfg'])))
            m = {**m, 'tla': os.path.join(model_dir, os.path.basename(m['tla'])),
                 'cfg': os.path.join(model_dir, os.path.basename(m['cfg']))}
            run_cwd = model_dir
        path = os.path.join(tmp, 'stats.json')
        args = [*(['-maxmem', '2048'] if dynamic else ['-fpmem', '64']), '-workers', '1', '-tlc', *m.get('flags', [])]
        if m.get('flags'):
            args += ['-seed', '1']
        if dynamic:
            args += ['-stats', f'json={path}']
        cmd = [binary, 'check', m['tla'], '-config', m['cfg'], *mode_args(binary, args, mode='compile')]
        env = tlx_env(classpath=True, extra={'TLX_COVERAGE': '1', 'TLX_CGEN_DEBUG': '1', 'TLX_NATIVE_SYNC': '1'})
        reported = []
        def read(line):
            if not reported and 'actions lowered' in line and 'IR nodes' in line:
                reported.append(time.monotonic())
        p = run_proc(cmd, timeout, env=env, cwd=run_cwd, on_line=None if dynamic else read,
                     stop_when=None if dynamic else lambda: reported and time.monotonic() > reported[0] + GRACE,
                     grace=TIMEOUT_GRACE if dynamic else 0, errors='replace', raise_timeout=False)
        # Streaming capture kills immediately; TERM allows normal spill cleanup.
        # TERM also requests best-effort partial stats; absent evidence remains unknown.
        out = p.stdout + (p.stderr or '')
        stats, stats_error = {}, None
        if os.path.isfile(path):
            try:
                with open(path) as f:
                    stats = json.load(f)
            except (OSError, ValueError) as error:
                stats_error = str(error)
        from tlc import parse
        parsed = parse(out, p.wall, p.returncode)
        status = 'timeout' if p.timed_out else 'stats error' if stats_error else parsed.get('result', 'unknown')
        if not dynamic and ACTION_REPORT.search(out):
            status = 'static only'
        # A timeout's partial counters are not a complete model measurement.
        d = dynamic_report(stats)
        if stats.get('interrupted') or p.timed_out or status in ('unknown', 'error', 'compile failure', 'killed', 'stats error'):
            d['partial_native_share'] = d['native_share']
            d['partial_host_time_share'] = d['host_time_share']
            d['native_share'] = d['host_time_share'] = None
        d['complete'] = not stats.get('interrupted', False) and status not in ('timeout', 'unknown', 'error', 'compile failure', 'killed', 'stats error')
        static = static_report(out)
        closure = []
        for kind, counts in d['by_kind'].items():
            for f in counts['functions']:
                calls = {p: n for p, n in f.get('calls', {}).items() if p in ('ir', 'interp', 'fallback') and n}
                if calls:
                    closure.append({'kind': kind, 'function': f['name'], 'calls': calls,
                                    'blockers': [r['reason'] for r in static['closure_functions']
                                                 if r['function'].endswith(' ' + f['name'])]})
        d['closure_evaluations'] = closure
        return {'id': m['id'], 'status': status, 'wall_s': p.wall, 'static': static,
                'dynamic': d, 'output': out, 'stats': stats, 'result': parsed, **({'stats_read_error': stats_error} if stats_error else {})}


# The census is a measurement like any other, so it is stored like one: the
# coverage attributes live in the same row as the timing they were taken with,
# and the environment that decides them (`TLX_MIXED_ADAPT`, the layout and
# pre-run summary switches this driver sets) is part of the row's key. Without
# that, a share measured under one adaptive tiering sits next to one measured
# under another and neither is reproducible.
CENSUS_ENV = {'TLX_COVERAGE': '1', 'TLX_CGEN_DEBUG': '1', 'TLX_NATIVE_SYNC': '1'}
CENSUS_OPS_LIMIT = 40


def census_ops(d, limit=CENSUS_OPS_LIMIT):
    """The per-operation coverage rows of one censused model.

    This is what makes the adaptive tier chooser auditable rather than a black
    box: for every function the run saw, how many of its calls took each path
    (`native`/`mixed`/`ir`/`interp`/`fallback`) and how many were fully native,
    next to the host regions and their elapsed time. A share that moved between
    two runs can then be attributed to the functions whose tier moved.
    """
    ops = []
    for kind, counts in (d.get('by_kind') or {}).items():
        for f in counts.get('functions', []):
            paths = {p: n for p, n in (f.get('calls') or {}).items() if n}
            ops.append({'kind': kind, 'operation': f.get('name'), 'arguments': [], 'attribution': 'evaluation',
                        'calls': sum(paths.values()), 'fully_native': f.get('fully_native'),
                        'paths': paths, 'time_s': None})
    for reg in d.get('regions') or []:
        ops.append({'kind': 'region', 'operation': reg.get('operation'), 'arguments': reg.get('arguments') or [],
                    'attribution': 'host_region', 'calls': reg.get('calls'), 'fully_native': None,
                    'paths': {}, 'time_s': reg.get('time_s')})
    ops.sort(key=lambda o: (-(o['time_s'] or 0), -(o['calls'] or 0), o['kind'], o['operation'] or ''))
    return ops[:limit]


def census_row(header, r, env, tlc_version, root):
    """One stored measurement for a censused model: its timing, its verdict and
    its coverage attributes, keyed by the run that produced them."""
    from benchmarking.records import STORE, digest, normalize, store_stem, validate
    d = r['dynamic']
    parsed = r.get('result') or {}
    counts = {k: parsed.get(k) for k in ('distinct', 'generated', 'depth')}
    counts['result'] = parsed.get('result')
    raw = {'tool': 'tlx', 'model': r['id'], 'mode': '-compile', 'workers': 1, 'wall_s': r.get('wall_s'),
           'cpu_s': None, 'rss_mib': None, 'instructions': None, **counts, 'args': header.get('args'),
           'env': env, 'tlc_version': tlc_version, 'content_digest': header.get('content_digest'),
           'native_share': d.get('native_share'), 'host_time_share': d.get('host_time_share'),
           'host_s': d.get('host_time_s'), 'host_calls': d.get('host_calls'), 'evaluations': d.get('evaluations'),
           'fully_native': d.get('fully_native'), 'search_thread_s_est': d.get('search_thread_s_est')}
    if ops := census_ops(d):
        raw['coverage'] = {'ops': ops}
    row = normalize({**header, 'diagnostic': True}, raw, '', '/measurement', model=r['id'],
                    mode='-compile', workers=1)
    source = f'{STORE}/{store_stem(row)}.json'
    row['provenance']['source'] = source
    row['id'] = digest([source, '/measurement'])[:24]
    row['provenance']['legacy'] = False
    return validate(row)


def census_env():
    """The environment the coverage attributes depend on, recorded with them."""
    env = dict(CENSUS_ENV)
    for name in ('TLX_MIXED_ADAPT',):
        if os.environ.get(name) is not None:
            env[name] = os.environ[name]
    return env


def census_header(models, a, root=ROOT):
    """The run-level header of a census: which checkout, machine, TLC build and
    arguments it was taken with, plus each model's input digest."""
    from benchmarking import machine as bench_machine
    from benchmarking.baselines import content_digest
    from benchmarking.records import instance_info
    machine = bench_machine.machine_desc()
    args = [*(['-maxmem', '2048'] if a.dynamic else ['-fpmem', '64']), '-workers', '1', '-tlc']
    return {'commit': __import__('tlxlib').git('rev-parse', 'HEAD'), 'date': time.strftime('%Y-%m-%d %H:%M:%S'),
            'machine': machine, 'instance_type': instance_info(machine)['type'], 'args': args,
            'tla2tools': bench_machine.tla2tools_info(),
            'content_digest': {m['id']: content_digest(m) for m in models if m.get('tla') and m.get('cfg')}}


def census_store(report, models, a, env, tlc_version, root=ROOT):
    """Publish a census into the store as one measurement per model."""
    from benchmarking.records import store_lock, write_records
    header = census_header(models, a, root)
    rows = [census_row({**header, 'content_digest': header['content_digest'].get(m['id'])}, m, env, tlc_version, root)
            for m in report['models'] if m.get('dynamic', {}).get('native_share') is not None]
    with store_lock(root):
        write_records(rows, root)
    return rows


def store_census(root, *, filter=''):
    """The census as a view over the store: every stored row that carries
    coverage attributes, in the shape `print_report` reads."""
    from benchmarking.records import load_records
    rows, ranked = [], {}
    for r in load_records(root):
        if r.get('native_share') is None and r.get('evaluations') is None:
            continue
        if filter and filter not in r['model']:
            continue
        rows.append({'id': r['model'], 'status': r['counts'].get('result'),
                     'wall_s': r['metrics']['wall_s'], 'static': static_report(''),
                     'dynamic': {'native_share': r.get('native_share'), 'evaluations': r.get('evaluations'),
                                 'fully_native': r.get('fully_native'), 'host_time_share': r.get('host_time_share'),
                                 'host_time_s': r.get('host_s'), 'host_calls': r.get('host_calls'),
                                 'search_thread_s_est': r.get('search_thread_s_est'),
                                 'regions': [], 'closure_evaluations': [],
                                 'by_kind': {k: {'evaluations': 0, 'fully_native': 0, 'functions': []} for k in KINDS}},
                     'result': r['counts'], 'revision': r['revision'], 'date': r['date'],
                     'env': (r.get('configuration') or {}).get('env'),
                     'operations': []})
        for o in ((r.get('coverage') or {}).get('ops') or []):
            key = (o.get('operation'), tuple(o.get('arguments') or []), o.get('attribution'))
            row = ranked.setdefault(key, {'operation': key[0], 'arguments': list(key[1]),
                                          'attribution': key[2], 'models': [], 'executed_models': [],
                                          'calls': 0, 'time_s': 0, 'paths': {}, 'family': lowering_family(key[0] or '')})
            calls = sum((o.get('calls') or {}).values()) if isinstance(o.get('calls'), dict) else (o.get('calls') or 0)
            row['models'].append(r['model'])
            if calls:
                row['executed_models'].append(r['model'])
                row['calls'] += calls
            row['time_s'] += o.get('time_s') or 0
            for path, n in (o.get('paths') or {}).items():
                row['paths'][path] = row['paths'].get(path, 0) + n
    operations = [{'operation': o['operation'], 'arguments': o['arguments'], 'calls': o['calls'],
                   'time_s': o['time_s'] if o['calls'] else None, 'attribution': o['attribution'],
                   'models': sorted(o['models']), 'executed_models': sorted(o['executed_models']),
                   'paths': dict(sorted(o['paths'].items())), 'family': o['family']}
                  for o in sorted(ranked.values(), key=lambda x: (-(x['time_s'] or 0), -x['calls'], x['operation'] or ''))]
    return {'version': 1, 'diagnostic': True, 'source': 'store', 'models': sorted(rows, key=lambda x: x['id']),
            'selected': len(rows), 'reported': len(rows),
            'measured': sum(1 for x in rows if x['dynamic']['native_share'] is not None),
            'static_reported': 0, 'operations': operations}


def census(models, binary, a):
    deadline = time.monotonic() + a.deadline_min * 60 if a.deadline_min else float('inf')
    if a.deadline_at is not None:
        deadline = min(deadline, time.monotonic() + max(0, a.deadline_at - time.time()))
    rows = []
    def one(m):
        left = deadline - time.monotonic()
        if left <= 0:
            return {'id': m['id'], 'status': 'deadline skipped', 'dynamic': dynamic_report({}), 'static': static_report('')}
        return run(m, min(a.timeout, left), binary, a.dynamic)
    with concurrent.futures.ThreadPoolExecutor(a.j) as ex:
        pending = {ex.submit(one, m): m for m in models}
        for f in concurrent.futures.as_completed(pending):
            r = f.result()
            if a.dump:
                os.makedirs(a.dump, exist_ok=True)
                with open(os.path.join(a.dump, r['id'].replace('/', '__') + '.txt'), 'w') as out:
                    out.write(r.get('output', ''))
            r.pop('output', None)
            rows.append(r)
            if a.models:
                share = r['dynamic']['native_share']
                partial = r['dynamic'].get('partial_native_share')
                print(f"{r['id']:60} {r['status']:20} native {share if share is not None else 'unknown'} "
                      f"nodes {r['static']['nodes']}" + (f' partial={partial:.6f}' if partial is not None else ''), flush=True)
            if a.out:
                write_report(a.out, rows, len(models), a)
    return write_report(a.out, rows, len(models), a)


def write_report(path, rows, selected, a):
    report = {'version': 1, 'commit': __import__('tlxlib').git('rev-parse', 'HEAD'),
              'diagnostic': True, 'source': a.source, 'dynamic': a.dynamic, 'mode': 'compile-tlc',
              'selection': {'max_runtime': a.max_runtime, 'sizes': a.sizes, 'filter': a.filter, 'timeout_s': a.timeout,
                            'timeout_grace_s': TIMEOUT_GRACE if a.dynamic else 0},
              'selected': selected, 'reported': len(rows),
              'measured': sum(r['dynamic']['native_share'] is not None for r in rows),
              'static_reported': sum(r['static']['reported'] for r in rows),
              'models': sorted(rows, key=lambda r: r['id']), 'operations': rank_operations(rows)}
    if path:
        os.makedirs(os.path.dirname(os.path.abspath(path)), exist_ok=True)
        tmp = path + '.tmp'
        with open(tmp, 'w') as f:
            json.dump(report, f, indent=1)
            f.write('\n')
        os.replace(tmp, path)
    return report


def print_report(report, limit=25):
    """Both views remain useful without writing a JSON artifact."""
    print(f"models selected {report['selected']}; reported {report['reported']}; dynamic measured {report['measured']}")
    print('status: ' + str(dict(collections.Counter(r['status'] for r in report['models']))))
    nodes = collections.Counter()
    histogram = collections.Counter()
    reasons = collections.Counter()
    for model in report['models']:
        static = model['static']
        nodes.update(static['nodes'])
        for node in static['histogram']:
            histogram[(node['representation'], node['kind'], node['arguments'], node['reason'])] += node['nodes']
        reasons.update(f['reason'] for f in static['closure_functions'])
    print(f"static IR nodes: typed {nodes['typed']}; boxed {nodes['boxed']}; interpreted {nodes['interpreted']}")
    print('-- static nodes (representation; kind; argument shapes; reason)')
    for (rep, kind, args, reason), count in histogram.most_common(limit):
        print(f'{count:8} {rep}: {kind} | {args} | {reason}')
    print('-- static native rejection reasons (functions)')
    for reason, count in reasons.most_common(limit):
        print(f'{count:8} {reason}')
    measured = [m['dynamic'] for m in report['models'] if m['dynamic']['native_share'] is not None]
    total = sum(d['evaluations'] for d in measured)
    native = sum(d['fully_native'] for d in measured)
    share = f'{100*native/total:.5f}%' if total else 'unknown'
    print(f'fully native evaluations {native}/{total} ({share}); complete nonempty measurements only')
    host = sum(d['host_time_s'] for d in measured)
    units = sum(d['search_thread_s_est'] for d in measured)
    host_share = f'{100*host/units:.5f}%' if units else 'unknown'
    print(f"host regions: {sum(d['host_calls'] for d in measured)} calls; {host:.9f}s; time share estimate {host_share}")
    print('-- non-native operations (diagnostic host time; calls; executed/present models; argument shapes; proposed family)')
    for r in report['operations'][:limit]:
        timing = f"{r['time_s']:10.6f}s" if r['time_s'] is not None else 'unknown time'
        # The path split is what makes an adaptive tier decision auditable.
        paths = ''.join(f" {p}={n}" for p, n in sorted((r.get('paths') or {}).items()))
        print(f"{timing} {r['calls']:12} {len(r['executed_models'])}/{len(r['models'])} {r['operation']} {r['arguments']} -> {r['family']}{paths}")


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--hist', type=int, default=25)
    ap.add_argument('--filter', default='')
    ap.add_argument('--prioritize', default='', help='comma-separated model ID substrings, measured first')
    ap.add_argument('-j', '--jobs', dest='j', type=int, default=DEFAULT_JOBS)
    ap.add_argument('--timeout', type=float, default=60)
    ap.add_argument('--deadline-min', type=float, default=0)
    ap.add_argument('--deadline-at', type=float, default=None, help=argparse.SUPPRESS)
    ap.add_argument('--models', action='store_true')
    ap.add_argument('--dump', default='')
    ap.add_argument('--out', default='')
    ap.add_argument('--dynamic', action='store_true')
    ap.add_argument('--record', action='store_true',
                    help='publish the census into the measurement store (one row per model, coverage attributes included)')
    ap.add_argument('--view', action='store_true',
                    help='print the census as a view over the measurement store instead of measuring')
    ap.add_argument('--smoke', action='store_true', help=argparse.SUPPRESS)
    ap.add_argument('--source', choices=['corpus', 'external', 'suite', 'all'], default='corpus')
    ap.add_argument('--max-runtime', type=int, default=10, help='Examples manifest runtime bound (seconds)')
    ap.add_argument('--sizes', default='small,medium', help='external/suite sizes, or all')
    ap.add_argument('--bin', default='')
    ap.add_argument('--no-build', action='store_true')
    add_profile_args(ap)
    a = ap.parse_args(argv)
    if a.smoke:
        from benchmarking import bench_smoke
        a.cmd = 'coverage'
        return bench_smoke.run(a)
    if a.view:
        report = store_census(ROOT if not a.out else a.out, filter=a.filter)
        print_report(report, a.hist)
        return 0
    if a.record and not a.dynamic:
        ap.error('--record needs --dynamic: a static census has no coverage attributes to store')
    if a.timeout <= 0 or a.j <= 0 or a.deadline_min < 0:
        ap.error('timeout/jobs must be positive; deadline must be nonnegative')
    if a.bin and not os.path.isfile(a.bin):
        ap.error(f'binary does not exist: {a.bin}')
    if a.no_build and not a.bin:
        from tlxlib import profile_dir
        expected_binary = os.path.join(ROOT, 'target', profile_dir(profile_of(a)), 'tlx')
        if not os.path.isfile(expected_binary):
            ap.error(f'--no-build binary does not exist: {expected_binary}; build it first')
    todo = select_models(a)
    if not todo:
        ap.error('no manifest models selected')
    with contextlib.nullcontext(os.path.abspath(a.bin)) if a.bin else build_tlx(profile=profile_of(a), build=not a.no_build, prefix='tlx-coverage-') as binary:
        report = census(todo, binary, a)
    if a.record:
        from benchmarking import machine as bench_machine
        rows = census_store(report, todo, a, census_env(), bench_machine.tla2tools_info().get('revision'), ROOT)
        print(f'recorded {len(rows)} coverage measurements in the store')
    print_report(report, a.hist)
    return 0 if (report['measured'] if a.dynamic else report['static_reported']) == report['selected'] else 2


if __name__ == '__main__':
    raise SystemExit(main())
