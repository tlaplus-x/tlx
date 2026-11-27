"""Inventory the paired tlx/TLC speedups the report would publish.

The public report (`benchmarking.bench_records.render`) computes a ratio only
for a stored tlx row whose recorded TLC baseline matches it under
`baselines.historical_match`, and it selects one row per measurement key with
`eligible`. A reader auditing a large speedup needs the same selection: an
inventory built by pairing the raw store by model name would treat excluded
or incomplete rows as claims the report never made.

Each case also carries its same-instance unreduced `-tlc` twin when the store
holds one (same model, revision, instance, workers and input), so a reduced
row's TLC ratio can be read next to the like-for-like reduction factor instead
of the two being conflated.

This module is read-only. It returns data (and `main` writes JSON/markdown to
the caller's chosen path); it never runs a model or changes the store.

    PYTHONPATH=scripts python3 -m benchmarking.speedup_audit --threshold 100
"""

import argparse
import json
import sys
from pathlib import Path

if __package__ in (None, ""):
    sys.path.insert(0, str(Path(__file__).resolve().parents[1]))

from benchmarking import bench_records
from benchmarking.baselines import historical_match
from benchmarking.records import load_records, record_path


def selection(records):
    """The rows the report is allowed to publish, one per measurement key.

    Mirrors `bench_records.render`: latest by (date, id) per key, over rows
    that pass `eligible`.
    """
    records = sorted(records, key=lambda r: (r['date'] or '', r['id']))
    latest = {}
    for r in records:
        if bench_records.eligible(r):
            key = (r['model'], r['mode'], r['workers'], r['instance']['type'], r['instance']['arch'],
                   tuple(r['category']), tuple(r['configuration'].get('args', [])), r['configuration'].get('cgroup_mib'))
            latest[key] = r
    return sorted(latest.values(), key=lambda r: (r['model'], r['mode'], r['workers'],
                                                  r['instance']['type'] or '', r['id']))


def paired(rows, by_id):
    """(row, baseline) for every selected row the report pairs with a TLC row."""
    out = []
    for r in rows:
        tc = by_id.get(r.get('baseline'))
        if tc is not None and historical_match(r, tc):
            out.append((r, tc))
    return out


def _samples(r):
    """The raw per-sample evidence of a row, without the aggregate metrics."""
    raw = r.get('raw_result') or {}
    return {
        'aggregation': r.get('aggregation'),
        'walls': raw.get('walls'),
        'cpu': raw.get('cpu'),
        'samples': raw.get('samples'),
        'warmups': raw.get('warmups'),
        'sample_results': r['provenance'].get('sample_results'),
        'repetitions': r['provenance'].get('repetitions'),
    }


def cold_seconds(r):
    """The discarded warm-up (cold, cache-filling) wall time of a row, if kept.

    The measured samples follow this run, so the published time is the warm
    (native-cache filled) one; the store keeps the cold run in the raw result.
    """
    warmups = ((r.get('raw_result') or {}).get('warmups')) or []
    walls = [w.get('wall_s') for w in warmups if isinstance(w.get('wall_s'), (int, float))]
    return min(walls) if walls else None


def verify_digest(model_id, models):
    """The content digest recomputed from the model's inputs, or None.

    `models` maps a model id to the resolved model (its cfg, tla, flags,
    features and measurement constraints), the same inputs
    `baselines.content_digest` hashes when the store is written.
    """
    from benchmarking.baselines import content_digest
    m = models.get(model_id)
    return content_digest(m) if m and m.get('tla') and m.get('cfg') else None


def case(r, tc, twins=None):
    """One candidate row with the pairing facts an auditor has to check."""
    tlx_wall = r['metrics']['wall_s']
    tlc_wall = tc['metrics']['wall_s']
    twin = bench_records.unreduced_twin(r, twins or {})
    return {
        'model': r['model'],
        'mode': r['mode'],
        'workers': r['workers'],
        'category': r['category'],
        'args': r['configuration'].get('args', []),
        'ratio': tlc_wall / tlx_wall,
        'cold_tlx_s': cold_seconds(r),
        'tlx': {
            'id': r['id'],
            'path': record_path(r),
            'date': r['date'],
            'revision': r['revision'],
            'instance': r['instance'],
            'content_digest': r['content_digest'],
            'tlc_version': r['tlc_version'],
            'counts': r['counts'],
            'metrics': r['metrics'],
            'configuration': r['configuration'],
            'provenance': r['provenance'],
            'coverage': {k: r.get(k) for k in ('evaluations', 'fully_native', 'host_calls', 'host_s',
                                               'host_time_share', 'native_share', 'search_thread_s_est')},
            'evidence': _samples(r),
        },
        'tlc': {
            'id': tc['id'],
            'path': record_path(tc),
            'date': tc['date'],
            'instance': tc['instance'],
            'content_digest': tc['content_digest'],
            'tlc_version': tc['tlc_version'],
            'counts': tc['counts'],
            'metrics': tc['metrics'],
            'provenance': tc['provenance'],
            'evidence': _samples(tc),
        },
        'unreduced_twin': None if twin is None else {
            'id': twin['id'],
            'path': record_path(twin),
            'date': twin['date'],
            'revision': twin['revision'],
            'instance': twin['instance'],
            'content_digest': twin['content_digest'],
            'tlc_version': twin['tlc_version'],
            'counts': twin['counts'],
            'metrics': twin['metrics'],
            'configuration': twin['configuration'],
            'provenance': twin['provenance'],
            'ratio': twin['metrics']['wall_s'] / tlx_wall,
        },
        'checks': {
            'result_equal': r['counts']['result'] == tc['counts']['result'],
            'distinct_comparable': r['mode'] != 'default' and r['configuration'].get('compatibility') is not False,
            'distinct_equal': r['counts']['distinct'] == tc['counts']['distinct'],
            'content_digest_equal': r['content_digest'] == tc['content_digest'],
            'tlc_version_equal': r['tlc_version'] == tc['tlc_version'],
            'workers_equal': r['workers'] == tc['workers'],
            'instance_equal': r['instance']['type'] == tc['instance']['type'],
            'arch_equal': r['instance']['arch'] == tc['instance']['arch'],
            'cgroup_equal': r['configuration'].get('cgroup_mib') == tc['configuration'].get('cgroup_mib'),
            'compatibility': r['configuration'].get('compatibility'),
            'unreduced_twin': twin is not None,
            'twin_counts_equal_tlc': None if twin is None else (
                twin['counts']['result'] == tc['counts']['result']
                and twin['counts']['distinct'] == tc['counts']['distinct']),
        },
    }


def inventory(records, threshold=100.0):
    """Every selected tlx/TLC pair whose recorded ratio exceeds `threshold`."""
    by_id = {r['id']: r for r in records}
    rows = selection(records)
    # (The whole store, not the report's latest-per-key rows: `latest` does not
    # key by revision, so a twin of an older revision must not be evicted from
    # the lookup by a newer run of the same mode.)
    twins = bench_records.unreduced_twins(records)
    cases = [case(r, tc, twins) for r, tc in paired(rows, by_id)]
    cases = [c for c in cases if c['ratio'] > threshold]
    cases.sort(key=lambda c: -c['ratio'])
    return cases


def resolved_models(ids):
    """Resolve corpus, external and benchmark-only model ids to their inputs.

    Best effort: an id that cannot be resolved (a missing corpus module or
    checkout) is simply absent, and its digest stays unverified.
    """
    import corpus
    from benchmarking import models as bench_models
    known = {m['id']: m for m in corpus.models(float('inf'))}
    known.update({m['id']: m for m in corpus.external_models(corpus.EXTERNAL_TIERS)})
    known.update(bench_models.oracle())
    for mid in ids:
        if mid not in known:
            try:
                known.update(bench_models.stress_models([mid]))
            except SystemExit:
                pass
    return known


def add_digest_checks(cases, models):
    """Attach the recomputed digest of each candidate's inputs, when resolvable."""
    for c in cases:
        recomputed = verify_digest(c['model'], models)
        c['digest'] = {
            'recomputed': recomputed,
            'tlx_matches': recomputed is not None and recomputed == c['tlx']['content_digest'],
            'tlc_matches': recomputed is not None and recomputed == c['tlc']['content_digest'],
        }
    return cases


def markdown(cases):
    """A compact table of the inventory, one row per candidate.

    A default-mode candidate with a same-instance unreduced `-tlc` twin carries
    the twin's time and its factor over the reduced row: the published TLC ratio
    then has both the like-for-like reduction factor and TLC's own denominator.
    """
    twinned = any(c.get('unreduced_twin') for c in cases)
    twin_head = ' -tlc s | -tlc / default |' if twinned else ''
    out = ['| # | model | mode | workers | ratio |' + twin_head + ' tlx warm s | tlx cold s | TLC s | tlx distinct | TLC distinct | digest |',
           '|---:|---|---|---:|---:|' + ('---:|---:|' if twinned else '') + '---:|---:|---:|---:|---:|---|']
    for i, c in enumerate(cases, 1):
        cold = c['cold_tlx_s']
        digest = c.get('digest') or {}
        ok = 'verified' if digest.get('tlx_matches') and digest.get('tlc_matches') else (
            'mismatch' if digest.get('recomputed') else 'unresolved')
        twin = c.get('unreduced_twin')
        twin_cells = (f" {twin['metrics']['wall_s']:.3f} | {twin['ratio']:.2f}× |" if twin
                      else ' — | — |') if twinned else ''
        out.append(f"| {i} | {c['model']} | {c['mode']} | {c['workers']} | {c['ratio']:.2f}× |"
                   + twin_cells +
                   f" {c['tlx']['metrics']['wall_s']:.3f} | " +
                   (f"{cold:.3f}" if cold else "—") + f" | {c['tlc']['metrics']['wall_s']:.3f} | "
                   f"{c['tlx']['counts']['distinct']} | {c['tlc']['counts']['distinct']} | {ok} |")
    return '\n'.join(out) + '\n'


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--threshold', type=float, default=100.0, help='minimum recorded ratio (default 100)')
    parser.add_argument('--verify-digests', action='store_true',
                        help='recompute each candidate input digest from the corpus and compare with the store')
    parser.add_argument('--json', help='write the full inventory here')
    parser.add_argument('--markdown', help='write the table here')
    args = parser.parse_args(argv)
    cases = inventory(load_records(), args.threshold)
    if args.verify_digests:
        add_digest_checks(cases, resolved_models([c['model'] for c in cases]))
    if args.json:
        Path(args.json).write_text(json.dumps(cases, indent=1) + '\n')
    if args.markdown:
        Path(args.markdown).write_text(markdown(cases))
    print(markdown(cases), end='')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
