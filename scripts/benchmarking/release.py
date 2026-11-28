"""The cross-release comparison: `bench.py release [TAG]`.

A release is compared with the release before it, and both with TLC, on one
machine class. `--report-only` derives the comparison from the canonical
measurement store alone; the campaign mode launches what the store lacks: the
missing TLC baselines and one sliced `suite` shard per `cloud_verify.py` launch,
then imports what those launches returned and renders the delta report.

Every number comes from stored rows, never from a timer here. Two rows are
compared only when every dimension that decides whether they are the same
measurement agrees - model, machine and architecture, mode, workers, arguments,
environment, memory limit and the input digest and TLC version the timing was
taken against - so a row measured on another machine, or against changed inputs,
is never paired: it shows `—` instead (`HARNESS-19`). A missing counterpart is
never read as zero.

The import direction is one way (`HARNESS-03`): the libraries below are read
downward, `scripts/cloud_verify.py` is a child process, and this module never
imports `bench`.
"""
import json
import os
from pathlib import Path
import re
import shlex
import shutil
import statistics
import subprocess
import sys

from benchmarking.baselines import historical_match
from benchmarking.bench_budget import parse_slice
from benchmarking.bench_records import (eligible, generate, number, optimizations, require_store,
                                        rss_ratio, unreduced_twin, unreduced_twins)
from benchmarking.legacy import ingest
from benchmarking.records import ROOT, load_records, peak_rss
from cloud.cloud_common import is_verdict_exit, read_receipt, receipt_problem
from harness.git import run as run_git
from tlxlib import geomean

# The machine class the cross-release numbers are quotable on: the same one the
# published report uses, and the one the campaign launches.
DEFAULT_INSTANCE = 'SA5.4XLARGE32'
# A regression is relative AND absolute: a 5% slowdown of a 0.1 s model is not a
# result, so the row must also be `--min-delta` seconds slower.
DEFAULT_THRESHOLD = 0.05
DEFAULT_MIN_DELTA = 0.05
# Rows per gains/regressions table.
DEFAULT_TOP = 8
# The model families a release is read by first: the external industrial
# specifications plus the corpus models whose id names Raft, Zab or Mongo
# (docs/performance.md's flagship cohort).
FLAGSHIP = ('Raft', 'Zab', 'Mongo')
# Where cloud_verify.py leaves each launch's result directory and its receipt.
# bench_suite.BENCH_RESULTS is the same path, but reading it there would import
# a module of the `bench` cluster (`scripts/check_imports.py`) into this one.
RESULTS = ('target', 'bench')
# `bench/history/` is where a runner's raw output lives and is committed beside
# the rows it produced, so `bench.py report --check` can re-derive them.
HISTORY = os.path.join('bench', 'history')


# ------------------------------------------------------------------ the tags

def _git(*args, root=ROOT):
    """Git's standard output, stripped, or None when git refused the request."""
    p = run_git(*args, cwd=str(root), text=True)
    return p.stdout.strip() if p.returncode == 0 else None


def release_tags(root=ROOT):
    """The `v*.*.*` release tags, newest version first."""
    out = _git('tag', '-l', 'v*.*.*', '--sort=-v:refname', root=root) or ''
    return [line.strip() for line in out.splitlines() if line.strip()]


def commit_of(rev, root=ROOT):
    """The full 40-character commit `rev` names, or None when it names none."""
    out = _git('rev-parse', '--verify', f'{rev}^{{commit}}', root=root) or ''
    return out if re.fullmatch(r'[0-9a-f]{40}', out) else None


def resolve_release_tags(tag=None, prev_tag='auto', *, root=ROOT):
    """The two releases a comparison is between: names and commit SHAs.

    `tag` defaults to the newest release tag. `prev_tag` is `auto` (the release
    immediately before `tag` in version order), `none`/empty (compare with TLC
    only), or a tag or commit. Fails closed: a name that resolves to no commit is
    refused with a message instead of entering the report as an unknown revision
    (`HARNESS-19`).
    """
    tags = release_tags(root)
    new = (tag or (tags[0] if tags else '')).strip()
    if not new:
        raise SystemExit('release: no v*.*.* tag in this checkout; run git fetch --tags first')
    sha = commit_of(new, root)
    if sha is None:
        raise SystemExit(f'release: {new!r} is not a tag or commit in this checkout')
    prev = str(prev_tag).strip() if prev_tag is not None else ''
    if prev in ('', 'none'):
        prev = None
    elif prev == 'auto':
        if new not in tags:
            raise SystemExit(f'release: --prev-tag auto needs TAG to be one of the v*.*.* tags '
                             f'({new!r} is not); name the previous release with --prev-tag TAG')
        index = tags.index(new)
        prev = tags[index + 1] if index + 1 < len(tags) else None
    prev_sha = commit_of(prev, root) if prev else None
    if prev and prev_sha is None:
        raise SystemExit(f'release: previous release {prev!r} is not a tag or commit in this checkout')
    return {'tag': new, 'sha': sha, 'short': sha[:12],
            'prev_tag': prev, 'prev_sha': prev_sha,
            'prev_short': prev_sha[:12] if prev_sha else None}


def head_revision(root=ROOT):
    """The harness revision the campaign launches run: this checkout's HEAD."""
    sha = commit_of('HEAD', root)
    if sha is None:
        raise SystemExit("release: cannot resolve HEAD; the campaign runs this checkout's harness")
    return sha


def same_revision(a, b):
    """Whether two spellings name one revision, or False when either is unknown.

    The same rule as `bench_suite._same_revision` (which cannot be imported here
    without joining that module's declared import cycle): an exact match, or a
    hexadecimal prefix of at least 7 characters on both sides. A `-dirty` record
    names a working tree nobody published, so it matches nothing but itself - a
    dirty measurement is never attributed to a release tag (`HARNESS-19`).
    """
    if not isinstance(a, str) or not isinstance(b, str) or not a or not b:
        return False
    if a == b:
        return True
    if a.endswith('-dirty') or b.endswith('-dirty'):
        return False
    return min(len(a), len(b)) >= 7 and (a.startswith(b) or b.startswith(a))


# --------------------------------------------------------------- the pairing

def release_key(r):
    """The dimensions two cross-release rows must share to be one measurement.

    The input digest and the TLC version are among them because a timing is only
    comparable on the same inputs measured against the same oracle; the machine,
    architecture, arguments, environment and memory limit because a ratio across
    them is not a version-to-version change either.
    """
    i = r.get('instance') or {}
    c = r.get('configuration') or {}
    return (r.get('model'), i.get('type'), i.get('arch'), r.get('mode'), r.get('workers'),
            tuple(c.get('args') or []), json.dumps(c.get('env') or {}, sort_keys=True),
            c.get('cgroup_mib'), r.get('content_digest'), r.get('tlc_version'))


def _key_order(key):
    """A stable order over `release_key` tuples (they mix values of several types)."""
    return json.dumps(key, sort_keys=True, default=str)


def _revision_rows(store, revision, instance_type):
    """The eligible `tlx` rows of one revision on the compared machine class."""
    found = {}
    for r in store:
        if r.get('tool') != 'tlx' or not eligible(r):
            continue
        if not same_revision(r.get('revision'), revision):
            continue
        if (r.get('instance') or {}).get('type') != instance_type:
            continue
        key = release_key(r)
        rank = (r.get('date') or '', r['id'])
        if key not in found or rank > found[key][0]:
            found[key] = (rank, r)
    return {key: row for key, (_, row) in found.items()}


def _view(r):
    """The fields of a stored row a comparison reports, never the whole row."""
    c = r.get('configuration') or {}
    return {'model': r.get('model'), 'mode': r.get('mode'), 'workers': r.get('workers'),
            'wall_s': (r.get('metrics') or {}).get('wall_s'),
            'rss_mib': peak_rss(r.get('metrics') or {}),
            'result': (r.get('counts') or {}).get('result'),
            'args': list(c.get('args') or []), 'cgroup_mib': c.get('cgroup_mib'),
            'optimizations': list(optimizations(r))}


def _wall_ratio(before, after):
    """`before / after` wall time (above one: `after` is faster), or None."""
    if before is None or after is None:
        return None
    a, b = (before.get('metrics') or {}).get('wall_s'), (after.get('metrics') or {}).get('wall_s')
    return a / b if a and b else None


def _pairable(r):
    """Whether a row states the dimensions a cross-release ratio needs.

    An unstated input digest, architecture or TLC version is not an *agreeing*
    one: two rows that both leave the digest unknown are two measurements of
    possibly different inputs, and equal `None`s are not evidence. Such a row is
    still reported on its own, and only its previous-release comparison stays
    empty - the twin pairing fails closed for the same reason (`HARNESS-19`).
    """
    return (bool(r.get('content_digest'))
            and bool((r.get('instance') or {}).get('arch'))
            and bool(r.get('tlc_version')))


def _new_optimizations(new, prev):
    """The optimizations the new record names and the previous release's does not.

    A row without a previous release states nothing *new*: without a baseline to
    differ from, every one of its own would otherwise be counted as new.
    """
    if prev is None:
        return []
    before = set(optimizations(prev))
    return [name for name in optimizations(new) if name not in before]


def _pair(new, prev, by_id, twins):
    """One comparable configuration: the new row, its previous release and TLC."""
    baseline = by_id.get(new.get('baseline'))
    tlc = baseline if baseline is not None and historical_match(new, baseline) else None
    twin = unreduced_twin(new, twins)
    i = new.get('configuration') or {}
    return {'model': new.get('model'), 'mode': new.get('mode'), 'workers': new.get('workers'),
            'args': list(i.get('args') or []), 'cgroup_mib': i.get('cgroup_mib'),
            'new': _view(new), 'prev': _view(prev) if prev is not None else None,
            'tlc': _view(tlc) if tlc is not None else None,
            'twin_s': None if twin is None else (twin.get('metrics') or {}).get('wall_s'),
            'new_optimizations': _new_optimizations(new, prev),
            # `rss_ratio(r, baseline)` is baseline/new: the new row is the
            # denominator on both sides, so the published statistic (the median
            # of the finite positive peak-RSS samples) is the one read here.
            'prev_wall_ratio': _wall_ratio(prev, new),
            'prev_rss_ratio': rss_ratio(new, prev) if prev is not None else None,
            'tlc_wall_ratio': _wall_ratio(tlc, new),
            'tlc_rss_ratio': rss_ratio(new, tlc) if tlc is not None else None}


def compare_releases(store, new_rev, prev_rev=None, instance_type=DEFAULT_INSTANCE):
    """Pair two releases' measurements and derive the comparison's numbers.

    One entry per eligible `tlx` measurement of `new_rev` on `instance_type`;
    `prev` is its counterpart in `prev_rev` (None when the releases have no
    identical configuration, when `prev_rev` is None, or when the two rows
    disagree on any `release_key` dimension). Identical keys are resolved the way
    the store resolves a key: the newest row wins, ties broken by id.
    """
    by_id = {r['id']: r for r in store}
    new_rows = _revision_rows(store, new_rev, instance_type)
    prev_rows = _revision_rows(store, prev_rev, instance_type) if prev_rev else {}
    # The unreduced twins are looked up on the new revision's rows alone: a twin
    # of another revision is exactly what the pairing must not borrow, and
    # `unreduced_twin`'s key carries the revision it was measured from.
    twins = unreduced_twins(new_rows.values())
    pairs = []
    for key in sorted(new_rows, key=_key_order):
        new = new_rows[key]
        # A row that leaves one of the identifying dimensions unknown has no
        # comparable counterpart, however the keys compare.
        prev = prev_rows.get(key) if _pairable(new) else None
        pairs.append(_pair(new, prev, by_id, twins))
    return pairs


# --------------------------------------------------------------- the report

def _median(values):
    """The median of the measured values, or None when nothing was measured."""
    values = [v for v in values if v]
    return statistics.median(values) if values else None


def _geomean(values):
    """The geometric mean of the measured values, or None when there is none."""
    values = [v for v in values if v]
    return geomean(values) if values else None


def _label(pair):
    """A row's model and mode, with its memory limit when the run states one."""
    text = f"{pair['model']} / {pair['mode']}"
    if pair['cgroup_mib']:
        text += f" / cgroup {pair['cgroup_mib']} MiB"
    return text


def _slowdown(pair):
    """How much slower the new release is, as a fraction, or None."""
    if pair['prev_wall_ratio'] is None:
        return None
    return 1 / pair['prev_wall_ratio'] - 1


def regressions(pairs, threshold=DEFAULT_THRESHOLD, min_delta=DEFAULT_MIN_DELTA):
    """The rows whose new wall time is `threshold` and `min_delta` worse.

    Both bounds are required: the relative one keeps a fast model's noise out of
    the table, the absolute one keeps a stalled 0.1 s run out of it.
    """
    flagged = [p for p in pairs
               if p['prev_wall_ratio'] is not None and p['prev'] is not None
               and _slowdown(p) > threshold
               and p['new']['wall_s'] - p['prev']['wall_s'] > min_delta]
    return sorted(flagged, key=lambda p: (p['prev_wall_ratio'], _key_order(_pair_key(p))))


def _pair_key(pair):
    return (pair['model'], pair['mode'], pair['workers'], pair['args'])


def _improved(pairs, ratio, top):
    """The rows whose `ratio` improves on the previous release, best first.

    A ratio of exactly one is no change and one below it is a regression: those
    belong to the regression table (for wall time) or to no table at all, never
    to a "largest gains"/"reductions" list that a reader takes for improvements.
    """
    measured = [p for p in pairs if (p.get(ratio) or 0) > 1]
    measured.sort(key=lambda p: (p[ratio], _key_order(_pair_key(p))), reverse=True)
    return measured[:top]


def flagship(model):
    """Whether a model belongs to the release report's flagship cohort."""
    return str(model).startswith('ext/') or any(name in str(model) for name in FLAGSHIP)


def render_release_report(pairs, *, tag, prev_tag=None, sha=None, prev_sha=None,
                          instance_type=DEFAULT_INSTANCE, threshold=DEFAULT_THRESHOLD,
                          min_delta=DEFAULT_MIN_DELTA, top=DEFAULT_TOP):
    """The deterministic Markdown comparison of two releases and TLC.

    Deterministic: the input is the store's rows, every table is sorted on the
    row's own identity, and nothing reads the clock, the machine or the network -
    so a re-render of the same evidence is byte for byte the same report.
    """
    previous = prev_tag or 'previous'
    out = [f'# {tag} vs. {previous}: performance and memory', '',
           f'Cross-release comparison of `{tag}`'
           + (f' (`{sha[:12]}`)' if sha else '')
           + f' with `{previous}`'
           + (f' (`{prev_sha[:12]}`)' if prev_sha else '')
           + f' on `{instance_type}`, generated by `python3 scripts/bench.py release'
             f' --report-only` from the canonical measurement store (`bench/records/`, '
             '`bench/tlc-baselines/`). Nothing here was re-measured.',
           '',
           'Rows are paired only when model, machine class and architecture, mode, worker count, '
           'arguments, environment, memory limit, input digest and TLC version all agree, so a row '
           'measured on another machine or against changed inputs stays unpaired (`—`) instead of '
           'becoming a ratio across incomparable evidence.', '',
           'Ratios are `previous / new` (above one: the new release is faster or used less peak '
           'memory) and `TLC / new` (above one: tlx is faster or used less peak memory than TLC on the '
           'same machine and input). Times are median process wall seconds and RSS is median peak '
           'resident MiB; both sides of a memory ratio are the stored `metrics.rss_mib`, and a '
           'missing or zero measurement stays `—` rather than reading as a zero-byte footprint. '
           f'A wall-time regression is flagged above {100 * threshold:.2f}% AND above '
           f'{min_delta:.2f} s.', '']
    if not pairs:
        out += [f'No eligible `tlx` measurement of `{tag}` on `{instance_type}` is in the store, so '
                'there is nothing to compare. Collect it with '
                f'`python3 scripts/bench.py release {tag}`.', '']
        return '\n'.join(out)
    if prev_tag is None:
        out += [f'No previous release was named, so the previous-release columns are `—`; '
                f're-run with `--prev-tag` to compare against an earlier release.', '']
    elif not any(p['prev'] is not None for p in pairs):
        out += [f'No eligible `tlx` measurement of `{previous}` on the same inputs and machine as '
                f'`{tag}` is in the store, so the previous-release columns are `—`.', '']
    out += ['## Cohort summary', '',
            '| Mode / workers | Models | Paired | Median prev / new | Geometric mean prev / new | '
            'Median prev / new RSS | Median TLC / new | Median TLC / new RSS | New optimizations |',
            '|---|---:|---:|---:|---:|---:|---:|---:|---:|']
    cohorts = {}
    for pair in pairs:
        cohorts.setdefault((pair['mode'], pair['workers']), []).append(pair)
    for (mode, workers), cohort in sorted(cohorts.items()):
        wall = [p['prev_wall_ratio'] for p in cohort if p['prev_wall_ratio']]
        rss = [p['prev_rss_ratio'] for p in cohort if p['prev_rss_ratio']]
        tlc_wall = [p['tlc_wall_ratio'] for p in cohort if p['tlc_wall_ratio']]
        tlc_rss = [p['tlc_rss_ratio'] for p in cohort if p['tlc_rss_ratio']]
        out.append(f"| {mode} / {workers} | {len(cohort)} | {sum(1 for p in cohort if p['prev'] is not None)} "
                   f"| {number(_median(wall), '×')} | {number(_geomean(wall), '×')} "
                   f"| {number(_median(rss), '×')} | {number(_median(tlc_wall), '×')} "
                   f"| {number(_median(tlc_rss), '×')} "
                   f"| {sum(1 for p in cohort if p['new_optimizations'])} |")
    out += ['', '## Regressions and notable gains', '',
            f'### Wall-time regressions (above {100 * threshold:.2f}% and {min_delta:.2f} s)',
            '',
            '| Model / mode | Workers | Previous s | New s | Slowdown | prev / new |',
            '|---|--:|--:|--:|--:|--:|']
    flagged = regressions(pairs, threshold, min_delta)
    if not flagged:
        out += ['No row regressed by both bounds.', '']
    for pair in flagged[:top]:
        out.append(f"| {_label(pair)} | {pair['workers']} | {number(pair['prev']['wall_s'])} "
                   f"| {number(pair['new']['wall_s'])} | {number(_slowdown(pair) * 100, '%')} "
                   f"| {number(pair['prev_wall_ratio'], '×')} |")
    if flagged:
        out += ['', 'A row stopped at a violation has worker-interleaving-dependent distinct counts, so '
                    'a timing-only entry here is a timing result; a changed distinct count of a complete '
                    'search is never a gain.', '']
    gains = _improved(pairs, 'prev_wall_ratio', top)
    out += ['', f'### Largest wall-time gains (up to {top})', '',
            '| Model / mode | Workers | Previous s | New s | prev / new |',
            '|---|--:|--:|--:|--:|']
    if not gains:
        out += ['No row ran faster on both releases.', '']
    for pair in gains:
        out.append(f"| {_label(pair)} | {pair['workers']} | {number(pair['prev']['wall_s'])} "
                   f"| {number(pair['new']['wall_s'])} "
                   f"| {number(pair['prev_wall_ratio'], '×')} |")
    memory = _improved(pairs, 'prev_rss_ratio', top)
    out += ['', f'### Largest peak-memory reductions (up to {top})', '',
            '| Model / mode | Workers | Previous MiB | New MiB | Reduction | prev / new RSS |',
            '|---|--:|--:|--:|--:|--:|']
    if not memory:
        out += ["No row used less peak memory on both releases.", '']
    for pair in memory:
        # `prev_rss_ratio` is previous / new, so the fraction saved is
        # 1 - new / previous = 1 - 1 / ratio; `ratio - 1` would claim more than
        # 100% for any reduction below half.
        reduction = (1 - 1 / pair['prev_rss_ratio']) * 100
        out.append(f"| {_label(pair)} | {pair['workers']} | {number(pair['prev']['rss_mib'])} "
                   f"| {number(pair['new']['rss_mib'])} | {number(reduction, '%')} "
                   f"| {number(pair['prev_rss_ratio'], '×')} |")
    flags = [p for p in pairs if flagship(p['model'])]
    out += ['', '## Flagship open-source models', '',
            'The external specifications (`ext/*`) and the corpus models whose id names Raft, Zab or '
            'Mongo. `-tlc twin s` is the same-instance unreduced `-tlc` record\'s wall time - the '
            'factor the reduced search saved - and `tlx optimizations` is what the new release\'s '
            'record states (never inferred from a count difference).', '',
            f'| Model / mode | Workers | {previous} s | {previous} MiB | {tag} s | {tag} MiB '
            '| TLC s | TLC MiB | TLC / new | -tlc twin s | tlx optimizations |',
            '|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|---|']
    if not flags:
        out += ['No flagship model was measured for these releases.', '']
    for pair in flags:
        prev = pair['prev'] or {}
        tlc = pair['tlc'] or {}
        out.append(f"| {_label(pair)} | {pair['workers']} | {number(prev.get('wall_s'))} "
                   f"| {number(prev.get('rss_mib'))} | {number(pair['new']['wall_s'])} "
                   f"| {number(pair['new']['rss_mib'])} | {number(tlc.get('wall_s'))} "
                   f"| {number(tlc.get('rss_mib'))} | {number(pair['tlc_wall_ratio'], '×')} "
                   f"| {number(pair['twin_s'])} "
                   f"| {'; '.join(pair['new']['optimizations']) or '—'} |")
    return '\n'.join(out) + '\n'


# ------------------------------------------------------------- the campaign

def history_path(stem, root=ROOT):
    """A free `bench/history/<stem>[-N].json` path.

    `bench.py suite --missing` refuses an `--out` that already exists or owns
    stored records, so a resumed campaign takes the next attempt number instead
    of trying to overwrite the shard it already recorded.
    """
    attempt = 1
    while True:
        name = stem if attempt == 1 else f'{stem}-{attempt}'
        rel = f'{HISTORY}/{name}.json'
        if not os.path.exists(os.path.join(str(root), rel)):
            return rel
        attempt += 1


def campaign_models(suite, models='', sizes=''):
    """The exact suite model ids a campaign passes to its launches.

    `--models` is a comma-separated list of ids or id substrings - the matching
    `suite --models` applies - and `--sizes` is a comma-separated list of size
    classes or `all`, `suite --sizes`'s own spelling for every class including
    `huge`. The result is the exact-id list `tlcbase --models` needs (it accepts
    only ids that exist and refuses a substring), and empty when nothing narrows
    the passes: no filter at all, or `--sizes all` alone, where each pass's own
    default already is the whole manifest.

    A filter that selects no suite model is refused here, before anything
    launches.
    """
    patterns = [p.strip() for p in str(models).split(',') if p.strip()]
    sizes = {s.strip() for s in str(sizes).split(',') if s.strip()}
    every_size = 'all' in sizes
    # A size filter that excludes a class is the only `--sizes` form that has to
    # be resolved into ids; `all` (or no `--sizes`) narrows nothing.
    if not patterns and (not sizes or every_size):
        return []
    kept = [m for m in suite.get('models') or []
            if (every_size or not sizes or m.get('size') in sizes)
            and (not patterns or any(p == m['id'] or p in m['id'] for p in patterns))]
    if not kept:
        raise SystemExit(f'release: --models {models!r} with --sizes {sizes!r} '
                         'selects no model of bench/suite.json')
    return [m['id'] for m in kept]


def _launch(a, head, bench, out, bins):
    """One cloud launch of a `bench.py` command, with what its receipt must pin."""
    argv = [sys.executable, os.path.join(ROOT, 'scripts', 'cloud_verify.py'), head,
            '--provider', a.provider, '--instance-type', a.instance_type,
            '--slots', str(a.slots), '--max-minutes', str(a.max_minutes + a.setup_minutes),
            '--bench', bench]
    if bins:
        argv += ['--bench-bin', f'rel={bins[0][1]}']
    return {'label': os.path.basename(out).removesuffix('.json'), 'argv': argv, 'bench': bench,
            'out': out, 'bins': bins}


def campaign_commands(a, tags, head, suite, root=ROOT):
    """The launches a release campaign runs, in order, as `_launch` records.

    The missing TLC baselines come first - the suite's ratios need them - then
    one `suite` shard per launch. Every launch runs this checkout's harness
    (`head`) and measures the released binary built from the tag
    (`--bench-bin rel=<sha>`), so the harness and the binary under test are
    stated separately (`HARNESS-19`). `--models`/`--sizes` are resolved against
    `suite` into exact ids, so a targeted campaign collects no baselines for a
    model (or a size class) it will not run.
    """
    models = campaign_models(suite, a.models, a.sizes)
    selected = ','.join(models)
    # `suite --sizes` defaults to `small,medium,large`, so naming a `huge` model
    # without `--sizes` would provision an instance and then drop it ("no
    # benchmark runs selected"). An explicit `--models` therefore asks for every
    # size class; an explicit `--sizes` is forwarded verbatim, `all` included.
    sizes = a.sizes or ('all' if a.models else '')
    launches = []
    tlc = ['tlcbase', '--missing', '--collect', '--workers', a.tlc_workers,
           '--tlc-repetitions', str(a.tlc_repetitions)]
    if selected:
        tlc += ['--models', selected]
    out = history_path(f'tlc-release-{tags["tag"]}', root)
    tlc += ['--out', out]
    launches.append(_launch(a, head, ' '.join(tlc), out, []))
    for index in range(1, a.slices + 1):
        spec = f'{index}/{a.slices}'
        parse_slice(spec)  # refuse a bad shard spec here, not on the instance
        shard = ['suite', '--missing', '--slice', spec,
                 '--bin', 'target/bench-bins/rel/tlx', '--bin-rev', tags['sha'],
                 '--isolate-cache', '--with-tlc-companion', '--repeat', str(a.repeat),
                 '--max-minutes', str(a.max_minutes)]
        if sizes:
            shard += ['--sizes', sizes]
        if selected:
            shard += ['--models', selected]
        out = history_path(f'suite-{tags["tag"]}-s{index}of{a.slices}', root)
        shard += ['--out', out]
        launches.append(_launch(a, head, ' '.join(shard), out, [('rel', tags['sha'], '')]))
    return launches


def receipt_names(root=ROOT):
    """The result-directory names under `target/bench/` right now.

    A launch gets a fresh time-stamped directory of its own
    (`cloud/setup.local_dir`), so the names present before it starts are exactly
    the earlier invocations' receipts: one of those must never authorize this
    run (`HARNESS-06`). A resumed campaign re-issues the same command (a 0-missing
    launch writes no history file, so its name is not taken), and without this
    the previous no-op's receipt would either double the match or stand in for a
    run that wrote none.
    """
    directory = Path(root).joinpath(*RESULTS)
    return (frozenset(entry.name for entry in directory.iterdir() if entry.is_dir())
            if directory.is_dir() else frozenset())


def launch_result(head, launch, code, root=ROOT, exclude=()):
    """`(history file, authorized)` of one finished launch.

    `authorized` says whether exactly one receipt names *this* invocation: it was
    not there before the launch (`exclude`, `receipt_names`) and it states the
    revision, pinned binary, exit status and the launch's own `--bench` command,
    since every launch of a campaign shares the first three (`HARNESS-12`). The
    file is the one history file that receipt holds, or `None` - `tlcbase` and
    `suite` both exit 0 without writing their `--out` when 0 items are missing,
    which is a completed no-op, not a failure. An absent, stale or ambiguous
    receipt authorizes nothing (`HARNESS-06`).
    """
    directory = Path(root).joinpath(*RESULTS)
    found = []
    for entry in sorted(directory.iterdir()) if directory.is_dir() else []:
        if not entry.is_dir() or entry.name in exclude:
            continue
        receipt = read_receipt(str(entry))
        if receipt is None or receipt_problem(receipt, head, launch['bins'], code) is not None:
            continue
        if launch['bench'] not in (receipt.get('bench') or []):
            continue
        found.append(entry)
    if len(found) != 1:
        return None, False
    candidate = found[0] / 'bench' / 'history' / os.path.basename(launch['out'])
    return (candidate if candidate.is_file() else None), True


def record(src, root=ROOT):
    """Copy a launch's returned history file into `bench/history/` and import it."""
    root = Path(root)
    target = root / HISTORY / Path(src).name
    target.parent.mkdir(parents=True, exist_ok=True)
    if Path(src).resolve() != target.resolve():
        shutil.copyfile(src, target)
    ingest(target, root)
    return target


def run_campaign(head, launches, root=ROOT):
    """Run the launches and record what each returned, or stop at the first failure.

    A launch that exits with anything but a benchmark verdict (0, 1 or 2) is an
    infrastructure refusal or a failure: its receipt is failure evidence, so what
    it fetched is not recorded (`HARNESS-06`). So is a verdict exit whose receipt
    holds no history file - except a successful one, which is how `--missing`
    reports that it had nothing left to measure.
    """
    for item in launches:
        print(f"release: {item['label']}: " + ' '.join(shlex.quote(word) for word in item['argv']),
              flush=True)
        # What is already there belongs to an earlier invocation; only the
        # receipt this launch writes may authorize it (`HARNESS-06`).
        before = receipt_names(root)
        code = subprocess.run(item['argv'], cwd=str(root)).returncode
        if not is_verdict_exit(code):
            print(f"release: {item['label']} exited {code}: not a benchmark verdict, nothing recorded",
                  file=sys.stderr)
            return False
        src, authorized = launch_result(head, item, code, root, exclude=before)
        if not authorized:
            print(f"release: {item['label']}: no receipt authorizes this launch, nothing recorded",
                  file=sys.stderr)
            return False
        if src is None:
            if code != 0:
                print(f"release: {item['label']} exited {code} without {item['out']}, "
                      "nothing recorded", file=sys.stderr)
                return False
            print(f"release: {item['label']}: nothing missing, nothing to record", flush=True)
            continue
        print(f"release: recorded {record(src, root)}", flush=True)
    generate(root=root, refresh=True)
    return True


# ------------------------------------------------------------------- command

def cmd_release(a):
    """`bench.py release`: the comparison, or the campaign that makes it possible."""
    # The store ships with the sources (docs/benchmarking.md section 6.2). A
    # checkout without it is "the measurements are not here", not "nothing was
    # measured": an empty report would read as the second, so the absent
    # `bench/suite.json` is named before any tag is resolved.
    suite = require_store()
    tags = resolve_release_tags(a.tag, a.prev_tag)
    if not a.report_only:
        if a.slices < 1:
            sys.exit('release: --slices must be at least 1')
        head = head_revision()
        launches = campaign_commands(a, tags, head, suite)
        if a.dry_run:
            for item in launches:
                print(f"release: {item['label']}: "
                      + ' '.join(shlex.quote(word) for word in item['argv']), flush=True)
            return 0
        if not run_campaign(head, launches):
            return 3
    # The strict store reader, like every other report: `load_store` is the
    # tolerant shape migration has to read, and it would let a store file whose
    # key, name or measurement disagree be skipped instead of refused.
    pairs = compare_releases(load_records(), tags['sha'], tags['prev_sha'], a.instance_type)
    text = render_release_report(pairs, tag=tags['tag'], prev_tag=tags['prev_tag'],
                                 sha=tags['sha'], prev_sha=tags['prev_sha'],
                                 instance_type=a.instance_type, threshold=a.threshold,
                                 min_delta=a.min_delta, top=a.top)
    if a.markdown:
        path = Path(a.markdown)
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
    print(text, end='')
    return 0


def add_args(sub):
    """Register `bench.py release` (the parser's one owner is benchmarking/cli.py)."""
    p = sub.add_parser('release', help='compare two release tags and TLC from the canonical records')
    p.add_argument('tag', nargs='?', default='',
                   help='release tag to compare (default: the newest v*.*.* tag)')
    p.add_argument('--prev-tag', default='auto',
                   help='the release before TAG: auto (the previous v*.*.* tag), none (TLC only), '
                        'or a tag or commit (default auto)')
    p.add_argument('--report-only', action='store_true',
                   help='render the comparison from bench/records without launching anything')
    p.add_argument('--instance-type', default=DEFAULT_INSTANCE,
                   help=f'the machine class both releases were measured on (default {DEFAULT_INSTANCE})')
    p.add_argument('--markdown', default='', help='also write the rendered comparison to this file')
    p.add_argument('--threshold', type=float, default=DEFAULT_THRESHOLD,
                   help='relative wall-time regression threshold (default 0.05)')
    p.add_argument('--min-delta', type=float, default=DEFAULT_MIN_DELTA,
                   help='absolute wall-time regression threshold in seconds (default 0.05)')
    p.add_argument('--top', type=int, default=DEFAULT_TOP,
                   help=f'rows per gains and regressions table (default {DEFAULT_TOP})')
    p.add_argument('--slices', type=int, default=1,
                   help='split the suite campaign into N load-balanced shards, one launch each (default 1)')
    p.add_argument('--slots', type=int, default=1,
                   help='concurrent cloud instances the launches may use (default 1)')
    p.add_argument('--provider', default='tencent', help='cloud provider of the campaign launches')
    p.add_argument('--sizes', default='',
                   help='the suite sizes to run (default: the suite manifest\'s own default)')
    p.add_argument('--models', default='', help='only models whose id equals or contains one of these')
    p.add_argument('--repeat', type=int, default=3, help='timed suite samples per configuration (default 3)')
    p.add_argument('--tlc-repetitions', type=int, default=3,
                   help='TLC samples per baseline key the campaign collects (default 3)')
    p.add_argument('--tlc-workers', default='1,16',
                   help='TLC worker counts the campaign collects baselines for (default 1,16)')
    p.add_argument('--max-minutes', type=int, default=120,
                   help='the suite\'s own budget per launch (default 120)')
    p.add_argument('--setup-minutes', type=int, default=20,
                   help='added to --max-minutes for each instance\'s dead-man switch (default 20)')
    p.add_argument('--dry-run', action='store_true', help='print the launches without running them')
