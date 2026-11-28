"""The cross-release comparison (`benchmarking/release.py`): tag resolution, the
pairing rules, the report's tables and the campaign's launches."""

from benchmarking import release as R
from benchmarking.records import normalize
from unittest.mock import patch
import contextlib
import io
import json
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

NEW = 'a' * 40
OLD = 'b' * 40
DIGEST = 'c' * 64
TLC_VERSION = '1813307'
CACHE = {'mode': 'fresh-per-model', 'initial_state': 'empty', 'warmup': True}
TAGS = {'tag': 'v0.1.2', 'sha': NEW, 'short': NEW[:12],
        'prev_tag': 'v0.1.1', 'prev_sha': OLD, 'prev_short': OLD[:12]}


def row(revision=NEW, *, model='ext/etcd/MCetcdraft', tool='tlx', mode='default', workers=1,
        wall=2.0, rss=100.0, digest=DIGEST, instance='SA5.4XLARGE32', machine=None,
        tlc_version=TLC_VERSION, result='success', args=(), cgroup=None, date='2026-11-01',
        optimizations=None, cache=CACHE, count_problems=None):
    """One canonical measurement row, built through the store's own normalizer."""
    machine = machine or ('x86_64, tencent ' + instance)
    raw = {'model': model, 'tool': tool, 'mode': mode, 'workers': workers, 'wall_s': wall,
           'cpu_s': wall, 'maxrss_mib': rss, 'result': result, 'distinct': 10, 'generated': 20,
           'depth': 3, 'content_digest': digest, 'tlc_version': tlc_version, 'args': list(args),
           'cgroup_mib': cgroup}
    if optimizations is not None:
        raw['samples'] = [{'wall_s': wall, 'optimizations': list(optimizations)}]
    if count_problems:
        raw['count_problems'] = list(count_problems)
    pointer = f"/runs/{model}/{tool}/{mode}/{workers}/{wall}"
    r = normalize({'commit': revision, 'date': date, 'machine': machine}, raw,
                  f'bench/history/{model.replace("/", "-")}.json', pointer)
    if cache is not None:
        r['provenance']['cache'] = cache
    return r


def baseline_of(new, *, instance='SA5.4XLARGE32', digest=DIGEST, tlc_version=TLC_VERSION,
                wall=20.0, rss=500.0):
    """A TLC baseline row linked from `new` by its `baseline` id."""
    tlc = row(OLD, model=new['model'], tool='tlc', mode='-tlc', workers=new['workers'],
              wall=wall, rss=rss, digest=digest, instance=instance, tlc_version=tlc_version,
              cache=None)
    new['baseline'] = tlc['id']
    return tlc


def section(text, heading):
    """The body of one Markdown section, up to the next heading."""
    start = text.index(heading)
    rest = re.search(r'\n#{2,3} ', text[start + len(heading):])
    return text[start:] if rest is None else text[start:start + len(heading) + rest.start()]


def output_of(call):
    """`(return value, standard output)` of a command."""
    buffer = io.StringIO()
    with contextlib.redirect_stdout(buffer):
        result = call()
    return result, buffer.getvalue()


def release_args(argv):
    """The namespace the real parser produces for `bench.py release ARGS`."""
    from benchmarking import cli
    _, parsed = cli.parse_args(['release', *argv], 'release usage')
    return parsed


class TagResolution(unittest.TestCase):
    """The two releases a report is between, resolved to names and commit SHAs."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.shas = {}
        self.git('-c', 'init.defaultBranch=main', 'init', '-q')
        self.git('config', 'user.name', 'Test Fixture')
        self.git('config', 'user.email', 'fixture@example.com')

    def git(self, *args):
        return subprocess.run(['git', *args], cwd=self.root, check=True, capture_output=True,
                              stdin=subprocess.DEVNULL)

    def commit(self, message):
        self.git('-c', 'commit.gpgsign=false', 'commit', '-q', '--allow-empty', '-m', message)
        return self.git('rev-parse', 'HEAD').stdout.decode().strip()

    def tag(self, name):
        self.shas[name] = self.commit(f'release {name}')
        self.git('tag', name)
        return self.shas[name]

    def test_newest_release_with_the_one_before_it(self):
        self.tag('v0.1.0')
        self.tag('v0.1.1')
        self.tag('v0.1.2')
        tags = R.resolve_release_tags(root=self.root)
        self.assertEqual((tags['tag'], tags['prev_tag']), ('v0.1.2', 'v0.1.1'))
        self.assertEqual(tags['sha'], self.shas['v0.1.2'])
        self.assertEqual(tags['prev_sha'], self.shas['v0.1.1'])
        self.assertEqual((tags['short'], tags['prev_short']),
                         (self.shas['v0.1.2'][:12], self.shas['v0.1.1'][:12]))

    def test_a_named_previous_release(self):
        self.tag('v0.1.0')
        self.tag('v0.1.1')
        self.tag('v0.1.2')
        tags = R.resolve_release_tags('v0.1.2', 'v0.1.0', root=self.root)
        self.assertEqual(tags['prev_tag'], 'v0.1.0')
        self.assertEqual(tags['prev_sha'], self.shas['v0.1.0'])

    def test_the_oldest_release_has_no_previous(self):
        self.tag('v0.1.0')
        self.tag('v0.1.1')
        self.tag('v0.1.2')
        tags = R.resolve_release_tags('v0.1.0', 'auto', root=self.root)
        self.assertIsNone(tags['prev_tag'])
        self.assertIsNone(tags['prev_sha'])

    def test_previous_can_be_disabled(self):
        self.tag('v0.1.0')
        self.tag('v0.1.1')
        tags = R.resolve_release_tags('v0.1.1', 'none', root=self.root)
        self.assertIsNone(tags['prev_tag'])
        self.assertIsNone(tags['prev_sha'])

    def test_an_unknown_tag_is_refused(self):
        self.tag('v0.1.0')
        with self.assertRaises(SystemExit) as refused:
            R.resolve_release_tags('v9.9.9', 'none', root=self.root)
        self.assertIn('v9.9.9', str(refused.exception))
        self.assertIn('not a tag or commit', str(refused.exception))

    def test_an_unknown_previous_tag_is_refused(self):
        self.tag('v0.1.0')
        with self.assertRaises(SystemExit) as refused:
            R.resolve_release_tags('v0.1.0', 'v9.9.9', root=self.root)
        self.assertIn('v9.9.9', str(refused.exception))

    def test_auto_requires_a_release_tag(self):
        sha = self.tag('v0.1.0')
        with self.assertRaises(SystemExit) as refused:
            R.resolve_release_tags(sha, 'auto', root=self.root)
        self.assertIn('--prev-tag auto', str(refused.exception))

    def test_a_checkout_without_release_tags_is_refused(self):
        self.commit('no release yet')
        with self.assertRaises(SystemExit) as refused:
            R.resolve_release_tags(root=self.root)
        self.assertIn('no v*.*.* tag', str(refused.exception))

    def test_head_is_the_harness_revision(self):
        sha = self.tag('v0.1.0')
        self.assertEqual(R.head_revision(self.root), sha)


class Pairing(unittest.TestCase):
    """Two releases are compared only where they measured the same thing."""

    def test_the_same_configuration_pairs(self):
        new = row(wall=4.0, rss=50.0, optimizations=['automatic symmetry'])
        old = row(OLD, wall=8.0, rss=200.0, optimizations=['automatic symmetry'])
        tlc = baseline_of(new)
        twin = row(NEW, tool='tlx', mode='-tlc', wall=6.0, rss=60.0, args=('-tlc',))
        pairs = R.compare_releases([new, old, tlc, twin], NEW, OLD)
        self.assertEqual(len(pairs), 2)
        pair = next(p for p in pairs if p['mode'] == 'default')
        self.assertEqual(pair['prev_wall_ratio'], 2.0)
        self.assertEqual(pair['prev_rss_ratio'], 4.0)
        self.assertEqual(pair['tlc_wall_ratio'], 5.0)
        self.assertEqual(pair['tlc_rss_ratio'], 10.0)
        self.assertEqual(pair['twin_s'], 6.0)
        self.assertEqual(pair['new_optimizations'], [])
        self.assertEqual(pair['new']['optimizations'], ['automatic symmetry'])
        self.assertEqual(pair['tlc']['wall_s'], 20.0)

    def test_another_machine_is_not_paired(self):
        new = row()
        old = row(OLD, instance='ecs.c8y.4xlarge')
        pairs = R.compare_releases([new, old], NEW, OLD)
        self.assertEqual(len(pairs), 1)
        self.assertIsNone(pairs[0]['prev'])
        self.assertIsNone(pairs[0]['prev_wall_ratio'])

    def test_changed_inputs_are_not_paired(self):
        new = row()
        old = row(OLD, digest='d' * 64)
        pairs = R.compare_releases([new, old], NEW, OLD)
        self.assertIsNone(pairs[0]['prev'])

    def test_another_tlc_version_is_not_paired(self):
        new = row()
        old = row(OLD, tlc_version='1700000')
        pairs = R.compare_releases([new, old], NEW, OLD)
        self.assertIsNone(pairs[0]['prev'])

    def test_rows_of_another_machine_class_are_excluded(self):
        pairs = R.compare_releases([row(instance='ecs.c8y.4xlarge')], NEW, OLD)
        self.assertEqual(pairs, [])

    def test_a_baseline_of_another_machine_is_not_a_ratio(self):
        new = row()
        tlc = baseline_of(new, instance='ecs.c8y.4xlarge')
        pairs = R.compare_releases([new, tlc], NEW, OLD)
        self.assertIsNone(pairs[0]['tlc'])
        self.assertIsNone(pairs[0]['tlc_wall_ratio'])

    def test_an_incomplete_or_diagnostic_row_is_excluded(self):
        for raw in (row(result='timeout', wall=600.0),
                    row(count_problems=['sample 1: TLC results disagree'])):
            with self.subTest(row=raw):
                self.assertEqual(R.compare_releases([raw], NEW, OLD), [])

    def test_new_optimizations_are_the_difference(self):
        new = row(optimizations=['automatic symmetry', 'threshold counters'])
        old = row(OLD, optimizations=['automatic symmetry'])
        pairs = R.compare_releases([new, old], NEW, OLD)
        self.assertEqual(pairs[0]['new_optimizations'], ['threshold counters'])

    def test_a_row_without_a_previous_release_states_no_new_optimization(self):
        # Every optimization of an unpaired row is its own, not a new one.
        new = row(optimizations=['automatic symmetry'])
        pairs = R.compare_releases([new], NEW, None)
        self.assertEqual(pairs[0]['new_optimizations'], [])
        text = R.render_release_report(pairs, tag='v0.1.2', prev_tag=None)
        self.assertTrue(section(text, '## Cohort summary').splitlines()[-1].rstrip().endswith('| 0 |'))

    def test_a_dirty_record_is_never_a_release(self):
        pairs = R.compare_releases([row(), row(OLD + '-dirty')], NEW, OLD)
        self.assertEqual(len(pairs), 1)
        self.assertIsNone(pairs[0]['prev'])

    def test_a_dirty_row_of_the_new_revision_is_excluded(self):
        self.assertEqual(R.compare_releases([row(NEW + '-dirty')], NEW, OLD), [])

    def test_unknown_identifying_dimensions_do_not_pair(self):
        # Two unknown digests are two possibly different inputs: equal `None`s
        # are not evidence, so the row stays unpaired (`HARNESS-19`).
        cases = ({'digest': None}, {'tlc_version': None},
                 {'machine': 'tencent SA5.4XLARGE32'})  # no architecture recorded
        for changes in cases:
            with self.subTest(**changes):
                pairs = R.compare_releases([row(**changes), row(OLD, **changes)], NEW, OLD)
                self.assertEqual(len(pairs), 1)
                self.assertIsNone(pairs[0]['prev'])
                self.assertIsNone(pairs[0]['prev_wall_ratio'])

    def test_without_a_previous_release_nothing_is_paired(self):
        pairs = R.compare_releases([row()], NEW, None)
        self.assertEqual(len(pairs), 1)
        self.assertIsNone(pairs[0]['prev'])
        self.assertIsNone(pairs[0]['prev_wall_ratio'])


class Report(unittest.TestCase):
    """The rendered comparison: which rows are flagged, and deterministic bytes."""

    def pairs(self, *rows):
        return R.compare_releases(list(rows), NEW, OLD)

    def pair(self, *, old_wall, new_wall, model='ext/etcd/MCetcdraft', rss_old=200.0, rss_new=100.0):
        new = row(model=model, wall=new_wall, rss=rss_new)
        old = row(OLD, model=model, wall=old_wall, rss=rss_old)
        return R.compare_releases([new, old], NEW, OLD)[0]

    def test_both_regression_bounds_are_required(self):
        pairs = [self.pair(old_wall=10.0, new_wall=10.6, model='both bounds'),
                 self.pair(old_wall=0.10, new_wall=0.107, model='relative only'),
                 self.pair(old_wall=10.0, new_wall=10.2, model='neither')]
        flagged = R.regressions(pairs)
        self.assertEqual([p['model'] for p in flagged], ['both bounds'])

    def test_the_report_flags_the_regressed_row_only(self):
        pairs = [self.pair(old_wall=10.0, new_wall=12.0, model='ext/kafka/slow'),
                 self.pair(old_wall=10.0, new_wall=10.2, model='ext/etcd/fine')]
        text = R.render_release_report(pairs, tag='v0.1.2', prev_tag='v0.1.1', sha=NEW, prev_sha=OLD)
        flagged = section(text, '### Wall-time regressions')
        self.assertIn('ext/kafka/slow', flagged)
        self.assertNotIn('ext/etcd/fine', flagged)
        self.assertIn('20.00%', flagged)

    def test_a_memory_reduction_is_the_fraction_saved(self):
        pairs = [self.pair(old_wall=8.0, new_wall=4.0, rss_old=400.0, rss_new=100.0)]
        text = R.render_release_report(pairs, tag='v0.1.2', prev_tag='v0.1.1')
        table = section(text, '### Largest peak-memory reductions')
        # 400 MiB -> 100 MiB is 75% saved (a 4.00x ratio), never 300%.
        self.assertIn('| 75.00% | 4.00× |', table)
        self.assertNotIn('300.00%', table)

    def test_a_gain_table_lists_only_improvements(self):
        pairs = [self.pair(old_wall=4.0, new_wall=4.4, model='ext/a/slower'),
                 self.pair(old_wall=4.0, new_wall=4.0, model='ext/b/same'),
                 self.pair(old_wall=4.0, new_wall=2.0, model='ext/c/faster')]
        text = R.render_release_report(pairs, tag='v0.1.2', prev_tag='v0.1.1')
        gains = section(text, '### Largest wall-time gains')
        self.assertIn('ext/c/faster', gains)
        self.assertNotIn('ext/a/slower', gains)
        self.assertNotIn('ext/b/same', gains)

    def test_a_memory_increase_is_not_a_reduction(self):
        pairs = [self.pair(old_wall=4.0, new_wall=2.0, model='ext/a/grew',
                           rss_old=100.0, rss_new=200.0),
                 self.pair(old_wall=4.0, new_wall=2.0, model='ext/b/shrank',
                           rss_old=200.0, rss_new=100.0)]
        text = R.render_release_report(pairs, tag='v0.1.2', prev_tag='v0.1.1')
        memory = section(text, '### Largest peak-memory reductions')
        self.assertIn('ext/b/shrank', memory)
        self.assertNotIn('ext/a/grew', memory)

    def test_the_gains_table_states_each_number_once(self):
        pairs = [self.pair(old_wall=4.0, new_wall=2.0)]
        text = R.render_release_report(pairs, tag='v0.1.2', prev_tag='v0.1.1')
        gains = section(text, '### Largest wall-time gains')
        header = next(line for line in gains.splitlines() if line.startswith('| Model / mode'))
        self.assertNotIn('Speedup', header)
        self.assertEqual(header.count('prev / new'), 1)

    def test_cohort_medians_and_geometric_mean(self):
        pairs = [self.pair(old_wall=8.0, new_wall=4.0, model='ext/a/x'),
                 self.pair(old_wall=8.0, new_wall=2.0, model='ext/b/y')]
        text = R.render_release_report(pairs, tag='v0.1.2', prev_tag='v0.1.1')
        summary = section(text, '## Cohort summary')
        # medians of prev/new = {2, 4}: median 3, geometric mean sqrt(8) = 2.83
        self.assertIn('| default / 1 | 2 | 2 | 3.00× | 2.83×', summary)

    def test_the_report_is_deterministic(self):
        pairs = self.pairs(row(wall=4.0), row(OLD, wall=8.0))
        one = R.render_release_report(pairs, tag='v0.1.2', prev_tag='v0.1.1', sha=NEW, prev_sha=OLD)
        two = R.render_release_report(pairs, tag='v0.1.2', prev_tag='v0.1.1', sha=NEW, prev_sha=OLD)
        self.assertEqual(one, two)
        for heading in ('# v0.1.2 vs. v0.1.1', '## Cohort summary',
                        '## Regressions and notable gains', '## Flagship open-source models'):
            self.assertIn(heading, one)

    def test_flagship_rows_name_both_releases_and_tlc(self):
        new = row(model='MC_tlx_Zab_new', wall=4.0, rss=50.0, optimizations=['automatic symmetry'])
        old = row(OLD, model='MC_tlx_Zab_new', wall=8.0, rss=100.0)
        tlc = baseline_of(new, wall=40.0, rss=400.0)
        pairs = R.compare_releases([new, old, tlc], NEW, OLD)
        text = R.render_release_report(pairs, tag='v0.1.2', prev_tag='v0.1.1')
        flagship_table = section(text, '## Flagship open-source models')
        self.assertIn('MC_tlx_Zab_new / default', flagship_table)
        self.assertIn('| 8.00 | 100.00 | 4.00 | 50.00 | 40.00 | 400.00 | 10.00× |', flagship_table)
        self.assertIn('automatic symmetry', flagship_table)

    def test_an_empty_store_says_what_is_missing(self):
        text = R.render_release_report([], tag='v0.1.2', prev_tag='v0.1.1', sha=NEW)
        self.assertIn('No eligible `tlx` measurement of `v0.1.2`', text)
        self.assertNotIn('## Cohort summary', text)

    def test_without_a_previous_release_the_columns_are_empty(self):
        text = R.render_release_report(self.pairs(row()), tag='v0.1.2', prev_tag=None)
        self.assertIn('No previous release was named', text)
        self.assertIn('| default / 1 | 1 | 0 | — | — |', text)

    def test_a_store_without_the_previous_release_says_so(self):
        text = R.render_release_report(self.pairs(row()), tag='v0.1.2', prev_tag='v0.1.1')
        self.assertIn('No eligible `tlx` measurement of `v0.1.1`', text)


class Command(unittest.TestCase):
    """`bench.py release`: the report-only pass and the campaign's dry run."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def patched(self, **extra):
        patches = [patch.object(R, 'resolve_release_tags', return_value=dict(TAGS)),
                   patch.object(R, 'head_revision', return_value='f' * 40)]
        patches += [patch.object(R, name, value) for name, value in extra.items()]
        return patches

    def run_release(self, argv, **patched):
        """`(return value, stdout, stderr)` with the named attributes patched."""
        errors = io.StringIO()
        with contextlib.ExitStack() as stack:
            for manager in self.patched(**patched):
                stack.enter_context(manager)
            with contextlib.redirect_stderr(errors):
                code, text = output_of(lambda: R.cmd_release(release_args(argv)))
        return code, text, errors.getvalue()

    def test_dry_run_prints_the_launches_and_runs_nothing(self):
        def refuse(*args, **kwargs):
            raise AssertionError('a dry run launches nothing')

        code, text, _ = self.run_release(['v0.1.2', '--dry-run', '--slices', '2', '--slots', '4'],
                                         **{'subprocess': patch.object(R.subprocess, 'run', refuse)})
        self.assertEqual(code, 0)
        launches = text.splitlines()
        self.assertEqual(len(launches), 3)
        self.assertIn('tlcbase --missing --collect', launches[0])
        self.assertNotIn('--bench-bin', launches[0])
        for number, line in enumerate(launches[1:], 1):
            self.assertIn(f'suite --missing --slice {number}/2', line)
            self.assertIn(f'--bin-rev {NEW}', line)
            self.assertIn(f'--bench-bin rel={NEW}', line)
            self.assertIn('--isolate-cache --with-tlc-companion', line)
            self.assertIn(f'--out bench/history/suite-v0.1.2-s{number}of2.json', line)
            self.assertIn('--max-minutes 140', line)
            self.assertIn('--slots 4', line)
        self.assertIn('cloud_verify.py ' + 'f' * 40, launches[0])

    def test_dry_run_keeps_a_resumed_campaign_off_an_ingested_shard(self):
        history = self.root / 'bench' / 'history'
        history.mkdir(parents=True)
        (history / 'suite-v0.1.2-s1of1.json').write_text('{}')
        with patch.object(R, 'ROOT', str(self.root)):
            out = R.history_path('suite-v0.1.2-s1of1', self.root)
        self.assertEqual(out, 'bench/history/suite-v0.1.2-s1of1-2.json')

    def test_report_only_renders_without_launching(self):
        def refuse(*args, **kwargs):
            raise AssertionError('--report-only launches nothing')

        markdown = self.root / 'out' / 'release.md'
        code, text, _ = self.run_release(
            ['v0.1.2', '--report-only', '--markdown', str(markdown)],
            **{'subprocess': patch.object(R.subprocess, 'run', refuse),
               'load_records': lambda root=R.ROOT: [row(wall=4.0), row(OLD, wall=8.0)]})
        self.assertEqual(code, 0)
        self.assertEqual(markdown.read_text(), text)
        self.assertIn('# v0.1.2 vs. v0.1.1', text)
        self.assertIn('2.00×', text)

    def test_a_shard_count_below_one_is_refused(self):
        with self.assertRaises(SystemExit) as refused:
            self.run_release(['v0.1.2', '--slices', '0'])
        self.assertIn('--slices must be at least 1', str(refused.exception))


class CampaignSelection(unittest.TestCase):
    """`--models`/`--sizes` reach both launches as the manifest's exact ids."""

    SUITE = {'models': [{'id': 'ext/etcd/A', 'size': 'small'},
                        {'id': 'ext/etcd/B', 'size': 'huge'},
                        {'id': 'ext/zab/C', 'size': 'small'}]}
    HEAD = 'f' * 40

    def launches(self, *argv):
        return R.campaign_commands(release_args(['v0.1.2', *argv]), TAGS, self.HEAD, self.SUITE)

    def test_a_substring_becomes_exact_ids_on_both_launches(self):
        # `tlcbase --models` accepts only ids that exist, so the substring the
        # suite understands has to be resolved before it is forwarded.
        launches = self.launches('--models', 'ext/etcd')
        self.assertIn('--models ext/etcd/A,ext/etcd/B', launches[0]['bench'])
        self.assertIn('--models ext/etcd/A,ext/etcd/B', launches[1]['bench'])

    def test_a_size_filter_excludes_the_other_size_classes(self):
        launches = self.launches('--sizes', 'small')
        self.assertIn('--models ext/etcd/A,ext/zab/C', launches[0]['bench'])
        self.assertNotIn('ext/etcd/B', launches[0]['bench'])
        self.assertIn('--sizes small', launches[1]['bench'])

    def test_a_selection_that_matches_nothing_is_refused(self):
        with self.assertRaises(SystemExit) as refused:
            self.launches('--models', 'ext/nope')
        self.assertIn('selects no model', str(refused.exception))

    def test_sizes_all_is_not_a_size_class(self):
        # `--sizes all` is the suite's own spelling for every class (huge
        # included); read as a literal class name it selected nothing.
        launches = self.launches('--sizes', 'all')
        self.assertNotIn('--models', launches[0]['bench'])
        self.assertNotIn('--models', launches[1]['bench'])
        self.assertIn('--sizes all', launches[1]['bench'])

    def test_a_huge_model_named_without_sizes_is_not_dropped(self):
        # `suite --sizes` defaults to small,medium,large: an explicit --models
        # has to keep a `huge` model, or the instance is provisioned to run
        # nothing.
        launches = self.launches('--models', 'ext/etcd/B')
        self.assertIn('--models ext/etcd/B', launches[0]['bench'])
        self.assertIn('--models ext/etcd/B', launches[1]['bench'])
        self.assertIn('--sizes all', launches[1]['bench'])

    def test_no_filter_leaves_each_pass_its_own_default(self):
        launches = self.launches()
        self.assertNotIn('--models', launches[0]['bench'])
        self.assertNotIn('--models', launches[1]['bench'])
        self.assertNotIn('--sizes', launches[1]['bench'])


class Campaign(unittest.TestCase):
    """What a launch has to return before its measurements are recorded."""

    HEAD = 'f' * 40
    OUT = 'bench/history/suite-v0.1.2-s1of1.json'
    BENCH = 'suite --missing --slice 1/1 --out ' + OUT

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.bins = [('rel', NEW, '')]

    def launch(self, **over):
        """The `_launch` record a campaign would run."""
        item = {'label': 'shard', 'argv': ['true'], 'bench': self.BENCH,
                'out': self.OUT, 'bins': self.bins}
        item.update(over)
        return item

    def receipt_dir(self, name, *, bench=None, rev=HEAD, code=0, bins=None, history=True):
        """One receipt directory as cloud_verify.py leaves it."""
        directory = self.root / 'target' / 'bench' / name
        (directory / 'bench' / 'history').mkdir(parents=True)
        receipt = {'rev': rev, 'verify_exit': code, 'bench': [bench or self.BENCH],
                   'bench_bins': [{'name': n, 'rev': r, 'features': f}
                                  for n, r, f in (bins if bins is not None else self.bins)]}
        (directory / 'cloud.json').write_text(json.dumps(receipt))
        if history:
            (directory / self.OUT).write_text('{"suite": {}}')
        return directory

    def writing_receipts(self, code, receipts):
        """A `subprocess.run` replacement that writes one receipt per launch.

        This is what a real launch does: its receipt directory is created while
        it runs, so `run_campaign`'s before/after snapshot sees exactly it.
        """
        calls = []

        def fake_run(argv, cwd=None):
            entry = receipts[len(calls)]
            calls.append(argv)
            if entry is not None:
                self.receipt_dir(f'run{len(calls)}', **{'code': code, **entry})
            return subprocess.CompletedProcess(argv, code)
        return fake_run

    def checked_campaign(self, code, launches, receipts):
        """`(return value, record mock, generate mock)`, with the result writes mocked."""
        with patch.object(R.subprocess, 'run', self.writing_receipts(code, receipts)), \
                patch.object(R, 'record') as record, patch.object(R, 'generate') as generate, \
                contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            ok = R.run_campaign(self.HEAD, launches, self.root)
        return ok, record, generate

    def test_the_receipt_that_pins_the_launch_holds_the_history(self):
        directory = self.receipt_dir('run1')
        self.assertEqual(R.launch_result(self.HEAD, self.launch(), 0, self.root),
                         (directory / self.OUT, True))

    def test_a_receipt_of_another_binary_authorizes_nothing(self):
        self.receipt_dir('run1', bins=[('rel', OLD, '')])
        self.assertEqual(R.launch_result(self.HEAD, self.launch(), 0, self.root), (None, False))

    def test_a_receipt_of_another_launch_authorizes_nothing(self):
        # Every shard shares revision and pinned binary; the command tells them apart.
        self.receipt_dir('run1', bench='suite --missing --slice 2/2 --out ' + self.OUT)
        self.assertEqual(R.launch_result(self.HEAD, self.launch(), 0, self.root), (None, False))

    def test_two_receipts_for_the_same_launch_are_ambiguous(self):
        self.receipt_dir('run1')
        self.receipt_dir('run2')
        self.assertEqual(R.launch_result(self.HEAD, self.launch(), 0, self.root), (None, False))

    def test_a_zero_exit_with_a_receipt_and_no_history_is_a_no_op(self):
        # `--missing` with nothing missing completes without writing `--out`.
        self.receipt_dir('run1', history=False)
        self.assertEqual(R.launch_result(self.HEAD, self.launch(), 0, self.root), (None, True))

    def test_a_rerun_of_a_zero_missing_launch_uses_only_its_new_receipt(self):
        # Resuming a campaign re-issues the same command (a 0-missing launch
        # leaves no history file to take the name), so the earlier no-op's
        # receipt is still on disk and must not make this one ambiguous.
        self.receipt_dir('previous', history=False)
        fresh = self.receipt_dir('fresh', history=False)
        before = frozenset({'previous'})
        self.assertEqual(R.launch_result(self.HEAD, self.launch(), 0, self.root, exclude=before),
                         (None, True))
        self.assertIn(fresh.name, R.receipt_names(self.root))

    def test_a_stale_receipt_does_not_authorize_a_launch_that_wrote_none(self):
        self.receipt_dir('previous', history=False)
        self.assertEqual(R.launch_result(self.HEAD, self.launch(), 0, self.root,
                                        exclude=frozenset({'previous'})), (None, False))

    def test_a_zero_missing_launch_does_not_stop_the_campaign(self):
        # Regression: the baseline pass exits 0 without a history file whenever
        # nothing is missing, which aborted every later release's campaign.
        launches = [self.launch(bench='tlcbase --missing --collect'), self.launch()]
        ok, record, generate = self.checked_campaign(
            0, launches, [{'bench': 'tlcbase --missing --collect', 'history': False}, {}])
        self.assertTrue(ok)
        record.assert_called_once_with(
            self.root / 'target/bench/run2/bench/history' / Path(self.OUT).name, self.root)
        generate.assert_called_once_with(root=self.root, refresh=True)

    def test_a_resumed_zero_missing_launch_does_not_stop_the_campaign(self):
        # Regression: the second invocation's receipt joins the first no-op's,
        # and both match revision, binary, exit and command.
        self.receipt_dir('previous', bench='tlcbase --missing --collect', history=False)
        launches = [self.launch(bench='tlcbase --missing --collect')]
        ok, record, generate = self.checked_campaign(
            0, launches, [{'bench': 'tlcbase --missing --collect', 'history': False}])
        self.assertTrue(ok)
        record.assert_not_called()
        generate.assert_called_once_with(root=self.root, refresh=True)

    def test_a_nonzero_verdict_without_its_history_stops_the_campaign(self):
        ok, record, generate = self.checked_campaign(1, [self.launch()], [{'history': False}])
        self.assertFalse(ok)
        record.assert_not_called()
        generate.assert_not_called()

    def test_a_launch_without_an_authorizing_receipt_stops_the_campaign(self):
        ok, record, generate = self.checked_campaign(0, [self.launch()], [None])
        self.assertFalse(ok)
        record.assert_not_called()
        generate.assert_not_called()

    def test_a_stale_receipt_does_not_stand_in_for_this_launch(self):
        # The only matching receipt predates the launch: it authorizes nothing.
        self.receipt_dir('previous')
        ok, record, generate = self.checked_campaign(0, [self.launch()], [None])
        self.assertFalse(ok)
        record.assert_not_called()

    def test_a_refused_launch_records_nothing(self):
        ok, record, generate = self.checked_campaign(3, [self.launch()], [{}])
        self.assertFalse(ok)
        record.assert_not_called()
        generate.assert_not_called()

    def test_a_recorded_launch_imports_its_history_and_regenerates(self):
        directory = self.root / 'target' / 'bench' / 'run1'
        with patch.object(R.subprocess, 'run', self.writing_receipts(0, [{}])), \
                patch.object(R, 'ingest') as ingest, patch.object(R, 'generate') as generate, \
                contextlib.redirect_stdout(io.StringIO()):
            self.assertTrue(R.run_campaign(self.HEAD, [self.launch()], self.root))
        ingest.assert_called_once_with(self.root / self.OUT, self.root)
        self.assertEqual((self.root / self.OUT).read_text(), '{"suite": {}}')
        generate.assert_called_once_with(root=self.root, refresh=True)
        self.assertTrue((directory / self.OUT).exists())


class ReleaseWorkflow(unittest.TestCase):
    """The tag webhook notifies for a published X.Y.Z release and nothing else."""

    def test_the_tag_check_is_a_strict_release_pattern(self):
        text = (Path(R.ROOT) / '.github/workflows/release-benchmark.yml').read_text()
        # The GitHub glob trigger also matches `v0.2.0-rc1`; only the strict
        # pattern gates the webhook, and it keeps the payload JSON-safe.
        self.assertIn(r'[[ ! "$tag" =~ ^v[0-9]+\.[0-9]+\.[0-9]+$ ]]', text)
        self.assertNotIn('v[0-9]*.[0-9]*.[0-9]*', text)

    def test_an_unset_secret_and_a_non_release_are_no_ops(self):
        text = (Path(R.ROOT) / '.github/workflows/release-benchmark.yml').read_text()
        self.assertIn('MULTICA_RELEASE_BENCH_WEBHOOK_URL is not set', text)
        self.assertIn('nothing to notify', text)
        self.assertIn('--data-binary @release-benchmark-payload.json', text)


if __name__ == '__main__':
    unittest.main()
