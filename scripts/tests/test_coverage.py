"""Native census contracts: actual path counts, missing evidence and attribution."""
import unittest
import json
import os
import subprocess
import sys
import tempfile
import shutil
from unittest.mock import patch
import coverage as C


class Reports(unittest.TestCase):
    def test_dynamic_uses_actual_native_calls_and_all_predicate_kinds(self):
        stats = {'actions': [{'name': 'Next', 'calls': {'native': 2, 'mixed': 5, 'ir': 3}, 'fully_native': 4}],
                 'invariants': [{'calls': {'interp': 2}, 'fully_native': 0}],
                 'action_properties': [{'calls': {'native': 2}, 'fully_native': 2}],
                 'units_time_est_s': 4,
                 'native_regions_1': [{'operation': 'ValOp \\in', 'arguments': ['Dyn', 'Set(Dyn)'], 'calls': 9, 'time_s': 1, 'context': 'Action'}],
                 'native_regions_2': [{'operation': 'MapSet', 'arguments': ['Dyn'], 'calls': 2, 'time_s': .5, 'context': 'Action'}]}
        d = C.dynamic_report(stats)
        self.assertEqual(d['evaluations'], 14)
        self.assertEqual(d['fully_native'], 6)
        self.assertAlmostEqual(d['native_share'], 6 / 14)
        self.assertAlmostEqual(d['host_time_share'], .375)
        self.assertEqual(d['host_calls'], 11)

    def test_missing_and_empty_stats_are_unknown_not_zero_or_one(self):
        self.assertIsNone(C.dynamic_report({})['native_share'])
        self.assertIsNone(C.dynamic_report({'actions': [{'calls': {'native': 1}}]})['native_share'])
        self.assertIsNone(C.dynamic_report({'actions': []})['host_time_share'])

    def test_ranking_groups_same_operation_and_shapes_across_models(self):
        op = {'operation': 'ValOp \\in', 'arguments': ['Dyn', 'Set(Dyn)'], 'calls': 7, 'time_s': .25}
        ranked = C.rank_operations([{'id': 'a', 'dynamic': {'regions': [op]}},
                                    {'id': 'b', 'dynamic': {'regions': [op]}}])
        self.assertEqual(ranked[0]['models'], ['a', 'b'])
        self.assertEqual(ranked[0]['calls'], 14)
        self.assertEqual(ranked[0]['time_s'], .5)
        self.assertTrue(ranked[0]['family'])

    def test_unexecuted_region_is_present_but_not_a_dynamically_affected_model(self):
        op = {'operation': 'ValOp \\in', 'arguments': ['Val', 'Val'], 'calls': 7, 'time_s': .25}
        rows = C.rank_operations([{'id': 'hot', 'dynamic': {'regions': [op]}},
                                  {'id': 'cold', 'dynamic': {'regions': [{**op, 'calls': 0, 'time_s': 0}]}}])
        self.assertEqual(rows[0]['models'], ['cold', 'hot'])
        self.assertEqual(rows[0]['executed_models'], ['hot'])

    def test_static_keeps_typed_boxed_and_interpreted_by_kind(self):
        out = 'compile: node typed 5 Var | Int\ncompile: node boxed 2 ValOp \\in | Val, Set(Dyn)\ncompile: node interpreted 1 Interp Apply | Val\ncgen: action Next not native: unsupported SortSeq\n'
        s = C.static_report(out)
        self.assertEqual(s['nodes']['typed'], 5)
        self.assertEqual(s['nodes']['boxed'], 2)
        self.assertEqual(s['nodes']['interpreted'], 1)
        self.assertIn('SortSeq', s['closure_functions'][0]['reason'])

    def test_static_cli_keeps_nodes_and_rejection_reasons_without_json(self):
        import io
        from contextlib import redirect_stdout
        static = C.static_report('compile: node typed 5 Var | Int\ncgen: action Next not native: unsupported SortSeq\n')
        report = {'selected': 1, 'reported': 1, 'measured': 0, 'models': [
            {'status': 'static only', 'static': static, 'dynamic': C.dynamic_report({})}], 'operations': []}
        out = io.StringIO()
        with redirect_stdout(out):
            C.print_report(report)
        self.assertIn('typed 5; boxed 0; interpreted 0', out.getvalue())
        self.assertIn('unsupported SortSeq', out.getvalue())
        self.assertIn('(unknown)', out.getvalue())

    def test_supplied_timeout_stats_are_partial_even_with_success_output(self):
        from types import SimpleNamespace
        with tempfile.TemporaryDirectory() as tmp:
            tla, cfg = os.path.join(tmp, 'A.tla'), os.path.join(tmp, 'A.cfg')
            for path in (tla, cfg):
                with open(path, 'w') as f:
                    f.write('fixture')
            def finish(cmd, timeout, **kwargs):
                self.assertIsNone(kwargs['on_line'])
                self.assertEqual(kwargs['grace'], C.TIMEOUT_GRACE)
                path = cmd[cmd.index('-stats') + 1].removeprefix('json=')
                with open(path, 'w') as f:
                    json.dump({'actions': [{'name': 'Next', 'calls': {'native': 3}, 'fully_native': 3}]}, f)
                return SimpleNamespace(stdout='Model checking completed. No error has been found.\n',
                                       stderr='compile: node typed 1 Var | Int\n', wall=.1, returncode=0, timed_out=True)
            with patch.object(C, 'run_proc', side_effect=finish):
                r = C.run({'id': 'fixture', 'tla': tla, 'cfg': cfg}, 1, '/usr/bin/true', True)
            self.assertEqual(r['status'], 'timeout')
            self.assertIsNone(r['dynamic']['native_share'])
            self.assertEqual(r['dynamic']['partial_native_share'], 1)
            self.assertFalse(r['dynamic']['complete'])
            self.assertEqual(r['static']['nodes']['typed'], 1)

    def test_real_engine_timeout_without_final_stats_remains_unknown(self):
        binary = next((os.path.join(C.ROOT, 'target', profile, 'tlx')
                       for profile in ('test-release', 'release')
                       if os.path.isfile(os.path.join(C.ROOT, 'target', profile, 'tlx'))), None)
        if binary is None:
            self.skipTest('build tlx first for real SIGTERM coverage acceptance')
        with tempfile.TemporaryDirectory() as tmp:
            tla, cfg = os.path.join(tmp, 'CensusTimeout.tla'), os.path.join(tmp, 'CensusTimeout.cfg')
            with open(tla, 'w') as f:
                f.write('---- MODULE CensusTimeout ----\nEXTENDS Naturals\nVARIABLE x\n'
                        "Init == x = 0\nNext == x < 1000000000 /\\ x' = x + 1\n====\n")
            with open(cfg, 'w') as f:
                f.write('INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n')
            # Allow enough time for C compilation on slow CI runners so the
            # static coverage report is printed before SIGTERM stops BFS.
            r = C.run({'id': 'signal-fixture', 'tla': tla, 'cfg': cfg}, 15, binary, True)
            self.assertEqual(r['status'], 'timeout')
            self.assertTrue(r['static']['reported'], r['output'])
            self.assertIsNone(r['dynamic']['native_share'])
            self.assertIsNone(r['dynamic']['partial_native_share'])
            self.assertFalse(r['dynamic']['complete'])
            self.assertEqual(r['stats'], {})

    def test_the_staged_trace_input_closes_the_ewd998_census_gap(self):
        """The one small-census unknown that was staging, not an engine gap.

        docs/native-coverage.md records EWD998ChanTrace among the small
        census's unknown metrics because its spec names its trace input
        relative to the Examples root and the census ran it from its own
        directory. The model is marked `cwd: root` (scripts/corpus.py), so the
        census measures it now; this pins the reduced example with the checked
        in trace (659 distinct states, depth 655).
        """
        binary = next((os.path.join(C.ROOT, 'target', profile, 'tlx')
                       for profile in ('test-release', 'release')
                       if os.path.isfile(os.path.join(C.ROOT, 'target', profile, 'tlx'))), None)
        if binary is None:
            self.skipTest('build tlx first for the real coverage measurement')
        import corpus
        import tlxlib
        models = {m['id']: m for m in corpus.models(float('inf'))}
        m = models.get('ewd998/EWD998ChanTrace')
        if m is None or not os.path.isfile(os.path.join(m['root'], 'specifications', 'ewd998',
                                                        'EWD998ChanTrace.ndjson')):
            self.skipTest('the Examples corpus with the EWD998 trace is not in this checkout')
        self.assertEqual(tlxlib.model_cwd(m), m['root'])
        r = C.run(m, 120, binary, True)
        self.assertEqual(r['status'], 'success', r.get('output'))
        self.assertTrue(r['dynamic']['complete'])
        self.assertGreater(r['dynamic']['evaluations'], 0)

    def test_truncated_final_stats_remain_an_explicit_gap(self):
        from types import SimpleNamespace
        with tempfile.TemporaryDirectory() as tmp:
            tla, cfg = os.path.join(tmp, 'A.tla'), os.path.join(tmp, 'A.cfg')
            for path in (tla, cfg):
                with open(path, 'w') as f:
                    f.write('fixture')
            def finish(cmd, timeout, **kwargs):
                path = cmd[cmd.index('-stats') + 1].removeprefix('json=')
                with open(path, 'w') as f:
                    f.write('{')
                return SimpleNamespace(stdout='Model checking completed. No error has been found.\n',
                                       stderr='', wall=.1, returncode=0, timed_out=False)
            with patch.object(C, 'run_proc', side_effect=finish):
                r = C.run({'id': 'fixture', 'tla': tla, 'cfg': cfg}, 1, '/usr/bin/true', True)
            self.assertEqual(r['status'], 'stats error')
            self.assertIsNone(r['dynamic']['native_share'])
            self.assertIn('stats_read_error', r)
            self.assertFalse(r['dynamic']['complete'])


class Families(unittest.TestCase):
    def test_symbolic_comparisons_and_function_operators_keep_their_family(self):
        for prefix in ('ValOp ', 'Interp builtin '):
            for symbol in ('=', '#', '<', '<=', '>', '>='):
                self.assertEqual(C.lowering_family(prefix + symbol), 'Heterogeneous comparison and membership')
            for symbol in ('DOMAIN', '@@', ':>'):
                self.assertEqual(C.lowering_family(prefix + symbol), 'Functions and records with dynamic values')

    def test_sequence_names_are_not_substring_equality(self):
        self.assertEqual(C.lowering_family('Interp FnApp'), 'Functions and records with dynamic values')
        for op in ('SeqAppend', 'SeqSub', 'SeqLen', 'Subseq', 'ValOp Len'):
            self.assertEqual(C.lowering_family(op), 'Sequences with dynamic elements')

    def test_closure_only_blocker_still_enters_dispatch_ranking(self):
        r = C.rank_operations([{'id': 'closure', 'dynamic': {'regions': [], 'closure_evaluations': [
            {'function': 'Next', 'calls': {'ir': 10}, 'blockers': ['unsupported SortSeq']}]}}])
        self.assertEqual(r[0]['calls'], 10)
        self.assertIsNone(r[0]['time_s'])
        self.assertEqual(r[0]['attribution'], 'closure_function')

    def test_missing_static_reason_is_not_claimed_as_a_lowering_blocker(self):
        ranked = C.rank_operations([{'id': 'adapt', 'dynamic': {'regions': [], 'closure_evaluations': [
            {'function': 'Next', 'calls': {'ir': 10}, 'blockers': []}]}}])
        self.assertIn('unattributed execution path', ranked[0]['operation'])
        self.assertIn('tier selection', ranked[0]['family'])


class SubprocessFailures(unittest.TestCase):
    def test_silent_engine_is_incomplete_for_census_and_cloud_forwarder(self):
        for driver in ('coverage.py', 'bench.py'):
            with self.subTest(driver=driver), tempfile.TemporaryDirectory() as tmp:
                out = os.path.join(tmp, 'report.json')
                # Copy the complete import closure rather than depending on a
                # contributor's installed Examples corpus or a hand-picked module list.
                scripts = os.path.join(tmp, 'scripts')
                shutil.copytree(os.path.dirname(os.path.dirname(__file__)), scripts,
                                ignore=shutil.ignore_patterns('__pycache__'))
                spec_dir = os.path.join(tmp, 'third_party', 'Examples', 'specifications', 'fixture')
                os.makedirs(spec_dir)
                with open(os.path.join(spec_dir, 'manifest.json'), 'w') as stream:
                    json.dump({'modules': [{'path': 'specifications/fixture/Silent.tla', 'models': [
                        {'path': 'specifications/fixture/Silent.cfg', 'mode': 'exhaustive search',
                         'runtime': '00:00:01'}]}]}, stream)
                for filename, text in [('Silent.tla', "---- MODULE Silent ----\nVARIABLE x\nInit == x = 0\nNext == x' = x\n====\n"),
                                       ('Silent.cfg', 'INIT Init\nNEXT Next\n')]:
                    with open(os.path.join(spec_dir, filename), 'w') as stream:
                        stream.write(text)
                subprocess.run(['git', 'init', '-q', tmp], check=True, capture_output=True)
                subprocess.run(['git', '-C', tmp, '-c', 'user.name=Test Fixture',
                                '-c', 'user.email=fixture@example.com', '-c', 'commit.gpgsign=false',
                                'commit', '--allow-empty', '-qm', 'fixture'], check=True, capture_output=True)
                cmd = [sys.executable, os.path.join(scripts, driver)]
                if driver == 'bench.py':
                    cmd += ['coverage']
                cmd += ['--dynamic', '--filter', 'fixture/Silent', '--bin', '/usr/bin/true',
                        '--timeout', '1', '--out', out]
                p = subprocess.run(cmd, cwd=tmp, capture_output=True, text=True)
                self.assertEqual(p.returncode, 2, p.stdout + p.stderr)
                self.assertTrue(os.path.isfile(out), p.stdout + p.stderr)
                with open(out) as f:
                    r = json.load(f)
                self.assertEqual(r['selected'], 1)
                self.assertEqual(r['measured'], 0)
                self.assertIsNone(r['models'][0]['dynamic']['native_share'])


class CloudSmoke(unittest.TestCase):
    def test_cloud_prelaunch_accepts_census_and_uses_its_measurement_path(self):
        from benchmarking import bench_smoke
        self.assertIn('coverage', bench_smoke.MEASURE_COMMANDS)
        import argparse
        with patch.object(C, 'run', return_value={'status': 'success', 'wall_s': .01, 'dynamic': {'native_share': 1.0}}) as run:
            with patch.object(bench_smoke.os, 'access', return_value=True):
                self.assertEqual(bench_smoke.run(argparse.Namespace(cmd='coverage')), 0)
        self.assertEqual(run.call_count, 3)
        self.assertTrue(run.call_args.args[3])

    def test_prelaunch_clippy_error_is_rejected_before_rebuild_or_provision(self):
        from benchmarking import bench_smoke
        from types import SimpleNamespace
        fresh = unittest.mock.Mock()
        with patch.object(bench_smoke.subprocess, 'run', return_value=SimpleNamespace(returncode=1, stdout='', stderr='clippy sentinel')) as run:
            with self.assertRaisesRegex(ValueError, 'clippy sentinel'):
                bench_smoke.preflight(['coverage --dynamic'], fresh=fresh)
        fresh.assert_not_called()
        self.assertIn('--all-targets', run.call_args.args[0])
        self.assertEqual(run.call_args.args[0][:2], ['cargo', 'clippy'])

    def test_prelaunch_rejects_success_without_a_measured_metric(self):
        from benchmarking import bench_smoke
        import argparse
        with patch.object(C, 'run', return_value={'status': 'success', 'wall_s': .01}):
            with patch.object(bench_smoke.os, 'access', return_value=True):
                with self.assertRaisesRegex(ValueError, 'no dynamic native-share measurement'):
                    bench_smoke.run(argparse.Namespace(cmd='coverage'))


if __name__ == '__main__':
    unittest.main()
