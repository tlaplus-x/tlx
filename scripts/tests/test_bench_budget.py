"""Deadline and compiler fallback guards exercise real benchmark consumers."""

from benchmarking import baselines as bench_baselines
from benchmarking import models as bench_models, machine as bench_machine
from benchmarking import bench_records
import argparse
import contextlib
import io
import json
import os
import subprocess
import sys
import tempfile
from pathlib import Path
import unittest
from unittest import mock
from unittest.mock import patch

import bench
from benchmarking import bench_budget as budget
from benchmarking import bench_disk
from benchmarking import bench_liveness
from benchmarking import bench_profile
from benchmarking import bench_records
from benchmarking import bench_suite
from benchmarking import bench_smoke
from benchmarking import bench_ttfr
from types import SimpleNamespace
from cloud import cloud_common
import cloud_verify
import tlc


class HogPolicy(unittest.TestCase):
    """`--hog` is a cloud measurement, never load on the shared machine.

    The boundary is zero: a spinning process is artificial load wherever it
    runs, so "one or two is fine" is not a cheaper version of the policy -- it
    is a different one (harness audit S6; the owner is section 1 of
    docs/cloud-verification.md, HARNESS-20). The refusal is at the entry point,
    before the smoke path and before anything is built, so it creates no load,
    and the cloud host keeps the measurement it is for.
    """

    def main(self, hog, host):
        """`bench.py ab --hog N` with the pass recorded instead of run."""
        started = []
        with patch.dict(os.environ, {"TLX_CLOUD_HOST": host}, clear=False), \
             patch.object(sys, "argv", ["bench.py", "ab", "--models", "A", "--hog", str(hog)]), \
             patch.object(bench, "cmd_ab", side_effect=lambda a: started.append(a)):
            bench.main()
        return started

    def test_every_local_hog_is_refused(self):
        for hog in (1, 2, 3):
            with self.subTest(hog=hog):
                with self.assertRaisesRegex(SystemExit, "STOP: local --hog is refused") as refused:
                    self.main(hog, "0")
                # A refusal names the rule and the way out, not just "no".
                self.assertIn("cloud_verify.py", str(refused.exception))

    def test_a_refusal_starts_no_measurement(self):
        started = []
        with patch.dict(os.environ, {"TLX_CLOUD_HOST": "0"}, clear=False), \
             patch.object(sys, "argv", ["bench.py", "ab", "--models", "A", "--hog", "2"]), \
             patch.object(bench, "cmd_ab", side_effect=lambda a: started.append(a)):
            with self.assertRaises(SystemExit):
                bench.main()
        self.assertEqual(started, [])

    def test_the_cloud_host_keeps_its_measurement(self):
        self.assertEqual(len(self.main(4, "1")), 1)

    def test_zero_hogs_is_not_load_and_runs_locally(self):
        self.assertEqual(len(self.main(0, "0")), 1)


class BenchBudget(unittest.TestCase):
    def tearDown(self):
        budget.configure(argparse.Namespace())

    def test_ab_samples_forward_per_binary_arguments(self):
        args = SimpleNamespace(bin=['old=/old', 'new=/new'], env=[], bin_args=['new:-seed 7'],
                               models='A', args='-tlc -interp -workers 1', repeat=2, timeout=10,
                               stats=False, hog=0, interp=False, no_warmup=False)
        result = dict(result='success', distinct=3, generated=4, depth=2,
                      wall_s=1, cpu_s=1, maxrss_mib=1, compatibility=True)
        with patch.object(bench.os, 'access', return_value=True), \
             patch.object(bench_models, 'oracle', return_value={'A': {'id': 'A'}}), \
             patch.object(bench_models, 'bench_flags', return_value=[]), \
             patch.object(bench, 'tlx', return_value=result) as run, \
             patch.object(bench, '_ab_summary') as summary, contextlib.redirect_stdout(io.StringIO()):
            bench.cmd_ab(args)
        self.assertEqual(run.call_count, 6)  # two warmups plus two interleaved rounds
        for call in run.call_args_list:
            forwarded = call.args[1]
            self.assertEqual(forwarded[:4], ['-tlc', '-interp', '-workers', '1'])
            self.assertEqual(forwarded[4:], ['-seed', '7'] if call.kwargs['exe'] == '/new' else [])
        self.assertEqual([len(rows) for rows in summary.call_args.args[-1].values()], [2, 2])

    def _ab_args(self, **changes):
        base = dict(bin=['old=/old', 'new=/new'], env=[], bin_args=[], models='A',
                    args='-compile -workers 1', repeat=2, timeout=10, stats=False, hog=0,
                    interp=False, no_warmup=False)
        base.update(changes)
        return SimpleNamespace(**base)

    def _sample(self, **changes):
        return {**dict(result='success', distinct=3, generated=4, depth=2, wall_s=1, cpu_s=1,
                       maxrss_mib=1, compatibility=True, exit=0), **changes}

    def test_measured_costs_uses_recorded_history_for_this_mode_and_workers(self):
        # c-r09/c-d09: deadline admission must reserve what a named model really
        # cost here, in the mode and worker count this pass measures, not another
        # tool's estimate. TLC rows and unfinished runs are not history.
        def rec(model, mode, workers, result, wall, tool='tlx'):
            return {'tool': tool, 'model': model, 'mode': mode, 'workers': workers,
                    'counts': {'result': result}, 'metrics': {'wall_s': wall}}
        records = [rec('A', '-compile', 1, 'success', 3), rec('A', '-compile', 1, 'success', 5),
                   rec('A', '-compile', 8, 'success', 100), rec('A', '-interp', 1, 'success', 7),
                   rec('A', '-compile', 1, 'timeout', 999), rec('B', '-compile', 1, 'success', 20),
                   rec('A', '-compile', 1, 'success', 40, tool='tlc')]
        with patch.object(bench, 'load_records', return_value=records):
            self.assertEqual(bench.measured_costs(['A'], 1, '-compile'), {'A': 4})
            self.assertEqual(bench.measured_costs(['A', 'B'], 1, '-compile'), {'A': 4, 'B': 20})
            self.assertEqual(bench.measured_costs(['A'], 1, '-interp'), {'A': 7})
            self.assertEqual(bench.measured_costs(['A'], 8, '-compile'), {'A': 100})
            self.assertEqual(bench.measured_costs(['A'], 1, '-compile', root='/elsewhere'),
                             {'A': 4})
            self.assertEqual(bench.measured_costs([], 1, '-compile'), {})

    def test_warmup_failure_censors_timeouts_and_normal_verdicts_only(self):
        # bpa-abi: an exit-101 panic printed `unknown/None` and looked like a
        # missing performance sample; a crash or a non-timeout unknown must stop
        # the pass, while a censored timeout, a normal verdict and a missing exit
        # on a normal verdict must not.
        fail = bench._ab_warmup_failure
        self.assertIsNone(fail('M', 'new', {'result': 'timeout', 'wall_s': 5}))
        self.assertIsNone(fail('M', 'new', {'result': 'skipped', 'wall_s': 5}))
        self.assertIsNone(fail('M', 'new', {'result': 'success', 'exit': 0}))
        self.assertIsNone(fail('M', 'new', {'result': 'success'}))
        self.assertIsNone(fail('M', 'new', {'result': 'safety failure', 'exit': 12}))
        crash = fail('M', 'new', {'result': 'success', 'exit': 101,
                                  'raw': {'output': 'thread "main" panicked\n', 'exit': 101}})
        self.assertIn('success', crash)
        self.assertIn('101', crash)
        self.assertIn('panicked', crash)
        unknown = fail('M', 'new', {'result': 'unknown', 'exit': None, 'raw': {'output': 'garbage\n'}})
        self.assertIn('unknown', unknown)

    def test_ab_backend_declaration_must_select_it_for_every_binary(self):
        # c-m05: a declared backend that a binary's environment does not select
        # would time (and warm) another backend; the pass refuses to start.
        args = self._ab_args(env=['new:TLX_JIT=0'], backend='c')
        with patch.object(bench.os, 'access', return_value=True), contextlib.redirect_stdout(io.StringIO()):
            with self.assertRaises(SystemExit) as caught:
                bench.cmd_ab(args)
        self.assertIn('old', str(caught.exception))
        self.assertIn('TLX_JIT=0', str(caught.exception))

    def test_ab_bin_rev_must_name_a_binary_and_flows_into_the_summary(self):
        with patch.object(bench.os, 'access', return_value=True), contextlib.redirect_stdout(io.StringIO()):
            with self.assertRaises(SystemExit):
                bench.cmd_ab(self._ab_args(bin_rev=['ghost=deadbeef']))
        args = self._ab_args(bin_rev=['new=deadbeef'])
        summary = {'A#old': {'complete': True}, 'A#new': {'complete': True}}
        with patch.object(bench.os, 'access', return_value=True), \
             patch.object(bench_models, 'oracle', return_value={'A': {'id': 'A'}}), \
             patch.object(bench, 'load_records', return_value=[]), \
             patch.object(bench_models, 'bench_flags', return_value=[]), \
             patch.object(bench, 'tlx', return_value=self._sample()), \
             patch.object(bench, '_ab_summary', return_value=summary) as reported, \
             contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(bench.cmd_ab(args), 0)
        self.assertEqual(reported.call_args.kwargs['bin_revs'], {'new': 'deadbeef'})
        self.assertEqual(reported.call_args.kwargs['backend'], '')

    def test_ab_incomplete_pass_exits_nonzero_and_names_the_model(self):
        # c-r05/c-r09: a named model without a complete sample set (a skipped or
        # crashed round) is not a green pass.
        args = self._ab_args(models='A,B', no_warmup=True)
        summary = {'A#old': {'complete': True}, 'A#new': {'complete': True},
                   'B#old': {'complete': True}, 'B#new': {'complete': False}}
        with patch.object(bench.os, 'access', return_value=True), \
             patch.object(bench_models, 'oracle', return_value={'A': {'id': 'A'}, 'B': {'id': 'B'}}), \
             patch.object(bench, 'load_records', return_value=[]), \
             patch.object(bench_models, 'bench_flags', return_value=[]), \
             patch.object(bench, 'tlx', return_value=self._sample()), \
             patch.object(bench, '_ab_summary', return_value=summary), \
             contextlib.redirect_stdout(io.StringIO()) as output:
            self.assertEqual(bench.cmd_ab(args), 1)
        self.assertIn('ab incomplete: B', output.getvalue())

    def test_ab_summary_returns_the_mapping_that_carries_completeness(self):
        # c-r05: cmd_ab reads 'complete' out of this mapping to decide the pass
        # verdict, so the printed and the returned summary must be one object.
        # A helper that only printed it (returning None) turned that check into a
        # TypeError, and no owned test noticed - the regression lived here.
        args = self._ab_args()
        args.tlc_baseline = None
        args.out = None
        bins = [('old', '/old'), ('new', '/new')]
        sample = {**self._sample(), 'cpu': 1.0, 'wall': 1.0, 'rss': 1.0}
        res = {('A', 'old'): [sample, sample], ('A', 'new'): [sample, sample]}
        with patch.object(bench_machine, 'tla2tools_info', return_value={}), \
             patch.object(bench_baselines, 'find_baseline', return_value=None), \
             contextlib.redirect_stdout(io.StringIO()):
            returned = bench._ab_summary(args, bins, ['A'], {'A': {'id': 'A'}},
                                         ['-compile', '-workers', '1'], {}, res)
        self.assertEqual(sorted(returned), ['A#new', 'A#old'])
        self.assertTrue(returned['A#old']['complete'])
        self.assertTrue(returned['A#new']['complete'])

    def test_ab_warmup_crash_stops_the_pass(self):
        args = self._ab_args()
        with patch.object(bench.os, 'access', return_value=True), \
             patch.object(bench_models, 'oracle', return_value={'A': {'id': 'A'}}), \
             patch.object(bench, 'load_records', return_value=[]), \
             patch.object(bench_models, 'bench_flags', return_value=[]), \
             patch.object(bench, 'tlx', return_value=self._sample(result='unknown', exit=101,
                                                                  raw={'output': 'boom\n', 'exit': 101})), \
             contextlib.redirect_stdout(io.StringIO()) as output:
            with self.assertRaises(SystemExit) as caught:
                bench.cmd_ab(args)
        self.assertIn('ab aborted', str(caught.exception))
        self.assertIn('boom', output.getvalue() + str(caught.exception))

    def test_profile_auxiliary_check_reports_fallback_as_failure(self):
        note = 'compile: IR verification failed; interpreting model: bad operand'
        result = subprocess.CompletedProcess([], 0, note, '')
        with patch.object(bench_profile.subprocess, 'run', return_value=result), \
             contextlib.redirect_stdout(io.StringIO()) as output:
            code, _ = bench_profile.sh(['perf', 'c2c', 'record', '--', 'fake', 'check', 'A.tla'])
        self.assertNotEqual(code, 0)
        self.assertEqual(budget.current().failures[0]['model'], 'A.tla')
        self.assertIn('FAIL A.tla:', output.getvalue())

    def test_suite_checkpoints_completed_samples_and_skips_remaining(self):
        now = [0.0]
        entry = {'key': 'A#compile#1', 'model': 'A', 'mode': 'compile', 'workers': 1,
                 'size': 'small', 'timeout_s': 100, 'estimate_s': 1, 'expect': {'result': 'success'}}
        checkpoints = []
        def measure(*args, **kwargs):
            now[0] += 10
            return {'result': 'success', 'wall_s': 10, 'distinct': 1, 'cpu_s': 1}
        with patch.object(budget.time, 'monotonic', side_effect=lambda: now[0]), \
             patch.object(bench_suite, 'measure_once', side_effect=measure) as measured, \
             contextlib.redirect_stdout(io.StringIO()) as output:
            limited = budget.Budget(.5)
            records = bench_suite.measure_entry(bench, {}, entry, [('new', 'fake')], 3, False, lambda _: 1,
                                                budget=limited, checkpoint=lambda row, samples: checkpoints.append(row))
        self.assertEqual(measured.call_count, 2)  # warmup and round 1 survive
        self.assertEqual(records['new']['walls'], [10])
        self.assertEqual(records['new']['result'], 'skipped')
        self.assertEqual(records['new']['completed_samples'], 1)
        self.assertEqual(checkpoints[-1]['reason'], 'deadline')
        self.assertIn('sample A new round 1: 10.000s', output.getvalue())

    def test_suite_timeout_checkpoints_before_return_and_preserves_samples(self):
        entry = {'key': 'A#compile#1', 'model': 'A', 'mode': 'compile', 'workers': 1,
                 'size': 'small', 'timeout_s': 10, 'expect': {'result': 'success'}}
        rows = []
        def run(*args, **kwargs):
            if len(rows) == 2:
                raise subprocess.TimeoutExpired('fake', 10)
            return {'result': 'success', 'wall_s': 1, 'distinct': 1}
        with patch.object(bench_suite, 'measure_once', side_effect=run), contextlib.redirect_stdout(io.StringIO()):
            records = bench_suite.measure_entry(bench, {}, entry, [('new', 'fake')], 3, False, lambda _: 1,
                                                checkpoint=lambda row, _: rows.append(row))
        self.assertEqual([row['result'] for row in rows], ['success', 'success', 'timeout', 'skipped'])
        self.assertEqual(records['new']['walls'], [1, 10])
        self.assertEqual(records['new']['skipped'], 'sample timeout')
        self.assertEqual(records['new']['result'], 'skipped')

    def test_prelaunch_smoke_refuses_failed_command_before_cloud(self):
        with patch.object(bench_smoke.subprocess, 'run', return_value=SimpleNamespace(returncode=1, stdout='FAIL scratch', stderr='missing file')) as run, \
             self.assertRaisesRegex(ValueError, 'FAIL scratch'):
            bench_smoke.preflight(['ab --bin a=old --bin b=new --models A'], fresh=lambda: None)
        self.assertIn('--smoke', run.call_args.args[0])
        self.assertLessEqual(run.call_args.kwargs['timeout'], 60)

    def test_prelaunch_refreshes_the_binary_before_the_timed_smoke(self):
        # A rebuild inside the 60 s smoke timed out (2026-10-07): it runs first, untimed.
        order = []
        ok = SimpleNamespace(returncode=0, stdout='', stderr='')
        with patch.object(bench_smoke.subprocess, 'run', side_effect=lambda *a, **k: (order.append('smoke'), ok)[1]):
            bench_smoke.preflight(['ab --bin a=old --bin b=new --models A'], fresh=lambda: order.append('fresh'))
        self.assertEqual(order, ['fresh', 'smoke'])

    def test_launcher_refuses_smoke_failure_before_creating_provider(self):
        args = cloud_verify.parse_args(['--provider', 'tencent', '--bench', 'run --models A'])
        with tempfile.TemporaryDirectory() as directory, \
             patch.object(cloud_verify, 'LaunchLedger', return_value=cloud_verify.LaunchLedger(directory + '/ledger.json')), \
             patch.object(cloud_verify, 'current_owner', return_value='worker'), \
             patch.object(cloud_verify, 'make_provider') as provider, \
             patch.object(cloud_verify, 'release_preflight', return_value=(True, 'prelaunch build ok')), \
             patch.object(bench_smoke, 'preflight', side_effect=subprocess.TimeoutExpired('smoke', 60)), \
             patch.object(cloud_verify, 'log'), self.assertRaises(cloud_common.CloudStop) as raised:
            cloud_verify.run(args)
        self.assertEqual(raised.exception.code, 23)
        self.assertIn('prelaunch bench smoke refused', str(raised.exception))
        provider.assert_not_called()

    def test_previous_pass_estimate_and_remaining_timeout(self):
        now = [0.0]
        with patch.object(budget.time, 'monotonic', side_effect=lambda: now[0]):
            b = budget.Budget(1)
            self.assertIsNone(b.admit('model', 100, estimate=100))
            self.assertEqual(b.skipped[0]['model'], 'model')
            timeout = b.admit('small', 100, estimate=2)
            self.assertLess(timeout, 60)
            b.observe('small', 2)
            now[0] = 58
            self.assertIsNone(b.admit('small', 100))

    def test_estimate_cannot_exceed_the_enforced_sample_timeout(self):
        with patch.object(budget.time, 'monotonic', return_value=0):
            b = budget.Budget(15)
            self.assertEqual(b.admit('profile', 240, estimate=1164), 240)
            b.observe('profile', 900)
            self.assertEqual(b.admit('profile', 240), 240)
            self.assertIsNone(b.admit('unbounded', 1200, estimate=1164))

    def test_expired_budget_starts_no_child_in_every_driver(self):
        # HARNESS-08/-21: an inventory of every measured entry point and the
        # helpers that start its children. After the deadline each of them
        # refuses admission and starts nothing; the same entry points are
        # exercised with time left by their own tests.
        budget.configure(argparse.Namespace(deadline_at=1))
        with tempfile.TemporaryDirectory() as tmp:
            for label, targets, call, check in self._inventory(tmp):
                with self.subTest(driver=label):
                    before = len(budget.current().skipped)
                    result = self._no_child(targets, call)
                    check(result)
                    self.assertGreater(len(budget.current().skipped), before,
                                       f'{label} started no child but recorded no deadline skip')

    @staticmethod
    def _no_child(targets, call):
        """Run `call` with every child-spawning helper in `targets` faked;
        return its result and assert that none of them was called."""
        mocks = []
        with contextlib.ExitStack() as stack:
            for module, attr in targets:
                mocks.append(stack.enter_context(patch.object(module, attr, create=True)))
            result = call()
        for (module, attr), fake in zip(targets, mocks):
            assert not fake.called, f'{module.__name__}.{attr} started a child after the deadline'
        return result

    def _inventory(self, tmp):
        """(label, spawn helpers, call, check) for every measured entry point.

        `call` runs the entry with the active budget; `check` asserts the skip
        it must report. Each spawn helper is where the entry starts a child
        (or an expensive build): `bench_ttfr` and `bench_suite`'s TLC passes
        delegate to `bench.tlx`/`bench._collect_tlc_measured` and are covered
        through them."""
        exe = os.path.join(tmp, 'tlx')
        Path(exe).write_text('#!/bin/sh\n')
        os.chmod(exe, 0o755)
        model = {'id': 'A', 'tla': 'A.tla', 'cfg': 'A.cfg'}
        skipped = lambda r: (self.assertEqual(r['result'], 'skipped'), self.assertEqual(r['reason'], 'deadline'))  # noqa: E731

        def perf(**over):
            a = SimpleNamespace(bin=[f'new={exe}'], models='A', args='', seconds=1, freq=99,
                                timeout=1, tlc=False, out=tmp)
            for key, value in over.items():
                setattr(a, key, value)
            with patch.object(bench_models, 'oracle', return_value={'A': model}), \
                 patch.object(bench_machine, 'machine_desc', return_value='test'), \
                 patch.object(bench_profile, 'ensure_perf', return_value='/usr/bin/perf'):
                return bench.cmd_perf(a)

        def suite():
            entry = {'key': 'A#compile#1', 'model': 'A', 'mode': 'compile', 'workers': 1,
                     'size': 'small', 'timeout_s': 10, 'estimate_s': 1, 'expect': {'result': 'success'}}
            rows = []
            records = bench_suite.measure_entry(bench, {}, entry, [('new', 'fake')], 3, False, lambda _: 1,
                                                checkpoint=lambda row, _samples: rows.append(row))
            assert rows and all(r['reason'] == 'deadline' for r in rows), rows
            return records['new']

        def liveness_run():
            return bench_liveness.run(SimpleNamespace(before='rev0', before_bin=exe, after_bin=exe, sizes='4,8',
                                                      repeat=1, timeout=60, out=os.path.join(tmp, 'liveness.json')))

        return [
            ('bench.tlx', [(bench, 'run_proc'), (bench, 'tlx_cmd')], lambda: bench.tlx(model, [], 120), skipped),
            ('bench._collect_tlc', [(bench, 'run_proc'), (tlc, 'tlc_cmd')], lambda: bench._collect_tlc(model, 1, 120), skipped),
            ('bench._collect_tlc_measured', [(bench, 'run_proc'), (tlc, 'tlc_cmd')],
             lambda: bench._collect_tlc_measured(model, 1, 120), skipped),
            ('bench.cmd_perf', [(bench, 'run_proc'), (bench.subprocess, 'run'), (bench, 'tlx_cmd'), (tlc, 'tlc_cmd')],
             perf, self.assertIsNone),
            ('bench.cmd_perf --tlc', [(bench, 'run_proc'), (bench.subprocess, 'run'), (bench, 'tlx_cmd'), (tlc, 'tlc_cmd')],
             lambda: perf(tlc=True), self.assertIsNone),
            ('benchmarking.bench_disk.run_tlx', [(bench_disk, 'run_sampled')], lambda: bench_disk.run_tlx(model, exe, [], 120, {}), skipped),
            ('benchmarking.bench_disk._collect_tlc', [(bench_disk, 'run_sampled'), (tlc, 'tlc_cmd')],
             lambda: bench_disk._collect_tlc(model, 1, 120, 512, 64), skipped),
            ('benchmarking.bench_profile.run_one', [(bench_profile, 'run_proc'), (bench, 'tlx_cmd')],
             lambda: bench_profile.run_one(model, [], 120, exe), skipped),
            ('benchmarking.bench_suite.measure_entry', [(bench_suite, 'measure_once')], suite,
             lambda r: self.assertEqual(r['result'], 'skipped')),
            ('benchmarking.bench_liveness.probe', [(bench_liveness.subprocess, 'run')],
             lambda: bench_liveness.probe(Path(tmp), 'rev0', 'before'), self.assertIsNone),
            ('benchmarking.bench_liveness.run', [(bench_liveness, 'run_proc'), (bench_liveness.subprocess, 'run'),
                                    (bench_liveness.subprocess, 'check_output')], liveness_run, self.assertIsNone),
        ]

    def test_admission_boundaries_before_at_and_after_the_cutoff(self):
        # HARNESS-08: `remaining` reserves two seconds for the handover; the
        # cutoff is the instant it reaches zero. A fake clock pins all three.
        now = [0.0]
        with patch.object(budget.time, 'monotonic', side_effect=lambda: now[0]):
            b = budget.Budget(1)  # until = 60 s
            self.assertEqual(b.admit('m', 100, estimate=1), 58.0)   # before: the whole remainder
            now[0] = 57.0                                            # remaining = 1: the estimate fits
            self.assertEqual(b.admit('m', 100, estimate=1), 1.0)
            now[0] = 58.0                                            # at the cutoff: remaining = 0
            self.assertIsNone(b.admit('m', 100, estimate=1))
            now[0] = 90.0                                            # after it
            self.assertIsNone(b.admit('m', 100, estimate=1))
            b.observe('m', 100.0)                                    # a 100 s pass raises the estimate
            self.assertEqual(b.estimates['m'], 151.0)
            now[0] = 57.0                                            # the raised estimate refuses what fitted before
            self.assertIsNone(b.admit('m', 100))
        self.assertEqual([row['reason'] for row in b.skipped], ['deadline'] * 3)
        self.assertEqual([row['remaining_s'] for row in b.skipped], [0.0, 0.0, 1.0])

    def test_a_key_with_no_known_cost_reserves_only_what_is_left(self):
        # 2026-10-10: a key with neither a measurement nor an estimate reserved
        # its whole --timeout, so a --deadline-min shorter than one timeout
        # skipped every key of the pass (the TLC baseline lanes reported nothing
        # but deadline skips for a budget their keys could each have fitted in
        # seconds). A hard timeout is an upper bound, not an expected cost.
        now = [0.0]
        with patch.object(budget.time, 'monotonic', side_effect=lambda: now[0]):
            b = budget.Budget(30)                                   # 1800 s
            self.assertEqual(b.admit('fresh', 3600), 1798.0)        # the whole budget, not the timeout
            self.assertEqual(b.skipped, [])
            b.observe('fresh', 1800.0)                              # 1800 s measured -> reserves 2701 s
            self.assertIsNone(b.admit('fresh', 3600))               # a known cost that does not fit still skips
            self.assertEqual(b.skipped[-1]['reason'], 'deadline')
            now[0] = 1799.0                                         # remaining = 0
            self.assertIsNone(b.admit('another', 60))               # no key starts with no budget left

    def test_liveness_probe_build_is_admitted_too(self):
        # HARNESS-08: the probe build is expensive setup; the deadline reserves
        # its estimate, so with no time left rustc is never started.
        now = [0.0]
        with patch.object(budget.time, 'monotonic', side_effect=lambda: now[0]):
            budget.configure(argparse.Namespace(deadline_min=5))
            with tempfile.TemporaryDirectory() as tmp, \
                 patch.object(bench_liveness.subprocess, 'run') as run, \
                 patch.object(bench_liveness.subprocess, 'check_output', return_value=''), \
                 patch.object(bench_liveness.Path, 'glob', side_effect=lambda pattern: [mock.Mock()]):
                run.return_value = mock.Mock(returncode=0)
                probe = bench_liveness.probe(Path(tmp), 'rev0', 'before')
                self.assertIsNotNone(probe)
                self.assertEqual(run.call_count, 1)
                self.assertEqual(budget.current().skipped, [])
                now[0] = 299.0  # the cutoff: remaining = 0
                self.assertIsNone(bench_liveness.probe(Path(tmp), 'rev0', 'before'))
                self.assertEqual(run.call_count, 1)  # no second rustc
        self.assertEqual([row['model'] for row in budget.current().skipped], ['liveness:probe:before'])

    def test_liveness_keeps_the_runs_measured_before_the_deadline(self):
        # HARNESS-08/-21: a deadline that cuts the tail of the scaling matrix
        # keeps what was measured before it and marks the rest incomplete.
        now = [0.0]
        calls = []
        out = Path(tempfile.mkdtemp()) / 'liveness.json'

        def measure(cmd, timeout, address_mib):
            calls.append(timeout)
            now[0] += 100.0
            return (mock.Mock(returncode=0, stdout='{"states": 1}'),
                    {'wall_s': 100.0, 'cpu_s': 50.0, 'rss_mib': 1.0, 'exit': 0, 'output': ''})

        args = SimpleNamespace(before='rev0', before_bin='/fake/before', after_bin='/fake/after',
                               sizes='4,8', repeat=1, timeout=60, out=str(out))
        with patch.object(budget.time, 'monotonic', side_effect=lambda: now[0]):
            budget.configure(argparse.Namespace(deadline_min=5))
            with patch.object(bench_liveness, 'probe', side_effect=lambda d, rev, name: Path(f'/fake/{name}')), \
                 patch.object(bench_liveness, 'measure', side_effect=measure), \
                 patch.object(bench_liveness, 'parse', return_value={'result': 'liveness failure', 'distinct': 4}), \
                 patch.object(bench_liveness.subprocess, 'check_output', return_value='rev-after'), \
                 patch.object(bench_records, 'ingest'), contextlib.redirect_stdout(io.StringIO()):
                with self.assertRaises(SystemExit) as raised:
                    bench_liveness.run(args)
        self.assertIn('pass(es) skipped at the deadline', str(raised.exception))
        self.assertEqual(len(calls), 3)  # three passes fit; the rest are skipped
        data = json.loads(out.read_text())
        self.assertEqual(len(data['runs']), 8)
        kept = [r for r in data['runs'] if r.get('result') != 'skipped']
        skipped = [r for r in data['runs'] if r.get('result') == 'skipped']
        self.assertEqual([r['wall_s'] for r in kept], [100.0, 100.0, 100.0])
        self.assertEqual(len(skipped), 5)
        self.assertTrue(all(r['reason'] == 'deadline' and r['complete'] is False for r in skipped))
        self.assertEqual(len(data['budget']['skipped']), 5)

    def test_an_admitted_pass_measures_its_real_child(self):
        # MEASURE/HARNESS-21: a pass admitted with time left runs a real child
        # whose wall, CPU and exit code are recorded. The deadline never
        # shortens a run by swallowing it: a timeout and an early error keep
        # the child's own end (its bound and its exit code), so a killed run
        # cannot pass as a fast one.
        with patch.object(budget.time, 'monotonic', return_value=0.0):
            b = budget.Budget(5)  # 300 s left
            self.assertEqual(b.admit('liveness:model:4', 60, estimate=10), 60)  # the full timeout, not the 298 s remainder
        _, row = bench_liveness.measure([sys.executable, '-c', 'x = sum(range(3000000))'], 30, 2048)
        self.assertEqual(row['exit'], 0)
        self.assertGreater(row['wall_s'], 0)
        self.assertGreater(row['cpu_s'], 0.0)       # real CPU, not zero attribution
        _, timed_out = bench_liveness.measure([sys.executable, '-c', 'import time; time.sleep(30)'], 1, 2048)
        self.assertNotEqual(timed_out['exit'], 0)   # killed at the bound
        self.assertGreaterEqual(timed_out['wall_s'], 0.9)
        _, failed = bench_liveness.measure([sys.executable, '-c', 'raise SystemExit(3)'], 30, 2048)
        self.assertEqual(failed['exit'], 3)         # the child's own exit is what is recorded

    def test_bench_run_keeps_every_sample_mismatch(self):
        # HARNESS-07: the last sample's problem is reported as before, and an
        # earlier deviating sample is named instead of being erased by it.
        ref = {'result': 'success', 'distinct': 5}
        ok = {'result': 'success', 'distinct': 5, 'compatibility': True}
        dead = {'result': 'deadlock', 'distinct': 3, 'compatibility': True}
        self.assertEqual(bench.run_problems([ok, ok, ok], ref, mode='compile', workers=1), [])
        self.assertEqual(bench.run_problems([ok, dead, ok], ref, mode='compile', workers=1),
                         ['sample 2: result or distinct differs from TLC'])
        self.assertEqual(bench.run_problems([{**ok, 'distinct': 6}, ok, ok], ref, mode='compile', workers=1),
                         ['sample 1: result or distinct differs from TLC'])
        self.assertEqual(bench.run_problems([ok, ok, dead], ref, mode='compile', workers=1),
                         ['result or distinct differs from TLC'])
        # Every sample failing the same way is still one aggregate problem.
        self.assertEqual(bench.run_problems([dead, dead], ref, mode='compile', workers=1),
                         ['result or distinct differs from TLC'])
        # A reduced default-mode sample is the positive case, not a problem.
        reduced = {'result': 'success', 'distinct': 2, 'compatibility': False}
        self.assertEqual(bench.run_problems([{**reduced, 'distinct': 1}, reduced], ref, mode='default', workers=1), [])

    def test_scaling_repeats_that_disagree_are_not_a_reduction(self):
        ref = {'1': {'result': 'success', 'distinct': 5}}
        good = {'result': 'success', 'distinct': 5, 'wall_s': 1, 'cpu_s': 1, 'maxrss_mib': 10}
        dead = {**good, 'result': 'deadlock', 'distinct': 3}
        rec = bench.scale_runs([good, dead, good])
        self.assertEqual(rec['result'], 'success')  # The aggregate is still the last run's.
        self.assertEqual(rec['walls'], [1, 1, 1])
        self.assertEqual([s['result'] for s in rec['samples']], ['success', 'deadlock', 'success'])
        self.assertEqual(rec['problems'], ["sample 2: result 'deadlock', expected 'success'"])
        self.assertEqual(bench.scale_counts({'tlx': {'1': rec}, 'tlc': ref}), '✗')
        # An unfinished repeat neither counts nor fails (the existing gate).
        rec = bench.scale_runs([{**good, 'result': 'timeout', 'distinct': None}, good])
        self.assertNotIn('problems', rec)
        self.assertEqual(bench.scale_counts({'tlx': {'1': rec}, 'tlc': ref}), '✓')
        # A budget skip has no counts either, so it is not the reference the
        # earlier repeats are held to (and not a disagreement).
        rec = bench.scale_runs([good, {**good, 'result': 'skipped', 'distinct': None}])
        self.assertNotIn('problems', rec)
        # A repeat that ended in a checker error is a disagreement, and an error
        # is never the reference of the others.
        rec = bench.scale_runs([good, {**good, 'result': 'error', 'distinct': None}])
        self.assertEqual(rec['problems'], ["sample 2: result 'error', expected 'success'"])
        # Repeats that all fail the same way stay one aggregate failure.
        rec = bench.scale_runs([dead, dead])
        self.assertNotIn('problems', rec)
        self.assertEqual(bench.scale_counts({'tlx': {'1': rec}, 'tlc': ref}), '✗')
        # No finished run at all: nothing to compare, nothing to report.
        rec = bench.scale_runs([{**good, 'result': 'timeout', 'distinct': None}] * 2)
        self.assertNotIn('problems', rec)

    def test_default_reduced_counts_are_not_a_benchmark_failure(self):
        from benchmarking import bench_ttfr
        ref = {'result': 'success', 'distinct': 100}
        reduced = {'result': 'success', 'distinct': 10, 'compatibility': False}
        self.assertTrue(bench.counts_check(reduced, ref))
        self.assertTrue(bench_ttfr.same(reduced, ref, {}))
        self.assertFalse(bench.counts_check({**reduced, 'compatibility': True}, ref))
        self.assertFalse(bench_ttfr.same({**reduced, 'compatibility': True}, ref, {}))
        self.assertFalse(bench.counts_check({**reduced, 'result': 'deadlock'}, ref))
        entry = {'model': 'A', 'size': 'small', 'mode': 'compile', 'workers': 1, 'expect': ref}
        self.assertEqual(bench_suite.record_of(entry, [{**reduced, 'wall_s': 1}], [])['count_problems'], [])
        self.assertEqual(bench.scale_counts({'tlx': {'1': reduced}, 'tlc': {'1': ref}}), '-')
        runs = {'A': {'tier': 'small', 'mode': 'default', 'result': 'success', 'walls': [1, 1, 1], 'distinct': 100}}
        changed = {'A': {**runs['A'], 'distinct': 10}}
        self.assertEqual(bench.compare_runs(runs, changed)['regress'], [])
        changed['A']['result'] = 'deadlock'
        self.assertEqual(bench.compare_runs(runs, changed)['regress'], ['A'])

    def test_scale_runs_aggregate_keeps_the_mode_contract(self):
        # HARNESS-19/-21: the aggregate over repeated runs must carry the last
        # run's compatibility and tier, or a reduced default-mode state count
        # is later read as a TLC-agreeing one (`scale_counts` '-' vs '✓').
        run = dict(result='success', distinct=10, generated=11, depth=3, wall_s=1.0, cpu_s=1.0,
                   maxrss_mib=1.0, compatibility=False, tier='small')
        rec = bench.scale_runs([run, {**run, 'wall_s': 2.0}])
        self.assertIs(rec['compatibility'], False)
        self.assertEqual(rec['tier'], 'small')
        self.assertEqual(rec['walls'], [1.0, 2.0])
        self.assertEqual(rec['result'], 'success')
        self.assertEqual(bench.scale_counts({'tlx': {'1': rec}, 'tlc': {'1': {'result': 'success', 'distinct': 100}}}), '-')
        compatible = bench.scale_runs([{**run, 'compatibility': True}])
        self.assertEqual(bench.scale_counts({'tlx': {'1': compatible}, 'tlc': {'1': {'result': 'success', 'distinct': 10}}}), '✓')

    def test_ttfr_short_round_trips_the_mode_contract(self):
        # HARNESS-19: `short` feeds the persisted record that a later comparison
        # reads through `same`; dropping `compatibility` there turned a
        # default-mode reduction into a phantom TLC mismatch.
        reduced = {'result': 'success', 'distinct': 10, 'wall_s': 1.0, 'compatibility': False}
        self.assertIs(bench_ttfr.short(reduced)['compatibility'], False)
        ref = {'result': 'success', 'distinct': 100}
        self.assertTrue(bench_ttfr.same(bench_ttfr.short(reduced), ref, {}))
        self.assertFalse(bench_ttfr.same(bench_ttfr.short({**reduced, 'compatibility': True}), ref, {}))

    def test_cloud_passes_share_one_absolute_deadline(self):
        script = cloud_common.bench_script('/home/test', 'clang', 'fake', [],
                                          ['run --models A', 'disk --models B'], deadline_at=900)
        self.assertEqual(script.count('--deadline-at 900'), 2)
        self.assertIn('python3 -u', script)

    def test_ir_fallback_is_a_failure_even_with_successful_counts(self):
        for note in ('compile: IR verification failed; interpreting model: bad operand',
                     'compile: no JIT and no C compiler: checking with the interpreter'):
            parsed = tlc.parse(note + '\nModel checking completed. No error has been found.\n', 1, 0)
            self.assertEqual(parsed['result'], 'compile failure')
            self.assertIn(note, parsed['error'])
        # Region-level fallbacks are expected, and must remain usable.
        parsed = tlc.parse('compile: layout miss checking temporal properties; checking them with the interpreter\n'
                           'Model checking completed. No error has been found.\n', 1, 0)
        self.assertEqual(parsed['result'], 'success')

    def test_parse_slice_and_balance_slices_share_lpt_partitioning(self):
        self.assertEqual(budget.parse_slice('1/1'), (1, 1))
        self.assertEqual(budget.parse_slice('2/4'), (2, 4))
        self.assertEqual(budget.parse_slice('4/4'), (4, 4))
        for bad in ('', '1', '1/2/3', '0/2', '3/2', '-1/2', 'a/2', '1/0'):
            with self.subTest(spec=bad), self.assertRaisesRegex(ValueError, '--slice expects I/N'):
                budget.parse_slice(bad)
        costs = {'big': 100.0, 'mid1': 60.0, 'mid2': 50.0, 'small1': 10.0, 'small2': 5.0}
        slices = budget.balance_slices(costs, 2, costs.__getitem__)
        self.assertEqual(slices, [['big', 'small1', 'small2'], ['mid1', 'mid2']])
        self.assertEqual(budget.balance_slices([], 3, lambda _: 1.0), [[], [], []])
        with self.assertRaises(ValueError):
            budget.balance_slices(['a'], 0, lambda _: 1.0)
        with self.assertRaises(ValueError):
            budget.balance_slices(['a'], 2, lambda _: -1.0)
        with self.assertRaises(ValueError):
            budget.balance_slices(['a'], 2, lambda _: float('nan'))
        # tlcbase_slices delegates directly to balance_slices.
        ms = {'M1': {'tlc': {'wall_s': 100}}, 'M2': {'tlc': {'wall_s': 60}}, 'M3': {'tlc': {'wall_s': 50}}}
        self.assertEqual(bench.tlcbase_slices(ms, 2, 1800, [1]), [['M1'], ['M2', 'M3']])


if __name__ == '__main__':
    unittest.main()
