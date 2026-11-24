"""Benchmark cancellation owns only the process group it launched."""
import contextlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

import bench
from harness import process


class BenchmarkProcessGroups(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.pids = Path(self.tmp.name) / 'pids.json'
        # A checker, its compiler child, and the compiler's child. The leaf
        # announces readiness only after all three exist, then holds stdout.
        leaf = ("import json,os,sys,time; "
                "print('ready',flush=True); "
                "tmp=sys.argv[1]+'.tmp'; "
                "f=open(tmp,'w'); json.dump([int(sys.argv[2]),os.getppid(),os.getpid(),os.getpgrp()],f); "
                "f.close(); os.replace(tmp,sys.argv[1]); time.sleep(10)")
        compiler = ("import subprocess,sys; "
                    f"subprocess.run([sys.executable,'-c',{leaf!r},*sys.argv[1:]])")
        checker = ("import os,subprocess,sys,time; "
                   f"p=subprocess.Popen([sys.executable,'-c',{compiler!r},sys.argv[1],str(os.getpid())]); "
                   "time.sleep(10)")
        self.cmd = [sys.executable, '-c', checker, str(self.pids)]
        self.addCleanup(self.clean_fixture)

    def clean_fixture(self):
        if self.pids.exists():
            # These identities come only from this fixture's creation receipt.
            # The captured leader is a separate session, never our own group.
            group = json.loads(self.pids.read_text())[-1]
            if group != os.getpgrp():
                with contextlib.suppress(ProcessLookupError):
                    os.killpg(group, signal.SIGKILL)

    def assert_stopped(self):
        self.assertTrue(self.pids.exists(), 'fixture never reached the grandchild')
        pids = json.loads(self.pids.read_text())
        self.assertEqual(pids[0], pids[3])
        self.assertNotEqual(pids[3], os.getpgrp())
        deadline = time.monotonic() + 2
        while True:
            active = []
            for pid in pids[:3]:
                state = subprocess.run(['ps', '-o', 'stat=', '-p', str(pid)],
                                       capture_output=True, text=True).stdout.strip()
                # An orphan zombie is already dead; the OS's adopter reaps it.
                if state and not state.startswith('Z'):
                    active.append((pid, state))
            if not active or time.monotonic() >= deadline:
                break
            time.sleep(.01)
        self.assertEqual(active, [])

    def test_benchmark_timeout_cleans_compiler_and_grandchild(self):
        # An unrelated child in the caller's process group must survive.
        with subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(10)']) as foreign:
            try:
                with patch.object(bench, 'tlx_cmd', return_value=self.cmd):
                    result = bench.tlx({'id': 'fixture'}, [], .5, exe=sys.executable, raw=True)
                self.assertEqual(result['result'], 'timeout')
                self.assertEqual(result['raw']['exit'], -signal.SIGKILL)
                self.assertIn('ready', result['raw']['output'])
                self.assert_stopped()
                self.assertIsNone(foreign.poll())
            finally:
                foreign.kill()
                foreign.wait()

    def test_pipe_timeout_and_stream_cancellation_clean_descendants(self):
        for options in ({}, {'grace': .1}, {'on_line': lambda line: None,
                                             'stop_when': self.pids.exists}):
            with self.subTest(options=options):
                self.pids.unlink(missing_ok=True)
                result = process.capture(self.cmd, .5, start_new_session=True,
                                         raise_timeout=False, **options)
                self.assertIn('ready', result.stdout)
                self.assert_stopped()

    def test_wait_interruption_cleans_owned_group(self):
        def interrupt(child, timeout):
            deadline = time.monotonic() + 2
            while not self.pids.exists() and time.monotonic() < deadline:
                time.sleep(.01)
            raise KeyboardInterrupt('fixture cancellation')
        with patch.object(process.OwnedChild, 'wait_usage', interrupt), \
             patch.object(process.os, 'killpg', wraps=os.killpg) as kill_group:
            with self.assertRaises(KeyboardInterrupt):
                process.capture(self.cmd, 3, rusage=True, start_new_session=True)
            # Cancellation signals the owned group once, then reaps the child.
            # A second signal races with the first one's process teardown.
            kill_group.assert_called_once_with(json.loads(self.pids.read_text())[-1], signal.SIGKILL)
        self.assert_stopped()

    def test_group_is_cleaned_after_leader_has_already_exited(self):
        cmd = list(self.cmd)
        cmd[2] = cmd[2].removesuffix('time.sleep(10)') + (
            "\nwhile not os.path.exists(sys.argv[1]): time.sleep(.01)\n")
        for options in ({}, {'rusage': True}):
            with self.subTest(options=options):
                self.pids.unlink(missing_ok=True)
                result = process.capture(cmd, 3, start_new_session=True,
                                         raise_timeout=False, **options)
                self.assertEqual(result.returncode, 0)
                self.assert_stopped()

    def test_fixture_detects_direct_child_only_cleanup(self):
        control = type(self)('test_benchmark_timeout_cleans_compiler_and_grandchild')
        result = unittest.TestResult()
        # Reproduce the old ownership mistake; the fixture's independent
        # teardown still kills its own group after detecting live descendants.
        with patch.object(process.OwnedChild, 'signal_group',
                          lambda child, sig: os.kill(child.pid, sig)):
            control.run(result)
        self.assertEqual(len(result.failures), 1)
        self.assertEqual(result.errors, [])
        self.assertIn('self.assertEqual(active, [])', result.failures[0][1])

    def test_success_and_nonzero_exit_keep_output_and_usage(self):
        for status in (0, 7):
            with self.subTest(status=status):
                result = process.capture([sys.executable, '-c',
                                          f"print('complete'); raise SystemExit({status})"],
                                         3, rusage=True, start_new_session=True)
                self.assertEqual((result.returncode, result.stdout, result.timed_out),
                                 (status, 'complete\n', False))
                self.assertIsNotNone(result.rusage)


if __name__ == '__main__':
    unittest.main()
