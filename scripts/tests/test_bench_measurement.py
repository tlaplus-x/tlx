"""A measured run owns its child: the deadline, this child's own accounting and
every observation that failed (HARNESS-09, HARNESS-08); staging a spec that
writes files and every measured child's command, directory, environment and
usage come from one shared adapter (`benchmarking.measurement`, CODE-23).

Each fixture runs a real child process, never a mocked Popen, so the wait4
usage, the kill and the reap under test are the ones the benchmark uses (and
every fake child records its complete ordered argv, HARNESS-22). A
model-checking pass is replaced at the seam where its command enters
(`tlc.tlc_cmd`), which keeps the fixtures fast and JVM-free.
"""

import argparse
import json
import os
import signal
import subprocess
import sys
import tempfile
import threading
import unittest
from types import SimpleNamespace
from unittest.mock import patch

import bench
from benchmarking import bench_budget
from benchmarking import bench_disk
from benchmarking import bench_profile
from benchmarking import models
from benchmarking.commands import tlcbase
import testkit
import tlc
import tlxlib
from benchmarking import machine, measurement
from benchmarking.records import normalize
from harness.process import ProcResult
from tlc import parse

# A measured child: it records its whole argv, runs the mode of argv[1] for
# argv[2] (CPU seconds for "burn", wall seconds for "sleep"), reports a
# completed model check and exits with argv[3]. With BENCH_CONTEXT it also
# records how it was launched (its own cwd and environment, and the files it
# can see), which is what a staged run has to hand over.
CHILD_SOURCE = '''#!/usr/bin/env python3
import json, os, resource, sys, time

with open(os.environ["BENCH_ARGV"], "w") as out:
    json.dump(sys.argv, out)
if os.environ.get("BENCH_CONTEXT"):
    with open(os.environ["BENCH_CONTEXT"], "w") as out:
        json.dump({"argv": sys.argv, "cwd": os.getcwd(), "env": dict(os.environ),
                   "files": sorted(os.listdir("."))}, out)
mode, amount = sys.argv[1], float(sys.argv[2])
if mode == "burn":
    # (The clock wait4 reports, so the expected CPU is exact. The success
    # marker comes first: a reader that fails on the next line still leaves a
    # result the run would otherwise report as complete.)
    def used():
        r = resource.getrusage(resource.RUSAGE_SELF)
        return r.ru_utime + r.ru_stime
    end = used() + amount
    print("Model checking completed. No error has been found.", flush=True)
    while used() < end:
        pass
else:
    print("Model checking completed. No error has been found.", flush=True)
    time.sleep(amount)
print("Progress(0) at 1: %d states generated, %d distinct states found" % (int(amount * 10), int(amount * 10)), flush=True)
sys.exit(int(sys.argv[3]))
'''

RUSAGE = SimpleNamespace(ru_utime=0.5, ru_stime=0.1, ru_maxrss=1024, ru_nvcsw=1, ru_nivcsw=1)


def child(tmp, name="child"):
    """A real measured child (see CHILD_SOURCE) in `tmp`."""
    path = os.path.join(tmp, name)
    with open(path, "w") as stream:
        stream.write(CHILD_SOURCE)
    os.chmod(path, 0o755)
    return path


def recorded(path):
    with open(path) as stream:
        return json.load(stream)


def alive(pid):
    """False once this pid is reaped (a zombie still answers signal 0)."""
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    return True


def open_files():
    return len(os.listdir("/proc/self/fd" if sys.platform == "linux" else "/dev/fd"))


class FakeCgroup:
    """A control group without sudo: it holds the pid its member wrote, and
    `wrap` passes the command through unchanged (as the real one does after
    sudo, setpriv and env)."""

    def __init__(self, path, mib=64):
        self.path, self.mib = path, mib

    def wrap(self, cmd, env):
        return list(cmd)


class CacheEnvironmentTest(unittest.TestCase):
    def test_isolation_lifetime_and_inherited_environment(self):
        with patch.dict(os.environ, {'TLX_CACHE': '/inherited'}):
            with measurement.cache_environment() as (env, provenance):
                self.assertEqual(env, {})
                self.assertEqual(provenance['mode'], 'inherited')
                self.assertEqual(provenance['initial_state'], 'unknown')
            paths = []
            for _ in range(2):
                with measurement.cache_environment(True, warmup=True) as (env, provenance):
                    path = env['TLX_CACHE']
                    paths.append(path)
                    self.assertTrue(os.path.isdir(path))
                    self.assertFalse([name for name in os.listdir(path) if name != ".tlx-temp-owner.json"])
                    self.assertEqual(env['TLX_NATIVE_SYNC'], '1')
                    self.assertEqual(provenance, dict(mode='fresh-per-model', initial_state='empty', warmup=True))
                self.assertFalse(os.path.exists(path))
            self.assertNotEqual(*paths)
            self.assertEqual(os.environ['TLX_CACHE'], '/inherited')

    def test_isolated_cache_removed_after_failure(self):
        with self.assertRaises(RuntimeError):
            with measurement.cache_environment(True) as (env, _):
                path = env['TLX_CACHE']
                raise RuntimeError('failed sample')
        self.assertFalse(os.path.exists(path))


class MeasuredChild(unittest.TestCase):
    """The sampled child, its sampler and its reader belong to one call."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="tlx-measure-")
        self.addCleanup(self.tmp.cleanup)
        self.argv = os.path.join(self.tmp.name, "argv.json")
        self.exe = child(self.tmp.name)
        self.model = {"id": "A", "tla": os.path.join(self.tmp.name, "A.tla"), "cfg": os.path.join(self.tmp.name, "A.cfg")}

    def run_sampled(self, *args, **kwargs):
        kwargs.setdefault("env", {**os.environ, "BENCH_ARGV": self.argv})
        return bench_disk.run_sampled([self.exe, *args], **kwargs)

    def test_a_child_that_ends_by_itself_is_neither_killed_nor_called_a_timeout(self):
        # (The known positive first: this child's own CPU is accounted to it.)
        run = self.run_sampled("burn", "0.4", "0", timeout=30)
        self.assertFalse(run.timed_out)
        self.assertEqual((run.returncode, run.problems), (0, []))
        self.assertGreater(run.rusage.ru_utime + run.rusage.ru_stime, 0.3)
        self.assertEqual(recorded(self.argv), [self.exe, "burn", "0.4", "0"])
        self.assertFalse(alive(run.sampler.pid))

    def test_the_deadline_kills_reaps_and_reports_the_child_it_owns(self):
        run = self.run_sampled("sleep", "30", "0", timeout=1)
        self.assertTrue(run.timed_out)
        self.assertEqual(run.returncode, -signal.SIGKILL)
        self.assertAlmostEqual(run.wall, 1, delta=0.8)
        self.assertEqual(run.problems, [])
        self.assertFalse(alive(run.sampler.pid))
        self.assertFalse(run.sampler.thread.is_alive())
        r = bench_disk.finish_record(parse(run.output, run.wall, run.returncode), run, 1)
        self.assertEqual((r["result"], r["wall_s"]), ("timeout", 1))

    def test_a_timeout_does_not_wait_for_a_signal_that_never_lands(self):
        # (A refused or lost kill must not hold the run open until the child
        # ends by itself: the wait is bounded and the child is still reaped.)
        asked = []
        with patch.object(bench_disk, "kill_pid", lambda pid, as_root: asked.append(pid)), \
             patch.object(bench_disk, "KILL_GRACE_S", 0.5):
            run = self.run_sampled("sleep", "30", "0", timeout=1)
        self.assertEqual(asked, [run.sampler.pid])
        self.assertTrue(run.timed_out)
        self.assertLess(run.wall, 4)
        self.assertFalse(alive(run.sampler.pid))

    def test_only_the_owned_child_and_its_group_member_are_signalled(self):
        decoy = subprocess.Popen([sys.executable, "-c", "import time; time.sleep(30)"])
        self.addCleanup(lambda: (decoy.kill(), decoy.wait()))
        group = os.path.join(self.tmp.name, "cgroup")
        os.mkdir(group)
        # (The group this runner made holds the measured process, which here is
        # the decoy: the only other pid the runner may signal.)
        with open(os.path.join(group, "cgroup.procs"), "w") as stream:
            stream.write(f"{decoy.pid}\n")
        killed = []
        with patch.object(bench_disk, "kill_pid", lambda pid, as_root: killed.append((pid, as_root))), \
             patch.object(bench_disk, "KILL_GRACE_S", 0.5):
            run = self.run_sampled("sleep", "30", "0", timeout=1, cgroup=FakeCgroup(group))
        self.assertEqual(sorted(killed), [(decoy.pid, True), (run.sampler.pid, False)])
        self.assertFalse(alive(run.sampler.pid))
        self.assertIsNone(decoy.poll())  # the recording stub never signalled it

    def test_a_reader_failure_is_reported_with_the_run(self):
        def fail_on_progress(self, text):
            if "Progress" in text:
                raise RuntimeError("no progress report")

        with patch.object(bench_disk.Sampler, "line", fail_on_progress):
            run = self.run_sampled("burn", "0.1", "0", timeout=30)
        self.assertEqual(run.returncode, 0)
        self.assertIn("Progress(0)", run.output)  # the line was read; parsing it failed
        self.assertEqual(len(run.problems), 1)
        self.assertIn("reader: RuntimeError: no progress report", run.problems[0])
        r = bench_disk.finish_record(parse(run.output, run.wall, run.returncode), run, 30)
        # (A run whose observation failed is not a complete sample, even when
        # the child itself exited successfully.)
        self.assertEqual(r["result"], "bench-error")
        self.assertIn("no progress report", r["error"])

    def test_a_sampler_failure_stops_sampling_and_is_reported(self):
        with patch.object(bench_disk.Sampler, "sample", side_effect=OSError("no /proc")):
            run = self.run_sampled("sleep", "1.5", "0", timeout=30)
        self.assertEqual(run.sampler.samples, [])
        self.assertEqual(len(run.problems), 1)
        self.assertIn("sampler: OSError: no /proc", run.problems[0])
        self.assertFalse(run.sampler.thread.is_alive())
        r = bench_disk.finish_record(parse(run.output, run.wall, run.returncode), run, 30)
        self.assertEqual(r["result"], "bench-error")

    def test_a_lost_wait4_leaves_no_child_and_no_invented_cpu(self):
        real = os.wait4
        seen = []

        def flaky(pid, options):
            if not seen:
                seen.append(pid)
                raise ChildProcessError(10, "No child processes")
            return real(pid, options)

        with patch.object(bench_disk.os, "wait4", flaky):
            run = self.run_sampled("burn", "0.2", "0", timeout=30)
        self.assertIsNone(run.rusage)  # never a process-wide delta in its place
        self.assertIn("wait4:", run.problems[0])
        self.assertFalse(alive(run.sampler.pid))
        r = bench_disk.finish_record(parse(run.output, run.wall, run.returncode), run, 30)
        self.assertNotIn("cpu_s", r)
        self.assertNotIn("maxrss_mib", r)
        self.assertNotEqual(r["result"], "success")  # what it is not: a clean sample
        self.assertIn("wait4:", r["problems"][0])
        self.assertEqual(bench_disk.describe(r).split()[4:6], ["cpu", "-"])

    def test_disk_telemetry_without_wait4_has_no_peak_rss(self):
        # The disk lane's `samples` are telemetry vectors (elapsed seconds,
        # instantaneous RSS, read/write bytes, disk bytes, state count, cgroup
        # MiB). Without wait4 usage none of them is this run's peak RSS, and the
        # importer must not read the read-byte column as MiB.
        sampler = SimpleNamespace(io={}, peak_disk=0, peak_cg=0,
                                  samples=[[1, 64, 4096, 1048576, 2097152, 40000, 128]])
        run = SimpleNamespace(rusage=None, timed_out=False, problems=[], sampler=sampler,
                              output="Model checking completed. No error has been found.\n",
                              wall=0.1, returncode=0)
        r = bench_disk.finish_record(parse(run.output, run.wall, run.returncode), run, 30)
        self.assertNotIn("maxrss_mib", r)
        row = normalize({}, r, "bench/disk.json", "/runs/M", model="M", mode="-compile", workers=1)
        self.assertIsNone(row["metrics"]["rss_mib"])

    def test_every_run_closes_the_pipe_it_opened(self):
        before = open_files()
        for _ in range(6):
            self.run_sampled("burn", "0.0", "0", timeout=30)
        self.assertLessEqual(open_files(), before)


class ControlGroupFailures(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="tlx-measure-")
        self.addCleanup(self.tmp.cleanup)
        self.model = {"id": "A", "tla": os.path.join(self.tmp.name, "A.tla"), "cfg": os.path.join(self.tmp.name, "A.cfg")}
        self.exe = os.path.join(self.tmp.name, "tlx")
        with open(self.exe, "w") as stream:
            stream.write("#!/bin/sh\n")
        os.chmod(self.exe, 0o755)

    def test_a_refused_control_group_starts_no_child(self):
        with patch.object(bench_disk.Cgroup, "__enter__", side_effect=subprocess.SubprocessError("sudo refused")), \
             patch.object(bench_disk, "run_sampled") as sampled:
            with self.assertRaises(subprocess.SubprocessError):
                bench_disk.run_tlx(self.model, self.exe, [], 30, {}, cg_mib=64)
        self.assertFalse(sampled.called)

    def test_a_half_made_control_group_is_released_again(self):
        # (The directory is made and the limit is not: `with` never calls
        # __exit__ when __enter__ raises, so the failed enter releases it.)
        released, made = [], []

        def fake_run(cmd, **kwargs):
            if "rmdir" in cmd:
                released.append(cmd)
                return subprocess.CompletedProcess(cmd, 0)
            if "memory.max" in " ".join(cmd):
                raise subprocess.CalledProcessError(1, cmd)
            made.append(cmd)
            return subprocess.CompletedProcess(cmd, 0)

        with patch.object(bench_disk.subprocess, "run", fake_run):
            with self.assertRaises(subprocess.SubprocessError):
                bench_disk.Cgroup(64).__enter__()
        self.assertTrue(made)
        self.assertEqual(len(released), 1)

    def test_a_refused_root_kill_is_named(self):
        refused = subprocess.CompletedProcess(["sudo"], 1, b"", b"sudo: a password is required")
        with patch.object(bench_disk.subprocess, "run", return_value=refused):
            why = bench_disk.kill_pid(4321, as_root=True)
        self.assertIn("kill 4321 refused", why)
        self.assertIn("password is required", why)
        with patch.object(bench_disk.os, "kill", side_effect=ProcessLookupError()):
            self.assertIsNone(bench_disk.kill_pid(4321, as_root=False))


class ReapRepeatedTlc(testkit.GuardedTestCase):
    """The repeated TLC collector accounts each child to its own lane
    (HARNESS-09): a process-wide RUSAGE_CHILDREN delta around the call folds in
    every child of another lane, and bench_ttfr runs its lanes in parallel."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="tlx-measure-")
        self.addCleanup(self.tmp.cleanup)
        self.argv = os.path.join(self.tmp.name, "argv.json")
        self.exe = child(self.tmp.name)
        self.model = {"id": "A", "tla": os.path.join(self.tmp.name, "A.tla"), "cfg": os.path.join(self.tmp.name, "A.cfg")}
        environ = patch.dict(os.environ, {"BENCH_ARGV": self.argv})
        environ.start()
        self.addCleanup(environ.stop)

    def collect(self, *args, timeout=30):
        with patch.object(tlc, "tlc_cmd", return_value=[self.exe, *args]):
            return bench._collect_tlc(self.model, 1, timeout)

    def test_parallel_lanes_keep_their_own_cpu(self):
        # (Two lanes at once, each with its own known CPU burn: the sum of both
        # would be wrong for either record.)
        results = {}

        def lane(name, amount):
            results[name] = self.collect("burn", amount, "0")

        lanes = [threading.Thread(target=lane, args=("long", "1.2")), threading.Thread(target=lane, args=("short", "0.2"))]
        for lane_thread in lanes:
            lane_thread.start()
        for lane_thread in lanes:
            lane_thread.join()
        long_cpu, short_cpu = results["long"]["cpu_s"], results["short"]["cpu_s"]
        self.assertGreater(long_cpu, 1.0)
        self.assertLess(long_cpu, 2.0)
        self.assertLess(short_cpu, 0.6)
        self.assertGreater(long_cpu - short_cpu, 0.6)
        self.assertEqual(recorded(self.argv)[1], "burn")  # the real child ran

    def test_a_repeated_run_past_its_deadline_is_a_timeout(self):
        r = self.collect("sleep", "30", "0", timeout=1)
        self.assertEqual((r["result"], r["wall_s"]), ("timeout", 1))


class StagedChild(testkit.GuardedTestCase):
    """What a measured run hands its child: the staged model, the directory of
    the copy, the environment, and a usage record of that child (HARNESS-09)."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="tlx-stage-")
        self.addCleanup(self.tmp.cleanup)
        self.argv = os.path.join(self.tmp.name, "argv.json")
        self.context = os.path.join(self.tmp.name, "context.json")
        self.exe = child(self.tmp.name)
        self.spec = os.path.join(self.tmp.name, "spec")
        os.mkdir(self.spec)
        for name, text in (("A.tla", "---- MODULE A ----\n====\n"), ("A.cfg", "SPECIFICATION Spec\n"), ("data.csv", "x\n")):
            with open(os.path.join(self.spec, name), "w") as stream:
                stream.write(text)
        self.model = {"id": "A", "scratch": True, "tla": os.path.join(self.spec, "A.tla"), "cfg": os.path.join(self.spec, "A.cfg")}
        environ = patch.dict(os.environ, {"BENCH_ARGV": self.argv, "BENCH_CONTEXT": self.context})
        environ.start()
        self.addCleanup(environ.stop)

    def test_the_child_runs_in_a_copy_of_the_spec_directory(self):
        asked = []

        def command(m, args, exe):
            asked.append((m, args, exe))
            return [self.exe, "burn", "0.05", "0"]

        with patch.object(bench, "tlx_cmd", command):
            r = bench.tlx(self.model, ["-workers", "1"], 60)
        self.assertEqual((r["result"], r["exit"]), ("success", 0))
        self.assertGreater(r["cpu_s"], 0.03)  # this child's own usage
        seen = recorded(self.context)
        self.assertEqual(seen["argv"], [self.exe, "burn", "0.05", "0"])  # the complete ordered argv
        self.assertEqual(os.path.basename(seen["cwd"]), "spec")
        self.assertNotEqual(os.path.realpath(seen["cwd"]), os.path.realpath(self.spec))
        self.assertEqual(seen["files"], ["A.cfg", "A.tla", "data.csv"])  # the whole directory
        self.assertIn("TLX_CLASSPATH", seen["env"])  # what a measured tlx child needs
        self.assertFalse(os.path.exists(seen["cwd"]))  # removed with the run
        # The model the run built its command from points into that copy.
        self.assertEqual(os.path.realpath(os.path.dirname(asked[0][0]["tla"])), seen["cwd"])
        self.assertEqual(os.path.basename(asked[0][0]["cfg"]), "A.cfg")
        self.assertEqual(sorted(os.listdir(self.spec)), ["A.cfg", "A.tla", "data.csv"])  # original untouched

    def test_a_model_without_a_scratch_spec_gets_no_directory(self):
        model = {"id": "B", "tla": "/nowhere/B.tla", "cfg": "/nowhere/B.cfg"}
        with measurement.staged_run(model, "tlx-measure-") as (staged, cwd, root):
            self.assertIs(staged, model)
            self.assertIsNone(cwd)
            self.assertIsNone(root)

    def test_a_workspace_run_gets_a_directory_of_its_own(self):
        model = {"id": "B", "tla": "/nowhere/B.tla", "cfg": "/nowhere/B.cfg"}
        with measurement.staged_run(model, "tlx-measure-", workspace=True, mode=0o755) as (staged, cwd, root):
            self.assertIs(staged, model)
            self.assertIsNone(cwd)
            self.assertTrue(os.path.isdir(root))
            self.assertEqual(os.stat(root).st_mode & 0o777, 0o755)
            self.assertTrue(os.path.basename(root).startswith("tlx-measure-"))
        self.assertFalse(os.path.exists(root))

    def test_a_failed_run_still_removes_the_scratch_directory(self):
        with self.assertRaises(RuntimeError):
            with measurement.staged_run(self.model, "tlx-measure-") as (staged, cwd, root):
                self.assertTrue(os.path.isdir(cwd))
                raise RuntimeError("the measured run failed")
        self.assertFalse(os.path.exists(root))


class RootRelativeStaging(testkit.GuardedTestCase):
    """A model whose spec reads inputs relative to the corpus root runs there.

    The benchmark used to hand every model that writes nothing ``cwd=None``, so
    a measured tlx (or TLC) child inherited the driver's directory and
    EWD998ChanTrace's ``specifications/ewd998/EWD998ChanTrace.ndjson`` - named
    the way upstream's Examples CI names it from the Examples root - was not
    there. ``staged_run``/``staged_tlc_run`` now start such a model in its
    corpus root; every other model keeps the driver's directory.
    """

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="tlx-root-relative-")
        self.addCleanup(self.tmp.cleanup)
        self.root = os.path.join(self.tmp.name, "Examples")
        self.spec = os.path.join(self.root, "specifications", "A")
        os.makedirs(self.spec)
        for name, text in (("A.tla", "---- MODULE A ----\n====\n"), ("A.cfg", "INIT Init\n"), ("A.ndjson", "{}\n")):
            with open(os.path.join(self.spec, name), "w") as stream:
                stream.write(text)
        self.model = {"id": "A", "tla": os.path.join(self.spec, "A.tla"),
                      "cfg": os.path.join(self.spec, "A.cfg"), "root": self.root,
                      "cwd": "root", "inputs": ["specifications/A/A.ndjson"]}

    def test_the_measured_child_starts_in_the_corpus_root(self):
        argv = os.path.join(self.tmp.name, "argv.json")
        context = os.path.join(self.tmp.name, "context.json")
        environ = patch.dict(os.environ, {"BENCH_ARGV": argv, "BENCH_CONTEXT": context})
        environ.start()
        self.addCleanup(environ.stop)
        exe = child(self.tmp.name)
        with patch.object(bench, "tlx_cmd", lambda m, args, binary: [exe, "burn", "0.02", "0"]):
            r = bench.tlx(self.model, ["-workers", "1"], 60)
        self.assertEqual(r["result"], "success")
        seen = recorded(context)
        self.assertEqual(os.path.realpath(seen["cwd"]), os.path.realpath(self.root))
        # The relative input the spec names resolves here, and nowhere else.
        self.assertIn("A.ndjson", os.listdir(os.path.join(seen["cwd"], "specifications", "A")))

    def test_run_dir_is_the_corpus_root_only_for_a_root_relative_model(self):
        self.assertIsNone(measurement.run_dir({"id": "A", "tla": "/spec/A.tla", "cfg": "/spec/A.cfg"}))
        self.assertEqual(measurement.run_dir(self.model), self.root)
        with measurement.staged_run(self.model, "tlx-measure-") as (staged, cwd, root):
            self.assertEqual(cwd, self.root)
            self.assertIsNone(root)

    def test_the_tlc_baseline_run_starts_where_its_inputs_are(self):
        with measurement.staged_tlc_run(self.model) as (cwd, module):
            self.assertEqual(os.path.realpath(cwd), os.path.realpath(self.root))
            self.assertEqual(module, os.path.join("specifications", "A", "A.tla"))
        plain = {"id": "A", "tla": "/spec/A.tla", "cfg": "/spec/A.cfg"}
        with measurement.staged_tlc_run(plain) as (cwd, module):
            self.assertEqual(cwd, "/spec")
            self.assertEqual(module, "A.tla")


class MeasurementAdapters(testkit.GuardedTestCase):
    """The staging, command, environment and accounting adapters themselves."""

    model = {"id": "A", "tla": "/spec/A.tla", "cfg": "/spec/A.cfg"}

    def test_a_measured_binary_is_absolute(self):
        relative = os.path.join("target", "release", "tlx")
        with patch.object(machine, "TLX", relative):
            self.assertEqual(measurement.binary_path(), os.path.abspath(relative))
        self.assertEqual(measurement.binary_path(os.path.join("bins", "old-tlx")), os.path.abspath(os.path.join("bins", "old-tlx")))

    def test_the_check_command_names_the_model_its_mode_and_its_extra_flags(self):
        self.assertEqual(measurement.check_argv("/bin/tlx", self.model, ["-workers", "2"]),
                         ["/bin/tlx", "check", "/spec/A.tla", "-config", "/spec/A.cfg", "-workers", "2"])
        # (One caller's own measurement is appended after the mode's arguments.)
        self.assertEqual(measurement.check_argv("/bin/tlx", self.model, ["-compile"], extra=["-metadir", "/tmp/md"]),
                         ["/bin/tlx", "check", "/spec/A.tla", "-config", "/spec/A.cfg", "-compile", "-metadir", "/tmp/md"])

    def test_the_measured_environment_carries_the_corpus_class_path_and_the_callers_overrides(self):
        env = measurement.measured_env({"TLX_CACHE": "/tmp/cache"})
        self.assertEqual(env["TLX_CLASSPATH"], os.pathsep.join(tlxlib.CLASSPATH_DIRS))
        self.assertEqual(env["TLX_CACHE"], "/tmp/cache")
        self.assertEqual(env["PATH"], os.environ["PATH"])  # the child inherits this process's environment

    def test_a_run_is_a_timeout_only_at_its_own_deadline(self):
        fields = {"stdout": "Model checking completed. No error has been found.\n", "stderr": "", "returncode": 0,
                  "wall": 1.0, "rusage": RUSAGE}
        self.assertEqual(measurement.result_of(ProcResult(**fields, timed_out=True), 120), {"result": "timeout", "wall_s": 120})
        killed = measurement.result_of(ProcResult(**{**fields, "returncode": -signal.SIGKILL, "wall": 200}), 120)
        self.assertNotEqual(killed["result"], "timeout")  # killed below its deadline: not the deadline's run
        self.assertEqual(killed["exit"], -signal.SIGKILL)  # the child's own exit code is the measurement

    def test_accounting_is_this_childs_own_usage(self):
        usage = SimpleNamespace(ru_utime=0.25, ru_stime=0.5, ru_maxrss=2 * 1024 * 1024)
        self.assertEqual(measurement.cpu_seconds(usage), 0.75)
        self.assertEqual(measurement.cpu_seconds(usage, decimals=None), 0.75)
        for platform, divisor in (("darwin", 1 << 20), ("linux", 1 << 10)):
            # (ru_maxrss is bytes on macOS and KiB on Linux: the same child
            # reads as a different number of MiB if the divisor is guessed.)
            with patch.object(measurement, "sys", SimpleNamespace(platform=platform)):
                self.assertEqual(measurement.rss_mib(usage), round(2 * 1024 * 1024 / divisor, 1))
                self.assertEqual(measurement.rss_mib(usage, decimals=None), 2 * 1024 * 1024 / divisor)


class TimeoutClassification(unittest.TestCase):
    """A run is a timeout when its own deadline expired - not when the child
    failed at its own pace (bench_profile) and not when something else killed
    it (bench.tlx: the OOM killer)."""

    model = {"id": "A", "tla": "A.tla", "cfg": "A.cfg"}

    def result(self, **over):
        fields = {"stdout": "", "stderr": "", "returncode": 0, "wall": 1.0, "timed_out": False, "rusage": RUSAGE}
        return ProcResult(**{**fields, **over})

    def test_a_run_that_fails_slowly_is_not_a_timeout(self):
        failed = self.result(returncode=3, wall=200, stdout="Error: Invariant I is violated\n")
        with patch.object(bench_profile, "run_proc", return_value=failed), \
             patch.object(bench, "tlx_cmd", return_value=["fake", "check"]):
            r = bench_profile.run_one(self.model, [], 120, "fake")
        # (The classifier this replaces read any nonzero exit after the deadline
        # as a timeout; the child's own exit code is the measurement.)
        self.assertEqual((r["result"], r["exit"]), ("safety failure", 3))

    def test_a_run_killed_below_its_deadline_is_not_a_timeout(self):
        oom = self.result(returncode=-signal.SIGKILL, wall=200)
        with patch.object(bench, "run_proc", return_value=oom), \
             patch.object(bench, "tlx_cmd", return_value=["fake", "check"]):
            r = bench.tlx(self.model, [], 120)
        self.assertNotEqual(r["result"], "timeout")

    def test_an_expired_deadline_is_kept_for_a_killed_run(self):
        expired = self.result(returncode=-signal.SIGKILL, wall=120, timed_out=True)
        with patch.object(bench, "run_proc", return_value=expired), \
             patch.object(bench, "tlx_cmd", return_value=["fake", "check"]):
            r = bench.tlx(self.model, [], 120)
        self.assertEqual((r["result"], r["wall_s"]), ("timeout", 120))


class TlcCollectorArguments(testkit.GuardedTestCase):
    """Every benchmark TLC collector passes the model's oracle arguments.

    A pinned `generated` count (EWD998ChanTrace's 11169 under `-fp 0`,
    docs/compat.md D-25) is deterministic only if the collectors that build a
    TLC baseline - not just `scripts/corpus.py` - pass the model's `tlc_args`,
    and the arguments are part of the input identity.
    """

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="tlx-collector-args-")
        self.addCleanup(self.tmp.cleanup)
        self.tla = os.path.join(self.tmp.name, "M.tla")
        self.cfg = os.path.join(self.tmp.name, "M.cfg")
        for path, text in ((self.tla, "---- MODULE M ----\n====\n"), (self.cfg, "INIT Init\n")):
            with open(path, "w") as stream:
                stream.write(text)
        self.model = {"id": "M", "tla": self.tla, "cfg": self.cfg, "features": [], "flags": [],
                      "tlc_args": ["-fp", "0"]}
        self.args = {}
        self.addCleanup(lambda: bench_budget.configure(argparse.Namespace()))
        bench_budget.configure(argparse.Namespace())  # no deadline for a collector probe

    def capture_tlc_cmd(self, spec, args, features=(), **kw):
        self.args["cmd"] = [str(a) for a in args]
        return ["java", *self.args["cmd"], kw.get("module") or os.path.basename(spec)]

    def assert_oracle_arguments(self):
        cmd = self.args["cmd"]
        self.assertIn("-fp", cmd)
        self.assertEqual(cmd[cmd.index("-fp") + 1], "0")

    def fake_proc(self, cmd, *args, **kwargs):
        self.args["cmd"] = [str(x) for x in cmd]
        return ProcResult(stdout="Model checking completed. No error has been found.\n", stderr="",
                          returncode=0, wall=0.1, timed_out=False, rusage=RUSAGE)

    def test_the_shared_rule_is_the_models_own_oracle_arguments(self):
        self.assertEqual(models.oracle_tlc_args(self.model), ["-fp", "0"])
        self.assertEqual(models.oracle_tlc_args({}), [])

    def test_bench_collect_tlc_passes_the_oracle_arguments(self):
        with patch.object(bench, "run_proc", self.fake_proc), \
             patch.object(tlc, "tlc_cmd", self.capture_tlc_cmd):
            r = bench._collect_tlc(self.model, 1, 10)
        self.assert_oracle_arguments()
        # A fresh `run --tlc` baseline needs this child's own peak RSS, not just
        # its CPU time, or the history row and the canonical baseline lose it.
        self.assertEqual(r["maxrss_mib"], measurement.rss_mib(RUSAGE))

    def test_tlcbase_measured_collector_passes_the_oracle_arguments(self):
        with patch.object(bench, "run_proc", self.fake_proc), \
             patch.object(tlc, "tlc_cmd", self.capture_tlc_cmd):
            tlcbase._collect_tlc_measured(self.model, 1, 10)
        self.assert_oracle_arguments()

    def test_disk_collector_passes_the_oracle_arguments(self):
        sampler = SimpleNamespace(io={}, peak_disk=0, samples=[], peak_cg=0)
        run = SimpleNamespace(rusage=RUSAGE, sampler=sampler, problems=[],
                              output="Model checking completed. No error has been found.\n", wall=0.1, returncode=0,
                              timed_out=False)
        with patch.object(bench_disk, "run_sampled", lambda *a, **k: run), \
             patch.object(tlc, "tlc_cmd", self.capture_tlc_cmd):
            bench_disk._collect_tlc(self.model, 1, 10, 512, 64)
        self.assert_oracle_arguments()


if __name__ == "__main__":
    unittest.main()
