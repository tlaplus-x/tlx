"""Tests of the continuous performance tracking (bench_suite.py): manifest,
comparator, verdict, report, and the runner end to end with fake tlx binaries."""

from benchmarking import models as bench_models
from unittest.mock import Mock, patch
import subprocess
import argparse, contextlib, io, json, os, shutil, stat, sys, tempfile, unittest

from benchmarking import bench_records as br
import bench
from benchmarking import bench_budget
from benchmarking import bench_suite as S
from cloud import cloud_common
import testkit
import tlxlib


def read(path):
    with open(path) as f:
        return json.load(f)


def write(path, text):
    with open(path, "w") as f:
        f.write(text)


def man(**over):
    m = {"id": "A/one", "size": "small", "timeout_s": 60, "runs": [{"mode": "compile", "workers": 1}, {"mode": "interp", "workers": 1}],
         "expect": {"result": "success", "source": "tlc-oracle", "distinct": 5, "generated": 10, "depth": 3}, "tlc_1w_s": 2.0}
    m.update(over)
    return {"version": 1, "models": [m, {**m, "id": "B/two", "size": "large", "runs": [{"mode": "compile", "workers": 16}]}]}


def rec(tier="small", walls=(1.0, 1.01, 1.02), distinct=5, result="success", model="A/one", mode="compile", workers=1, **kw):
    return {"tier": tier, "model": model, "mode": mode, "workers": workers, "walls": list(walls), "cpu": list(walls), "min": min(walls),
            "distinct": distinct, "result": result, **kw}


class Manifest(unittest.TestCase):
    def test_validation(self):
        self.assertEqual(S.validate_manifest(man()), [])
        bad = man(size="giant", timeout_s=0, runs=[{"mode": "jit", "workers": 0}], expect={"result": "success", "source": "tlc-oracle"})
        text = "\n".join(S.validate_manifest(bad))
        for s in ("size must", "timeout_s", "run mode", "run workers", "needs expect.distinct"):
            self.assertIn(s, text)
        dup = man()
        dup["models"].append(dict(dup["models"][0]))
        self.assertIn("duplicate id", "\n".join(S.validate_manifest(dup)))
        self.assertIn("duplicate run", "\n".join(S.validate_manifest(man(runs=[{"mode": "compile", "workers": 1}] * 2))))
        self.assertIn("expect.source", "\n".join(S.validate_manifest(man(expect={"result": "success", "source": "guess", "distinct": 1}))))
        with self.assertRaises(ValueError):
            tmp = tempfile.NamedTemporaryFile("w", suffix=".json", delete=False)
            json.dump({"version": 2, "models": []}, tmp)
            tmp.close()
            S.load_manifest(tmp.name)

    def test_entries(self):
        m = man()
        es = S.entries(m, "small,medium,large")
        self.assertEqual([e["key"] for e in es], ["small:A/one:compile:1w", "small:A/one:interp:1w", "large:B/two:compile:16w"])
        self.assertEqual([e["model"] for e in S.entries(m, "large")], ["B/two"])
        self.assertEqual(len(S.entries(m, "all")), 3)
        self.assertEqual([e["model"] for e in S.entries(m, "all", "two")], ["B/two"])
        with self.assertRaises(ValueError):
            S.entries(m, "tiny")
        self.assertEqual([e["mode"] for e in S.entries(m, "all", modes="compile")], ["compile", "compile"])
        self.assertEqual(S.entries(m, "all", modes="default"), [])
        with self.assertRaisesRegex(ValueError, "unknown mode"):
            S.entries(m, "all", modes="compiled")

    def test_oracle_problems(self):
        m = man()
        ok = {"A/one": {"tlc": {"result": "success", "distinct": 5, "generated": 10, "depth": 3}},
              "B/two": {"tlc": {"result": "success", "distinct": 5, "generated": 10, "depth": 3}}}
        self.assertEqual(S.oracle_problems(m, ok), [])
        ok["A/one"]["tlc"]["distinct"] = 6
        self.assertIn("distinct 6", S.oracle_problems(m, ok)[0])
        self.assertIn("no oracle result", S.oracle_problems(m, {})[0])

    def test_the_ewd_trace_pin_matches_the_corrected_oracle(self):
        # The active suite pin and the correctness oracle move together: the
        # pre-fix staging's `error` is now the corrected complete search, with
        # TLC collected under `-fp 0` (docs/compat.md D-25).
        manifest = S.load_manifest()
        self.assertEqual(S.validate_manifest(manifest), [])
        entry = next(m for m in manifest["models"] if m["id"] == "ewd998/EWD998ChanTrace")
        expect = entry["expect"]
        self.assertEqual(expect["source"], "tlc-oracle")
        self.assertEqual({f: expect[f] for f in ("result", "distinct", "generated", "depth")},
                         {"result": "success", "distinct": 659, "generated": 11169, "depth": 655})
        corrected = {"result": "success", "distinct": 659, "generated": 11169, "depth": 655}
        self.assertEqual(S.check_counts(corrected, expect), [])
        # (The frozen staging's result stays a mismatch; it is not relabelled.)
        self.assertTrue(S.check_counts({"result": "error"}, expect))


class Counts(unittest.TestCase):
    ex = {"result": "success", "source": "tlc-oracle", "distinct": 5, "generated": 10, "depth": 3}

    def test_match_and_mismatch(self):
        good = rec(generated=10, depth=3)
        self.assertEqual(S.check_counts(good, self.ex), [])
        self.assertEqual(len(S.check_counts({**good, "distinct": 6}, self.ex)), 1)
        self.assertIn("depth 4", S.check_counts({**good, "depth": 4}, self.ex)[0])
        self.assertIn("result 'timeout'", S.check_counts({**good, "result": "timeout"}, self.ex)[0])

    def test_violations_check_only_the_kind(self):
        ex = {"result": "deadlock", "source": "tlc-oracle"}
        self.assertEqual(S.check_counts(rec(result="deadlock", distinct=7), ex), [])
        self.assertTrue(S.check_counts(rec(result="success"), ex))

    def test_unpinned_is_not_enforced(self):
        self.assertEqual(S.check_counts(rec(result="anything"), {"source": "unpinned", "result": None, "distinct": None}), [])


class SampleContract(unittest.TestCase):
    """HARNESS-07: every completed sample and warm-up is validated against its mode
    contract before the aggregate is taken, and a mismatch of an earlier run is
    kept next to the aggregate instead of being erased by a later success."""

    def entry(self, **over):
        e = {"key": "small:A/one:compile:1w", "model": "A/one", "size": "small", "mode": "compile", "workers": 1, "timeout_s": 30,
             "expect": {"result": "success", "source": "tlc-oracle", "distinct": 5, "generated": 10, "depth": 3}}
        e.update(over)
        return e

    def sample(self, result="success", distinct=5, **over):
        return {"result": result, "distinct": distinct, "generated": 10, "depth": 3,
                "wall_s": 1.0, "cpu_s": 1.0, "compatibility": True, **over}

    def measure(self, script, entry=None, repeat=3):
        """One suite entry measured with the scripted samples (one per run, the
        discarded warm-up first): the last bin's record and the runs made."""
        runs = []

        def once(bench, m, e, exe, instr, **kw):
            runs.append(script[len(runs)])
            return runs[-1]

        entry = entry or self.entry()
        with patch.object(S, 'measure_once', side_effect=once), contextlib.redirect_stdout(io.StringIO()):
            records = S.measure_entry(bench, {}, entry, [("new", "fake")], repeat, False, lambda _: 1,
                                      budget=bench_budget.Budget())
        return records["new"], runs

    def test_isolated_cache_is_shared_with_samples_but_not_other_binary(self):
        seen = {}
        def once(bench, m, e, exe, instr, **kw):
            env = kw['env']
            path = env['TLX_CACHE']
            self.assertTrue(os.path.isdir(path))
            self.assertEqual(env['TLX_NATIVE_SYNC'], '1')
            seen.setdefault(exe, []).append(path)
            return self.sample()
        with patch.object(S, 'measure_once', side_effect=once), contextlib.redirect_stdout(io.StringIO()):
            records = S.measure_entry(bench, {}, self.entry(), [('base', 'a'), ('new', 'b')], 3,
                                      False, lambda _: 1, budget=bench_budget.Budget(), isolate_cache=True)
        self.assertEqual(len(seen['a']), 4)
        self.assertEqual(len(set(seen['a'])), 1)
        self.assertNotEqual(seen['a'][0], seen['b'][0])
        self.assertFalse(os.path.exists(seen['a'][0]))
        self.assertEqual(records['new']['cache']['mode'], 'fresh-per-model')

    def test_first_middle_and_last_sample_mismatches_are_all_reported(self):
        for i in (1, 2, 3):
            script = [self.sample() for _ in range(4)]  # index 0 is the warm-up
            script[i] = self.sample(result='deadlock', distinct=3)
            rec, _ = self.measure(script)
            self.assertEqual(rec["count_problems"],
                             ["result 'deadlock', expected 'success'"] if i == 3 else
                             [f"sample {i}: result 'deadlock', expected 'success'"], f"sample {i}")
            # The aggregate is still the last measured sample's.
            self.assertEqual((rec["result"], rec["distinct"]), ('deadlock', 3) if i == 3 else ('success', 5))

    def test_a_wrong_count_in_an_earlier_sample_survives_a_later_success(self):
        rec, _ = self.measure([self.sample(), self.sample(distinct=6), self.sample(), self.sample()])
        self.assertEqual(rec["count_problems"], ["sample 1: distinct 6, expected 5"])
        self.assertEqual((rec["result"], rec["distinct"]), ("success", 5))

    def test_a_mismatching_warmup_is_reported_with_its_diagnostics(self):
        bad = self.sample(result='safety failure', distinct=3, violated='Inv!One', error='Error: Invariant Inv!One is violated')
        rec, _ = self.measure([bad, self.sample(), self.sample(), self.sample()])
        self.assertEqual(rec["count_problems"], ["warmup 1: result 'safety failure', expected 'success'"])
        # The wrong verdict is kept with the name it was found under and why.
        self.assertEqual([w["result"] for w in rec["warmups"]], ["safety failure"])
        self.assertEqual([w["violated"] for w in rec["warmups"]], ["Inv!One"])
        self.assertIn("Inv!One is violated", rec["warmups"][0]["error"])
        self.assertEqual(rec["walls"], [1.0, 1.0, 1.0])  # A discarded warm-up is not a repetition.
        self.assertEqual([s["result"] for s in rec["samples"]], ["success"] * 3)
        self.assertEqual([s.get("violated") for s in rec["samples"]], [None] * 3)  # Nothing to keep on agreement.

    def test_an_unfinished_run_has_no_counts_and_stays_with_the_incomplete_gate(self):
        # Only a run that produced a verdict has counts of its own to compare. A
        # timed-out warm-up leaves the entry skipped and inconclusive, with no
        # count problem invented for it.
        rec, _ = self.measure([self.sample(result='timeout', distinct=None, wall_s=10, cpu_s=0)] + [self.sample()] * 3)
        self.assertEqual((rec["result"], rec["skipped"], rec["completed_samples"]), ("skipped", "sample timeout", 0))
        self.assertEqual((rec["walls"], rec["samples"], rec["count_problems"]), ([], [], []))
        self.assertEqual([w["result"] for w in rec["warmups"]], ["timeout"])
        # An earlier run without a verdict is not a mismatch either, while a run
        # that ended in an error is: it is a verdict, not a missing measurement.
        for label, bad, expected in (("unknown", self.sample(result='unknown', distinct=None), []),
                                     ("error", self.sample(result='error', distinct=None, error='Error: bad operand'),
                                      ["sample 1: result 'error', expected 'success'"])):
            rec, _ = self.measure([self.sample(), bad, self.sample(), self.sample()])
            with self.subTest(middle=label):
                self.assertEqual(rec["count_problems"], expected)

    def test_a_reduced_default_mode_sample_is_allowed_but_still_needs_its_verdict(self):
        entry = self.entry(mode="default")
        script = [self.sample(distinct=2, compatibility=False) for _ in range(4)]
        rec, _ = self.measure(script, entry)
        self.assertEqual(rec["count_problems"], [])
        self.assertEqual(S.judge(None, {entry["key"]: rec}, [], [], bench.compare_runs)["count_failures"], [])
        script[2] = self.sample(result='violation', distinct=2, compatibility=False)
        rec, _ = self.measure(script, entry)
        self.assertEqual(rec["count_problems"], ["sample 2: result 'violation', expected 'success'"])

    def test_warmups_are_not_repetitions_so_the_incomplete_gate_is_preserved(self):
        rec, _ = self.measure([self.sample() for _ in range(4)])
        self.assertEqual((len(rec["samples"]), len(rec["warmups"]), len(rec["walls"])), (3, 1, 3))
        for key, script, requested, expect_eligible in (
                ("complete", [self.sample()] * 4, 3, True),
                ("incomplete", [self.sample(), self.sample(result='timeout', wall_s=10, cpu_s=0)], 3, False)):
            rec, _ = self.measure(script, repeat=requested)
            with tempfile.TemporaryDirectory() as root:
                os.makedirs(os.path.join(root, "bench"))
                write(os.path.join(root, "bench", "h.json"), json.dumps(
                    {"suite": True, "repeat": requested, "commit": "abc1234",
                     "runs": {"small:A/one:compile:1w": {**rec, "content_digest": "verified-input"}}}))
                migrated, = br.migrate(root)
            with self.subTest(case=key):
                self.assertEqual(migrated["provenance"]["repetitions"], {"requested": requested, "completed": len(rec["walls"])})
                self.assertEqual(br.eligible(migrated), expect_eligible)


class Comparator(unittest.TestCase):
    def cmp(self, a, b, **kw):
        return bench.compare_runs({"k": a}, {"k": b}, **kw)

    def test_pass_regression_faster(self):
        self.assertEqual(self.cmp(rec(), rec(walls=(1.01, 1.02, 1.03)))["rows"][0]["flag"], "PASS")
        c = self.cmp(rec(), rec(walls=(1.5, 1.51, 1.52)))
        self.assertEqual((c["regress"], c["rows"][0]["flag"]), (["k"], "REGRESSION"))
        self.assertEqual(self.cmp(rec(walls=(2.0, 2.01, 2.02)), rec())["better"], ["k"])

    def test_inconclusive(self):
        noisy = self.cmp(rec(), rec(walls=(1.0, 1.5, 1.2)))
        self.assertEqual((noisy["inconclusive"], noisy["regress"]), (["k"], []))
        few = self.cmp(rec(walls=(1.0, 1.0)), rec(walls=(2.0, 2.0)))
        self.assertEqual(few["inconclusive"], ["k"])
        self.assertEqual(bench.compare_runs({"k": rec()}, {})["inconclusive"], ["k"])

    def test_noise_does_not_hide_a_big_regression_threshold(self):
        # A 2x slowdown is a regression when the samples are quiet, never when they are noisy (inconclusive instead).
        self.assertEqual(self.cmp(rec(), rec(walls=(2.0, 2.01, 2.02)))["regress"], ["k"])

    def test_distinct_change_is_a_regression(self):
        c = self.cmp(rec(), rec(distinct=6))
        self.assertEqual(c["regress"], ["k"])
        self.assertEqual(c["rows"][0]["distinct"], (5, 6))

    def test_violation_counts_are_scheduling_dependent(self):
        # A stop at a violation counts the states found so far: with several workers it varies (seen on a deadlock run).
        d, d2 = rec(result="deadlock", distinct=100), rec(result="deadlock", distinct=90)
        self.assertEqual(self.cmp(d, d2)["regress"], ["k"])
        self.assertEqual(self.cmp(d, d2, distinct_success_only=True)["regress"], [])
        self.assertEqual(self.cmp(rec(), rec(distinct=6), distinct_success_only=True)["regress"], ["k"])

    def test_min_delta(self):
        c = self.cmp(rec(walls=(0.01, 0.0101, 0.0102)), rec(walls=(0.03, 0.0301, 0.0302)))
        self.assertEqual(c["regress"], [])


class Verdict(unittest.TestCase):
    def judge(self, base, runs, skipped=()):
        return S.judge(base, runs, [], skipped, bench.compare_runs)

    def test_outcomes(self):
        ok = {"k": rec(count_problems=[])}
        self.assertEqual(self.judge(None, ok)["outcome"], "BASELINE")
        self.assertEqual(self.judge({"k": rec()}, ok)["outcome"], "PASS")
        slow = {"k": rec(walls=(2.0, 2.01, 2.02), count_problems=[])}
        v = self.judge({"k": rec()}, slow)
        self.assertEqual((v["outcome"], v["regressions"][0]["key"]), ("REGRESSION", "k"))
        self.assertEqual(S.exit_status(v), 1)
        v = self.judge(None, {"k": rec(count_problems=["distinct 6, expected 5"])})
        self.assertEqual((v["outcome"], v["count_failures"][0]["key"]), ("REGRESSION", "k"))
        v = self.judge({"k": rec()}, {"k": rec(walls=(1.0, 1.4, 1.1), count_problems=[])})
        self.assertEqual((v["outcome"], S.exit_status(v)), ("INCONCLUSIVE", 2))
        v = self.judge(None, ok, skipped=["large:B/two:compile:16w"])
        self.assertEqual((v["outcome"], S.exit_status(v)), ("INCONCLUSIVE", 2))
        self.assertEqual(S.exit_status({"outcome": "PASS"}), 0)

    def test_regression_names_model_and_range(self):
        h = {"commit": "bbb", "base": {"commit": "aaa"}, "runs": {"k": {}}, "machine": "m", "range": ["abc1234 slower thing"]}
        v = {"outcome": "REGRESSION", "count_failures": [], "inconclusive": [], "skipped": [],
             "regressions": [{"key": "small:A/one:compile:1w", "ratio": 2.0, "a": 1.0, "b": 2.0}]}
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            S.print_verdict(h, v)
        text = buf.getvalue()
        self.assertIn("small:A/one:compile:1w", text)
        self.assertIn("aaa..bbb", text)
        self.assertIn("abc1234 slower thing", text)


class Parsing(unittest.TestCase):
    def test_perf_output(self):
        self.assertEqual(S.instructions_of("# started\n12345678,,instructions:u,100,100.00,,\n"), 12345678)
        self.assertIsNone(S.instructions_of("<not counted>,,instructions:u,0,100.00,,\n"))
        self.assertIsNone(S.instructions_of(""))


FAKE = """#!/usr/bin/env python3
import os, sys, time
time.sleep({sleep})
print("Model checking completed. No error has been found.")
print("{generated} states generated, {distinct} distinct states found, 0 states left on queue.")
print("The depth of the complete state graph search is 3.")
"""


def fake(directory, name, sleep=0.1, distinct=5, generated=10):
    path = os.path.join(directory, name)
    with open(path, "w") as f:
        f.write(FAKE.format(sleep=sleep, distinct=distinct, generated=generated))
    os.chmod(path, os.stat(path).st_mode | stat.S_IEXEC)
    return path


FAKE_WALL_S = 0.1  # The fixed wall time of one fake run (see EndToEnd.setUp).


class EndToEnd(testkit.GuardedTestCase):
    """The runner with fake tlx binaries: baseline, pass, forced regression, count mismatch."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.d = self.tmp.name
        self.model = {"tla": "x.tla", "cfg": "x.cfg", "flags": [], "tlc": {}}
        self.man = {"version": 1, "models": [
            {"id": "A/one", "size": "small", "timeout_s": 30, "runs": [{"mode": "compile", "workers": 1}], "tlc_1w_s": 1.0,
             "expect": {"result": "success", "source": "tlc-oracle", "distinct": 5, "generated": 10, "depth": 3}},
            {"id": "B/two", "size": "small", "timeout_s": 30, "runs": [{"mode": "interp", "workers": 1}],
             "expect": {"result": "success", "source": "tlc-oracle", "distinct": 5, "generated": 10, "depth": 3}}]}
        # The clock of the verdicts is the test's, not the machine's: every fake
        # run still executes for real (exit status, parsed counts), but its
        # wall and cpu time are fixed at FAKE_WALL_S times the forced slow-down,
        # so machine load cannot make a PASS inconclusive. The noise rules are
        # exercised with injected samples in Comparator and Verdict.
        real = S.measure_once
        def clocked(bench, m, entry, exe, instr, slow=1.0, **kw):
            r = real(bench, m, entry, exe, instr, slow=1.0, **kw)
            if r.get("result") not in ("timeout", "skipped"):
                r["wall_s"] = r["cpu_s"] = round(FAKE_WALL_S * slow, 3)
            return r
        patcher = patch.object(S, "measure_once", clocked)
        patcher.start()
        self.addCleanup(patcher.stop)

    def tearDown(self):
        self.tmp.cleanup()

    def test_sample_checkpoint_exists_before_next_sample_times_out(self):
        calls = []
        def measure(bench, model, entry, exe, instr, **kwargs):
            calls.append(entry['key'])
            if len(calls) == 3:
                saved = read(os.path.join(self.d, 'h.json'))
                self.assertEqual(len(saved['samples']), 2)
                self.assertEqual(saved['runs'][entry['key']]['walls'], [1])
                raise subprocess.TimeoutExpired('fake', 30)
            return {'result': 'success', 'wall_s': 1, 'cpu_s': 1, 'distinct': 5, 'generated': 10, 'depth': 3}
        with patch.object(S, 'measure_once', side_effect=measure):
            rc, output, history = self.run_suite(fake(self.d, 'checkpoint'))
        self.assertNotEqual(rc, 0)
        self.assertIn('sample timeout', str(history['budget']['skipped']))
        self.assertTrue(history['verdict']['skipped'])
        self.assertIn('sample A/one new round 1: 1.000s', output)

    def test_a_mismatching_earlier_sample_is_not_erased_by_the_final_success(self):
        # The whole driver: a binary that agrees except on its third run (the
        # second measured sample of A/one). The aggregate is a success, and the
        # mismatch of round 2 still fails the run and is named in the report.
        flaky = os.path.join(self.d, "flaky")
        write(flaky, """#!/usr/bin/env python3
import json, os, sys
n = int(open(__file__ + '.runs').read()) + 1 if os.path.exists(__file__ + '.runs') else 1
open(__file__ + '.runs', 'w').write(str(n))
with open(__file__ + '.log', 'a') as f:
    f.write(json.dumps({'argv': sys.argv, 'cwd': os.getcwd(), 'classpath': os.environ.get('TLX_CLASSPATH'),
                        'native_sync': os.environ.get('TLX_NATIVE_SYNC')}) + '\\n')
distinct = 6 if n == 3 else 5
print("Model checking completed. No error has been found.")
print(f"{distinct * 2} states generated, {distinct} distinct states found, 0 states left on queue.")
print("The depth of the complete state graph search is 3.")
""")
        os.chmod(flaky, os.stat(flaky).st_mode | stat.S_IEXEC)
        for run in self.man["models"][0]["runs"]:
            run["args"] = ["-tlc"]  # The counts of a TLC-compatible run are its contract.
        rc, out, h = self.run_suite(flaky)
        self.assertEqual((rc, h["verdict"]["outcome"]), (1, "REGRESSION"), out)
        key, = (k for k in h["runs"] if k.startswith("small:A/one"))
        r = h["runs"][key]
        self.assertEqual(r["count_problems"], ["sample 2: distinct 6, expected 5; generated 12, expected 10"])
        self.assertEqual((len(r["walls"]), r["result"], r["distinct"]), (3, "success", 5))
        self.assertEqual([s["distinct"] for s in r["samples"]], [5, 6, 5])
        # The discarded warm-up and every sample keep their own diagnostics.
        self.assertEqual([len(r["samples"]), len(r["warmups"])], [3, 1])
        self.assertTrue(all(s.get("wall_s") and s.get("cpu_s") is not None for s in r["samples"] + r["warmups"]))
        self.assertIn("COUNT MISMATCH: sample 2: distinct 6, expected 5; generated 12, expected 10", out)
        # The child recorded every invocation: the executable, the full argv, its
        # working directory and the environment the driver promised it (the TLC
        # classpath, and TLX_NATIVE_SYNC for the warm-up alone), and the parser
        # saw each of them exit 0.
        with open(flaky + ".log") as log:
            calls = [json.loads(line) for line in log if "-tlc" in line]
        self.assertEqual(len(calls), 4)  # The discarded warm-up and three measured samples.
        self.assertEqual(calls[0]["argv"][:-2], [flaky, "check", "x.tla", "-config", "x.cfg", "-workers", "1", "-compile", "-tlc"])
        self.assertEqual(calls[0]["argv"][-2], "-stats")
        self.assertTrue(calls[0]["argv"][-1].startswith("json="))
        self.assertEqual([c["native_sync"] for c in calls], ["1", None, None, None])
        self.assertEqual([c["classpath"] for c in calls], [tlxlib.tlx_env(classpath=True)["TLX_CLASSPATH"]] * 4)
        self.assertTrue(all(os.path.realpath(c["cwd"]) == os.path.realpath(os.getcwd()) for c in calls))
        mine = [s for s in h["samples"] if s["entry"].startswith("small:A/one")]
        self.assertEqual([(s["exit"], s["result"]) for s in mine], [(0, "success")] * 4)

    def test_a_run_without_a_completed_sample_cannot_pass(self):
        # HS: zero and partial samples are never a pass. The warm-up times out, so
        # no measured sample is even started: the entry is skipped, its record
        # claims nothing, and the verdict is not PASS.
        def measure(bench, model, entry, exe, instr, **kwargs):
            raise subprocess.TimeoutExpired('fake', 30)
        with patch.object(S, 'measure_once', side_effect=measure) as called:
            rc, out, h = self.run_suite(fake(self.d, 'zero'))
        self.assertEqual(called.call_count, 2)  # one warm-up per model, no measured sample
        self.assertEqual((rc, h['verdict']['outcome']), (2, 'INCONCLUSIVE'), out)
        self.assertTrue(h['verdict']['skipped'])
        for key, r in h['runs'].items():
            with self.subTest(run=key):
                self.assertEqual((r['result'], r['skipped'], r['completed_samples']), ('skipped', 'sample timeout', 0))
                self.assertEqual((r['walls'], r['samples'], r['count_problems']), ([], [], []))
                self.assertEqual([w['result'] for w in r['warmups']], ['timeout'])

    def run_suite(self, new, base=None, slow=(), **kw):
        a = argparse.Namespace(manifest=None, sizes="small", models="", bin=new, base_bin=base or "", base_rev="aaaaaaaaaaaa" if base else "",
                               repeat=3, max_minutes=0, threshold=0.05, max_noise=0.5, min_delta=0.01, no_instructions=True,
                               inject_slow=list(slow), out=os.path.join(self.d, "h.json"))
        for k, v in kw.items():
            setattr(a, k, v)
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = S.run_suite(a, bench=bench, resolve=lambda mid: self.model, man=self.man)
        return rc, buf.getvalue(), read(a.out)

    def test_baseline_pass_and_forced_regression(self):
        new = fake(self.d, "new")
        rc, out, h = self.run_suite(new)
        self.assertEqual((rc, h["verdict"]["outcome"]), (0, "BASELINE"), out)
        self.assertEqual(set(h["runs"]), {"small:A/one:compile:1w", "small:B/two:interp:1w"})
        r = h["runs"]["small:A/one:compile:1w"]
        self.assertEqual((len(r["walls"]), r["distinct"], r["count_problems"], r["tlc_1w_s"]), (3, 5, [], 1.0))
        base = fake(self.d, "base")
        rc, out, h = self.run_suite(new, base)
        self.assertEqual((rc, h["verdict"]["outcome"]), (0, "PASS"), out)
        self.assertEqual(set(h["base"]["runs"]), set(h["runs"]))
        # The forced regression: the new binary's runs of A/one take 3x as long.
        rc, out, h = self.run_suite(new, base, slow=["A/one=3"])
        self.assertEqual((rc, h["verdict"]["outcome"]), (1, "REGRESSION"), out)
        self.assertEqual([r["key"] for r in h["verdict"]["regressions"]], ["small:A/one:compile:1w"])
        self.assertIn("small:A/one:compile:1w", out)
        self.assertNotIn("REGRESSION small:B/two", out)
        # It was retried once, with two more repeats.
        self.assertEqual(h["verdict"]["retried"], ["small:A/one:compile:1w"])
        self.assertEqual(len(h["runs"]["small:A/one:compile:1w"]["walls"]), 5)
        self.assertEqual(set(h["runs"]["small:A/one:compile:1w"]["walls"]), {round(3 * FAKE_WALL_S, 3)})
        self.assertEqual(len(h["runs"]["small:B/two:interp:1w"]["walls"]), 3)

    def test_count_mismatch_fails_even_without_a_base(self):
        for model in self.man['models']:
            for run in model['runs']:
                run['args'] = ['-tlc']
        rc, out, h = self.run_suite(fake(self.d, "wrong", distinct=6))
        self.assertEqual((rc, h["verdict"]["outcome"]), (1, "REGRESSION"), out)
        self.assertEqual(len(h["verdict"]["count_failures"]), 2)
        self.assertIn("COUNT MISMATCH", out)

    def test_default_mode_reduced_counts_are_allowed(self):
        rc, out, history = self.run_suite(fake(self.d, 'reduced', distinct=2))
        self.assertEqual(rc, 0, out)
        self.assertEqual(history['verdict']['count_failures'], [])

    def test_time_budget_skips_and_is_inconclusive(self):
        rc, out, h = self.run_suite(fake(self.d, "new"), max_minutes=-1)
        self.assertEqual((rc, h["verdict"]["outcome"]), (2, "INCONCLUSIVE"), out)
        self.assertEqual(len(h["verdict"]["skipped"]), 2)


class Report(unittest.TestCase):
    def hist(self, commit, date, wall, machine="m1", verdict="PASS"):
        return {"suite": True, "commit": commit, "date": date, "machine": machine, "verdict": {"outcome": verdict, "regressions": [], "count_failures": []},
                "runs": {"small:A/one:compile:1w": rec(walls=(wall, wall, wall), tlc_1w_s=10.0, rss_mib=[100.0, 110.0, 105.0], instructions=[2e9, 2.1e9, 2e9]),
                         "small:A/one:interp:1w": rec(mode="interp", walls=(wall * 5,) * 3)}}

    def test_trend(self):
        hs = [self.hist("aaaaaaaaaaaa", "2026-10-01 10:00:00", 1.0), self.hist("bbbbbbbbbbbb", "2026-10-02 10:00:00", 2.0, verdict="REGRESSION")]
        text = S.trend_markdown(hs)
        self.assertIn("`bbbbbbbbbbbb`", text)
        self.assertIn("| small | A/one | compile | 1 | 2.00 |", text)
        self.assertIn("5.0x", text)           # 10 s of TLC / 2 s
        self.assertIn("2.00x", text)          # against the previous revision
        self.assertIn("2.0", text)            # instructions in G
        self.assertIn("REGRESSION", text)
        self.assertIn("1.00 | 2.00", text)    # the time-over-revisions row
        self.assertIn("geometric mean", text.lower())

    def test_other_machine_is_not_compared(self):
        text = S.trend_markdown([self.hist("a" * 12, "2026-10-01 10:00:00", 1.0, "m1"), self.hist("b" * 12, "2026-10-02 10:00:00", 1.0, "m2")])
        self.assertIn("different machine", text)
        self.assertNotIn("1.00x", text)

    def test_empty(self):
        self.assertIn("No suite run", S.trend_markdown([]))

    def test_load_history_and_previous(self):
        with tempfile.TemporaryDirectory() as d:
            for h in (self.hist("a" * 12, "2026-10-01 10:00:00", 1.0), self.hist("b" * 12, "2026-10-02 10:00:00", 1.0)):
                write(os.path.join(d, h["commit"] + ".json"), json.dumps(h))
            write(os.path.join(d, "other.json"), "{}")     # not a suite history
            write(os.path.join(d, "broken.json"), "{")
            hs = S.load_history(d)
            self.assertEqual([h["commit"][0] for h in hs], ["a", "b"])
            self.assertEqual(S.previous_recorded("c" * 12, hs, lambda c, r: True), "b" * 12)
            self.assertEqual(S.previous_recorded("b" * 12, hs, lambda c, r: True), "a" * 12)
            self.assertIsNone(S.previous_recorded("c" * 12, hs, lambda c, r: False))
            self.assertIsNone(S.previous_recorded("c" * 12, [], lambda c, r: True))


class Track(unittest.TestCase):
    def test_cloud_command(self):
        a = argparse.Namespace(sizes="small,medium", repeat=3, max_minutes=40, setup_minutes=20, models="", inject_slow=["Raft=2"],
                               provider="tencent", instance_type="")
        args = S.remote_args(a, "abc123")
        self.assertIn("--base-bin target/bench-bins/base/tlx --base-rev abc123", args)
        self.assertIn("--inject-slow Raft=2", args)
        cmd = S.cloud_command(a, "def456", "abc123", args)
        self.assertIn("--bench", cmd)
        self.assertEqual(cmd[cmd.index("--bench-bin") + 1], "base=abc123")
        self.assertEqual(cmd[cmd.index("--max-minutes") + 1], "60")      # one launch of at most 60 minutes
        self.assertNotIn("--bench-bin", S.cloud_command(a, "def456", None, S.remote_args(a, None)))
        self.assertNotIn("--base-bin", S.remote_args(a, None))


class TrackReceipt(testkit.GuardedTestCase):
    """HARNESS-06, HARNESS-12: `track` records a run only from the receipt of the
    invocation that produced it - its revision, its external binaries and its exit
    status - and only when the run ended in a suite status. A stale PASS next to
    an infrastructure failure, a receipt of another revision or base, and two
    concurrent result directories each authorize nothing. Every refusal is paired
    with the control that records once the refused (or ambiguous) run is gone."""

    REV, BASE = "a" * 40, "b" * 40

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.results = os.path.join(self.tmp.name, "bench")
        os.makedirs(self.results)
        for name, value in (("BENCH_RESULTS", self.results), ("HISTORY", os.path.join(self.tmp.name, "history"))):
            p = patch.object(S, name, value)
            p.start()
            self.addCleanup(p.stop)
        for target in ("ingest", "generate"):
            p = patch.object(S.bench_records if hasattr(S, "bench_records") else br, target)
            p.start()
            self.addCleanup(p.stop)

    def receipt(self, rev=REV, exit_code=0, bins=(), **over):
        r = {"provider": "tencent", "rev": rev, "verify_exit": exit_code, "verify_env": {}, "arch": "arm64",
             "fetched_at": "2026-10-08T00:00:00Z", "phases_s": {}, "bench": ["suite --sizes small"],
             "bench_bins": [{"name": n, "rev": b, "features": ""} for n, b, _ in bins]}
        r.update(over)
        return r

    def suite_history(self, rev=REV, base=BASE, outcome="PASS"):
        return {"suite": True, "commit": rev, "date": "2026-10-08 10:00:00", "machine": "test machine",
                "base": {"commit": base} if base else {},
                "runs": [{"key": "M#compile", "min": 1.0, "walls": [1.0]}],
                "verdict": {"outcome": outcome, "count_failures": [], "regressions": [], "inconclusive": [], "skipped": []}}

    def result_dir(self, name, receipt, history=None):
        d = os.path.join(self.results, name)
        os.makedirs(d)
        with open(os.path.join(d, "cloud.json"), "w") as f:
            json.dump(receipt, f)
        if history is not None:
            hd = os.path.join(d, "bench", "history")
            os.makedirs(hd)
            with open(os.path.join(hd, "history.json"), "w") as f:
                json.dump(history, f)
        return d

    def invoke(self, rc, base=None):
        a = argparse.Namespace(rev="HEAD", base=self.BASE if base is None else base, sizes="small", models="",
                               repeat=3, max_minutes=40, setup_minutes=20, provider="tencent", instance_type="",
                               inject_slow=[], dry_run=False)

        def fake_git(*args, **kw):
            ref = args[-1]
            return self.BASE if ref == self.BASE else self.REV

        with patch.object(S, "git", side_effect=fake_git), \
             patch.object(S.subprocess, "run", return_value=Mock(returncode=rc)), \
             contextlib.redirect_stdout(io.StringIO()) as out, contextlib.redirect_stderr(io.StringIO()) as err:
            code = S.cmd_track(a)
        return code, out.getvalue() + err.getvalue()

    def recorded(self):
        return sorted(os.listdir(S.HISTORY)) if os.path.isdir(S.HISTORY) else []

    def clear(self):
        """A clean slate for the control of a pairing: two result directories that
        both authorize one invocation are refused, so the control that must
        record runs against an empty results root."""
        for name in os.listdir(self.results):
            shutil.rmtree(os.path.join(self.results, name))
        if os.path.isdir(S.HISTORY):
            shutil.rmtree(S.HISTORY)

    def test_a_fresh_pass_and_regression_are_recorded(self):
        self.result_dir("run-pass", self.receipt(bins=[("base", self.BASE, "")]),
                        self.suite_history(outcome="PASS"))
        code, _ = self.invoke(0)
        self.assertEqual((code, self.recorded()), (0, ["history.json"]))
        # The control's sibling: a REGRESSION is a real verdict, not a failure.
        self.result_dir("run-reg", self.receipt(exit_code=1, bins=[("base", self.BASE, "")]),
                        self.suite_history(outcome="REGRESSION"))
        code, _ = self.invoke(1)
        self.assertEqual(code, 1)

    def test_an_infrastructure_exit_is_refused_despite_a_stale_pass(self):
        # A PASS of an earlier run of the same revision sits next to a run that
        # exited with an infrastructure code: the exit status decides, so the
        # stale PASS is not adopted (the pre-fix code read only the file).
        self.result_dir("run-old", self.receipt(bins=[("base", self.BASE, "")]), self.suite_history())
        for rc in (cloud_common.INFRA_FAIL, 20, 23, cloud_common.DEADLINE_RC):
            with self.subTest(exit=rc):
                self.result_dir(f"run-{rc}", self.receipt(exit_code=rc, bins=[("base", self.BASE, "")]),
                                self.suite_history())
                code, message = self.invoke(rc)
                self.assertEqual(code, 3)
                self.assertEqual(self.recorded(), [])                 # nothing copied
                self.assertIn(str(rc), message)                       # the exit is named
        # Control: the same setup with a suite status records.
        self.clear()
        self.result_dir("run-good", self.receipt(bins=[("base", self.BASE, "")]), self.suite_history())
        self.assertEqual(self.invoke(0)[0], 0)

    def test_a_receipt_of_another_revision_or_exit_is_refused(self):
        self.result_dir("run-other", self.receipt(rev="c" * 40, bins=[("base", self.BASE, "")]),
                        self.suite_history(rev="c" * 40))
        self.assertEqual(self.invoke(0)[0], 3)                        # another revision
        self.assertEqual(self.recorded(), [])                         # and nothing was copied
        self.clear()
        self.result_dir("run-mismatch", self.receipt(exit_code=1, bins=[("base", self.BASE, "")]), self.suite_history())
        self.assertEqual(self.invoke(0)[0], 3)                        # receipt states a different exit
        self.clear()
        self.result_dir("run-wrong-bin", self.receipt(bins=[("base", "e" * 40, "")]), self.suite_history())
        self.assertEqual(self.invoke(0)[0], 3)                        # receipt built another base binary
        self.clear()
        # Control: the receipt that matches this invocation records.
        self.result_dir("run-ok", self.receipt(bins=[("base", self.BASE, "")]), self.suite_history())
        self.assertEqual(self.invoke(0)[0], 0)

    def test_a_history_of_another_base_is_refused(self):
        self.result_dir("run-wrong-base", self.receipt(bins=[("base", self.BASE, "")]),
                        self.suite_history(base="d" * 40))
        self.assertEqual(self.invoke(0)[0], 3)
        self.assertEqual(self.recorded(), [])
        # Control: the same directory with the requested base records.
        self.clear()
        self.result_dir("run-right-base", self.receipt(bins=[("base", self.BASE, "")]), self.suite_history())
        self.assertEqual(self.invoke(0)[0], 0)

    def test_a_baseline_run_records_without_a_base_binary(self):
        # `--base none`: the run pins no external binary, and its receipt must
        # say so; a receipt that pinned one would authorize a comparison this
        # invocation never asked for.
        self.result_dir("run-baseline", self.receipt(bins=[]), self.suite_history(base=None))
        self.assertEqual(self.invoke(0, base="none")[0], 0)
        self.assertEqual(self.recorded(), ["history.json"])
        self.clear()
        self.result_dir("run-extra-bin", self.receipt(bins=[("base", self.BASE, "")]), self.suite_history(base=None))
        self.assertEqual(self.invoke(0, base="none")[0], 3)

    def test_two_receipts_for_one_invocation_are_refused(self):
        for name in ("run-a", "run-b"):
            self.result_dir(name, self.receipt(bins=[("base", self.BASE, "")]), self.suite_history())
        code, message = self.invoke(0)
        self.assertEqual(code, 3)
        self.assertEqual(self.recorded(), [])
        self.assertIn("more than one", message)


class CommitRangePrivacy(unittest.TestCase):
    def test_range_keeps_revision_without_private_commit_subject(self):
        with tempfile.TemporaryDirectory() as directory:
            def git(*args, **kwargs):
                return subprocess.check_output(['git', '-C', directory, '-c', 'user.name=Test',
                                                '-c', 'user.email=test@example.com', *args],
                                               text=True, stderr=subprocess.DEVNULL).strip()
            git('init', '-q')
            git('commit', '--allow-empty', '-qm', 'Baseline')
            base = git('rev-parse', 'HEAD')
            git('commit', '--allow-empty', '-qm', 'Merge ' + 'TST' + '-12: private backlog title')
            head = git('rev-parse', '--short', 'HEAD')
            with patch.object(S, 'git', side_effect=git):
                self.assertEqual(S.commit_range(base, 'HEAD'), [head])


class RunBench(unittest.TestCase):
    """bench.py's own `run` driver with a scripted tlx: every sample of a run is
    validated against its mode contract and kept, and a mismatch of an earlier
    sample is not erased by the last one. `modes="tlc"` puts `-tlc` in the
    arguments, which puts the counts of every sample in the contract (without it
    the search is reduced and only the result is checked)."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.model = {"id": "A", "tla": "x.tla", "cfg": "x.cfg", "flags": [], "tier": "small",
                      "tlc": {"result": "success", "distinct": 5}}
        self.out = os.path.join(self.tmp.name, "bench.json")

    def tearDown(self):
        self.tmp.cleanup()

    def sample(self, distinct=5, result="success", **over):
        return {"result": result, "distinct": distinct, "generated": distinct * 2, "depth": 3,
                "wall_s": 1.0, "cpu_s": 1.0, "maxrss_mib": 8.0, **over}

    def run_bench(self, samples, modes="tlc", *, tlc=False):
        a = argparse.Namespace(external=None, models="A", tiers="", per_tier=0, modes=modes, workers="", tlc=tlc,
                               tlc_workers="", tlc_timeout=0, timeout=30, repeat=len(samples), resume=False, stats=False, out=self.out)
        made = []

        def fake(m, args, timeout, exe=None, env=None):
            # bench.tlx is wrapped by bench_budget.model_pass, which marks a run
            # TLC-compatible exactly when -tlc is among its arguments.
            made.append(args)
            return {**samples[len(made) - 1], "compatibility": "-tlc" in args}

        with contextlib.ExitStack() as stack:
            stack.enter_context(patch.object(bench_models, "oracle", return_value={"A": self.model}))
            stack.enter_context(patch.object(bench, "tlx", side_effect=fake))
            if tlc:
                # The cache-miss collector's record; test_bench_measurement owns
                # that each fresh collection really measures the child's RSS.
                stack.enter_context(patch.object(bench, "tlc", return_value={
                    "wall_s": 1.0, "cpu_s": 1.0, "maxrss_mib": 8.0, "result": "success",
                    "distinct": 5, "generated": 10, "depth": 3}))
            output = stack.enter_context(contextlib.redirect_stdout(io.StringIO()))
            bench.run_bench(a, "/fake/tlx")
        runs = read(self.out)["runs"]
        if tlc:
            return runs, output.getvalue(), made
        key, = runs  # `--models` selects the "custom" tier.
        self.assertEqual(key, f"custom:A:{modes}:1w")
        return runs[key], output.getvalue(), made

    def test_stats_child_uses_the_live_isolated_cache(self):
        exe = os.path.join(self.tmp.name, 'fake-tlx')
        log = os.path.join(self.tmp.name, 'children.jsonl')
        inherited = os.path.join(self.tmp.name, 'inherited')
        os.mkdir(inherited)
        write(exe, "#!/usr/bin/env python3\n" + """
import json, os, sys
cache = os.environ['TLX_CACHE']
assert os.path.isdir(cache)
marker = os.path.join(cache, 'marker')
seen = os.path.exists(marker)
with open(marker, 'w') as f:
    f.write('built')
record = dict(argv=sys.argv, cache=cache, seen=seen, sync=os.environ.get('TLX_NATIVE_SYNC'))
with open(os.environ['CHILD_LOG'], 'a') as f:
    f.write(json.dumps(record) + '\\n')
for arg in sys.argv:
    if arg.startswith('json='):
        with open(arg[5:], 'w') as f:
            json.dump(record, f)
print('Model checking completed. No error has been found.')
print('10 states generated, 5 distinct states found, 0 states left on queue.')
""")
        os.chmod(exe, 0o755)
        a = argparse.Namespace(external=None, models='A', tiers='', per_tier=0, modes='compile', workers='1',
                               tlc=False, tlc_workers='', tlc_timeout=0, timeout=10, repeat=2,
                               resume=False, stats=True, isolate_cache=True, out=self.out)
        with patch.object(bench_models, 'oracle', return_value={'A': self.model}), \
             patch.dict(os.environ, {'TLX_CACHE': inherited, 'CHILD_LOG': log}), \
             contextlib.redirect_stdout(io.StringIO()):
            bench.run_bench(a, exe)
        with open(log) as f:
            children = [json.loads(line) for line in f]
        self.assertEqual(len(children), 3)
        self.assertEqual(len({c['cache'] for c in children}), 1)
        self.assertEqual([c['seen'] for c in children], [False, True, True])
        self.assertTrue(all(c['sync'] == '1' for c in children))
        self.assertIn('-stats', children[-1]['argv'])
        self.assertFalse(os.path.exists(children[0]['cache']))
        self.assertEqual(os.listdir(inherited), [])
        row = next(iter(read(self.out)['runs'].values()))
        self.assertEqual(row['stats']['cache'], children[0]['cache'])
        self.assertEqual(row['cache']['mode'], 'fresh-per-model')

    def test_every_sample_is_validated_and_an_earlier_mismatch_is_kept(self):
        # HARNESS-07: sample 2 disagrees and is not erased by sample 3.
        r, out, made = self.run_bench([self.sample(), self.sample(distinct=6), self.sample()])
        self.assertEqual([a[:3] for a in made], [["-workers", "1", "-tlc"]] * 3)
        self.assertEqual([s["distinct"] for s in r["samples"]], [5, 6, 5])
        self.assertEqual(r["count_problems"], ["sample 2: result or distinct differs from TLC"])
        self.assertEqual((r["result"], r["distinct"]), ("success", 5))  # The aggregate is the last sample's.
        self.assertIn("(result or distinct differs from TLC)", out)

    def test_a_wrong_last_sample_is_reported_as_before(self):
        r, out, _ = self.run_bench([self.sample(), self.sample(result="deadlock", distinct=3)])
        self.assertEqual(r["count_problems"], ["result or distinct differs from TLC"])
        self.assertEqual([s["result"] for s in r["samples"]], ["success", "deadlock"])
        self.assertIn("(result or distinct differs from TLC)", out)

    def test_agreeing_samples_report_nothing(self):
        r, out, _ = self.run_bench([self.sample(), self.sample()])
        self.assertNotIn("count_problems", r)
        self.assertNotIn("differs from TLC", out)

    def test_each_sample_keeps_its_peak_rss(self):
        # history-report pairs this list with TLC's, so every sample's peak RSS
        # has to reach the history file, not only the aggregate counts.
        r, _, _ = self.run_bench([self.sample(), self.sample(maxrss_mib=10.0)])
        self.assertEqual(r["rss_mib"], [8.0, 10.0])

    def test_a_tlc_run_keeps_its_peak_rss_in_the_history_row(self):
        # A fresh `run --tlc` collection is only usable as a memory baseline if
        # the collector's peak RSS survives the history serialization.
        runs, _, _ = self.run_bench([self.sample()], modes="compile", tlc=True)
        self.assertEqual(runs["custom:A:tlc:1w"]["rss_mib"], [8.0])

    def test_a_reduced_default_run_checks_its_result_only(self):
        # The positive case: without -tlc the search is reduced, so differing
        # counts are not a problem — a differing verdict still is.
        r, out, made = self.run_bench([self.sample(distinct=2), self.sample(distinct=9), self.sample(distinct=3)], modes="compile")
        self.assertEqual(made[0], ["-workers", "1", "-compile"])
        self.assertNotIn("count_problems", r)
        self.assertNotIn("differs from TLC", out)
        r, out, _ = self.run_bench([self.sample(result="deadlock", distinct=2), self.sample()], modes="compile")
        self.assertEqual(r["count_problems"], ["sample 1: result or distinct differs from TLC"])
        self.assertEqual(r["result"], "success")  # The aggregate is still the last sample's.




class NativeCoverage(unittest.TestCase):
    def test_record_keeps_discarded_warmup_metric_separate_from_timing_samples(self):
        e = S.entries(man())[0]
        sample = {'result': 'success', 'wall_s': 1, 'distinct': 5, 'generated': 10, 'depth': 3}
        r = S.record_of(e, [sample], [0, 0], warmups=[{**sample, 'native_coverage': {'native_share': .75, 'host_time_share': .2}}])
        self.assertEqual(r['native_coverage']['native_share'], .75)
        self.assertEqual(r['walls'], [1])

    def test_warmup_reads_real_stats_and_owns_its_temporary_directory(self):
        import tempdirs
        from types import SimpleNamespace
        directories = []
        def run(model, args, timeout, **kwargs):
            path = args[args.index('-stats') + 1].removeprefix('json=')
            directory = os.path.dirname(path)
            directories.append(directory)
            self.assertEqual(tempdirs.owner(directory)['root'], os.path.realpath(S.ROOT))
            with open(path, 'w') as f:
                json.dump({'actions': [{'calls': {'native': 3}, 'fully_native': 3}]}, f)
            return {'result': 'success', 'wall_s': .1}
        fake = SimpleNamespace(mode_args=lambda *a, **kw: [], tlx=run)
        entry = {'mode': 'compile', 'workers': 1, 'timeout_s': 5}
        result = S.measure_once(fake, {}, entry, '/usr/bin/true', False, collect_native=True)
        self.assertEqual(result['native_coverage']['native_share'], 1)
        self.assertEqual(result['native_coverage']['evaluations'], 3)
        self.assertNotIn('regions', result['native_coverage'])
        self.assertNotIn('by_kind', result['native_coverage'])
        self.assertFalse(os.path.exists(directories[0]))

    def test_native_share_drop_is_regression_even_with_equal_timings(self):
        a = {'k': rec(native_coverage={'native_share': .9})}
        b = {'k': rec(native_coverage={'native_share': .8})}
        v = S.judge(a, b, [], [], bench.compare_runs)
        self.assertEqual(v['outcome'], 'REGRESSION')
        self.assertEqual(v['regressions'][0]['metric'], 'native_share')

    def test_missing_new_counter_is_inconclusive_not_a_pass(self):
        a = {'k': rec(native_coverage={'native_share': .9})}
        b = {'k': rec()}
        self.assertEqual(S.judge(a, b, [], [], bench.compare_runs)['outcome'], 'INCONCLUSIVE')


class SuiteCheck(unittest.TestCase):
    def test_batch_resolution_preserves_precedence_and_staging_mode(self):
        import corpus
        ids = ["cached", "scaled", "example", "missing"]
        for stage in (False, True):
            with self.subTest(stage=stage), \
                 patch.object(bench_models, "oracle", return_value={"cached": {"from": "oracle"}}) as oracle, \
                 patch.object(bench_models, "SCALE_CFGS", {"cached": "a", "scaled": "b"}), \
                 patch.object(bench_models, "scale_models", return_value={"scaled": {"from": "scale"}}) as scale, \
                 patch.object(corpus, "models", return_value=[{"id": mid} for mid in ids[:-1]]) as examples, \
                 patch.object(bench_models, "declared_run_fields", return_value={"tlc_args": ["-seed", "1"]}):
                resolved = S.resolve_models(ids, stage=stage)
                self.assertEqual(resolved, {
                    "cached": {"from": "oracle"},
                    "scaled": {"from": "scale"},
                    "example": {"id": "example", "tlc_args": ["-seed", "1"], "tlc": {}},
                })
                oracle.assert_called_once_with(ids, stage=stage)
                scale.assert_called_once_with(["scaled"])
                examples.assert_called_once_with(float("inf"), include_invalid=True)

    def test_suite_check_succeeds_without_third_party_external_or_examples(self):
        import corpus
        with tempfile.TemporaryDirectory() as tmp:
            absent_tp = os.path.join(tmp, "third_party")
            absent_ext = os.path.join(absent_tp, "external")
            absent_ex = os.path.join(absent_tp, "Examples")
            buf = io.StringIO()
            with patch.object(bench_models, "TP", absent_tp), \
                 patch.object(bench_models, "load_oracle", side_effect=lambda *a, **kw: {}), \
                 patch.object(corpus, "EXTERNAL", absent_ext), \
                 patch.object(corpus, "EX", absent_ex), \
                 contextlib.redirect_stdout(buf):
                rc = S.run_check(argparse.Namespace(manifest=S.SUITE, oracle=False))
            self.assertEqual(rc, 0, buf.getvalue())
            self.assertIn("models,", buf.getvalue())
            self.assertIn("runs", buf.getvalue())

    def test_suite_check_still_rejects_unknown_external_model_without_third_party(self):
        import corpus
        with tempfile.TemporaryDirectory() as tmp:
            absent_tp = os.path.join(tmp, "third_party")
            manifest = os.path.join(tmp, "suite.json")
            write(manifest, json.dumps({
                "version": 1,
                "models": [{
                    "id": "ext/nonexistent/Model",
                    "size": "small",
                    "timeout_s": 60,
                    "runs": [{"mode": "compile", "workers": 1}],
                    "expect": {"source": "unpinned"},
                }],
            }))
            buf = io.StringIO()
            with patch.object(bench_models, "TP", absent_tp), \
                 patch.object(bench_models, "load_oracle", return_value={}), \
                 patch.object(corpus, "EXTERNAL", os.path.join(absent_tp, "external")), \
                 patch.object(corpus, "EX", os.path.join(absent_tp, "Examples")), \
                 contextlib.redirect_stdout(buf):
                rc = S.run_check(argparse.Namespace(manifest=manifest, oracle=False))
            self.assertEqual(rc, 1)
            self.assertIn("ext/nonexistent/Model", buf.getvalue())

    def test_stress_models_handles_absent_external_sources_without_staging(self):
        import corpus
        with tempfile.TemporaryDirectory() as tmp:
            absent_tp = os.path.join(tmp, "third_party")
            with patch.object(bench_models, "TP", absent_tp), \
                 patch.object(corpus, "EXTERNAL", os.path.join(absent_tp, "external")), \
                 patch.object(corpus, "EX", os.path.join(absent_tp, "Examples")):
                resolved = bench_models.stress_models(["bench/ReprZab", "bench/FlexibleRaftReduced5", "bench/ReprPaxosCommit"], stage=False)
            self.assertEqual(set(resolved), {"bench/ReprZab", "bench/FlexibleRaftReduced5", "bench/ReprPaxosCommit"})
            self.assertTrue(resolved["bench/ReprZab"]["tla"].endswith("/target/bench-models/ReprZab/ReprZab.tla"))
            self.assertTrue(resolved["bench/ReprZab"]["cfg"].endswith("/bench/repr-configs/Zab.cfg"))
            self.assertTrue(resolved["bench/FlexibleRaftReduced5"]["tla"].endswith("/target/bench-models/FlexibleRaftReduced5/FlexibleRaftReduced5.tla"))

    def test_stress_models_stage_true_refuses_missing_upstream_even_with_stale_stage(self):
        import corpus
        with tempfile.TemporaryDirectory() as tmp:
            tmp_root = os.path.join(tmp, "root")
            os.makedirs(tmp_root)
            os.symlink(os.path.join(S.ROOT, "bench"), os.path.join(tmp_root, "bench"))
            tmp_tp = os.path.join(tmp, "third_party")
            tmp_ext = os.path.join(tmp_tp, "external")
            cases = [
                ("bench/FlexibleRaftReduced5", os.path.join(tmp_ext, "vanlightly-raft", "flexible-raft", "FlexibleRaft.tla")),
                ("bench/ReprZab", os.path.join(tmp_ext, "alpha-zk", "MC_tlx_Zab_new.tla")),
            ]
            with patch.object(bench_models, "ROOT", tmp_root), \
                 patch.object(bench_models, "TP", tmp_tp), \
                 patch.object(corpus, "EXTERNAL", tmp_ext), \
                 patch.object(corpus, "EX", os.path.join(tmp_tp, "Examples")):
                for mid, upstream in cases:
                    with self.subTest(model=mid):
                        os.makedirs(os.path.dirname(upstream), exist_ok=True)
                        write(upstream, "---- MODULE Stub ----\n====\n")
                        staged = bench_models.stress_models([mid], stage=True)
                        self.assertTrue(os.path.isfile(staged[mid]["tla"]))
                        os.remove(upstream)
                        self.assertTrue(os.path.isfile(staged[mid]["tla"]))
                        with self.assertRaisesRegex(SystemExit, "missing upstream source"):
                            bench_models.stress_models([mid], stage=True)
                        meta = bench_models.stress_models([mid], stage=False)
                        self.assertEqual(meta[mid]["tla"], staged[mid]["tla"])

    def _checkout_fixture(self, tmp):
        root = os.path.join(tmp, "repo")
        os.makedirs(root)
        shutil.copytree(os.path.join(S.ROOT, "scripts"), os.path.join(root, "scripts"),
                        ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
        shutil.copytree(os.path.join(S.ROOT, "bench"), os.path.join(root, "bench"))
        os.makedirs(os.path.join(root, "corpus"))
        shutil.copyfile(os.path.join(S.ROOT, "corpus", "external.json"),
                        os.path.join(root, "corpus", "external.json"))
        return root

    def _generated_examples_fixture(self, root):
        spec_dir = os.path.join(root, "third_party", "Examples", "specifications", "KnuthYao")
        os.makedirs(spec_dir)
        write(os.path.join(spec_dir, "SimKnuthYao.tla"), "---- MODULE SimKnuthYao ----\n====\n")
        write(os.path.join(spec_dir, "SimKnuthYao.cfg"), "INIT Init\nNEXT Next\n")
        write(os.path.join(spec_dir, "manifest.json"), json.dumps({
            "modules": [{
                "path": "specifications/KnuthYao/SimKnuthYao.tla",
                "models": [{
                    "path": "specifications/KnuthYao/SimKnuthYao.cfg",
                    "mode": "generate",
                    "runtime": "unknown",
                }],
            }]
        }))
        manifest = os.path.join(root, "bench", "gen-suite.json")
        write(manifest, json.dumps({
            "version": 1,
            "models": [{
                "id": "KnuthYao/SimKnuthYao",
                "size": "small",
                "timeout_s": 60,
                "runs": [{"mode": "compile", "workers": 1}],
                "expect": {"source": "unpinned"},
            }],
        }))
        return manifest

    def _run_suite_check_cli(self, root, *extra_args):
        env = {k: v for k, v in os.environ.items() if k != "PYTHONPATH"}
        return subprocess.run(
            [sys.executable, "scripts/bench.py", "suite-check", *extra_args],
            cwd=root, env=env, capture_output=True, text=True, timeout=30,
        )

    def test_suite_check_cli_fails_when_tracked_flexible_raft_stress_input_is_missing(self):
        for name in ("FlexibleRaftReduced5.cfg", "FlexibleRaftReduced5.tla"):
            with self.subTest(missing=name), tempfile.TemporaryDirectory() as tmp:
                root = self._checkout_fixture(tmp)
                os.remove(os.path.join(root, "bench", "stress", name))
                result = self._run_suite_check_cli(root)
                output = result.stdout + result.stderr
                self.assertNotEqual(result.returncode, 0, output)
                self.assertIn("FlexibleRaftReduced5", output)
                self.assertIn(name, output)
                self.assertNotIn("Traceback", output)

    def test_suite_check_cli_succeeds_with_partial_oracle_when_examples_absent(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self._checkout_fixture(tmp)
            out_dir = os.path.join(root, "corpus", "out")
            os.makedirs(out_dir)
            write(os.path.join(out_dir, "tlc.json"), json.dumps({
                "transaction_commit/PaxosCommit": {
                    "id": "transaction_commit/PaxosCommit",
                    "tla": "third_party/Examples/specifications/transaction_commit/PaxosCommit.tla",
                    "cfg": "third_party/Examples/specifications/transaction_commit/PaxosCommit.cfg",
                    "tlc": {"result": "success", "distinct": 1321761, "generated": 16959159, "depth": 28},
                }
            }))
            result = self._run_suite_check_cli(root)
            output = result.stdout + result.stderr
            self.assertEqual(result.returncode, 0, output)
            self.assertIn(os.path.join(root, "bench", "suite.json"), output)
            self.assertIn("models,", output)
            self.assertIn("runs", output)

    def test_suite_check_cli_rejects_deleted_external_model_even_if_cached_in_oracle(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self._checkout_fixture(tmp)
            manifest = os.path.join(root, "bench", "retired-suite.json")
            write(manifest, json.dumps({
                "version": 1,
                "models": [{
                    "id": "ext/retired/Model",
                    "size": "small",
                    "timeout_s": 60,
                    "runs": [{"mode": "compile", "workers": 1}],
                    "expect": {"source": "unpinned"},
                }],
            }))
            out_dir = os.path.join(root, "corpus", "out")
            os.makedirs(out_dir)
            write(os.path.join(out_dir, "tlc-ext.json"), json.dumps({
                "ext/retired/Model": {
                    "id": "ext/retired/Model",
                    "tla": "third_party/external/retired/Model.tla",
                    "cfg": "third_party/external/retired/Model.cfg",
                    "tlc": {"result": "success", "distinct": 10, "generated": 20, "depth": 2},
                }
            }))
            result = self._run_suite_check_cli(root, "--manifest", manifest)
            output = result.stdout + result.stderr
            self.assertEqual(result.returncode, 1, output)
            self.assertIn("ext/retired/Model", output)

    def test_suite_check_resolves_invalid_upstream_entries_without_oracle(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self._checkout_fixture(tmp)
            ids = {"ewd998/EWD998ChanID_export", "ewd998/EWD998ChanID_shiviz"}
            spec_dir = os.path.join(root, "third_party", "Examples", "specifications", "ewd998")
            os.makedirs(spec_dir)
            write(os.path.join(spec_dir, "manifest.json"), json.dumps({
                "modules": [{
                    "path": "specifications/ewd998/EWD998ChanID.tla",
                    "models": [{"path": f"specifications/{mid}.cfg",
                                "mode": "exhaustive search", "runtime": "00:00:01"}
                               for mid in sorted(ids)],
                }],
            }))
            # Use the actual tracked entries, including their frozen expectations.
            manifest = os.path.join(root, "bench", "suite.json")
            with open(manifest) as source:
                man = json.load(source)
            man["models"] = [m for m in man["models"] if m["id"] in ids]
            self.assertEqual({m["id"] for m in man["models"]}, ids)
            write(manifest, json.dumps(man))
            self.assertFalse(os.path.exists(os.path.join(root, "corpus", "out")))
            result = self._run_suite_check_cli(root)
            output = result.stdout + result.stderr
            self.assertEqual(result.returncode, 0, output)
            self.assertIn("2 models,", output)
            self.assertNotIn("corpus resolution skipped", output)

    def test_suite_check_cli_accepts_generated_examples_model_without_oracle(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self._checkout_fixture(tmp)
            manifest = self._generated_examples_fixture(root)
            result = self._run_suite_check_cli(root, "--manifest", manifest)
            output = result.stdout + result.stderr
            self.assertEqual(result.returncode, 0, output)
            self.assertIn("1 models, 1 runs", output)
            # Scaling resolver still enforces its exhaustive-only restriction.
            import corpus
            with patch.object(corpus, "EX", os.path.join(root, "third_party", "Examples")), \
                 self.assertRaisesRegex(SystemExit, "unknown scaling model"):
                bench_models.scale_models(["KnuthYao/SimKnuthYao"])

    def test_suite_cli_executes_generated_examples_model_with_generate_flag(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = self._checkout_fixture(tmp)
            manifest = self._generated_examples_fixture(root)
            log_path = os.path.join(tmp, "argv.log")
            fake_bin = os.path.join(tmp, "fake-tlx")
            write(fake_bin, f"""#!/usr/bin/env python3
import json, sys
with open({log_path!r}, "a") as f:
    f.write(json.dumps(sys.argv) + "\\n")
print("Model checking completed. No error has been found.")
print("10 states generated, 5 distinct states found, 0 states left on queue.")
print("The depth of the complete state graph search is 3.")
""")
            os.chmod(fake_bin, os.stat(fake_bin).st_mode | stat.S_IEXEC)
            out_path = os.path.join(tmp, "history.json")
            env = {k: v for k, v in os.environ.items() if k != "PYTHONPATH"}
            result = subprocess.run(
                [sys.executable, "scripts/bench.py", "suite",
                 "--manifest", manifest, "--sizes", "small",
                 "--models", "KnuthYao/SimKnuthYao", "--bin", fake_bin,
                 "--repeat", "1", "--no-instructions", "--out", out_path],
                cwd=root, env=env, capture_output=True, text=True, timeout=30,
            )
            output = result.stdout + result.stderr
            self.assertEqual(result.returncode, 0, output)
            with open(log_path) as f:
                calls = [json.loads(line) for line in f]
            self.assertTrue(calls, "expected fake checker to be invoked")
            for argv in calls:
                self.assertIn("-generate", argv)
                self.assertIn("-seed", argv)


if __name__ == "__main__":
    unittest.main()
