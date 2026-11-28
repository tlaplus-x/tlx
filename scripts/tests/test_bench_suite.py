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

    def test_companion_entries_pair_each_default_run_with_its_tlc_twin(self):
        # (The companion is scheduled from the manifest, not from a run result:
        # one `default` run may reduce its search or not, and the twin is what
        # makes either timing comparable with TLC's own run on the same machine.)
        m = {"version": 1, "models": [
            {"id": "T/pinned", "size": "small", "timeout_s": 60,
             "runs": [{"mode": "default", "workers": 1},
                      {"mode": "default", "workers": 4, "args": ["-maxmem", "512"], "env": {"TLX_MIXED_ADAPT": "0"}}],
             "expect": {"result": "success", "source": "tlx-pinned", "distinct": 2}},
            {"id": "O/oracle", "size": "small", "timeout_s": 60,
             "runs": [{"mode": "default", "workers": 1}, {"mode": "tlc", "workers": 1},
                      {"mode": "default", "workers": 2, "args": ["-tlc"]}],
             "expect": {"result": "success", "source": "tlc-oracle", "distinct": 5}}]}
        self.assertEqual([e["mode"] for e in S.entries(m, "small")],
                         ["default", "default", "default", "tlc", "default"])
        es = S.entries(m, "small", with_tlc_companion=True)
        self.assertEqual([e["mode"] for e in es],
                         ["default", "tlc", "default", "tlc", "default", "tlc", "default"])
        self.assertEqual([e["model"] for e in es], ["T/pinned"] * 4 + ["O/oracle"] * 3)
        for i in (0, 2):
            self.assertEqual(es[i]["key"].replace(":default:", ":tlc:", 1), es[i + 1]["key"])
            self.assertEqual({k: es[i][k] for k in ("workers", "args", "cgroup_mib", "env", "timeout_s")},
                             {k: es[i + 1][k] for k in ("workers", "args", "cgroup_mib", "env", "timeout_s")})
        # A pin taken from a reduced run cannot be the unreduced twin's contract;
        # a pin taken from TLC applies unchanged (here: the explicit `tlc` run,
        # which therefore needed no companion).
        self.assertEqual(es[1]["expect"], {"result": "success", "source": "unpinned"})
        self.assertEqual(es[3]["expect"], {"result": "success", "source": "unpinned"})
        self.assertEqual(es[5]["expect"], {"result": "success", "source": "tlc-oracle", "distinct": 5})
        # A default run that already asks for `-tlc` gets no second twin.
        self.assertFalse(any(e["mode"] == "tlc" and "-tlc" in e["args"] for e in es))
        self.assertEqual(S.companion_expect({"result": "deadlock", "source": "tlc-bench"}),
                         {"result": "deadlock", "source": "tlc-bench"})

    def test_with_companions_deduplicates_compile_tlc_entries(self):
        m = {"version": 1, "models": [
            {"id": "M/covered", "size": "medium", "timeout_s": 60,
             "runs": [{"mode": "compile", "workers": 1, "args": ["-tlc"]},
                      {"mode": "compile", "workers": 16, "args": ["-tlc"]},
                      {"mode": "default", "workers": 1},
                      {"mode": "default", "workers": 16}],
             "expect": {"result": "success", "source": "tlc-oracle", "distinct": 5}},
            {"id": "M/uncovered", "size": "medium", "timeout_s": 60,
             "runs": [{"mode": "compile", "workers": 1},  # no -tlc: does not cover twin
                      {"mode": "compile", "workers": 1, "args": ["-tlc", "-maxmem", "512"]},  # different args
                      {"mode": "default", "workers": 1}],
             "expect": {"result": "success", "source": "tlc-oracle", "distinct": 5}},
        ]}
        es = S.entries(m, "medium", with_tlc_companion=True)
        covered = [e for e in es if e["model"] == "M/covered"]
        self.assertEqual([(e["mode"], e["workers"], e["args"]) for e in covered],
                         [("compile", 1, ["-tlc"]), ("compile", 16, ["-tlc"]),
                          ("default", 1, []), ("default", 16, [])])
        uncovered = [e for e in es if e["model"] == "M/uncovered"]
        self.assertEqual([(e["mode"], e["workers"], e["args"]) for e in uncovered],
                         [("compile", 1, []), ("compile", 1, ["-tlc", "-maxmem", "512"]),
                          ("default", 1, []), ("tlc", 1, [])])

    def test_manifest_flagship_external_models_have_1w_16w_and_tlc_compile(self):
        manifest = S.load_manifest()
        self.assertEqual(S.validate_manifest(manifest), [])
        by_id = {m["id"]: m for m in manifest["models"]}
        flagship = (
            "ext/etcd-raft/MCetcdraft_3s_t2",
            "ext/etcd-raft/MCetcdraft_4s_t3_reconfig",
            "ext/zookeeper/FastLeaderElection_medium",
            "ext/alpha-zk/MC_tlx_Zab_new",
            "ext/mongo/MCRaftMongo",
            "ext/mongo/MCMongoReplReconfig",
            "ext/logless-reconfig/MCMongoRaftReconfig",
            "ext/cassandra/Accord_baseline__deep_chain",
            "ext/cassandra/Accord_baseline__deep_chain_live",
            "ext/elastic/consensus",
            "ext/vanlightly-kafka/kraft_kip_853_small",
            "ext/pingcap/DistributedTransaction_Test1",
        )
        for mid in flagship:
            with self.subTest(model=mid):
                runs = by_id[mid]["runs"]
                for w in (1, 16):
                    self.assertTrue(any(r["mode"] == "compile" and r["workers"] == w and "-tlc" in (r.get("args") or [])
                                        for r in runs), f"{mid} missing compile -tlc {w}w")
                    self.assertTrue(any(r["mode"] == "default" and r["workers"] == w
                                        for r in runs), f"{mid} missing default {w}w")
        # Every external compile run sitting beside a default run passes -tlc.
        for m in manifest["models"]:
            if not m["id"].startswith("ext/"):
                continue
            has_default = any(r["mode"] == "default" and "-tlc" not in (r.get("args") or []) for r in m["runs"])
            if has_default:
                for r in m["runs"]:
                    if r["mode"] == "compile":
                        self.assertIn("-tlc", r.get("args") or [], f"{m['id']} compile {r['workers']}w missing -tlc")

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

    def test_with_tlc_companion_measures_a_same_instance_twin(self):
        self.man["models"] = [self.man["models"][0]]
        self.man["models"][0]["runs"] = [{"mode": "default", "workers": 1}]
        rc, out, h = self.run_suite(fake(self.d, "companion"), with_tlc_companion=True, isolate_cache=True)
        self.assertEqual((rc, h["verdict"]["outcome"]), (0, "BASELINE"), out)
        self.assertEqual(list(h["runs"]), ["small:A/one:default:1w", "small:A/one:tlc:1w"])
        reduced, twin = (h["runs"][k] for k in h["runs"])
        self.assertEqual(twin["mode"], "tlc")
        self.assertEqual((twin["workers"], twin["args"]), (1, []))
        self.assertEqual(len(twin["samples"]), 3)
        # One cache policy for both sides of the pair, each configuration with
        # its own fresh cache rather than the reduced run's.
        self.assertEqual({r["cache"]["mode"] for r in (reduced, twin)}, {"fresh-per-model"})
        # The stored twin is a tlx `-tlc` row, never a TLC baseline row: the two
        # are different measurements even though they share a mode name.
        from benchmarking.records import normalize
        row = normalize({"commit": h["commit"], "date": h["date"], "machine": h["machine"],
                         "suite": True, "repeat": 3}, twin, "bench/history/x.json", "/runs/twin")
        self.assertEqual((row["tool"], row["mode"]), ("tlx", "-tlc"))

    def test_a_reduced_pin_does_not_reject_the_unreduced_twin(self):
        # The manifest pinned this model's distinct count from a reduced run.
        # The default-mode row is allowed to differ by contract; the companion
        # exists to measure the unreduced count, so its pin is its verdict only.
        self.man["models"] = [{**self.man["models"][0], "runs": [{"mode": "default", "workers": 1}],
                               "expect": {"result": "success", "source": "tlx-pinned", "distinct": 2}}]
        rc, out, h = self.run_suite(fake(self.d, "pinned"), with_tlc_companion=True)
        self.assertEqual((rc, h["verdict"]["outcome"]), (0, "BASELINE"), out)
        self.assertEqual(h["verdict"]["count_failures"], [])
        self.assertEqual([s["distinct"] for s in h["runs"]["small:A/one:tlc:1w"]["samples"]], [5, 5, 5])

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
        # The companion collection travels to the cloud launch with the rest of
        # the run's protocol, so the twin is measured on the same instance.
        a.with_tlc_companion = True
        self.assertIn("--with-tlc-companion", S.remote_args(a, None))
        # A shard of the suite is one launch's work: the slice travels to the
        # remote `suite` and names the history file `track` copies back.
        a.slice = "2/3"
        self.assertIn("--slice 2/3", S.remote_args(a, None))

    def test_track_refuses_a_bad_slice_before_the_launch(self):
        with contextlib.redirect_stderr(io.StringIO()), self.assertRaises(SystemExit) as cm:
            S.cmd_track(argparse.Namespace(rev="HEAD", base="none", sizes="all", models="", repeat=3,
                                           max_minutes=40, setup_minutes=20, provider="tencent",
                                           instance_type="", inject_slow=[], slice="3/2", dry_run=True))
        self.assertIn("--slice expects I/N", str(cm.exception))


class SuiteMerge(unittest.TestCase):
    """`suite-merge` joins the `--slice I/N` histories of one suite run: the
    shards are disjoint, so the merged file is their union, and the verdict is
    judged again over that union with the thresholds the shards recorded."""

    REV, BASE = "a" * 12, "b" * 12

    def history(self, **over):
        h = {"suite": True, "commit": self.REV, "date": "2026-11-01 10:00:00", "machine": "m1", "repeat": 3,
             "sizes": "all", "tla2tools": {"revision": "r1"},
             "judgement": {"threshold": 0.05, "max_noise": 0.25, "min_delta": 0.05},
             "runs": {}, "samples": [],
             "verdict": {"outcome": "PASS", "count_failures": [], "regressions": [], "inconclusive": [], "skipped": []}}
        h.update(over)
        return h

    def run_record(self, key, walls=(1.0, 1.01, 1.02), result="success"):
        return {"tier": "large", "model": key.split(":")[1], "mode": "compile", "workers": 1,
                "walls": list(walls), "cpu": list(walls), "min": min(walls) if walls else None,
                "distinct": 5, "result": result, "key": key}

    def merge(self, out, inputs, sets=()):
        a = argparse.Namespace(out=str(out), inputs=[str(p) for p in inputs], set=list(sets))
        with contextlib.redirect_stdout(io.StringIO()) as buf, contextlib.redirect_stderr(io.StringIO()) as err:
            code = S.cmd_suite_merge(a)
        return code, read(out), buf.getvalue() + err.getvalue()

    def slice(self, directory, name, h):
        path = os.path.join(directory, name)
        write(path, json.dumps(h))
        return path

    def test_merges_runs_base_runs_and_samples(self):
        k1, k2 = "large:M/a:compile:1w", "large:M/b:compile:1w"
        with tempfile.TemporaryDirectory() as d:
            s1 = self.slice(d, "s1.json", self.history(
                date="2026-11-01 10:00:00", slice="1/2",
                runs={k1: self.run_record(k1)},
                base={"commit": self.BASE, "runs": {k1: self.run_record(k1)}},
                samples=[{"model": "M/a", "round": 1}]))
            s2 = self.slice(d, "s2.json", self.history(
                date="2026-11-01 11:00:00", slice="2/2",
                runs={k2: self.run_record(k2)},
                base={"commit": self.BASE, "runs": {k2: self.run_record(k2)}},
                samples=[{"model": "M/b", "round": 1}]))
            code, out, _ = self.merge(os.path.join(d, "merged.json"), [s1, s2])
        self.assertEqual(code, 0)
        self.assertEqual(sorted(out["runs"]), [k1, k2])
        self.assertEqual(sorted(out["base"]["runs"]), [k1, k2])
        self.assertEqual([s["model"] for s in out["samples"]], ["M/a", "M/b"])
        self.assertEqual((out["date"], out["date_end"]), ("2026-11-01 10:00:00", "2026-11-01 11:00:00"))
        self.assertEqual([s["slice"] for s in out["slices"]], ["1/2", "2/2"])
        self.assertEqual(out["judgement"], {"threshold": 0.05, "max_noise": 0.25, "min_delta": 0.05})
        self.assertNotIn("slice", out)
        self.assertEqual(out["verdict"]["outcome"], "PASS")

    def test_a_regression_in_one_slice_regresses_the_merged_verdict(self):
        k = "large:M/a:compile:1w"
        with tempfile.TemporaryDirectory() as d:
            s1 = self.slice(d, "s1.json", self.history(
                runs={k: self.run_record(k, walls=(2.0, 2.02, 2.04))},
                base={"commit": self.BASE, "runs": {k: self.run_record(k)}}))
            code, out, _ = self.merge(os.path.join(d, "merged.json"), [s1])
        self.assertEqual(code, 1)
        self.assertEqual(out["verdict"]["outcome"], "REGRESSION")
        self.assertEqual([r["key"] for r in out["verdict"]["regressions"]], [k])

    def test_a_duplicate_key_keeps_the_stronger_run(self):
        k = "large:M/a:compile:1w"
        skipped = self.run_record(k, walls=(), result="skipped")
        with tempfile.TemporaryDirectory() as d:
            s1 = self.slice(d, "s1.json", self.history(runs={k: self.run_record(k)}))
            s2 = self.slice(d, "s2.json", self.history(
                date="2026-11-01 11:00:00", runs={k: skipped},
                verdict={"outcome": "INCONCLUSIVE", "count_failures": [], "regressions": [],
                         "inconclusive": [], "skipped": [k]}))
            _, out, err = self.merge(os.path.join(d, "merged.json"), [s1, s2])
        self.assertEqual(out["runs"][k]["result"], "success")
        self.assertEqual(out["verdict"]["skipped"], [])
        self.assertIn("keeping the stronger run", err)

    def test_a_duplicate_ab_key_keeps_one_shard_pair(self):
        # Each shard measured its own interleaved (new, base) pair on its own
        # instance. Selecting the two sides independently would pair s2's new
        # time (10.6) with s1's base time (10.0) and fabricate a REGRESSION.
        k = "large:M/a:compile:1w"
        with tempfile.TemporaryDirectory() as d:
            s1 = self.slice(d, "s1.json", self.history(
                runs={k: self.run_record(k, walls=(10.7, 10.7, 10.7))},
                base={"commit": self.BASE, "runs": {k: self.run_record(k, walls=(10.0, 10.0, 10.0))}}))
            s2 = self.slice(d, "s2.json", self.history(
                date="2026-11-01 11:00:00", runs={k: self.run_record(k, walls=(10.6, 10.6, 10.6))},
                base={"commit": self.BASE, "runs": {k: self.run_record(k, walls=(10.8, 10.8, 10.8))}}))
            code, out, _ = self.merge(os.path.join(d, "merged.json"), [s1, s2])
        self.assertEqual((out["runs"][k]["min"], out["base"]["runs"][k]["min"]), (10.6, 10.8))
        self.assertEqual(out["verdict"]["outcome"], "PASS")
        self.assertEqual(code, 0)

    def test_a_count_mismatch_does_not_beat_a_clean_duplicate(self):
        k = "large:M/a:compile:1w"
        mismatch = {**self.run_record(k, walls=(1.0, 1.0, 1.0)), "count_problems": ["distinct 5 -> 6"]}
        with tempfile.TemporaryDirectory() as d:
            s1 = self.slice(d, "s1.json", self.history(
                runs={k: self.run_record(k, walls=(10.6, 10.6, 10.6))},
                base={"commit": self.BASE, "runs": {k: self.run_record(k, walls=(10.0, 10.0, 10.0))}}))
            s2 = self.slice(d, "s2.json", self.history(
                date="2026-11-01 11:00:00", runs={k: mismatch},
                base={"commit": self.BASE, "runs": {k: self.run_record(k, walls=(9.0, 9.0, 9.0))}}))
            _, out, _ = self.merge(os.path.join(d, "merged.json"), [s1, s2])
        self.assertEqual(out["runs"][k]["min"], 10.6)
        self.assertEqual(out["base"]["runs"][k]["min"], 10.0)

    def test_run_evidence_matches_the_store_order(self):
        clean = S._suite_run_evidence({"result": "success", "min": 10.6, "date": "d"})
        # A zero minimum is a measurement, not an unknown: it must not be read
        # as `float("inf")` by a truthiness test.
        zero = S._suite_run_evidence({"result": "success", "min": 0.0, "date": "d"})
        self.assertEqual(zero[0], 2)
        self.assertGreater(zero, clean)
        # An expectation mismatch proves no more than no verdict (records.evidence).
        bad = S._suite_run_evidence({"result": "success", "min": 1.0, "count_problems": ["distinct 5 -> 6"]})
        self.assertEqual(bad[0], 0)
        # Two timeouts: the longer measured bound proves more.
        self.assertGreater(S._suite_run_evidence({"result": "timeout", "min": 20.0}),
                           S._suite_run_evidence({"result": "timeout", "min": 10.0}))

    def test_a_skipped_stub_does_not_beat_a_real_measurement(self):
        # A shard that hit `--max-minutes` records a (skipped, skipped) stub
        # with no samples; a retry shard runs the key and its new side completes
        # while the base side fails. The empty stub must not win just because
        # both of its sides are "not an error" (the report's looser `ok_result`).
        k = "large:M/a:compile:1w"
        with tempfile.TemporaryDirectory() as d:
            s1 = self.slice(d, "s1.json", self.history(
                runs={k: self.run_record(k, walls=(), result="skipped")},
                base={"commit": self.BASE, "runs": {k: self.run_record(k, walls=(), result="skipped")}},
                verdict={"outcome": "INCONCLUSIVE", "count_failures": [], "regressions": [],
                         "inconclusive": [], "skipped": [k]}))
            s2 = self.slice(d, "s2.json", self.history(
                date="2026-11-01 11:00:00", runs={k: self.run_record(k, walls=(10.0, 10.0, 10.0))},
                base={"commit": self.BASE, "runs": {k: self.run_record(k, walls=(), result="unknown")}}))
            _, out, _ = self.merge(os.path.join(d, "merged.json"), [s1, s2])
        self.assertEqual(out["runs"][k]["result"], "success")
        self.assertEqual(out["base"]["runs"][k]["result"], "unknown")
        self.assertNotIn(k, out["verdict"]["skipped"])

    def test_a_count_mismatch_pair_still_beats_a_skipped_stub(self):
        k = "large:M/a:compile:1w"
        mismatch = {**self.run_record(k, walls=(10.0, 10.0, 10.0)), "count_problems": ["distinct 5 -> 6"]}
        with tempfile.TemporaryDirectory() as d:
            s1 = self.slice(d, "s1.json", self.history(
                runs={k: self.run_record(k, walls=(), result="skipped")},
                base={"commit": self.BASE, "runs": {k: self.run_record(k, walls=(), result="skipped")}}))
            s2 = self.slice(d, "s2.json", self.history(
                date="2026-11-01 11:00:00", runs={k: mismatch},
                base={"commit": self.BASE, "runs": {k: self.run_record(k, walls=(11.0, 11.0, 11.0))}}))
            _, out, _ = self.merge(os.path.join(d, "merged.json"), [s1, s2])
        self.assertEqual(out["runs"][k]["count_problems"], ["distinct 5 -> 6"])
        self.assertEqual(out["base"]["runs"][k]["min"], 11.0)

    def test_the_inputs_must_state_one_run_identity(self):
        cases = {
            "commit": {"commit": "c" * 12},
            "machine": {"machine": "m2"},
            "repeat": {"repeat": 5},
            "sizes": {"sizes": "small"},
            "tla2tools": {"tla2tools": {"revision": "r2"}},
            "different thresholds": {"judgement": {"threshold": 0.2, "max_noise": 0.25, "min_delta": 0.05}},
            "base revision": {"base": {"commit": "d" * 12, "runs": {}}},
        }
        with tempfile.TemporaryDirectory() as d:
            first = self.slice(d, "s1.json", self.history())
            for label, over in cases.items():
                with self.subTest(label):
                    second = self.slice(d, "s2.json", self.history(**over))
                    a = argparse.Namespace(out=os.path.join(d, "merged.json"), inputs=[first, second], set=[])
                    with contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()), \
                            self.assertRaises(SystemExit):
                        S.cmd_suite_merge(a)

    def test_spot_launch_identities_of_one_instance_type_merge(self):
        # Slices are separate spot launches, so their recorded machine strings
        # name different zones; the hardware (instance type and architecture) is
        # what has to agree, and the merged header states one deterministically.
        hard = "x86_64, AMD EPYC 9754 64-Core Processor, 16 cores, tencent SA5.4XLARGE32 (%s, spot 1.0 CNY/h)"
        with tempfile.TemporaryDirectory() as d:
            s1 = self.slice(d, "s1.json", self.history(machine=hard % "ap-beijing-3"))
            s2 = self.slice(d, "s2.json", self.history(machine=hard % "ap-beijing-4"))
            _, out, _ = self.merge(os.path.join(d, "merged.json"), [s1, s2])
        self.assertEqual(out["machine"], hard % "ap-beijing-3")
        self.assertEqual([s["machine"] for s in out["slices"]], [hard % "ap-beijing-3", hard % "ap-beijing-4"])

    def test_set_adds_a_header_field(self):
        with tempfile.TemporaryDirectory() as d:
            first = self.slice(d, "s1.json", self.history())
            _, out, _ = self.merge(os.path.join(d, "merged.json"), [first], sets=["instance_type=SA5.4XLARGE32"])
        self.assertEqual(out["instance_type"], "SA5.4XLARGE32")


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

    def namespace(self, base=None, slice_spec=""):
        """The `track` arguments the tests launch, including the shard `--slice`
        (`slice_spec` is the `I/N` value, empty for an unsliced run)."""
        return argparse.Namespace(rev="HEAD", base=self.BASE if base is None else base, sizes="small", models="",
                                  repeat=3, max_minutes=40, setup_minutes=20, provider="tencent", instance_type="",
                                  inject_slow=[], dry_run=False, slice=slice_spec)

    def bench_args(self, base=None, slice_spec=""):
        """The remote `bench.py suite` command `cmd_track` launches, as the
        receipt records it."""
        return S.remote_args(self.namespace(base, slice_spec), None if base == "none" else self.BASE)

    def receipt(self, rev=REV, exit_code=0, bins=(), bench=None, **over):
        r = {"provider": "tencent", "rev": rev, "verify_exit": exit_code, "verify_env": {}, "arch": "arm64",
             "fetched_at": "2026-10-08T00:00:00Z", "phases_s": {}, "bench": [self.bench_args()] if bench is None else bench,
             "bench_bins": [{"name": n, "rev": b, "features": ""} for n, b, _ in bins]}
        r.update(over)
        return r

    def suite_history(self, rev=REV, base=BASE, outcome="PASS", slice_spec=None):
        h = {"suite": True, "commit": rev, "date": "2026-10-08 10:00:00", "machine": "test machine",
             "base": {"commit": base} if base else {},
             "runs": [{"key": "M#compile", "min": 1.0, "walls": [1.0]}],
             "verdict": {"outcome": outcome, "count_failures": [], "regressions": [], "inconclusive": [], "skipped": []}}
        if slice_spec is not None:
            h["slice"] = slice_spec
        return h

    def result_dir(self, name, receipt, history=None, history_name="history.json"):
        d = os.path.join(self.results, name)
        os.makedirs(d)
        with open(os.path.join(d, "cloud.json"), "w") as f:
            json.dump(receipt, f)
        if history is not None:
            hd = os.path.join(d, "bench", "history")
            os.makedirs(hd)
            with open(os.path.join(hd, history_name), "w") as f:
                json.dump(history, f)
        return d

    def invoke(self, rc, base=None, slice_spec=""):
        a = self.namespace(base, slice_spec)

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
        baseline = [self.bench_args(base="none")]
        self.result_dir("run-baseline", self.receipt(bins=[], bench=baseline), self.suite_history(base=None))
        self.assertEqual(self.invoke(0, base="none")[0], 0)
        self.assertEqual(self.recorded(), ["history.json"])
        self.clear()
        self.result_dir("run-extra-bin", self.receipt(bins=[("base", self.BASE, "")], bench=baseline),
                        self.suite_history(base=None))
        self.assertEqual(self.invoke(0, base="none")[0], 3)

    def test_sequential_slices_are_recorded_from_their_own_receipts(self):
        # Two shards of one revision are two launches of the same revision, base
        # and exit status; only the receipt's bench command (its `--slice I/N`)
        # tells them apart. Before the fix the second shard saw two matching
        # receipts and exited 3 without recording its history.
        self.result_dir("run-slice1", self.receipt(bins=[("base", self.BASE, "")], bench=[self.bench_args(slice_spec="1/2")]),
                        self.suite_history(slice_spec="1/2"), history_name="a-slice1of2.json")
        code, message = self.invoke(0, slice_spec="1/2")
        self.assertEqual(code, 0, message)
        self.assertEqual(self.recorded(), ["a-slice1of2.json"])
        self.result_dir("run-slice2", self.receipt(bins=[("base", self.BASE, "")], bench=[self.bench_args(slice_spec="2/2")]),
                        self.suite_history(slice_spec="2/2"), history_name="b-slice2of2.json")
        code, message = self.invoke(0, slice_spec="2/2")
        self.assertEqual(code, 0, message)
        self.assertEqual(self.recorded(), ["a-slice1of2.json", "b-slice2of2.json"])

    def test_a_receipt_or_history_of_another_slice_is_refused(self):
        # A receipt of another shard (its bench command names `1/2`) and a
        # receipt of the right shard whose history file is the other shard's
        # both authorize nothing: the requested shard is never guessed from the
        # only file lying around.
        self.result_dir("run-other-slice", self.receipt(bins=[("base", self.BASE, "")], bench=[self.bench_args(slice_spec="1/2")]),
                        self.suite_history(slice_spec="1/2"), history_name="history.json")
        self.assertEqual(self.invoke(0, slice_spec="2/2")[0], 3)
        self.assertEqual(self.recorded(), [])
        self.clear()
        self.result_dir("run-wrong-history", self.receipt(bins=[("base", self.BASE, "")], bench=[self.bench_args(slice_spec="2/2")]),
                        self.suite_history(slice_spec="1/2"), history_name="history.json")
        self.assertEqual(self.invoke(0, slice_spec="2/2")[0], 3)
        self.assertEqual(self.recorded(), [])
        # Control: the same receipt with its own shard's history records.
        self.clear()
        self.result_dir("run-right-history", self.receipt(bins=[("base", self.BASE, "")], bench=[self.bench_args(slice_spec="2/2")]),
                        self.suite_history(slice_spec="2/2"), history_name="history.json")
        self.assertEqual(self.invoke(0, slice_spec="2/2")[0], 0)

    def test_two_receipts_of_the_same_slice_are_refused(self):
        for name in ("run-a", "run-b"):
            self.result_dir(name, self.receipt(bins=[("base", self.BASE, "")], bench=[self.bench_args(slice_spec="1/2")]),
                            self.suite_history(slice_spec="1/2"), history_name="history.json")
        code, message = self.invoke(0, slice_spec="1/2")
        self.assertEqual(code, 3)
        self.assertEqual(self.recorded(), [])
        self.assertIn("more than one", message)

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


class ShardingSchedulingAndMissing(testkit.GuardedTestCase):
    """`suite --missing`, `--slice I/N`, shortest-first scheduling, and `--bin` provenance."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = os.path.join(self.tmp.name, "repo")
        os.makedirs(os.path.join(self.root, "bench"))
        self.specs = {}
        for name in ("Fast", "Medium", "Heavy", "Unknown"):
            tla = os.path.join(self.root, f"{name}.tla")
            cfg = os.path.join(self.root, f"{name}.cfg")
            write(tla, f"---- MODULE {name} ----\n====\n")
            write(cfg, "INIT Init\nNEXT Next\n")
            self.specs[f"ext/{name}"] = {"id": f"ext/{name}", "tla": tla, "cfg": cfg, "flags": [], "tlc": {}}

    def _stored_row(self, model, *, mode="default", workers=1, rev="e5dffafd5419e069ccd854d7aa674d18631eea15",
                    instance="SA5.4XLARGE32", arch="x86_64", tlc_version="tlc-v1", args=(), wall=5.0,
                    compatibility=None, cache_mode="fresh-per-model", cache_warmup=True,
                    variant=None, count_problems=None, tool="tlx", ptr=None):
        from benchmarking.baselines import content_digest
        from benchmarking.records import normalize
        raw = {
            "tool": tool, "model": model, "mode": mode, "workers": workers,
            "walls": [wall, wall, wall], "cpu": [wall, wall, wall], "rss_mib": [32.0, 32.0, 32.0],
            "result": "success", "distinct": 10, "generated": 20, "depth": 3,
            "args": list(args), "content_digest": content_digest(self.specs[model]),
            "tlc_version": tlc_version,
        }
        if compatibility is not None:
            raw["compatibility"] = compatibility
        if cache_mode is not None:
            raw["cache"] = {"mode": cache_mode,
                            "initial_state": "empty" if cache_mode == "fresh-per-model" else "unknown",
                            "warmup": cache_warmup}
        if count_problems is not None:
            raw["count_problems"] = count_problems
        header = {"suite": True, "repeat": 3, "commit": rev, "date": "2026-11-28 10:00:00",
                  "machine": f"{arch}, tencent {instance}", "tla2tools": {"revision": tlc_version}}
        return normalize(header, raw, "bench/history/s.json", ptr or f"/runs/{model}:{mode}:{workers}",
                         revision=rev, variant=variant)

    def test_cost_estimation_priority_and_shortest_first_scheduling(self):
        from benchmarking.records import write_records
        tlx_fast = self._stored_row("ext/Medium", mode="default", workers=1, wall=1.5)
        tlc_heavy = self._stored_row("ext/Heavy", mode="-tlc", workers=1, wall=250.0, rev=None, tool="tlc", ptr="/runs/tlc")
        tlx_walls, tlc_walls = S._cost_indices([tlx_fast, tlc_heavy])
        man = {"version": 1, "models": [
            {"id": "ext/Heavy", "size": "large", "timeout_s": 600,
             "runs": [{"mode": "default", "workers": 1}], "expect": {"source": "unpinned"}},
            {"id": "ext/Unknown", "size": "huge", "timeout_s": 1800,
             "runs": [{"mode": "default", "workers": 1}], "expect": {"source": "unpinned"}},
            {"id": "ext/Medium", "size": "medium", "timeout_s": 300,
             "runs": [{"mode": "default", "workers": 1}], "expect": {"source": "unpinned"}},
            {"id": "ext/Fast", "size": "small", "timeout_s": 120,
             "runs": [{"mode": "default", "workers": 1}], "expect": {"source": "unpinned"}},
        ]}
        es = S.entries(man, "all", with_tlc_companion=True)
        # Cost priorities: (a) stored tlx (1.5s), (b) stored TLC (250s), (c) size fallback (small=2s, huge=600s).
        by_key = {e["key"]: S.estimate_entry_cost(e, tlx_walls=tlx_walls, tlc_walls=tlc_walls) for e in es}
        self.assertEqual(by_key["medium:ext/Medium:default:1w"], 1.5)
        self.assertEqual(by_key["small:ext/Fast:default:1w"], 2.0)
        self.assertEqual(by_key["large:ext/Heavy:default:1w"], 250.0)
        self.assertEqual(by_key["huge:ext/Unknown:default:1w"], 600.0)
        # Shortest-first orders models by total cost and keeps default + companion adjacent.
        ordered = S.order_entries_shortest_first(es, records=[tlx_fast, tlc_heavy])
        models_order = list(dict.fromkeys(e["model"] for e in ordered))
        self.assertEqual(models_order, ["ext/Fast", "ext/Medium", "ext/Heavy", "ext/Unknown"])
        for i in range(0, len(ordered), 2):
            self.assertEqual(ordered[i]["model"], ordered[i + 1]["model"])
            self.assertEqual((ordered[i]["mode"], ordered[i + 1]["mode"]), ("default", "tlc"))
        # LPT slicing keeps all entries of each model in the same slice.
        s1 = S.slice_entries(es, "1/2", records=[tlx_fast, tlc_heavy])
        s2 = S.slice_entries(es, "2/2", records=[tlx_fast, tlc_heavy])
        m1, m2 = {e["model"] for e in s1}, {e["model"] for e in s2}
        self.assertEqual(m1 & m2, set())
        self.assertEqual(m1 | m2, {"ext/Fast", "ext/Medium", "ext/Heavy", "ext/Unknown"})
        self.assertEqual(len(s1) + len(s2), len(es))
        # Verify write_records round-trip is clean for the fixture.
        write_records([tlx_fast], self.root)

    def test_missing_filters_satisfied_keys_and_checks_companion_twins(self):
        from benchmarking.baselines import content_digest
        full_rev = "e5dffafd5419e069ccd854d7aa674d18631eea15"
        short_rev = "e5dffafd5419"
        man = {"version": 1, "models": [
            {"id": "ext/Fast", "size": "small", "timeout_s": 60,
             "runs": [{"mode": "compile", "workers": 1, "args": ["-tlc"]}, {"mode": "default", "workers": 1}],
             "expect": {"source": "unpinned"}},
            {"id": "ext/Medium", "size": "medium", "timeout_s": 60,
             "runs": [{"mode": "default", "workers": 1}],
             "expect": {"source": "unpinned"}},
            {"id": "ext/Heavy", "size": "large", "timeout_s": 60,
             "runs": [{"mode": "default", "workers": 1}],
             "expect": {"source": "unpinned"}},
        ]}
        es = S.entries(man, "all", with_tlc_companion=True)
        digests = {mid: content_digest(m) for mid, m in self.specs.items()}
        records = [
            # ext/Fast has both default and compile -tlc paired under full_rev + fresh-per-model.
            self._stored_row("ext/Fast", mode="default", rev=full_rev, cache_mode="fresh-per-model"),
            self._stored_row("ext/Fast", mode="-compile", rev=full_rev, args=["-tlc"], compatibility=True, cache_mode="fresh-per-model"),
            # ext/Medium has default with full_rev + fresh-per-model, but NO twin yet.
            self._stored_row("ext/Medium", mode="default", rev=full_rev, cache_mode="fresh-per-model"),
            # ext/Heavy has default under shared-batch (incompatible with --isolate-cache) and an ineligible record.
            self._stored_row("ext/Heavy", mode="default", rev=full_rev, cache_mode="shared-batch"),
            self._stored_row("ext/Heavy", mode="-tlc", rev=full_rev, cache_mode="fresh-per-model", count_problems=["mismatch"]),
        ]
        # When running with matching full_rev/arch/tlc_version, ext/Medium's stored default can pair with the new twin.
        missing, satisfied = S.filter_missing_entries(
            es, records, revision=full_rev, instance_type="SA5.4XLARGE32", digests=digests,
            with_tlc_companion=True, isolate_cache=True, instance_arch="x86_64", tlc_version="tlc-v1")
        self.assertEqual(satisfied, 3)  # ext/Fast default + compile -tlc, plus ext/Medium default
        self.assertEqual([(e["model"], e["mode"]) for e in missing],
                         [("ext/Medium", "tlc"), ("ext/Heavy", "default"), ("ext/Heavy", "tlc")])
        # Adding a matching `-compile -tlc` record satisfies ext/Medium's synthesized `tlc` companion too.
        records.append(self._stored_row("ext/Medium", mode="-compile", rev=full_rev, args=["-tlc"],
                                        compatibility=True, cache_mode="fresh-per-model"))
        missing2, satisfied2 = S.filter_missing_entries(
            es, records, revision=full_rev, instance_type="SA5.4XLARGE32", digests=digests,
            with_tlc_companion=True, isolate_cache=True, instance_arch="x86_64", tlc_version="tlc-v1")
        self.assertEqual(satisfied2, 4)
        self.assertEqual([(e["model"], e["mode"]) for e in missing2],
                         [("ext/Heavy", "default"), ("ext/Heavy", "tlc")])
        # Already-paired ext/Fast stays satisfied even when queried with short_rev, whereas
        # an unpaired single half at full_rev cannot pair with a short_rev follow-up run!
        unpaired_single = [self._stored_row("ext/Medium", mode="default", rev=full_rev, cache_mode="fresh-per-model")]
        med_es = [e for e in es if e["model"] == "ext/Medium"]
        missing_short, satisfied_short = S.filter_missing_entries(
            med_es, unpaired_single, revision=short_rev, instance_type="SA5.4XLARGE32", digests=digests,
            with_tlc_companion=True, isolate_cache=True, instance_arch="x86_64", tlc_version="tlc-v1")
        self.assertEqual(satisfied_short, 0)
        self.assertEqual([(e["model"], e["mode"]) for e in missing_short],
                         [("ext/Medium", "default"), ("ext/Medium", "tlc")])
        # Mixed 40-char / 12-char halves do not pair in bench_records.unreduced_twin and must NOT report 0 missing.
        fast_es = [e for e in es if e["model"] == "ext/Fast"]
        mixed_rev = [
            self._stored_row("ext/Fast", mode="default", rev=full_rev, cache_mode="fresh-per-model"),
            self._stored_row("ext/Fast", mode="-compile", rev=short_rev, args=["-tlc"], compatibility=True, cache_mode="fresh-per-model"),
        ]
        m_short, _ = S.filter_missing_entries(
            fast_es, mixed_rev, revision=short_rev, instance_type="SA5.4XLARGE32", digests=digests,
            with_tlc_companion=True, isolate_cache=True, instance_arch="x86_64", tlc_version="tlc-v1")
        self.assertEqual([(e["model"], e["mode"]) for e in m_short], [("ext/Fast", "default")])
        m_full, _ = S.filter_missing_entries(
            fast_es, mixed_rev, revision=full_rev, instance_type="SA5.4XLARGE32", digests=digests,
            with_tlc_companion=True, isolate_cache=True, instance_arch="x86_64", tlc_version="tlc-v1")
        self.assertEqual([(e["model"], e["mode"]) for e in m_full], [("ext/Fast", "compile")])
        # Mismatched tlc_version, arch, variant, cache, or missing compatibility=True on -compile -tlc
        # must schedule the non-matching half(ves) so the result actually pairs.
        for label, twin_over, expected_missing in (
                ("mismatched tlc_version", {"tlc_version": "tlc-old"}, [("ext/Fast", "compile")]),
                ("mismatched arch", {"arch": "aarch64"}, [("ext/Fast", "compile")]),
                ("mismatched variant", {"variant": "new"}, [("ext/Fast", "compile")]),
                ("mismatched cache mode", {"cache_mode": "shared-batch"}, [("ext/Fast", "compile")]),
                ("mismatched cache warmup", {"cache_warmup": False}, [("ext/Fast", "compile")]),
                ("compile -tlc compatibility False", {"compatibility": False}, [("ext/Fast", "compile")]),
                ("compile -tlc compatibility absent", {"compatibility": None}, [("ext/Fast", "compile")]),
        ):
            with self.subTest(case=label):
                pair = [
                    self._stored_row("ext/Fast", mode="default", rev=full_rev, cache_mode="fresh-per-model"),
                    self._stored_row("ext/Fast", mode="-compile", rev=full_rev, args=["-tlc"],
                                     compatibility=twin_over.get("compatibility", True),
                                     cache_mode=twin_over.get("cache_mode", "fresh-per-model"),
                                     cache_warmup=twin_over.get("cache_warmup", True),
                                     tlc_version=twin_over.get("tlc_version", "tlc-v1"),
                                     arch=twin_over.get("arch", "x86_64"),
                                     variant=twin_over.get("variant")),
                ]
                got_missing, _ = S.filter_missing_entries(
                    fast_es, pair, revision=full_rev, instance_type="SA5.4XLARGE32", digests=digests,
                    with_tlc_companion=True, isolate_cache=(twin_over.get("cache_mode", "fresh-per-model") == "fresh-per-model"),
                    instance_arch="x86_64", tlc_version="tlc-v1",
                    expected_cache={"mode": "fresh-per-model", "initial_state": "empty", "warmup": True})
                self.assertEqual([(e["model"], e["mode"]) for e in got_missing], expected_missing)

    def test_consecutive_missing_passes_preserve_prior_ingested_records(self):
        from benchmarking.records import load_records
        man = {"version": 1, "models": [
            {"id": "ext/Fast", "size": "small", "timeout_s": 60,
             "runs": [{"mode": "default", "workers": 1}], "expect": {"source": "unpinned"}},
            {"id": "ext/Medium", "size": "medium", "timeout_s": 60,
             "runs": [{"mode": "default", "workers": 1}], "expect": {"source": "unpinned"}},
            {"id": "ext/Heavy", "size": "large", "timeout_s": 60,
             "runs": [{"mode": "default", "workers": 1}], "expect": {"source": "unpinned"}},
        ]}
        fake_bin = fake(self.tmp.name, "inc-tlx", sleep=0.0)
        rev = "e5dffafd5419"

        def run_missing(models, out=""):
            a = argparse.Namespace(manifest=None, sizes="all", models=models, modes="", pin_adapt="",
                                   with_tlc_companion=False, isolate_cache=True,
                                   missing=True, slice="", bin=fake_bin, bin_rev=rev,
                                   instance_type="", dry_run=False,
                                   base_bin="", base_rev="", repeat=1, max_minutes=0,
                                   threshold=0.05, max_noise=0.5, min_delta=0.01,
                                   no_instructions=True, inject_slow=[], out=out)
            buf = io.StringIO()
            with patch.object(S.bench_machine, "machine_desc", return_value="x86_64, tencent SA5.4XLARGE32"), \
                 contextlib.redirect_stdout(buf):
                rc = S.run_suite(a, bench=bench, resolve=self.specs.__getitem__, man=man, root=self.root)
            return rc, buf.getvalue()

        # Pass 1: collect ext/Fast into default history path and ingest into bench/records/.
        rc1, out1 = run_missing("ext/Fast")
        self.assertEqual(rc1, 0, out1)
        self.assertEqual({r["model"] for r in load_records(self.root)}, {"ext/Fast"})
        first_hist = os.path.join(self.root, "bench", "history", f"{rev}.json")
        self.assertTrue(os.path.isfile(first_hist))

        # Explicit --out pointing to an already-existing history file is refused under --missing.
        with self.assertRaisesRegex(SystemExit, "refuses to overwrite existing history file"):
            run_missing("ext/Fast,ext/Medium", out=first_hist)

        # Pass 2: default --out picks a non-colliding history file so Pass 1's ext/Fast survives ingest!
        rc2, out2 = run_missing("ext/Fast,ext/Medium")
        self.assertEqual(rc2, 0, out2)
        self.assertIn("1 missing run(s) (1 satisfied)", out2)
        self.assertEqual({r["model"] for r in load_records(self.root)}, {"ext/Fast", "ext/Medium"})
        second_hist = os.path.join(self.root, "bench", "history", f"{rev}-missing-1.json")
        self.assertTrue(os.path.isfile(second_hist))

        # Pass 3: both models are now satisfied -> 0 missing runs, no extra history file created.
        rc3, out3 = run_missing("ext/Fast,ext/Medium")
        self.assertEqual(rc3, 0, out3)
        self.assertIn("0 missing run(s) (2 satisfied)", out3)
        self.assertFalse(os.path.exists(os.path.join(self.root, "bench", "history", f"{rev}-missing-2.json")))
        self.assertEqual({r["model"] for r in load_records(self.root)}, {"ext/Fast", "ext/Medium"})

        # Even if first_hist is removed on disk, passing its path explicitly is still refused while its records remain owned.
        os.remove(first_hist)
        with self.assertRaisesRegex(SystemExit, "refuses to overwrite existing history file"):
            run_missing("ext/Heavy", out=first_hist)

    def test_run_suite_missing_slice_dry_run_and_external_bin_provenance(self):
        from benchmarking.records import write_records
        man = {"version": 1, "models": [
            {"id": "ext/Heavy", "size": "large", "timeout_s": 60, "tlc_1w_s": 200.0,
             "runs": [{"mode": "default", "workers": 1}], "expect": {"source": "unpinned"}},
            {"id": "ext/Fast", "size": "small", "timeout_s": 60, "tlc_1w_s": 1.0,
             "runs": [{"mode": "default", "workers": 1}], "expect": {"source": "unpinned"}},
        ]}
        write_records([self._stored_row("ext/Heavy", mode="default", rev="e5dffafd5419",
                                        instance="SA5.4XLARGE32", cache_mode="fresh-per-model")], self.root)
        # Dry-run planning works off-host with --instance-type and --bin-rev, printing only missing runs.
        a = argparse.Namespace(manifest=None, sizes="all", models="", modes="", pin_adapt="",
                               with_tlc_companion=False, isolate_cache=True,
                               missing=True, slice="1/2", bin="", bin_rev="e5dffafd5419",
                               instance_type="SA5.4XLARGE32", dry_run=True,
                               base_bin="", base_rev="", repeat=1, max_minutes=0,
                               threshold=0.05, max_noise=0.5, min_delta=0.01,
                               no_instructions=True, inject_slow=[], out="")
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = S.run_suite(a, bench=bench, resolve=self.specs.__getitem__, man=man, root=self.root)
        self.assertEqual(rc, 0)
        self.assertIn("1 missing run(s) (1 satisfied)", buf.getvalue())
        self.assertIn("small:ext/Fast:default:1w", buf.getvalue())
        self.assertNotIn("ext/Heavy", buf.getvalue())
        # Empty slice 2/2 exits 0 cleanly without running anything.
        a.slice = "2/2"
        buf2 = io.StringIO()
        with contextlib.redirect_stdout(buf2):
            rc = S.run_suite(a, bench=bench, resolve=self.specs.__getitem__, man=man, root=self.root)
        self.assertEqual(rc, 0)
        self.assertIn("0 runs in slice", buf2.getvalue())
        # Refusals: --missing --bin without --bin-rev; --bin-rev without --bin (non-dry-run); --instance-type mismatch.
        for label, over, msg in (
                ("missing+bin no bin-rev", {"dry_run": False, "bin": "/fake/tlx", "bin_rev": "", "missing": True}, "--bin-rev"),
                ("bin-rev no bin", {"dry_run": False, "bin": "", "bin_rev": "abc1234", "missing": False}, "--bin-rev requires --bin"),
                ("instance mismatch", {"dry_run": False, "bin": "/fake/tlx", "bin_rev": "abc1234", "instance_type": "OTHER"}, "--instance-type"),
                ("bad slice", {"slice": "3/2"}, "--slice expects I/N"),
        ):
            with self.subTest(case=label):
                bad = argparse.Namespace(**{**vars(a), **over})
                with self.assertRaisesRegex(SystemExit, msg):
                    S.run_suite(bad, bench=bench, resolve=self.specs.__getitem__, man=man, root=self.root)
        # External --bin provenance (HARNESS-19): commit is None when --bin-rev is omitted,
        # and print_verdict + trend_markdown + previous_recorded handle commit=None cleanly.
        fake_bin = fake(self.tmp.name, "ext-tlx", sleep=0.0)
        out_path = os.path.join(self.tmp.name, "ext-run.json")
        run_args = argparse.Namespace(manifest=None, sizes="small", models="ext/Fast", modes="", pin_adapt="",
                                      with_tlc_companion=False, isolate_cache=False,
                                      missing=False, slice="", bin=fake_bin, bin_rev="",
                                      instance_type="", dry_run=False,
                                      base_bin="", base_rev="", repeat=1, max_minutes=0,
                                      threshold=0.05, max_noise=0.5, min_delta=0.01,
                                      no_instructions=True, inject_slow=[], out=out_path)
        out_buf = io.StringIO()
        with contextlib.redirect_stdout(out_buf):
            rc = S.run_suite(run_args, bench=bench, resolve=self.specs.__getitem__, man=man, root=self.root)
        self.assertEqual(rc, 0, out_buf.getvalue())
        h = read(out_path)
        self.assertIsNone(h["commit"])
        self.assertEqual(h["bin"], os.path.abspath(fake_bin))
        self.assertTrue(h["runner_commit"])
        self.assertNotIn("bin_revs", h)
        self.assertIn("baseline, unknown", out_buf.getvalue())
        md = S.trend_markdown([h])
        self.assertIn("`unknown`", md)
        self.assertIsNone(S.previous_recorded("abc1234", [h], lambda c, r: True))
        # With explicit --bin-rev, commit and bin_revs.new record the supplied revision.
        out_path2 = os.path.join(self.tmp.name, "ext-run-rev.json")
        run_args.bin_rev = "e5dffafd5419"
        run_args.out = out_path2
        with contextlib.redirect_stdout(io.StringIO()):
            rc2 = S.run_suite(run_args, bench=bench, resolve=self.specs.__getitem__, man=man, root=self.root)
        self.assertEqual(rc2, 0)
        h2 = read(out_path2)
        self.assertEqual(h2["commit"], "e5dffafd5419")
        self.assertEqual(h2["bin_revs"], {"new": "e5dffafd5419"})
        self.assertEqual(h2["bin"], os.path.abspath(fake_bin))


if __name__ == "__main__":
    unittest.main()
