"""Consumer regressions for the shared script infrastructure; no cloud calls."""

from benchmarking import models as bench_models, machine as bench_machine
import contextlib, importlib.util, io, json, os, re, subprocess, sys, tarfile, tempfile, unittest
from types import SimpleNamespace
from unittest.mock import patch

import bench, corpus, coverage, difftest, fuzz_expr, spectest, tlcsuite, tlxlib, verify, verify_compare


class Drivers(unittest.TestCase):

    def test_driver_and_verify_judgment(self):
        # A driver report is authoritative even when the log says PASS.
        with tempfile.TemporaryDirectory() as root:
            ctx = SimpleNamespace(wt=root, profile="release", env={}, cache=None, logdir=root,
                                  jobs=3, tier="quick", verbose=False, filter="", quick_corpus=["A"])
            for driver in ("spectest.py", "difftest.py", "tlcsuite.py"):
                os.makedirs(os.path.join(root, "scripts"), exist_ok=True)
                with open(os.path.join(root, "scripts", driver), "w") as f:
                    f.write("add_profile_args(ap)\n")
            for status in ("pass", "fail", "xpass", "error", "timeout", "xfail"):
                for kind in ("spec", "corpus", "tlcsuite"):
                    with self.subTest(status=status, kind=kind):
                        case = tlxlib.CaseResult("A", status, {"message": "injected"})
                        def run(cmd, *_):
                            report = tlxlib.finish_cases([case], ["A"], cmd[cmd.index("--results-json") + 1])
                            return report["exit_code"], "PASS A misleading text\n1/1 passed\n"
                        with patch.object(verify, "run_logged", side_effect=run):
                            result = verify.run_suite("test-suite", kind, [], {}, ctx)
                        report = tlxlib.finish_cases([case], ["A"])
                        self.assertEqual(bool(result.error), bool(report["exit_code"]))
            # A nonzero process cannot be hidden by a successful report.
            def failed_process(cmd, *_):
                tlxlib.finish_cases([tlxlib.CaseResult("A", "pass", {})], ["A"], cmd[cmd.index("--results-json") + 1])
                return 7, "1/1 passed\n"
            with patch.object(verify, "run_logged", side_effect=failed_process):
                self.assertIn("exit 7", verify.run_suite("test-suite", "spec", [], {}, ctx).error)
            _, checked = tlxlib.read_case_report(os.path.join(root, "test-suite.log.cases.json"), 7)
            self.assertEqual(checked["exit_code"], 1)
            for selected, cases in (([], []), (["A"], []), (["A"], [tlxlib.CaseResult("A", "skip", {})])):
                self.assertEqual(tlxlib.finish_cases(cases, selected)["exit_code"], 1)

    def test_spectest_standalone_matches_verify(self):
        with tempfile.TemporaryDirectory() as root:
            Path = lambda name: os.path.join(root, name)
            with open(Path("A.tla"), "w") as f:
                f.write("module")
            with open(Path("A.cfg"), "w") as f:
                f.write("config")
            a = SimpleNamespace(refresh=False, extra="", names=["A"], suite=None, timeout=7, results_json=Path("report.json"))
            verdict = {"result": "success", "violated": None, "exit": 0, "distinct": 1, "generated": 1,
                       "depth": 1, "trace": [], "lasso": None}
            for mode in ("pass", "xpass", "fail", "error", "nonzero", "workers", "timeout", "zero"):
                with self.subTest(mode=mode):
                    a.extra = "-compile -workers 8" if mode == "workers" else ""
                    entries = [{"suite": "spectest*-w8", "id": "A", "reason": "worker race"}] if mode == "workers" else []
                    with open(Path("A.flags"), "w") as f:
                        f.write("# xfail known" if mode in ("xpass", "error", "timeout") else "")
                    with patch.object(spectest, "SPECS", root), patch.object(spectest, "VALIDATED", Path("validated.json")), \
                         patch.object(spectest, "tlc_output", return_value=("oracle", 0, False)), \
                         patch.object(spectest, "must", return_value=verdict), \
                         patch.object(spectest, "load_expected_cases", return_value=entries), \
                         patch.object(spectest, "compare", return_value=(["result"] if mode == "fail" else [], "", "")), \
                         patch.object(spectest, "compare_workers", return_value=(["result"], "", "")), \
                         patch.object(spectest, "run_proc", side_effect=(OSError("cannot execute") if mode == "error" else
                                      subprocess.TimeoutExpired(["fake"], a.timeout) if mode == "timeout" else None),
                                      return_value=tlxlib.ProcResult("", "", 7 if mode == "nonzero" else 0, 0)) as run, \
                         contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit) as exited:
                        spectest.run_specs(a, [] if mode == "zero" else ["A"], "fake")
                    result = verify.Result("spectest")
                    verify.consume_case_report(result, a.results_json, exited.exception.code)
                    self.assertEqual(exited.exception.code, 0 if mode in ("pass", "workers") else 1)
                    self.assertEqual(bool(result.error), bool(exited.exception.code))
                    if mode != "zero":
                        self.assertEqual(run.call_args.kwargs.get("timeout"), a.timeout)
                    if mode == "timeout":
                        self.assertEqual(result.case_report["cases"][0]["status"], "timeout")

    def test_difftest_standalone_matches_verify(self):
        with tempfile.TemporaryDirectory() as root:
            os.makedirs(os.path.join(root, "corpus", "out"))
            a = SimpleNamespace(filter="", ids="", oracle="", tag="", workers=1, failed=False, extra="",
                                timeout=1, recover=0, v=False, j=1, suite="corpus-compile",
                                results_json=os.path.join(root, "report.json"))
            model = {"id": "A", "tlc": {"result": "success", "distinct": 1, "generated": 1, "depth": 1}}
            for mode in ("pass", "xpass", "fail", "error", "nonzero", "zero"):
                with self.subTest(mode=mode):
                    entries = [{"suite": "corpus-*", "id": "A", "reason": "known"}] if mode in ("xpass", "error") else []
                    with patch.object(difftest, "ROOT", root), \
                         patch.object(difftest, "select_models", return_value={} if mode == "zero" else {"A": model}), \
                         patch.object(difftest, "load_expected_cases", return_value=entries), \
                         patch.object(difftest, "run_tlx", side_effect=OSError("cannot execute") if mode == "error" else None,
                                      return_value={**model["tlc"], "distinct": 2 if mode == "fail" else 1,
                                                    "exit": 7 if mode == "nonzero" else 0}), \
                         contextlib.redirect_stdout(io.StringIO()):
                        report = difftest.run_models(a, "fake")
                    result = verify.Result("corpus-compile")
                    verify.consume_case_report(result, a.results_json, report["exit_code"])
                    self.assertEqual(report["exit_code"], 0 if mode == "pass" else 1)
                    self.assertEqual(bool(result.error), bool(report["exit_code"]))

    def test_difftest_depth_contract(self):
        # Early-stop depth is exact with one worker, scheduling-dependent with
        # several; completed searches still compare it with either worker count.
        with tempfile.TemporaryDirectory() as root:
            os.makedirs(os.path.join(root, "corpus", "out"))
            a = SimpleNamespace(filter="", ids="", oracle="", tag="", workers=1, failed=False, extra="",
                                timeout=1, recover=0, v=False, j=1, suite="corpus-interp", results_json=None)
            for kind in ("success", "deadlock", "safety failure", "property failure"):
                oracle = {"result": kind, "violated": "Inv", "distinct": 192, "generated": 192, "depth": 3}
                for workers in (1, 8):
                    for depth in (3, 19):
                        for flags in ([], ["-deadlock"], ["-simulate", "num=1"], ["-generate", "num=1"]):
                            with self.subTest(kind=kind, workers=workers, depth=depth, flags=flags):
                                a.workers = workers
                                model = {"id": "Depth", "tlc": oracle, "flags": flags}
                                with patch.object(difftest, "ROOT", root), \
                                     patch.object(difftest, "select_models", return_value={"Depth": model}), \
                                     patch.object(difftest, "load_expected_cases", return_value=[]), \
                                     patch.object(difftest, "run_tlx", return_value={**oracle, "depth": depth}), \
                                     contextlib.redirect_stdout(io.StringIO()):
                                    report = difftest.run_models(a, "fake")
                                simulation = "-simulate" in flags or "-generate" in flags
                                mismatch = depth != 3 and not simulation and (workers == 1 or kind == "success")
                                self.assertEqual(report["exit_code"], int(mismatch))

    def test_spectest_timeout_argument(self):
        for flags, budget, want in (([], "120", 120), ([], "7", 7), (["--timeout", ".05"], "7", .05)):
            with patch.dict(os.environ, TLX_SPEC_TIMEOUT=budget), \
                 patch.object(sys, "argv", ["spectest.py", *flags, "A"]), \
                 patch.object(spectest, "resolve_names", return_value=["A"]), \
                 patch.object(spectest, "build_tlx", return_value=contextlib.nullcontext("fake")), \
                 patch.object(spectest, "run_specs") as run:
                spectest.main()
            self.assertEqual(run.call_args.args[0].timeout, want)

    def test_spectest_oracle_timeout(self):
        with tempfile.TemporaryDirectory() as root:
            with open(os.path.join(root, "A.tla"), "w") as source:
                source.write("module")
            with patch.object(spectest, "SPECS", root), patch.object(spectest, "TLC_OUT", root), \
                 patch.object(spectest, "run_tlc_raw", side_effect=subprocess.TimeoutExpired(["java"], 1)) as run:
                with self.assertRaises(subprocess.TimeoutExpired):
                    spectest.tlc_output("A", [], True, timeout=1)
                self.assertLessEqual(run.call_args.kwargs["timeout"], 1)
                self.assertGreater(run.call_args.kwargs["timeout"], 0)
            self.assertFalse(os.path.exists(os.path.join(root, "A.out")))

    def test_tlcsuite_retains_missing_oracle_and_retries(self):
        with tempfile.TemporaryDirectory() as root:
            tm = os.path.join(root, "test-model")
            os.makedirs(tm)
            with open(os.path.join(tm, "M.tla"), "w") as f:
                f.write("module")
            case = {"cls": "A", "spec": "M", "path": "", "args": [], "base": "ModelCheckerTestCase",
                    "exit": "SUCCESS", "stats": [], "ignored": False, "nonlit": False, "deadlock": False}
            oracle = os.path.join(root, "oracle.json")
            report_path = os.path.join(root, "report.json")
            success = {"result": "success", "exit": 0, "distinct": 1, "generated": 1, "depth": 1}
            def collect(_, budget):
                return {"result": "timeout"} if budget == 10 else success
            with patch.object(tlcsuite, "suite_dir", return_value=(root, "commit")), \
                 patch.object(tlcsuite, "extract_cases", return_value=[case]), \
                 patch.object(tlcsuite, "WORKDIR", os.path.join(root, "work")), \
                 patch.object(tlcsuite, "ORACLE", oracle), patch.object(tlcsuite, "RESULTS", os.path.join(root, "results.json")), \
                 patch.object(tlcsuite, "tlc_identity", return_value={"jar": "digest"}), \
                 patch.object(tlcsuite, "load_expected", return_value=[]), \
                 patch.object(tlcsuite, "build_tlx", return_value=contextlib.nullcontext("fake")), \
                 patch.object(tlcsuite, "run_tlx", return_value=success), \
                 patch.object(tlcsuite, "run_oracle", side_effect=collect) as run, contextlib.redirect_stdout(io.StringIO()):
                for budget, want, calls in ((10, 1, 1), (10, 1, 1), (20, 0, 2)):
                    with patch.object(sys, "argv", ["tlcsuite.py", "--ids", "A", "--oracle-timeout", str(budget),
                                                   "--results-json", report_path]), self.assertRaises(SystemExit) as exited:
                        tlcsuite.main()
                    self.assertEqual(exited.exception.code, want)
                    self.assertEqual(run.call_count, calls)
                    with open(report_path) as source:
                        report = json.load(source)
                    self.assertEqual(report["selected"], ["A"])
                    self.assertEqual(report["coverage"]["missing"], want)
                    self.assertEqual(report["coverage"]["verified"], 1 - want)
                    self.assertEqual(report["coverage"]["to_test"], 1)
                # Changing an input invalidates a completed oracle. If collecting
                # its replacement times out, the selected case must still fail.
                with open(os.path.join(tm, "M.tla"), "a") as source:
                    source.write("changed")
                with patch.object(sys, "argv", ["tlcsuite.py", "--ids", "A", "--oracle-timeout", "10",
                                               "--results-json", report_path]), self.assertRaises(SystemExit) as exited:
                    tlcsuite.main()
                self.assertEqual(exited.exception.code, 1)
                self.assertEqual(run.call_count, 3)
                with open(report_path) as source:
                    report = json.load(source)
                self.assertEqual(report["selected"], ["A"])
                self.assertEqual(report["coverage"]["stale"], 1)
                self.assertEqual(report["coverage"]["missing"], 1)
                self.assertEqual(report["coverage"]["verified"], 0)
                result = verify.Result("tlcsuite")
                verify.consume_case_report(result, report_path, exited.exception.code)
                self.assertIsNotNone(result.error)

    def test_expected_failure_policy(self):
        entries = [{"suite": "corpus-*", "id": "A", "reason": "known"}]
        for status, want in (("pass", "xpass"), ("fail", "xfail"), ("error", "error")):
            got = tlxlib.judge_case(tlxlib.CaseResult("A", status, {}), entries, "corpus-compile")
            self.assertEqual(got.status, want)

    def test_worker_exceptions_accept_only_their_verdict(self):
        # The multi-worker exceptions name the alternative verdict they accept:
        # a checker that reports success instead of the violation must fail.
        with open(os.path.join(tlxlib.ROOT, "tests", "expected_failures.json")) as source:
            entries = json.load(source)["expected_failures"]
        suite = "spectest-compile-w8"
        for name, kind, passing in (("FzWorkersAPropFirst", "property failure", "pass"),
                                    ("LZS2", "liveness failure", "xpass"),
                                    ("SN21", "deadlock", "pass")):
            with self.subTest(name=name), tempfile.TemporaryDirectory() as root:
                path = os.path.join(root, "report.json")
                accepted = tlxlib.judge_case(tlxlib.CaseResult(name, "fail", {"kind": kind}), entries, suite)
                self.assertEqual(accepted.status, "xfail")
                report = tlxlib.finish_cases([accepted], [name], path, suite=suite)
                self.assertEqual(report["exit_code"], 0)
                self.assertEqual(report["suite"], suite)
                false_success = tlxlib.judge_case(tlxlib.CaseResult(name, "fail", {"kind": "success"}), entries, suite)
                self.assertEqual(false_success.status, "fail")
                self.assertEqual(tlxlib.finish_cases([false_success], [name], suite=suite)["exit_code"], 1)
                passed = tlxlib.judge_case(tlxlib.CaseResult(name, "pass", {"kind": "success"}), entries, suite)
                self.assertEqual(passed.status, passing)

    def test_tlcsuite_standalone_matches_verify(self):
        with tempfile.TemporaryDirectory() as root:
            os.makedirs(os.path.join(root, "test-model"))
            with open(os.path.join(root, "test-model", "M.tla"), "w") as source:
                source.write("module")
            case = {"cls": "A", "spec": "M", "path": "", "args": [], "base": "ModelCheckerTestCase",
                    "exit": "SUCCESS", "stats": [], "ignored": False, "nonlit": False, "deadlock": False}
            success = {"result": "success", "exit": 0, "distinct": 1, "generated": 1, "depth": 1}
            report_path = os.path.join(root, "report.json")
            expected_path = os.path.join(root, "expected.json")
            for mode in ("pass", "xpass", "fail", "error", "nonzero", "timeout", "zero"):
                with self.subTest(mode=mode):
                    entries = [{"id": "A", "result": "error", "reason": "known"}] if mode == "xpass" else []
                    if mode == "timeout":
                        entries = [{"id": "A", "result": "timeout", "flaky": True, "reason": "known slow case"}]
                    with patch.object(tlcsuite, "suite_dir", return_value=(root, "commit")), \
                         patch.object(tlcsuite, "extract_cases", return_value=[] if mode == "zero" else [case]), \
                         patch.object(tlcsuite, "WORKDIR", os.path.join(root, "work")), \
                         patch.object(tlcsuite, "ORACLE", os.path.join(root, "oracle.json")), \
                         patch.object(tlcsuite, "RESULTS", os.path.join(root, "results.json")), \
                         patch.object(tlcsuite, "EXPECTED", expected_path), \
                         patch.object(tlcsuite, "tlc_identity", return_value={"jar": "digest"}), \
                         patch.object(tlcsuite, "load_expected", return_value=entries), \
                         patch.object(tlcsuite, "build_tlx", return_value=contextlib.nullcontext("fake")), \
                         patch.object(tlcsuite, "run_oracle", return_value=success), \
                         patch.object(tlcsuite, "run_tlx", side_effect=OSError("cannot execute") if mode == "error" else None,
                                      return_value={**success, "distinct": 2 if mode == "fail" else 1,
                                                    "exit": 7 if mode == "nonzero" else 0,
                                                    "result": "timeout" if mode == "timeout" else "success"}), \
                         patch.object(sys, "argv", ["tlcsuite.py", "--ids", "A", "--results-json", report_path,
                                                   *(["--update-expected"] if mode == "error" else [])]), \
                         contextlib.redirect_stdout(io.StringIO()), self.assertRaises(SystemExit) as exited:
                        tlcsuite.main()
                    result = verify.Result("tlcsuite")
                    verify.consume_case_report(result, report_path, exited.exception.code)
                    self.assertEqual(exited.exception.code, 0 if mode in ("pass", "timeout") else 1)
                    self.assertEqual(bool(result.error), bool(exited.exception.code))
                    if mode == "timeout":
                        self.assertEqual(result.case_report["counts"]["xfail"], 1)
                        self.assertEqual(result.case_report["coverage"]["verified"], 0)
                    if mode == "error":
                        with open(expected_path) as source:
                            self.assertEqual(json.load(source)["expected_failures"], [])

    def test_oracle_timeout_retry_and_identity(self):
        with tempfile.TemporaryDirectory() as root:
            spec = os.path.join(root, "M.tla")
            with open(spec, "w") as f:
                f.write("module")
            case = {"dir": root, "tla": "M.tla", "spec": "M", "path": "", "run_args": [], "base": "test", "exit": "SUCCESS", "stats": []}
            identity = {"jar": "digest", "java": "version"}
            meta = tlcsuite.oracle_metadata(case, "commit", identity)
            entry = tlcsuite.oracle_entry(meta, {"result": "timeout"}, 10, case)
            self.assertFalse(tlcsuite.oracle_ready(entry, meta))
            self.assertFalse(tlcsuite.oracle_retry(entry, meta, 10))
            self.assertTrue(tlcsuite.oracle_retry(entry, meta, 20))
            completed = tlcsuite.oracle_entry(meta, {"result": "success"}, 10, case)
            self.assertTrue(tlcsuite.oracle_ready(completed, meta))
            with open(spec, "a") as f:
                f.write("changed")
            changed = tlcsuite.oracle_metadata(case, "commit", identity)
            self.assertFalse(tlcsuite.oracle_ready(completed, changed))
            self.assertTrue(tlcsuite.oracle_retry(completed, changed, 10))
            for altered in ({**meta, "args": ["-deadlock"]}, {**meta, "tlc_identity": {"jar": "new"}},
                            {**meta, "dependency_digest": "new"}):
                self.assertFalse(tlcsuite.oracle_ready(completed, altered))
                self.assertTrue(tlcsuite.oracle_retry(completed, altered, 10))
            failed = tlcsuite.oracle_entry(meta, {"result": "collection error"}, 10, case)
            self.assertIsNone(failed["tlc"])
            self.assertTrue(tlcsuite.oracle_retry(failed, meta, 10))

    def test_oracle_launcher_failure_is_not_semantic_evidence(self):
        case = {"dir": "/scratch", "tla": "M.tla", "run_args": [], "exit": "SUCCESS", "stats": []}
        for prefix in ("", "Picked up JAVA_TOOL_OPTIONS: -Xmx512m\n", "NOTE: Picked up JDK_JAVA_OPTIONS: -Xmx512m\n"):
            with self.subTest(prefix=prefix), patch.object(tlcsuite, "run_tlc_raw", return_value=(
                    prefix + "Error: Could not find or load main class tlc2.TLC\n", 1, .1)):
                result = tlcsuite.run_oracle(case, 10)
            entry = tlcsuite.oracle_entry({}, result, 10, case)
            self.assertFalse(tlcsuite.oracle_ready(entry, {}))
            self.assertIsNone(entry["tlc"])
            self.assertTrue(tlcsuite.oracle_retry(entry, {}, 10))

    def test_spectest_includes(self):
        # (tlapm/library is not passed: its Bags.tla would shadow the
        # standard Bags.)
        self.assertEqual(spectest.INCLUDES[1::2], [os.path.join(tlxlib.ROOT, "third_party", d) for d in ("community", "apalache")])

    def test_spectest_workers(self):
        self.assertEqual([spectest.extra_workers(e.split()) for e in ("", "-compile", "-workers 8", "-compile -workers 3", "-workers auto", "-workers")], [1, 1, 8, 3, 0, 1])
        res = lambda result, violated=None, d=5, g=9, depth=3: {"result": result, "violated": violated, "distinct": d, "generated": g, "depth": depth}
        cw = lambda want, got, sim=False: spectest.compare_workers("S1", want, got, sim)[0]
        # An early stop counts whatever the workers had done: not compared.
        self.assertEqual(cw(res("safety failure", "Inv"), res("safety failure", "Inv", d=7, g=12)), [])
        self.assertEqual(cw(res("deadlock"), res("deadlock", g=11, depth=19)), [])
        # The verdict and the violated name still are.
        self.assertEqual(cw(res("safety failure", "Inv"), res("safety failure", "Other")), ["violated"])
        self.assertEqual(cw(res("success"), res("deadlock")), ["result"])
        # A complete run matches TLC's counts and depth exactly.
        self.assertEqual(cw(res("success"), res("success")), [])
        self.assertEqual(cw(res("success"), res("success", d=6)), ["distinct"])
        self.assertEqual(cw(res("success"), res("success", depth=4)), ["depth"])
        # TLC's evaluation error may lose the race to a violation, not to success.
        self.assertEqual(cw(res("error"), res("safety failure", "Inv")), [])
        self.assertEqual(cw(res("error"), res("success")), ["result"])
        # A simulation only has a verdict.
        self.assertEqual(cw(res("success"), res("success", g=99), sim=True), [])
        self.assertEqual(cw(res("success"), res("safety failure", "Inv"), sim=True), ["result", "violated"])
        # Specs reading TLC registers or statistics depend on the schedule.
        self.assertTrue(spectest.schedule_dependent("M3"))
        self.assertFalse(spectest.schedule_dependent("S6"))
        self.assertEqual(spectest.compare_workers("M3", res("success"), res("postcondition failure", "Post"), False)[0], [])

    def test_fuzzer_reports(self):
        runner = fuzz_expr.Runner(None, "/unused")
        runner.note_coverage("compile", "IR: 2/3 actions lowered, 1 fully typed; IR nodes 20 (4 boxed, 5 interpreter)\nnative code: 1/3 actions, 2/4 invariants")
        self.assertEqual(runner.stats["compile"], {"native_actions": 1, "actions": 6, "native_invs": 2, "invs": 4,
                                                  "ir_nodes": 20, "ir_boxed": 4, "ir_interp": 5, "lowered": 2})
        self.assertEqual(coverage.ACTION_REPORT.search("2/3 actions lowered, 1 fully typed; IR nodes 20 (4 boxed, 5 interpreter)").groups(),
                         ("2", "3", "1", "20", "4", "5"))
        self.assertEqual(coverage.PRED_REPORT.search("IR action properties: 2 lowered; IR nodes 9 (1 boxed, 2 interpreter)").groups(),
                         ("action properties", "2", "9", "1", "2"))
        # the action report must not match the predicate lines (and vice versa)
        self.assertIsNone(coverage.ACTION_REPORT.search("IR invariants: 2 lowered; IR nodes 9 (1 boxed, 2 interpreter)"))

    def test_expected_failures(self):
        entries = [{"suite": "spec*", "id": "A*", "result": "error", "reason": "known"},
                   {"suite": "spec*", "id": "B*", "flaky": True, "reason": "random"}]
        result = verify.Result("spectest")
        result.failed = {"A1": ("error", "line"), "A2": ("timeout", "line2"), "B1": ("success", "line3")}
        result.passed = ["A3", "B2"]
        verify.classify(result, entries)
        self.assertEqual(result.expected, [("A1", "known"), ("B1", "random")])
        self.assertEqual(result.unexpected, [("A2", "line2")])
        self.assertEqual(result.fixed, [("A3", "known")])
        self.assertTrue(verify_compare.is_flaky(entries[1:], "spectest", "B1", ["success"]))
        self.assertFalse(verify_compare.is_flaky(entries[1:], "corpus", "B1", ["success"]))

    def test_log_contract(self):
        with tempfile.NamedTemporaryFile(mode="w+") as log:
            log.write("PASS A1 tlc={} tlx={'result': 'success', 'distinct': 5}\n"
                      "FAIL Model tlc=error tlx=timeout/None/None/None (0s vs 1s)\n"
                      "PASS Sim tlc=success tlx=success/None/12/None (0s vs 1s)\n"
                      "test example::test ... ok\n")
            log.flush()
            self.assertEqual(verify_compare.outcomes(log.name), {"A1": "{'result': 'success', 'distinct': 5}",
                                                               "Model": "timeout/None/None/None", "Sim": "success/None/*/None",
                                                               "example::test": "ok"})

    def test_bench_builds_release(self):
        with patch.object(bench, "build_tlx") as build:
            bench.build_release("p-")
            build.assert_called_once_with(profile="release", prefix="p-")
        # An older revision's tlxlib (cloud_verify.py --bench): no `profile`, release by default.
        def old(copy=True, *, release=True, prefix="tlx-run-", build=True):
            return prefix
        with patch.object(bench, "build_tlx", side_effect=old):
            self.assertEqual(bench.build_release("p-"), "p-")

    def bench_compare(self, left, right, metric="wall"):
        with tempfile.TemporaryDirectory() as root:
            paths = [os.path.join(root, name + ".json") for name in ("a", "b")]
            for path, runs in zip(paths, (left, right)):
                with open(path, "w") as out:
                    json.dump({"runs": runs}, out)
            output = io.StringIO()
            args = SimpleNamespace(a=paths[0], b=paths[1], metric=metric, threshold=.05, min_delta=.05, max_noise=.05)
            with patch("sys.stdout", output), self.assertRaises(SystemExit) as exit:
                bench.cmd_compare(args)
            return exit.exception.code, output.getvalue()

    @staticmethod
    def bench_run(walls, **extra):
        return {"tier": "medium", "walls": walls, "cpu": walls, "distinct": 10, "result": "success", **extra}

    def test_bench_compare_pass(self):
        code, output = self.bench_compare({"M": self.bench_run([1, 1, 1])}, {"M": self.bench_run([1.01, 1.02, 1.01])})
        self.assertEqual(code, 0)
        self.assertIn("PASS", output)
        self.assertIn("noise", output)

    def test_bench_compare_regression(self):
        code, output = self.bench_compare({"M": self.bench_run([1, 1, 1])}, {"M": self.bench_run([2, 2, 2])})
        self.assertEqual(code, 1)
        self.assertIn("REGRESSION", output)

    def test_bench_compare_noise_inconclusive(self):
        for walls in ([2, 10, 10], [1, 1, 10]):
            with self.subTest(walls=walls):
                code, output = self.bench_compare({"M": self.bench_run([1, 1, 1])}, {"M": self.bench_run(walls)})
                self.assertEqual(code, 2)
                self.assertIn("INCONCLUSIVE", output)
                self.assertIn("noise", output)
                self.assertIn("re-run", output)

    def test_bench_compare_missing_samples(self):
        good = {"M": self.bench_run([1, 1, 1])}
        cases = [{}, {"M": self.bench_run([])}, {"M": self.bench_run([1])}, {"M": self.bench_run([1, 1])},
                 {"M": self.bench_run([1, 1, 1, 1])}, {"M": self.bench_run([1, 0, 1])},
                 {"M": self.bench_run([1, None, 1])}, {"M": self.bench_run([1, float("nan"), 1])},
                 {"M": self.bench_run([1, 1, 1], result="timeout")},
                 {"M": self.bench_run([1, 1, 1], result="error")},
                 {"M": self.bench_run([1, 1, 1], cpu=[1, None, 1])}]
        for incomplete in cases:
            for left, right in ((good, incomplete), (incomplete, good)):
                with self.subTest(left=left, right=right):
                    code, output = self.bench_compare(left, right, metric="cpu")
                    self.assertEqual(code, 2)
                    self.assertIn("INCONCLUSIVE", output)
        code, output = self.bench_compare({}, {})
        self.assertEqual(code, 2)
        self.assertIn("INCONCLUSIVE", output)

    def test_bench_compare_counts_override_noise(self):
        code, output = self.bench_compare({"M": self.bench_run([1, 1, 1])},
                                          {"M": self.bench_run([2, 10, 10], distinct=11)})
        self.assertEqual(code, 1)
        self.assertIn("DISTINCT", output)

    def test_bench_compare_regression_precedes_inconclusive(self):
        code, output = self.bench_compare({"M": self.bench_run([1, 1, 1]), "N": self.bench_run([1, 1, 1])},
                                          {"M": self.bench_run([2, 2, 2]), "N": self.bench_run([2, 10, 10])})
        self.assertEqual(code, 1)
        self.assertIn("1 regression(s), 0 improvement(s), 1 inconclusive timing(s)", output)

    def test_bench_compare_cpu_and_absolute_threshold(self):
        left = {"M": self.bench_run([1, 1, 1])}
        right = {"M": self.bench_run([2, 10, 10], cpu=[1, 1, 1])}
        code, output = self.bench_compare(left, right, metric="cpu")
        self.assertEqual(code, 0)
        self.assertIn("PASS", output)
        code, output = self.bench_compare({"M": self.bench_run([.01] * 3)}, {"M": self.bench_run([.02] * 3)})
        self.assertEqual(code, 0)
        code, output = self.bench_compare({"M": self.bench_run([2] * 3)}, left)
        self.assertEqual(code, 0)
        self.assertIn("1 improvement(s)", output)

    def test_bench_fixed_stress_selection(self):
        # The `bench/<name>` id family resolves to a configuration file in the
        # measurement store, which a checkout of the published sources does not
        # carry (docs/benchmarking.md section 6.2), so the test owns the one
        # file it reads: it asserts the resolution *and* the property read, and
        # the store is neither. A checkout path compiled into `stress_models`
        # instead of the root it is handed fails here, rather than passing on
        # data the contributor happens to have on disk.
        with tempfile.TemporaryDirectory() as root:
            cfg = os.path.join(root, "bench", "stress", "ClockSettles.cfg")
            os.makedirs(os.path.dirname(cfg))
            with open(cfg, "w") as source:
                source.write("SPECIFICATION Spec\nPROPERTY ClockSettles\n")
            with patch.object(bench_models, "ROOT", root), \
                    patch.object(bench_models, "load_oracle", return_value={}):
                selected = bench_models.select(["stress"], 1)["stress"]
                self.assertEqual(selected, ["bench/ClockSettles", "MultiPaxos-SMR/MultiPaxos_MC"])
                models = bench_models.oracle(selected)
            clock = models["bench/ClockSettles"]
            self.assertEqual(clock["cfg"], cfg)
            with open(clock["cfg"]) as source:
                self.assertIn("PROPERTY ClockSettles", source.read())
            self.assertIn("tlaplus-tests/test-model/examples/", clock["tla"])
            self.assertTrue(models["MultiPaxos-SMR/MultiPaxos_MC"]["cfg"].endswith("MultiPaxos_MC.cfg"))

    def test_verify_profile_args(self):
        with tempfile.TemporaryDirectory() as root:
            os.makedirs(os.path.join(root, "scripts"))
            ctx = SimpleNamespace(wt=root, profile="release")
            for script in ("spectest.py", "difftest.py"):
                with open(os.path.join(root, "scripts", script), "w") as source:
                    source.write("add_profile_args(ap)\n")
                self.assertEqual(verify.profile_args(ctx, script), ["--profile", "release"])
                # A checkout from before --profile: its old defaults.
                with open(os.path.join(root, "scripts", script), "w") as source:
                    source.write("ap.add_argument('--release')\n")
            self.assertEqual(verify.profile_args(ctx, "spectest.py"), [])
            self.assertEqual(verify.profile_args(ctx, "difftest.py"), ["--release"])

    def test_verify_external_suites(self):
        suites = {s[0]: s for s in verify.SUITES}
        with tempfile.TemporaryDirectory() as root:
            os.makedirs(os.path.join(root, "scripts"))
            with open(os.path.join(root, "scripts", "difftest.py"), "w") as source:
                source.write("add_profile_args(ap)\n")
            ctx = SimpleNamespace(wt=root, profile="release", env={}, cache=None, logdir=root, jobs=16, tier="quick",
                                  verbose=False, filter="", quick_corpus=["A/B"])

            def run(name, filter=""):
                ctx.filter = filter
                calls = []
                with patch.object(verify, "run_logged", side_effect=lambda cmd, *_: calls.append(cmd) or (0, "0/0 passed (this run)\n")):
                    _, _, kind, args, env = suites[name]
                    verify.run_suite(name, kind, args, env, ctx)
                return calls

            [cmd] = run("corpus-ext")
            # Its own selection: no quick-corpus ids, the filter ext/.
            self.assertNotIn("--ids", cmd)
            self.assertEqual(cmd[cmd.index("--filter") + 1], "ext/")
            [cmd] = run("corpus-ext-large", "ext/ccf/")
            self.assertEqual([cmd[i + 1] for i, a in enumerate(cmd) if a == "--filter"], ["ext/ccf/"])
            self.assertEqual(cmd[cmd.index("--oracle") + 1], "tlc-ext-large")
            self.assertEqual(cmd[cmd.index("-j") + 1], "1")
            self.assertEqual(cmd[cmd.index("--tiers") + 1], "medium,large")
            # A filter of the Examples corpus: the external suites run nothing.
            self.assertEqual(run("corpus-ext", "DieHard"), [])
            [cmd] = run("corpus-compile", "DieHard")
            self.assertEqual(cmd[cmd.index("--filter") + 1], "DieHard")

    def test_verify_cargo_preflight(self):
        with tempfile.TemporaryDirectory() as root:
            with open(os.path.join(root, "Cargo.toml"), "w") as manifest:
                manifest.write("[profile.test-release]\n")
            ctx = SimpleNamespace(env={}, cache=None, logdir=root, wt=root, jobs=3, verbose=False)
            with patch.object(verify, "run_logged", side_effect=[(0, "python ok"), (0, "test unit ... ok\n")]) as run:
                result = verify.run_suite("cargo-test", "cargo-test", [], {}, ctx)
            self.assertIsNone(result.error)
            self.assertEqual(run.call_args_list[0].args[0], [sys.executable, "-m", "unittest", "discover", "-s", "scripts", "-p", "test_*.py"])
            self.assertEqual(run.call_args_list[1].args[0][:4], ["cargo", "test", "--profile", "test-release"])
            with patch.object(verify, "run_logged", return_value=(1, "failed")) as run:
                self.assertIn("Python driver tests failed", verify.run_suite("cargo-test", "cargo-test", [], {}, ctx).error)
                self.assertEqual(run.call_count, 1)

    def test_verify_clippy_gate(self):
        # The build suite runs clippy only for revisions that declare [workspace.lints]; its warnings fail verify.
        with tempfile.TemporaryDirectory() as root:
            ctx = SimpleNamespace(env={}, cache=None, logdir=root, wt=root, jobs=3, verbose=False)
            self.assertFalse(verify.has_workspace_lints(root))
            with open(os.path.join(root, "Cargo.toml"), "w") as manifest:
                manifest.write("[workspace]\n")
            self.assertFalse(verify.has_workspace_lints(root))
            with patch.object(verify, "run_logged", return_value=(0, "")) as run:
                verify.run_suite("build", "build", [], {}, ctx)
            self.assertEqual([c.args[0][:2] for c in run.call_args_list], [["cargo", "build"]])
            with open(os.path.join(root, "Cargo.toml"), "w") as manifest:
                manifest.write("[workspace]\n\n[workspace.lints.clippy]\n")
            self.assertTrue(verify.has_workspace_lints(root))
            outs = [(0, ""), (0, "warning: manual implementation of `.is_multiple_of()`\nwarning: `tlx-cli` (bin \"tlx\") generated 1 warning\n")]
            with patch.object(verify, "run_logged", side_effect=outs) as run:
                result = verify.run_suite("build", "build", [], {}, ctx)
            self.assertEqual(run.call_args_list[1].args[0][:6], ["cargo", "clippy", "--workspace", "--release", "--all-targets", "-j"])
            self.assertEqual(result.warnings, ["warning: manual implementation of `.is_multiple_of()`"])

    def test_bench_usage(self):
        result = tlxlib.ProcResult("Model checking completed. No error has been found.\n", "", 0, 1.25,
                                   rusage=SimpleNamespace(ru_utime=.5, ru_stime=.25, ru_maxrss=1 << 20))
        with patch.object(bench, "run_proc", return_value=result) as run:
            measured = bench.tlx({"tla": "Spec.tla", "cfg": "Spec.cfg"}, [], 10, exe="private-tlx")
        self.assertEqual(measured["result"], "success")
        self.assertEqual(measured["cpu_s"], .75)
        # (By absolute path: a scratch model runs in another directory.)
        self.assertEqual(run.call_args.args[0][0], os.path.abspath("private-tlx"))
        self.assertTrue(run.call_args.kwargs["rusage"])

    def test_bench_table_tier_columns(self):
        cols = bench.table_columns("TLC 1w (baseline)", 16)
        self.assertEqual(cols[7:10], ["tlx jit 1w", "tlx c 1w", "tlx compile 1w cold"])
        line = bench.render_row(("M/A", 100, 10.0, 2.0, 5.0, 1.0, 0.5, 1.25, 0.8, None, True))
        self.assertEqual(bench.table_cells(line), ["M/A", "100", "10.00", "2.00", "5.00", "1.00", "0.50", "1.25", "0.80", "-", "10.0×", "4.0×", "✓"])
        text = "\n".join(["# t", "", "| " + " | ".join(cols) + " |", "|---|", line, "", "not a row"])
        self.assertEqual(bench.table_header(text), cols)
        self.assertEqual(bench.parse_table(text), [("M/A", line)])
        # Rows kept from a table without the tier columns (and another TLC 1w source) get "-" there.
        old_cols = ["model", "distinct", "TLC 1w (oracle, -j 4)", "TLC 16w", "tlx interp 1w", "tlx compile 1w", "tlx compile 16w",
                    "speedup (1w)", "speedup (16w)", "counts"]
        old = [("M/B", "| M/B | 7 | 3.00 | 1.00 | 2.00 | 0.30 | 0.10 | 10.0× | 10.0× | ✓ |")]
        (k, up), = bench.upgrade_rows(old, old_cols, cols)
        self.assertEqual(k, "M/B")
        self.assertEqual(bench.table_cells(up), ["M/B", "7", "3.00", "1.00", "2.00", "0.30", "0.10", "-", "-", "-", "10.0×", "10.0×", "✓"])
        self.assertIs(bench.upgrade_rows(old, cols, cols), old)
        self.assertEqual(bench.merge_rows(bench.upgrade_rows(old, old_cols, cols), {"M/A": line}, ["M/A"]), [up, line])

    def test_bench_external_models(self):
        sel = bench_models.external_selection("small,medium")
        self.assertEqual(sorted(sel), ["ext-medium", "ext-small"])
        self.assertTrue(all(k.startswith("ext/") for ks in sel.values() for k in ks))
        medium = sel["ext-medium"][0]
        self.assertEqual(bench_models.external_selection("small,medium", medium), {"ext-medium": [medium]})
        # A model without a TLC oracle result comes from the manifest, with an empty one.
        with patch.object(bench_models, "load_oracle", return_value={}):
            d = bench_models.oracle([medium])
        self.assertEqual((d[medium]["tlc"], d[medium]["tier"]), ({}, "medium"))
        self.assertTrue(d[medium]["cfg"].endswith(".cfg"))
        with patch.object(bench_models, "load_oracle", return_value={}):
            self.assertEqual(bench_models.oracle(), {})
        # The cloud runs upload the external trees.
        from cloud import cloud_common
        self.assertIn("--include=/external/***", cloud_common.THIRD_PARTY_FILTER)
        self.assertLess(cloud_common.THIRD_PARTY_FILTER.index("--include=/external/***"), cloud_common.THIRD_PARTY_FILTER.index("--exclude=*"))

    def test_bench_report_markdown(self):
        run = lambda tier, model, mode, w, t, result="success", d=10: {
            "tier": tier, "model": model, "mode": mode, "workers": w, "min": t, "walls": [t], "cpu": [t], "result": result, "distinct": d}
        rs = [run("ext-small", "A", "tlc", 1, 8.0), run("ext-small", "A", "tlc", 16, 2.0), run("ext-small", "A", "interp", 1, 4.0),
              run("ext-small", "A", "compile", 1, 4.0), run("ext-small", "A", "compile", 16, 0.5),
              # A violation: the counts at the stop are not compared, the verdict is.
              run("ext-medium", "B", "tlc", 1, 100.0, "deadlock", 7), run("ext-medium", "B", "compile", 1, 10.0, "deadlock", 9),
              run("ext-medium", "B", "compile", 16, 1.0, "safety failure", 9),
              run("ext-medium", "C", "tlc", 1, 50.0, "timeout"), run("ext-medium", "C", "compile", 1, 5.0),
              # TLC 1w timed out: the counts are checked against TLC Nw.
              run("ext-large", "D", "tlc", 1, 50.0, "timeout"), run("ext-large", "D", "tlc", 16, 20.0), run("ext-large", "D", "compile", 16, 2.0)]
        h = {"runs": {f"{r['tier']}:{r['model']}:{r['mode']}:{r['workers']}w": r for r in rs}}
        self.assertTrue(bench.counts_check(rs[3], rs[0]))
        self.assertFalse(bench.counts_check({**rs[3], "distinct": 11}, rs[0]))
        self.assertTrue(bench.counts_check(rs[6], rs[5]))
        self.assertFalse(bench.counts_check(rs[7], rs[5]))
        self.assertIsNone(bench.counts_check(rs[9], rs[8]))
        out = bench.report_markdown(h)
        rows = {bench.table_cells(l)[0]: bench.table_cells(l) for l in out if l.startswith("| ") and not l.startswith("| model")}
        self.assertEqual(rows["A"][1:], ["ext-small", "success", "10", "8.00", "2.00", "4.00", "4.00", "0.50", "2.0×", "2.0×", "4.0×", "✓"])
        self.assertEqual(rows["B"][-1], "✗")
        self.assertEqual(rows["C"][4:8] + rows["C"][-1:], [">50", "-", "-", "5.00", "?"])
        # TLC timed out, tlx finished: a lower bound.
        self.assertEqual(rows["C"][10], ">10.0×")
        self.assertEqual(rows["D"][2:6] + rows["D"][-2:], ["success", "10", ">50", "20.00", "10.0×", "✓"])
        self.assertEqual(rows["tier ext-medium"][1:4], ["2", "-", "10.0×"])
        self.assertEqual(rows["all"][1:5], ["4", "2.0×", f"{(2.0 * 10.0) ** .5:.1f}×", f"{(4.0 * 10.0) ** .5:.1f}×"])
        self.assertEqual(rows["TLC 1w >= 60 s"][1], "1")
        self.assertIn("A (2.0×)", out[-3])
        self.assertNotIn("B (", out[-3])
        self.assertIn("16w is less than 3×", out[-1])
        self.assertNotIn("A (", out[-1])
        # TLC's multi-worker counts differing from its own 1-worker ones are noted, not a tlx failure.
        rs += [run("ext-small", "E", "tlc", 1, 8.0), run("ext-small", "E", "tlc", 16, 2.0, d=11), run("ext-small", "E", "compile", 16, 0.5)]
        out = bench.report_markdown({"runs": {f"{r['tier']}:{r['model']}:{r['mode']}:{r['workers']}w": r for r in rs}})
        rows = {bench.table_cells(l)[0]: bench.table_cells(l) for l in out if l.startswith("| ") and not l.startswith("| model")}
        self.assertEqual(rows["E"][-1], "✓")
        self.assertIn("E (success 11 vs success 10)", out[-1])

    def test_bench_cold_run(self):
        seen = {}

        def fake(m, args, timeout, exe=None, env=None):
            seen.update(env)
            os.makedirs(os.path.join(env["TLX_CACHE"], "slot"))
            open(os.path.join(env["TLX_CACHE"], "slot", "build.lock"), "w").close()
            return {"result": "success", "wall_s": 1.0}
        with patch.object(bench, "tlx", side_effect=fake):
            self.assertEqual(bench.tlx_cold({}, ["-compile"], 10, env={"TLX_JIT": "tier"})["wall_s"], 1.0)
        self.assertEqual(seen["TLX_JIT"], "tier")
        # A fresh cache per run, removed afterwards (after waiting for the unlocked build).
        self.assertFalse(os.path.exists(seen["TLX_CACHE"]))

    def test_bench_scale_helpers(self):
        self.assertEqual(bench_machine.scale_workers("16,1,max, 64", 192), [1, 16, 64, 192])
        topo = bench_machine.parse_lscpu("CPU(s):  192\nThread(s) per core:  2\nCore(s) per socket:  96\nSocket(s):  1\n"
                                 "NUMA node(s):  2\nNUMA node0 CPU(s):  0-47,96-143\nNUMA node1 CPU(s):  48-95,144-191\n")
        self.assertEqual((topo["cpus"], topo["threads_per_core"], topo["cores_per_socket"], topo["sockets"], topo["numa_nodes"]),
                         ("192", "2", "96", "1", "2"))
        self.assertEqual(topo["numa_cpus"], {"node0": "0-47,96-143", "node1": "48-95,144-191"})
        self.assertEqual(sorted(bench_models.scale_models(["bench/MCLamportMutex_clock14"])), ["bench/MCLamportMutex_clock14"])
        # The hand-written list's ids are well-formed `bench/<name>` keys that
        # `scale_models` resolves to `bench/scaling/<name>.cfg`; that the file
        # is on disk is a fact about the measurement store, which the published
        # sources do not carry (docs/testing.md, "Python driver tests").
        for k in bench_models.SCALE_CFGS:
            self.assertTrue(k.startswith("bench/") and k.split("/", 1)[1], k)

    def test_bench_scale_report(self):
        run = lambda t, d=50, result="success": {"min": t, "result": result, "distinct": d}
        tlc = lambda t, d=50: {"wall_s": t, "result": "success", "distinct": d}
        h = {"models": {
            "A": {"warmup": run(1.0), "tlx": {"1": run(64.0), "4": run(20.0)}, "tlc": {"1": tlc(640.0), "4": tlc(320.0)}},
            "B": {"warmup": run(1.0), "tlx": {"1": run(10.0), "4": run(5.0, d=51)}, "tlc": {"4": tlc(50.0)}},
            "C": {"tlx": {"1": run(1.0)}, "tlc": {}},
            "D": {"tlx": {"1": run(1.0, d=9)}, "tlc": {}, "reference": {"distinct": 9, "source": "tlc-x"}},
        }}
        self.assertEqual([bench.scale_counts(h["models"][k]) for k in "ABCD"], ["✓", "✗", "?", "✓"])
        # Unfinished runs (timed out, killed) neither count nor fail.
        unfinished = {"tlx": {"1": run(1.0), "4": {"result": "timeout", "min": 9.0}}, "tlc": {"4": {"result": "killed", "wall_s": 3.0}}}
        self.assertEqual(bench.scale_counts(unfinished), "?")
        self.assertEqual(bench.scale_counts({**unfinished, "tlc": {**unfinished["tlc"], "1": tlc(9.0)}}), "✓")
        self.assertEqual(bench.scale_counts({**unfinished, "tlc": {"1": {**tlc(9.0), "result": "deadlock"}}}), "✗")
        out = bench.scale_report(h)
        rows = {(i // 5, bench.table_cells(l)[2]): bench.table_cells(l)[3:5] for i, l in enumerate(out[2:22])}
        self.assertEqual(rows[0, "tlx s"], ["64.00", "20.00"])
        self.assertEqual(rows[0, "tlx speedup over TLC"], ["10.0×", "16.0×"])
        self.assertEqual(rows[0, "tlx efficiency"], ["100%", "80%"])
        self.assertEqual(rows[0, "TLC efficiency"], ["100%", "50%"])
        # B has no TLC 1-worker run: TLC's efficiency is relative to its smallest count.
        self.assertEqual(rows[1, "TLC efficiency (vs 4w)"], ["-", "100%"])
        self.assertEqual(rows[1, "tlx speedup over TLC"], ["-", "10.0×"])
        gm = {bench.table_cells(l)[0]: bench.table_cells(l)[1:] for l in out[23:]}
        self.assertEqual(gm["tlx speedup over TLC"], ["10.0×", f"{(16.0 * 10.0) ** .5:.1f}×"])
        self.assertEqual(gm["TLC efficiency (models with a TLC 1w run)"], ["100%", "50%"])


def load_script(filename):
    """A script whose file name is not an identifier (fetch-external.py)."""
    spec = importlib.util.spec_from_file_location(filename.replace("-", "_").removesuffix(".py"), os.path.join(tlxlib.ROOT, "scripts", filename))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


class ExternalCorpora(unittest.TestCase):
    """corpus/external.json, scripts/fetch-external.py, the external models of scripts/corpus.py."""

    @classmethod
    def setUpClass(cls):
        cls.fx = load_script("fetch-external.py")
        with open(os.path.join(tlxlib.ROOT, "corpus", "external.json")) as source:
            cls.manifest = json.load(source)

    def tarball(self, members):
        buf = io.BytesIO()
        with tarfile.open(fileobj=buf, mode="w:gz") as tar:
            for name, data in members.items():
                info = tarfile.TarInfo(name)
                if data is None:
                    info.type, info.linkname = tarfile.SYMTYPE, "/etc/passwd"
                    tar.addfile(info)
                else:
                    info.size = len(data)
                    tar.addfile(info, io.BytesIO(data))
        return buf.getvalue()

    def test_manifest(self):
        repos = {**self.manifest["repos"], **self.manifest["suites"]}
        for name, repo in repos.items():
            self.assertRegex(repo["commit"], r"^[0-9a-f]{40}$", name)
            self.assertTrue(repo.get("license") and repo.get("attribution"), name)
            self.assertIn(repo.get("fetch", "tarball"), ("tarball", "files"), name)
            if repo.get("fetch") == "files":
                self.assertTrue(repo.get("include"), name)
        ids = set()
        for m in self.manifest["models"]:
            self.assertIn(m["repo"], self.manifest["repos"], m["name"])
            self.assertIn(m["tier"], corpus.EXTERNAL_TIERS, m["name"])
            self.assertTrue(m["tla"].endswith(".tla") and m["cfg"].endswith(".cfg"), m["name"])
            self.assertNotIn((m["repo"], m["name"]), ids)
            ids.add((m["repo"], m["name"]))
            # A model without a cfg or wrapper of ours must not name a file that is not upstream's.
            self.assertFalse(os.path.isabs(m["tla"]) or os.path.isabs(m["cfg"]), m["name"])
        # Our own files live below corpus/external/<repo>/ for a repository of the manifest.
        overlay = os.path.join(tlxlib.ROOT, "corpus", "external")
        for name in os.listdir(overlay):
            self.assertIn(name, self.manifest["repos"])

    def test_unpack_tarball(self):
        data = self.tarball({"repo-abc/": None, "repo-abc/root/a.tla": b"A", "repo-abc/root/sub/b.cfg": b"B", "repo-abc/other/c.tla": b"C",
                             "repo-abc/root/link": None, "repo-abc/root/../../escape": b"X"})
        with tempfile.TemporaryDirectory() as tmp:
            self.assertEqual(self.fx.unpack_tarball(data, tmp, "root"), 2)
            self.assertEqual(sorted(os.listdir(tmp)), ["a.tla", "sub"])
        with tempfile.TemporaryDirectory() as tmp:
            self.assertEqual(self.fx.unpack_tarball(data, tmp, "", ["other"]), 1)
            self.assertEqual(os.listdir(tmp), ["other"])
        self.assertIsNone(self.fx.safe_member("a/../b"))

    def test_overlay(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(self.fx, "OVERLAY", os.path.join(tmp, "overlay")):
            os.makedirs(os.path.join(tmp, "overlay", "r", "d"))
            with open(os.path.join(tmp, "overlay", "r", "d", "x.cfg"), "w") as f:
                f.write("ours")
            dest = os.path.join(tmp, "tree")
            os.makedirs(os.path.join(dest, "d"))
            with open(os.path.join(dest, "d", "x.cfg"), "w") as f:
                f.write("upstream")
            digest = self.fx.apply_overlay("r", dest)
            with open(os.path.join(dest, "d", "x.cfg")) as f:
                self.assertEqual(f.read(), "ours")
            self.assertEqual(digest, self.fx.apply_overlay("r", dest))
            self.assertEqual(self.fx.apply_overlay("none", dest), self.fx.apply_overlay("none2", dest))

    def test_external_models(self):
        ms = corpus.external_models(("small", "medium", "large", "huge"))
        self.assertEqual(len(ms), len(self.manifest["models"]))
        self.assertTrue(all(m["id"].startswith("ext/") and m["id"].count("/") == 2 for m in ms))
        self.assertTrue(all(m["tla"].startswith(corpus.EXTERNAL) and m["cfg"].startswith(corpus.EXTERNAL) for m in ms))
        # The default selection never has the large and huge models.
        default = {m["id"] for m in corpus.external_models()}
        self.assertTrue(all(m["tier"] in ("small", "medium") for m in ms if m["id"] in default))
        self.assertTrue(default <= {m["id"] for m in ms})

    def test_select(self):
        args = lambda **kw: SimpleNamespace(**{"source": "examples", "tier": "", "repos": "", "name": "", "min_runtime": 0, "max_runtime": 10, **kw})
        ms, name = corpus.select(args(source="external"))
        self.assertEqual(name, "tlc-ext")
        self.assertTrue(all(m["id"].startswith("ext/") for m in ms))
        self.assertEqual(corpus.select(args(source="external", tier="large"))[1], "tlc-ext-large")
        self.assertEqual(corpus.select(args(source="external", tier="small", name="mine"))[1], "mine")
        with patch.object(corpus, "models", return_value=[]) as models:
            self.assertEqual(corpus.select(args()), ([], "tlc"))
            self.assertEqual(models.call_args.args, (10, 0))
            self.assertEqual(corpus.select(args(tier="large")), ([], "tlc-large"))
            self.assertEqual(models.call_args.args, (700, 61))
            self.assertEqual(corpus.select(args(tier="huge")), ([], "tlc-huge"))
            self.assertEqual(models.call_args.args, (corpus.HUGE_MAX_RUNTIME, corpus.HUGE_MIN_RUNTIME))
        # Unknown runtimes (10**9 s) are not in the huge tier.
        self.assertLess(corpus.HUGE_MAX_RUNTIME, corpus.secs("unknown"))
        self.assertGreater(corpus.secs("00:11:41"), 700)

    def test_load_oracle_external_only_by_name(self):
        with tempfile.TemporaryDirectory() as tmp:
            os.makedirs(os.path.join(tmp, "corpus", "out"))
            for name, key in (("tlc", "A/B"), ("tlc-ext", "ext/r/m")):
                with open(os.path.join(tmp, "corpus", "out", name + ".json"), "w") as f:
                    json.dump({key: {"id": key, "tla": "third_party/x.tla"}}, f)
            with patch.object(tlxlib, "ROOT", tmp):
                self.assertEqual(sorted(tlxlib.load_oracle()), ["A/B"])
                self.assertEqual(sorted(tlxlib.load_oracle("", "A/B")), ["A/B"])
                self.assertEqual(sorted(tlxlib.load_oracle("ext/")), ["ext/r/m"])
                self.assertEqual(sorted(tlxlib.load_oracle("", "A/B,ext/r/m")), ["A/B", "ext/r/m"])
            with open(os.path.join(tmp, "corpus", "out", "tlc-ext-large.json"), "w") as f:
                json.dump({"ext/r/big": {"id": "ext/r/big", "tla": "third_party/y.tla"}}, f)
            with patch.object(tlxlib, "ROOT", tmp):
                self.assertEqual(sorted(tlxlib.load_oracle("ext/", oracles="tlc-ext-large")), ["ext/r/big", "ext/r/m"])
                self.assertEqual(sorted(tlxlib.load_oracle("", oracles=["tlc-ext-large"])), ["A/B", "ext/r/big"])


class TlcSuite(unittest.TestCase):
    JUNIT = """package tlc2;
public class %s extends ModelCheckerTestCase {
	public %s() { super("Spec", "dir", new String[] { "-config", "X.tla", "-workers", "1" }, EC.ExitStatus.VIOLATION_SAFETY); }
	@Test public void testSpec() { assertTrue(recorder.recorded(EC.TLC_STATS)); assertTrue(recorder.recordedWithStringValues(EC.TLC_STATS, "10", "7", "0")); }
	@Override protected boolean checkDeadLock() { return true; }
}
"""

    def tree(self, tmp):
        for pkg, cls in (("a", "OneTest"), ("b", "Dup"), ("c", "Dup")):
            os.makedirs(os.path.join(tmp, "test", pkg), exist_ok=True)
            with open(os.path.join(tmp, "test", pkg, cls + ".java"), "w") as f:
                f.write(self.JUNIT % (cls, cls))
        with open(os.path.join(tmp, "test", "a", "Other.java"), "w") as f:
            f.write("public class Other extends Something { }\n")
        with open(os.path.join(tmp, "test", "a", "Susp.java"), "w") as f:
            f.write('@Ignore public class Susp extends PCalModelCheckerTestCase { public Susp() { super("P", "pcal", new String[] { "-wf" }); } }\n')
        with open(os.path.join(tmp, "test", "a", "Lit.java"), "w") as f:
            f.write('public class Lit extends ModelCheckerTestCase { public Lit() { super("L", new String[] { ARG, "-x" }); } }\n')
        with open(os.path.join(tmp, "test", "a", "Sep.java"), "w") as f:
            f.write('public class Sep extends ModelCheckerTestCase { public Sep() { super("S", new String[] { "-dumpTrace", "json", "states" + File.separator + "S.json" /* comment */ }); } }\n')
        with open(os.path.join(tmp, "test", "a", "DynPath.java"), "w") as f:
            f.write('public class DynPath extends ModelCheckerTestCase { public DynPath() { super("D", new String[] { "-dumptrace", "tlcaction", "states" + FileUtil.separator + DynPath.class.getCanonicalName() + ".tla" }); } }\n')
        with open(os.path.join(tmp, "test", "a", "QuotedDelims.java"), "w") as f:
            f.write('public class QuotedDelims extends ModelCheckerTestCase { public QuotedDelims() { super("Q", new String[] { /* skip */ "-config", "a/*literal*/b.cfg", "{x,y}", "p\\tq\\"r\\\\s" // end\n }, ExitStatus.VIOLATION_SAFETY); } }\n')
        with open(os.path.join(tmp, "test", "a", "BadEsc.java"), "w") as f:
            f.write('public class BadEsc extends ModelCheckerTestCase { public BadEsc() { super("B", new String[] { "\\u0041" }); } }\n')
        with open(os.path.join(tmp, "test", "a", "SubSep.java"), "w") as f:
            f.write('public class SubSep extends ModelCheckerTestCase { public SubSep() { super("Spec", "dir" + File.separator + "sub", new String[] {"-config", "X.cfg"}, ExitStatus.VIOLATION_SAFETY); } }\n')
        with open(os.path.join(tmp, "test", "a", "BadExit.java"), "w") as f:
            f.write('public class BadExit extends ModelCheckerTestCase { public BadExit() { super("Spec", "dir" + dyn(), new String[] {"-config", "X.cfg"}, computeExit()); } }\n')
        with open(os.path.join(tmp, "test", "a", "CommentedSuper.java"), "w") as f:
            f.write('/** Uses a different overload from super(). */\n// super("Old")\n/* super("Other") */\npublic class CommentedSuper extends ModelCheckerTestCase { static class Helper { Helper() { super(); } } static final String TB = """\n    super("Wrong", new String[] {"-simulate"})\n    """; public CommentedSuper() { String s = "super(\\"Quoted\\")"; super("Clock", new String[] { "-config", "Clock.cfg" }); } }\n')
        with open(os.path.join(tmp, "test", "a", "UnicodeComment.java"), "w") as f:
            f.write('public class UnicodeComment extends ModelCheckerTestCase { public UnicodeComment() { super("Clock", new String[] { "-config", // config \\u000a "Clock.cfg"\n }); } }\n')
        with open(os.path.join(tmp, "test", "a", "Test7.java"), "w") as f:
            f.write('public class Test7 extends SuiteTestCase { /* super("99", "98", "97"); */ public Test7() { super("10", "7", "0"); } }\n')
        with open(os.path.join(tmp, "test", "a", "Test17.java"), "w") as f:
            f.write('public class Test17 extends SuiteTestCase { public Test17() { super("7", "2", "0", "1", "line 101: 0\\n" + "line 102: 0"); } }\n')
        with open(os.path.join(tmp, "test", "a", "Test18.java"), "w") as f:
            f.write('public class Test18 extends SuiteTestCase { public Test18() { super("14", "1", "0", "1"); } }\n')
        with open(os.path.join(tmp, "test", "a", "TestDefault.java"), "w") as f:
            f.write('public class TestDefault extends SuiteTestCase { }\n')
        with open(os.path.join(tmp, "test", "a", "TestBadSuite.java"), "w") as f:
            f.write('public class TestBadSuite extends SuiteTestCase { public TestBadSuite() { super(dyn(), "1", "0", "1"); } }\n')
        with open(os.path.join(tmp, "test", "a", "ETestSim.java"), "w") as f:
            f.write('public class ETestSim extends SuiteETestCase { public ETestSim() { super(new String[]{"-simulate"}, ExitStatus.ERROR /*comment*/); } }\n')

    def test_extract_cases(self):
        with tempfile.TemporaryDirectory() as tmp:
            self.tree(tmp)
            cases = {c["cls"]: c for c in tlcsuite.extract_cases(tmp)}
        self.assertEqual(sorted(cases), ["BadEsc", "BadExit", "CommentedSuper", "DynPath", "ETestSim", "Lit", "OneTest", "QuotedDelims", "Sep", "SubSep", "Susp", "Test17", "Test18", "Test7", "TestBadSuite", "TestDefault", "UnicodeComment", "b.Dup", "c.Dup"])
        one = cases["OneTest"]
        self.assertEqual((one["spec"], one["path"], one["args"], one["exit"], one["deadlock"]), ("Spec", "dir", ["-config", "X.tla", "-workers", "1"], "VIOLATION_SAFETY", True))
        self.assertEqual(one["stats"], [["10", "7", "0"]])
        self.assertTrue(
            cases["Susp"]["ignored"]
            and cases["Lit"]["nonlit"]
            and cases["DynPath"]["nonlit"]
            and cases["BadEsc"]["nonlit"]
            and cases["BadExit"]["nonlit"]
            and cases["UnicodeComment"]["nonlit"]
            and cases["TestBadSuite"]["nonlit"]
        )
        self.assertEqual((cases["Sep"]["nonlit"], cases["Sep"]["args"]), (False, ["-dumpTrace", "json", "states/S.json"]))
        self.assertEqual(
            (cases["CommentedSuper"]["nonlit"], cases["CommentedSuper"]["spec"], cases["CommentedSuper"]["args"]),
            (False, "Clock", ["-config", "Clock.cfg"]),
        )
        self.assertEqual(
            (cases["SubSep"]["nonlit"], cases["SubSep"]["path"], cases["SubSep"]["args"], cases["SubSep"]["exit"]),
            (False, "dir/sub", ["-config", "X.cfg"], "VIOLATION_SAFETY"),
        )
        self.assertEqual(
            (cases["QuotedDelims"]["nonlit"], cases["QuotedDelims"]["args"], cases["QuotedDelims"]["exit"]),
            (False, ["-config", "a/*literal*/b.cfg", "{x,y}", 'p\tq"r\\s'], "VIOLATION_SAFETY"),
        )
        self.assertEqual((cases["Test7"]["nonlit"], cases["Test7"]["spec"], cases["Test7"]["path"], cases["Test7"]["stats"]), (False, "test7", "suite", [["10", "7", "0"]]))
        self.assertEqual((cases["Test17"]["nonlit"], cases["Test17"]["stats"]), (False, [["7", "2", "0"]]))
        self.assertEqual((cases["Test18"]["nonlit"], cases["Test18"]["stats"]), (False, [["14", "1", "0"]]))
        self.assertEqual((cases["TestDefault"]["nonlit"], cases["TestDefault"]["stats"]), (False, [["2", "1", "0"]]))
        self.assertEqual((cases["ETestSim"]["nonlit"], cases["ETestSim"]["args"], cases["ETestSim"]["exit"], cases["ETestSim"]["stats"]), (False, ["-simulate"], "ERROR", []))
        self.assertTrue(tlcsuite.junit_agrees(cases["ETestSim"], {"result": "error", "exit": 255}))
        self.assertFalse(tlcsuite.junit_agrees(cases["ETestSim"], {"result": "success", "exit": 0}))

    def test_prepare_skips_and_inline_config(self):
        with tempfile.TemporaryDirectory() as tmp:
            os.makedirs(os.path.join(tmp, "dir"))
            with open(os.path.join(tmp, "dir", "Spec.tla"), "w") as f:
                f.write("---- MODULE Spec ----\n====\n\n---- CONFIG Spec ----\nSPECIFICATION Spec\n====\n")
            base = dict(cls="T", base="ModelCheckerTestCase", spec="Spec", path="dir", args=["-config", "Spec.tla", "-lncheck", "final"], deadlock=False,
                        ignored=False, nonlit=False)
            case = tlcsuite.prepare(base, tmp, "unused.jar")
            self.assertIsNone(case["skip"])
            self.assertEqual(case["run_args"], ["-config", "_inline_T.cfg", "-deadlock"])
            with open(os.path.join(tmp, "dir", "_inline_T.cfg")) as f:
                self.assertIn("SPECIFICATION Spec", f.read())
            self.assertEqual(tlcsuite.prepare(dict(base, ignored=True), tmp, "j")["skip"], "ignored in the JUnit sources")
            self.assertEqual(tlcsuite.prepare(dict(base, spec="Missing"), tmp, "j")["skip"], "spec not found")
            # A test that checks deadlock keeps it on.
            self.assertNotIn("-deadlock", tlcsuite.prepare(dict(base, deadlock=True, args=[]), tmp, "j")["run_args"])

    def test_compare(self):
        res = lambda result, violated=None, d=5, g=9, depth=3: {"result": result, "violated": violated, "distinct": d, "generated": g, "depth": depth}
        case = {"run_args": ["-deadlock"]}
        sim = {"run_args": ["-simulate", "num=3"]}
        cmp = tlcsuite.compare
        self.assertEqual(cmp(case, res("success"), res("success")), [])
        self.assertEqual(cmp(case, res("success"), res("success", d=6, depth=4)), ["distinct", "depth"])
        self.assertEqual(cmp(sim, res("success"), res("success", g=1)), [])
        self.assertEqual(cmp(case, res("success"), res("error")), ["result"])
        # Deterministic failing runs compare counts as well as violated names.
        self.assertEqual(cmp(case, res("safety failure", "Inv"), res("safety failure", "Inv", d=1)), ["distinct"])
        self.assertEqual(cmp(case, res("safety failure", "Inv"), res("safety failure", "Other")), ["violated"])
        # A liveness failure only needs a name.
        self.assertEqual(cmp(case, res("liveness failure", None), res("liveness failure", "P")), [])
        self.assertEqual(cmp(case, res("liveness failure", None), res("liveness failure", None)), ["violated"])
        self.assertEqual(cmp(case, res("error"), res("error")), [])

    def test_expected_failures(self):
        entries = [{"id": "Github*", "reason": "group"}, {"id": "Slow", "result": "timeout", "flaky": True, "reason": "load"}]
        self.assertEqual(tlcsuite.match_expected(entries, "Github12Test", "error")["reason"], "group")
        self.assertIsNone(tlcsuite.match_expected(entries, "Slow", "error"))
        self.assertEqual(tlcsuite.match_expected(entries, "Slow", "timeout")["reason"], "load")
        case = {"args": ["-continue"], "cls": "C"}
        self.assertIn("-continue", tlcsuite.reason_for(case, {"result": "success"}, {"result": "error"}, ["result"]))
        case = {"args": [], "cls": "C"}
        self.assertEqual(tlcsuite.reason_for(case, {"result": "success"}, {"result": "error", "error": "x\nError: boom\n"}, ["result"]), "TLC success, tlx error (Error: boom)")
        self.assertIn("distinct", tlcsuite.reason_for(case, {"result": "success"}, {"result": "success"}, ["distinct"]))
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, "e.json")
            self.assertEqual(tlcsuite.load_expected(path), [])
            tlcsuite.write_expected(path, entries)
            self.assertEqual(tlcsuite.load_expected(path), entries)

    def test_verify_reads_the_output_lines(self):
        line = ("FAIL Github12Test                                 tlc=success/2/3/2 tlx=error/None/None/None (0.3s vs 0.02s) differs: result "
                "[expected: TLC success, tlx error]")
        self.assertEqual(tlxlib.RESULT_LINE.match(line).groups(), ("FAIL", "Github12Test"))
        self.assertEqual(re.search(r" tlx=(.*?)/\S+/\S+/\S+ \(", line).group(1), "error")
        self.assertEqual(re.search(r" tlx=(.*?)/\S+/\S+/\S+ \(", line.replace("error", "liveness failure")).group(1), "liveness failure")
        self.assertIn("tlcsuite", [s[0] for s in verify.SUITES])
        with open(os.path.join(tlxlib.ROOT, tlcsuite.EXPECTED)) as source:
            for e in json.load(source)["expected_failures"]:
                self.assertTrue(e["id"] and e["reason"], e)


class NativeCRequirement(unittest.TestCase):
    """`--require-native`: a sanitizer suite fails when generated C was not used."""

    def test_reports_a_disabled_native_build(self):
        out = "compile: native code disabled: cannot load /cache/1/model.so: dlopen failed\n4 states generated\n"
        self.assertIn("native code disabled", spectest.native_missing(out))

    def test_reports_a_failed_c_build(self):
        out = "compile: C build failed, keeping the JIT code: compiler not found\n"
        self.assertIn("C build failed", spectest.native_missing(out))

    def test_reports_a_whole_model_fallback(self):
        self.assertIsNotNone(spectest.native_missing("compile: IR verification failed; interpreting the model\n"))

    def test_accepts_a_native_run(self):
        self.assertIsNone(spectest.native_missing("compile: native code: 4/4 actions, 1/1 invariants, Init\n4 states generated\n"))


if __name__ == "__main__":
    unittest.main()
