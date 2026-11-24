#!/usr/bin/env python3
"""Tests of scripts/spectest.py's NAME handling: whitespace splitting and
validation against the specs on disk. Runs no tlx and no TLC (only the
argument handling is exercised).

usage: python3 scripts/tests/test_spectest_args.py [-v]
"""
import contextlib, io, json, os, sys, tempfile, threading, time, unittest
from types import SimpleNamespace
from unittest.mock import patch

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import spectest


def resolve(names):
    """(result, stderr, exit code) of spectest.resolve_names: `result` is
    None when it exited, `code` is None when it returned."""
    err = io.StringIO()
    with contextlib.redirect_stderr(err):
        try:
            return spectest.resolve_names(names), err.getvalue(), None
        except SystemExit as e:
            return None, err.getvalue(), e.code


class ResolveNames(unittest.TestCase):
    def test_valid_names(self):
        self.assertEqual(spectest.resolve_names(["A1"]), ["A1"])
        self.assertEqual(spectest.resolve_names(["A1", "B8"]), ["A1", "B8"])

    def test_whitespace_splits(self):
        # An unsplit shell variable "A B" means the specs A and B.
        self.assertEqual(spectest.resolve_names(["A1 B8"]), ["A1", "B8"])
        self.assertEqual(spectest.resolve_names(["A1\tB8"]), ["A1", "B8"])
        self.assertEqual(spectest.resolve_names([" A1   B8 "]), ["A1", "B8"])

    def test_no_names_means_every_spec(self):
        self.assertEqual(spectest.resolve_names([]), spectest.spec_names())

    def test_unknown_exits_2(self):
        result, err, code = resolve(["NoSuchSpec"])
        self.assertIsNone(result)
        self.assertEqual(code, 2)
        self.assertIn("spectest: unknown spec NoSuchSpec (no tests/specs/NoSuchSpec.tla)\n", err)
        self.assertNotIn("did you mean", err)  # nothing close enough

    def test_unknown_reports_every_name(self):
        result, err, code = resolve(["NoSuchSpec", "A1 OtherSpec"])
        self.assertIsNone(result)
        self.assertEqual(code, 2)
        self.assertIn("unknown spec NoSuchSpec", err)
        self.assertIn("unknown spec OtherSpec", err)

    def test_near_miss_suggests(self):
        result, err, code = resolve(["B88"])
        self.assertIsNone(result)
        self.assertEqual(code, 2)
        self.assertIn("spectest: unknown spec B88 (no tests/specs/B88.tla)\n", err)
        self.assertIn("did you mean", err)
        self.assertIn("B8", err)

    def test_known_specs_are_valid(self):
        # The discovery rule and validation agree: every NAME.tla + NAME.cfg
        # resolves, and a .tla without its .cfg would not.
        known = spectest.spec_names()
        self.assertIn("A1", known)
        self.assertIn("B8", known)
        self.assertEqual(spectest.resolve_names(known), known)


class ParallelJobs(unittest.TestCase):
    def test_parallel_runs_in_isolated_dirs_and_preserves_order(self):
        tlc_ok = (
            "@!@!@STARTMSG 2185:0 @!@!@\n"
            "Model checking completed. No error has been found.\n"
            "@!@!@ENDMSG 2185 @!@!@\n"
            "@!@!@STARTMSG 2190:0 @!@!@\n"
            "2 states generated, 2 distinct states found, 0 states left on queue.\n"
            "@!@!@ENDMSG 2190 @!@!@\n"
            "@!@!@STARTMSG 2194:0 @!@!@\n"
            "The depth of the complete state graph search is 1.\n"
            "@!@!@ENDMSG 2194 @!@!@\n"
        )
        with tempfile.TemporaryDirectory() as root:
            specs = os.path.join(root, "specs")
            tlc_dir = os.path.join(specs, "tlc")
            os.makedirs(tlc_dir)
            names = ["S1", "S2", "S3", "S4"]
            for n in names:
                with open(os.path.join(specs, f"{n}.tla"), "w") as f:
                    f.write(f"---- MODULE {n} ----\n====\n")
                with open(os.path.join(specs, f"{n}.cfg"), "w") as f:
                    f.write("INIT Init\n")
                with open(os.path.join(tlc_dir, f"{n}.out"), "w") as f:
                    f.write(f"# exit 0\n{tlc_ok}")

            barrier = threading.Barrier(2, timeout=5)
            seen_cwds = []
            lock = threading.Lock()

            def fake_run_proc(cmd, **kw):
                name = cmd[2][:-4]
                if name in ("S1", "S2"):
                    barrier.wait()
                with lock:
                    seen_cwds.append((name, kw["cwd"]))
                return SimpleNamespace(stdout=tlc_ok, stderr="", returncode=0, rusage=None)

            report_path = os.path.join(root, "report.json")
            a = SimpleNamespace(
                names=names,
                refresh=False,
                jobs=2,
                extra="",
                default_mode=False,
                timeout=30.0,
                results_json=report_path,
                suite="spectest",
            )
            out = io.StringIO()
            with patch.object(spectest, "SPECS", specs), \
                 patch.object(spectest, "TLC_OUT", tlc_dir), \
                 patch.object(spectest, "VALIDATED", os.path.join(tlc_dir, "validated.json")), \
                 patch.object(spectest, "load_expected_cases", return_value=[]), \
                 patch.object(spectest, "parity_args", side_effect=lambda _b, args: args), \
                 patch.object(spectest, "parity_env", return_value={}), \
                 patch.object(spectest, "run_proc", side_effect=fake_run_proc), \
                 contextlib.redirect_stdout(out), \
                 self.assertRaises(SystemExit) as exited:
                spectest.run_specs(a, names, "fake-tlx")

            self.assertEqual(exited.exception.code, 0)
            cwds_by_name = dict(seen_cwds)
            self.assertNotEqual(cwds_by_name["S1"], cwds_by_name["S2"])
            with open(report_path) as f:
                report = json.load(f)
            self.assertEqual([c["id"] for c in report["cases"]], names)
            pass_lines = [line for line in out.getvalue().splitlines() if line.startswith("PASS ")]
            self.assertEqual([line.split()[1] for line in pass_lines], names)


if __name__ == "__main__":
    unittest.main()
