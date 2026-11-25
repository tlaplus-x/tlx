"""Scheduling regression tests for the generated-certificate verifier."""

import contextlib
import importlib.util
import io
from pathlib import Path
import subprocess
import sys
import threading
import time
import unittest
from unittest.mock import patch

from tempdirs import TemporaryDirectory


spec = importlib.util.spec_from_file_location(
    "check_generated", Path(__file__).resolve().parents[2] / "proofs/check_generated.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


class LeanConcurrency(unittest.TestCase):
    def test_jobs_caps_positive_checks_and_mutations_together(self):
        # Only scheduling is under test; fake Lean accepts the original and
        # rejects each mutation with the same diagnostic contract as Lean.
        source = "\n".join([
            "namespace TlxOptimization.GeneratedHistory",
            "fun i => s.2 i ∧ q i e",
            "m.step s.1 t.1 w s.2",
            "m.transfer s.1 t.1 w s.2",
            "def after := (model sem).reduced",
        ]) + "\n"
        for jobs in (1, 2):
            with self.subTest(jobs=jobs), TemporaryDirectory() as tmp:
                paths = [Path(tmp) / name for name in ("Fast.lean", "Slow.lean")]
                for path in paths:
                    path.write_text(source)
                lock = threading.Lock()
                mutation_started = threading.Event()
                active = peak = positives = negatives = 0

                def invoke(lean, path):
                    nonlocal active, peak, positives, negatives
                    broken = path.name == "Broken.lean"
                    with lock:
                        active += 1
                        peak = max(peak, active)
                        positives += not broken
                        negatives += broken
                    try:
                        if broken:
                            mutation_started.set()
                        elif path.name == "Slow.lean" and jobs > 1:
                            self.assertTrue(mutation_started.wait(2))
                        time.sleep(0.02)
                        output = "error: unsolved goals" if broken else "\n".join(
                            f"'TlxOptimization.GeneratedHistory.{name}' does not depend on any axioms"
                            for name in checker.THEOREMS)
                        return subprocess.CompletedProcess([], int(broken), output)
                    finally:
                        with lock:
                            active -= 1

                argv = ["check_generated.py", *map(str, paths), "--negative", "--jobs", str(jobs)]
                with patch.object(sys, "argv", argv), \
                     patch.object(checker, "find_lean", return_value="fake-lean"), \
                     patch.object(checker.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "Lean test")), \
                     patch.object(checker, "invoke", side_effect=invoke), \
                     contextlib.redirect_stdout(io.StringIO()):
                    checker.main()
                self.assertEqual((positives, negatives, active), (2, 8, 0))
                self.assertLessEqual(peak, jobs)


if __name__ == "__main__":
    unittest.main()
