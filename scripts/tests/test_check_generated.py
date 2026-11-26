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


HISTORY_SOURCE = "\n".join([
    "fun i => s.2 i ∧ q i e",
    "m.step s.1 t.1 w s.2",
    "m.transfer s.1 t.1 w s.2",
    "namespace TlxOptimization.GeneratedHistory",
    "def after := (model sem).reduced",
    "end TlxOptimization.GeneratedHistory",
]) + "\n"

# A generated field certificate carries one extra scheduling path: the
# dead-to-live probe that decides whether the write-table mutation
# applies. It must queue behind the same --jobs bound as everything else.
FIELD_SOURCE = "\n".join([
    "def mask (p : K → P) (v : K → F → V) : K → F → V :=",
    "  fun k f => if m.live (p k) f then v k f else m.missing f",
    "def observations (p : K → P) (v : K → F → V) : K → F → V :=",
    "  fun k f => if m.observed (p k) f then v k f else m.missing f",
    "def seed (c : C) (b : B) (w : W) : State C K P F V :=",
    "  s = m.project (m.seed c b w)",
    "def advance (s : State C K P F V) (d : C) (b : B) (w : W) : State C K P F V :=",
    "  t = m.project (m.advance s t.1 b w)",
    "    fun k f => if k = a ∧ m.writes b f = true then m.value b s.1 d w s.2.1 input f else s.2.2 k f",
    "namespace TlxOptimization.GeneratedField",
    "def model : FieldRule.Model C Key Phase Field V BranchId W where",
    "  readsActor := readsActor",
    "  writes := writes",
    "  readsGlobal := readsGlobal",
    "  observed := observed",
    "def after := (model sem).reduced",
    "end TlxOptimization.GeneratedField",
]) + "\n"


class LeanConcurrency(unittest.TestCase):
    def test_jobs_caps_positive_checks_mutations_and_field_probe_together(self):
        # Only scheduling is under test; fake Lean accepts the original and
        # rejects each mutation with the same diagnostic contract as Lean.
        for jobs in (1, 2):
            with self.subTest(jobs=jobs), TemporaryDirectory() as tmp:
                paths = [Path(tmp) / name for name in ("Field.lean", "Fast.lean")]
                for path in paths:
                    path.write_text(FIELD_SOURCE if path.name == "Field.lean" else HISTORY_SOURCE)
                lock = threading.Lock()
                active = peak = positives = negatives = probes = 0

                def invoke(lean, path):
                    nonlocal active, peak, positives, negatives, probes
                    probe = path.name == "Probe.lean"
                    broken = path.name == "Broken.lean"
                    with lock:
                        active += 1
                        peak = max(peak, active)
                        if probe:
                            probes += 1
                        else:
                            positives += not broken
                            negatives += broken
                    try:
                        if probe:
                            # Stay in flight long enough for the field worker's
                            # mutation batch to start. If the probe bypasses the
                            # pool, that batch plus this probe exceeds --jobs.
                            time.sleep(0.4)
                            return subprocess.CompletedProcess([], 0, "true\n")
                        time.sleep(0.02)
                        if broken:
                            return subprocess.CompletedProcess([], 1, "error: unsolved goals")
                        text = path.read_text()
                        namespace = (
                            "GeneratedField" if "namespace TlxOptimization.GeneratedField" in text
                            else "GeneratedHistory")
                        output = "\n".join(
                            f"'TlxOptimization.{namespace}.{name}' does not depend on any axioms"
                            for name in checker.THEOREMS)
                        return subprocess.CompletedProcess([], 0, output)
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
                self.assertEqual((positives, probes, negatives, active), (2, 1, 14, 0))
                self.assertLessEqual(peak, jobs)

    def test_sharding_partitions_all_positive_and_negative_checks(self):
        with TemporaryDirectory() as tmp:
            paths = [Path(tmp) / name for name in ("Field.lean", "Fast.lean")]
            for path in paths:
                path.write_text(FIELD_SOURCE if path.name == "Field.lean" else HISTORY_SOURCE)

            seen_pos = []
            seen_neg = []
            lock = threading.Lock()

            def invoke(lean, path):
                text = path.read_text()
                if path.name == "Probe.lean":
                    return subprocess.CompletedProcess([], 0, "true\n")
                if path.name == "Broken.lean":
                    with lock:
                        seen_neg.append(text)
                    return subprocess.CompletedProcess([], 1, "error: unsolved goals")
                with lock:
                    seen_pos.append(path.name)
                namespace = (
                    "GeneratedField" if "namespace TlxOptimization.GeneratedField" in text
                    else "GeneratedHistory")
                output = "\n".join(
                    f"'TlxOptimization.{namespace}.{name}' does not depend on any axioms"
                    for name in checker.THEOREMS)
                return subprocess.CompletedProcess([], 0, output)

            total = 3
            for idx in range(1, total + 1):
                argv = ["check_generated.py", *map(str, paths), "--negative", "--jobs", "2", "--shard", f"{idx}/{total}"]
                with patch.object(sys, "argv", argv), \
                     patch.object(checker, "find_lean", return_value="fake-lean"), \
                     patch.object(checker.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "Lean test")), \
                     patch.object(checker, "invoke", side_effect=invoke), \
                     contextlib.redirect_stdout(io.StringIO()):
                    checker.main()

            self.assertEqual(sorted(seen_pos), ["Fast.lean", "Field.lean"])
            self.assertEqual(len(seen_neg), 14)
            self.assertEqual(len(set(seen_neg)), 14)

    def test_parse_shard_rejects_invalid_specs(self):
        for bad in ("0/4", "5/4", "1/0", "abc", "1/2/3"):
            with self.subTest(bad=bad), self.assertRaises(checker.argparse.ArgumentTypeError):
                checker.parse_shard(bad)
        self.assertEqual(checker.parse_shard("2/4"), (2, 4))



if __name__ == "__main__":
    unittest.main()
