#!/usr/bin/env python3
"""Explicit local Lean check of the blob history-quotient proof; no installation."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
RULES = ROOT / "crates/tlx-sema/src/optimize/Rules.lean"
THEOREMS = {
    "optimization_correct", "specification_correct", "counterexample_lifts", "deadlock_preserved",
    "reachable_core_wf",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def invoke(command, env=None):
    # Each subprocess is owned and reaped by subprocess.run, including on
    # timeout. Lean does not spawn a model checker or cloud work.
    return subprocess.run(
        command, cwd=ROOT, env=env, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=600, check=False,
    )


def require_success(result):
    if result.returncode:
        raise RuntimeError(f"Lean failed ({result.returncode}):\n{result.stdout}")


def check(lean):
    inputs = json.loads((HERE / "inputs.json").read_text())
    for name in ("source", "config"):
        path = ROOT / inputs[name]
        if digest(path) != inputs[name + "_sha256"]:
            raise RuntimeError(f"{name} changed: review the formalization before refreshing {path}")
    version = invoke([lean, "--version"])
    require_success(version)
    if f"version {inputs['lean_version']}," not in version.stdout:
        raise RuntimeError(f"expected Lean {inputs['lean_version']}, got {version.stdout.strip()}")
    flags = [lean, "-t0", "-DwarningAsError=true"]
    with tempfile.TemporaryDirectory(prefix="tlx-blob-proof-") as tmp:
        tmp = Path(tmp)
        # A fresh import directory prevents stale/custom oleans from supplying
        # the certificate. -t0 also checks imported proof terms.
        env = dict(os.environ, LEAN_PATH=str(tmp))
        shared = invoke(flags + ["-R", str(RULES.parent), "-o", str(tmp / "Rules.olean"), str(RULES)], env)
        require_success(shared)
        proof = invoke(flags + [str(HERE / "Blob.lean")], env)
        require_success(proof)
        axioms = {}
        for name, values in re.findall(r"'Blob\.(\w+)' depends on axioms: \[([^]]*)\]", proof.stdout):
            actual = {v.strip() for v in values.split(",") if v.strip()}
            if actual - ALLOWED_AXIOMS:
                raise RuntimeError(f"unexpected axioms in {name}: {sorted(actual)}")
            axioms[name] = sorted(actual)
        if set(axioms) != THEOREMS:
            raise RuntimeError(f"missing or unexpected theorem audit:\n{proof.stdout}")

        # A plausible unsound change: forget previous failed prefix obligations
        # and keep only whether the newly appended event is consistent.
        source = (HERE / "Blob.lean").read_text()
        before = "⟨seen, s.consistent ∧ eventOK e seen⟩"
        if source.count(before) != 1:
            raise RuntimeError("negative test no longer targets exactly one summary update")
        bad = tmp / "Broken.lean"
        bad.write_text(source.replace(before, "⟨seen, eventOK e seen⟩"))
        rejected = invoke(flags + ["-R", str(tmp), str(bad)], env)
        if rejected.returncode == 0 or not all(word in rejected.stdout for word in ("error:", "summarize", "appendSummary")):
            raise RuntimeError(f"bad-summary test did not fail at the preservation proof:\n{rejected.stdout}")
        print(proof.stdout, end="")
        print("PASS: discarding the prior consistency bit is rejected by Lean.")
        return {
            "lean": version.stdout.strip(), "inputs": inputs,
            "rules_sha256": digest(RULES), "proof_sha256": digest(HERE / "Blob.lean"),
            "axioms": axioms, "trust_level": 0, "negative_test": "rejected",
            "scope": "Manual typed formalization; TLA+ translation, Rust recognizer and runtime are not verified.",
        }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean", default="lean", help="Lean 4.34.1 executable (default: lean on PATH)")
    parser.add_argument("--report", type=Path, help="write a JSON verification receipt")
    args = parser.parse_args()
    lean = shutil.which(args.lean)
    if lean is None:
        parser.error(f"Lean executable not found: {args.lean}")
    try:
        # Preserve a lean -> elan dispatcher symlink's invoked name.
        result = check(os.path.abspath(lean))
        if args.report:
            args.report.write_text(json.dumps(result, indent=2) + "\n")
    except (OSError, RuntimeError, subprocess.TimeoutExpired) as error:
        parser.exit(1, f"{error}\n")
    print("PASS: blob history optimization certificate checked; no nonstandard axioms.")


if __name__ == "__main__":
    main()
