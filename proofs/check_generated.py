#!/usr/bin/env python3
"""Explicitly verify generated rule certificates; never called by tlx check."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


THEOREMS = {
    "certificate", "optimization_correct", "specification_correct",
    "counterexample_lifts", "deadlock_preserved",
}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def invoke(lean, path):
    return subprocess.run(
        [lean, "-t0", "-DwarningAsError=true", "-R", str(path.parent), str(path)],
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        timeout=600, check=False,
    )


def verify(lean, path, negative):
    # Check the exact standalone bytes without a checkout-specific import path.
    source = path.read_text()
    namespaces = [name for name in ("GeneratedHistory", "GeneratedOrdered", "GeneratedErasure", "GeneratedAge")
                  if f"namespace TlxOptimization.{name}\n" in source]
    if len(namespaces) != 1:
        raise RuntimeError(f"{path}: expected one supported generated certificate")
    namespace = namespaces[0]
    result = invoke(lean, path)
    if result.returncode:
        raise RuntimeError(f"{path}: Lean failed:\n{result.stdout}")
    axioms = {}
    for name, values in re.findall(
        rf"'TlxOptimization\.{namespace}\.(\w+)' depends on axioms: \[([^]]*)\]",
        result.stdout,
    ):
        actual = {v.strip() for v in values.split(",") if v.strip()}
        if actual - ALLOWED_AXIOMS:
            raise RuntimeError(f"{path}: unexpected axioms for {name}: {actual}")
        axioms[name] = sorted(actual)
    for name in re.findall(
        rf"'TlxOptimization\.{namespace}\.(\w+)' does not depend on any axioms",
        result.stdout,
    ):
        axioms[name] = []
    theorems = THEOREMS | ({"runtime_key_equivalent"} if namespace == "GeneratedOrdered" else set())
    if set(axioms) != theorems:
        raise RuntimeError(f"{path}: incomplete theorem audit:\n{result.stdout}")
    mutations = []
    if negative:
        changes = ([
            ("fun i => s.2 i ∧ q i e", "fun i => q i e", "lost prefix verdict"),
        ] if namespace == "GeneratedHistory" else [
            ("next c d := ∃ w, m.step c d w", "next c d := False ∧ ∃ w, m.step c d w", "removed reduced successors"),
        ] if namespace == "GeneratedErasure" else [
            ("min (n + delta) cap", "min (n + delta - delta) cap", "failed to advance capped ages"),
            ("| .reset, _ => some 0", "| .reset, _ => some cap", "reset to the wrong age"),
            ("| .erase, _ => none\n\ntheorem update_commutes", "| .erase, a => a\n\ntheorem update_commutes", "failed to erase a timestamp"),
            ("h k = some n ∧ d ≤ n", "h k = some n ∧ d < n", "changed deadline strictness"),
        ] if namespace == "GeneratedAge" else [
            ("(phase m.seed s.1.val, s.2)", "(false, s.2)", "forgot the initial anchor"),
            ("t.1 = (s.1 && decide (m.delta w = 0))", "t.1 = s.1", "failed to advance the reduced phase"),
        ])
        changes.append(
            ("def after := (model sem).reduced",
             "def after := { (model sem).reduced with safe := fun _ => True }",
             "changed reduced observation")
        )
        for before, after, label in changes:
            if source.count(before) != 1:
                raise RuntimeError(f"{path}: negative test no longer targets one expression: {label}")
            with tempfile.TemporaryDirectory(prefix="tlx-generated-proof-") as tmp:
                bad = Path(tmp) / "Broken.lean"
                bad.write_text(source.replace(before, after))
                rejected = invoke(lean, bad)
            if rejected.returncode == 0 or not any(
                marker in rejected.stdout for marker in
                ("error: Tactic", "error: Type mismatch", "error: type mismatch", "error: Application type mismatch", "error: unsolved goals", "error: omega could not prove the goal")
            ):
                raise RuntimeError(f"{path}: mutation was not rejected: {label}\n{rejected.stdout}")
            mutations.append({"change": label, "diagnostic": rejected.stdout})
    print(f"PASS: {path} ({len(theorems)} theorem audits, {len(mutations)} rejected mutations)")
    return {
        "file": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "axioms": axioms, "rejected_mutations": mutations,
        "scope": f"Parametric {namespace} rule IR; lowering, totality and runtime remain trusted.",
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", type=Path, nargs="+")
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--negative", action="store_true", help="also require deliberately broken proofs to fail")
    parser.add_argument("--report", type=Path, help="write a JSON receipt after all checks pass")
    args = parser.parse_args()
    lean = shutil.which(args.lean)
    if lean is None:
        parser.error(f"Lean executable not found: {args.lean}")
    lean = os.path.abspath(lean)  # Preserve an elan dispatcher's invoked name.
    try:
        version = subprocess.run([lean, "--version"], capture_output=True, text=True, timeout=30, check=True).stdout.strip()
        results = [verify(lean, p.resolve(), args.negative) for p in args.files]
        if args.report:
            args.report.write_text(json.dumps({"lean": version, "trust_level": 0, "results": results}, indent=2) + "\n")
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        parser.exit(1, f"{error}\n")


if __name__ == "__main__":
    main()
