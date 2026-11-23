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
    namespaces = [name for name in ("GeneratedHistory", "GeneratedOrdered", "GeneratedErasure", "GeneratedAge", "GeneratedAgeHistory", "GeneratedLength", "GeneratedField", "GeneratedPipeline", "GeneratedSymmetry", "GeneratedEquivSymmetry", "GeneratedChooseSymmetry", "GeneratedNested", "GeneratedLive", "GeneratedErasedSymmetry")
                  if f"namespace TlxOptimization.{name}\n" in source]
    if len(namespaces) != 1:
        raise RuntimeError(f"{path}: expected one supported generated certificate")
    namespace = namespaces[0]
    result = invoke(lean, path)
    if result.returncode:
        raise RuntimeError(f"{path}: Lean failed:\n{result.stdout}")
    axioms = {}
    scope = rf"(?:{namespace}|AgeRule\.(?:Test|Decision))" if namespace in {"GeneratedAge", "GeneratedAgeHistory"} else namespace
    for name, values in re.findall(
        rf"'TlxOptimization\.{scope}\.(\w+)' depends on axioms: \[([^]]*)\]",
        result.stdout,
    ):
        actual = {v.strip() for v in values.split(",") if v.strip()}
        if actual - ALLOWED_AXIOMS:
            raise RuntimeError(f"{path}: unexpected axioms for {name}: {actual}")
        axioms[name] = sorted(actual)
    for name in re.findall(
        rf"'TlxOptimization\.{scope}\.(\w+)' does not depend on any axioms",
        result.stdout,
    ):
        axioms[name] = []
    theorems = THEOREMS | ({"runtime_key_equivalent"} if namespace in {"GeneratedOrdered", "GeneratedNested", "GeneratedLive"} else set())
    if namespace in {"GeneratedSymmetry", "GeneratedErasedSymmetry", "GeneratedEquivSymmetry"}:
        theorems |= {"orbit_key_equivalent"}
    if namespace == "GeneratedChooseSymmetry":
        theorems |= {"inductive_invariant", "orbit_key_equivalent"}
    if namespace == "GeneratedErasedSymmetry":
        theorems |= {"erasure_certificate"}
    if namespace in {"GeneratedAge", "GeneratedAgeHistory"} and "def Test.select" in source:
        theorems |= {"select_concrete", "select_reduced"}
    if namespace in {"GeneratedAge", "GeneratedAgeHistory"} and "theorem Test.bind_concrete" in source:
        theorems |= {"bind_concrete", "bind_reduced"}
    if "theorem Decision.commutes" in source:
        theorems |= {"commutes", "bindValue_concrete", "bindValue_reduced"}
    if set(axioms) != theorems:
        raise RuntimeError(f"{path}: incomplete theorem audit:\n{result.stdout}")
    mutations = []
    if negative:
        if namespace == "GeneratedPipeline":
            final = re.search(r"def rawAfter := (M\d+)\.system", source)[1]
            block = source.split(f"namespace {final}\n", 1)[1].split(f"end {final}\n", 1)[0]
            initial = re.search(r"def initial[^\n]*\n  \| 0 => (\d+)", block)
            prefix = f"namespace {final}\n" + block[:initial.end()]
            changes = [
                (prefix, prefix[:-len(initial[1])] + str(int(initial[1]) + 1), "changed final initial value"),
                (f"def rawAfter := {final}.system", f"def rawAfter := {{ {final}.system with safe := fun s => ¬ {final}.system.safe s }}", "negated exported observation"),
            ]
            saturated = re.search(r"def update\d+.*?\n(?:  \| [^\n]*\n)*?  \| \d+ => if s \d+ < (\d+) then s \d+ \+ 1 else (\d+)", block)
            if saturated:
                prefix = f"namespace {final}\n" + block[:saturated.end()]
                changes.append((prefix, prefix[:-len(saturated[2])] + str(int(saturated[2]) + 1), "incremented past the certified cap"))
            for step, rule in re.findall(r'namespace Step(\d+)\ndef rule : String := "([^"\n]+)"', source):
                model = f"M{int(step) + 1}"
                target = source.split(f"namespace {model}\n", 1)[1].split(f"end {model}\n", 1)[0]
                if rule == "constant-state-propagation/v1":
                    step_block = source.split(f"namespace Step{step}\n", 1)[1].split(f"end Step{step}\n", 1)[0]
                    constraint = re.search(r"def valid[^\n]*?s \d+ = (\d+)", step_block)
                    if constraint:
                        prefix = f"namespace Step{step}\n" + step_block[:constraint.end()]
                        changes.append((prefix, prefix[:-len(constraint[1])] + str(int(constraint[1]) + 1), "assumed an incorrect inductive constant"))
                elif rule == "predicate-simplification/v1":
                    guard = re.search(r"def guard0 \(s : State\) : Prop := ([^\n]+)", target)
                    if guard:
                        prefix = f"namespace {model}\n" + target[:guard.end()]
                        changes.append((prefix, prefix[:-len(guard[1])] + f"(¬ {guard[1]})", "negated a simplified guard"))
                elif rule == "dead-action-elimination/v1":
                    prefix = f"namespace {model}\n" + target
                    # Alter Init as well when the result has no live action: an
                    # empty relation cannot lose another successor.
                    initial = re.search(r"def initial[^\n]*\n  \| 0 => (\d+)", target)
                    if "def guard0" in target:
                        changed = re.sub(r"next s t := ([^\n]+)", lambda m: f"next s t := False ∧ ({m[1]})", prefix)
                    else:
                        start = len(f"namespace {model}\n") + initial.start(1)
                        changed = prefix[:start] + str(int(initial[1]) + 1) + prefix[start + len(initial[1]):]
                    changes.append((prefix, changed, "changed the dead-action result"))
        else:
            changes = ([
                ("fun i => s.2 i ∧ q i e", "fun i => q i e", "lost prefix verdict"),
            ] if namespace == "GeneratedHistory" else [
                ("next c d := ∃ w, m.step c d w", "next c d := False ∧ ∃ w, m.step c d w", "removed reduced successors"),
            ] if namespace == "GeneratedErasure" else [
                ("| .keep => n", "| .keep => 0", "discarded preserved length"),
                ("| .reset values => values.length", "| .reset values => 0", "discarded reset contents length"),
                ("previous.reduced n + 1", "previous.reduced n + 2", "appended the wrong length"),
                ("m.step s.1 t.1 w s.2", "m.step s.1 t.1 w (fun _ => 0)", "discarded length guard feedback"),
                ("m.transfer s.1 d w s.2 k", "m.transfer s.1 d w (fun _ => 0) k", "discarded length transfer feedback"),
            ] if namespace == "GeneratedLength" else [
                ("if m.live (p k) f then v k f else m.missing", "if m.live (p k) f then m.missing else v k f", "erased live fields"),
                ("s = m.project (m.seed c b w)", "s = m.seed c b w", "omitted initial projection"),
                ("t = m.project (m.advance s t.1 b w)", "t = m.project s", "dropped reduced transfers"),
                ("  readsActor := readsActor", "  readsActor := fun _ _ => true", "read dead actor fields"),
                ("  writes := writes", "  writes := fun _ _ => false", "exposed dead framed fields"),
                ("  readsGlobal := readsGlobal", "  readsGlobal := fun _ _ => true", "read dead fields of another actor"),
            ] if namespace == "GeneratedField" else [
                ("fun i => p.toFun (keys i)", "fun i => keys i", "failed to rename bound keys"),
                ("fun m k => r m (p.invFun k)", "fun m k => r m k", "failed to permute map keys"),
                ("fun s => renameKeyVal p (u s)", "fun s => u s", "failed to permute scalar key slots"),
                ("| .inl k => .inl (p.toFun k)", "| .inl k => .inl k", "failed to rename key values"),
                ("if mask g then countFin (sizes g) (fun i => pred ⟨g, i⟩) else 0", "if mask g then (List.finRange (sizes g)).findIdx (fun i => pred ⟨g, i⟩) else 0", "replaced key cardinality with order-dependent index"),
                ("next a b := ∃ s t, project s = a ∧ m.concrete.next s t ∧ project t = b", "next a b := False ∧ ∃ s t, project s = a ∧ m.concrete.next s t ∧ project t = b", "discarded quotient successors"),
                ("initial a := ∃ s, m.concrete.initial s ∧ project s = a", "initial a := False ∧ ∃ s, m.concrete.initial s ∧ project s = a", "discarded quotient initialization"),
            ] if namespace in {"GeneratedSymmetry", "GeneratedErasedSymmetry"} else [
                ("| .key k => .key (p.toFun k)", "| .key k => .key k", "failed to rename keys"),
                ("| .seq xs => .seq (renameRawList p xs)", "| .seq xs => .seq xs", "failed to rename sequence elements"),
                ("| .set xs => .set (renameRawList p xs)", "| .set xs => .set xs", "failed to rename set elements"),
                ("| .fn ps => .fn (renameRawPairs p ps)", "| .fn ps => .fn ps", "failed to rename function entries"),
                ("| .set xs => some (dedupList (xs.map mkVal)).length", "| .set xs => some xs.length", "replaced set cardinality with non-extensional list length"),
                ("next a b := ∃ s t, project s = a ∧ m.concrete.next s t ∧ project t = b", "next a b := False ∧ ∃ s t, project s = a ∧ m.concrete.next s t ∧ project t = b", "discarded quotient successors"),
                ("initial a := ∃ s, m.concrete.initial s ∧ project s = a", "initial a := False ∧ ∃ s, m.concrete.initial s ∧ project s = a", "discarded quotient initialization"),
            ] if namespace == "GeneratedEquivSymmetry" else [
                ("fun i => p.toFun (keys i)", "fun i => keys i", "failed to rename bound keys"),
                ("fun m k => r m (p.invFun k)", "fun m k => r m k", "failed to permute map keys"),
                ("fun f k => fl f (p.invFun k)", "fun f k => fl f k", "failed to permute flag keys"),
                ("fun id k => ms id (p.invFun k)", "fun id k => ms id k", "failed to permute message-set keys"),
                ("!(mask y.1 && q.eval testFn fixedAtom st (push keys y) aux) || decide (y = k)", "!(mask y.1 && q.eval testFn fixedAtom st (push keys y) aux) || true", "dropped syntactic uniqueness guard in CHOOSE"),
                ("| .atMostOneFlag mask flag _ =>\n      inv.atMostOneFlags.any (fun item => decide (item.1 = flag) && maskImplies mask item.2)", "| .atMostOneFlag _ _ _ => true", "accepted unproved unique-flag choice"),
                ("| .msgUniform ms _ =>\n      inv.uniformValMsgs.any (fun m => decide (m = ms)) ||\n        inv.constValMsgs.any (fun item => decide (item.1 = ms))", "| .msgUniform _ _ => true", "accepted unproved projected-value choice"),
                ("next a b := ∃ s t, m.project s = a ∧ m.validConcrete.next s t ∧ m.project t = b", "next a b := False ∧ ∃ s t, m.project s = a ∧ m.validConcrete.next s t ∧ m.project t = b", "discarded quotient successors"),
                ("initial a := ∃ s, m.validConcrete.initial s ∧ m.project s = a", "initial a := False ∧ ∃ s, m.validConcrete.initial s ∧ m.project s = a", "discarded quotient initialization"),
            ] if namespace == "GeneratedChooseSymmetry" else [
                ("slots := fun i => ((transfers i).eval layout s).eval layout s", "slots := fun _ => 0", "discarded nested slot transfers"),
                ("(∀ i, sentinel (read layout s i) = sentinel (read layout t i))", "True", "forgot exact nonpositive sentinels"),
                ("next a b := ∃ s t, m.project s = a ∧ m.concrete.next s t ∧ m.project t = b", "next a b := False ∧ ∃ s t, m.project s = a ∧ m.concrete.next s t ∧ m.project t = b", "discarded quotient successors"),
                ("initial a := ∃ s, m.concrete.initial s ∧ m.project s = a", "initial a := False ∧ ∃ s, m.concrete.initial s ∧ m.project s = a", "discarded quotient initialization"),
            ] if namespace == "GeneratedNested" else [
                ("then some v else h.values k", "then some v else none", "discarded still-live old versions"),
                ("k = ((clock + 1 : Nat) : Int)", "k = ((clock + 2 : Nat) : Int)", "inserted at the wrong fresh key"),
                ("(s.core, m.numericKey refs s, m.retainedTable refs s)", "(s.core, m.numericKey refs s, fun (_ : Int) (_ : V) => False)", "discarded retained payloads from the key"),
                ("def after := (model sem).reduced", "def after := { (model sem).reduced with next := fun _ _ => False }", "discarded live-version successors"),
                ("def after := (model sem).reduced", "def after := { (model sem).reduced with initial := fun _ => False }", "discarded live-version initialization"),
            ] if namespace == "GeneratedLive" else [
                ("min (n + delta) cap", "min (n + delta - delta) cap", "failed to advance capped ages"),
                ("| .reset, _ => some 0", "| .reset, _ => some cap", "reset to the wrong age"),
                ("| .erase, _ => none\n\ntheorem update_commutes", "| .erase, a => a\n\ntheorem update_commutes", "failed to erase a timestamp"),
                ("h k = some n ∧ d ≤ n", "h k = some n ∧ d < n", "changed deadline strictness"),
            ] if namespace in {"GeneratedAge", "GeneratedAgeHistory"} else [
                ("(phase m.seed s.1.val, s.2)", "(false, s.2)", "forgot the initial anchor"),
                ("t.1 = (s.1 && decide (m.delta w = 0))", "t.1 = s.1", "failed to advance the reduced phase"),
            ])
        if namespace == "GeneratedErasedSymmetry":
            changes.append(("t.2 = m.hiddenUpdate b s.1 w keys s.2", "False ∧ t.2 = m.hiddenUpdate b s.1 w keys s.2", "removed concrete hidden successors"))
        if namespace in {"GeneratedAge", "GeneratedAgeHistory"} and "def Test.select" in source:
            changes.extend([
                ("(b = true ↔ p.reduced h)", "(b = false ↔ p.reduced h)", "inverted filter decision"),
                ("consume (if b then k :: selected else selected)", "consume (if b then selected else k :: selected)", "inverted selected key membership"),
            ])
        if namespace in {"GeneratedAge", "GeneratedAgeHistory"} and "theorem Test.bind_concrete" in source:
            changes.append(("(next b).reduced h", "(next (!b)).reduced h", "passed the wrong Boolean to the consumer"))
        if "theorem Decision.commutes" in source:
            changes.extend([
                ("(yes.reduced h) (no.reduced h)", "(no.reduced h) (yes.reduced h)", "swapped reduced update decision"),
                (".branch p (yes.bindValue f) (no.bindValue f)", ".branch p (no.bindValue f) (yes.bindValue f)", "swapped value continuation branches"),
            ])
        if namespace == "GeneratedHistory":
            changes.extend([
                ("m.step s.1 t.1 w s.2", "m.step s.1 t.1 w (History.summary m.predicate History.empty)", "discarded guard feedback"),
                ("m.transfer s.1 t.1 w s.2", "m.transfer s.1 t.1 w (History.summary m.predicate History.empty)", "discarded transfer feedback"),
            ])
        if namespace == "GeneratedAgeHistory":
            changes.extend([
                ("fun i => s.2 i ∧ q i e", "fun i => q i e", "lost prefix verdict"),
                ("m.guard s.1.1 t.1.1 w (presence s.1.2) s.2", "m.guard s.1.1 t.1.1 w (presence s.1.2) (History.summary m.predicate History.empty)", "discarded guard feedback"),
                ("m.historyTransfer s.1.1 d w (presence s.1.2) s.2", "m.historyTransfer s.1.1 d w (presence s.1.2) (History.summary m.predicate History.empty)", "discarded transfer feedback"),
                ("((m.historyTransfer s.1.1 d w (presence s.1.2) s.2).reduced s.1.2).reduced m.predicate s.2" if "theorem Decision.commutes" in source else "(m.historyTransfer s.1.1 d w (presence s.1.2) s.2).reduced m.predicate s.2", "(HistoryRule.Transfer.keep).reduced m.predicate s.2", "dropped the shared branch history transfer"),
                ("(m.age.project s.1, History.summary m.predicate s.2)", "(m.age.project s.1, History.summary m.predicate History.empty)", "discarded observed history"),
            ])
        if namespace == "GeneratedAgeHistory" and "theorem Decision.commutes" in source:
            changes.append(("m.change s.1.1 d w (presence s.1.2) s.2 k", "m.change s.1.1 d w (presence s.1.2) (History.summary m.predicate History.empty) k", "discarded timestamp history feedback"))
        if namespace != "GeneratedPipeline":
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
        "scope": ("Closed counter-pipeline IR; source lowering, TLA+ emission and runtime remain trusted."
                  if namespace == "GeneratedPipeline" else
                  f"Parametric {namespace} rule IR; lowering, totality and runtime remain trusted."),
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
