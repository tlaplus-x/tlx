#!/usr/bin/env python3
"""Explicitly verify generated rule certificates; never called by tlx check."""

import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parent.parent
SUPPORTED_NAMESPACES = (
    "GeneratedHistory",
    "GeneratedOrdered",
    "GeneratedErasure",
    "GeneratedAge",
    "GeneratedAgeHistory",
    "GeneratedLength",
    "GeneratedField",
    "GeneratedPipeline",
    "GeneratedSymmetry",
    "GeneratedEquivSymmetry",
    "GeneratedChooseSymmetry",
    "GeneratedNested",
    "GeneratedLive",
    "GeneratedErasedSymmetry",
    "GeneratedErasedEquivSymmetry",
    "GeneratedThresholdCounter",
)
# Representative tracked specifications covering every supported generated
# certificate namespace when check_generated.py is invoked without explicit files.
DEFAULT_CASES = (
    ("GeneratedErasure", "check", "proofs/symmetry/Erased.tla", None, ("-interp", "-optimize", "-noautosymmetry"), (0,)),
    ("GeneratedHistory", "check", "proofs/history/Feedback.tla", None, ("-interp", "-optimize", "-noautosymmetry"), (0,)),
    (
        "GeneratedOrdered",
        "check",
        "crates/tlx-cli/tests/fixtures/optimization_ordered/HiddenAnchor.tla",
        "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n",
        ("-interp", "-optimize", "-noautosymmetry"),
        (12,),
    ),
    ("GeneratedAge", "check", "proofs/age/FilteredAge.tla", None, ("-interp", "-optimize", "-noautosymmetry"), (0,)),
    ("GeneratedAgeHistory", "check", "proofs/age/DependentHistory.tla", None, ("-interp", "-optimize", "-noautosymmetry"), (0,)),
    ("GeneratedLength", "check", "proofs/length/Length.tla", None, ("-interp", "-optimize", "-noautosymmetry"), (0,)),
    ("GeneratedField", "check", "proofs/field/Phase.tla", None, ("-interp", "-optimize", "-noautosymmetry"), (0,)),
    ("GeneratedPipeline", "optimize", "proofs/counter/Counter.tla", None, (), (0,)),
    ("GeneratedSymmetry", "check", "proofs/symmetry/Keyed.tla", None, ("-interp",), (0,)),
    ("GeneratedSymmetry", "check", "proofs/symmetry/KeyedSeven.tla", None, ("-interp",), (0,)),
    ("GeneratedSymmetry", "check", "proofs/symmetry/ProductLarge.tla", None, ("-interp",), (0,)),
    ("GeneratedEquivSymmetry", "check", "proofs/symmetry/KeyValMaps.tla", None, ("-interp",), (0,)),
    ("GeneratedChooseSymmetry", "check", "proofs/symmetry/ChooseSym.tla", None, ("-interp",), (0,)),
    ("GeneratedNested", "check", "proofs/ordered/Nested.tla", None, ("-interp", "-optimize", "-noautosymmetry"), (0,)),
    ("GeneratedLive", "check", "proofs/ordered/LiveVersions.tla", None, ("-interp", "-optimize", "-noautosymmetry"), (0,)),
    ("GeneratedErasedSymmetry", "check", "proofs/symmetry/Erased.tla", None, ("-interp", "-optimize"), (0,)),
    ("GeneratedErasedEquivSymmetry", "check", "proofs/symmetry/ErasedMultiKey.tla", None, ("-interp", "-optimize"), (0,)),
    ("GeneratedThresholdCounter", "check", "proofs/counter/ThresholdProtocol.tla", None, ("-interp", "-optimize", "-noautosymmetry"), (0,)),
)
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


def has_decl_line(block, line):
    return re.search(rf"(?m)^{re.escape(line)}$", block) is not None


def has_preamble_decl(preamble, prefix):
    return re.search(rf"(?m)^{re.escape(prefix)}\b", preamble) is not None


def split_certificate(path, source):
    found = [
        name for name in SUPPORTED_NAMESPACES
        if re.search(rf"(?m)^namespace TlxOptimization\.{re.escape(name)}$", source)
    ]
    if len(found) != 1:
        raise RuntimeError(f"{path}: expected one supported generated certificate")
    namespace = found[0]
    open_matches = list(re.finditer(rf"(?m)^namespace TlxOptimization\.{re.escape(namespace)}\n", source))
    if len(open_matches) != 1:
        raise RuntimeError(f"{path}: malformed generated namespace {namespace}")
    open_match = open_matches[0]
    preamble = source[:open_match.start()]
    ns_open = open_match.group(0)
    rest = source[open_match.end():]
    close_matches = list(re.finditer(rf"(?m)^end TlxOptimization\.{re.escape(namespace)}(?=\n|$)", rest))
    if not close_matches:
        raise RuntimeError(f"{path}: malformed generated namespace {namespace}")
    close_match = close_matches[-1]
    gen_block = rest[:close_match.start()]
    ns_close = close_match.group(0)
    suffix = rest[close_match.end():]
    return namespace, preamble, ns_open, gen_block, ns_close, suffix


def replace_once_in(text, before, after, path, label):
    if text.count(before) != 1:
        raise RuntimeError(f"{path}: negative test no longer targets one expression: {label}")
    return text.replace(before, after, 1)


def replace_gen_regex(gen_block, pattern, repl, path, label):
    matches = list(re.finditer(pattern, gen_block, flags=re.MULTILINE))
    if len(matches) != 1:
        raise RuntimeError(f"{path}: negative test no longer targets one generated declaration: {label}")
    m = matches[0]
    return gen_block[:m.start()] + repl(m) + gen_block[m.end():]


def field_write_can_break_frame(lean, path, source, lean_pool=None):
    """Whether clearing the write table can violate `frameLive`.
    `frameLive` needs `live (target b) f = true -> live (source b) f = true`; only a
    dead-to-live write (`live (target b) f` and not `live (source b) f`) makes
    clearing `writes` unsound. Instance-level frame mutations on a certificate
    without such a transition would be accepted by Lean, so scope them out.
    """
    probe = source + (
        "\n#eval decide (∃ (b : TlxOptimization.GeneratedField.BranchId)"
        " (f : TlxOptimization.GeneratedField.Field),"
        " TlxOptimization.GeneratedField.live (TlxOptimization.GeneratedField.target b) f = true ∧"
        " TlxOptimization.GeneratedField.live (TlxOptimization.GeneratedField.source b) f = false)\n")
    with tempfile.TemporaryDirectory(prefix="tlx-frame-probe-") as tmp:
        probe_path = Path(tmp) / "Probe.lean"
        probe_path.write_text(probe)
        # Schedule through the shared Lean pool so the probe cannot exceed --jobs
        # while positive checks and mutations are already running.
        result = (lean_pool.submit(invoke, lean, probe_path).result()
                  if lean_pool is not None else invoke(lean, probe_path))
    if result.returncode:
        raise RuntimeError(f"{path}: frame probe failed:\n{result.stdout}")
    values = [line.strip() for line in result.stdout.splitlines() if line.strip() in {"true", "false"}]
    if len(values) != 1:
        raise RuntimeError(f"{path}: frame probe did not decide the finite-table condition:\n{result.stdout}")
    return values[0] == "true"


def parse_shard(spec):
    match = re.fullmatch(r"(\d+)/(\d+)", spec)
    if not match:
        raise argparse.ArgumentTypeError(f"invalid --shard {spec!r}: expected INDEX/TOTAL (e.g. 1/4)")
    index, total = int(match.group(1)), int(match.group(2))
    if total < 1 or not (1 <= index <= total):
        raise argparse.ArgumentTypeError(f"invalid --shard {spec!r}: require 1 <= INDEX <= TOTAL")
    return index, total


def check_positive(lean, path, namespace, theorems, lean_pool=None):
    # Check the exact standalone bytes without a checkout-specific import path.
    result = (lean_pool.submit(invoke, lean, path).result()
              if lean_pool is not None else invoke(lean, path))
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
    if set(axioms) != theorems:
        raise RuntimeError(f"{path}: incomplete theorem audit:\n{result.stdout}")
    return axioms


def plan_certificate(lean, path, negative, lean_pool=None, run_positive=True):
    source = path.read_text()
    namespace, preamble, ns_open, gen_block, ns_close, suffix = split_certificate(path, source)
    has_select = has_preamble_decl(preamble, "def Test.select")
    has_bind = has_preamble_decl(preamble, "theorem Test.bind_concrete")
    has_commutes = has_preamble_decl(preamble, "theorem Decision.commutes")
    is_constrained = has_decl_line(gen_block, "def constrainedAfter := (model sem).constrainedReduced")
    has_erasure_constrained = has_decl_line(gen_block, "def constrainedIntermediate := (model sem).erased.constrainedConcrete")
    has_const_declared = has_decl_line(gen_block, "def constSubstDeclared (i : Fin ConstSubstCount) : String :=")
    has_const_expanded = has_decl_line(gen_block, "def constSubstExpanded (i : Fin ConstSubstCount) : String :=")
    if has_const_declared != has_const_expanded:
        raise RuntimeError(f"{path}: mismatched constSubstDeclared/constSubstExpanded declarations")

    theorems = THEOREMS | ({"runtime_key_equivalent"} if namespace in {"GeneratedOrdered", "GeneratedNested", "GeneratedLive"} else set())
    if namespace in {"GeneratedSymmetry", "GeneratedErasedSymmetry", "GeneratedEquivSymmetry", "GeneratedErasedEquivSymmetry"}:
        theorems |= {"orbit_key_equivalent"}
    if namespace == "GeneratedChooseSymmetry":
        theorems |= {"inductive_invariant", "orbit_key_equivalent"}
    if namespace in {"GeneratedErasedSymmetry", "GeneratedErasedEquivSymmetry"}:
        theorems |= {"erasure_certificate"}
    if namespace in {"GeneratedAge", "GeneratedAgeHistory"} and has_select:
        theorems |= {"select_concrete", "select_reduced"}
    if namespace in {"GeneratedAge", "GeneratedAgeHistory"} and has_bind:
        theorems |= {"bind_concrete", "bind_reduced"}
    if has_commutes:
        theorems |= {"commutes", "bindValue_concrete", "bindValue_reduced"}
    if is_constrained:
        theorems |= {
            "constrained_certificate",
            "constrained_optimization_correct",
            "constrained_init_counterexample_lifts",
            "constrained_step_counterexample_lifts",
            "admitted_deadlock_preserved",
        }
    if has_erasure_constrained:
        theorems |= {"erasure_constrained_certificate"}
    if has_const_declared:
        theorems |= {"const_subst_bindings_match", "const_subst_sound"}
        if is_constrained:
            theorems |= {"const_subst_constrained_sound"}

    axioms = check_positive(lean, path, namespace, theorems, lean_pool) if run_positive else None
    mutated_sources = []
    if negative:

        def add_preamble_mutation(before, after, label):
            new_preamble = replace_once_in(preamble, before, after, path, label)
            mutated_sources.append((new_preamble + ns_open + gen_block + ns_close + suffix, label))

        def add_gen_decl_mutation(pattern, repl, label):
            new_gen = replace_gen_regex(gen_block, pattern, repl, path, label)
            mutated_sources.append((preamble + ns_open + new_gen + ns_close + suffix, label))

        if namespace == "GeneratedPipeline":
            final = re.search(r"(?m)^def rawAfter := (M\d+)\.system$", gen_block)[1]
            block = gen_block.split(f"namespace {final}\n", 1)[1].split(f"end {final}\n", 1)[0]
            initial = re.search(r"def initial[^\n]*\n  \| 0 => (\d+)", block)
            prefix = f"namespace {final}\n" + block[:initial.end()]
            pipe_changes = [
                (prefix, prefix[:-len(initial[1])] + str(int(initial[1]) + 1), "changed final initial value"),
                (f"def rawAfter := {final}.system", f"def rawAfter := {{ {final}.system with safe := fun s => ¬ {final}.system.safe s }}", "negated exported observation"),
            ]
            saturated = re.search(r"def update\d+.*?\n(?:  \| [^\n]*\n)*?  \| \d+ => if s \d+ < (\d+) then s \d+ \+ 1 else (\d+)", block)
            if saturated:
                prefix = f"namespace {final}\n" + block[:saturated.end()]
                pipe_changes.append((prefix, prefix[:-len(saturated[2])] + str(int(saturated[2]) + 1), "incremented past the certified cap"))
            for step, rule in re.findall(r'namespace Step(\d+)\ndef rule : String := "([^"\n]+)"', gen_block):
                model = f"M{int(step) + 1}"
                target = gen_block.split(f"namespace {model}\n", 1)[1].split(f"end {model}\n", 1)[0]
                if rule == "constant-state-propagation/v1":
                    step_block = gen_block.split(f"namespace Step{step}\n", 1)[1].split(f"end Step{step}\n", 1)[0]
                    constraint = re.search(r"def valid[^\n]*?s \d+ = (\d+)", step_block)
                    if constraint:
                        prefix = f"namespace Step{step}\n" + step_block[:constraint.end()]
                        pipe_changes.append((prefix, prefix[:-len(constraint[1])] + str(int(constraint[1]) + 1), "assumed an incorrect inductive constant"))
                elif rule == "predicate-simplification/v1":
                    guard = re.search(r"def guard0 \(s : State\) : Prop := ([^\n]+)", target)
                    if guard:
                        prefix = f"namespace {model}\n" + target[:guard.end()]
                        pipe_changes.append((prefix, prefix[:-len(guard[1])] + f"(¬ {guard[1]})", "negated a simplified guard"))
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
                    pipe_changes.append((prefix, changed, "changed the dead-action result"))
            for before, after, label in pipe_changes:
                new_gen = replace_once_in(gen_block, before, after, path, label)
                mutated_sources.append((preamble + ns_open + new_gen + ns_close + suffix, label))
        else:
            preamble_changes = ([
                ("fun i => s.2 i ∧ q i e", "fun i => q i e", "lost prefix verdict"),
            ] if namespace == "GeneratedHistory" else [
                ("next c d := ∃ w, m.step c d w", "next c d := False ∧ ∃ w, m.step c d w", "removed reduced successors"),
                ("s.2 = m.seed s.1 w", "False ∧ s.2 = m.seed s.1 w", "removed concrete hidden initialization"),
                ("t.2 = m.update s.1 t.1 w s.2", "False ∧ t.2 = m.update s.1 t.1 w s.2", "removed concrete hidden successors"),
            ] if namespace == "GeneratedErasure" else [
                ("| .keep => n", "| .keep => 0", "discarded preserved length"),
                ("| .reset values => values.length", "| .reset values => 0", "discarded reset contents length"),
                ("previous.reduced n + 1", "previous.reduced n + 2", "appended the wrong length"),
                ("m.step s.1 t.1 w s.2", "m.step s.1 t.1 w (fun _ => 0)", "discarded length guard feedback"),
                ("m.transfer s.1 d w s.2 k", "m.transfer s.1 d w (fun _ => 0) k", "discarded length transfer feedback"),
            ] if namespace == "GeneratedLength" else [
                ("if m.live (p k) f then v k f else m.missing f", "if m.live (p k) f then m.missing f else v k f", "erased live fields"),
                ("if m.observed (p k) f then v k f else m.missing f", "v k f", "dropped observation phase mask"),
                ("s = m.project (m.seed c b w)", "s = m.seed c b w", "omitted initial projection"),
                ("t = m.project (m.advance s t.1 b w)", "t = m.project s", "dropped reduced transfers"),
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
                ("| .set xs => foldSetACList ops op base ((dedupList (xs.map mkVal)).map f)", "| .set xs => foldSetACList ops op base ((xs.map mkVal).map f)", "dropped key-set dedupList in AC fold"),
                ("| .set xs => foldSetACList ops op base ((dedupList (xs.map mkVal)).map f)", "| .set xs => foldSetACList ops op base (dedupList ((xs.map mkVal).map f))", "deduplicated mapped AC fold outputs instead of source set"),
                ("if right then items.foldr step base", "if right then items.foldl (fun acc x => step x acc) base", "swapped sequence foldRight direction to foldLeft"),
                ("Val.setFilter (Val.domain b1) (fun k =>\n        match Val.bagCountOpt ops b1 k, Val.bagCountOpt ops b2 k with\n        | some c1, some c2 => c1 - c2 > 0", "Val.setFilter (Val.domain b1) (fun k =>\n        match Val.bagCountOpt ops b1 k, Val.bagCountOpt ops b2 k with\n        | some c1, some c2 => c1 - c2 ≥ 0", "dropped positive-count filtering in bagDiff"),
                ("(Val.foldSetAC ops .intAdd (Val.domain b) (Val.atom (ops.intAtom 0)) (fun k => Val.apply b k))", "(Val.foldSetAC ops .intAdd (Val.domain b) (Val.atom (ops.intAtom 0)) (fun _ => Val.atom (ops.intAtom 1)))", "replaced bagCard count sum with domain size"),
                ("match (Val.fnLookup b k).bind (valInt ops) with\n          | some n => List.replicate n.toNat k", "match (Val.fnLookup b k).bind (valInt ops) with\n          | some _ => [k]", "dropped multiplicity replication in foldBag"),
                ("next a b := ∃ s t, project s = a ∧ m.concrete.next s t ∧ project t = b", "next a b := False ∧ ∃ s t, project s = a ∧ m.concrete.next s t ∧ project t = b", "discarded quotient successors"),
                ("initial a := ∃ s, m.concrete.initial s ∧ project s = a", "initial a := False ∧ ∃ s, m.concrete.initial s ∧ project s = a", "discarded quotient initialization"),
            ] if namespace in {"GeneratedEquivSymmetry", "GeneratedErasedEquivSymmetry"} else [
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
            ] if namespace == "GeneratedLive" else [
                ("min (n + delta) cap", "min (n + delta - delta) cap", "failed to advance capped ages"),
                ("| .reset, _ => some 0", "| .reset, _ => some cap", "reset to the wrong age"),
                ("| .erase, _ => none\n\ntheorem update_commutes", "| .erase, a => a\n\ntheorem update_commutes", "failed to erase a timestamp"),
                ("h k = some n ∧ d ≤ n", "h k = some n ∧ d < n", "changed deadline strictness"),
            ] if namespace in {"GeneratedAge", "GeneratedAgeHistory"} else [
                ("| .le, t => t + 1", "| .le, t => t", "off-by-one cap on <= comparison"),
                ("| .add d => min (a i + d) (cap i)", "| .add d => min (a i) (cap i)", "dropped increment in reduced transfer"),
                ("(m.guard a.1 b.1 w).eval a.2", "(m.guard a.1 b.1 w).eval (fun _ => 0)", "discarded threshold guard feedback"),
            ] if namespace == "GeneratedThresholdCounter" else [
                ("(phase m.seed s.1.val, s.2)", "(false, s.2)", "forgot the initial anchor"),
                ("t.1 = (s.1 && decide (m.delta w = 0))", "t.1 = s.1", "failed to advance the reduced phase"),
            ])
            if namespace == "GeneratedErasedSymmetry":
                preamble_changes.append(("t.2 = m.hiddenUpdate b s.1 w keys s.2", "False ∧ t.2 = m.hiddenUpdate b s.1 w keys s.2", "removed concrete hidden successors"))
            if namespace == "GeneratedErasedEquivSymmetry":
                preamble_changes.extend([
                    ("s.2 = m.hiddenSeed b s.1 ws", "False ∧ s.2 = m.hiddenSeed b s.1 ws", "removed concrete hidden initialization"),
                    ("t.2 = m.hiddenUpdate b s.1 t.1 ws s.2", "False ∧ t.2 = m.hiddenUpdate b s.1 t.1 ws s.2", "removed concrete hidden successors"),
                ])
            if namespace in {"GeneratedAge", "GeneratedAgeHistory"} and has_select:
                preamble_changes.extend([
                    ("(b = true ↔ p.reduced h)", "(b = false ↔ p.reduced h)", "inverted filter decision"),
                    ("consume (if b then k :: selected else selected)", "consume (if b then selected else k :: selected)", "inverted selected key membership"),
                ])
            if namespace in {"GeneratedAge", "GeneratedAgeHistory"} and has_bind:
                preamble_changes.append(("(next b).reduced h", "(next (!b)).reduced h", "passed the wrong Boolean to the consumer"))
            if has_commutes:
                preamble_changes.extend([
                    ("(yes.reduced h) (no.reduced h)", "(no.reduced h) (yes.reduced h)", "swapped reduced update decision"),
                    (".branch p (yes.bindValue f) (no.bindValue f)", ".branch p (no.bindValue f) (yes.bindValue f)", "swapped value continuation branches"),
                ])
            if namespace == "GeneratedHistory":
                preamble_changes.extend([
                    ("m.step s.1 t.1 w s.2", "m.step s.1 t.1 w (History.summary m.predicate History.empty)", "discarded guard feedback"),
                    ("m.transfer s.1 t.1 w s.2", "m.transfer s.1 t.1 w (History.summary m.predicate History.empty)", "discarded transfer feedback"),
                ])
            if namespace == "GeneratedAgeHistory":
                preamble_changes.extend([
                    ("fun i => s.2 i ∧ q i e", "fun i => q i e", "lost prefix verdict"),
                    ("m.guard s.1.1 t.1.1 w (presence s.1.2) s.2", "m.guard s.1.1 t.1.1 w (presence s.1.2) (History.summary m.predicate History.empty)", "discarded guard feedback"),
                    ("m.historyTransfer s.1.1 d w (presence s.1.2) s.2", "m.historyTransfer s.1.1 d w (presence s.1.2) (History.summary m.predicate History.empty)", "discarded transfer feedback"),
                    ("((m.historyTransfer s.1.1 d w (presence s.1.2) s.2).reduced s.1.2).reduced m.predicate s.2" if has_commutes else "(m.historyTransfer s.1.1 d w (presence s.1.2) s.2).reduced m.predicate s.2", "(HistoryRule.Transfer.keep).reduced m.predicate s.2", "dropped the shared branch history transfer"),
                    ("(m.age.project s.1, History.summary m.predicate s.2)", "(m.age.project s.1, History.summary m.predicate History.empty)", "discarded observed history"),
                ])
            if namespace == "GeneratedAgeHistory" and has_commutes:
                preamble_changes.append(("m.change s.1.1 d w (presence s.1.2) s.2 k", "m.change s.1.1 d w (presence s.1.2) (History.summary m.predicate History.empty) k", "discarded timestamp history feedback"))
            for before, after, label in preamble_changes:
                add_preamble_mutation(before, after, label)

            if namespace == "GeneratedField":
                # A dead-to-live write is the frame obligation's sharpest case:
                # abandoning the write must break `advance_commutes`, not just
                # the read tables.
                add_preamble_mutation(
                    "fun k f => if k = a ∧ m.writes b f = true then m.value b s.1 d w s.2.1 input f else s.2.2 k f",
                    "fun k f => if k = a ∧ False then m.value b s.1 d w s.2.1 input f else s.2.2 k f",
                    "exposed a dead-to-live write to the concrete state",
                )
                add_gen_decl_mutation(
                    r"^  readsActor := readsActor$",
                    lambda _: "  readsActor := fun _ _ => true",
                    "read dead actor fields",
                )
                if field_write_can_break_frame(lean, path, preamble + ns_open + gen_block + ns_close + suffix, lean_pool):
                    add_gen_decl_mutation(
                        r"^  writes := writes$",
                        lambda _: "  writes := fun _ _ => false",
                        "exposed dead framed fields",
                    )
                add_gen_decl_mutation(
                    r"^  readsGlobal := readsGlobal$",
                    lambda _: "  readsGlobal := fun _ _ => true",
                    "read dead fields of another actor",
                )
                add_gen_decl_mutation(
                    r"^  observed := observed$",
                    lambda _: "  observed := fun _ _ => true",
                    "observed dead field in a dead phase",
                )

            after_pat = r"^def after := \(model sem\)\.reduced$"
            if namespace == "GeneratedLive":
                add_gen_decl_mutation(
                    after_pat,
                    lambda _: "def after := { (model sem).reduced with next := fun _ _ => False }",
                    "discarded live-version successors",
                )
                add_gen_decl_mutation(
                    after_pat,
                    lambda _: "def after := { (model sem).reduced with initial := fun _ => False }",
                    "discarded live-version initialization",
                )
            add_gen_decl_mutation(
                after_pat,
                lambda _: "def after := { (model sem).reduced with safe := fun _ => True }",
                "changed reduced observation",
            )
            if is_constrained:
                constrained_pat = r"^def constrainedAfter := \(model sem\)\.constrainedReduced$"
                for field_expr, label in (
                    ("constraint := fun a => ¬ (model sem).constrainedReduced.constraint a", "negated reduced state constraint"),
                    ("initSafe := fun a => ¬ (model sem).constrainedReduced.initSafe a", "negated reduced initSafe"),
                    ("actionSafe := fun a b => ¬ (model sem).constrainedReduced.actionSafe a b", "negated reduced actionSafe"),
                    ("actionConstraint := fun a b => ¬ (model sem).constrainedReduced.actionConstraint a b", "negated reduced actionConstraint"),
                ):
                    add_gen_decl_mutation(
                        constrained_pat,
                        lambda _, fe=field_expr: f"def constrainedAfter := {{ (model sem).constrainedReduced with {fe} }}",
                        label,
                    )
            if has_const_expanded:
                add_gen_decl_mutation(
                    r'^(def constSubstExpanded \(i : Fin ConstSubstCount\) : String :=\n(?:  .*\n)*?  *if i\.val = 0 then )"((?:[^"\\]|\\.)*)"( else "")$',
                    lambda m: f'{m.group(1)}"{m.group(2)}_mismatch"{m.group(3)}',
                    "mismatched constant substitution expansion",
                )
                add_gen_decl_mutation(
                    r"^  \(hModel : sys \(fun i => eval \(constSubstExpanded i\)\) = before sem\) :$",
                    lambda _: '  (hModel : sys (fun _ => eval "") = before sem) :',
                    "disconnected constant substitution model expansion",
                )

    return namespace, theorems, axioms, mutated_sources


def check_mutation(lean, path, item):
    mutated, label = item
    with tempfile.TemporaryDirectory(prefix="tlx-generated-proof-") as tmp:
        bad = Path(tmp) / "Broken.lean"
        bad.write_text(mutated)
        rejected = invoke(lean, bad)
    if rejected.returncode == 0 or not any(
        marker in rejected.stdout for marker in
        ("error: Tactic", "error: 'change' tactic failed", "error: Type mismatch", "error: type mismatch", "error: Application type mismatch", "error: unsolved goals", "error: omega could not prove the goal", "error: invalid `▸` notation")
    ):
        raise RuntimeError(f"{path}: mutation was not rejected: {label}\n{rejected.stdout}")
    return {"change": label, "diagnostic": rejected.stdout}


def verify(lean, path, negative, lean_pool=None):
    namespace, theorems, axioms, mutated_sources = plan_certificate(lean, path, negative, lean_pool, run_positive=True)
    mutations = []
    if negative:
        if lean_pool is not None:
            mutations = list(lean_pool.map(lambda item: check_mutation(lean, path, item), mutated_sources))
        else:
            mutations = [check_mutation(lean, path, item) for item in mutated_sources]

    print(f"PASS: {path} ({len(theorems)} theorem audits, {len(mutations)} rejected mutations)")
    return {
        "file": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "axioms": axioms, "rejected_mutations": mutations,
        "scope": ("Closed counter-pipeline IR; source lowering, TLA+ emission and runtime remain trusted."
                  if namespace == "GeneratedPipeline" else
                  f"Parametric {namespace} rule IR; lowering, totality and runtime remain trusted."),
    }


def verify_sharded(lean, paths, negative, workers, shard_index, shard_total):
    """Run a deterministic round-robin shard of all positive and negative Lean checks.

    Sharding at the individual-check level balances heavy certificate families
    evenly across shards while ensuring that shards 1/N..N/N together run the
    exact same checks as an unsharded run.
    """
    specs = []
    tasks = []
    for cert_idx, path in enumerate(paths):
        namespace, theorems, _, mutated_sources = plan_certificate(lean, path, negative, lean_pool=None, run_positive=False)
        specs.append((path, namespace, theorems))
        tasks.append(("pos", cert_idx, None))
        for item in mutated_sources:
            tasks.append(("neg", cert_idx, item))

    selected = [task for i, task in enumerate(tasks) if i % shard_total == (shard_index - 1)]

    def run_task(task):
        kind, cert_idx, payload = task
        path, namespace, theorems = specs[cert_idx]
        if kind == "pos":
            return ("pos", cert_idx, check_positive(lean, path, namespace, theorems))
        return ("neg", cert_idx, check_mutation(lean, path, payload))

    if workers == 1:
        outcomes = [run_task(t) for t in selected]
    else:
        with ThreadPoolExecutor(max_workers=workers) as lean_pool:
            outcomes = list(lean_pool.map(run_task, selected))

    by_cert = {i: {"axioms": None, "mutations": []} for i in range(len(specs))}
    pos_count = neg_count = 0
    for kind, cert_idx, value in outcomes:
        if kind == "pos":
            by_cert[cert_idx]["axioms"] = value
            pos_count += 1
        else:
            by_cert[cert_idx]["mutations"].append(value)
            neg_count += 1

    results = []
    for cert_idx, (path, namespace, theorems) in enumerate(specs):
        entry = by_cert[cert_idx]
        if entry["axioms"] is None and not entry["mutations"]:
            continue
        audits = len(theorems) if entry["axioms"] is not None else 0
        print(f"PASS: {path} ({audits} theorem audits, {len(entry['mutations'])} rejected mutations)")
        results.append({
            "file": str(path), "sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "axioms": entry["axioms"] or {}, "rejected_mutations": entry["mutations"],
            "scope": ("Closed counter-pipeline IR; source lowering, TLA+ emission and runtime remain trusted."
                      if namespace == "GeneratedPipeline" else
                      f"Parametric {namespace} rule IR; lowering, totality and runtime remain trusted."),
        })
    print(f"Shard {shard_index}/{shard_total}: {pos_count} positive, {neg_count} negative checks passed")
    return results


def find_lean(requested):
    lean = shutil.which(requested)
    if lean is None and requested == "lean":
        candidate = Path.home() / ".elan" / "bin" / "lean"
        if candidate.is_file() and os.access(candidate, os.X_OK):
            lean = str(candidate)
    if lean is None:
        return None
    return os.path.abspath(lean)  # Preserve an elan dispatcher's invoked name.


def find_tlx(requested):
    if requested:
        path = Path(requested)
        if path.is_file() and os.access(path, os.X_OK):
            return str(path.resolve())
        found = shutil.which(requested)
        return os.path.abspath(found) if found else None
    for rel in ("target/test-release/tlx", "target/release/tlx", "target/debug/tlx"):
        candidate = ROOT / rel
        if candidate.is_file() and os.access(candidate, os.X_OK):
            return str(candidate)
    found = shutil.which("tlx")
    return os.path.abspath(found) if found else None


def generate_default_certificates(tlx, workdir):
    generated = []
    covered = set()
    for index, (namespace, subcommand, spec_rel, inline_cfg, extra_args, ok_codes) in enumerate(DEFAULT_CASES):
        spec = ROOT / spec_rel
        # One output directory per case: several cases share a namespace, and
        # each run must produce exactly one certificate for the assertion below.
        case_dir = workdir / namespace / f"{index:02d}-{Path(spec_rel).stem}"
        case_dir.mkdir(parents=True, exist_ok=True)
        if subcommand == "optimize":
            out_dir = case_dir / "out"
            cmd = [tlx, "optimize", str(spec), "-output", str(out_dir), *extra_args]
            result = subprocess.run(cmd, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120, check=False)
            if result.returncode not in ok_codes:
                raise RuntimeError(f"{namespace}: tlx optimize failed ({result.returncode}):\n{result.stdout}")
            cert = out_dir / "Optimization.lean"
        else:
            proof_dir = case_dir / "proofs"
            cmd = [tlx, "check", str(spec)]
            if inline_cfg is not None:
                cfg_path = case_dir / "Model.cfg"
                cfg_path.write_text(inline_cfg)
                cmd.extend(["-config", str(cfg_path)])
            cmd.extend(["-proofdir", str(proof_dir), *extra_args])
            result = subprocess.run(cmd, cwd=ROOT, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120, check=False)
            if result.returncode not in ok_codes:
                raise RuntimeError(f"{namespace}: tlx check failed ({result.returncode}):\n{result.stdout}")
            certs = sorted(proof_dir.glob("*/Optimization.lean"))
            if len(certs) != 1:
                raise RuntimeError(f"{namespace}: expected 1 generated certificate under {proof_dir}, found {len(certs)}\n{result.stdout}")
            cert = certs[0]
        if not re.search(rf"(?m)^namespace TlxOptimization\.{re.escape(namespace)}$", cert.read_text()):
            raise RuntimeError(f"{namespace}: generated {cert} does not contain expected namespace TlxOptimization.{namespace}")
        covered.add(namespace)
        generated.append(cert)
    missing = set(SUPPORTED_NAMESPACES) - covered
    if missing:
        raise RuntimeError(f"default certificate suite does not cover namespaces: {sorted(missing)}")
    return generated


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", type=Path, nargs="*", help="generated Optimization.lean files (omit to generate and verify all supported certificate families)")
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--tlx", default="", help="tlx binary used to generate certificates when no files are given")
    parser.add_argument("--jobs", type=int, default=min(os.cpu_count() or 1, 4), help="parallel Lean verifications (default: min(cpus, 4))")
    parser.add_argument("--shard", type=parse_shard, default=None, metavar="INDEX/TOTAL", help="run only deterministic 1-based shard INDEX of TOTAL across all checks")
    parser.add_argument("--negative", action="store_true", help="also require deliberately broken proofs to fail")
    parser.add_argument("--report", type=Path, help="write a JSON receipt after all checks pass")
    args = parser.parse_args()
    lean = find_lean(args.lean)
    if lean is None:
        parser.error(f"Lean executable not found: {args.lean}")
    try:
        version = subprocess.run([lean, "--version"], capture_output=True, text=True, timeout=30, check=True).stdout.strip()
        with tempfile.TemporaryDirectory(prefix="tlx-generated-suite-") as tmp:
            if args.files:
                paths = [p.resolve() for p in args.files]
            else:
                tlx = find_tlx(args.tlx)
                if tlx is None:
                    raise RuntimeError("tlx binary not found; build with `cargo build --profile test-release -p tlx-cli` or pass --tlx")
                paths = generate_default_certificates(tlx, Path(tmp))
            workers = max(1, args.jobs)
            if args.shard is not None and args.shard[1] > 1:
                results = verify_sharded(lean, paths, args.negative, workers, args.shard[0], args.shard[1])
            elif workers == 1:
                results = [verify(lean, p, args.negative) for p in paths]
            else:
                with ThreadPoolExecutor(max_workers=min(workers, len(paths))) as outer_pool, \
                     ThreadPoolExecutor(max_workers=workers) as lean_pool:
                    results = list(outer_pool.map(lambda p: verify(lean, p, args.negative, lean_pool), paths))
        if args.report:
            args.report.write_text(json.dumps({"lean": version, "trust_level": 0, "results": results}, indent=2) + "\n")
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        parser.exit(1, f"{error}\n")


if __name__ == "__main__":
    main()
