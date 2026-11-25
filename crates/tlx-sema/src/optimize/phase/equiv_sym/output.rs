//! Render a standalone `GeneratedEquivSymmetry` Lean certificate instantiating
//! `EquivSymCertificate.lean` with the model's exact lowered Init/Next/Inv ASTs.

use std::fmt::Write;

use super::{lower::LowerCtx, GroupInfo};
use crate::{
    hir::{Expr, VarId},
    optimize::lean::literal,
    Program,
};

pub(super) struct Forms<'a> {
    pub(super) init: &'a str,
    pub(super) next: &'a str,
    pub(super) obs: &'a str,
    pub(super) init_obs: &'a str,
    pub(super) constraint: &'a str,
    pub(super) action_constraint: &'a str,
    pub(super) action_obs: &'a str,
    pub(super) constrained: bool,
}

pub(super) struct ErasedBranch {
    pub(super) bounds: Vec<String>,
    pub(super) body: String,
    pub(super) hidden: Vec<String>,
}

pub(super) struct ErasedSpec<'a> {
    pub(super) retained_count: usize,
    pub(super) omitted: &'a [VarId],
    pub(super) init_branches: &'a [ErasedBranch],
    pub(super) step_branches: &'a [ErasedBranch],
    pub(super) hidden_atoms: &'a [String],
    pub(super) obs: &'a str,
    pub(super) init_obs: &'a str,
    pub(super) constraint: &'a str,
    pub(super) action_constraint: &'a str,
    pub(super) action_obs: &'a str,
    pub(super) constrained: bool,
}

fn write_common_header(out: &mut String, groups: &[GroupInfo], var_count: usize, ctx: &LowerCtx<'_>, initial: &Expr) {
    writeln!(out, "abbrev GroupCount : Nat := {}", groups.len()).unwrap();
    out.push_str("def groupSizes (g : Fin GroupCount) : Nat :=\n  match g.val with\n");
    for (i, g) in groups.iter().enumerate() {
        writeln!(out, "  | {i} => {}", g.keys.len()).unwrap();
    }
    out.push_str("  | _ => 0\n");
    writeln!(out, "abbrev VarId := Fin {var_count}").unwrap();
    writeln!(
        out,
        "def layout : String := {}",
        literal(&format!(
            "Disjoint product of {} full permutation group(s) {:?}; {var_count} retained variables in recursive equivariant Val",
            groups.len(),
            groups.iter().map(|g| &g.keys).collect::<Vec<_>>(),
        ))
    )
    .unwrap();
    writeln!(out, "def initialHIR : String := {}", literal(&format!("{initial:#?}"))).unwrap();
    for (i, atom) in ctx.atoms.iter().enumerate() {
        writeln!(out, "def atom{i} : String := {}", literal(&atom.describe())).unwrap();
    }
    for (i, op) in ctx.atom_ops.iter().enumerate() {
        writeln!(out, "def atomOp{i} : String := {}", literal(op)).unwrap();
    }
    for (i, op) in ctx.atom_set_ops.iter().enumerate() {
        writeln!(out, "def atomSetOp{i} : String := {}", literal(op)).unwrap();
    }
    for (i, op) in ctx.atom_set_aggs.iter().enumerate() {
        writeln!(out, "def atomSetAgg{i} : String := {}", literal(op)).unwrap();
    }
    for (i, rel) in ctx.atom_rels.iter().enumerate() {
        writeln!(out, "def atomRel{i} : String := {}", literal(rel)).unwrap();
    }
    for (i, pred) in ctx.atom_preds.iter().enumerate() {
        writeln!(out, "def atomPred{i} : String := {}", literal(pred)).unwrap();
    }
}

pub(super) fn render(
    program: &Program,
    groups: &[GroupInfo],
    ctx: &LowerCtx<'_>,
    initial: &Expr,
    forms: &Forms<'_>,
) -> super::super::OpenCert {
    let mut out = String::from(include_str!("../../EquivSymCertificate.lean"));
    out.push_str("\nnamespace TlxOptimization.GeneratedEquivSymmetry\n");
    out.push_str(
        "open TlxOptimization EquivRule\n\
         noncomputable section\n\
         set_option linter.unusedVariables false\n\
         set_option maxRecDepth 20000\n",
    );
    write_common_header(&mut out, groups, program.vars.len(), ctx, initial);
    out.push_str(
        "-- A contains key-free atoms only (integers, strings, booleans, unmoved model values).\n\
         -- Lowering, leaf atom interpretation, totality, group closure and runtime\n\
         -- canonicalization remain trusted.\n\
         abbrev Semantics (A : Type) := EquivRule.AtomOps A\n",
    );
    writeln!(out, "def initForm : Form GroupCount VarId := {}", forms.init).unwrap();
    writeln!(out, "def nextForm : Form GroupCount VarId := {}", forms.next).unwrap();
    writeln!(out, "def obsForm : Form GroupCount VarId := {}", forms.obs).unwrap();
    if forms.constrained {
        writeln!(out, "def initObsForm : Form GroupCount VarId := {}", forms.init_obs).unwrap();
        writeln!(out, "def constraintForm : Form GroupCount VarId := {}", forms.constraint).unwrap();
        writeln!(out, "def actionConstraintForm : Form GroupCount VarId := {}", forms.action_constraint).unwrap();
        writeln!(out, "def actionObsForm : Form GroupCount VarId := {}", forms.action_obs).unwrap();
        out.push_str(
            "variable {A : Type} [HasNatAtom A] (sem : Semantics A)\n\
             def model : EquivRule.Model GroupCount groupSizes VarId A where\n\
             \x20 ops := sem\n\
             \x20 initForm := initForm\n\
             \x20 nextForm := nextForm\n\
             \x20 obsForm := obsForm\n\
             \x20 initObsForm := initObsForm\n\
             \x20 constraintForm := constraintForm\n\
             \x20 actionConstraintForm := actionConstraintForm\n\
             \x20 actionObsForm := actionObsForm\n",
        );
    } else {
        out.push_str(
            "variable {A : Type} [HasNatAtom A] (sem : Semantics A)\n\
             def model : EquivRule.Model GroupCount groupSizes VarId A where\n\
             \x20 ops := sem\n\
             \x20 initForm := initForm\n\
             \x20 nextForm := nextForm\n\
             \x20 obsForm := obsForm\n",
        );
    }
    super::super::OpenCert::new(out, include_str!("certificate.lean"), "GeneratedEquivSymmetry", forms.constrained, false, false)
}

pub(super) fn render_erased(groups: &[GroupInfo], ctx: &LowerCtx<'_>, initial: &Expr, spec: &ErasedSpec<'_>) -> super::super::OpenCert {
    let mut out = String::from(include_str!("../../EquivSymCertificate.lean"));
    out.push_str(include_str!("../../ErasedEquivCertificate.lean"));
    out.push_str("\nnamespace TlxOptimization.GeneratedErasedEquivSymmetry\n");
    out.push_str(
        "open TlxOptimization EquivRule ErasedEquivRule\n\
         noncomputable section\n\
         set_option linter.unusedVariables false\n\
         set_option maxRecDepth 20000\n",
    );
    write_common_header(&mut out, groups, spec.retained_count, ctx, initial);
    writeln!(
        out,
        "def erasedVariables : String := {}",
        literal(&format!("omitted variable indices {:?}; retained variables stay in source order", spec.omitted))
    )
    .unwrap();
    for (i, atom) in spec.hidden_atoms.iter().enumerate() {
        writeln!(out, "def hiddenAtom{i}HIR : String := {}", literal(atom)).unwrap();
    }
    writeln!(out, "abbrev Hidden (H : Type) := Fin {} → H", spec.omitted.len()).unwrap();
    out.push_str(
        "-- A contains key-free atoms only; H is the erased hidden-variable value type.\n\
         -- Lowering, leaf atom interpretation, totality, group closure and runtime\n\
         -- canonicalization remain trusted.\n\
         structure Semantics (A H : Type) [HasNatAtom A] where\n\
         \x20 ops : EquivRule.AtomOps A\n\
         \x20 hiddenSeed : Nat → State VarId groupSizes A → List (Val groupSizes A) → H\n\
         \x20 hiddenUpdate : Nat → State VarId groupSizes A → State VarId groupSizes A → List (Val groupSizes A) → Hidden H → H\n\
         \x20 number : Int → H\n\
         \x20 string : String → H\n\
         \x20 boolean : Bool → H\n",
    );
    let write_branches = |out: &mut String, name: &str, bs: &[ErasedBranch]| {
        writeln!(out, "def {name} : List (ErasedEquivRule.Branch GroupCount VarId) := [").unwrap();
        for (i, b) in bs.iter().enumerate() {
            let comma = if i + 1 < bs.len() { "," } else { "" };
            writeln!(out, "  ⟨[{}], {}⟩{comma}", b.bounds.join(", "), b.body).unwrap();
        }
        out.push_str("]\n");
    };
    write_branches(&mut out, "initBranches", spec.init_branches);
    write_branches(&mut out, "stepBranches", spec.step_branches);
    writeln!(out, "def obsForm : Form GroupCount VarId := {}", spec.obs).unwrap();
    if spec.constrained {
        writeln!(out, "def initObsForm : Form GroupCount VarId := {}", spec.init_obs).unwrap();
        writeln!(out, "def constraintForm : Form GroupCount VarId := {}", spec.constraint).unwrap();
        writeln!(out, "def actionConstraintForm : Form GroupCount VarId := {}", spec.action_constraint).unwrap();
        writeln!(out, "def actionObsForm : Form GroupCount VarId := {}", spec.action_obs).unwrap();
    }
    out.push_str(
        "variable {A H : Type} [HasNatAtom A] (sem : Semantics A H)\n\
         def hiddenSeed {A H : Type} [HasNatAtom A] (sem : Semantics A H) (b : Fin initBranches.length) (s : State VarId groupSizes A) (ws : List (Val groupSizes A)) : Hidden H :=\n\
         \x20 match b.val with\n",
    );
    for (bi, b) in spec.init_branches.iter().enumerate() {
        writeln!(out, "  | {bi} => fun i => match i.val with").unwrap();
        for (hi, hval) in b.hidden.iter().enumerate() {
            writeln!(out, "      | {hi} => {hval}").unwrap();
        }
        out.push_str("      | _ => sem.boolean false\n");
    }
    out.push_str(
        "  | _ => fun _ => sem.boolean false\n\
         def hiddenUpdate {A H : Type} [HasNatAtom A] (sem : Semantics A H) (b : Fin stepBranches.length) (s t : State VarId groupSizes A) (ws : List (Val groupSizes A)) (h : Hidden H) : Hidden H :=\n\
         \x20 match b.val with\n",
    );
    for (bi, b) in spec.step_branches.iter().enumerate() {
        writeln!(out, "  | {bi} => fun i => match i.val with").unwrap();
        for (hi, hval) in b.hidden.iter().enumerate() {
            writeln!(out, "      | {hi} => {hval}").unwrap();
        }
        out.push_str("      | _ => sem.boolean false\n");
    }
    out.push_str(
        "  | _ => fun _ => sem.boolean false\n\
         def model : ErasedEquivRule.Model GroupCount groupSizes VarId A (Hidden H) where\n\
         \x20 ops := sem.ops\n\
         \x20 initBranches := initBranches\n\
         \x20 hiddenSeed := hiddenSeed sem\n\
         \x20 stepBranches := stepBranches\n\
         \x20 hiddenUpdate := hiddenUpdate sem\n\
         \x20 obsForm := obsForm\n",
    );
    if spec.constrained {
        out.push_str(
            "  initObsForm := initObsForm\n\
             \x20 constraintForm := constraintForm\n\
             \x20 actionConstraintForm := actionConstraintForm\n\
             \x20 actionObsForm := actionObsForm\n",
        );
    }
    super::super::OpenCert::new(out, include_str!("erasure.lean"), "GeneratedErasedEquivSymmetry", spec.constrained, true, false)
}
