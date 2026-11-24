//! Render a standalone `GeneratedEquivSymmetry` Lean certificate instantiating
//! `EquivSymCertificate.lean` with the model's exact lowered Init/Next/Inv ASTs.

use std::fmt::Write;

use super::{lower::LowerCtx, GroupInfo};
use crate::{hir::Expr, optimize::lean::literal, Program};

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
    writeln!(out, "abbrev GroupCount : Nat := {}", groups.len()).unwrap();
    out.push_str("def groupSizes (g : Fin GroupCount) : Nat :=\n  match g.val with\n");
    for (i, g) in groups.iter().enumerate() {
        writeln!(out, "  | {i} => {}", g.keys.len()).unwrap();
    }
    out.push_str("  | _ => 0\n");
    writeln!(out, "abbrev VarId := Fin {}", program.vars.len()).unwrap();
    writeln!(
        out,
        "def layout : String := {}",
        literal(&format!(
            "Disjoint product of {} full permutation group(s) {:?}; {} variables in recursive equivariant Val",
            groups.len(),
            groups.iter().map(|g| &g.keys).collect::<Vec<_>>(),
            program.vars.len(),
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
