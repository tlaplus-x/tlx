//! Render a standalone `GeneratedThresholdSymmetry` Lean certificate
//! instantiating `ThresholdSymCertificate.lean` (over
//! `ThresholdCounterCertificate.lean`, `EquivSymCertificate.lean`, and
//! `OrbitQuotient.lean`).

use std::fmt::Write;

use crate::{hir::Expr, optimize::lean::literal};

use super::super::super::{
    equiv_sym::{lower::LowerCtx, output::write_common_header, GroupInfo},
    OpenCert,
};
use super::{InitBranchData, SlotInfo, StepBranchData};

pub(super) struct RenderSpec<'a> {
    pub(super) groups: &'a [GroupInfo],
    pub(super) ctx: &'a LowerCtx<'a>,
    pub(super) orig_init: &'a Expr,
    pub(super) core_count: usize,
    pub(super) slots: &'a [SlotInfo],
    pub(super) template_count: usize,
    pub(super) branch_count: usize,
    pub(super) init_branches: &'a [InitBranchData],
    pub(super) step_branches: &'a [StepBranchData],
    pub(super) obs_test: &'a str,
    pub(super) init_obs_test: &'a str,
    pub(super) constraint_test: &'a str,
    pub(super) action_constraint_form: &'a str,
    pub(super) action_obs_form: &'a str,
    pub(super) constrained: bool,
}

pub(super) fn render(spec: &RenderSpec<'_>) -> OpenCert {
    let mut out = String::from(include_str!("../../../ThresholdCounterCertificate.lean"));
    out.push_str(include_str!("../../../EquivSymCertificate.lean"));
    out.push_str(include_str!("../../../OrbitQuotient.lean"));
    out.push_str(include_str!("../../../ThresholdSymCertificate.lean"));
    out.push_str("\nnamespace TlxOptimization.GeneratedThresholdSymmetry\n");
    out.push_str(
        "open TlxOptimization ThresholdCounterRule EquivRule ThresholdSymRule\n\
         noncomputable section\n\
         set_option linter.unusedVariables false\n\
         set_option maxRecDepth 20000\n",
    );
    write_common_header(&mut out, spec.groups, spec.core_count, spec.ctx, spec.orig_init);
    writeln!(out, "abbrev CoreVar := VarId").unwrap();
    writeln!(out, "abbrev SlotCount : Nat := {}", spec.slots.len()).unwrap();
    writeln!(out, "abbrev TemplateCount : Nat := {}", spec.template_count).unwrap();
    writeln!(out, "abbrev BranchCount : Nat := {}", spec.branch_count).unwrap();

    write_slot_tables(&mut out, spec.slots);
    write_branch_tables(&mut out, spec.init_branches, spec.step_branches);

    writeln!(out, "def obsTest : SymTest GroupCount cap CoreVar := {}", spec.obs_test).unwrap();
    if spec.constrained {
        writeln!(out, "def initObsTest : SymTest GroupCount cap CoreVar := {}", spec.init_obs_test).unwrap();
        writeln!(out, "def constraintTest : SymTest GroupCount cap CoreVar := {}", spec.constraint_test).unwrap();
        writeln!(out, "def actionConstraintForm : Form GroupCount CoreVar := {}", spec.action_constraint_form).unwrap();
        writeln!(out, "def actionObsForm : Form GroupCount CoreVar := {}", spec.action_obs_form).unwrap();
    }

    out.push_str(
        "abbrev Semantics (A : Type) := EquivRule.AtomOps A\n\
         variable {A : Type} [HasNatAtom A] (sem : Semantics A)\n\
         def model : ThresholdSymRule.Model GroupCount groupSizes CoreVar SlotCount TemplateCount BranchCount A where\n\
         \x20 ops := sem\n\
         \x20 cap := cap\n\
         \x20 slotInfo := slotInfo\n\
         \x20 fixedSlotAtom := fixedSlotAtom\n\
         \x20 slotTemplate := slotTemplate\n\
         \x20 slotBounds := by decide\n\
         \x20 slotClosed := by decide\n\
         \x20 capUniform := by decide\n\
         \x20 templateUniform := by decide\n\
         \x20 initValid := initValid\n\
         \x20 initBounds := initBounds\n\
         \x20 initGuard := initGuard\n\
         \x20 initSeed := initSeed\n\
         \x20 stepValid := stepValid\n\
         \x20 stepBounds := stepBounds\n\
         \x20 stepGuard := stepGuard\n\
         \x20 stepTransfer := stepTransfer\n\
         \x20 obsTest := obsTest\n",
    );
    if spec.constrained {
        out.push_str(
            "  initObsTest := initObsTest\n\
             \x20 constraintTest := constraintTest\n\
             \x20 actionConstraintForm := actionConstraintForm\n\
             \x20 actionObsForm := actionObsForm\n",
        );
    }
    out.push_str(
        "  stepGuardValid := by decide\n\
         \x20 stepTransferValid := by decide\n\
         \x20 obsValid := by decide\n\
         \x20 initObsValid := by decide\n\
         \x20 constraintValid := by decide\n",
    );

    OpenCert::new_composed(
        out,
        include_str!("../sym.lean"),
        "GeneratedThresholdSymmetry",
        spec.constrained,
        "threshold",
        "thresholdProject",
    )
}

fn write_slot_tables(out: &mut String, slots: &[SlotInfo]) {
    for (k, s) in slots.iter().enumerate() {
        let desc = match s {
            SlotInfo::Fixed { desc, .. } | SlotInfo::Sym { desc, .. } => desc,
        };
        writeln!(out, "def slot{k}Desc : String := {}", literal(desc)).unwrap();
    }

    out.push_str("def cap (k : Fin SlotCount) : Nat :=\n  match k.val with\n");
    for (k, s) in slots.iter().enumerate() {
        let c = match s {
            SlotInfo::Fixed { cap, .. } | SlotInfo::Sym { cap, .. } => *cap,
        };
        writeln!(out, "  | {k} => {c}").unwrap();
    }
    out.push_str("  | _ => 0\n");

    out.push_str(
        "def slotInfo (k : Fin SlotCount) : Option (Nat × Sigma (fun g : Fin GroupCount => Fin (groupSizes g))) :=\n  match k.val with\n",
    );
    for (k, s) in slots.iter().enumerate() {
        match s {
            SlotInfo::Fixed { .. } => writeln!(out, "  | {k} => none").unwrap(),
            SlotInfo::Sym { off, group, elem, .. } => {
                writeln!(out, "  | {k} => some ({off}, ⟨⟨{group}, by decide⟩, ⟨{elem}, by decide⟩⟩)").unwrap();
            }
        }
    }
    out.push_str("  | _ => none\n");

    out.push_str("def fixedSlotAtom (k : Fin SlotCount) : Nat :=\n  match k.val with\n");
    for (k, s) in slots.iter().enumerate() {
        if let SlotInfo::Fixed { atom_id, .. } = s {
            if *atom_id != 0 {
                writeln!(out, "  | {k} => {atom_id}").unwrap();
            }
        }
    }
    out.push_str("  | _ => 0\n");

    out.push_str("def slotTemplate (k : Fin SlotCount) : Fin TemplateCount :=\n  match k.val with\n");
    for (k, s) in slots.iter().enumerate() {
        let t = match s {
            SlotInfo::Fixed { template, .. } | SlotInfo::Sym { template, .. } => *template,
        };
        writeln!(out, "  | {k} => ⟨{t}, by decide⟩").unwrap();
    }
    out.push_str("  | _ => ⟨0, by decide⟩\n");
}

fn write_branch_tables(out: &mut String, init_branches: &[InitBranchData], step_branches: &[StepBranchData]) {
    out.push_str("def initValid (b : Fin BranchCount) : Bool :=\n  match b.val with\n");
    for bi in 0..init_branches.len() {
        writeln!(out, "  | {bi} => true").unwrap();
    }
    out.push_str("  | _ => false\n");

    out.push_str("def initBounds (b : Fin BranchCount) : List (SetPred GroupCount CoreVar) :=\n  match b.val with\n");
    for (bi, b) in init_branches.iter().enumerate() {
        writeln!(out, "  | {bi} => [{}]", b.bounds.join(", ")).unwrap();
    }
    out.push_str("  | _ => []\n");

    out.push_str("def initGuard (b : Fin BranchCount) : Form GroupCount CoreVar :=\n  match b.val with\n");
    for (bi, b) in init_branches.iter().enumerate() {
        writeln!(out, "  | {bi} => {}", b.guard).unwrap();
    }
    out.push_str("  | _ => Form.truth false\n");

    out.push_str("def initSeed (b : Fin BranchCount) (t : Fin TemplateCount) : SymSeed GroupCount CoreVar :=\n  match b.val, t.val with\n");
    for (bi, b) in init_branches.iter().enumerate() {
        for (ti, seed) in b.seeds.iter().enumerate() {
            writeln!(out, "  | {bi}, {ti} => {seed}").unwrap();
        }
    }
    out.push_str("  | _, _ => SymSeed.const 0\n");

    out.push_str("def stepValid (b : Fin BranchCount) : Bool :=\n  match b.val with\n");
    for bi in 0..step_branches.len() {
        writeln!(out, "  | {bi} => true").unwrap();
    }
    out.push_str("  | _ => false\n");

    out.push_str("def stepBounds (b : Fin BranchCount) : List (SetPred GroupCount CoreVar) :=\n  match b.val with\n");
    for (bi, b) in step_branches.iter().enumerate() {
        writeln!(out, "  | {bi} => [{}]", b.bounds.join(", ")).unwrap();
    }
    out.push_str("  | _ => []\n");

    out.push_str("def stepGuard (b : Fin BranchCount) : SymTest GroupCount cap CoreVar :=\n  match b.val with\n");
    for (bi, b) in step_branches.iter().enumerate() {
        writeln!(out, "  | {bi} => {}", b.guard).unwrap();
    }
    out.push_str("  | _ => SymTest.pure (Form.truth false)\n");

    out.push_str("def stepTransfer (b : Fin BranchCount) (t : Fin TemplateCount) : SymTransfer GroupCount cap CoreVar :=\n  match b.val, t.val with\n");
    for (bi, b) in step_branches.iter().enumerate() {
        for (ti, tr) in b.transfers.iter().enumerate() {
            writeln!(out, "  | {bi}, {ti} => {tr}").unwrap();
        }
    }
    out.push_str("  | _, _ => SymTransfer.keep\n");
}
