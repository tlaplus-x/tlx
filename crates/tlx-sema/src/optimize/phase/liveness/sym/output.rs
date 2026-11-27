//! Render a standalone `GeneratedFieldSymmetry` Lean certificate instantiating
//! `FieldSymCertificate.lean` (over `FieldCertificate.lean`,
//! `EquivSymCertificate.lean`, and `OrbitQuotient.lean`).

use std::fmt::Write;

use crate::{hir::Expr, optimize::lean::literal, Program};

use super::super::super::{
    domain::Atom,
    equiv_sym::{lower::LowerCtx, output::write_common_header, GroupInfo, GroupMask},
    OpenCert,
};
use super::super::{Analysis, Slot};
use super::{SeedData, StepCase};

pub(super) struct RenderSpec<'a> {
    pub(super) program: &'a Program,
    pub(super) groups: &'a [GroupInfo],
    pub(super) ctx: &'a LowerCtx<'a>,
    pub(super) orig_init: &'a Expr,
    pub(super) analysis: &'a Analysis<'a>,
    pub(super) fields: &'a [Slot],
    pub(super) phases: &'a [Atom],
    pub(super) phase_atom_ids: &'a [usize],
    pub(super) fixed_atom_ids: &'a [usize],
    pub(super) key_mask: GroupMask,
    pub(super) default_key_lean: &'a str,
    pub(super) is_keyed: bool,
    pub(super) core_count: usize,
    pub(super) var_roles: &'a [String],
    pub(super) rec_field_atoms: &'a [usize],
    pub(super) sentinel_exprs: &'a [String],
    pub(super) branch_count: usize,
    pub(super) seeds: &'a [SeedData],
    pub(super) cases: &'a [StepCase],
    pub(super) observed: &'a [Vec<bool>],
    pub(super) obs_form: &'a str,
    pub(super) init_obs_form: &'a str,
    pub(super) constraint_form: &'a str,
    pub(super) action_constraint_form: &'a str,
    pub(super) action_obs_form: &'a str,
    pub(super) fallback_expr: &'a str,
    pub(super) constrained: bool,
}

pub(super) fn render(spec: &RenderSpec<'_>) -> OpenCert {
    let mut out = String::from(include_str!("../../../FieldCertificate.lean"));
    out.push_str(include_str!("../../../EquivSymCertificate.lean"));
    out.push_str(include_str!("../../../OrbitQuotient.lean"));
    out.push_str(include_str!("../../../FieldSymCertificate.lean"));
    out.push_str("\nnamespace TlxOptimization.GeneratedFieldSymmetry\n");
    out.push_str(
        "open TlxOptimization FieldRule EquivRule FieldSymRule\n\
         noncomputable section\n\
         set_option linter.unusedVariables false\n\
         set_option maxRecDepth 20000\n",
    );
    write_common_header(&mut out, spec.groups, spec.program.vars.len(), spec.ctx, spec.orig_init);
    writeln!(out, "abbrev FullVar := VarId").unwrap();
    writeln!(out, "abbrev CoreVar := Fin {}", spec.core_count).unwrap();
    writeln!(out, "abbrev FixedCount : Nat := {}", spec.fixed_atom_ids.len()).unwrap();
    writeln!(out, "abbrev PhaseCount : Nat := {}", spec.phases.len()).unwrap();
    writeln!(out, "abbrev FieldCount : Nat := {}", spec.fields.len()).unwrap();
    writeln!(out, "abbrev BranchCount : Nat := {}", spec.branch_count).unwrap();

    // Key mask and fixed atom IDs.
    let mask_parts: Vec<String> =
        (0..spec.groups.len()).filter(|gi| (spec.key_mask & (1u16 << gi)) != 0).map(|gi| format!("g.val == {gi}")).collect();
    let key_mask_lean = if mask_parts.is_empty() { "fun _ => false".to_string() } else { format!("fun g => {}", mask_parts.join(" || ")) };
    writeln!(out, "def keyMask : GroupMask GroupCount := {key_mask_lean}").unwrap();
    out.push_str("def fixedAtomId (i : Fin FixedCount) : Nat :=\n  match i.val with\n");
    for (i, aid) in spec.fixed_atom_ids.iter().enumerate() {
        writeln!(out, "  | {i} => {aid}").unwrap();
    }
    out.push_str("  | _ => 0\n");
    writeln!(out, "def defaultKey : KeyElem groupSizes FixedCount keyMask := {}", spec.default_key_lean).unwrap();

    out.push_str("def phaseAtom (p : Fin PhaseCount) : Nat :=\n  match p.val with\n");
    for (i, aid) in spec.phase_atom_ids.iter().enumerate() {
        writeln!(out, "  | {i} => {aid}").unwrap();
    }
    out.push_str("  | _ => 0\n");

    out.push_str("def recordFieldAtom (f : Fin FieldCount) : Nat :=\n  match f.val with\n");
    for (i, aid) in spec.rec_field_atoms.iter().enumerate() {
        writeln!(out, "  | {i} => {aid}").unwrap();
    }
    out.push_str("  | _ => 0\n");

    out.push_str("def varRole (v : FullVar) : VarRole CoreVar (Fin FieldCount) :=\n  match v.val, v.isLt with\n");
    for (i, role) in spec.var_roles.iter().enumerate() {
        writeln!(out, "  | {i}, _ => {role}").unwrap();
    }
    writeln!(out, "  | _ + {}, h => absurd h (by omega)", spec.var_roles.len()).unwrap();

    out.push_str("def sentinelExpr (f : Fin FieldCount) : EquivRule.Expr GroupCount Empty :=\n  match f.val with\n");
    for (i, se) in spec.sentinel_exprs.iter().enumerate() {
        writeln!(out, "  | {i} => {se}").unwrap();
    }
    writeln!(out, "  | _ => {}", spec.fallback_expr).unwrap();

    // Liveness and branch tables.
    out.push_str("def live (p : Fin PhaseCount) (f : Fin FieldCount) : Bool :=\n  match p.val, f.val with\n");
    for (pi, p) in spec.phases.iter().enumerate() {
        for (fi, slot) in spec.fields.iter().enumerate() {
            if spec.analysis.live[slot].contains(p) {
                writeln!(out, "  | {pi}, {fi} => true").unwrap();
            }
        }
    }
    out.push_str("  | _, _ => false\n");

    out.push_str("def source (b : Fin BranchCount) : Fin PhaseCount :=\n  match b.val with\n");
    for (bi, c) in spec.cases.iter().enumerate() {
        writeln!(out, "  | {bi} => ⟨{}, by decide⟩", c.source).unwrap();
    }
    out.push_str("  | _ => ⟨0, by decide⟩\n");

    out.push_str("def target (b : Fin BranchCount) : Fin PhaseCount :=\n  match b.val with\n");
    for (bi, c) in spec.cases.iter().enumerate() {
        writeln!(out, "  | {bi} => ⟨{}, by decide⟩", c.target).unwrap();
    }
    out.push_str("  | _ => ⟨0, by decide⟩\n");

    out.push_str("def readsActor (b : Fin BranchCount) (f : Fin FieldCount) : Bool :=\n  match b.val, f.val with\n");
    for (bi, c) in spec.cases.iter().enumerate() {
        for (fi, &r) in c.reads.actor.iter().enumerate() {
            if r {
                writeln!(out, "  | {bi}, {fi} => true").unwrap();
            }
        }
    }
    out.push_str("  | _, _ => false\n");

    out.push_str("def readsGlobal (b : Fin BranchCount) (f : Fin FieldCount) : Bool :=\n  match b.val, f.val with\n");
    for (bi, c) in spec.cases.iter().enumerate() {
        for (fi, &r) in c.reads.global.iter().enumerate() {
            if r {
                writeln!(out, "  | {bi}, {fi} => true").unwrap();
            }
        }
    }
    out.push_str("  | _, _ => false\n");

    out.push_str("def writes (b : Fin BranchCount) (f : Fin FieldCount) : Bool :=\n  match b.val, f.val with\n");
    for (bi, c) in spec.cases.iter().enumerate() {
        for (fi, &w) in c.writes.iter().enumerate() {
            if w {
                writeln!(out, "  | {bi}, {fi} => true").unwrap();
            }
        }
    }
    out.push_str("  | _, _ => false\n");

    out.push_str("def observed (p : Fin PhaseCount) (f : Fin FieldCount) : Bool :=\n  match p.val, f.val with\n");
    for (pi, row) in spec.observed.iter().enumerate() {
        for (fi, &o) in row.iter().enumerate() {
            if o {
                writeln!(out, "  | {pi}, {fi} => true").unwrap();
            }
        }
    }
    out.push_str("  | _, _ => false\n");

    // Seed tables.
    out.push_str("def seedValid (b : Fin BranchCount) : Bool :=\n  match b.val with\n");
    for bi in 0..spec.seeds.len() {
        writeln!(out, "  | {bi} => true").unwrap();
    }
    out.push_str("  | _ => false\n");

    out.push_str("def seedBounds (b : Fin BranchCount) : List (SetPred GroupCount FullVar) :=\n  match b.val with\n");
    for (bi, s) in spec.seeds.iter().enumerate() {
        writeln!(out, "  | {bi} => [{}]", s.bounds.join(", ")).unwrap();
    }
    out.push_str("  | _ => []\n");

    out.push_str("def seedGuard (b : Fin BranchCount) : Form GroupCount FullVar :=\n  match b.val with\n");
    for (bi, s) in spec.seeds.iter().enumerate() {
        writeln!(out, "  | {bi} => {}", s.guard).unwrap();
    }
    out.push_str("  | _ => Form.truth false\n");

    out.push_str("def seedPhase (b : Fin BranchCount) : Fin PhaseCount :=\n  match b.val with\n");
    for (bi, s) in spec.seeds.iter().enumerate() {
        writeln!(out, "  | {bi} => ⟨{}, by decide⟩", s.phase).unwrap();
    }
    out.push_str("  | _ => ⟨0, by decide⟩\n");

    out.push_str(
        "def seedValueExpr (b : Fin BranchCount) (f : Fin FieldCount) : EquivRule.Expr GroupCount FullVar :=\n  match b.val, f.val with\n",
    );
    for (bi, s) in spec.seeds.iter().enumerate() {
        for (fi, v) in s.values.iter().enumerate() {
            writeln!(out, "  | {bi}, {fi} => {v}").unwrap();
        }
    }
    writeln!(out, "  | _, _ => {}", spec.fallback_expr).unwrap();

    // Step tables.
    out.push_str("def stepValid (b : Fin BranchCount) : Bool :=\n  match b.val with\n");
    for bi in 0..spec.cases.len() {
        writeln!(out, "  | {bi} => true").unwrap();
    }
    out.push_str("  | _ => false\n");

    out.push_str("def stepHasActor (b : Fin BranchCount) : Bool :=\n  match b.val with\n");
    for (bi, c) in spec.cases.iter().enumerate() {
        if c.has_actor {
            writeln!(out, "  | {bi} => true").unwrap();
        }
    }
    out.push_str("  | _ => false\n");

    out.push_str("def stepBounds (b : Fin BranchCount) : List (SetPred GroupCount FullVar) :=\n  match b.val with\n");
    for (bi, c) in spec.cases.iter().enumerate() {
        writeln!(out, "  | {bi} => [{}]", c.bounds.join(", ")).unwrap();
    }
    out.push_str("  | _ => []\n");

    out.push_str("def stepGuard (b : Fin BranchCount) : Form GroupCount FullVar :=\n  match b.val with\n");
    for (bi, c) in spec.cases.iter().enumerate() {
        writeln!(out, "  | {bi} => {}", c.guard).unwrap();
    }
    out.push_str("  | _ => Form.truth false\n");

    out.push_str(
        "def stepValueExpr (b : Fin BranchCount) (f : Fin FieldCount) : EquivRule.Expr GroupCount FullVar :=\n  match b.val, f.val with\n",
    );
    for (bi, c) in spec.cases.iter().enumerate() {
        for (fi, v) in c.values.iter().enumerate() {
            writeln!(out, "  | {bi}, {fi} => {v}").unwrap();
        }
    }
    writeln!(out, "  | _, _ => {}", spec.fallback_expr).unwrap();

    writeln!(out, "def obsForm : Form GroupCount FullVar := {}", spec.obs_form).unwrap();
    if spec.constrained {
        writeln!(out, "def initObsForm : Form GroupCount FullVar := {}", spec.init_obs_form).unwrap();
        writeln!(out, "def constraintForm : Form GroupCount FullVar := {}", spec.constraint_form).unwrap();
        writeln!(out, "def actionConstraintForm : Form GroupCount FullVar := {}", spec.action_constraint_form).unwrap();
        writeln!(out, "def actionObsForm : Form GroupCount FullVar := {}", spec.action_obs_form).unwrap();
    }
    writeln!(
        out,
        "def fieldSummary : String := {}",
        literal(&format!(
            "control={:?}; fields={:?}; phases={:?}; keyed={}",
            spec.analysis.control, spec.fields, spec.phases, spec.is_keyed
        ))
    )
    .unwrap();

    out.push_str(
        "abbrev Semantics (A : Type) := EquivRule.AtomOps A\n\
         variable {A : Type} [HasNatAtom A] (sem : Semantics A)\n\
         def model : FieldSymRule.Model GroupCount groupSizes FixedCount keyMask CoreVar FullVar PhaseCount FieldCount BranchCount A where\n\
         \x20 ops := sem\n\
         \x20 fixedAtom := fun i => sem.atomVal (fixedAtomId i)\n\
         \x20 defaultKey := defaultKey\n\
         \x20 phaseAtom := phaseAtom\n\
         \x20 varRole := varRole\n\
         \x20 sentinelExpr := sentinelExpr\n\
         \x20 live := live\n\
         \x20 source := source\n\
         \x20 target := target\n\
         \x20 readsActor := readsActor\n\
         \x20 readsGlobal := readsGlobal\n\
         \x20 writes := writes\n\
         \x20 observed := observed\n\
         \x20 actorLive := by decide\n\
         \x20 globalLive := by decide\n\
         \x20 frameLive := by decide\n\
         \x20 observedLive := by decide\n\
         \x20 seedValid := seedValid\n\
         \x20 seedBounds := seedBounds\n\
         \x20 seedGuard := seedGuard\n\
         \x20 seedPhase := seedPhase\n\
         \x20 seedValueExpr := seedValueExpr\n\
         \x20 stepValid := stepValid\n\
         \x20 stepHasActor := stepHasActor\n\
         \x20 stepBounds := stepBounds\n\
         \x20 stepGuard := stepGuard\n\
         \x20 stepValueExpr := stepValueExpr\n\
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
    // Prove `defaultKeyFixed` cleanly for both keyed (all `isKeyed = true`) and
    // scalar (`defaultKey = Sum.inl ⟨0, _⟩`, invariant by `rfl`).
    out.push_str("  defaultKeyFixed := by\n    intro p v\n    rcases v with ⟨v, hv⟩\n    match v, hv with\n");
    for (i, role) in spec.var_roles.iter().enumerate() {
        let tactic = if spec.is_keyed || role.starts_with("VarRole.core") { "trivial" } else { "rfl" };
        writeln!(out, "    | {i}, _ => {tactic}").unwrap();
    }
    writeln!(out, "    | _ + {}, h => exact absurd h (by omega)", spec.var_roles.len()).unwrap();

    OpenCert::new_composed(out, include_str!("../sym.lean"), "GeneratedFieldSymmetry", spec.constrained, "field", "fieldProject")
}
