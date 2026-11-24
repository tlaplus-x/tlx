//! Instantiate the proved keyed-state IR with this model's exact operations.
use super::super::ObsBundle;
use super::{Case, Emitter};
use crate::{hir::Expr, optimize::lean::literal};
use std::fmt::Write;

impl Emitter<'_> {
    pub(super) fn output(&self, initial: &Expr, cases: &[Case], obs: &ObsBundle<'_>) -> super::super::OpenCert {
        let mut out = String::from(include_str!("../../KeyedCertificate.lean"));
        let namespace = if self.omitted.is_empty() {
            "GeneratedSymmetry"
        } else {
            out.push_str(include_str!("../../ErasedKeyedCertificate.lean"));
            "GeneratedErasedSymmetry"
        };
        writeln!(out, "\nnamespace TlxOptimization.{namespace}").unwrap();
        out.push_str("open TlxOptimization KeyedRule\nnoncomputable section\nset_option linter.unusedVariables false\nset_option maxRecDepth 10000\n");
        writeln!(out, "abbrev GroupCount : Nat := {}", self.groups.len()).unwrap();
        out.push_str("def groupSizes (g : Fin GroupCount) : Nat :=\n  match g.val with\n");
        for (i, g) in self.groups.iter().enumerate() {
            writeln!(out, "  | {i} => {}", g.size).unwrap();
        }
        out.push_str("  | _ => 0\n");
        writeln!(
            out,
            "abbrev MapId := Fin {}\nabbrev SlotId := Fin {}\nabbrev BranchId := Fin {}",
            self.num_maps,
            self.num_slots,
            cases.len()
        )
        .unwrap();
        writeln!(
            out,
            "def layout : String := {}",
            literal(&format!(
                "Disjoint product of {} full permutation group(s) {:?}; shapes {:?}; maps {}; slots {}; payloads and core contain no moved keys",
                self.groups.len(),
                self.groups.iter().map(|g| &g.keys).collect::<Vec<_>>(),
                self.shapes,
                self.num_maps,
                self.num_slots
            ))
        )
        .unwrap();
        writeln!(
            out,
            "def erasedVariables : String := {}",
            literal(&format!("omitted variable indices {:?}; retained variables stay in source order", self.omitted))
        )
        .unwrap();
        writeln!(out, "def initialHIR : String := {}", literal(&format!("{initial:#?}"))).unwrap();
        for (i, atom) in self.atoms.iter().enumerate() {
            writeln!(out, "def atom{i}HIR : String := {}", literal(atom)).unwrap();
        }
        for (i, fa) in self.fixed_atoms.iter().enumerate() {
            writeln!(out, "def fixedAtom{i} : String := {}", literal(fa)).unwrap();
        }
        for (i, c) in cases.iter().enumerate() {
            writeln!(
                out,
                "def branch{i}Keys : String := {}",
                literal(&format!("environment slots: {:?}; other locals belong to W", c.keys))
            )
            .unwrap();
        }
        out.push_str("-- C, A and W contain no renamed keys; V contains only key-free payloads.\n-- Lowering, inferred domains, leaf interpretation, totality, group closure and\n-- runtime canonicalization remain trusted. Init need not be symmetric.\n");
        if self.omitted.is_empty() {
            out.push_str("structure Semantics (C V A W : Type) where\n  initial : State C MapId SlotId (Key groupSizes) V A → Prop\n  fixedAtom : Nat → A\n  test : Nat → C → C → W → List V → List (Option V) → List (Option A) → List Nat → Prop\n  value : Nat → C → C → W → List V → List (Option V) → List (Option A) → List Nat → V\n  fixedVal : Nat → C → C → W → List V → List (Option V) → List (Option A) → List Nat → A\n  observe : Nat → C → List V → List (Option V) → List (Option A) → List Nat → Prop\n");
            if obs.constrained {
                out.push_str("  actionObserve : Nat → C → C → List V → List (Option V) → List (Option A) → List Nat → Prop\n");
            }
        } else {
            self.erasure_semantics(&mut out, obs.constrained);
        }
        out.push_str("def guard (b : BranchId) : Test GroupCount MapId SlotId :=\n  match b.val with\n");
        for (i, c) in cases.iter().enumerate() {
            writeln!(out, "  | {i} => {}", c.guard).unwrap();
        }
        out.push_str("  | _ => Test.truth false\n");
        out.push_str("def writes (b : BranchId) : List (Write GroupCount MapId SlotId) :=\n  match b.val with\n");
        for (i, c) in cases.iter().enumerate() {
            writeln!(out, "  | {i} => [{}]", c.writes.join(", ")).unwrap();
        }
        out.push_str("  | _ => []\n");
        out.push_str("def slotWrites (b : BranchId) : List (SlotWrite GroupCount MapId SlotId) :=\n  match b.val with\n");
        for (i, c) in cases.iter().enumerate() {
            writeln!(out, "  | {i} => [{}]", c.slot_writes.join(", ")).unwrap();
        }
        out.push_str("  | _ => []\n");
        writeln!(out, "def observation : Test GroupCount MapId SlotId := {}", obs.observation).unwrap();
        if obs.constrained {
            writeln!(out, "def initObservation : Test GroupCount MapId SlotId := {}", obs.init_observation).unwrap();
            writeln!(out, "def constraintTest : Test GroupCount MapId SlotId := {}", obs.constraint_test).unwrap();
            writeln!(out, "def actionConstraintTest : ActionTest GroupCount MapId SlotId := {}", obs.action_constraint_test).unwrap();
            writeln!(out, "def actionObservation : ActionTest GroupCount MapId SlotId := {}", obs.action_observation).unwrap();
        }
        if !self.omitted.is_empty() {
            return self.erasure_model(out, cases, obs.constrained);
        }
        out.push_str("variable {C V A W : Type} (sem : Semantics C V A W)\ndef model : KeyedRule.Model GroupCount groupSizes C MapId SlotId V A BranchId W where\n  initial := sem.initial\n  fixedAtom := sem.fixedAtom\n  guard := guard\n  test := fun _ c d w id inputs sinputs finputs nats => sem.test id c d w inputs sinputs finputs nats\n  writes := writes\n  value := fun _ c d w id inputs sinputs finputs nats => sem.value id c d w inputs sinputs finputs nats\n  slotWrites := slotWrites\n  fixedVal := fun _ c d w id inputs sinputs finputs nats => sem.fixedVal id c d w inputs sinputs finputs nats\n  observation := observation\n  observe := fun c id inputs sinputs finputs nats => sem.observe id c inputs sinputs finputs nats\n");
        if obs.constrained {
            out.push_str("  initObservation := initObservation\n  constraintTest := constraintTest\n  actionConstraintTest := actionConstraintTest\n  actionObservation := actionObservation\n  actionObserve := fun c d id inputs sinputs finputs nats => sem.actionObserve id c d inputs sinputs finputs nats\n");
        }
        super::super::OpenCert::new(out, include_str!("certificate.lean"), "GeneratedSymmetry", obs.constrained, false, false)
    }
}
