//! Instantiate the proved keyed-state IR with this model's exact operations.
use super::{Case, Emitter};
use crate::{hir::Expr, optimize::lean::literal};
use std::fmt::Write;

impl Emitter<'_> {
    pub(super) fn output(&self, initial: &Expr, cases: &[Case], observation: &str) -> String {
        let mut out = String::from(include_str!("../../KeyedCertificate.lean"));
        let namespace = if self.omitted.is_empty() {
            "GeneratedSymmetry"
        } else {
            out.push_str(include_str!("../../ErasedKeyedCertificate.lean"));
            "GeneratedErasedSymmetry"
        };
        writeln!(out, "\nnamespace TlxOptimization.{namespace}").unwrap();
        out.push_str("open TlxOptimization KeyedRule\nnoncomputable section\nset_option linter.unusedVariables false\nset_option maxRecDepth 10000\n");
        writeln!(
            out,
            "abbrev Key := Fin {}\nabbrev MapId := Fin {}\nabbrev BranchId := Fin {}",
            self.keys.len(),
            self.maps.len(),
            cases.len()
        )
        .unwrap();
        writeln!(
            out,
            "def layout : String := {}",
            literal(&format!("Full permutation group of {:?}; maps {:?}; payloads and core contain no moved keys", self.keys, self.maps))
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
        for (i, c) in cases.iter().enumerate() {
            writeln!(
                out,
                "def branch{i}Keys : String := {}",
                literal(&format!("environment slots: {:?}; other locals belong to W", c.keys))
            )
            .unwrap();
        }
        out.push_str("-- C and W contain no renamed keys; V contains only key-free payloads.\n-- Lowering, inferred domains, leaf interpretation, totality, group closure and\n-- runtime canonicalization remain trusted. Init need not be symmetric.\n");
        if self.omitted.is_empty() {
            out.push_str("structure Semantics (C V W : Type) where\n  initial : State C MapId Key V → Prop\n  test : Nat → C → C → W → List V → Prop\n  value : Nat → C → C → W → List V → V\n  observe : Nat → C → List V → Prop\n");
        } else {
            self.erasure_semantics(&mut out);
        }
        out.push_str("def guard (b : BranchId) : Test MapId :=\n  match b.val with\n");
        for (i, c) in cases.iter().enumerate() {
            writeln!(out, "  | {i} => {}", c.guard).unwrap();
        }
        out.push_str("  | _ => Test.truth false\n");
        out.push_str("def writes (b : BranchId) : List (Write MapId) :=\n  match b.val with\n");
        for (i, c) in cases.iter().enumerate() {
            writeln!(out, "  | {i} => [{}]", c.writes.join(", ")).unwrap();
        }
        out.push_str("  | _ => []\n");
        writeln!(out, "def observation : Test MapId := {observation}").unwrap();
        if !self.omitted.is_empty() {
            self.erasure_model(&mut out, cases);
            return out;
        }
        out.push_str("variable {C V W : Type} (sem : Semantics C V W)\ndef model : KeyedRule.Model C MapId Key V BranchId W where\n  initial := sem.initial\n  guard := guard\n  test := fun _ c d w id inputs => sem.test id c d w inputs\n  writes := writes\n  value := fun _ c d w id inputs => sem.value id c d w inputs\n  observation := observation\n  observe := fun c id inputs => sem.observe id c inputs\n");
        out.push_str(include_str!("certificate.lean"));
        out
    }
}
