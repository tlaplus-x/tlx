//! Erasure transfers share the keyed branch; semantic leaves cannot read them.
use super::{binding, Case, Emitter};
use crate::{hir::*, optimize::lean::literal};
use std::fmt::Write;

impl Emitter<'_> {
    pub(super) fn hidden_updates(&mut self, b: &super::Branch) -> Option<Vec<String>> {
        self.omitted.clone().iter().map(|v| self.hidden_value(&binding(b, *v, true)?)).collect()
    }

    fn hidden_value(&mut self, e: &Expr) -> Option<String> {
        Some(match &*e.kind {
            ExprKind::Num(n) if i32::try_from(*n).is_ok() => format!("sem.number ({n})"),
            ExprKind::Str(s) => format!("sem.string {}", literal(s)),
            ExprKind::Bool(b) => format!("sem.boolean {b}"),
            ExprKind::Var(v) => {
                if let Some(i) = self.omitted.iter().position(|x| x == v) {
                    format!("h ⟨{i}, by decide⟩")
                } else {
                    let id = self.atoms.len();
                    self.atoms.push(format!("Hidden old retained-variable copy HIR: {e:#?}"));
                    format!("sem.hiddenValue {id} s")
                }
            }
            _ => return None,
        })
    }

    pub(super) fn erasure_semantics(&self, out: &mut String) {
        writeln!(out, "abbrev Hidden (H : Type) := Fin {} → H", self.omitted.len()).unwrap();
        out.push_str("structure Semantics (C V A W H : Type) where\n  initial : (State C MapId SlotId (Key groupSizes) V A × Hidden H) → Prop\n  fixedAtom : Nat → A\n  test : Nat → C → C → W → List V → List (Option V) → List (Option A) → List Nat → Prop\n  value : Nat → C → C → W → List V → List (Option V) → List (Option A) → List Nat → V\n  fixedVal : Nat → C → C → W → List V → List (Option V) → List (Option A) → List Nat → A\n  observe : Nat → C → List V → List (Option V) → List (Option A) → List Nat → Prop\n  number : Int → H\n  string : String → H\n  boolean : Bool → H\n  hiddenValue : Nat → State C MapId SlotId (Key groupSizes) V A → H\n");
    }

    pub(super) fn erasure_model(&self, out: &mut String, cases: &[Case]) {
        out.push_str("variable {C V A W H : Type} (sem : Semantics C V A W H)\ndef hiddenUpdate {C V A W H : Type} (sem : Semantics C V A W H) (b : BranchId) (s : State C MapId SlotId (Key groupSizes) V A) (_w : W) (_keys : Environment (Key groupSizes)) (h : Hidden H) : Hidden H :=\n  match b.val with\n");
        for (b, c) in cases.iter().enumerate() {
            writeln!(out, "  | {b} => fun i => match i.val with").unwrap();
            for (i, v) in c.hidden.iter().enumerate() {
                writeln!(out, "      | {i} => {v}").unwrap();
            }
            out.push_str("      | _ => sem.boolean false\n");
        }
        out.push_str("  | _ => fun _ => sem.boolean false\ndef model : ErasedKeyedRule.Model GroupCount groupSizes C MapId SlotId V A BranchId W (Hidden H) where\n  initial := sem.initial\n  fixedAtom := sem.fixedAtom\n  hiddenUpdate := hiddenUpdate sem\n  guard := guard\n  test := fun _ c d w id inputs sinputs finputs nats => sem.test id c d w inputs sinputs finputs nats\n  writes := writes\n  value := fun _ c d w id inputs sinputs finputs nats => sem.value id c d w inputs sinputs finputs nats\n  slotWrites := slotWrites\n  fixedVal := fun _ c d w id inputs sinputs finputs nats => sem.fixedVal id c d w inputs sinputs finputs nats\n  observation := observation\n  observe := fun c id inputs sinputs finputs nats => sem.observe id c inputs sinputs finputs nats\n");
        out.push_str(include_str!("erasure.lean"));
    }
}
