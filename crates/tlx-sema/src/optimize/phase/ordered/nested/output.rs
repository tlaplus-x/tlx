//! Emit closed finite layouts and the actual transfer selected for each branch.
use super::{Case, Emitter, Seed};
use crate::optimize::lean::literal;
use std::fmt::Write;

impl Emitter<'_, '_> {
    pub(super) fn output(&self, seeds: &[Seed], cases: &[Case], observation: &str) -> String {
        let mut out = String::from(include_str!("../../../NestedRank.lean"));
        out.push_str(include_str!("../../../NestedCertificate.lean"));
        out.push_str("\nnamespace TlxOptimization.GeneratedNested\nopen TlxOptimization NestedRule\nnoncomputable section\nset_option linter.unusedVariables false\nset_option maxRecDepth 10000\nset_option maxHeartbeats 0\n");
        writeln!(out, "abbrev Family := Fin {}\nabbrev BranchId := Fin {}", self.families.len(), seeds.len().max(cases.len())).unwrap();
        for name in ["slotCount", "anchorCount"] {
            writeln!(out, "def {name} (f : Family) : Nat :=\n  match f.val with").unwrap();
            for f in 0..self.families.len() {
                let count = if name == "slotCount" { self.slots.iter().filter(|s| s.family == f).count() } else { self.anchors[f].len() };
                writeln!(out, "  | {f} => {count}").unwrap();
            }
            out.push_str("  | _ => 0\n");
        }
        out.push_str("abbrev Slot (f : Family) := Fin (slotCount f)\nabbrev Anchor (f : Family) := Fin (anchorCount f)\n");
        writeln!(
            out,
            "def sourceLayout : String := {}",
            literal(&format!(
                "numeric paths {:?}; retained paths {:?}; configured atom holes {:?}; core targets {:?}; runtime plan {:?}",
                self.slots, self.plain, self.context.aliases, self.targets, self.plan
            ))
        )
        .unwrap();
        for (i, atom) in self.atoms.iter().enumerate() {
            writeln!(out, "def atom{i}HIR : String := {}", literal(atom)).unwrap();
        }
        self.layout(&mut out);
        out.push_str("-- C is exactly the retained leaf values; W is independent branch choices.\n-- Source lowering, fixed shapes, domains, totality and runtime remain trusted.\nstructure Semantics (C W : Type) where\n  initial : Nat → C → W → Prop\n  test : Nat → C → C → W → Prop\n  observe : Nat → C → Prop\nvariable {C W : Type} (sem : Semantics C W)\n");
        self.seeds(&mut out, seeds);
        self.cases(&mut out, cases);
        writeln!(out, "def observe {{C W : Type}} (sem : Semantics C W) (c : C) : FamilyTest Family Slot Anchor := {observation}").unwrap();
        out.push_str("def model : NestedRule.Model C Family (BranchId × W) Slot Anchor where\n  layout := layout\n  initial := initial sem\n  seedValues := seedValues\n  delta := delta\n  transfers := transfers sem\n  guard := guard sem\n  observe := observe sem\n");
        out.push_str(include_str!("certificate.lean"));
        out
    }
    fn layout(&self, out: &mut String) {
        out.push_str("def layout (f : Family) : Layout (Anchor f) :=\n  match f with\n");
        for (f, family) in self.families.iter().enumerate() {
            writeln!(
                out,
                "  | ⟨{f}, _⟩ => {{ seed := {}, positive := by decide +revert, anchors := fun a => match a.val with",
                family.initial
            )
            .unwrap();
            for (i, n) in self.anchors[f].iter().enumerate() {
                writeln!(out, "      | {i} => ⟨({n}), by decide +revert⟩").unwrap();
            }
            out.push_str("      | _ => ⟨0, by decide +revert⟩ }\n");
        }
        out.push_str("  | _ => { seed := 1, positive := by decide +revert, anchors := fun _ => ⟨0, by decide +revert⟩ }\n");
        out.push_str("def references (f : Family) : List (Reference (Slot f) (Anchor f)) :=\n  Reference.frontier :: ((List.finRange (slotCount f)).map Reference.slot ++ (List.finRange (anchorCount f)).map Reference.anchor)\ntheorem references_complete (f : Family) (r : Reference (Slot f) (Anchor f)) : r ∈ references f := by\n  cases r <;> simp [references]\n");
    }
    fn seeds(&self, out: &mut String, seeds: &[Seed]) {
        for (b, s) in seeds.iter().enumerate() {
            writeln!(out, "def seed{b} (f : Family) : Slot f → {{ n : Int // n ≤ ((layout f).seed : Int) }} :=\n  match f with").unwrap();
            for (f, values) in s.values.iter().enumerate() {
                writeln!(out, "  | ⟨{f}, _⟩ => fun i => match i.val with").unwrap();
                for (i, n) in values.iter().enumerate() {
                    writeln!(out, "      | {i} => ⟨({n}), by decide +revert⟩").unwrap();
                }
                out.push_str("      | _ => ⟨0, by decide +revert⟩\n");
            }
            out.push_str("  | _ => fun _ => ⟨0, by omega⟩\n");
        }
        out.push_str("def seedValues {W : Type} (choice : BranchId × W) (f : Family) : Slot f → { n : Int // n ≤ ((layout f).seed : Int) } :=\n  match choice.1.val with\n");
        for b in 0..seeds.len() {
            writeln!(out, "  | {b} => seed{b} f").unwrap();
        }
        out.push_str("  | _ => fun _ => ⟨0, by omega⟩\n");
        out.push_str("def initial {C W : Type} (sem : Semantics C W) (c : C) (choice : BranchId × W) : FamilyTest Family Slot Anchor :=\n  match choice.1.val with\n");
        for (b, s) in seeds.iter().enumerate() {
            writeln!(out, "  | {b} => {}", s.guard).unwrap();
        }
        out.push_str("  | _ => FamilyTest.pure False\n");
    }
    fn cases(&self, out: &mut String, cases: &[Case]) {
        for (b, c) in cases.iter().enumerate() {
            writeln!(out, "def delta{b} (f : Family) : Nat :=\n  match f.val with").unwrap();
            for (f, delta) in c.deltas.iter().enumerate() {
                writeln!(out, "  | {f} => {delta}").unwrap();
            }
            out.push_str("  | _ => 0\n");
            writeln!(out,"def transfer{b} {{C W : Type}} (sem : Semantics C W) (c d : C) (choice : BranchId × W) (f : Family) : Slot f → Transfer (Slot f) (Anchor f) (delta{b} f) :=\n  match f with").unwrap();
            for (f, values) in c.values.iter().enumerate() {
                writeln!(out, "  | ⟨{f}, _⟩ => fun i => match i.val with").unwrap();
                for (i, value) in values.iter().enumerate() {
                    writeln!(out, "      | {i} => {value}").unwrap();
                }
                out.push_str("      | _ => Transfer.value (Token.old Reference.frontier)\n");
            }
            out.push_str("  | _ => fun _ => Transfer.value (Token.old Reference.frontier)\n");
        }
        out.push_str("def delta {W : Type} (choice : BranchId × W) (f : Family) : Nat :=\n  match choice.1.val with\n");
        for b in 0..cases.len() {
            writeln!(out, "  | {b} => delta{b} f").unwrap();
        }
        out.push_str("  | _ => 0\n");
        out.push_str("def transfers {C W : Type} (sem : Semantics C W) (c d : C) (choice : BranchId × W) (f : Family) : Slot f → Transfer (Slot f) (Anchor f) (delta choice f) :=\n  match choice with\n");
        for b in 0..cases.len() {
            writeln!(out, "  | (⟨{b}, h⟩, w) => transfer{b} sem c d (⟨{b}, h⟩, w) f").unwrap();
        }
        out.push_str("  | _ => fun _ => Transfer.value (Token.old Reference.frontier)\n");
        out.push_str("def guard {C W : Type} (sem : Semantics C W) (c d : C) (choice : BranchId × W) : FamilyTest Family Slot Anchor :=\n  match choice.1.val with\n");
        for (b, c) in cases.iter().enumerate() {
            writeln!(out, "  | {b} => {}", c.guard).unwrap();
        }
        out.push_str("  | _ => FamilyTest.pure False\n");
    }
}
