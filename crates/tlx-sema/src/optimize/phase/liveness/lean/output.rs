//! Emit finite liveness obligations and the same branch's concrete transfers.
use super::{conjunction, Case, Emitter, Seed};
use crate::optimize::lean::literal;
use std::fmt::Write;

impl Emitter<'_, '_> {
    pub(super) fn output(&self, seeds: Vec<Seed>, cases: Vec<Case>, observed: Vec<bool>, observations: Vec<String>) -> String {
        let keys = self.a.keys.map_or(1, |keys| keys.len());
        let mut out = String::from(include_str!("../../../FieldCertificate.lean"));
        out.push_str("\nnamespace TlxOptimization.GeneratedField\nopen TlxOptimization FieldRule\nnoncomputable section\nset_option linter.unusedVariables false\nset_option maxRecDepth 10000\nset_option maxHeartbeats 0\nattribute [local instance] Classical.propDecidable\n");
        writeln!(
            out,
            "abbrev Key := Fin {keys}\nabbrev Phase := Fin {}\nabbrev Field := Fin {}\nabbrev BranchId := Fin {}",
            self.phases.len(),
            self.fields.len(),
            cases.len().max(seeds.len())
        )
        .unwrap();
        writeln!(
            out,
            "def layout : String := {}",
            literal(&format!(
                "var {:?}, control {:?}, keys {:?}, phases {:?}, data fields {:?}; missing = FALSE",
                self.a.var, self.a.control, self.a.keys, self.phases, self.fields
            ))
        )
        .unwrap();
        for (i, atom) in self.atoms.iter().enumerate() {
            writeln!(out, "def atom{i}HIR : String := {}", literal(atom)).unwrap();
        }
        for (i, case) in cases.iter().enumerate() {
            writeln!(
                out,
                "def branch{i}HIR : String := {}",
                literal(&format!("source branch {}, actor binding {:?}", case.branch, case.actor))
            )
            .unwrap();
        }
        self.tables(&mut out, &cases, &observed);
        out.push_str("-- C excludes the projected record/map; inputs contain only recorded field reads.\n-- Source lowering, domains, totality, leaf interpretation and runtime remain trusted.\nstructure Semantics (C V W : Type) where\n  missing : V\n  initial : Nat → C → W → Prop\n  seedValue : Nat → C → W → Key → V\n  actor : Nat → W → Key\n  test : Nat → C → C → W → (Key → Phase) → (Key → Field → V) → Prop\n  value : Nat → C → C → W → (Key → Phase) → (Key → Field → V) → V\n  observe : Nat → C → (Key → Phase) → (Key → Field → V) → Prop\n");
        let params = "{C V W : Type} (sem : Semantics C V W)";
        writeln!(out, "variable {params}").unwrap();
        self.seeds(&mut out, params, &seeds);
        self.steps(&mut out, params, &cases);
        writeln!(out, "def observe {params} (c : C) (p : Key → Phase) (input : Key → Field → V) : Prop := {}", conjunction(&observations))
            .unwrap();
        out.push_str("def model : FieldRule.Model C Key Phase Field V BranchId W where\n  missing := sem.missing\n  live := live\n  source := source\n  target := target\n  readsActor := readsActor\n  readsGlobal := readsGlobal\n  writes := writes\n  observed := observed\n  actorLive := by decide\n  globalLive := by decide\n  frameLive := by decide\n  observedLive := by decide\n  actor := fun b w => actor sem (b, w)\n  initial := fun c b w => initial sem c (b, w)\n  seedPhase := fun _ b _ _ => seedPhase b\n  seedValue := fun c b w k f => seedValue sem c (b, w) k f\n  guard := fun b c d w p input => guard sem c d (b, w) p input\n  value := fun b c d w p input f => value sem c d (b, w) p input f\n  observe := observe sem\n");
        out.push_str(include_str!("certificate.lean"));
        out
    }

    fn tables(&self, out: &mut String, cases: &[Case], observed: &[bool]) {
        out.push_str("def live (p : Phase) (f : Field) : Bool :=\n  match p.val with\n");
        for (i, p) in self.phases.iter().enumerate() {
            writeln!(out, "  | {i} => match f.val with").unwrap();
            for (j, f) in self.fields.iter().enumerate() {
                writeln!(out, "    | {j} => {}", self.a.live[f].contains(p)).unwrap();
            }
            out.push_str("    | _ => false\n");
        }
        out.push_str("  | _ => false\n");
        for name in ["source", "target"] {
            writeln!(out, "def {name} (b : BranchId) : Phase :=\n  match b.val with").unwrap();
            for (i, c) in cases.iter().enumerate() {
                writeln!(out, "  | {i} => ⟨{}, by decide⟩", if name == "source" { c.source } else { c.target }).unwrap();
            }
            out.push_str("  | _ => ⟨0, by decide⟩\n");
        }
        for name in ["readsActor", "readsGlobal", "writes"] {
            writeln!(out, "def {name} (b : BranchId) (f : Field) : Bool :=\n  match b.val with").unwrap();
            for (i, c) in cases.iter().enumerate() {
                writeln!(out, "  | {i} => match f.val with").unwrap();
                for f in 0..self.fields.len() {
                    let value = match name {
                        "readsActor" => c.reads.actor[f],
                        "readsGlobal" => c.reads.global[f],
                        _ => c.values[f].is_some(),
                    };
                    writeln!(out, "    | {f} => {value}").unwrap();
                }
                out.push_str("    | _ => false\n");
            }
            out.push_str("  | _ => false\n");
        }
        out.push_str("def observed (f : Field) : Bool :=\n  match f.val with\n");
        for (i, v) in observed.iter().enumerate() {
            writeln!(out, "  | {i} => {v}").unwrap();
        }
        out.push_str("  | _ => false\n");
    }

    fn seeds(&self, out: &mut String, params: &str, seeds: &[Seed]) {
        writeln!(out, "def initial {params} (c : C) (choice : BranchId × W) : Prop :=\n  match choice.1.val with").unwrap();
        for (i, s) in seeds.iter().enumerate() {
            writeln!(out, "  | {i} => {}", s.guard).unwrap();
        }
        out.push_str("  | _ => False\n");
        out.push_str("def seedPhase (b : BranchId) : Phase :=\n  match b.val with\n");
        for (i, s) in seeds.iter().enumerate() {
            writeln!(out, "  | {i} => ⟨{}, by decide⟩", s.phase).unwrap();
        }
        out.push_str("  | _ => ⟨0, by decide⟩\n");
        writeln!(out, "def seedValue {params} (c : C) (choice : BranchId × W) (k : Key) (f : Field) : V :=\n  match choice.1.val with")
            .unwrap();
        for (i, s) in seeds.iter().enumerate() {
            writeln!(out, "  | {i} => match f.val with").unwrap();
            for (j, v) in s.values.iter().enumerate() {
                writeln!(out, "    | {j} => {v}").unwrap();
            }
            out.push_str("    | _ => sem.missing\n");
        }
        out.push_str("  | _ => sem.missing\n");
    }

    fn steps(&self, out: &mut String, params: &str, cases: &[Case]) {
        writeln!(out, "def actor {params} (choice : BranchId × W) : Key :=\n  match choice.1.val with").unwrap();
        for (i, c) in cases.iter().enumerate() {
            writeln!(
                out,
                "  | {i} => {}",
                if c.actor.is_some() { format!("sem.actor {} choice.2", c.branch) } else { "⟨0, by decide⟩".into() }
            )
            .unwrap();
        }
        out.push_str("  | _ => ⟨0, by decide⟩\n");
        let args = "(c d : C) (choice : BranchId × W) (p : Key → Phase) (input : Key → Field → V)";
        writeln!(out, "def guard {params} {args} : Prop :=\n  match choice.1.val with").unwrap();
        for (i, c) in cases.iter().enumerate() {
            writeln!(out, "  | {i} => {}", c.guard).unwrap();
        }
        out.push_str("  | _ => False\n");
        writeln!(out, "def value {params} {args} (f : Field) : V :=\n  match choice.1.val with").unwrap();
        for (i, c) in cases.iter().enumerate() {
            writeln!(out, "  | {i} => match f.val with").unwrap();
            for (j, v) in c.values.iter().enumerate() {
                if let Some(v) = v {
                    writeln!(out, "    | {j} => {v}").unwrap();
                }
            }
            out.push_str("    | _ => sem.missing\n");
        }
        out.push_str("  | _ => sem.missing\n");
    }
}
