//! Connect age transfers to the same branch's history transfer and observations.
use std::fmt::Write;

use super::super::{binding, Branch};
use super::{fold, Emitter};
use crate::optimize::lean::literal;

pub(super) struct Code {
    predicates: Vec<String>,
    seeds: Vec<String>,
    transfers: Vec<String>,
}

impl Emitter<'_, '_> {
    pub(super) fn history_code(&mut self, initial: &[Branch], steps: &[Branch]) -> Option<Option<Code>> {
        let Some(history) = &self.history else { return Some(None) };
        let var = history.var;
        let predicates = history.predicates()?;
        let mut transfers = |branches: &[Branch], primed| {
            branches
                .iter()
                .map(|b| {
                    let rhs = binding(b, var, primed)?;
                    // Event values and transfer conditions cannot inspect time or
                    // uncapped ages. History reads must lower to proved summary predicates.
                    if !self.age_independent(&rhs) {
                        return None;
                    }
                    self.history.as_mut()?.transfer(&rhs, primed)
                })
                .collect::<Option<Vec<_>>>()
        };
        let seeds = transfers(initial, false)?;
        let transfers = transfers(steps, true)?;
        Some(Some(Code { predicates, seeds, transfers }))
    }

    pub(super) fn emit_history(&self, out: &mut String, params: &str, code: Code, observations: Vec<String>) {
        let count = code.predicates.len();
        for (i, atom) in self.history.as_ref().unwrap().atoms.iter().enumerate() {
            writeln!(out, "def historyAtom{i}HIR : String := {}", literal(atom)).unwrap();
        }
        writeln!(out, "def historyPredicate {params} (i : Fin {count}) (event : V) (seen : V → Prop) : Prop :=\n  let sem := sem.history\n  match i.val with").unwrap();
        for (i, p) in code.predicates.iter().enumerate() {
            writeln!(out, "  | {i} => {p}").unwrap();
        }
        out.push_str("  | _ => True\n");
        writeln!(out, "def historySeed {params} (c : C) (choice : Nat × W) : History V :=\n  let p := seed choice\n  let c := (c, p)\n  let d := c\n  let sem := sem.history\n  match choice.1 with").unwrap();
        for (i, seed) in code.seeds.iter().enumerate() {
            writeln!(out, "  | {i} => ({seed}).concrete History.empty").unwrap();
        }
        out.push_str("  | _ => History.empty\n");
        writeln!(out, "def historyTransfer {params} (c d : C) (choice : Nat × W) (p : Key → Bool) (s : Summary V (Fin {count})) : Transfer V :=\n  let c := (c, p)\n  let d := (d, p)\n  let sem := sem.history\n  match choice.1 with").unwrap();
        for (i, transfer) in code.transfers.iter().enumerate() {
            writeln!(out, "  | {i} => {transfer}").unwrap();
        }
        out.push_str("  | _ => Transfer.keep\n");
        writeln!(
            out,
            "def observe {params} (c : C) (p : Key → Bool) (s : Summary V (Fin {count})) : Test caps := {}",
            fold(observations, "conj", "True")
        )
        .unwrap();
        out.push_str("def ageModel : AgeRule.Model C Key (Nat × W) where\n  caps := caps\n  initial := initial sem\n  seed := fun _ w => seed w\n  delta := delta\n  guard := fun _ _ _ _ => Test.pure True\n  change := change sem\n  observe := fun _ _ => Test.pure True\n");
        writeln!(out, "def model : AgeHistoryRule.Model C Key V (Fin {count}) (Nat × W) where\n  age := ageModel sem\n  predicate := historyPredicate sem\n  historySeed := historySeed sem\n  historyTransfer := historyTransfer sem\n  guard := guard sem\n  observe := observe sem").unwrap();
        out.push_str(
            &include_str!("../certificate.lean")
                .replace("State C Key", "(State C Key × History V)")
                .replace("TlxOptimization.GeneratedAge", "TlxOptimization.GeneratedAgeHistory"),
        );
    }
}
