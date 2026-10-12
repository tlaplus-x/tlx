//! Connect age transfers to the same branch's history transfer and observations.
use std::fmt::Write;

use super::super::{binding, Branch};
use super::{fold, Emitter};
use crate::{builtins::Builtin as B, hir::*, optimize::lean::literal};

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
        let seeds = initial
            .iter()
            .map(|b| {
                let rhs = binding(b, var, false)?;
                if !self.age_independent(&rhs) {
                    return None;
                }
                self.history.as_mut()?.transfer(&rhs, false)
            })
            .collect::<Option<Vec<_>>>()?;
        let transfers = steps.iter().map(|b| self.history_transfer(&binding(b, var, true)?)).collect::<Option<Vec<_>>>()?;
        Some(Some(Code { predicates, seeds, transfers }))
    }

    fn history_value(&mut self, e: &Expr) -> Option<String> {
        if let Some((test, then, els)) = self.split_decision(e) {
            let yes = self.history_value(&then)?;
            let no = self.history_value(&els)?;
            self.remaining = self.remaining.checked_sub(test.len() + yes.len() + no.len())?;
            return Some(format!("(Decision.branch {test} {yes} {no})"));
        }
        if let ExprKind::If { cond, then, els } = &*e.kind {
            return Some(format!(
                "(Decision.branch {} {} {})",
                self.test(cond, false)?,
                self.history_value(then)?,
                self.history_value(els)?
            ));
        }
        if !self.age_independent(e) {
            return None;
        }
        let value = self.history.as_mut()?.value(e, true)?;
        Some(format!("(Decision.pure (let sem := sem.history; let c := (c, p); let d := (d, p); {value}))"))
    }

    fn history_transfer(&mut self, e: &Expr) -> Option<String> {
        Some(match &*e.kind {
            ExprKind::Var(v) if *v == self.history.as_ref()?.var => "(Decision.pure Transfer.keep)".into(),
            ExprKind::Tuple(es) => {
                let mut h = "(Decision.pure History.empty)".to_owned();
                for e in es {
                    h = format!("(Decision.bindValue {h} (fun previous => Decision.bindValue {} (fun event => Decision.pure (History.append previous event))))", self.history_value(e)?);
                }
                format!("(Decision.bindValue {h} (fun h => Decision.pure (Transfer.reset h)))")
            }
            ExprKind::Builtin { op: B::Append, args } if args.len() == 2 => {
                let t = self.history_transfer(&args[0])?;
                let value = self.history_value(&args[1])?;
                format!("(Decision.bindValue {t} (fun previous => Decision.bindValue {value} (fun event => Decision.pure (Transfer.append previous event))))")
            }
            ExprKind::If { cond, then, els } => {
                format!("(Decision.branch {} {} {})", self.test(cond, false)?, self.history_transfer(then)?, self.history_transfer(els)?)
            }
            _ => return None,
        })
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
        writeln!(out, "def historyTransfer {params} (c d : C) (choice : Nat × W) (p : Key → Bool) (s : Summary V (Fin {count})) : Decision caps (Transfer V) :=\n  match choice.1 with").unwrap();
        for (i, transfer) in code.transfers.iter().enumerate() {
            writeln!(out, "  | {i} => {transfer}").unwrap();
        }
        out.push_str("  | _ => Decision.pure Transfer.keep\n");
        writeln!(
            out,
            "def observe {params} (c : C) (p : Key → Bool) (s : Summary V (Fin {count})) : Test caps := {}",
            fold(observations, "conj", "True")
        )
        .unwrap();
        out.push_str("def ageModel : AgeRule.Model C Key (Nat × W) where\n  caps := caps\n  initial := initial sem\n  seed := fun _ w => seed w\n  delta := delta\n  guard := fun _ _ _ _ => Test.pure True\n  change := fun _ _ _ _ _ => Decision.pure Change.keep\n  observe := fun _ _ => Test.pure True\n");
        writeln!(out, "def model : AgeHistoryRule.Model C Key V (Fin {count}) (Nat × W) where\n  age := ageModel sem\n  predicate := historyPredicate sem\n  historySeed := historySeed sem\n  historyTransfer := historyTransfer sem\n  change := change sem\n  guard := guard sem\n  observe := observe sem").unwrap();
        out.push_str(
            &include_str!("../certificate.lean")
                .replace("State C Key", "(State C Key × History V)")
                .replace("TlxOptimization.GeneratedAge", "TlxOptimization.GeneratedAgeHistory"),
        );
    }
}
