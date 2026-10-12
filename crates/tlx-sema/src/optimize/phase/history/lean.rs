//! Lower the history-dependent slice to a parametric Lean rule model.
//! Unchanged, history-free HIR leaves are recorded and universally interpreted;
//! they cannot access the forgotten history. No source-model names are special.

use std::{fmt::Write, sync::Arc};

use super::super::{binding, unchanged, variable, Branch};
use super::{interval_end, one_local};
use crate::{builtins::Builtin as B, hir::*, optimize::lean::literal, visit};

pub(super) fn emit(var: VarId, initial: &[Branch], steps: &[Branch], observations: &[Expr], monitors: &[Expr]) -> Option<String> {
    let mut emitter = Emitter::new(var, monitors);
    let predicates = emitter.predicates()?;
    let (initial_guards, seeds) = emitter.branches(initial, false)?;
    let (step_guards, transfers) = emitter.branches(steps, true)?;
    let observations = observations.iter().map(|e| emitter.observe(e)).collect::<Option<Vec<_>>>()?;
    let count = monitors.len();
    let mut out = String::from(include_str!("../../HistoryCertificate.lean"));
    out.push_str("\nnamespace TlxOptimization.GeneratedHistory\nopen TlxOptimization HistoryRule\nnoncomputable section\nset_option linter.unusedVariables false\nattribute [local instance] Classical.propDecidable\n");
    out.push_str(SEMANTICS);
    for (i, atom) in emitter.atoms.iter().enumerate() {
        writeln!(out, "def atom{i}HIR : String := {}", literal(atom)).unwrap();
    }
    writeln!(out, "\nvariable {{C V W : Type}} (sem : Semantics C V W)").unwrap();
    let params = "{C V W : Type} (sem : Semantics C V W)";
    // Named arguments are intentionally identical to the generated expression
    // context. Core leaves share their witness with the history transfer.
    writeln!(out, "def predicate {params} (i : Fin {count}) (event : V) (seen : V → Prop) : Prop :=\n  match i.val with").unwrap();
    for (i, p) in predicates.iter().enumerate() {
        writeln!(out, "  | {i} => {p}").unwrap();
    }
    out.push_str("  | _ => True\n");
    for (name, args, typ, values, default) in [
        ("initial", "(c : C) (choice : Nat × W)", "Prop", initial_guards, "False"),
        ("seed", "(c : C) (choice : Nat × W)", "History V", seeds, "History.empty"),
        ("step", "(c d : C) (choice : Nat × W)", "Prop", step_guards, "False"),
        ("transfer", "(c d : C) (choice : Nat × W)", "Transfer V", transfers, "Transfer.keep"),
    ] {
        writeln!(out, "\ndef {name} {params} {args} : {typ} :=\n  match choice.1 with").unwrap();
        for (i, v) in values.iter().enumerate() {
            writeln!(out, "  | {i} => {v}").unwrap();
        }
        writeln!(out, "  | _ => {default}").unwrap();
    }
    writeln!(out, "\ndef observe {params} (c : C) (s : Summary V (Fin {count})) : Prop :=\n  {}", combine(&observations, "∧", "True"))
        .unwrap();
    writeln!(out, "\ndef model : HistoryRule.Model C V (Fin {count}) (Nat × W) where").unwrap();
    for field in ["predicate", "initial", "seed", "step", "transfer", "observe"] {
        writeln!(out, "  {field} := @{field} C V W sem").unwrap();
    }
    out.push_str(
        "\ndef before := (model sem).concrete\n\
         def after := (model sem).reduced\n\
         def project := (model sem).project\n\n\
         theorem certificate : Certificate (before sem) (after sem) (project sem) :=\n\
         \x20 (model sem).certificate\n\n\
         theorem optimization_correct :\n\
         \x20 (∀ s, Reachable (before sem) s → (before sem).safe s) ↔\n\
         \x20 (∀ a, Reachable (after sem) a → (after sem).safe a) :=\n\
         \x20 (model sem).optimization_correct\n\n\
         theorem specification_correct :\n\
         \x20 (∀ s, Reachable (withStuttering (before sem)) s → (before sem).safe s) ↔\n\
         \x20 (∀ a, Reachable (withStuttering (after sem)) a → (after sem).safe a) :=\n\
         \x20 (model sem).specification_correct\n\
         theorem counterexample_lifts {a} (ha : Reachable (after sem) a) (bad : ¬ (after sem).safe a) :\n\
         \x20 ∃ s, Reachable (before sem) s ∧ project sem s = a ∧ ¬ (before sem).safe s :=\n\
         \x20 (model sem).counterexample_lifts ha bad\n\
         theorem deadlock_preserved (s : C × History V) :\n\
         \x20 (¬ ∃ t, (before sem).next s t) ↔ (¬ ∃ a, (after sem).next (project sem s) a) :=\n\
         \x20 (model sem).deadlock_preserved s\n\n\
         #print axioms certificate\n\
         #print axioms optimization_correct\n\
         #print axioms specification_correct\n\
         #print axioms counterexample_lifts\n\
         #print axioms deadlock_preserved\n\
         end\nend TlxOptimization.GeneratedHistory\n",
    );
    Some(out)
}

pub(in super::super) const SEMANTICS: &str = "\n-- These are universal semantic parameters, not correctness axioms.\n\
         -- C contains retained variables; W contains branch-local bindings.\n\
         structure Semantics (C V W : Type) where\n\
         \x20 test : Nat → C → C → W → Prop\n\
         \x20 value : Nat → C → C → W → V\n\
         \x20 observe : Nat → C → Prop\n\
         \x20 member : Nat → V → Prop\n\
         \x20 field : V → String → V\n\
         \x20 constant : Nat → V\n\
         \x20 number : Int → V\n\
         \x20 string : String → V\n\
         \x20 boolean : Bool → V\n\n";

pub(in super::super) struct Emitter<'a> {
    pub(in super::super) var: VarId,
    monitors: &'a [Expr],
    pub(in super::super) atoms: Vec<String>,
}

impl<'a> Emitter<'a> {
    pub(in super::super) fn new(var: VarId, monitors: &'a [Expr]) -> Self {
        Self { var, monitors, atoms: vec![] }
    }

    pub(in super::super) fn predicates(&self) -> Option<Vec<String>> {
        self.monitors
            .iter()
            .map(|m| {
                let ExprKind::Quant { kind, bounds, body } = &*m.kind else { return None };
                let outer = one_local(&bounds[0])?;
                let predicate = self.predicate(body, outer, &[outer])?;
                Some(if *kind == QuantKind::Exists { format!("(¬ {predicate})") } else { predicate })
            })
            .collect::<Option<Vec<_>>>()
    }

    pub(in super::super) fn independent(&self, e: &Expr) -> bool {
        if matches!(&*e.kind, ExprKind::Var(v) if *v == self.var) {
            return false;
        }
        let mut valid = true;
        visit::children(e, &mut |e| valid &= self.independent(e));
        valid
    }

    fn atom(&mut self, e: &Expr) -> Option<usize> {
        if !self.independent(e) {
            return None;
        }
        let i = self.atoms.len();
        self.atoms.push(format!("{e:#?}"));
        Some(i)
    }

    fn branches(&mut self, branches: &[Branch], primed: bool) -> Option<(Vec<String>, Vec<String>)> {
        let mut guards = vec![];
        let mut transfers = vec![];
        for b in branches {
            let rhs = binding(b, self.var, primed)?;
            let mut terms = vec![];
            for e in &b.terms {
                match &*e.kind {
                    ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 && variable(&args[0], primed) == Some(self.var) => {}
                    ExprKind::Builtin { op: B::Unchanged, args } if primed && args.len() == 1 && unchanged(&args[0], self.var) == 1 => {
                        let rest = self.remove_history(&args[0])?;
                        terms.push(Expr::new(ExprKind::Builtin { op: B::Unchanged, args: vec![rest] }, e.span));
                    }
                    _ => terms.push(e.clone()),
                }
            }
            // Keep local bounds in the leaf record. Its semantic witness is
            // the same environment used to evaluate the appended event.
            if !b.bounds.iter().all(|b| self.independent(&b.set)) || !terms.iter().all(|e| self.independent(e)) {
                return None;
            }
            let id = self.atoms.len();
            self.atoms.push(format!("bounds: {:#?}\nterms: {terms:#?}", b.bounds));
            let next = if primed { "d" } else { "c" };
            guards.push(format!("sem.test {id} c {next} choice.2"));
            let transfer = self.transfer(&rhs, primed)?;
            transfers.push(if primed { transfer } else { format!("({transfer}).concrete History.empty") });
        }
        Some((guards, transfers))
    }

    fn remove_history(&self, e: &Expr) -> Option<Expr> {
        let kind = match &*e.kind {
            ExprKind::Var(v) if *v == self.var => ExprKind::Tuple(vec![]),
            ExprKind::Var(_) => return Some(e.clone()),
            ExprKind::Tuple(es) => ExprKind::Tuple(es.iter().map(|e| self.remove_history(e)).collect::<Option<_>>()?),
            _ => return None,
        };
        Some(Expr::new(kind, e.span))
    }

    pub(in super::super) fn transfer(&mut self, e: &Expr, primed: bool) -> Option<String> {
        let next = if primed { "d" } else { "c" };
        Some(match &*e.kind {
            ExprKind::Var(v) if primed && *v == self.var => "Transfer.keep".into(),
            ExprKind::Tuple(es) => {
                let mut h = "History.empty".to_string();
                for e in es {
                    let id = self.atom(e)?;
                    h = format!("(History.append {h} (sem.value {id} c {next} choice.2))");
                }
                format!("(Transfer.reset {h})")
            }
            ExprKind::Builtin { op: B::Append, args } if args.len() == 2 => {
                let t = self.transfer(&args[0], primed)?;
                let id = self.atom(&args[1])?;
                format!("(Transfer.append {t} (sem.value {id} c {next} choice.2))")
            }
            ExprKind::If { cond, then, els } => {
                let id = self.atom(cond)?;
                let then = self.transfer(then, primed)?;
                let els = self.transfer(els, primed)?;
                format!("(if sem.test {id} c {next} choice.2 then {then} else {els})")
            }
            _ => return None,
        })
    }

    fn predicate(&self, e: &Expr, outer: LocalId, indices: &[LocalId]) -> Option<String> {
        if let Some(p) = boolean(e, |e| self.predicate(e, outer, indices)) {
            return Some(p);
        }
        match &*e.kind {
            ExprKind::Builtin { op: B::Eq | B::Neq, args } if args.len() == 2 => {
                let a = self.term(&args[0], outer, indices)?;
                let b = self.term(&args[1], outer, indices)?;
                let op = if matches!(&*e.kind, ExprKind::Builtin { op: B::Eq, .. }) { "=" } else { "≠" };
                Some(format!("({a} {op} {b})"))
            }
            ExprKind::Quant { kind, bounds, body } if bounds.len() == 1 => {
                let id = one_local(&bounds[0])?;
                if !interval_end(&bounds[0].set).is_some_and(|e| matches!(&*e.kind, ExprKind::Local(i) if *i == outer)) {
                    return None;
                }
                let mut indices = indices.to_vec();
                indices.push(id);
                let p = self.predicate(body, outer, &indices)?;
                let (quant, join) = match kind {
                    QuantKind::Exists => ("∃", "∧"),
                    QuantKind::Forall => ("∀", "→"),
                };
                Some(format!("({quant} l{}, seen l{} {join} {p})", id.0, id.0))
            }
            _ => None,
        }
    }

    fn term(&self, e: &Expr, outer: LocalId, indices: &[LocalId]) -> Option<String> {
        Some(match &*e.kind {
            ExprKind::Const(c) => format!("(sem.constant {})", c.0),
            ExprKind::Num(n) => format!("(sem.number ({n}))"),
            ExprKind::Str(s) => format!("(sem.string {})", literal(s)),
            ExprKind::Bool(b) => format!("(sem.boolean {b})"),
            ExprKind::Field { record, field } => format!("(sem.field {} {})", self.term(record, outer, indices)?, literal(field)),
            ExprKind::FnApp { func, args } if variable(func, false) == Some(self.var) && args.len() == 1 => {
                let ExprKind::Local(i) = &*args[0].kind else { return None };
                if *i == outer {
                    "event".into()
                } else if indices.contains(i) {
                    format!("l{}", i.0)
                } else {
                    return None;
                }
            }
            _ => return None,
        })
    }

    pub(in super::super) fn observe(&mut self, e: &Expr) -> Option<String> {
        if self.independent(e) {
            return Some(format!("(sem.observe {} c)", self.atom(e)?));
        }
        if let Some(i) = self.monitors.iter().position(|m| Arc::ptr_eq(&m.kind, &e.kind)) {
            let bit = format!("(s.2 ⟨{i}, by decide⟩)");
            return Some(if matches!(&*e.kind, ExprKind::Quant { kind: QuantKind::Exists, .. }) { format!("(¬ {bit})") } else { bit });
        }
        if let Some(p) = boolean(e, |e| self.observe(e)) {
            return Some(p);
        }
        match &*e.kind {
            ExprKind::Builtin { op: B::Eq | B::Neq, args } if args.len() == 2 => {
                let empty = |e: &Expr| matches!(&*e.kind, ExprKind::Tuple(es) if es.is_empty());
                if (variable(&args[0], false) == Some(self.var) && empty(&args[1]))
                    || (variable(&args[1], false) == Some(self.var) && empty(&args[0]))
                {
                    Some(if matches!(&*e.kind, ExprKind::Builtin { op: B::Eq, .. }) { "(¬ ∃ e, s.1 e)" } else { "(∃ e, s.1 e)" }.into())
                } else {
                    None
                }
            }
            ExprKind::Builtin { op: B::In, args } if args.len() == 2 && variable(&args[0], false) == Some(self.var) => {
                let ExprKind::Builtin { op: B::Seq, args } = &*args[1].kind else { return None };
                if args.len() != 1 {
                    return None;
                }
                let id = self.atom(&args[0])?;
                Some(format!("(∀ e, s.1 e → sem.member {id} e)"))
            }
            _ => None,
        }
    }
}

fn combine(parts: &[String], op: &str, empty: &str) -> String {
    if parts.is_empty() {
        empty.into()
    } else {
        format!("({})", parts.join(&format!(" {op} ")))
    }
}

fn boolean(e: &Expr, mut child: impl FnMut(&Expr) -> Option<String>) -> Option<String> {
    Some(match &*e.kind {
        ExprKind::Bool(b) => if *b { "True" } else { "False" }.into(),
        ExprKind::And(es) => combine(&es.iter().map(&mut child).collect::<Option<Vec<_>>>()?, "∧", "True"),
        ExprKind::Or(es) => combine(&es.iter().map(&mut child).collect::<Option<Vec<_>>>()?, "∨", "False"),
        ExprKind::Builtin { op: B::Not, args } if args.len() == 1 => format!("(¬ {})", child(&args[0])?),
        ExprKind::Builtin { op: B::Implies | B::Equiv, args } if args.len() == 2 => {
            let op = if matches!(&*e.kind, ExprKind::Builtin { op: B::Implies, .. }) { "→" } else { "↔" };
            format!("({} {op} {})", child(&args[0])?, child(&args[1])?)
        }
        ExprKind::If { cond, then, els } => format!("(if {} then {} else {})", child(cond)?, child(then)?, child(els)?),
        _ => return None,
    })
}
