//! Lower accepted clock actions to the age rule IR. Semantic leaves may see
//! retained payloads and field presence, never absolute time or timestamp ages.
use std::fmt::Write;

mod decisions;
mod filters;
mod history;

use super::{binding, clock_transfer, variable, Atom, Branch, Domain, Proof};
use crate::{builtins::Builtin as B, hir::*, optimize::lean::literal, visit};

pub(super) fn emit(
    proof: &Proof<'_>,
    initial: &[Branch],
    steps: &[Branch],
    spec: super::super::CheckSpec<'_>,
    history: Option<&super::super::history::Candidate>,
) -> Option<super::super::OpenCert> {
    let mut slots = vec![];
    for (i, stamp) in proof.stamps.iter().enumerate() {
        let Domain::Function(keys, _) = &proof.domains.vars[stamp.var.idx()] else { return None };
        for key in keys {
            slots.push((i, key.clone()));
        }
    }
    if slots.is_empty() || slots.len() > 256 {
        return None;
    }
    let mut e = Emitter {
        proof,
        slots,
        atoms: vec![],
        scope: vec![],
        history: history.map(|h| super::super::history::lean::Emitter::new(h.var, &h.monitors)),
        remaining: 100_000,
    };
    let history_code = e.history_code(initial, steps)?;
    let initial = initial.iter().map(|b| e.branch(b, false)).collect::<Option<Vec<_>>>()?;
    let steps = steps.iter().map(|b| e.branch(b, true)).collect::<Option<Vec<_>>>()?;
    let observations = spec.invariants.iter().map(|o| e.test(o, true)).collect::<Option<Vec<_>>>()?;
    let init_obs = spec.init_props.iter().map(|o| e.test(o, true)).collect::<Option<Vec<_>>>()?;
    let constraints = spec.constraints.iter().map(|o| e.test(o, true)).collect::<Option<Vec<_>>>()?;
    let constrained = spec.is_constrained();
    let mut out = String::from(include_str!("../../AgeCertificate.lean"));
    if history.is_some() {
        out.push_str(include_str!("../../HistoryCertificate.lean"));
        out.push_str(include_str!("../../AgeHistoryCertificate.lean"));
    }
    out.push_str("\nnamespace TlxOptimization.GeneratedAge\nopen TlxOptimization AgeRule\nnoncomputable section\nset_option linter.unusedVariables false\nattribute [local instance] Classical.propDecidable\n");
    writeln!(out, "abbrev Key := Fin {}\ndef caps (k : Key) : Nat :=\n  match k.val with", e.slots.len()).unwrap();
    for (k, (i, key)) in e.slots.iter().enumerate() {
        writeln!(out, "  | {k} => {}", proof.stamps[*i].cap).unwrap();
        e.atoms.push(format!("slot {k}: map {:?}, field {:?}, key {key:#?}", proof.stamps[*i].var, proof.stamps[*i].field));
    }
    out.push_str("  | _ => 0\n\n-- C retains payloads with timestamp fields removed; p retains their presence.\n-- W supplies branch-local choices. HIR leaf interpretation/lowering is trusted.\nstructure Semantics (C W : Type) where\n  test : Nat → C → C → (Key → Bool) → W → Prop\n  observe : Nat → C → (Key → Bool) → Prop\n  filterTest : Nat → C → C → (Key → Bool) → W → List (List Nat) → List Bool → Prop\n  filterObserve : Nat → C → (Key → Bool) → List (List Nat) → List Bool → Prop\n");
    if history.is_some() {
        out = out.replace("namespace TlxOptimization.GeneratedAge\n", "namespace TlxOptimization.GeneratedAgeHistory\n");
        out = out.replace("structure Semantics (C W : Type) where", &format!(
            "namespace HistoryLeaves\n{}\nend HistoryLeaves\nstructure Semantics (C V W : Type) where\n  history : HistoryLeaves.Semantics (C × (Key → Bool)) V W",
            super::super::history::lean::SEMANTICS));
        out.push_str("open HistoryRule\n");
    }
    for (i, atom) in e.atoms.iter().enumerate() {
        writeln!(out, "def atom{i}HIR : String := {}", literal(atom)).unwrap();
    }
    let params = if history.is_some() { "{C V W : Type} (sem : Semantics C V W)" } else { "{C W : Type} (sem : Semantics C W)" };
    writeln!(out, "\nvariable {params}\ndef seed (choice : Nat × W) (k : Key) : Bool :=\n  match choice.1 with").unwrap();
    for (i, (_, changes, _)) in initial.iter().enumerate() {
        writeln!(out, "  | {i} => match k.val with").unwrap();
        for (k, change) in changes.iter().enumerate() {
            writeln!(out, "    | {k} => {}", change == "(Decision.pure Change.reset)").unwrap();
        }
        out.push_str("    | _ => false\n");
    }
    out.push_str("  | _ => false\n");
    writeln!(out, "def initial {params} (c : C) (choice : Nat × W) : Prop :=\n  let d := c\n  let p := seed choice\n  match choice.1 with")
        .unwrap();
    for (i, (guard, _, _)) in initial.iter().enumerate() {
        writeln!(out, "  | {i} => ({guard} : Test caps).reduced (fun k => if p k then some 0 else none)").unwrap();
    }
    out.push_str("  | _ => False\ndef delta (choice : Nat × W) : Nat :=\n  match choice.1 with\n");
    for (i, (_, _, tick)) in steps.iter().enumerate() {
        writeln!(out, "  | {i} => {}", usize::from(*tick)).unwrap();
    }
    out.push_str("  | _ => 0\n");
    let summary = history.map(|h| format!(" (s : Summary V (Fin {}))", h.monitors.len())).unwrap_or_default();
    writeln!(out, "def guard {params} (c d : C) (choice : Nat × W) (p : Key → Bool){summary} : Test caps :=\n  match choice.1 with")
        .unwrap();
    for (i, (guard, _, _)) in steps.iter().enumerate() {
        writeln!(out, "  | {i} => {guard}").unwrap();
    }
    out.push_str("  | _ => Test.pure False\n");
    writeln!(out, "def change {params} (c d : C) (choice : Nat × W) (p : Key → Bool) {summary} (k : Key) : Decision caps Change :=\n  match choice.1 with")
        .unwrap();
    for (i, (_, changes, _)) in steps.iter().enumerate() {
        writeln!(out, "  | {i} => match k.val with").unwrap();
        for (k, change) in changes.iter().enumerate() {
            writeln!(out, "    | {k} => {change}").unwrap();
        }
        out.push_str("    | _ => Decision.pure Change.keep\n");
    }
    out.push_str("  | _ => Decision.pure Change.keep\n");
    if let Some(code) = history_code {
        Some(e.emit_history(out, params, code, observations, init_obs, constraints, constrained))
    } else {
        writeln!(out, "def observe {params} (c : C) (p : Key → Bool) : Test caps := {}", fold(observations, "conj", "True")).unwrap();
        if constrained {
            writeln!(out, "def initObserve {params} (c : C) (p : Key → Bool) : Test caps := {}", fold(init_obs, "conj", "True")).unwrap();
            writeln!(out, "def constraint {params} (c : C) (p : Key → Bool) : Test caps := {}", fold(constraints, "conj", "True")).unwrap();
        }
        out.push_str("def model : AgeRule.Model C Key (Nat × W) where\n  caps := caps\n  initial := initial sem\n  seed := fun _ w => seed w\n  delta := delta\n  guard := guard sem\n  change := change sem\n  observe := observe sem\n");
        if constrained {
            out.push_str("  initObserve := initObserve sem\n  constraint := constraint sem\n");
        }
        Some(super::super::OpenCert::new(out, include_str!("certificate.lean"), "GeneratedAge", constrained, false, false))
    }
}

struct Emitter<'a, 'd> {
    proof: &'a Proof<'d>,
    slots: Vec<(usize, Atom)>,
    atoms: Vec<String>,
    scope: Vec<(LocalId, Atom)>,
    history: Option<super::super::history::lean::Emitter<'a>>,
    remaining: usize,
}
impl Emitter<'_, '_> {
    fn independent(&self, e: &Expr) -> bool {
        self.history.as_ref().is_none_or(|h| h.independent(e)) && self.age_independent(e)
    }

    fn age_independent(&self, e: &Expr) -> bool {
        match &*e.kind {
            ExprKind::Var(v) if *v == self.proof.clock || self.proof.stamps.iter().any(|s| s.var == *v) => return false,
            ExprKind::Builtin { op: B::Prime, args } if args.iter().any(|e| self.mentions_age_state(e)) => return false,
            ExprKind::Field { record, field } => {
                if let Some((i, index)) = self.proof.entry(record) {
                    return *field != self.proof.stamps[i].field && self.age_independent(index);
                }
            }
            ExprKind::Builtin { op: B::Domain, args } if args.len() == 1 => {
                if variable(&args[0], false).is_some_and(|v| self.proof.stamps.iter().any(|s| s.var == v)) {
                    return true;
                }
                if let Some((_, index)) = self.proof.entry(&args[0]) {
                    return self.age_independent(index);
                }
            }
            ExprKind::Builtin { op: B::In, args } if args.len() == 2 => {
                if variable(&args[0], false).is_some_and(|v| {
                    self.proof.stamps.iter().any(|s| s.var == v) && self.proof.domains.belongs(&self.proof.domains.vars[v.idx()], &args[1])
                }) {
                    return true;
                }
            }
            ExprKind::Builtin { op: B::Eq | B::Neq, args } if args.len() == 2 => {
                for (entry, literal) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                    if let Some((i, index)) = self.proof.entry(entry) {
                        if matches!(&*literal.kind, ExprKind::Record(fs) if fs.iter().all(|(f, _)| *f != self.proof.stamps[i].field)) {
                            return self.age_independent(index) && self.age_independent(literal);
                        }
                    }
                }
            }
            _ => {}
        }
        let mut valid = true;
        visit::children(e, &mut |child| valid &= self.age_independent(child));
        valid
    }

    // Leaves receive old timestamp presence only. Even a primed DOMAIN read
    // needs the new presence bits; do not hide that dependency in a pure leaf.
    fn mentions_age_state(&self, e: &Expr) -> bool {
        if matches!(&*e.kind, ExprKind::Var(v) if *v == self.proof.clock || self.proof.stamps.iter().any(|s| s.var == *v)) {
            return true;
        }
        let mut found = false;
        visit::children(e, &mut |e| found |= self.mentions_age_state(e));
        found
    }

    fn atom(&mut self, e: &Expr, observation: bool, payload: bool) -> Option<String> {
        if !payload && !self.independent(e) {
            return None;
        }
        let id = self.atoms.len();
        self.atoms.push(format!(
            "{} {e:#?}\nBound atoms: {:?}",
            if payload { "Retained-payload equation:" } else { "Independent predicate:" },
            self.scope
        ));
        Some(if observation { format!("sem.observe {id} c p") } else { format!("sem.test {id} c d p choice.2") })
    }

    // Configured model values can occur inside a set without any scalar
    // constant naming them. Record their exact Atom identity instead of
    // inventing a TLA expression or a runtime-specific numeric identifier.
    fn slot_test(&mut self, index: &Expr, k: usize, observation: bool) -> Option<String> {
        if !self.independent(index) {
            return None;
        }
        let id = self.atoms.len();
        self.atoms.push(format!("Slot equality: index {index:#?} = configured atom {:?}\nBound atoms: {:?}", self.slots[k].1, self.scope));
        Some(if observation { format!("sem.observe {id} c p") } else { format!("sem.test {id} c d p choice.2") })
    }

    fn branch(&mut self, b: &Branch, primed: bool) -> Option<(String, Vec<String>, bool)> {
        let tick = primed && clock_transfer(&binding(b, self.proof.clock, true)?, self.proof.clock)?;
        let mut tests = vec![];
        let mut changes = vec!["(Decision.pure Change.keep)".to_owned(); self.slots.len()];
        for i in 0..self.proof.stamps.len() {
            let var = self.proof.stamps[i].var;
            let rhs = binding(b, var, primed)?;
            tests.push(self.payload_guard(&rhs, i, primed)?);
            for (k, change) in changes.iter_mut().enumerate() {
                if self.slots[k].0 == i {
                    *change = self.change(&rhs, i, k, primed)?;
                }
            }
        }
        for bound in &b.bounds {
            let BoundVars::Many(ids) = &bound.vars else { return None };
            if !primed && !self.independent(&bound.set) {
                return None;
            }
            for id in ids {
                tests.push(
                    self.test(
                        &builtin(B::In, vec![Expr::new(ExprKind::Local(*id), bound.set.span), bound.set.clone()], &bound.set),
                        false,
                    )?,
                );
            }
        }
        for term in &b.terms {
            if self.history.as_ref().is_some_and(
                |h| matches!(&*term.kind, ExprKind::Builtin {op:B::Eq,args} if args.len()==2 && variable(&args[0],primed)==Some(h.var)),
            ) {
                continue;
            }
            if matches!(&*term.kind, ExprKind::Builtin {op:B::Eq,args} if args.len()==2 && variable(&args[0],primed).is_some_and(|v| v==self.proof.clock || self.proof.stamps.iter().any(|s|s.var==v)))
            {
                continue;
            }
            if let ExprKind::Builtin { op: B::Unchanged, args } = &*term.kind {
                if primed && args.len() == 1 {
                    let mut frames = vec![];
                    self.frames(&args[0], &mut frames)?;
                    for frame in frames {
                        tests.push(self.test(&builtin(B::Unchanged, vec![frame], term), false)?);
                    }
                    continue;
                }
            }
            // Initial predicates must not inspect time, even through deadlines.
            if !primed && !self.independent(term) {
                return None;
            }
            tests.push(self.test(term, false)?);
        }
        Some((fold(tests, "conj", "True"), changes, tick))
    }

    fn frames(&self, e: &Expr, out: &mut Vec<Expr>) -> Option<()> {
        match &*e.kind {
            ExprKind::Var(v) => {
                if *v != self.proof.clock
                    && !self.proof.stamps.iter().any(|s| s.var == *v)
                    && self.history.as_ref().is_none_or(|h| h.var != *v)
                {
                    out.push(e.clone());
                }
            }
            ExprKind::Tuple(es) => {
                for e in es {
                    self.frames(e, out)?;
                }
            }
            _ => return None,
        }
        Some(())
    }

    fn payload_guard(&mut self, rhs: &Expr, i: usize, primed: bool) -> Option<String> {
        if primed {
            if let Some((test, then, els)) = self.split_decision(rhs) {
                let yes = self.payload_guard(&then, i, primed)?;
                let no = self.payload_guard(&els, i, primed)?;
                self.remaining = self.remaining.checked_sub(test.len() * 2 + yes.len() + no.len())?;
                return Some(format!("(Test.disj (Test.conj {test} {yes}) (Test.conj (Test.neg {test}) {no}))"));
            }
        }
        if let ExprKind::If { cond, then, els } = &*rhs.kind {
            if primed {
                let test = self.test(cond, false)?;
                let yes = self.payload_guard(then, i, primed)?;
                let no = self.payload_guard(els, i, primed)?;
                return Some(format!("(Test.disj (Test.conj {test} {yes}) (Test.conj (Test.neg {test}) {no}))"));
            }
        }
        let payload = self.payload(rhs, i)?;
        let lhs = Expr::new(ExprKind::Var(self.proof.stamps[i].var), rhs.span);
        let lhs = if primed { builtin(B::Prime, vec![lhs], rhs) } else { lhs };
        let equation = builtin(B::Eq, vec![lhs, payload], rhs);
        Some(format!("(Test.pure ({}))", self.atom(&equation, false, true)?))
    }

    fn record(&self, e: &Expr, i: usize) -> Option<Expr> {
        let ExprKind::Record(fs) = &*e.kind else { return None };
        let fields: Vec<_> = fs.iter().filter(|(f, _)| *f != self.proof.stamps[i].field).cloned().collect();
        if !fields.iter().all(|(_, e)| self.independent(e)) {
            return None;
        }
        Some(Expr::new(ExprKind::Record(fields), e.span))
    }

    fn payload(&mut self, e: &Expr, i: usize) -> Option<Expr> {
        self.remaining = self.remaining.checked_sub(1)?;
        let field = &self.proof.stamps[i].field;
        let kind = match &*e.kind {
            ExprKind::Var(v) if *v == self.proof.stamps[i].var => return Some(e.clone()),
            ExprKind::FnConstruct { bounds, body } if bounds.iter().all(|b| self.independent(&b.set)) => {
                ExprKind::FnConstruct { bounds: bounds.clone(), body: self.record(body, i)? }
            }
            ExprKind::Except { base, updates } => {
                let mut retained = vec![];
                for (path, rhs) in updates {
                    let [ExceptKey::Index(indices), rest @ ..] = path.as_slice() else { return None };
                    if !indices.iter().all(|e| self.independent(e)) {
                        return None;
                    }
                    match rest {
                        [] => retained.push((path.clone(), self.record(rhs, i)?)),
                        [ExceptKey::Field(f)] if f == field => {}
                        [ExceptKey::Field(_)] if self.independent(rhs) => retained.push((path.clone(), rhs.clone())),
                        _ => return None,
                    }
                }
                if retained.is_empty() {
                    return Some(base.clone());
                }
                ExprKind::Except { base: base.clone(), updates: retained }
            }
            ExprKind::If { cond, then, els } if self.independent(cond) => {
                ExprKind::If { cond: cond.clone(), then: self.payload(then, i)?, els: self.payload(els, i)? }
            }
            _ => return None,
        };
        Some(Expr::new(kind, e.span))
    }

    fn change(&mut self, e: &Expr, i: usize, k: usize, primed: bool) -> Option<String> {
        self.remaining = self.remaining.checked_sub(1)?;
        if primed {
            if let Some((test, then, els)) = self.split_decision(e) {
                let yes = self.change(&then, i, k, primed)?;
                let no = self.change(&els, i, k, primed)?;
                self.remaining = self.remaining.checked_sub(test.len() + yes.len() + no.len())?;
                return Some(format!("(Decision.branch {test} {yes} {no})"));
            }
        }
        let record_change = |r: &Expr| {
            let ExprKind::Record(fs) = &*r.kind else { return None };
            Some(
                if fs.iter().any(|(f, _)| *f == self.proof.stamps[i].field) {
                    "(Decision.pure Change.reset)"
                } else {
                    "(Decision.pure Change.erase)"
                }
                .to_owned(),
            )
        };
        match &*e.kind {
            ExprKind::Var(_) if primed => Some("(Decision.pure Change.keep)".into()),
            ExprKind::FnConstruct { body, .. } => record_change(body),
            ExprKind::Except { updates, .. } if primed => {
                let mut result = "(Decision.pure Change.keep)".to_owned();
                for (path, rhs) in updates {
                    let [ExceptKey::Index(indices), rest @ ..] = path.as_slice() else { return None };
                    let [index] = indices.as_slice() else { return None };
                    let update = match rest {
                        [] => record_change(rhs)?,
                        // EXCEPT on an absent record field is a no-op. Preserve
                        // the presence bit instead of manufacturing a timestamp.
                        [ExceptKey::Field(f)] if *f == self.proof.stamps[i].field => {
                            format!("(Decision.bindValue {result} (fun previous => Decision.pure (Change.refresh previous (p ⟨{k}, by decide⟩))))")
                        }
                        [ExceptKey::Field(_)] => continue,
                        _ => return None,
                    };
                    self.remaining = self.remaining.checked_sub(result.len() + update.len())?;
                    result = format!("(if {} then {update} else {result})", self.slot_test(index, k, false)?);
                }
                Some(result)
            }
            ExprKind::If { cond, then, els } if primed => Some(format!(
                "(Decision.branch {} {} {})",
                self.test(cond, false)?,
                self.change(then, i, k, primed)?,
                self.change(els, i, k, primed)?
            )),
            _ => None,
        }
    }

    fn test(&mut self, e: &Expr, observation: bool) -> Option<String> {
        self.remaining = self.remaining.checked_sub(1)?;
        if self.age_independent(e) {
            if let Some(h) = &mut self.history {
                if !h.independent(e) {
                    let start = h.atoms.len();
                    if let Some(term) = h.test(e, observation) {
                        for atom in &mut h.atoms[start..] {
                            write!(atom, "\nBound atoms: {:?}", self.scope).unwrap();
                        }
                        let next = if observation { "" } else { "let d := (d, p); " };
                        return Some(format!("(Test.pure (let sem := sem.history; let c := (c, p); {next}{term}))"));
                    }
                    // A finite filter can bind history predicates even when
                    // the standalone history consumer rejects its binder.
                    h.atoms.truncate(start);
                }
            }
        }
        if self.independent(e) {
            return Some(format!("(Test.pure ({}))", self.atom(e, observation, false)?));
        }
        let result = match &*e.kind {
            ExprKind::Quant { .. } => return self.quantified(e, observation),
            ExprKind::And(es) | ExprKind::Or(es) => {
                let and = matches!(&*e.kind, ExprKind::And(_));
                fold(
                    es.iter().map(|e| self.test(e, observation)).collect::<Option<_>>()?,
                    if and { "conj" } else { "disj" },
                    if and { "True" } else { "False" },
                )
            }
            ExprKind::If { cond, then, els } => {
                let c = self.test(cond, observation)?;
                format!(
                    "(Test.disj (Test.conj {c} {}) (Test.conj (Test.neg {c}) {}))",
                    self.test(then, observation)?,
                    self.test(els, observation)?
                )
            }
            ExprKind::Builtin { op, args } => match (op, args.as_slice()) {
                (B::Not, [p]) => format!("(Test.neg {})", self.test(p, observation)?),
                (B::Implies, [p, q]) => format!("(Test.disj (Test.neg {}) {})", self.test(p, observation)?, self.test(q, observation)?),
                (B::In, [a, b])
                    if variable(a, false) == Some(self.proof.clock)
                        && self.proof.domains.belongs(&self.proof.domains.vars[self.proof.clock.idx()], b) =>
                {
                    "(Test.pure True)".into()
                }
                (B::Eq | B::Neq | B::Lt | B::Le | B::Gt | B::Ge, [a, b]) => {
                    return self.comparison(*op, a, b, observation).or_else(|| self.filtered_consumer(e, observation));
                }
                _ => return self.filtered_consumer(e, observation),
            },
            _ => return self.filtered_consumer(e, observation),
        };
        Some(result)
    }

    fn comparison(&mut self, op: B, a: &Expr, b: &Expr, observation: bool) -> Option<String> {
        if variable(a, false) == Some(self.proof.clock) {
            return self.comparison(
                match op {
                    B::Lt => B::Gt,
                    B::Le => B::Ge,
                    B::Gt => B::Lt,
                    B::Ge => B::Le,
                    x => x,
                },
                b,
                a,
                observation,
            );
        }
        if variable(b, false) != Some(self.proof.clock) {
            return None;
        }
        let (i, index, delay) = self.proof.timestamp(a)?;
        let mut alternatives = vec![];
        for k in 0..self.slots.len() {
            if self.slots[k].0 != i {
                continue;
            }
            let key = format!("(Test.pure ({}))", self.slot_test(index, k, observation)?);
            let at_least = |d| format!("(Test.atLeast ⟨{k}, by decide⟩ {d} (by decide))");
            let predicate = match op {
                B::Le => at_least(delay),
                B::Lt => at_least(delay + 1),
                B::Ge => format!("(Test.neg {})", at_least(delay + 1)),
                B::Gt => format!("(Test.neg {})", at_least(delay)),
                B::Eq => format!("(Test.conj {} (Test.neg {}))", at_least(delay), at_least(delay + 1)),
                B::Neq => format!("(Test.neg (Test.conj {} (Test.neg {})))", at_least(delay), at_least(delay + 1)),
                _ => return None,
            };
            alternatives.push(format!("(Test.conj {key} {predicate})"));
        }
        Some(fold(alternatives, "disj", "False"))
    }
}
fn builtin(op: B, args: Vec<Expr>, at: &Expr) -> Expr {
    Expr::new(ExprKind::Builtin { op, args }, at.span)
}
fn fold(tests: Vec<String>, op: &str, identity: &str) -> String {
    tests.into_iter().rev().fold(format!("(Test.pure {identity})"), |tail, head| format!("(Test.{op} {head} {tail})"))
}
