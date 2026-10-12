//! Lower accepted clock actions to the age rule IR. Semantic leaves may see
//! retained payloads and field presence, never absolute time or timestamp ages.
use std::fmt::Write;

mod filters;

use super::{binding, clock_transfer, variable, Atom, Branch, Domain, Proof};
use crate::{builtins::Builtin as B, hir::*, optimize::lean::literal, visit};

pub(super) fn emit(proof: &Proof<'_>, initial: &[Branch], steps: &[Branch], observations: &[Expr]) -> Option<String> {
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
    let mut e = Emitter { proof, slots, atoms: vec![], scope: vec![], remaining: 100_000 };
    let initial = initial.iter().map(|b| e.branch(b, false)).collect::<Option<Vec<_>>>()?;
    let steps = steps.iter().map(|b| e.branch(b, true)).collect::<Option<Vec<_>>>()?;
    let observations = observations.iter().map(|o| e.test(o, true)).collect::<Option<Vec<_>>>()?;
    let mut out = String::from(include_str!("../../AgeCertificate.lean"));
    out.push_str("\nnamespace TlxOptimization.GeneratedAge\nopen TlxOptimization AgeRule\nnoncomputable section\nset_option linter.unusedVariables false\nattribute [local instance] Classical.propDecidable\n");
    writeln!(out, "abbrev Key := Fin {}\ndef caps (k : Key) : Nat :=\n  match k.val with", e.slots.len()).unwrap();
    for (k, (i, key)) in e.slots.iter().enumerate() {
        writeln!(out, "  | {k} => {}", proof.stamps[*i].cap).unwrap();
        e.atoms.push(format!("slot {k}: map {:?}, field {:?}, key {key:#?}", proof.stamps[*i].var, proof.stamps[*i].field));
    }
    out.push_str("  | _ => 0\n\n-- C retains payloads with timestamp fields removed; p retains their presence.\n-- W supplies branch-local choices. HIR leaf interpretation/lowering is trusted.\nstructure Semantics (C W : Type) where\n  test : Nat → C → C → (Key → Bool) → W → Prop\n  observe : Nat → C → (Key → Bool) → Prop\n  filterTest : Nat → C → C → (Key → Bool) → W → List (List Nat) → Prop\n  filterObserve : Nat → C → (Key → Bool) → List (List Nat) → Prop\n");
    for (i, atom) in e.atoms.iter().enumerate() {
        writeln!(out, "def atom{i}HIR : String := {}", literal(atom)).unwrap();
    }
    let params = "{C W : Type} (sem : Semantics C W)";
    writeln!(
        out,
        "\nvariable {{C W : Type}} (sem : Semantics C W)\ndef seed (choice : Nat × W) (k : Key) : Bool :=\n  match choice.1 with"
    )
    .unwrap();
    for (i, (_, changes, _)) in initial.iter().enumerate() {
        writeln!(out, "  | {i} => match k.val with").unwrap();
        for (k, change) in changes.iter().enumerate() {
            writeln!(out, "    | {k} => {}", change == "Change.reset").unwrap();
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
    writeln!(out, "def guard {params} (c d : C) (choice : Nat × W) (p : Key → Bool) : Test caps :=\n  match choice.1 with").unwrap();
    for (i, (guard, _, _)) in steps.iter().enumerate() {
        writeln!(out, "  | {i} => {guard}").unwrap();
    }
    out.push_str("  | _ => Test.pure False\n");
    writeln!(out, "def change {params} (c d : C) (choice : Nat × W) (p : Key → Bool) (k : Key) : Change :=\n  match choice.1 with")
        .unwrap();
    for (i, (_, changes, _)) in steps.iter().enumerate() {
        writeln!(out, "  | {i} => match k.val with").unwrap();
        for (k, change) in changes.iter().enumerate() {
            writeln!(out, "    | {k} => {change}").unwrap();
        }
        out.push_str("    | _ => Change.keep\n");
    }
    out.push_str("  | _ => Change.keep\n");
    writeln!(out, "def observe {params} (c : C) (p : Key → Bool) : Test caps := {}", fold(observations, "conj", "True")).unwrap();
    out.push_str("def model : AgeRule.Model C Key (Nat × W) where\n  caps := caps\n  initial := initial sem\n  seed := fun _ w => seed w\n  delta := delta\n  guard := guard sem\n  change := change sem\n  observe := observe sem\n");
    out.push_str(include_str!("certificate.lean"));
    Some(out)
}

struct Emitter<'a, 'd> {
    proof: &'a Proof<'d>,
    slots: Vec<(usize, Atom)>,
    atoms: Vec<String>,
    scope: Vec<(LocalId, Atom)>,
    remaining: usize,
}
impl Emitter<'_, '_> {
    fn independent(&self, e: &Expr) -> bool {
        match &*e.kind {
            ExprKind::Var(v) if *v == self.proof.clock || self.proof.stamps.iter().any(|s| s.var == *v) => return false,
            ExprKind::Field { record, field } => {
                if let Some((i, index)) = self.proof.entry(record) {
                    return *field != self.proof.stamps[i].field && self.independent(index);
                }
            }
            ExprKind::Builtin { op: B::Domain, args } if args.len() == 1 => {
                if variable(&args[0], false).is_some_and(|v| self.proof.stamps.iter().any(|s| s.var == v)) {
                    return true;
                }
                if let Some((_, index)) = self.proof.entry(&args[0]) {
                    return self.independent(index);
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
                            return self.independent(index) && self.independent(literal);
                        }
                    }
                }
            }
            _ => {}
        }
        let mut valid = true;
        visit::children(e, &mut |child| valid &= self.independent(child));
        valid
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
        let mut changes = vec!["Change.keep".to_owned(); self.slots.len()];
        for i in 0..self.proof.stamps.len() {
            let var = self.proof.stamps[i].var;
            let rhs = binding(b, var, primed)?;
            let payload = self.payload(&rhs, i)?;
            let lhs = Expr::new(ExprKind::Var(var), rhs.span);
            let lhs = if primed { builtin(B::Prime, vec![lhs], &rhs) } else { lhs };
            let equation = builtin(B::Eq, vec![lhs, payload], &rhs);
            tests.push(format!("(Test.pure ({}))", self.atom(&equation, false, true)?));
            for (k, change) in changes.iter_mut().enumerate() {
                if self.slots[k].0 == i {
                    *change = self.change(&rhs, i, k, primed)?;
                }
            }
        }
        for bound in &b.bounds {
            let BoundVars::Many(ids) = &bound.vars else { return None };
            if !self.independent(&bound.set) {
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
                if *v != self.proof.clock && !self.proof.stamps.iter().any(|s| s.var == *v) {
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
        let record_change = |r: &Expr| {
            let ExprKind::Record(fs) = &*r.kind else { return None };
            Some(if fs.iter().any(|(f, _)| *f == self.proof.stamps[i].field) { "Change.reset" } else { "Change.erase" }.to_owned())
        };
        match &*e.kind {
            ExprKind::Var(_) if primed => Some("Change.keep".into()),
            ExprKind::FnConstruct { body, .. } => record_change(body),
            ExprKind::Except { updates, .. } if primed => {
                let mut result = "Change.keep".to_owned();
                for (path, rhs) in updates {
                    let [ExceptKey::Index(indices), rest @ ..] = path.as_slice() else { return None };
                    let [index] = indices.as_slice() else { return None };
                    let update = match rest {
                        [] => record_change(rhs)?,
                        // EXCEPT on an absent record field is a no-op. Preserve
                        // the presence bit instead of manufacturing a timestamp.
                        [ExceptKey::Field(f)] if *f == self.proof.stamps[i].field => {
                            format!("(Change.refresh {result} (p ⟨{k}, by decide⟩))")
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
                "(if {} then {} else {})",
                self.atom(cond, false, false)?,
                self.change(then, i, k, primed)?,
                self.change(els, i, k, primed)?
            )),
            _ => None,
        }
    }

    fn test(&mut self, e: &Expr, observation: bool) -> Option<String> {
        self.remaining = self.remaining.checked_sub(1)?;
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
