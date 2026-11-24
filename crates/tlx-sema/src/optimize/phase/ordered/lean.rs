//! Connected rule-model certificates. Unsupported applications are refused;
//! independent HIR leaves cannot access the forgotten allocation magnitude.
use super::{binding, syntax, variable, Branch, Family, OrderedPlan};
use crate::{builtins::Builtin as B, hir::*, optimize::lean::literal, visit};
use std::fmt::Write;

pub(super) fn emit(
    families: &[Family],
    plan: &OrderedPlan,
    initial: &[Branch],
    steps: &[Branch],
    spec: super::super::CheckSpec<'_>,
) -> Option<super::super::OpenCert> {
    let [family] = families else { return None };
    if plan.history.is_some()
        || plan.anchors != [vec![family.initial]]
        || plan.variables.iter().enumerate().any(|(i, s)| {
            i != family.variable.idx()
                && (s.family.is_some() || !s.fields.is_empty() || s.key.is_some() || s.value.is_some() || s.element.is_some())
        })
    {
        return None;
    }
    let mut e = Emitter { frontier: family.variable, seed: family.initial, atoms: vec![], remaining: 100_000 };
    let mut init = vec![];
    let mut guards = vec![];
    let mut deltas = vec![];
    for branch in initial {
        init.push(e.branch(branch, false)?);
    }
    for branch in steps {
        let delta = syntax::increment(&binding(branch, family.variable, true)?, family.variable)?;
        let ExprKind::Num(delta) = &*delta.kind else { return None };
        if *delta < 0 {
            return None;
        }
        deltas.push(delta.to_string());
        guards.push(e.branch(branch, true)?);
    }
    let observations = spec.invariants.iter().map(|p| e.test(p, true)).collect::<Option<Vec<_>>>()?;
    let init_obs = spec.init_props.iter().map(|p| e.test(p, true)).collect::<Option<Vec<_>>>()?;
    let constraints = spec.constraints.iter().map(|p| e.test(p, true)).collect::<Option<Vec<_>>>()?;
    let constrained = spec.is_constrained();
    let mut out = String::from(include_str!("../../OrderedCertificate.lean"));
    out.push_str("\nnamespace TlxOptimization.GeneratedOrdered\nopen TlxOptimization OrderedRule\nnoncomputable section\nset_option linter.unusedVariables false\nattribute [local instance] Classical.propDecidable\n");
    out.push_str("\n-- C contains exactly retained state; W contains independent local choices.\nstructure Semantics (C W : Type) where\n  test : Nat → C → C → W → Prop\n  observe : Nat → C → Prop\n");
    for (i, atom) in e.atoms.iter().enumerate() {
        writeln!(out, "def atom{i}HIR : String := {}", literal(atom)).unwrap();
    }
    let seed = family.initial;
    out.push_str("\nvariable {C W : Type} (sem : Semantics C W)\n");
    let params = "{C W : Type} (sem : Semantics C W)";
    writeln!(out, "def initial {params} (c : C) (choice : Nat × W) : Prop :=\n  let d := c\n  match choice.1 with").unwrap();
    for (i, guard) in init.iter().enumerate() {
        writeln!(out, "  | {i} => ({guard}).concrete {seed} {seed}").unwrap();
    }
    out.push_str("  | _ => False\n");
    out.push_str("def delta (choice : Nat × W) : Nat :=\n  match choice.1 with\n");
    for (i, delta) in deltas.iter().enumerate() {
        writeln!(out, "  | {i} => {delta}").unwrap();
    }
    out.push_str("  | _ => 0\n");
    writeln!(out, "def guard {params} (c d : C) (choice : Nat × W) : Test :=\n  match choice.1 with").unwrap();
    for (i, guard) in guards.iter().enumerate() {
        writeln!(out, "  | {i} => {guard}").unwrap();
    }
    out.push_str("  | _ => Test.pure False\n");
    writeln!(out, "def observe {params} (c : C) : Test := {}", fold(observations, "conj", "True")).unwrap();
    if constrained {
        writeln!(out, "def initObserve {params} (c : C) : Test := {}", fold(init_obs, "conj", "True")).unwrap();
        writeln!(out, "def constraint {params} (c : C) : Test := {}", fold(constraints, "conj", "True")).unwrap();
    }
    writeln!(out, "def model : OrderedRule.Model C (Nat × W) where\n  seed := {seed}\n  initial := initial sem\n  delta := delta\n  guard := guard sem\n  observe := observe sem").unwrap();
    if constrained {
        out.push_str("  initObserve := initObserve sem\n  constraint := constraint sem\n");
    }
    let tail = "def before := (model sem).concrete\n\
         def after := (model sem).reduced\n\
         def project := (model sem).project\n\
         theorem runtime_key_equivalent (s t : State C (model sem).seed) :\n\
         \x20 (model sem).rankKey s = (model sem).rankKey t ↔ project sem s = project sem t :=\n\
         \x20 (model sem).runtime_key_equivalent s t\n\
         theorem certificate : Certificate (before sem) (after sem) (project sem) :=\n\
         \x20 (model sem).certificate\n\
         theorem optimization_correct :\n\
         \x20 (∀ s, Reachable (before sem) s → (before sem).safe s) ↔\n\
         \x20 (∀ a, Reachable (after sem) a → (after sem).safe a) :=\n\
         \x20 (model sem).optimization_correct\n\
         theorem specification_correct :\n\
         \x20 (∀ s, Reachable (withStuttering (before sem)) s → (before sem).safe s) ↔\n\
         \x20 (∀ a, Reachable (withStuttering (after sem)) a → (after sem).safe a) :=\n\
         \x20 (model sem).specification_correct\n\
         theorem counterexample_lifts {a} (ha : Reachable (after sem) a) (bad : ¬ (after sem).safe a) :\n\
         \x20 ∃ s, Reachable (before sem) s ∧ project sem s = a ∧ ¬ (before sem).safe s :=\n\
         \x20 (model sem).counterexample_lifts ha bad\n\
         theorem deadlock_preserved (s : State C (model sem).seed) :\n\
         \x20 (¬ ∃ t, (before sem).next s t) ↔ (¬ ∃ a, (after sem).next (project sem s) a) :=\n\
         \x20 (model sem).deadlock_preserved s\n\
         #print axioms certificate\n\
         #print axioms runtime_key_equivalent\n\
         #print axioms optimization_correct\n\
         #print axioms specification_correct\n\
         #print axioms counterexample_lifts\n\
         #print axioms deadlock_preserved\n";
    Some(super::super::OpenCert::new(out, tail, "GeneratedOrdered", constrained, false, false))
}

struct Emitter {
    frontier: VarId,
    seed: i128,
    atoms: Vec<String>,
    remaining: usize,
}
impl Emitter {
    fn independent(&self, e: &Expr) -> bool {
        if matches!(&*e.kind, ExprKind::Var(v) if *v == self.frontier) {
            return false;
        }
        let mut valid = true;
        visit::children(e, &mut |child| valid &= self.independent(child));
        valid
    }

    fn branch(&mut self, branch: &Branch, primed: bool) -> Option<String> {
        // Branch-local domains must not inspect the allocation frontier.
        let mut predicates = vec![];
        for b in &branch.bounds {
            if !self.independent(&b.set) {
                return None;
            }
            for l in b.vars.locals() {
                if !matches!(b.vars, BoundVars::Many(_)) {
                    return None;
                }
                predicates.push(self.test(
                    &Expr::new(
                        ExprKind::Builtin { op: B::In, args: vec![Expr::new(ExprKind::Local(*l), b.set.span), b.set.clone()] },
                        b.set.span,
                    ),
                    false,
                )?);
            }
        }
        for term in &branch.terms {
            if matches!(&*term.kind, ExprKind::Builtin {op:B::Eq,args} if args.len()==2 && variable(&args[0],primed)==Some(self.frontier)) {
                continue;
            }
            if let ExprKind::Builtin { op: B::Unchanged, args } = &*term.kind {
                if primed && args.len() == 1 {
                    let mut variables = vec![];
                    self.frame(&args[0], &mut variables)?;
                    for v in variables {
                        let frame = Expr::new(ExprKind::Builtin { op: B::Unchanged, args: vec![v] }, term.span);
                        predicates.push(self.test(&frame, false)?);
                    }
                    continue;
                }
            }
            predicates.push(self.test(term, false)?);
        }
        Some(fold(predicates, "conj", "True"))
    }

    fn frame(&self, e: &Expr, out: &mut Vec<Expr>) -> Option<()> {
        match &*e.kind {
            ExprKind::Var(v) if *v != self.frontier => out.push(e.clone()),
            ExprKind::Var(_) => {}
            ExprKind::Tuple(es) => {
                for e in es {
                    self.frame(e, out)?;
                }
            }
            _ => return None,
        }
        Some(())
    }

    fn test(&mut self, e: &Expr, observation: bool) -> Option<String> {
        self.remaining = self.remaining.checked_sub(1)?;
        if self.independent(e) {
            let i = self.atoms.len();
            self.atoms.push(format!("{e:#?}"));
            return Some(if observation {
                format!("(Test.pure (sem.observe {i} c))")
            } else {
                format!("(Test.pure (sem.test {i} c d choice.2))")
            });
        }
        let t = match &*e.kind {
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
                (B::Eq | B::Neq, [a, b]) => {
                    let equal = self.equality(a, b, observation)?;
                    if *op == B::Neq {
                        format!("(Test.neg {equal})")
                    } else {
                        equal
                    }
                }
                (B::Lt | B::Le | B::Gt | B::Ge, [a, b]) => self.comparison(*op, a, b)?,
                (B::In, [a, b])
                    if variable(a, false) == Some(self.frontier)
                        && matches!(&*b.kind, ExprKind::Builtin {op:B::Nat | B::Int,args} if args.is_empty()) =>
                {
                    "(Test.pure True)".into()
                }
                _ => return None,
            },
            _ => return None,
        };
        Some(t)
    }

    fn equality(&mut self, a: &Expr, b: &Expr, observation: bool) -> Option<String> {
        if let ExprKind::If { cond, then, els } = &*b.kind {
            let eq = |rhs: &Expr| Expr::new(ExprKind::Builtin { op: B::Eq, args: vec![a.clone(), rhs.clone()] }, a.span);
            let c = self.test(cond, observation)?;
            return Some(format!(
                "(Test.disj (Test.conj {c} {}) (Test.conj (Test.neg {c}) {}))",
                self.test(&eq(then), observation)?,
                self.test(&eq(els), observation)?
            ));
        }
        if matches!(&*a.kind, ExprKind::If { .. }) {
            return self.equality(b, a, observation);
        }
        if variable(a, false) == Some(self.frontier) {
            let ExprKind::Num(n) = &*b.kind else { return None };
            if *n > self.seed {
                return None;
            }
            return Some(if *n == self.seed { "Test.initial" } else { "(Test.pure False)" }.into());
        }
        if variable(b, false) == Some(self.frontier) {
            return self.equality(b, a, observation);
        }
        // This small lowering keeps the equality-sensitive set consumer explicit
        // in the formal Test rather than interpreting it as an independent leaf.
        if let ExprKind::Builtin { op: B::Cardinality, args } = &*a.kind {
            let [set] = args.as_slice() else { return None };
            let ExprKind::SetEnum(es) = &*set.kind else { return None };
            let [x, y] = es.as_slice() else { return None };
            let literal = if variable(x, false) == Some(self.frontier) {
                y
            } else if variable(y, false) == Some(self.frontier) {
                x
            } else {
                return None;
            };
            if !matches!(&*literal.kind, ExprKind::Num(n) if *n==self.seed) {
                return None;
            }
            let ExprKind::Num(size) = &*b.kind else { return None };
            if *size < 0 {
                return None;
            }
            return Some(format!("(Test.pairCardinalityEq {size})"));
        }
        if matches!(&*b.kind, ExprKind::Builtin { op: B::Cardinality, .. }) {
            return self.equality(b, a, observation);
        }
        None
    }

    fn comparison(&self, op: B, a: &Expr, b: &Expr) -> Option<String> {
        if variable(a, false) != Some(self.frontier) && variable(b, false) == Some(self.frontier) {
            let reverse = match op {
                B::Lt => B::Gt,
                B::Le => B::Ge,
                B::Gt => B::Lt,
                B::Ge => B::Le,
                _ => return None,
            };
            return self.comparison(reverse, b, a);
        }
        if variable(a, false) != Some(self.frontier) {
            return None;
        }
        let ExprKind::Num(n) = &*b.kind else { return None };
        if *n > self.seed {
            return None;
        }
        Some(
            match op {
                B::Lt => "(Test.pure False)",
                B::Le if *n == self.seed => "Test.initial",
                B::Le => "(Test.pure False)",
                B::Gt if *n == self.seed => "(Test.neg Test.initial)",
                B::Gt | B::Ge => "(Test.pure True)",
                _ => return None,
            }
            .into(),
        )
    }
}

fn fold(tests: Vec<String>, op: &str, identity: &str) -> String {
    tests.into_iter().rev().fold(format!("(Test.pure {identity})"), |tail, head| format!("(Test.{op} {head} {tail})"))
}
