//! Numeric decisions stay explicit; pure leaves see only retained paths.
use super::{schema::Schema, Atom, Emitter, Mode};
use crate::{builtins::Builtin as B, hir::*, visit};

impl Mode {
    fn ty(self) -> &'static str {
        if matches!(self, Self::Transfer(_)) {
            "Test"
        } else {
            "FamilyTest"
        }
    }
}
impl Emitter<'_, '_> {
    pub(super) fn tests(&mut self, es: &[Expr], mode: Mode) -> Option<String> {
        let ty = mode.ty();
        let mut out = format!("({ty}.pure True)");
        for e in es {
            out = bounded(format!("({ty}.conj {out} {})", self.test(e, mode)?))?;
        }
        Some(out)
    }
    pub(super) fn action_tests(&mut self, es: &[Expr]) -> Option<String> {
        let mut out = "(True)".to_owned();
        for e in es {
            let test = self.action_test(e)?;
            out = format!("({out} ∧ {test})");
        }
        Some(out)
    }

    /// Lower an action check over the retained core state. Any read of a
    /// projected allocation or live-version value is refused.
    pub(super) fn action_test(&mut self, e: &Expr) -> Option<String> {
        if !self.independent(e) {
            return None;
        }
        let i = self.atoms.len();
        self.atoms.push(format!("Action-level HIR: {e:#?}; only retained leaf values"));
        Some(format!("(sem.actionTest {i} c d)"))
    }

    fn test(&mut self, e: &Expr, mode: Mode) -> Option<String> {
        let out = self.test_inner(e, mode)?;
        bounded(out)
    }
    fn test_inner(&mut self, e: &Expr, mode: Mode) -> Option<String> {
        let ty = mode.ty();
        if let ExprKind::Builtin { op: B::In, args } = &*e.kind {
            if let [a, b] = args.as_slice() {
                if let ExprKind::Var(v) = &*a.kind {
                    if self.context.domains.belongs(&self.context.domains.vars[v.idx()], b) {
                        return Some(format!("({ty}.pure True)"));
                    }
                }
                if let Some((f, r)) = self.reference(a) {
                    if matches!(&*b.kind,ExprKind::Builtin{op:B::Int,args} if args.is_empty()) {
                        return Some(format!("({ty}.pure True)"));
                    }
                    if matches!(&*b.kind,ExprKind::Builtin{op:B::Nat,args} if args.is_empty()) {
                        let zero = self.anchor(f, 0)?;
                        return self.le(f, &zero, &r, mode);
                    }
                }
            }
        }
        if let Some(lowered) = self.history_reads(e, mode) {
            if self.independent(&lowered) {
                return Some(self.leaf(&lowered, mode));
            }
        }
        match &*e.kind {
            ExprKind::And(es) => return self.tests(es, mode),
            ExprKind::Or(es) => {
                let mut out = format!("({ty}.pure False)");
                for e in es {
                    out = bounded(format!("({ty}.disj {out} {})", self.test(e, mode)?))?;
                }
                return Some(out);
            }
            ExprKind::Builtin { op, args } => match (op, args.as_slice()) {
                (B::Not, [e]) => return Some(format!("({ty}.neg {})", self.test(e, mode)?)),
                (B::Implies, [p, q]) => return Some(format!("({ty}.disj ({ty}.neg {}) {})", self.test(p, mode)?, self.test(q, mode)?)),
                (B::Eq | B::Neq | B::Le | B::Lt | B::Ge | B::Gt, [a, b]) => {
                    if let Some((f, left, right)) = self.comparison(a, b) {
                        let le = self.le(f, &left, &right, mode)?;
                        let ge = self.le(f, &right, &left, mode)?;
                        return Some(match op {
                            B::Eq => format!("({ty}.conj {le} {ge})"),
                            B::Neq => format!("({ty}.neg ({ty}.conj {le} {ge}))"),
                            B::Le => le,
                            B::Ge => ge,
                            B::Lt => format!("({ty}.neg {ge})"),
                            B::Gt => format!("({ty}.neg {le})"),
                            _ => unreachable!(),
                        });
                    }
                }
                _ => {}
            },
            ExprKind::Quant { kind, bounds, body } => {
                let cases = self.context.expand(&[super::Branch { bounds: bounds.clone(), terms: vec![body.clone()] }])?;
                let op = if *kind == QuantKind::Forall { "conj" } else { "disj" };
                let mut out = format!("({ty}.pure {})", if *kind == QuantKind::Forall { "True" } else { "False" });
                for b in cases {
                    out = bounded(format!("({ty}.{op} {out} {})", self.test(&b.terms[0], mode)?))?;
                }
                return Some(out);
            }
            _ => {}
        }
        let (condition, yes, no) = split_decision(e)?;
        let condition = self.test(&condition, mode)?;
        Some(format!(
            "({ty}.disj ({ty}.conj {condition} {}) ({ty}.conj ({ty}.neg {condition}) {}))",
            self.test(&yes, mode)?,
            self.test(&no, mode)?
        ))
    }
    fn le(&self, f: usize, a: &str, b: &str, mode: Mode) -> Option<String> {
        Some(match mode {
            Mode::Transfer(g) if f == g => format!("(Test.le {a} {b})"),
            Mode::Transfer(_) => return None,
            _ => format!("(FamilyTest.le ⟨{f}, by decide +revert⟩ {a} {b})"),
        })
    }
    fn comparison(&mut self, a: &Expr, b: &Expr) -> Option<(usize, String, String)> {
        let ar = self.reference(a);
        let br = self.reference(b);
        match (ar, br) {
            (Some((f, a)), Some((g, b))) if f == g => Some((f, a, b)),
            (Some((f, a)), None) => {
                let Atom::Num(n) = self.context.atom(b)? else { return None };
                Some((f, a, self.anchor(f, n)?))
            }
            (None, Some((f, b))) => {
                let Atom::Num(n) = self.context.atom(a)? else { return None };
                Some((f, self.anchor(f, n)?, b))
            }
            _ => None,
        }
    }
    pub(super) fn reference(&self, e: &Expr) -> Option<(usize, String)> {
        let path = self.context.path(e)?;
        if path.keys.is_empty() {
            if let Some(f) = self.families.iter().position(|f| f.variable == path.var) {
                return Some((f, "Reference.frontier".into()));
            }
        }
        let slot = self.slots.iter().find(|s| s.path == path)?;
        Some((slot.family, format!("(Reference.slot ⟨{}, by decide +revert⟩)", slot.index)))
    }
    pub(super) fn anchor(&mut self, f: usize, n: i128) -> Option<String> {
        if n > self.families[f].initial || (n > 0 && !self.plan.anchors[f].contains(&n)) {
            return None;
        }
        let i = if let Some(i) = self.anchors[f].iter().position(|a| *a == n) {
            i
        } else {
            self.anchors[f].push(n);
            self.anchors[f].len() - 1
        };
        Some(format!("(Reference.anchor ⟨{i}, by decide +revert⟩)"))
    }
    pub(super) fn independent(&self, e: &Expr) -> bool {
        if let Some(path) = self.context.path(e) {
            return matches!(self.context.at_path(&path), Some(Schema::Plain));
        }
        let mut valid = true;
        visit::children(e, &mut |e| valid &= self.independent(e));
        valid
    }
    fn leaf(&mut self, e: &Expr, mode: Mode) -> String {
        let i = self.atoms.len();
        self.atoms.push(format!("Retained-state HIR: {e:#?}; numeric/container paths are excluded from this leaf"));
        let value = match mode {
            Mode::Initial => format!("sem.initial {i} c choice.2"),
            Mode::Observe => format!("sem.observe {i} c"),
            Mode::Step | Mode::Transfer(_) => format!("sem.test {i} c d choice.2"),
        };
        let reads = if self.plan.history.is_some() && !matches!(mode, Mode::Initial) { " reads" } else { "" };
        format!("({}.pure ({value}{reads}))", mode.ty())
    }
    pub(super) fn transfer(&mut self, e: &Expr, f: usize, delta: i128) -> Option<String> {
        if let ExprKind::If { cond, then, els } = &*e.kind {
            let out = format!(
                "(Transfer.branch {} {} {})",
                self.test(cond, Mode::Transfer(f))?,
                self.transfer(then, f, delta)?,
                self.transfer(els, f, delta)?
            );
            return bounded(out);
        }
        let value = if let Some((g, r)) = self.reference(e) {
            if f != g {
                return None;
            }
            format!("(Token.old {r})")
        } else if let Some(Atom::Num(n)) = self.context.atom(e) {
            format!("(Token.old {})", self.anchor(f, n)?)
        } else {
            let offset = super::syntax::increment(e, self.families[f].variable)?;
            let Atom::Num(n) = self.context.atom(&offset)? else { return None };
            if n < 0 || n > delta {
                return None;
            }
            // Output specializes this branch's delta before elaborating Fin.
            format!("(Token.fresh ⟨{n}, by decide +revert⟩)")
        };
        Some(format!("(Transfer.value {value})"))
    }
}

// Lift a value conditional or a nested Boolean consumer without crossing binders.
fn split_decision(e: &Expr) -> Option<(Expr, Expr, Expr)> {
    if let ExprKind::If { cond, then, els } = &*e.kind {
        return Some((cond.clone(), then.clone(), els.clone()));
    }
    if matches!(
        &*e.kind,
        ExprKind::Quant { .. }
            | ExprKind::FnConstruct { .. }
            | ExprKind::SetMap { .. }
            | ExprKind::SetFilter { .. }
            | ExprKind::Choose { .. }
            | ExprKind::Lambda { .. }
            | ExprKind::Builtin { op: B::Prime, .. }
    ) {
        return None;
    }
    let mut found = None;
    let mut index = 0;
    visit::children(e, &mut |child| {
        if found.is_none() {
            let decision = if matches!(&*child.kind,ExprKind::Builtin{op:B::Eq|B::Neq|B::Le|B::Lt|B::Ge|B::Gt,args} if args.len()==2) {
                Some((child.clone(), Expr::new(ExprKind::Bool(true), child.span), Expr::new(ExprKind::Bool(false), child.span)))
            } else {
                split_decision(child)
            };
            if let Some((p, y, n)) = decision {
                found = Some((index, p, y, n));
            }
        }
        index += 1;
    });
    let (target, p, y, n) = found?;
    let replace = |value: Expr| {
        let mut out = e.clone();
        let mut i = 0;
        visit::children_mut(&mut out, &mut |e| {
            if i == target {
                *e = value.clone();
            }
            i += 1;
        });
        out
    };
    Some((p, replace(y), replace(n)))
}
fn bounded(s: String) -> Option<String> {
    (s.len() <= 1_000_000).then_some(s)
}
