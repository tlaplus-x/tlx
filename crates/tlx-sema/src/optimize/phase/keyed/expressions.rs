//! Explicit equality/quantifier IR and payload-only semantic leaves.
use super::super::{max_local, variable};
use super::{independent, Emitter, Locals};
use crate::{builtins::Builtin as B, hir::*, visit};

impl Emitter<'_> {
    pub(super) fn tests(&mut self, es: &[Expr], keys: &[LocalId]) -> Option<String> {
        let mut out = "(Test.truth true)".to_owned();
        for e in es {
            out = bounded(format!("(Test.conj {out} {})", self.test(e, keys)?))?;
        }
        Some(out)
    }

    fn test(&mut self, e: &Expr, keys: &[LocalId]) -> Option<String> {
        let result = self.test_inner(e, keys)?;
        bounded(result)
    }

    fn test_inner(&mut self, e: &Expr, keys: &[LocalId]) -> Option<String> {
        match &*e.kind {
            ExprKind::And(es) => return self.tests(es, keys),
            ExprKind::Or(es) if !es.is_empty() => {
                let mut terms = es.iter().map(|e| self.test(e, keys));
                let mut out = terms.next()??;
                for t in terms {
                    out = bounded(format!("(Test.disj {out} {})", t?))?;
                }
                return Some(out);
            }
            ExprKind::Builtin { op, args } => match (op, args.as_slice()) {
                (B::Eq | B::Neq, [a, b]) => {
                    if let (ExprKind::Local(a), ExprKind::Local(b)) = (&*a.kind, &*b.kind) {
                        if let (Some(a), Some(b)) = (keys.iter().position(|k| k == a), keys.iter().position(|k| k == b)) {
                            let eq = format!("(Test.equal {a} {b})");
                            return Some(if *op == B::Eq { eq } else { format!("(Test.neg {eq})") });
                        }
                    }
                }
                (B::Not, [a]) => return Some(format!("(Test.neg {})", self.test(a, keys)?)),
                (B::Implies, [a, b]) => return Some(format!("(Test.disj (Test.neg {}) {})", self.test(a, keys)?, self.test(b, keys)?)),
                _ => {}
            },
            ExprKind::Quant { kind, bounds, body } if bounds.iter().all(|b| self.domains.exact_set(&b.set).as_ref() == Some(self.keys)) => {
                let mut scope = keys.to_vec();
                let mut count = 0;
                for bound in bounds {
                    let BoundVars::Many(ids) = &bound.vars else { return None };
                    for id in ids {
                        scope.insert(0, *id);
                        count += 1;
                    }
                }
                let mut out = self.test(body, &scope)?;
                let quant = match kind {
                    QuantKind::Forall => "all",
                    QuantKind::Exists => "some",
                };
                for _ in 0..count {
                    out = format!("(Test.{quant} {out})");
                }
                return Some(out);
            }
            ExprKind::If { cond, then, els } => {
                let condition = self.test(cond, keys)?;
                return Some(format!(
                    "(Test.disj (Test.conj {condition} {}) (Test.conj (Test.neg {condition}) {}))",
                    self.test(then, keys)?,
                    self.test(els, keys)?
                ));
            }
            _ => {}
        }
        self.leaf(e, keys, "Test")
    }

    pub(super) fn value(&mut self, e: &Expr, keys: &[LocalId]) -> Option<String> {
        let result = self.value_inner(e, keys)?;
        bounded(result)
    }

    fn value_inner(&mut self, e: &Expr, keys: &[LocalId]) -> Option<String> {
        if let ExprKind::If { cond, then, els } = &*e.kind {
            return Some(format!("(ValueExpr.branch {} {} {})", self.test(cond, keys)?, self.value(then, keys)?, self.value(els, keys)?));
        }
        self.leaf(e, keys, "ValueExpr")
    }

    fn leaf(&mut self, e: &Expr, keys: &[LocalId], kind: &str) -> Option<String> {
        let mut next = max_local(e).checked_add(1)?;
        let mut reads = vec![];
        let mut holes = vec![];
        let masked = self.mask(e, keys, &mut next, &mut reads, &mut holes)?;
        let id = self.atoms.len();
        self.atoms.push(format!("{kind} HIR: {masked:#?}\nPayload holes: {holes:?}"));
        Some(format!("({kind}.leaf {id} [{}])", reads.join(", ")))
    }

    fn mask(&self, e: &Expr, keys: &[LocalId], next: &mut u32, reads: &mut Vec<String>, holes: &mut Vec<LocalId>) -> Option<Expr> {
        if let ExprKind::Builtin { op: B::In, args } = &*e.kind {
            if let [value, set] = args.as_slice() {
                if let Some(v) = variable(value, false).filter(|v| self.maps.contains(v)) {
                    if self.domains.belongs(&self.domains.vars[v.idx()], set) {
                        return Some(Expr::new(ExprKind::Bool(true), e.span));
                    }
                }
            }
        }
        if let ExprKind::FnApp { func, args } = &*e.kind {
            if let Some(slot) = variable(func, false).and_then(|v| self.maps.iter().position(|m| *m == v)) {
                let [arg] = args.as_slice() else { return None };
                let ExprKind::Local(id) = &*arg.kind else { return None };
                let key = keys.iter().position(|k| k == id)?;
                let hole = LocalId(*next);
                *next = next.checked_add(1)?;
                reads.push(format!("(⟨{slot}, by decide⟩, {key})"));
                holes.push(hole);
                return Some(Expr::new(ExprKind::Local(hole), e.span));
            }
        }
        match &*e.kind {
            ExprKind::Var(v) if self.maps.contains(v) => return None,
            ExprKind::Local(id) if keys.contains(id) => return None,
            ExprKind::Const(_) if !independent(&self.domains.value(e, &Locals::new()), self.keys) => return None,
            ExprKind::Builtin { op: B::Prime, .. } if mentions_map(e, &self.maps) => return None,
            // Never move a binder-dependent read outside its scope.
            ExprKind::Quant { .. }
            | ExprKind::Choose { .. }
            | ExprKind::FnConstruct { .. }
            | ExprKind::SetFilter { .. }
            | ExprKind::SetMap { .. }
                if mentions_map(e, &self.maps) =>
            {
                return None
            }
            _ => {}
        }
        let mut masked = e.clone();
        let mut valid = true;
        visit::children_mut(&mut masked, &mut |child| {
            if let Some(e) = self.mask(child, keys, next, reads, holes) {
                *child = e;
            } else {
                valid = false;
            }
        });
        valid.then_some(masked)
    }
}
fn mentions_map(e: &Expr, maps: &[VarId]) -> bool {
    if matches!(&*e.kind,ExprKind::Var(v) if maps.contains(v)) {
        return true;
    }
    let mut found = false;
    visit::children(e, &mut |e| found |= mentions_map(e, maps));
    found
}

// Boolean IF expansion duplicates its condition. Bound each intermediate term
// so deeply nested conditions cannot expand an otherwise small HIR exponentially.
fn bounded(term: String) -> Option<String> {
    (term.len() <= 1_000_000).then_some(term)
}
