//! Lift quotient-observable values into the shared, proved decision tree.
//! Each branch substitutes a literal result into its original expression.
use super::Emitter;
use crate::{builtins::Builtin as B, hir::*, visit};

impl Emitter<'_, '_> {
    pub(super) fn split_decision(&mut self, e: &Expr) -> Option<(String, Expr, Expr)> {
        self.remaining = self.remaining.checked_sub(1)?;
        if self.independent(e) {
            return None;
        }
        if let ExprKind::If { cond, then, els } = &*e.kind {
            if !self.independent(cond) {
                return Some((self.test(cond, false)?, then.clone(), els.clone()));
            }
        }
        let boolean = matches!(
            &*e.kind,
            ExprKind::Builtin { op: B::Eq | B::Neq | B::Lt | B::Le | B::Gt | B::Ge | B::In, .. } | ExprKind::Quant { .. }
        );
        if boolean {
            if let Some(test) = self.test(e, false) {
                return Some((test, Expr::new(ExprKind::Bool(true), e.span), Expr::new(ExprKind::Bool(false), e.span)));
            }
        }
        // Never move a dependent predicate out of its binding environment or
        // interpret a next-state expression as a current-state observation.
        if matches!(
            &*e.kind,
            ExprKind::Quant { .. }
                | ExprKind::QuantUnbounded { .. }
                | ExprKind::FnConstruct { .. }
                | ExprKind::SetFilter { .. }
                | ExprKind::SetMap { .. }
                | ExprKind::Choose { .. }
                | ExprKind::Lambda { .. }
                | ExprKind::TemporalQuant { .. }
                | ExprKind::Builtin { op: B::Prime, .. }
        ) {
            return None;
        }
        let mut split = None;
        let mut index = 0;
        visit::children(e, &mut |child| {
            if split.is_none() {
                split = self.split_decision(child).map(|decision| (index, decision));
            }
            index += 1;
        });
        let (selected, (test, yes, no)) = split?;
        let replace = |value: Expr| {
            let mut result = e.clone();
            let mut index = 0;
            visit::children_mut(&mut result, &mut |child| {
                if index == selected {
                    *child = value.clone();
                }
                index += 1;
            });
            result
        };
        Some((test, replace(yes), replace(no)))
    }
}
