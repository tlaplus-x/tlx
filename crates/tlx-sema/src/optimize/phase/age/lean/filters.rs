//! Finite filters and quantified deadline observations. Filter predicates stay
//! explicit in Lean; only consumers of their exact selected sets are leaves.
use super::{fold, Emitter};
use crate::{hir::*, visit};

struct Filter {
    local: LocalId,
    keys: Vec<super::Atom>,
    predicates: Vec<String>,
}

impl Emitter<'_, '_> {
    fn finite_predicates(&mut self, bound: &Bound, pred: &Expr, observation: bool) -> Option<(Vec<super::Atom>, Vec<String>)> {
        let BoundVars::Many(ids) = &bound.vars else { return None };
        let [local] = ids.as_slice() else { return None };
        let keys: Vec<_> = self.proof.domains.exact_set(&bound.set)?.into_iter().collect();
        if keys.len() > 256 {
            return None;
        }
        let mut predicates = Vec::new();
        for key in &keys {
            self.scope.push((*local, key.clone()));
            let predicate = self.test(pred, observation);
            self.scope.pop();
            let predicate = predicate?;
            self.remaining = self.remaining.checked_sub(predicate.len())?;
            predicates.push(predicate);
        }
        Some((keys, predicates))
    }

    pub(super) fn quantified(&mut self, e: &Expr, observation: bool) -> Option<String> {
        let ExprKind::Quant { kind, bounds, body } = &*e.kind else { return None };
        let [bound] = bounds.as_slice() else { return None };
        let (_, tests) = self.finite_predicates(bound, body, observation)?;
        let universal = matches!(kind, QuantKind::Forall);
        Some(fold(tests, if universal { "conj" } else { "disj" }, if universal { "True" } else { "False" }))
    }

    pub(super) fn filtered_consumer(&mut self, e: &Expr, observation: bool) -> Option<String> {
        // No hole is introduced under a binder. Above all referenced locals
        // (including enumerated scopes), these IDs cannot capture source uses.
        fn max_local(e: &Expr, max: &mut u32) {
            if let ExprKind::Local(l) = &*e.kind {
                *max = (*max).max(l.0);
            }
            visit::children(e, &mut |child| max_local(child, max));
        }
        let mut local = self.scope.iter().map(|(l, _)| l.0).max().unwrap_or(0);
        max_local(e, &mut local);
        let mut next_local = local.checked_add(1)?;
        let mut filters = vec![];
        let masked = self.mask_filters(e, observation, &mut next_local, &mut filters)?;
        if filters.is_empty() || !self.independent(&masked) {
            return None;
        }
        let id = self.atoms.len();
        let mut description = format!("Filtered consumer HIR: {masked:#?}\nBound atoms: {:?}\n", self.scope);
        for (i, filter) in filters.iter().enumerate() {
            use std::fmt::Write;
            writeln!(description, "Hole {:?} = source atoms {:?} at selected positions in argument {i}.", filter.local, filter.keys)
                .unwrap();
        }
        self.atoms.push(description);
        let args = (0..filters.len()).map(|i| format!("selected{i}")).collect::<Vec<_>>().join(", ");
        let mut test = if observation {
            format!("(Test.pure (sem.filterObserve {id} c p [{args}]))")
        } else {
            format!("(Test.pure (sem.filterTest {id} c d p choice.2 [{args}]))")
        };
        for (i, filter) in filters.into_iter().enumerate().rev() {
            let keys = (0..filter.keys.len()).map(|k| k.to_string()).collect::<Vec<_>>().join(", ");
            let mut predicate = "fun index : Nat => match index with".to_owned();
            for (k, p) in filter.predicates.iter().enumerate() {
                predicate.push_str(&format!(" | {k} => {p}"));
            }
            predicate.push_str(" | _ => Test.pure False");
            self.remaining = self.remaining.checked_sub(test.len() + predicate.len())?;
            test = format!("(Test.select [{keys}] ({predicate}) (fun selected{i} => {test}))");
        }
        Some(test)
    }

    fn mask_filters(&mut self, e: &Expr, observation: bool, next_local: &mut u32, filters: &mut Vec<Filter>) -> Option<Expr> {
        self.remaining = self.remaining.checked_sub(1)?;
        if self.independent(e) {
            return Some(e.clone());
        }
        match &*e.kind {
            ExprKind::SetFilter { bound, pred } => {
                let (keys, predicates) = self.finite_predicates(bound, pred, observation)?;
                if filters.iter().map(|f| f.keys.len()).sum::<usize>() + keys.len() > 256 {
                    return None;
                }
                let local = LocalId(*next_local);
                *next_local = next_local.checked_add(1)?;
                filters.push(Filter { local, keys, predicates });
                Some(Expr::new(ExprKind::Local(local), e.span))
            }
            // Enumerated filters own their predicate binders. Other dependent
            // binders need separate lowering; do not pretend they are free W.
            ExprKind::Quant { .. }
            | ExprKind::QuantUnbounded { .. }
            | ExprKind::FnConstruct { .. }
            | ExprKind::SetMap { .. }
            | ExprKind::Choose { .. }
            | ExprKind::Lambda { .. }
            | ExprKind::TemporalQuant { .. } => None,
            _ => {
                let mut result = e.clone();
                let mut valid = true;
                visit::children_mut(&mut result, &mut |child| {
                    if let Some(masked) = self.mask_filters(child, observation, next_local, filters) {
                        *child = masked;
                    } else {
                        valid = false;
                    }
                });
                (valid && self.independent(&result)).then_some(result)
            }
        }
    }
}
