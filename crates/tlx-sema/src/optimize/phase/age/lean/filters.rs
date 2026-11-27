//! Finite filters and quantified deadline observations. Filter predicates stay
//! explicit in Lean; only consumers of their exact selected sets are leaves.
use super::super::super::max_local;
use super::{fold, Emitter};
use crate::{builtins::Builtin as B, hir::*, visit};

struct Filter {
    local: LocalId,
    keys: Vec<super::Atom>,
    predicates: Vec<String>,
}

#[derive(Default)]
struct Inputs {
    filters: Vec<Filter>,
    predicates: Vec<(LocalId, String)>,
}

impl Emitter<'_, '_> {
    fn finite_predicates(
        &mut self,
        bound: &Bound,
        pred: &Expr,
        observation: bool,
        universal: bool,
    ) -> Option<(Vec<super::Atom>, Vec<String>)> {
        let BoundVars::Many(ids) = &bound.vars else { return None };
        let [local] = ids.as_slice() else { return None };
        let exact = self.proof.domains.exact_set(&bound.set);
        let keys: Vec<_> = if let Some(keys) = &exact {
            keys.iter().cloned().collect()
        } else {
            let locals = self.scope.iter().map(|(id, atom)| (*id, super::Domain::Atoms([atom.clone()].into()))).collect();
            let super::Domain::Set(elements) = self.proof.domains.value(&bound.set, &locals) else { return None };
            if matches!(*elements, super::Domain::Bottom) {
                Vec::new()
            } else {
                elements.atoms()?.iter().cloned().collect()
            }
        };
        if keys.len() > 256 {
            return None;
        }
        let mut predicates = Vec::new();
        for key in &keys {
            self.scope.push((*local, key.clone()));
            let predicate = if exact.is_some() {
                self.test(pred, observation)
            } else {
                let member = super::builtin(B::In, vec![Expr::new(ExprKind::Local(*local), pred.span), bound.set.clone()], pred);
                let guarded = if universal {
                    super::builtin(B::Implies, vec![member, pred.clone()], pred)
                } else {
                    Expr::new(ExprKind::And(vec![member, pred.clone()]), pred.span)
                };
                self.test(&guarded, observation)
            };
            self.scope.pop();
            let predicate = predicate?;
            self.remaining = self.remaining.checked_sub(predicate.len())?;
            predicates.push(predicate);
        }
        Some((keys, predicates))
    }

    pub(super) fn quantified(&mut self, e: &Expr, observation: bool) -> Option<String> {
        let ExprKind::Quant { kind, bounds, body } = &*e.kind else { return None };
        let Some((bound, rest)) = bounds.split_first() else { return self.test(body, observation) };
        let BoundVars::Many(ids) = &bound.vars else { return None };
        let (first, others) = ids.split_first()?;
        let mut bound = bound.clone();
        bound.vars = BoundVars::Many(vec![*first]);
        let mut remaining = Vec::new();
        if !others.is_empty() {
            let mut next = bound.clone();
            next.vars = BoundVars::Many(others.to_vec());
            remaining.push(next);
        }
        remaining.extend_from_slice(rest);
        let body = if remaining.is_empty() {
            body.clone()
        } else {
            Expr::new(ExprKind::Quant { kind: *kind, bounds: remaining, body: body.clone() }, e.span)
        };
        let universal = matches!(kind, QuantKind::Forall);
        let (_, tests) = self.finite_predicates(&bound, &body, observation, universal)?;
        Some(fold(tests, if universal { "conj" } else { "disj" }, if universal { "True" } else { "False" }))
    }

    pub(super) fn filtered_consumer(&mut self, e: &Expr, observation: bool) -> Option<String> {
        // No hole is introduced under a binder. Above all referenced and
        // declared locals (including enumerated scopes), these IDs cannot
        // capture source uses.
        let mut local = self.scope.iter().map(|(l, _)| l.0).max().unwrap_or(0);
        local = local.max(max_local(e));
        let mut next_local = local.checked_add(1)?;
        let mut inputs = Inputs::default();
        let masked = self.mask_filters(e, observation, &mut next_local, &mut inputs)?;
        if (inputs.filters.is_empty() && inputs.predicates.is_empty()) || !self.independent(&masked) {
            return None;
        }
        let id = self.atoms.len();
        let mut description = format!("Filtered consumer HIR: {masked:#?}\nBound atoms: {:?}\n", self.scope);
        for (i, filter) in inputs.filters.iter().enumerate() {
            use std::fmt::Write;
            writeln!(description, "Hole {:?} = source atoms {:?} at selected positions in argument {i}.", filter.local, filter.keys)
                .unwrap();
        }
        for (i, (local, predicate)) in inputs.predicates.iter().enumerate() {
            use std::fmt::Write;
            writeln!(description, "Boolean hole {local:?} = {predicate} in predicate argument {i}.").unwrap();
        }
        self.atoms.push(description);
        let args = (0..inputs.filters.len()).map(|i| format!("selected{i}")).collect::<Vec<_>>().join(", ");
        let bits = (0..inputs.predicates.len()).map(|i| format!("decision{i}")).collect::<Vec<_>>().join(", ");
        let mut test = if observation {
            format!("(Test.pure (sem.filterObserve {id} c p [{args}] [{bits}]))")
        } else {
            format!("(Test.pure (sem.filterTest {id} c d p choice.2 [{args}] [{bits}]))")
        };
        for (i, (_, predicate)) in inputs.predicates.into_iter().enumerate().rev() {
            self.remaining = self.remaining.checked_sub(test.len() + predicate.len())?;
            test = format!("(Test.bind {predicate} (fun decision{i} => {test}))");
        }
        for (i, filter) in inputs.filters.into_iter().enumerate().rev() {
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

    fn mask_filters(&mut self, e: &Expr, observation: bool, next_local: &mut u32, inputs: &mut Inputs) -> Option<Expr> {
        self.remaining = self.remaining.checked_sub(1)?;
        if self.independent(e) {
            return Some(e.clone());
        }
        // Only recognized summary predicates can become Boolean holes. An
        // arbitrary history-dependent expression might be a set or a value.
        if self.age_independent(e) {
            if let Some(history) = &mut self.history {
                if let Some(predicate) = history.summary_read(e) {
                    if inputs.predicates.len() >= 256 {
                        return None;
                    }
                    let local = LocalId(*next_local);
                    *next_local = next_local.checked_add(1)?;
                    inputs.predicates.push((local, format!("(Test.pure (let sem := sem.history; {predicate}))")));
                    return Some(Expr::new(ExprKind::Local(local), e.span));
                }
            }
        }
        if let ExprKind::Builtin { op: B::Eq | B::Neq | B::Lt | B::Le | B::Gt | B::Ge, args } = &*e.kind {
            if let [a, b] = args.as_slice() {
                let ExprKind::Builtin { op, .. } = &*e.kind else { unreachable!() };
                if let Some(predicate) = self.comparison(*op, a, b, observation) {
                    if inputs.predicates.len() >= 256 {
                        return None;
                    }
                    let local = LocalId(*next_local);
                    *next_local = next_local.checked_add(1)?;
                    inputs.predicates.push((local, predicate));
                    return Some(Expr::new(ExprKind::Local(local), e.span));
                }
            }
        }
        match &*e.kind {
            ExprKind::SetFilter { bound, pred } => {
                let (keys, predicates) = self.finite_predicates(bound, pred, observation, false)?;
                if inputs.filters.iter().map(|f| f.keys.len()).sum::<usize>() + keys.len() > 256 {
                    return None;
                }
                let local = LocalId(*next_local);
                *next_local = next_local.checked_add(1)?;
                inputs.filters.push(Filter { local, keys, predicates });
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
            | ExprKind::TemporalQuant { .. }
            // Test.select inspects current stamps, not next-state stamps.
            | ExprKind::Builtin { op: B::Prime, .. } => None,
            _ => {
                let mut result = e.clone();
                let mut valid = true;
                visit::children_mut(&mut result, &mut |child| {
                    if let Some(masked) = self.mask_filters(child, observation, next_local, inputs) {
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
