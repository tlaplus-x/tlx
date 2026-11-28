//! The assignment-shaped built-ins of the next-state relation: `x' = e`,
//! `x' \in S` and `x' \subseteq S` on a target variable that is not
//! assigned yet; every other use of them is a plain test (moved out of
//! `enumerate.rs`).

use tlx_value::{ops, LazySet};

use crate::subsetfilter::{self, ActionConstraint};

use super::*;

struct ActionSubsetVisitor<'a, 'b, 'c> {
    en: &'b mut Enumerator<'a>,
    var: VarId,
    guards: &'b [(ActionConstraint, &'c Env)],
    conts_after: &'b [Cont<'c>],
    orig_k: &'b Cont<'c>,
    err: Option<EvalError>,
}

impl ops::SubsetVisitor for ActionSubsetVisitor<'_, '_, '_> {
    fn elem(&mut self, v: Value) -> tlx_value::Result<bool> {
        match self.en.assign(self.var, v, self.orig_k) {
            Ok(go_on) => Ok(go_on),
            Err(e) => {
                self.err = Some(e);
                Ok(false)
            }
        }
    }

    fn subsets(&mut self, base: &ops::SubsetBase<'_>) -> tlx_value::Result<Option<bool>> {
        let narrow = {
            let cx = self.en.cx();
            subsetfilter::narrow_action_guards(self.en.ip, &cx, base, self.guards)
        };
        let Some(narrow) = narrow else {
            return Ok(None);
        };
        if narrow.is_empty() {
            return Ok(Some(true));
        }
        let rem_k = if narrow.consumed == 0 { self.orig_k } else { &self.conts_after[narrow.consumed - 1] };
        let done =
            ops::for_each_constrained_subset(base, &narrow.required, &narrow.optional, narrow.min_card, narrow.max_card, &mut |subset| {
                match self.en.assign(self.var, subset, rem_k) {
                    Ok(go_on) => Ok(go_on),
                    Err(e) => {
                        self.err = Some(e);
                        Ok(false)
                    }
                }
            })?;
        Ok(Some(done))
    }
}

impl<'a> Enumerator<'a> {
    /// `x' = e`: evaluate `e` and assign it to the unassigned target.
    pub(super) fn assign_eq(&mut self, args: &[Expr], e: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        match self.unassigned_target(&args[0], env) {
            Some(v) => {
                let val = self.eval(&args[1], env)?;
                self.assign(v, val, k)
            }
            None => self.test(e, env, k),
        }
    }

    /// Push leading pure subset guards (e.g. `L \subseteq x'`, `e \in x'`)
    /// from `k` into next-state `SUBSET` assignment enumeration via
    /// `subsetfilter` and `ops::for_each_constrained_subset`.
    fn try_assign_constrained_subsets<'c>(&mut self, v: VarId, set: &Value, k: &Cont<'c>, depth: usize) -> EResult<Option<bool>> {
        if let Some((Item::Expr(e, env), rest)) = k.next() {
            if let ExprKind::And(es) = &*e.kind {
                if !es.is_empty() && depth < 8 {
                    let k2 = Cont::push(Seg::Conj(es, env), &rest);
                    return self.try_assign_constrained_subsets(v, set, &k2, depth + 1);
                }
            }
        }
        let mut guards: Vec<(ActionConstraint, &'c Env)> = Vec::new();
        let mut conts_after: Vec<Cont<'c>> = Vec::new();
        let mut cur = *k;
        while let Some((Item::Expr(e, env), next_k)) = cur.next() {
            if self.unassigned > 1 {
                if let ExprKind::Quant { kind: QuantKind::Forall, body, .. } = &*e.kind {
                    if !self.is_pure_test(body, env, 0) {
                        break;
                    }
                }
            }
            let Some(constraint) = subsetfilter::recognize_action_constraint(self.ip, e, v, &self.s1, env) else {
                break;
            };
            guards.push((constraint, env));
            conts_after.push(next_k);
            cur = next_k;
        }
        if guards.is_empty() {
            return Ok(None);
        }
        let mut visitor = ActionSubsetVisitor { en: self, var: v, guards: &guards, conts_after: &conts_after, orig_k: k, err: None };
        let done = ops::for_each_enumerated_subsets(set, &mut visitor)?;
        match visitor.err {
            Some(e) => Err(e),
            None => Ok(Some(done)),
        }
    }

    /// Stream `set` element by element into `self.assign`, propagating the
    /// first error and stopping as soon as the continuation asks to stop.
    fn assign_stream(&mut self, v: VarId, set: &Value, k: &Cont) -> EResult<bool> {
        if !self.init() && matches!(set, Value::LazySet(l) if matches!(**l, LazySet::Subset(_) | LazySet::Union(_))) {
            if let Some(done) = self.try_assign_constrained_subsets(v, set, k, 0)? {
                return Ok(done);
            }
        }
        let mut err = None;
        let done = ops::for_each_enumerated(set, &mut |x| match self.assign(v, x, k) {
            Ok(go_on) => Ok(go_on),
            Err(e) => {
                err = Some(e);
                Ok(false)
            }
        })?;
        match err {
            Some(e) => Err(e),
            None => Ok(done),
        }
    }

    /// `x' \in S`: assign each element of `S` to the unassigned
    /// target.
    pub(super) fn assign_in(&mut self, args: &[Expr], e: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        match self.unassigned_target(&args[0], env) {
            Some(v) if !self.random => {
                // The elements are assigned as they are enumerated (TLC:
                // `Enumerable.elements()`): a set filter over a set that is
                // not enumerated (`{c \in [a: S, b: T] : P}`) is never
                // materialized as a whole.
                let set = self.eval(&args[1], env)?;
                self.assign_stream(v, &set, k)
            }
            Some(v) => {
                let set = self.eval(&args[1], env)?;
                self.assign_each(v, ops::enumerate(&set)?, k)
            }
            None => self.test(e, env, k),
        }
    }

    /// `x' \subseteq S`: assign each subset of `S` to the unassigned
    /// target.
    pub(super) fn assign_subseteq(&mut self, args: &[Expr], e: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        match self.unassigned_target(&args[0], env) {
            Some(v) if !self.random => {
                // `SUBSET S` streams in TLC's normalized order
                // (`SubsetValue.elementsNormalized`): assign each subset as it
                // is generated without materializing all `2^|S|` subsets.
                let set = self.eval(&args[1], env)?;
                let ps = ops::powerset(&set)?;
                self.assign_stream(v, &ps, k)
            }
            Some(v) => {
                let set = self.eval(&args[1], env)?;
                let ps = ops::powerset(&set)?;
                self.assign_each(v, ops::enumerate_normalized(&ps)?, k)
            }
            None => self.test(e, env, k),
        }
    }
}
