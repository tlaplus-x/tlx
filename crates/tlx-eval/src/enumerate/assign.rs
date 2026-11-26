//! The assignment-shaped built-ins of the next-state relation: `x' = e`,
//! `x' \in S` and `x' \subseteq S` on a target variable that is not
//! assigned yet; every other use of them is a plain test (moved out of
//! `enumerate.rs`).

use tlx_value::ops;

use super::*;

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

    /// Stream `set` element by element into `self.assign`, propagating the
    /// first error and stopping as soon as the continuation asks to stop.
    fn assign_stream(&mut self, v: VarId, set: &Value, k: &Cont) -> EResult<bool> {
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
