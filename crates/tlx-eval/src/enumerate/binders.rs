//! The binders of the next-state relation: `\E`, `\A`, `IF/THEN/ELSE`,
//! `CASE`, `LET` and a lazily represented function applied (moved out of
//! `enumerate.rs`). An existential enumerates its body once per binding of
//! its variables; a universal is expanded into a conjunction over them.

use super::*;

use tlx_value::ops;

use crate::eval::BoundElems;

impl<'a> Enumerator<'a> {
    /// `\E x \in S : P`: enumerate `P` once per binding of `x`.
    pub(super) fn exists(&mut self, bounds: &[Bound], body: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        let ip: &'a Arc<Interp> = self.ip;
        // One variable over one set: its elements are evaluated
        // first, then the binding is updated in place
        // (`for_each_binding`'s common case).
        if let ([Bound { vars: BoundVars::Many(ls), set }], false) = (bounds, self.random) {
            if let [l] = ls.as_slice() {
                let mut elems = match ip.bound_elems(set, env, &self.cx())? {
                    BoundElems::Elems(elems) => elems,
                    // The domain cannot be materialized: stream it
                    // (`for_each_enumerated`; see `BoundElems`) and stop when
                    // the continuation does.
                    BoundElems::Stream(v) => {
                        let mut go_on = true;
                        let mut err = None;
                        ops::for_each_enumerated(&v, &mut |x| match self.go(body, &env.bind_val(*l, x), k) {
                            Ok(cont) => {
                                go_on = cont;
                                Ok(cont)
                            }
                            Err(e) => {
                                err = Some(e);
                                Ok(false)
                            }
                        })?;
                        return match err {
                            Some(e) => Err(e),
                            None => Ok(go_on),
                        };
                    }
                };
                let Some(first) = elems.next() else {
                    return Ok(true);
                };
                let mut env2 = env.bind_val(*l, first);
                loop {
                    if !self.go(body, &env2, k)? {
                        return Ok(false);
                    }
                    let Some(x) = elems.next() else {
                        return Ok(true);
                    };
                    if let Err(x) = env2.rebind_head(x) {
                        env2 = env.bind_val(*l, x);
                    }
                }
            }
        }
        // The body is enumerated while the bindings are: evaluate the
        // bounds over a snapshot of the target state.
        let s1 = self.s1.clone();
        let cache = self.cache.clone();
        let cx = ctx_over(self.s0, self.level, &s1, &cache);
        if self.random {
            let mut envs = Vec::new();
            ip.for_each_binding(bounds, env, &cx, &mut |env2| {
                envs.push(env2.clone());
                Ok(true)
            })?;
            return self.try_randomly(envs, |en, env2| en.go(body, &env2, k));
        }
        let mut go_on = true;
        ip.for_each_binding(bounds, env, &cx, &mut |env2| {
            go_on = self.go(body, env2, k)?;
            Ok(go_on)
        })?;
        Ok(go_on)
    }

    /// `\A x \in S : P`: expanded into a conjunction over the bindings.
    pub(super) fn forall(&mut self, bounds: &[Bound], body: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        let ip: &'a Arc<Interp> = self.ip;
        // Expanded into a conjunction over the elements.
        let mut envs = Vec::new();
        ip.for_each_binding(bounds, env, &self.cx(), &mut |env2| {
            envs.push(env2.clone());
            Ok(true)
        })?;
        let k2 = Cont::push(Seg::Forall(body, &envs), k);
        self.cont(&k2)
    }

    /// `IF c THEN t ELSE e`: enumerate the branch `c` picks.
    pub(super) fn conditional(&mut self, cond: &Expr, then: &Expr, els: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        if self.eval_bool(cond, env)? {
            self.go(then, env, k)
        } else {
            self.go(els, env, k)
        }
    }

    /// `CASE`: enumerate the value of the first arm whose guard holds.
    pub(super) fn case_expr(&mut self, arms: &[(Expr, Expr)], other: &Option<Expr>, env: &Env, k: &Cont) -> EResult<bool> {
        for (g, v) in arms {
            if self.eval_bool(g, env)? {
                return self.go(v, env, k);
            }
        }
        match other {
            Some(o) => self.go(o, env, k),
            None => Err(EvalError::new("Attempted to evaluate a CASE with no conditions true.")),
        }
    }

    /// `LET d IN e`: enumerate `e` in the extended environment.
    pub(super) fn let_expr(&mut self, defs: &[DefId], body: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        let (env2, _frame) = self.ip.let_env(defs, env);
        self.go(body, &env2, k)
    }

    /// `f[a]` for a lazily represented `f`: expand its body with its
    /// arguments bound.
    pub(super) fn fn_app(&mut self, func: &Expr, args: &[Expr], e: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        let ip: &'a Arc<Interp> = self.ip;
        // TLC expands the body of a lazily represented function
        // (FcnLambdaValue: `[x \in S |-> e]` or a recursive function
        // definition) applied in an action (Tool.java getNextStates).
        let Some((bounds, body, fenv)) = self.lambda_of(func, env) else {
            return self.test(e, env, k);
        };
        let arg = ip.eval_args(args, env, &self.cx())?;
        let env2 = ip.bind_fn_args(&bounds, &arg, &fenv)?;
        self.go(&body, &env2, k)
    }
}
