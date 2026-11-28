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

    /// `\A x \in S : P`: expanded into a conjunction over the bindings, or
    /// evaluated directly as a predicate when `body` can neither assign an
    /// unassigned variable nor branch (matching `Lowerer::go_forall` so
    /// streamed `SUBSET`/`kSubset` bounds short-circuit without materializing
    /// all bindings into a `Vec`).
    pub(super) fn forall(&mut self, e: &Expr, bounds: &[Bound], body: &Expr, env: &Env, k: &Cont) -> EResult<bool> {
        if self.is_pure_test(body, env, 0) {
            return self.test(e, env, k);
        }
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

    /// Whether enumerating `e` in `env` can neither assign an unassigned
    /// variable nor branch into multiple paths (so `self.go(e, env, k)` is
    /// equivalent to `self.test(e, env, k)`).
    pub(super) fn is_pure_test(&self, e: &Expr, env: &Env, depth: usize) -> bool {
        if depth > 8 {
            return false;
        }
        match &*e.kind {
            ExprKind::And(es) => es.iter().all(|c| self.is_pure_test(c, env, depth)),
            ExprKind::Or(_) | ExprKind::Quant { kind: QuantKind::Exists, .. } => false,
            ExprKind::Quant { kind: QuantKind::Forall, body, .. } => self.is_pure_test(body, env, depth),
            ExprKind::If { then, els, .. } => self.is_pure_test(then, env, depth) && self.is_pure_test(els, env, depth),
            ExprKind::Case { .. } if self.random => false,
            ExprKind::Case { arms, other } => {
                arms.iter().all(|(_, v)| self.is_pure_test(v, env, depth))
                    && other.as_ref().is_none_or(|o| self.is_pure_test(o, env, depth))
            }
            ExprKind::Let { body, .. } => self.is_pure_test(body, env, depth),
            ExprKind::Builtin { op: B::Implies, args } => self.is_pure_test(&args[1], env, depth),
            ExprKind::Builtin { op: B::Eq | B::In | B::SubsetEq, args } => !self.lhs_may_assign(&args[0], env, depth),
            ExprKind::Builtin { op: B::Unchanged | B::Compose, .. } | ExprKind::BoxAction { .. } | ExprKind::AngleAction { .. }
                if !self.init() =>
            {
                false
            }
            ExprKind::FnApp { func, .. } => !self.may_be_lambda(func, env, depth),
            ExprKind::Apply { op: OpRef::Const(_) | OpRef::Param(_), .. } => false,
            ExprKind::Apply { op: OpRef::Builtin(b), .. } => {
                !matches!(b, B::Eq | B::In | B::SubsetEq | B::Implies | B::Unchanged | B::Compose)
            }
            ExprKind::Apply { op: OpRef::Def(d), args } => {
                let d = self.ip.redirect_def(*d);
                let def = &self.ip.prog.defs[d.idx()];
                let expand = self.ip.def_defer_errors[d.idx()] || self.ip.def_by_name[d.idx()];
                match &def.kind {
                    DefKind::Op(body)
                        if expand && def.builtin.is_none() && !self.ip.def_value.contains_key(&d) && !self.ip.def_const[d.idx()] =>
                    {
                        if args.iter().any(|a| !self.arg_is_value_only(a, env, depth + 1)) {
                            return false;
                        }
                        self.is_pure_test(body, &self.ip.def_env(d, env), depth + 1)
                    }
                    _ => true,
                }
            }
            ExprKind::Local(l) => match env.lookup(*l) {
                Some(b) => match b.by_name(&self.ip.prog) {
                    Some((a, aenv)) => self.is_pure_test(a, aenv, depth + 1),
                    None => true,
                },
                None => true,
            },
            _ => true,
        }
    }

    /// Whether a call-by-name argument `a` can neither assign/branch in
    /// statement position, act as an assignment target on the LHS of
    /// `=`/`\in`/`\subseteq`, nor expand as a syntactic lambda in `fn_app`.
    fn arg_is_value_only(&self, a: &Expr, env: &Env, depth: usize) -> bool {
        !self.lhs_may_assign(a, env, depth) && !self.may_be_lambda(a, env, depth) && self.is_pure_test(a, env, depth)
    }

    /// Conservative check matching `Enumerator::lambda_of`: whether `f` could
    /// expand as a lazily represented function in `Enumerator::fn_app`.
    fn may_be_lambda(&self, f: &Expr, env: &Env, depth: usize) -> bool {
        if depth > 8 {
            return true;
        }
        match &*f.kind {
            ExprKind::FnConstruct { .. } => true,
            ExprKind::Local(l) => match env.lookup(*l) {
                Some(b) => b.by_name(&self.ip.prog).is_some_and(|(a, aenv)| self.may_be_lambda(a, aenv, depth + 1)),
                None => false,
            },
            ExprKind::Apply { op: OpRef::Def(_), args } if args.is_empty() => self.lambda_of(f, env).is_some(),
            ExprKind::Apply { op: OpRef::Const(_) | OpRef::Param(_), args } if args.is_empty() => true,
            _ => false,
        }
    }

    /// Conservative check matching `Enumerator::target` / `unassigned_target`.
    fn lhs_may_assign(&self, lhs: &Expr, env: &Env, depth: usize) -> bool {
        if depth > 8 {
            return true;
        }
        if self.init() {
            return self.may_be_var(lhs, env, depth);
        }
        match &*lhs.kind {
            ExprKind::Builtin { op: B::Prime, args } => self.may_be_var(&args[0], env, depth),
            ExprKind::Local(l) => match env.lookup(*l) {
                Some(b) => b.by_name(&self.ip.prog).is_some_and(|(a, aenv)| self.lhs_may_assign(a, aenv, depth + 1)),
                None => false,
            },
            ExprKind::Apply { op: OpRef::Def(d), args } if args.is_empty() => match self.ip.plain_op_body(*d) {
                Some((_, body)) => self.lhs_may_assign(body, env, depth + 1),
                None => false,
            },
            ExprKind::Apply { op: OpRef::Const(_) | OpRef::Param(_), args } if args.is_empty() => true,
            ExprKind::Let { body, .. } => self.lhs_may_assign(body, env, depth),
            _ => false,
        }
    }

    /// Conservative check matching `Enumerator::var_of` for unassigned vars.
    fn may_be_var(&self, e: &Expr, env: &Env, depth: usize) -> bool {
        if depth > 8 {
            return true;
        }
        match &*e.kind {
            ExprKind::Var(v) => self.s1[v.idx()].is_none(),
            ExprKind::InstVar { slot, .. } => {
                let v = self.ip.inst_var(*slot);
                v.idx() < self.s1.len() && self.s1[v.idx()].is_none()
            }
            ExprKind::Local(l) => match env.lookup(*l) {
                Some(b) => b.by_name(&self.ip.prog).is_some_and(|(a, aenv)| self.may_be_var(a, aenv, depth + 1)),
                // Inside a stepped-into operator body (`depth > 0`), an unbound
                // formal parameter might receive a state variable (e.g.
                // `Assign(v) == v' = 1`). At `depth == 0`, an unbound local is
                // a quantifier value variable, never a state variable.
                None => depth > 0,
            },
            ExprKind::Apply { op: OpRef::Def(d), args } if args.is_empty() => match self.ip.plain_op_body(*d) {
                Some((_, body)) => self.may_be_var(body, env, depth + 1),
                None => false,
            },
            ExprKind::Apply { op: OpRef::Const(_) | OpRef::Param(_), args } if args.is_empty() => true,
            ExprKind::Let { body, .. } => self.may_be_var(body, env, depth),
            _ => false,
        }
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
