//! Path counting: a conjunct of an action that cannot assign but may branch
//! (`\/`, `\E`, expanded definitions and lazily applied functions in
//! statement position) only multiplies its continuation: TLC continues once
//! per successful path through it, every path leaving the same state. When
//! enumerating such a conjunct as statements would exceed the statement
//! budget (e.g. VoteProof's recursive `SafeAt`), its number of paths is
//! computed as an integer expression mirroring `go` (sums for disjunctions
//! and `\E`, products for conjunctions and `\A`, unrolled recursion) and the
//! continuation is run that many times.

use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{self, BoundVars, DefKind, ExprKind as H, OpRef, QuantKind};

use super::*;

impl Lowerer<'_> {
    /// The number of paths through the non-assigning conjunct `e` (an
    /// integer expression), as `go` would enumerate them.
    pub(super) fn path_count(&mut self, e: &hir::Expr, env: &LEnv, st: &St) -> LResult<Expr> {
        self.count()?;
        if st.depth > INLINE_DEPTH {
            return unsupported("operator inlining too deep");
        }
        match &*e.kind {
            H::And(es) => {
                // Later conjuncts are only enumerated on the paths of the
                // earlier ones: a product that stops at zero.
                let mut acc = self.path_count(&es[0], env, st)?;
                for c in &es[1..] {
                    let n = self.path_count(c, env, st)?;
                    let (a, bind) = self.share(acc);
                    let zero = eq(a.clone(), int_lit(0));
                    let prod = Expr::new(Ty::Int, ExprKind::IntBin(IntOp::Mul, a, n));
                    acc = let_in(bind, Expr::new(Ty::Int, ExprKind::If(zero, int_lit(0), prod)));
                }
                Ok(acc)
            }
            H::Or(es) => {
                let mut acc: Option<Expr> = None;
                for c in es {
                    let n = self.path_count(c, env, st)?;
                    acc = Some(match acc {
                        None => n,
                        Some(a) => Expr::new(Ty::Int, ExprKind::IntBin(IntOp::Add, a, n)),
                    });
                }
                Ok(acc.unwrap_or_else(|| int_lit(0)))
            }
            H::Quant { kind, bounds, body } => {
                let product = *kind == QuantKind::Forall;
                if product && !self.may_branch(body, env, 0) {
                    return Ok(self.test_count(e, env, st));
                }
                if self.some_bound_empty(bounds, env) {
                    return Ok(int_lit(product as i64));
                }
                // One fold per binder, the first binder outermost (the
                // order only matters for errors).
                let mut slots = Vec::new();
                let mut env2 = env.clone();
                for b in bounds {
                    let set = self.extensional_set_expr(&b.set, env, st);
                    let (set, ety) = self.typed_iter(set);
                    match &b.vars {
                        BoundVars::Many(ls) => {
                            for l in ls {
                                let t = self.temp(ety);
                                env2 = env2.bind(*l, LBind::Ir(temp_ref(ety, t)));
                                slots.push((t, set.clone(), None));
                            }
                        }
                        BoundVars::Tuple(_) => {
                            let t = self.temp(ety);
                            let Some((e3, check)) = self.bind_elem(&b.vars, &temp_ref(ety, t), &env2) else {
                                return unsupported("tuple binder over boxed elements");
                            };
                            env2 = e3;
                            slots.push((t, set, check));
                        }
                    }
                }
                let n = self.path_count(body, &env2, st)?;
                Ok(slots.into_iter().rev().fold(n, |n, (bind, set, check)| {
                    let body = binders::checked(check, n);
                    Expr::new(Ty::Int, ExprKind::Fold { product, bind, set, body })
                }))
            }
            H::If { cond, then, els } => {
                if let Some(b) = self.const_bool(cond, env) {
                    return self.path_count(if b { then } else { els }, env, st);
                }
                let c = self.bool_expr(cond, env, st);
                let t = self.path_count(then, env, st)?;
                let f = self.path_count(els, env, st)?;
                Ok(Expr::new(Ty::Int, ExprKind::If(c, t, f)))
            }
            H::Case { arms, other } => {
                let (arms, other) = self.live_case_arms(arms, other.as_ref(), env);
                let mut acc = match other {
                    Some(o) => self.path_count(o, env, st)?,
                    None => Expr::new(Ty::Int, ExprKind::Fail("Attempted to evaluate a CASE with no conditions true.".into())),
                };
                for (g, v) in arms.iter().rev() {
                    let c = self.bool_expr(g, env, st);
                    let n = self.path_count(v, env, st)?;
                    acc = Expr::new(Ty::Int, ExprKind::If(c, n, acc));
                }
                Ok(acc)
            }
            H::Let { defs, body } => {
                let (env2, lets) = self.let_temps(defs, body, env, st);
                let n = self.path_count(body, &env2, st)?;
                Ok(let_in(lets.into_iter().rev(), n))
            }
            H::Builtin { op: B::Implies, args } => {
                let c = self.bool_expr(&args[0], env, st);
                let n = self.path_count(&args[1], env, st)?;
                Ok(Expr::new(Ty::Int, ExprKind::If(c, n, int_lit(1))))
            }
            H::Local(l) => match env.lookup(*l, &self.ip.prog) {
                Some(LBind::Thunk(te, tenv)) => self.path_count(&te, &tenv, st),
                _ => Ok(self.test_count(e, env, st)),
            },
            H::Apply { op, args } => self.count_apply(e, *op, args, env, st),
            H::FnApp { func, args } => match self.lambda_of(func, env) {
                Some((bounds, body, fenv)) => self.count_fn_app(args, bounds, body, fenv, env, st),
                None => Ok(self.test_count(e, env, st)),
            },
            _ => Ok(self.test_count(e, env, st)),
        }
    }

    /// A conjunct that does not branch: one path if it holds.
    fn test_count(&mut self, e: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        let c = self.bool_expr(e, env, st);
        Expr::new(Ty::Int, ExprKind::If(c, int_lit(1), int_lit(0)))
    }

    /// `go_apply` for path counting: definitions are expanded with their
    /// arguments by name.
    fn count_apply(&mut self, e: &hir::Expr, op: OpRef, args: &[hir::Expr], env: &LEnv, st: &St) -> LResult<Expr> {
        let target = match op {
            OpRef::Def(d) => Some(d),
            OpRef::Const(c) => match self.ip.const_op_ref(c) {
                Some(OpRef::Def(d)) => Some(d),
                _ => None,
            },
            OpRef::Param(l) => match env.lookup(l, &self.ip.prog) {
                Some(LBind::Op(LOp::Ref(OpRef::Def(d)))) => Some(d),
                Some(LBind::Op(LOp::Lambda(params, body, lenv))) => {
                    let env2 = self.bind_params(&params, args, env, lenv)?;
                    return self.path_count(&body, &env2, &st.deeper());
                }
                _ => None,
            },
            OpRef::Builtin(_) => None,
        };
        let Some(d) = target else { return Ok(self.test_count(e, env, st)) };
        let ip = self.ip;
        let d = ip.redirect_def(d);
        let def = &ip.prog.defs[d.idx()];
        let expandable =
            def.builtin.is_none() && !ip.has_def_value(d) && !ip.is_const_def(d) && (ip.defers_arg_errors(d) || ip.is_action_level(d));
        let (true, DefKind::Op(body)) = (expandable, &def.kind) else { return Ok(self.test_count(e, env, st)) };
        let base = self.def_env(d, env);
        let env2 = self.bind_params(&def.params, args, env, base)?;
        self.path_count(body, &env2, &st.deeper())
    }

    /// `go_fn_app` for path counting: the body of a lazily applied function
    /// with its binders bound to the arguments (recursion unrolled a few
    /// levels; deeper is a runtime failure).
    fn count_fn_app(
        &mut self,
        args: &[hir::Expr],
        bounds: Vec<hir::Bound>,
        body: hir::Expr,
        fenv: LEnv,
        env: &LEnv,
        st: &St,
    ) -> LResult<Expr> {
        let key = std::sync::Arc::as_ptr(&body.kind) as usize;
        let depth = self.count_stack.iter().filter(|k| **k == key).count();
        if depth >= RECURSION_UNROLL {
            return Ok(Expr::new(Ty::Int, ExprKind::Fail("recursion deeper than the compiled unrolling".into())));
        }
        let locals: Vec<hir::LocalId> = bounds
            .iter()
            .flat_map(|b| match &b.vars {
                BoundVars::Many(ls) => ls.clone(),
                BoundVars::Tuple(_) => Vec::new(),
            })
            .collect();
        if locals.len() != args.len() || bounds.iter().any(|b| matches!(b.vars, BoundVars::Tuple(_))) {
            return unsupported("function application with tuple binders in a counted conjunct");
        }
        let mut env2 = fenv;
        let mut lets = Vec::new();
        for (l, a) in locals.iter().zip(args) {
            let x = self.expr(a, env, st);
            let (x, bind) = self.share(x);
            lets.extend(bind);
            env2 = env2.bind(*l, LBind::Ir(x));
        }
        self.count_stack.push(key);
        let n = self.path_count(&body, &env2, &st.deeper());
        self.count_stack.pop();
        Ok(let_in(lets.into_iter().rev(), n?))
    }

    /// Whether `e` (a conjunct) should be counted rather than enumerated:
    /// counting is enabled, `e` cannot assign, may branch, and evaluating it
    /// a different number of times than TLC cannot be observed.
    pub(super) fn counts_paths(&self, e: &hir::Expr, env: &LEnv, st: &St) -> bool {
        self.count_branches && !self.may_assign(e, env, st) && self.may_branch(e, env, 0) && !self.volatile_expr(e, env)
    }
}
