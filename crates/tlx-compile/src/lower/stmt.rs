//! Statement lowering: an action (or Init) becomes a CPS statement tree
//! that enumerates successors exactly like `tlx_eval::enumerate` (TLC's
//! next-state enumeration). Keep the two in sync: the order of the checks
//! in `go`/`cont` encodes TLC semantics, including deliberate quirks such as
//! duplicate successors from overlapping disjuncts, the "all variables
//! assigned" shortcut, the expansion of `\A`, lazily expanded function
//! constructors and call-by-name operator arguments.
//!
//! The assigned next-state variables are tracked statically (`St`); the
//! pending conjuncts form a persistent continuation (`Cont`) that every
//! branch gets a copy of, bounded by `STMT_BUDGET`.

use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{self, BoundVars, DefKind, ExprKind as H, LocalId, OpRef, QuantKind};
use tlx_value::Value;

use super::*;

impl Lowerer<'_> {
    /// Continue with the pending conjuncts `k`.
    pub(super) fn cont(&mut self, k: &Cont, st: &St) -> LResult<Stmt> {
        self.count()?;
        // TLC: in Next, once every variable is assigned the remaining
        // conjuncts are only evaluated as predicates.
        if !st.init && k.0.is_some() && st.all_assigned() {
            return Ok(self.cont_as_guards(k, st));
        }
        let Some(node) = &k.0 else { return Ok(self.end_of_path(st)) };
        let (item, rest) = &**node;
        match item {
            Item::Expr(e, env) => self.go(e, env, rest, st),
            Item::Count(id) => Ok(Stmt::Count(*id)),
            Item::MustChange(e, env) => {
                let c = self.must_change(e, env, st);
                self.guarded(c, rest, st)
            }
        }
    }

    /// `ENABLED a` (outside Init and primes): the statement tree of `a`
    /// over a fresh next state. None if it cannot be lowered, or if a value
    /// bound in the environment reads the (outer) next state.
    pub(super) fn typed_enabled(&mut self, a: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        fn reads_next(e: &Expr) -> bool {
            let mut found = matches!(&*e.kind, ExprKind::NextVar(_));
            if !found {
                e.for_each_child(&mut |c| found |= reads_next(c));
            }
            found
        }
        if env.binds.iter().any(|(_, b)| matches!(b, LBind::Ir(x) if reads_next(x))) {
            return None;
        }
        // (The variables of an instantiated module that ENABLED quantifies
        // over have no place in the compiled next state: the interpreter.)
        if !self.ip.prog.inst_vars.is_empty() && self.ip.prog.mentions_inst_var(a) {
            return None;
        }
        let mut st2 = St::new(self.nvars(), false, false);
        st2.partial = true;
        st2.depth = st.depth;
        let saved_at = self.at.take();
        let r = self.go(a, env, &Cont::default(), &st2);
        self.at = saved_at;
        Some(Expr::new(Ty::Bool, ExprKind::Enabled(Box::new(r.ok()?))))
    }

    /// The rest of a path once every variable is assigned: each pending
    /// conjunct is a guard.
    fn cont_as_guards(&mut self, k: &Cont, st: &St) -> Stmt {
        let mut conds = Vec::new();
        let mut cur = k;
        let mut end = Stmt::Emit;
        while let Some(node) = &cur.0 {
            let (item, rest) = &**node;
            match item {
                Item::Expr(e, env) => conds.push(self.bool_expr(e, env, st)),
                Item::MustChange(e, env) => conds.push(self.must_change(e, env, st)),
                Item::Count(id) => {
                    end = Stmt::Count(*id);
                    break;
                }
            }
            cur = rest;
        }
        conds.into_iter().rev().fold(end, |s, c| guard(c, s))
    }

    /// The end of a path: emit the state, or report unassigned variables.
    fn end_of_path(&self, st: &St) -> Stmt {
        if st.all_assigned() || st.partial {
            return Stmt::Emit;
        }
        let missing: Vec<&str> = st.assigned.iter().enumerate().filter(|(_, a)| !**a).map(|(i, _)| &*self.ip.prog.vars[i].name).collect();
        let what = if st.init { "The initial state" } else { "Successor state" };
        Stmt::Error(
            format!("{what} is not completely specified. The following variable(s) are not defined: {}.", missing.join(", ")).into(),
        )
    }

    /// `~UNCHANGED e` (for `<<A>>_e`).
    fn must_change(&mut self, e: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        not(self.unchanged_expr(e, env, st))
    }

    /// Enumerate `e` as an action conjunct, then continue with `k`.
    pub(super) fn go(&mut self, e: &hir::Expr, env: &LEnv, k: &Cont, st: &St) -> LResult<Stmt> {
        self.count()?;
        if st.depth > INLINE_DEPTH {
            return unsupported("operator inlining too deep");
        }
        // TLC (Init): once every variable is assigned, conjuncts are predicates.
        if st.init && st.all_assigned() {
            return self.test(e, env, k, st);
        }
        if self.counts_paths(e, env, st) {
            // The continuation, once per path through `e`.
            let n = self.path_count(e, env, st)?;
            let rest = self.cont(k, st)?;
            let t = self.temp(Ty::Int);
            let set = Expr::new(Ty::Val, ExprKind::IntRange(int_lit(1), n));
            return Ok(Stmt::ForEach { bind: t, set, sorted: false, body: Box::new(rest) });
        }
        match &*e.kind {
            H::And(es) => {
                let k2 = es[1..].iter().rev().fold(k.clone(), |k2, c| k2.push(Item::Expr(c.clone(), env.clone())));
                self.go(&es[0], env, &k2, st)
            }
            H::Or(es) => {
                let branches = es.iter().map(|c| self.go(c, env, k, st)).collect::<LResult<_>>()?;
                Ok(Stmt::Branches(branches))
            }
            H::Quant { kind: QuantKind::Exists, bounds, body } => {
                if self.some_bound_empty(bounds, env) {
                    return Ok(Stmt::Stop);
                }
                let (env2, wrap) = self.bind_bounds(bounds, env, st)?;
                let inner = self.go(body, &env2, k, st)?;
                Ok(wrap(inner))
            }
            H::Quant { kind: QuantKind::Forall, bounds, body } => self.go_forall(e, bounds, body, env, k, st),
            H::If { cond, then, els } => {
                if let Some(b) = self.const_bool(cond, env) {
                    return self.go(if b { then } else { els }, env, k, st);
                }
                let c = self.bool_expr(cond, env, st);
                let t = self.go(then, env, k, st)?;
                let f = self.go(els, env, k, st)?;
                Ok(if_stmt(c, t, f))
            }
            H::Case { arms, other } => self.go_case(arms, other.as_ref(), env, k, st),
            H::Let { defs, body } => {
                let (env2, lets) = self.let_temps(defs, body, env, st);
                let mut s = self.go(body, &env2, k, st)?;
                for (t, v) in lets.into_iter().rev() {
                    s = Stmt::Let { temp: t, value: v, body: Box::new(s) };
                }
                Ok(s)
            }
            H::Apply { op, args } => self.go_apply(e, *op, args, env, k, st),
            H::Local(l) => match env.lookup(*l, &self.ip.prog) {
                Some(LBind::Thunk(te, tenv)) => self.go(&te, &tenv, k, st),
                _ => self.test(e, env, k, st),
            },
            H::Builtin { op: B::Eq, args } => match self.unassigned_target(&args[0], env, st) {
                Some(v) => self.go_assign_eq(v, &args[1], env, k, st),
                None => self.test(e, env, k, st),
            },
            H::Builtin { op: B::In, args } => match self.unassigned_target(&args[0], env, st) {
                Some(v) => self.go_assign_in(v, &args[1], env, k, st),
                None => self.test(e, env, k, st),
            },
            H::Builtin { op: B::SubsetEq, args } => match self.unassigned_target(&args[0], env, st) {
                Some(v) => self.go_assign_subset(v, &args[1], env, k, st),
                None => self.test(e, env, k, st),
            },
            H::Builtin { op: B::Unchanged, args } if !st.init => self.go_unchanged(&args[0], env, k, st),
            H::Builtin { op: B::Compose, args } if !st.init => self.go_compose(&args[0], &args[1], env, k, st),
            H::Builtin { op: B::Implies, args } => {
                let c = self.bool_expr(&args[0], env, st);
                let t = self.go(&args[1], env, k, st)?;
                let f = self.cont(k, st)?;
                Ok(if_stmt(c, t, f))
            }
            H::BoxAction { action, sub } if !st.init => {
                let a = self.go(action, env, k, st)?;
                let u = self.go_unchanged(sub, env, k, st)?;
                Ok(Stmt::Branches(vec![a, u]))
            }
            H::AngleAction { action, sub } if !st.init => {
                let k2 = k.push(Item::MustChange(sub.clone(), env.clone()));
                self.go(action, env, &k2, st)
            }
            H::FnApp { func, args } => match self.lambda_of(func, env) {
                Some(lambda) => self.go_fn_app(args, lambda, env, k, st),
                None => self.test(e, env, k, st),
            },
            _ => self.test(e, env, k, st),
        }
    }

    /// Lower each step independently. The continuation sees the original
    /// current state, not the intermediate one (compatibility D-19).
    fn go_compose(&mut self, a: &hir::Expr, b: &hir::Expr, env: &LEnv, k: &Cont, st: &St) -> LResult<Stmt> {
        let mut inner = St::new(self.nvars(), false, false);
        inner.partial = true;
        inner.depth = st.depth;
        let first = self.go(a, env, &Cont::default(), &inner)?;
        let second = self.go(b, env, &Cont::default(), &inner)?;
        let masks = second.emitted_assignments(self.nvars()).expect("lowered variable indices");
        let mut paths = Vec::new();
        for assigned in masks {
            let mut after = st.clone();
            for (a, b) in after.assigned.iter_mut().zip(&assigned) {
                *a |= *b;
            }
            paths.push(ComposePath { assigned, rest: self.cont(k, &after)? });
        }
        Ok(Stmt::Compose { first: Box::new(first), second: Box::new(second), paths, count: !st.partial })
    }

    /// `\A` in an action: TLC expands it into a conjunction over the
    /// elements. A body that can neither assign nor branch is just a test;
    /// a non-assigning body that may branch (`\/`, `\E`, expanded
    /// definitions) becomes a `Repeat`; otherwise the domains must be
    /// compile-time constants and the conjunction is expanded statically.
    fn go_forall(&mut self, e: &hir::Expr, bounds: &[hir::Bound], body: &hir::Expr, env: &LEnv, k: &Cont, st: &St) -> LResult<Stmt> {
        if !self.may_assign(body, env, st) {
            if !self.may_branch(body, env, 0) {
                return self.test(e, env, k, st);
            }
            if let Some(s) = self.repeat_forall(bounds, body, env, k, st)? {
                return Ok(s);
            }
        }
        let instances = self.forall_instances(bounds, env)?;
        let k2 = instances.into_iter().rev().fold(k.clone(), |k2, e2| k2.push(Item::Expr(body.clone(), e2)));
        self.cont(&k2, st)
    }

    /// Environments binding each combination of elements of the constant
    /// `\A` domains, first variable varying fastest.
    fn forall_instances(&self, bounds: &[hir::Bound], env: &LEnv) -> LResult<Vec<LEnv>> {
        let mut domains = Vec::new();
        let mut constant = true;
        for b in bounds {
            match self.const_value(&b.set, env).map(|set| tlx_value::ops::enumerate(&set)) {
                Some(Ok(xs)) => domains.push((&b.vars, xs)),
                _ => constant = false,
            }
        }
        if !constant {
            return unsupported("\\A with a state-dependent domain over an assigning body");
        }
        let mut combos: Vec<LEnv> = vec![env.clone()];
        for (vars, xs) in domains {
            // The choices of each binder; a tuple binder binds all its
            // components at once.
            let binders: Vec<Vec<Vec<(LocalId, Value)>>> = match vars {
                BoundVars::Tuple(ls) => vec![xs.iter().map(|x| destructure(ls, x)).collect::<LResult<_>>()?],
                BoundVars::Many(ls) => ls.iter().map(|l| xs.iter().map(|x| vec![(*l, x.clone())]).collect()).collect(),
            };
            for choices in binders {
                let mut next = Vec::with_capacity(choices.len() * combos.len());
                for choice in &choices {
                    for base in &combos {
                        next.push(choice.iter().fold(base.clone(), |e2, (l, v)| e2.bind(*l, LBind::Ir(val_lit(v.clone())))));
                    }
                }
                combos = next;
            }
        }
        Ok(combos)
    }

    /// `\A` over a non-assigning, branching body as a `Repeat` (one binder
    /// at a time; further binders become an inner `\A`).
    fn repeat_forall(&mut self, bounds: &[hir::Bound], body: &hir::Expr, env: &LEnv, k: &Cont, st: &St) -> LResult<Option<Stmt>> {
        let Some((b, more)) = bounds.split_first() else { return Ok(None) };
        let BoundVars::Many(ls) = &b.vars else { return Ok(None) };
        let Some((l, ls_rest)) = ls.split_first() else { return Ok(None) };
        let mut inner_bounds = Vec::new();
        if !ls_rest.is_empty() {
            inner_bounds.push(hir::Bound { vars: BoundVars::Many(ls_rest.to_vec()), set: b.set.clone() });
        }
        inner_bounds.extend(more.iter().cloned());
        let inner = if inner_bounds.is_empty() {
            body.clone()
        } else {
            hir::Expr::new(H::Quant { kind: QuantKind::Forall, bounds: inner_bounds, body: body.clone() }, body.span)
        };
        let set = self.action_iter_set_expr(&b.set, env, st);
        let (set, ety) = self.typed_iter(set);
        let t = self.iter_temp(ety, &set);
        let id = self.repeats;
        self.repeats += 1;
        let env2 = env.bind(*l, LBind::Ir(temp_ref(ety, t)));
        let kb = Cont::default().push(Item::Count(id));
        let body_s = self.go(&inner, &env2, &kb, st)?;
        let rest = self.cont(k, st)?;
        Ok(Some(Stmt::Repeat { id, bind: t, set, body: Box::new(body_s), rest: Box::new(rest) }))
    }

    /// CASE: the first true guard, in order; none true is an error.
    fn go_case(&mut self, arms: &[(hir::Expr, hir::Expr)], other: Option<&hir::Expr>, env: &LEnv, k: &Cont, st: &St) -> LResult<Stmt> {
        let (arms, other) = self.live_case_arms(arms, other, env);
        let mut tail = match other {
            Some(o) => self.go(o, env, k, st)?,
            None => Stmt::Error("Attempted to evaluate a CASE with no conditions true.".into()),
        };
        for (g, v) in arms.iter().rev() {
            let c = self.bool_expr(g, env, st);
            let body = self.go(v, env, k, st)?;
            tail = if_stmt(c, body, tail);
        }
        Ok(tail)
    }

    /// `x' = e` (`x = e` in Init) for an unassigned `x`.
    fn go_assign_eq(&mut self, v: usize, rhs: &hir::Expr, env: &LEnv, k: &Cont, st: &St) -> LResult<Stmt> {
        let sid = self.var_sid(v);
        let val = self.expr_into(rhs, env, st, sid);
        self.assign(v, val, k, st)
    }

    /// `x' \in S` for an unassigned `x`: a branch per element.
    fn go_assign_in(&mut self, v: usize, set: &hir::Expr, env: &LEnv, k: &Cont, st: &St) -> LResult<Stmt> {
        let set = self.action_iter_set_expr(set, env, st);
        // A constant domain: list its elements directly in the variable's
        // encoding.
        let direct = match (&*set.kind, self.var_ty(v)) {
            (ExprKind::Const(c), Ty::Enc(vsid)) => {
                let es = self.shape_of(Ty::Enc(vsid)).cloned();
                es.and_then(|es| self.const_elems(c, &es))
            }
            _ => None,
        };
        let (set, ety) = match direct {
            Some(x) => x,
            None => self.typed_iter(set),
        };
        // An encoded set iterated as a boxed one (the encoded order of its
        // elements is not TLC's): computed into a temp first, so that only
        // the conversion is a boxed region, not the computation of the set.
        let (set, outer) = match &*set.kind {
            ExprKind::Convert(x) if ety == Ty::Val && matches!(x.ty, Ty::Enc(_)) && !is_trivial(x) => {
                let (s, bind) = self.share(x.clone());
                (to_val(s), bind)
            }
            _ => (set, None),
        };
        let t = self.temp(ety);
        let body = self.assign(v, temp_ref(ety, t), k, st)?;
        let each = Stmt::ForEach { bind: t, set, sorted: false, body: Box::new(body) };
        Ok(match outer {
            Some((temp, value)) => Stmt::Let { temp, value, body: Box::new(each) },
            None => each,
        })
    }

    /// `x' \subseteq S` for an unassigned `x`: a branch per subset, in
    /// normalized (TLC) order.
    fn go_assign_subset(&mut self, v: usize, set: &hir::Expr, env: &LEnv, k: &Cont, st: &St) -> LResult<Stmt> {
        let set = self.val_expr(set, env, st);
        let subsets = Expr::new(Ty::Val, ExprKind::ValOp { op: B::Subset, args: vec![set] });
        let t = self.temp(Ty::Val);
        let body = self.assign(v, temp_ref(Ty::Val, t), k, st)?;
        Ok(Stmt::ForEach { bind: t, set: subsets, sorted: true, body: Box::new(body) })
    }

    /// Application of a lazily expanded function constructor (TLC
    /// enumerates its body with the argument bound).
    fn go_fn_app(
        &mut self,
        args: &[hir::Expr],
        lambda: (Vec<hir::Bound>, hir::Expr, LEnv),
        env: &LEnv,
        k: &Cont,
        st: &St,
    ) -> LResult<Stmt> {
        let (bounds, body, fenv) = lambda;
        // One argument per (non-tuple) binder: bind each to its lowered
        // argument (evaluated in order, before the body).
        let locals: Vec<Option<LocalId>> = bounds
            .iter()
            .flat_map(|b| match &b.vars {
                BoundVars::Many(ls) => ls.iter().map(|l| Some(*l)).collect::<Vec<_>>(),
                BoundVars::Tuple(_) => vec![None],
            })
            .collect();
        if locals.len() == args.len() && locals.iter().all(|l| l.is_some()) {
            let mut env2 = fenv.clone();
            let mut lets = Vec::new();
            for (l, a) in locals.iter().zip(args) {
                let x = self.expr(a, env, st);
                if is_trivial(&x) {
                    env2 = env2.bind(l.unwrap(), LBind::Ir(x));
                    continue;
                }
                let t = self.temp(x.ty);
                env2 = env2.bind(l.unwrap(), LBind::Ir(temp_ref(x.ty, t)));
                lets.push((t, x));
            }
            let mut out = self.go(&body, &env2, k, st)?;
            for (temp, value) in lets.into_iter().rev() {
                out = Stmt::Let { temp, value, body: Box::new(out) };
            }
            return Ok(out);
        }
        let arg = if args.len() == 1 {
            self.val_expr(&args[0], env, st)
        } else {
            let parts = args.iter().map(|a| self.val_expr(a, env, st)).collect();
            Expr::new(Ty::Val, ExprKind::Tuple(parts))
        };
        let t = self.temp(Ty::Val);
        let env2 = bind_fn_arg(&bounds, temp_ref(Ty::Val, t), &fenv);
        let body = self.go(&body, &env2, k, st)?;
        Ok(Stmt::Let { temp: t, value: arg, body: Box::new(body) })
    }

    /// An operator application in an action: user definitions are expanded
    /// (arguments by name), everything else is a test.
    fn go_apply(&mut self, e: &hir::Expr, op: OpRef, args: &[hir::Expr], env: &LEnv, k: &Cont, st: &St) -> LResult<Stmt> {
        match op {
            OpRef::Def(d) => {
                let ip = self.ip;
                let d = ip.redirect_def(d);
                let def = &ip.prog.defs[d.idx()];
                // Not a definition TLC overrides by a Java method (evaluated
                // with its arguments, see `Enumerator::go_call`).
                let expandable = def.builtin.is_none()
                    && !ip.has_def_value(d)
                    && !ip.is_const_def(d)
                    && (ip.defers_arg_errors(d) || ip.is_action_level(d));
                let (true, DefKind::Op(body)) = (expandable, &def.kind) else { return self.test(e, env, k, st) };
                let base = self.def_env(d, env);
                let env2 = self.bind_params(&def.params, args, env, base)?;
                self.go(body, &env2, k, &st.deeper())
            }
            OpRef::Const(c) => match self.ip.const_op_ref(c) {
                Some(OpRef::Def(d)) => self.go_call(d, args, e, env, k, st),
                Some(OpRef::Builtin(b)) => self.go_builtin_ref(b, args, e, env, k, st),
                _ => self.test(e, env, k, st),
            },
            OpRef::Param(l) => match env.lookup(l, &self.ip.prog) {
                Some(LBind::Op(LOp::Ref(OpRef::Def(d)))) => self.go_call(d, args, e, env, k, st),
                Some(LBind::Op(LOp::Ref(OpRef::Builtin(b)))) => self.go_builtin_ref(b, args, e, env, k, st),
                Some(LBind::Op(LOp::Ref(OpRef::Const(c)))) => self.go_apply(e, OpRef::Const(c), args, env, k, st),
                Some(LBind::Op(LOp::Lambda(params, body, lenv))) => {
                    let env2 = self.bind_params(&params, args, env, lenv)?;
                    self.go(&body, &env2, k, &st.deeper())
                }
                _ => self.test(e, env, k, st),
            },
            OpRef::Builtin(b) => self.go_builtin_ref(b, args, e, env, k, st),
        }
    }

    /// Enumerate `d(args)` (for an operator reached through a constant
    /// override or an operator argument).
    fn go_call(&mut self, d: hir::DefId, args: &[hir::Expr], at: &hir::Expr, env: &LEnv, k: &Cont, st: &St) -> LResult<Stmt> {
        let call = hir::Expr::new(H::Apply { op: OpRef::Def(d), args: args.to_vec() }, at.span);
        self.go(&call, env, k, st)
    }

    /// Enumerate builtin `op(args)` (when reached through an operator
    /// parameter or constant override).
    fn go_builtin_ref(&mut self, op: B, args: &[hir::Expr], at: &hir::Expr, env: &LEnv, k: &Cont, st: &St) -> LResult<Stmt> {
        let call = hir::Expr::new(H::Builtin { op, args: args.to_vec() }, at.span);
        self.go(&call, env, k, st)
    }

    /// `UNCHANGED e` in an action: assigns unassigned variables (through
    /// tuples and 0-ary definitions), otherwise a guard.
    fn go_unchanged(&mut self, e: &hir::Expr, env: &LEnv, k: &Cont, st: &St) -> LResult<Stmt> {
        if let Some(v) = self.var_of(e, env) {
            if !st.assigned[v] {
                let cur = self.var_expr(v);
                return self.assign(v, cur, k, st);
            }
            // Assigned: must equal the current value (else the branch is pruned).
            let next = self.next_var_expr(v);
            let cur = self.var_expr(v);
            let same = to_bool(self.typed_eq(next, cur));
            return self.guarded(same, k, st);
        }
        match &*e.kind {
            H::Tuple(es) => {
                let k2 = es.iter().rev().fold(k.clone(), |k2, c| {
                    let u = hir::Expr::new(H::Builtin { op: B::Unchanged, args: vec![c.clone()] }, c.span);
                    k2.push(Item::Expr(u, env.clone()))
                });
                self.cont(&k2, st)
            }
            H::Apply { op: OpRef::Def(d), args } if args.is_empty() => match self.op_body(*d) {
                Some((d, body)) => {
                    let base = self.def_env(d, env);
                    self.go_unchanged(&body, &base, k, st)
                }
                None => {
                    let u = self.unchanged_expr(e, env, st);
                    self.guarded(u, k, st)
                }
            },
            H::Local(l) => match env.lookup(*l, &self.ip.prog) {
                Some(LBind::Thunk(te, tenv)) => self.go_unchanged(&te, &tenv, k, st),
                _ => {
                    let u = self.unchanged_expr(e, env, st);
                    self.guarded(u, k, st)
                }
            },
            H::Let { defs, body } => {
                let (env2, lets) = self.let_temps(defs, body, env, st);
                let mut s = self.go_unchanged(body, &env2, k, st)?;
                for (t, v) in lets.into_iter().rev() {
                    s = Stmt::Let { temp: t, value: v, body: Box::new(s) };
                }
                Ok(s)
            }
            _ => {
                let u = self.unchanged_expr(e, env, st);
                self.guarded(u, k, st)
            }
        }
    }

    /// Assign next-state variable `v` (in its encoding) and continue.
    fn assign(&mut self, v: usize, value: Expr, k: &Cont, st: &St) -> LResult<Stmt> {
        let sid = self.var_sid(v);
        let value = self.coerce_enc(value, sid);
        let mut st2 = st.clone();
        st2.assigned[v] = true;
        let body = self.cont(k, &st2)?;
        Ok(Stmt::Assign { var: v as u32, value, body: Box::new(body) })
    }

    /// `e` as a guard on the rest of the path.
    fn test(&mut self, e: &hir::Expr, env: &LEnv, k: &Cont, st: &St) -> LResult<Stmt> {
        let c = self.bool_expr(e, env, st);
        self.guarded(c, k, st)
    }

    /// Continue with `k` if `cond` holds.
    fn guarded(&mut self, cond: Expr, k: &Cont, st: &St) -> LResult<Stmt> {
        let then = self.cont(k, st)?;
        Ok(guard(cond, then))
    }

    /// Bind the variables of `\E` bounds: returns the extended environment and
    /// a function wrapping a body into the corresponding loops (first
    /// variable varies fastest, like TLC's ContextEnumerator).
    /// All the domains of `bounds` are constant valid finite sets and at least
    /// one is empty (there is nothing to enumerate, and no domain raises an
    /// error).
    pub(super) fn some_bound_empty(&self, bounds: &[hir::Bound], env: &LEnv) -> bool {
        let Some(sets): Option<Vec<Value>> = bounds.iter().map(|b| self.const_value(&b.set, env)).collect() else {
            return false;
        };
        let mut empty = false;
        for s in &sets {
            if !s.is_set() || tlx_value::ops::materialization_error(s).is_some() {
                return false;
            }
            let Ok(card) = tlx_value::ops::cardinality(s) else {
                return false;
            };
            if card == 0 {
                empty = true;
            }
        }
        empty
    }

    /// `set` is statically known to be a valid finite enumerable set (cannot
    /// fail with a non-set / non-enumerable bound error when iterated).
    pub(super) fn bound_is_valid_set(&self, set: &Expr) -> bool {
        match &*set.kind {
            ExprKind::Const(v) => {
                v.is_set() && tlx_value::ops::materialization_error(v).is_none() && tlx_value::ops::cardinality(v).is_ok()
            }
            ExprKind::IntRange(_, _)
            | ExprKind::ConstElems { .. }
            | ExprKind::Subsets(_)
            | ExprKind::OrderedSet { .. }
            | ExprKind::RefElems(_) => true,
            _ => matches!(self.shape_of(set.ty), Some(Shape::Set { .. })),
        }
    }

    /// Hoist the value sub-expressions of a statically-valid bound `set` into
    /// `upfront` so they are evaluated before an outer loop (which may be
    /// empty), without ever binding an iteration-source-only IR node as a
    /// first-class `Let` value.
    pub(super) fn hoist_valid_bound(&mut self, set: Expr, upfront: &mut Vec<(Temp, Expr)>) -> Expr {
        match &*set.kind {
            ExprKind::ConstElems { .. } => set,
            ExprKind::IntRange(lo, hi) => {
                let (lo, b1) = self.share(lo.clone());
                let (hi, b2) = self.share(hi.clone());
                upfront.extend(b1);
                upfront.extend(b2);
                Expr::new(Ty::Val, ExprKind::IntRange(lo, hi))
            }
            ExprKind::Subsets(x) => {
                let (x, b) = self.share(x.clone());
                upfront.extend(b);
                Expr::new(set.ty, ExprKind::Subsets(x))
            }
            ExprKind::OrderedSet { set: inner, plan } => {
                let (inner, b) = self.share(inner.clone());
                upfront.extend(b);
                Expr::new(set.ty, ExprKind::OrderedSet { set: inner, plan: plan.clone() })
            }
            ExprKind::RefElems(x) => {
                let (x, b) = self.share(x.clone());
                upfront.extend(b);
                Expr::new(set.ty, ExprKind::RefElems(x))
            }
            _ => {
                let (s, b) = self.share(set);
                upfront.extend(b);
                s
            }
        }
    }

    fn bind_bounds(&mut self, bounds: &[hir::Bound], env: &LEnv, st: &St) -> LResult<(LEnv, Box<dyn FnOnce(Stmt) -> Stmt>)> {
        // (temp, set, tuple binder check) per enumerated slot, in binding order.
        let mut slots: Vec<(Temp, Expr, Option<Expr>)> = Vec::new();
        let mut upfront: Vec<(Temp, Expr)> = Vec::new();
        let mut env2 = env.clone();
        let sets: Vec<Expr> = bounds.iter().map(|b| self.action_iter_set_expr(&b.set, env, st)).collect();
        let multi = bounds.len() > 1;
        for (idx, (b, set)) in bounds.iter().zip(sets).enumerate() {
            let need_upfront = multi && idx + 1 < bounds.len();
            let mut hoist = |this: &mut Self, set: Expr| -> Expr {
                if !need_upfront {
                    return set;
                }
                if this.bound_is_valid_set(&set) {
                    return this.hoist_valid_bound(set, &mut upfront);
                }
                let (s, bnd) = this.share(set);
                upfront.extend(bnd);
                let dummy = this.temp(Ty::Val);
                let chk = this.temp(Ty::Bool);
                let probe = Expr::new(Ty::Bool, ExprKind::Exists { bind: dummy, set: s.clone(), body: bool_lit(true) });
                upfront.push((chk, probe));
                s
            };
            match &b.vars {
                BoundVars::Many(ls) => {
                    let (set, ety) = self.typed_iter(set);
                    let set = hoist(self, set);
                    for l in ls {
                        let t = self.iter_temp(ety, &set);
                        env2 = env2.bind(*l, LBind::Ir(temp_ref(ety, t)));
                        slots.push((t, set.clone(), None));
                    }
                }
                BoundVars::Tuple(ls) => {
                    let (tset, ety) = self.typed_iter(set.clone());
                    let t = self.temp(ety);
                    if let Some((e3, check)) = self.bind_elem(&b.vars, &temp_ref(ety, t), &env2) {
                        let tset = hoist(self, tset);
                        env2 = e3;
                        slots.push((t, tset, check));
                        continue;
                    }
                    // Boxed elements: components by application (the
                    // interpreter checks that the element is a tuple of
                    // the binder's length).
                    let set = hoist(self, to_val(set));
                    let t = self.temp(Ty::Val);
                    for (i, l) in ls.iter().enumerate() {
                        env2 = env2.bind(*l, LBind::Ir(tuple_component(temp_ref(Ty::Val, t), i)));
                    }
                    let len = Expr::new(Ty::Val, ExprKind::ValOp { op: B::Len, args: vec![temp_ref(Ty::Val, t)] });
                    slots.push((t, set, Some(eq(len, val_lit(Value::Int(ls.len() as i64))))));
                }
            }
        }
        // First slot fastest = innermost loop; upfront domain checks run
        // outside all loops in binding order.
        let wrap = move |inner: Stmt| {
            let looped = slots.into_iter().fold(inner, |s, (t, set, check)| Stmt::ForEach {
                bind: t,
                set,
                sorted: false,
                body: Box::new(binders::checked_stmt(check, s)),
            });
            upfront.into_iter().rev().fold(looped, |body, (temp, value)| Stmt::Let { temp, value, body: Box::new(body) })
        };
        Ok((env2, Box::new(wrap)))
    }

    /// Bind operator parameters: operator arguments as operators, the
    /// others by name (TLC passes arguments lazily in actions).
    pub(super) fn bind_params(&mut self, params: &[LocalId], args: &[hir::Expr], env: &LEnv, base: LEnv) -> LResult<LEnv> {
        let mut out = base;
        for (p, a) in params.iter().zip(args) {
            let b =
                if self.ip.prog.locals[p.idx()].arity > 0 { LBind::Op(self.op_arg(a, env)?) } else { LBind::Thunk(a.clone(), env.clone()) };
            out = out.bind(*p, b);
        }
        Ok(out)
    }

    /// The operator passed as argument `e`.
    pub(super) fn op_arg(&self, e: &hir::Expr, env: &LEnv) -> LResult<LOp> {
        match &*e.kind {
            H::OpArg(OpRef::Param(l)) => match env.lookup(*l, &self.ip.prog) {
                Some(LBind::Op(o)) => Ok(o),
                _ => unsupported("operator parameter not bound to an operator"),
            },
            // A LET definition closes over the current lexical environment
            // (matching `tlx_eval::Interp::op_val`).
            H::OpArg(OpRef::Def(d)) if self.ip.prog.def_is_let(*d) => match &self.ip.prog.defs[d.idx()].kind {
                DefKind::Op(body) => Ok(LOp::Lambda(self.ip.prog.defs[d.idx()].params.clone().into(), body.clone(), env.clone())),
                _ => Ok(LOp::Ref(OpRef::Def(*d))),
            },
            H::OpArg(r) => Ok(LOp::Ref(*r)),
            H::Lambda { params, body } => Ok(LOp::Lambda(params.clone().into(), body.clone(), env.clone())),
            _ => unsupported("unexpected operator argument"),
        }
    }
}

/// Bind the bound variables of a function constructor to argument `arg`
/// (a tuple of the components when there are several).
fn bind_fn_arg(bounds: &[hir::Bound], arg: Expr, env: &LEnv) -> LEnv {
    let n: usize = bounds
        .iter()
        .map(|b| match &b.vars {
            BoundVars::Many(ls) => ls.len(),
            BoundVars::Tuple(_) => 1,
        })
        .sum();
    let component = |i: usize| if n == 1 { arg.clone() } else { tuple_component(arg.clone(), i) };
    let mut out = env.clone();
    let mut i = 0;
    for b in bounds {
        match &b.vars {
            BoundVars::Many(ls) => {
                for l in ls {
                    out = out.bind(*l, LBind::Ir(component(i)));
                    i += 1;
                }
            }
            BoundVars::Tuple(ls) => {
                let x = component(i);
                i += 1;
                for (j, l) in ls.iter().enumerate() {
                    out = out.bind(*l, LBind::Ir(tuple_component(x.clone(), j)));
                }
            }
        }
    }
    out
}

/// Bind the components of tuple `x` to the locals of a tuple binder.
fn destructure(ls: &[LocalId], x: &Value) -> LResult<Vec<(LocalId, Value)>> {
    let Value::Tuple(parts) = x else {
        return unsupported("tuple binder over non-tuple");
    };
    if parts.len() != ls.len() {
        return unsupported("tuple binder length mismatch");
    }
    Ok(ls.iter().copied().zip(parts.iter().cloned()).collect())
}

/// Component `i` (0-based) of a boxed tuple.
fn tuple_component(t: Expr, i: usize) -> Expr {
    Expr::new(Ty::Val, ExprKind::Apply(t, val_lit(Value::Int(i as i64 + 1))))
}
