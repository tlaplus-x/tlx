//! Expression lowering with value semantics: constant folding, the typed
//! fast paths (see `typed`) when lowering for encoded states, boxed
//! operations otherwise, operator inlining, and the interpreter fallback
//! (`ExprKind::Interp`) for everything else.
//!
//! Variables read the current state, the next state when primed (only once
//! assigned on the path; otherwise the interpreter reports the error), and
//! in Init the state being built.

use tlx_eval::env::Env;
use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{self, BoundVars, DefKind, ExprKind as H, LocalId, OpRef, QuantKind};

use super::*;

impl Lowerer<'_> {
    pub(super) fn bool_expr(&mut self, e: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        let x = self.expr(e, env, st);
        if self.is_ref(x.ty) {
            return self.ref_op(crate::ir::RefOp::ToBool, vec![x]);
        }
        to_bool(x)
    }

    pub(super) fn val_expr(&mut self, e: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        let x = self.expr(e, env, st);
        to_val(x)
    }

    /// `UNCHANGED e` as a boolean expression.
    pub(super) fn unchanged_expr(&mut self, e: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        let u = hir::Expr::new(H::Builtin { op: B::Unchanged, args: vec![e.clone()] }, e.span);
        self.bool_expr(&u, env, st)
    }

    /// Lower `e` as if primed (`e'`).
    pub(super) fn primed_expr(&mut self, e: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        let saved = std::mem::replace(&mut self.primed, true);
        let x = self.expr(e, env, st);
        self.primed = saved;
        x
    }

    /// Lower an expression (value semantics).
    pub(super) fn expr(&mut self, e: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        let x = self.expr_lowered(e, env, st);
        self.regions_post(e, env, x)
    }

    fn expr_lowered(&mut self, e: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        if let Some(v) = self.const_value(e, env) {
            return const_expr(v);
        }
        if let Some(x) = self.typed_expr(e, env, st) {
            return x;
        }
        match &*e.kind {
            H::Var(v) if !st.init && self.primed => {
                if st.assigned[v.idx()] {
                    self.next_var_expr(v.idx())
                } else {
                    self.interp(e, env)
                }
            }
            H::Var(v) if !st.init => self.var_expr(v.idx()),
            // In Init, variables read the state being built.
            H::Var(v) if st.assigned[v.idx()] && !self.primed => self.next_var_expr(v.idx()),
            H::Builtin { op: B::Prime, args } if !st.init && !self.primed => self.prime_expr(e, &args[0], env, st),
            H::Local(l) => match env.lookup(*l, &self.ip.prog) {
                Some(LBind::Ir(x)) => x,
                Some(LBind::Thunk(te, tenv)) => self.expr(&te, &tenv, st),
                _ => self.interp(e, env),
            },
            H::And(es) => and(es.iter().map(|c| self.bool_expr(c, env, st)).collect()),
            H::Or(es) => or(es.iter().map(|c| self.bool_expr(c, env, st)).collect()),
            H::Builtin { op: B::Not, args } => not(self.bool_expr(&args[0], env, st)),
            H::Builtin { op: B::Implies, args } => {
                let a = self.bool_expr(&args[0], env, st);
                let b = self.bool_expr(&args[1], env, st);
                or(vec![not(a), b])
            }
            H::If { cond, then, els } => {
                if let Some(b) = self.const_bool(cond, env) {
                    return self.expr(if b { then } else { els }, env, st);
                }
                let c = self.bool_expr(cond, env, st);
                let t = self.val_expr(then, env, st);
                let f = self.val_expr(els, env, st);
                Expr::new(Ty::Val, ExprKind::If(c, t, f))
            }
            H::Builtin { op: B::Eq, args } => {
                let a = self.val_expr(&args[0], env, st);
                let b = self.val_expr(&args[1], env, st);
                eq(a, b)
            }
            H::Builtin { op: B::Neq, args } => {
                let a = self.val_expr(&args[0], env, st);
                let b = self.val_expr(&args[1], env, st);
                not(eq(a, b))
            }
            H::Quant { kind, bounds, body } => match self.quant_expr(*kind, bounds, body, env, st) {
                Some(x) => x,
                None => self.interp(e, env),
            },
            H::Choose { vars, set: Some(set), body } if !matches!(vars, BoundVars::Many(ls) if ls.len() != 1) => {
                if let Some(x) = self.typed_choose_fn(vars, set, body, env, st) {
                    return x;
                }
                let unique = self.unique_choice(vars, set, body);
                let set = self.expr(set, env, st);
                if !unique {
                    if let Some(x) = self.verified_choose(vars, &set, body, env, st) {
                        return x;
                    }
                }
                let (set, ety) = self.typed_iter_in(set, unique);
                let t = self.iter_temp(ety, &set);
                match self.bind_elem(vars, &temp_ref(ety, t), env) {
                    Some((env2, check)) => {
                        let b = self.bool_expr(body, &env2, st);
                        Expr::new(ety, ExprKind::Choose { bind: t, set, body: binders::checked(check, b) })
                    }
                    None => self.interp(e, env),
                }
            }
            // A native insertion sort over an encoded sequence when the
            // comparator compiles (lower/maps.rs; one-line hook).
            H::Builtin { op: B::SortSeq, args } if args.len() == 2 => {
                self.typed_sort_seq(&args[0], &args[1], env, st).unwrap_or_else(|| self.interp(e, env))
            }
            H::Builtin { op, args } if is_strict_value_op(*op) => {
                let args = args.iter().map(|a| self.val_expr(a, env, st)).collect();
                self.val_op(*op, args)
            }
            H::Apply { op, args } => match self.inline_apply(*op, args, env, st) {
                Some(x) => x,
                None => self.interp(e, env),
            },
            H::Let { defs, body } => {
                let (env2, lets) = self.let_temps(defs, body, env, st);
                let out = self.expr(body, &env2, st);
                let_in(lets.into_iter().rev(), out)
            }
            _ => self.interp(e, env),
        }
    }

    /// `arg'` (the prime expression `e`) outside a primed context, in Next.
    fn prime_expr(&mut self, e: &hir::Expr, arg: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        if let Some(v) = self.var_of(arg, env) {
            if st.assigned[v] {
                return self.next_var_expr(v);
            }
            return self.interp(e, env);
        }
        let x = self.primed_expr(arg, env, st);
        if !contains_interp(&x) {
            return x;
        }
        self.interp(e, env)
    }

    /// `\A`/`\E x \in S, y \in T : P` as nested quantifiers (sets are
    /// evaluated outside the binders, as in TLA+).
    /// Tuple binders bind the components of typed elements (None if an
    /// element has no typed components).
    fn quant_expr(&mut self, kind: QuantKind, bounds: &[hir::Bound], body: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        if self.some_bound_empty(bounds, env) {
            return Some(bool_lit(kind == QuantKind::Forall));
        }
        let plain = self.quant_loops(kind, bounds, body, env, st)?;
        // A boxed body over a set that depends on an outer binder: unrolled
        // over that binder's constant set if that leaves fewer boxed nodes.
        let boxed = regions::count_boxed(&plain);
        if boxed > 0 {
            if let Some(u) = self.unrolled_quant(kind, bounds, body, env, st) {
                if regions::count_boxed(&u) < boxed {
                    return Some(u);
                }
            }
            // A boxed domain that can still be iterated natively: a constant
            // function applied to a computed index, and an integer interval
            // (with `\cap`). Each is one typed loop per piece, in the order
            // the elements are enumerated in, so that short-circuiting and
            // errors fall where they do in the interpreter. Only a loop the
            // code generators can iterate is taken: the generic lowering is
            // kept whenever it already loops natively (a boxed body alone
            // makes its regions of its own).
            if !loops_native(&plain) {
                for u in [self.const_fn_quant(kind, bounds, body, env, st), self.interval_quant(kind, bounds, body, env, st)]
                    .into_iter()
                    .flatten()
                {
                    if loops_native(&u) {
                        return Some(u);
                    }
                }
            }
        }
        Some(plain)
    }

    /// `\A`/`\E x \in C[i] : P` with a *constant* function `C` (a table
    /// stored in the spec) and a computed integer index: one typed loop per
    /// key of `C`, guarded by the index, and `None` for an index outside
    /// `C`'s domain.
    ///
    /// The generic lowering boxes the whole quantifier instead. A constant
    /// function is one `Val` (its values need not share an encoding: an
    /// empty set and a set of atoms do not), and C cannot loop over a boxed
    /// set, so a table lookup in a domain costs a host region twice - in the
    /// domain of the quantifier and in every `e \in C[i]` of its body.
    /// TLC evaluates the index and then the one set it selects; the chain
    /// does the same, so a key that is not an integer, or not a set, keeps
    /// the generic lowering.
    fn const_fn_quant(&mut self, kind: QuantKind, bounds: &[hir::Bound], body: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        /// One branch per key: a longer table costs the body once per key.
        const MAX_KEYS: usize = 8;
        let [b] = bounds else { return None };
        let BoundVars::Many(ls) = &b.vars else { return None };
        let [l] = ls.as_slice() else { return None };
        let H::FnApp { func, args } = &*b.set.kind else { return None };
        let [idx] = args.as_slice() else { return None };
        let f = self.const_value(func, env)?;
        let keys: Vec<(i64, Value)> = match &f {
            Value::Tuple(vs) => vs.iter().enumerate().map(|(k, v)| (k as i64 + 1, v.clone())).collect(),
            Value::Fcn(ps, _) => ps
                .iter()
                .map(|(k, v)| match k {
                    Value::Int(i) => Some((*i, v.clone())),
                    _ => None,
                })
                .collect::<Option<Vec<_>>>()?,
            _ => return None,
        };
        if keys.is_empty() || keys.len() > MAX_KEYS {
            return None;
        }
        // The guards compare integers: an index that is not one statically
        // may still be no key at all, and the generic lowering reports that.
        let ix = self.expr(idx, env, st);
        let ii = self.as_int(ix).ok()?;
        let (ii, bind) = self.share(ii);
        let mut branches = Vec::with_capacity(keys.len());
        for (k, v) in &keys {
            // An empty value: nothing is bound, and the body is not
            // evaluated at all (TLC enumerates no element).
            if v.is_set() && tlx_value::ops::cardinality(v).ok() == Some(0) {
                branches.push((eq(ii.clone(), int_lit(*k)), bool_lit(kind == QuantKind::Forall)));
                continue;
            }
            let (set, ety) = self.const_iter(v)?;
            let t = self.iter_temp(ety, &set);
            let env2 = env.bind(*l, LBind::Ir(temp_ref(ety, t)));
            let bd = self.bool_expr(body, &env2, st);
            let q = match kind {
                QuantKind::Exists => ExprKind::Exists { bind: t, set, body: bd },
                QuantKind::Forall => ExprKind::Forall { bind: t, set, body: bd },
            };
            branches.push((eq(ii.clone(), int_lit(*k)), Expr::new(Ty::Bool, q)));
        }
        let mut out = Expr::new(Ty::Bool, ExprKind::Fail("Attempted to apply function to an argument not in its domain.".into()));
        for (guard, q) in branches.into_iter().rev() {
            out = Expr::new(Ty::Bool, ExprKind::If(guard, q, out));
        }
        Some(let_in(bind, out))
    }

    /// `\A`/`\E x \in D : P` where `D` is an integer set the generic
    /// lowering boxes but whose elements are still enumerable: an interval
    /// `a..b` with computed bounds, `\cap` of such (the
    /// `(1..Len(x)) \cap (1..Len(y))` of the trace-validation specs) and
    /// `\` of two of them. One typed loop per interval, in ascending order,
    /// so the elements are visited in TLC's order.
    fn interval_quant(&mut self, kind: QuantKind, bounds: &[hir::Bound], body: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let [b] = bounds else { return None };
        let BoundVars::Many(ls) = &b.vars else { return None };
        let [l] = ls.as_slice() else { return None };
        let (visit, skip, binds) = self.int_intervals(&b.set, env, st)?;
        let mut loops = Vec::with_capacity(visit.len());
        for (lo, hi) in visit {
            let set = Expr::new(Ty::Val, ExprKind::IntRange(lo, hi));
            let t = self.iter_temp(Ty::Int, &set);
            let body_env = env.bind(*l, LBind::Ir(temp_ref(Ty::Int, t)));
            let bd = self.bool_expr(body, &body_env, st);
            // The removed intervals are a guard, not a piece: the elements
            // are visited where TLC visits them, and only the ones the
            // difference keeps reach the body.
            let bd = match self.skip_guard(&skip, &temp_ref(Ty::Int, t)) {
                Some(g) if kind == QuantKind::Forall => or(vec![not(g), bd]),
                Some(g) => and(vec![g, bd]),
                None => bd,
            };
            let q = match kind {
                QuantKind::Exists => ExprKind::Exists { bind: t, set, body: bd },
                QuantKind::Forall => ExprKind::Forall { bind: t, set, body: bd },
            };
            loops.push(Expr::new(Ty::Bool, q));
        }
        // The bounds are evaluated once each, in the order the set
        // expression evaluates them, before the first element is visited.
        let out = match kind {
            QuantKind::Forall => and(loops),
            QuantKind::Exists => or(loops),
        };
        Some(let_in(binds.into_iter().rev(), out))
    }

    /// `x \notin (the union of `skip`)` for the element expression `x`, or
    /// `None` when nothing is removed.
    fn skip_guard(&mut self, skip: &[(Expr, Expr)], x: &Expr) -> Option<Expr> {
        let mut inside = Vec::with_capacity(skip.len());
        for (lo, hi) in skip {
            let lo = Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Le, lo.clone(), x.clone()));
            let hi = Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Le, x.clone(), hi.clone()));
            inside.push(and(vec![lo, hi]));
        }
        (!inside.is_empty()).then(|| not(or(inside)))
    }

    /// The intervals to visit for the integer set `e`, the intervals to skip
    /// (the difference removes them from the visited ones), and a binding
    /// for every bound, in the order the set expression evaluates them
    /// (`let_in` takes them the other way round).
    ///
    /// Only an interval `a..b`, an intersection of such, and a difference of
    /// such from such: the intersection of two ascending lists of disjoint
    /// intervals, taken in the order of the factors, is ascending again (a
    /// later interval of one factor is above every element of an earlier
    /// one), and a difference visits its left side, so the pieces may be
    /// visited one after the other. A *union* can need an order that only
    /// the values decide - a later piece of the left operand may sit above
    /// an earlier one of the right - and visiting them out of order would
    /// move where a `\E` stops and where an error is reported.
    fn int_intervals(&mut self, e: &hir::Expr, env: &LEnv, st: &St) -> Option<(Vec<(Expr, Expr)>, Vec<(Expr, Expr)>, Vec<(Temp, Expr)>)> {
        let mut binds = Vec::new();
        let (visit, skip) = self.interval_parts(e, env, st, &mut binds, 0)?;
        Some((visit, skip, binds))
    }

    fn interval_parts(
        &mut self,
        e: &hir::Expr,
        env: &LEnv,
        st: &St,
        binds: &mut Vec<(Temp, Expr)>,
        depth: usize,
    ) -> Option<(Vec<(Expr, Expr)>, Vec<(Expr, Expr)>)> {
        /// One loop per piece; `\cap` multiplies the pieces of its factors.
        const MAX_INTERVALS: usize = 8;
        if depth > 4 {
            return None;
        }
        let H::Builtin { op, args } = &*e.kind else { return None };
        let [a, b] = args.as_slice() else { return None };
        if self.ip.is_builtin_overridden(*op) {
            return None;
        }
        match op {
            B::DotDot => {
                let lo = self.int_bound(a, env, st, binds)?;
                let hi = self.int_bound(b, env, st, binds)?;
                Some((vec![(lo, hi)], Vec::new()))
            }
            B::Cap => {
                let (fa, sa) = self.interval_parts(a, env, st, binds, depth + 1)?;
                let (fb, sb) = self.interval_parts(b, env, st, binds, depth + 1)?;
                // Only two exact lists intersect by pieces; a factor that
                // already removes intervals would need their difference.
                if !sa.is_empty() || !sb.is_empty() {
                    return None;
                }
                let mut out = Vec::with_capacity(fa.len() * fb.len());
                for (alo, ahi) in &fa {
                    for (blo, bhi) in &fb {
                        out.push((imax(alo.clone(), blo.clone()), imin(ahi.clone(), bhi.clone())));
                        if out.len() > MAX_INTERVALS {
                            return None;
                        }
                    }
                }
                Some((out, Vec::new()))
            }
            B::SetMinus => {
                let (fa, sa) = self.interval_parts(a, env, st, binds, depth + 1)?;
                let (fb, sb) = self.interval_parts(b, env, st, binds, depth + 1)?;
                // `(V \ S) \ B` is `V \ (S \cup B)`: the visited intervals
                // stay the left one's and everything removed accumulates.
                if !sb.is_empty() || sa.len() + fb.len() > MAX_INTERVALS {
                    return None;
                }
                let mut skip = sa;
                skip.extend(fb);
                Some((fa, skip))
            }
            _ => None,
        }
    }

    /// One bound of an interval, shared so that the pieces of an
    /// intersection evaluate it once, in this order.
    fn int_bound(&mut self, x: &hir::Expr, env: &LEnv, st: &St, binds: &mut Vec<(Temp, Expr)>) -> Option<Expr> {
        let v = self.expr(x, env, st);
        let i = self.as_int(v).ok()?;
        let (i, bind) = self.share(i);
        binds.extend(bind);
        Some(i)
    }

    /// `quant_expr` as nested loops.
    fn quant_loops(&mut self, kind: QuantKind, bounds: &[hir::Bound], body: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        // (temp, set, tuple binder check) per slot, in binding order.
        let mut slots = Vec::new();
        let mut env2 = env.clone();
        for b in bounds {
            let set = self.expr(&b.set, env, st);
            let (set, ety) = self.typed_iter_in(set, true);
            match &b.vars {
                BoundVars::Many(ls) => {
                    for l in ls {
                        let t = self.iter_temp(ety, &set);
                        env2 = env2.bind(*l, LBind::Ir(temp_ref(ety, t)));
                        slots.push((t, set.clone(), None));
                    }
                }
                BoundVars::Tuple(_) => {
                    let t = self.temp(ety);
                    let (e3, check) = self.bind_elem(&b.vars, &temp_ref(ety, t), &env2)?;
                    env2 = e3;
                    slots.push((t, set, check));
                }
            }
        }
        let body = self.bool_expr(body, &env2, st);
        Some(slots.into_iter().rev().fold(body, |body, (bind, set, check)| {
            let body = binders::checked(check, body);
            let k = match kind {
                QuantKind::Exists => ExprKind::Exists { bind, set, body },
                QuantKind::Forall => ExprKind::Forall { bind, set, body },
            };
            Expr::new(Ty::Bool, k)
        }))
    }

    /// `\A x \in C : \A y \in S(x) : P` (or `\E`) over a small constant `C`
    /// where the set of an inner binder depends on `x` and is constant once
    /// `x` is (`\A len \in 1..N : \A data \in [1..len -> T] : P`): one
    /// conjunct (disjunct) per element of `C`, in TLC's order, so each inner
    /// set is a constant with typed elements. (`\A`/`\E` in expressions do
    /// not depend on the order, see `typed_iter_in`.)
    fn unrolled_quant(&mut self, kind: QuantKind, bounds: &[hir::Bound], body: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        const MAX_UNROLL: usize = 8;
        let first = bounds.first()?;
        let BoundVars::Many(ls) = &first.vars else { return None };
        let l = *ls.first()?;
        // The binders after `x`: the rest of this bound, the other bounds,
        // or (for the last binder) those of a quantifier body of the same kind.
        let mut rest: Vec<hir::Bound> = Vec::new();
        if ls.len() > 1 {
            rest.push(hir::Bound { vars: BoundVars::Many(ls[1..].to_vec()), set: first.set.clone() });
        }
        rest.extend(bounds[1..].iter().cloned());
        let inner_sets: Vec<&hir::Expr> = match (&rest[..], &*body.kind) {
            ([], H::Quant { kind: k, bounds: ib, .. }) if *k == kind => ib.iter().map(|b| &b.set).collect(),
            ([], _) => return None,
            (r, _) => r.iter().map(|b| &b.set).collect(),
        };
        let dependent: Vec<&hir::Expr> = inner_sets
            .into_iter()
            .filter(|s| {
                let mut used = Vec::new();
                self.free_locals(s, &mut used, &mut Vec::new());
                used.contains(&l)
            })
            .collect();
        if dependent.is_empty() {
            return None;
        }
        let set = self.const_value(&first.set, env)?;
        if !set.is_set() || tlx_value::ops::cardinality(&set).ok()? > MAX_UNROLL as i64 {
            return None;
        }
        let elems = tlx_value::ops::enumerate(&set).ok()?;
        // Unrolling only helps when the dependent sets become constants.
        let probe = binders::bind_const(&first.vars, elems.first()?, env)?;
        if dependent.iter().any(|s| self.const_value(s, &probe).is_none()) {
            return None;
        }
        let mut parts = Vec::with_capacity(elems.len());
        for v in &elems {
            let env2 = env.bind(l, LBind::Ir(const_expr(v.clone())));
            let part = if rest.is_empty() {
                self.bool_expr(body, &env2, st)
            } else {
                let q = hir::Expr::new(H::Quant { kind, bounds: rest.clone(), body: body.clone() }, body.span);
                self.bool_expr(&q, &env2, st)
            };
            parts.push(part);
        }
        Some(match kind {
            QuantKind::Forall => and(parts),
            QuantKind::Exists => or(parts),
        })
    }

    /// Inline a user-defined operator application in expression position.
    /// Arguments are passed by name in action-level contexts (as TLC
    /// does), by value (bound to temps) otherwise.
    fn inline_apply(&mut self, op: OpRef, args: &[hir::Expr], env: &LEnv, st: &St) -> Option<Expr> {
        self.inline_with(op, args, env, st, None)
    }

    /// Inline an operator application; with `into`, its body is built
    /// directly in that encoding (destination-driven construction).
    pub(super) fn inline_with(&mut self, op: OpRef, args: &[hir::Expr], env: &LEnv, st: &St, into: Option<ShapeId>) -> Option<Expr> {
        // A LET definition computed once at its LET (see `let_temps`).
        if let (OpRef::Def(d), true, false) = (op, args.is_empty(), self.primed) {
            if let Some(LBind::Ir(x)) = env.lookup(tlx_eval::env::let_cache_key(d), &self.ip.prog) {
                return Some(match into {
                    Some(sid) => self.coerce_enc(x, sid),
                    None => x,
                });
            }
        }
        let (params, body, base, def) = match op {
            OpRef::Def(d) => self.def_target(d, env)?,
            OpRef::Const(c) => match self.ip.const_op_ref(c)? {
                OpRef::Def(d) => self.def_target(d, env)?,
                _ => return None,
            },
            OpRef::Param(l) => match env.lookup(l, &self.ip.prog)? {
                LBind::Op(LOp::Ref(OpRef::Def(d))) => self.def_target(d, env)?,
                LBind::Op(LOp::Lambda(params, body, lenv)) => (params.to_vec(), body, lenv, None),
                _ => return None,
            },
            OpRef::Builtin(_) => return None,
        };
        if params.len() != args.len() || self.inline_stack.len() >= INLINE_DEPTH {
            return None;
        }
        if let Some(d) = def {
            if let Some(x) = self.recursive_call(d, &params, &body, &base, args, env, st, into) {
                return Some(x);
            }
        }
        if let Some(d) = def {
            // RECURSIVE operators that do not compile to a function are
            // unrolled a few levels; a deeper call is evaluated by the
            // interpreter. Only linear recursion (one self-call) is
            // unrolled: otherwise the unrolled code grows exponentially. (A
            // definition that cannot call itself is on the stack again when
            // an application of it was passed to it as a lazily lowered
            // argument, `Wrap(Wrap(x))`: that is no recursion.)
            let depth = self.inline_stack.iter().filter(|x| **x == d).count();
            let deep = depth >= RECURSION_UNROLL && !(depth < CONST_RECURSION_UNROLL && self.const_driven(&params, args, env));
            if depth > 0 && self.ip.is_recursive(d) && (deep || self_calls(&body, d) != 1) {
                let call = hir::Expr::new(H::Apply { op, args: args.to_vec() }, body.span);
                let x = self.interp(&call, env);
                return Some(match into {
                    Some(sid) => self.coerce_enc(x, sid),
                    None => x,
                });
            }
        }
        let by_name = !st.init && def.is_none_or(|d| self.ip.is_action_level(d));
        // Definitions TLC overrides by Java methods (standard and community
        // modules) evaluate every argument, used or not (the
        // interpreter's `bind_params` without `defer_errors`).
        let eager = !by_name && !self.defers_arg_errors(def, &body);
        let mut env2 = base;
        let mut lets: Vec<(Temp, Expr)> = Vec::new();
        for (p, a) in params.iter().zip(args) {
            let b = if self.ip.prog.locals[p.idx()].arity > 0 {
                LBind::Op(self.op_arg(a, env).ok()?)
            } else if !eager
                && (by_name
                    || (self.constructs(a, env) && (local_uses(&self.ip.prog, &body, *p) <= 1 || self.is_product_literal(a, env)))
                    || self.is_lazy_fn_ref(a, env))
            {
                // Constructor arguments stay unevaluated (TLC passes
                // arguments lazily) so that projections like `p[1]` / `p.f`
                // in the body select the component expression directly;
                // so do function definitions, applied in the body like the
                // definition itself (see `inline_fn_def`).
                LBind::Thunk(a.clone(), env.clone())
            } else {
                let x = self.expr(a, env, st);
                let (x, binding) = self.share(x);
                lets.extend(binding);
                LBind::Ir(x)
            };
            env2 = env2.bind(*p, b);
        }
        if let Some(d) = def {
            self.inline_stack.push(d);
        }
        let out = match into {
            Some(sid) => self.expr_into(&body, &env2, st, sid),
            None => self.expr(&body, &env2, st),
        };
        if def.is_some() {
            self.inline_stack.pop();
        }
        Some(let_in(lets.into_iter().rev(), out))
    }

    /// `f[a]` / `f[a, b, ...]` for a function definition
    /// `f[x \in S, y \in T, ...] == body` (not precomputed): inlined with
    /// the binders bound to the arguments (checked to be in their domains;
    /// the function is applied lazily, as TLC does). Recursive definitions
    /// are compiled functions (see `recursive_fn_call`), else unrolled like
    /// RECURSIVE operators (linear recursion only; deeper
    /// applications are evaluated by the interpreter).
    pub(super) fn inline_fn_def(&mut self, func: &hir::Expr, args: &[hir::Expr], env: &LEnv, st: &St) -> Option<Expr> {
        self.inline_fn_def_into(func, args, env, st, None)
    }

    /// `inline_fn_def`; with `into`, a recursive definition is compiled to
    /// a function returning that encoding.
    pub(super) fn inline_fn_def_into(
        &mut self,
        func: &hir::Expr,
        args: &[hir::Expr],
        env: &LEnv,
        st: &St,
        into: Option<ShapeId>,
    ) -> Option<Expr> {
        let (d, denv) = self.fn_def_of(func, env)?;
        let DefKind::Fn { bounds, body } = &self.ip.prog.defs[d.idx()].kind else { return None };
        // The binders (a local or a tuple binder) with their domains.
        let mut vars: Vec<(BoundVars, hir::Expr)> = Vec::new();
        for b in bounds {
            match &b.vars {
                BoundVars::Many(vs) => vars.extend(vs.iter().map(|v| (BoundVars::Many(vec![*v]), b.set.clone()))),
                BoundVars::Tuple(_) => vars.push((b.vars.clone(), b.set.clone())),
            }
        }
        // The arguments: one per binder (`f[a, b]`, or `f[<<a, b>>]`).
        let args: Vec<(hir::Expr, LEnv)> = if args.len() == vars.len() {
            args.iter().map(|a| (a.clone(), env.clone())).collect()
        } else if args.len() == 1 && vars.len() > 1 {
            let (t, tenv) = self.peel(&args[0], env)?;
            let H::Tuple(es) = &*t.kind else { return None };
            if es.len() != vars.len() {
                return None;
            }
            es.iter().map(|a| (a.clone(), tenv.clone())).collect()
        } else {
            return None;
        };
        let calls = self.calls_through_lets(body, d);
        if calls > 0 {
            if let Some(x) = self.recursive_fn_call(d, &vars, body, &args, &denv, calls, into, st) {
                return Some(x);
            }
        }
        // Else linear recursion only (possibly through LET definitions).
        if calls > 1 {
            return None;
        }
        let depth = self.inline_stack.iter().filter(|x| **x == d).count();
        if calls == 0 && depth > 0 {
            return None;
        }
        let const_args = depth < CONST_RECURSION_UNROLL && args.iter().all(|(a, aenv)| self.const_value(a, aenv).is_some());
        if depth >= RECURSION_UNROLL && !const_args {
            // Deeper applications are evaluated by the interpreter,
            // in the result representation the unrolling assumes.
            let ty = self.fn_result.iter().rev().find(|(x, _)| *x == d).map_or(Ty::Val, |(_, t)| *t);
            let app = hir::Expr::new(H::FnApp { func: func.clone(), args: args.iter().map(|(a, _)| a.clone()).collect() }, func.span);
            let x = self.interp(&app, env);
            return Some(match ty {
                Ty::Val => x,
                Ty::Int | Ty::Bool => Expr::new(ty, ExprKind::Convert(x)),
                Ty::Enc(sid) => self.coerce_enc(x, sid),
            });
        }
        if depth == 0 && calls == 1 {
            // The result type is not known before lowering the body: assume
            // a scalar one and keep the first assumption the unrolling
            // confirms (else the result is boxed).
            let mut ty = Ty::Int;
            loop {
                self.fn_result.push((d, ty));
                let out = self.inline_fn_level(d, &vars, body, &args, &denv, st);
                self.fn_result.pop();
                match out.as_ref().map(|x| x.ty) {
                    None => return None,
                    Some(t) if t == ty || ty == Ty::Val => return out,
                    // Retry with the type the unrolling produced (if scalar).
                    Some(Ty::Bool) if ty == Ty::Int => ty = Ty::Bool,
                    _ => ty = Ty::Val,
                }
            }
        }
        self.inline_fn_level(d, &vars, body, &args, &denv, st)
    }

    /// The arguments of a recursive call are compile-time constants, passed
    /// through unchanged (`params[i]` as argument `i`) or operators.
    fn const_driven(&self, params: &[LocalId], args: &[hir::Expr], env: &LEnv) -> bool {
        params.iter().zip(args).all(|(p, a)| {
            self.ip.prog.locals[p.idx()].arity > 0 || matches!(&*a.kind, H::Local(l) if l == p) || self.const_value(a, env).is_some()
        })
    }

    /// `e` denotes a function definition (see `fn_def_of`) with constant
    /// domains: passing it by name cannot skip an error.
    fn is_lazy_fn_ref(&self, e: &hir::Expr, env: &LEnv) -> bool {
        let Some((d, denv)) = self.fn_def_of(e, env) else { return false };
        let DefKind::Fn { bounds, .. } = &self.ip.prog.defs[d.idx()].kind else { return false };
        let benv = self.def_env(d, &denv);
        bounds.iter().all(|b| self.const_value(&b.set, &benv).is_some())
    }

    /// The function definition `f[x \in S] == ...` (not precomputed) that
    /// `func` denotes (through 0-ary definitions and by-name arguments), and
    /// the environment of its use.
    fn fn_def_of(&self, func: &hir::Expr, env: &LEnv) -> Option<(hir::DefId, LEnv)> {
        let (mut e, mut env) = (func.clone(), env.clone());
        for _ in 0..16 {
            match &*e.kind {
                H::Local(l) => match env.lookup(*l, &self.ip.prog) {
                    Some(LBind::Thunk(x, xenv)) => (e, env) = (x, xenv),
                    _ => return None,
                },
                H::Apply { op: OpRef::Def(d), args } if args.is_empty() => {
                    let d = self.ip.redirect_def(*d);
                    if self.ip.has_def_value(d) || self.ip.prog.defs[d.idx()].builtin.is_some() {
                        return None;
                    }
                    match &self.ip.prog.defs[d.idx()].kind {
                        DefKind::Fn { .. } => return Some((d, env)),
                        DefKind::Op(body) if !self.inline_stack.contains(&d) => {
                            let base = self.def_env(d, &env);
                            (e, env) = (body.clone(), base);
                        }
                        _ => return None,
                    }
                }
                _ => return None,
            }
        }
        None
    }

    /// One level of `inline_fn_def`: `body` with the binders bound to `args`
    /// (each in its environment); `env` is the environment of the use of
    /// the definition.
    fn inline_fn_level(
        &mut self,
        d: hir::DefId,
        vars: &[(BoundVars, hir::Expr)],
        body: &hir::Expr,
        args: &[(hir::Expr, LEnv)],
        env: &LEnv,
        st: &St,
    ) -> Option<Expr> {
        let mut benv = self.def_env(d, env);
        let mut binds = Vec::new();
        let mut checks = Vec::new();
        for ((vars, set), (arg, aenv)) in vars.iter().zip(args) {
            if let BoundVars::Tuple(ls) = vars {
                let in_dom = self.bind_tuple_arg(ls, set, arg, aenv, &mut benv, &mut binds, st)?;
                checks.push(in_dom);
                continue;
            }
            let v = vars.locals()[0];
            let a = self.expr(arg, aenv, st);
            if a.ty == Ty::Val && !matches!(&*a.kind, ExprKind::Const(_)) {
                return None;
            }
            let (a, bind) = self.share(a);
            binds.extend(bind);
            benv = benv.bind(v, LBind::Ir(a));
            let x = hir::Expr::new(H::Local(v), set.span);
            let in_dom = self.typed_in(&x, set, &benv, st);
            if in_dom.ty != Ty::Bool {
                return None;
            }
            checks.push(in_dom);
        }
        self.inline_stack.push(d);
        let out = self.expr(body, &benv, st);
        self.inline_stack.pop();
        let fail = Expr::new(out.ty, ExprKind::Fail("Attempted to apply function to an argument not in its domain.".into()));
        let in_dom = if checks.len() == 1 { checks.pop().unwrap() } else { and(checks) };
        Some(let_in(binds.into_iter().rev(), Expr::new(out.ty, ExprKind::If(in_dom, out, fail))))
    }

    /// Bind the tuple binder `ls` (of domain `set`) of a function definition
    /// to the argument `arg`: a tuple literal binds its lowered components,
    /// a constant its components, an encoded tuple its slots. Returns the
    /// domain check (`arg \in set`, after which the argument is known to be
    /// a tuple of the binder's length).
    #[allow(clippy::too_many_arguments)]
    fn bind_tuple_arg(
        &mut self,
        ls: &[LocalId],
        set: &hir::Expr,
        arg: &hir::Expr,
        aenv: &LEnv,
        benv: &mut LEnv,
        binds: &mut Vec<(Temp, Expr)>,
        st: &St,
    ) -> Option<Expr> {
        if let Some((t, tenv)) = self.peel(arg, aenv) {
            if let H::Tuple(es) = &*t.kind {
                if es.len() != ls.len() {
                    return None;
                }
                // The components, then `<<l1, ..., ln>> \in set`.
                for (l, c) in ls.iter().zip(es) {
                    let x = self.expr(c, &tenv, st);
                    if x.ty == Ty::Val && !matches!(&*x.kind, ExprKind::Const(_)) {
                        return None;
                    }
                    let (x, bind) = self.share(x);
                    binds.extend(bind);
                    *benv = benv.bind(*l, LBind::Ir(x));
                }
                let span = set.span;
                let tuple = hir::Expr::new(H::Tuple(ls.iter().map(|l| hir::Expr::new(H::Local(*l), span)).collect()), span);
                let in_dom = self.typed_in(&tuple, set, benv, st);
                return (in_dom.ty == Ty::Bool).then_some(in_dom);
            }
        }
        let a = self.expr(arg, aenv, st);
        let (a, bind) = self.share(a);
        binds.extend(bind);
        let parts: Vec<Expr> = match &*a.kind {
            ExprKind::Const(Value::Tuple(vs)) if vs.len() == ls.len() => vs.iter().map(|v| const_expr(v.clone())).collect(),
            _ if a.ty == Ty::Val => return None,
            // Once in the domain, the argument is a tuple of the binder's
            // length (or the definition's domain is not made of such
            // tuples: then binding is an error the check does not make).
            _ => match self.tuple_parts(ls.len(), &a)? {
                (parts, None) => parts,
                (_, Some(_)) => return None,
            },
        };
        for (l, p) in ls.iter().zip(parts) {
            *benv = benv.bind(*l, LBind::Ir(p));
        }
        let in_dom = self.member_of(a, set, benv, st);
        (in_dom.ty == Ty::Bool).then_some(in_dom)
    }

    /// Syntactic applications of definition `d` in `e`, including in the
    /// bodies of the LET definitions of `e`.
    fn calls_through_lets(&self, e: &hir::Expr, d: hir::DefId) -> usize {
        let mut n = self_calls(e, d);
        let mut lets = Vec::new();
        collect_lets(e, &mut lets);
        for l in lets {
            if let DefKind::Op(body) = &self.ip.prog.defs[l.idx()].kind {
                n += self.calls_through_lets(body, d);
            }
        }
        n
    }

    /// Whether the operator (definition `def`, else a LAMBDA with `body`)
    /// takes its arguments lazily, so that an unused failing argument is no
    /// error (see `Interp::defers_arg_errors`).
    pub(super) fn defers_arg_errors(&self, def: Option<hir::DefId>, body: &hir::Expr) -> bool {
        match def {
            Some(d) => self.ip.defers_arg_errors(d),
            None => self.ip.lambda_defers_arg_errors(body.span.file),
        }
    }

    /// A record or tuple literal (behind definitions / by-name arguments):
    /// projections of it select components without building it.
    fn is_product_literal(&self, e: &hir::Expr, env: &LEnv) -> bool {
        self.peel(e, env).is_some_and(|(p, _)| matches!(&*p.kind, H::Record(_) | H::Tuple(_)))
    }

    /// Interpreter fallback: binds every IR-bound local the expression uses
    /// (transitively through LET definitions, call-by-name arguments and
    /// operator arguments).
    pub(super) fn interp(&mut self, e: &hir::Expr, env: &LEnv) -> Expr {
        if self.primed {
            // Inside a primed expression: the interpreter evaluates `e'`.
            let p = hir::Expr::new(H::Builtin { op: B::Prime, args: vec![e.clone()] }, e.span);
            self.primed = false;
            let x = self.interp(&p, env);
            self.primed = true;
            return x;
        }
        let mut c = Captures { binds: Vec::new(), deferred: Vec::new(), base: env.base.clone(), done: Vec::new() };
        let mut used = Vec::new();
        self.free_locals(e, &mut used, &mut Vec::new());
        for l in used {
            self.capture(l, env, &mut c);
        }
        Expr::new(Ty::Val, ExprKind::Interp { expr: e.clone(), binds: c.binds, deferred: c.deferred, env: c.base })
    }

    /// Capture local `l` (and, for by-name and operator arguments, the
    /// locals they use) for an interpreter fallback.
    fn capture(&self, l: LocalId, env: &LEnv, c: &mut Captures) {
        if c.done.contains(&l) {
            return;
        }
        c.done.push(l);
        let Some(b) = env.binds.iter().rev().find(|(x, _)| *x == l).map(|(_, b)| b.clone()) else {
            return; // bound in the constant base environment (or inside the expression)
        };
        match b {
            LBind::Ir(x) => c.binds.push((l, to_val(x))),
            LBind::Thunk(te, tenv) => {
                self.capture_free(&te, &tenv, c);
                let once = self.single_valued(&te, &tenv, 0);
                c.deferred.push(if once { Deferred::Once(l, te) } else { Deferred::Thunk(l, te) });
            }
            LBind::Op(LOp::Ref(r)) => c.deferred.push(Deferred::OpRef(l, r)),
            LBind::Op(LOp::Lambda(params, body, lenv)) => {
                self.capture_free(&body, &lenv, c);
                c.deferred.push(Deferred::Lambda(l, params, body));
            }
        }
    }

    /// Whether by-name argument `e` (bound in `env`) has one value in a
    /// given (unprimed) context: deterministic, without effects and not
    /// action-level, also through the LET definitions it calls and the
    /// by-name arguments it reads. Its first evaluation can then serve every
    /// use, as when the interpreter evaluates the argument at the call.
    fn single_valued(&self, e: &hir::Expr, env: &LEnv, depth: usize) -> bool {
        if depth > 8 || self.expr_volatile(e) || self.action_level_expr(e) {
            return false;
        }
        let mut used = Vec::new();
        self.free_locals(e, &mut used, &mut Vec::new());
        used.iter().all(|l| {
            if tlx_eval::env::is_let_cache_key(*l) {
                return true;
            }
            match env.lookup(*l, &self.ip.prog) {
                None | Some(LBind::Ir(_)) => true,
                Some(LBind::Thunk(te, tenv)) => self.single_valued(&te, &tenv, depth + 1),
                Some(LBind::Op(_)) => false,
            }
        })
    }

    /// Whether `e` (with the LET definitions it calls) may observe the next
    /// state or apply an operator argument.
    fn action_level_expr(&self, e: &hir::Expr) -> bool {
        let here = match &*e.kind {
            H::Builtin { op: B::Prime | B::Unchanged | B::Enabled | B::Always | B::Eventually | B::LeadsTo, .. }
            | H::BoxAction { .. }
            | H::AngleAction { .. }
            | H::Fairness { .. }
            | H::TemporalQuant { .. }
            | H::Apply { op: OpRef::Param(_), .. } => true,
            H::Apply { op: OpRef::Def(d), .. } | H::OpArg(OpRef::Def(d)) => self.ip.is_action_level(*d),
            H::Apply { op: OpRef::Const(c), .. } => match self.ip.const_op_ref(*c) {
                Some(OpRef::Def(d)) => self.ip.is_action_level(d),
                Some(OpRef::Builtin(_)) => false,
                _ => true,
            },
            H::Let { defs, .. } => defs.iter().any(|d| self.ip.is_action_level(*d)),
            _ => false,
        };
        let mut found = here;
        if !found {
            tlx_sema::visit::children(e, &mut |c| found = found || self.action_level_expr(c));
        }
        found
    }

    /// Capture the locals of deferred expression `e` (bound in `env`).
    fn capture_free(&self, e: &hir::Expr, env: &LEnv, c: &mut Captures) {
        c.base = c.base.extend_from(&env.base);
        let mut used = Vec::new();
        self.free_locals(e, &mut used, &mut Vec::new());
        for u in used {
            self.capture(u, env, c);
        }
    }

    /// Locals referenced by `e`, including inside the LET definitions it calls.
    pub(super) fn free_locals(&self, e: &hir::Expr, out: &mut Vec<LocalId>, seen: &mut Vec<hir::DefId>) {
        match &*e.kind {
            H::Local(l) | H::Apply { op: OpRef::Param(l), .. } | H::OpArg(OpRef::Param(l)) => {
                if !out.contains(l) {
                    out.push(*l);
                }
            }
            H::Apply { op: OpRef::Def(d), .. } | H::OpArg(OpRef::Def(d)) if self.ip.prog.def_is_let(*d) && !seen.contains(d) => {
                seen.push(*d);
                // Its value, if computed once at its LET (see `let_temps`).
                out.push(tlx_eval::env::let_cache_key(*d));
                match &self.ip.prog.defs[d.idx()].kind {
                    DefKind::Op(body) => self.free_locals(body, out, seen),
                    DefKind::Fn { bounds, body } => {
                        for b in bounds {
                            self.free_locals(&b.set, out, seen);
                        }
                        self.free_locals(body, out, seen);
                    }
                    DefKind::Pending => {}
                }
            }
            _ => {}
        }
        tlx_sema::visit::children(e, &mut |c| self.free_locals(c, out, seen));
    }
}

/// What an interpreter fallback captures from the lowering environment.
struct Captures {
    /// IR values of locals.
    binds: Vec<(LocalId, Expr)>,
    /// By-name and operator arguments, bound lazily in this order.
    deferred: Vec<Deferred>,
    /// The constant environment (extended by those of deferred arguments).
    base: Env,
    /// Locals already captured.
    done: Vec<LocalId>,
}

/// Builtins that are pure functions of their (evaluated) arguments.
fn is_strict_value_op(op: B) -> bool {
    op.is_strict_value_op()
}

fn contains_interp(e: &Expr) -> bool {
    let mut found = matches!(&*e.kind, ExprKind::Interp { .. });
    if !found {
        e.for_each_child(&mut |c| found |= contains_interp(c));
    }
    found
}

/// Number of references to local `l` in `e`, including the bodies of the
/// LET definitions of `e` (each lowered where it is applied).
fn local_uses(prog: &tlx_sema::Program, e: &hir::Expr, l: LocalId) -> usize {
    let mut n = matches!(&*e.kind, H::Local(x) if *x == l) as usize;
    if let H::Let { defs, .. } = &*e.kind {
        for d in defs {
            if let DefKind::Op(b) = &prog.defs[d.idx()].kind {
                n += local_uses(prog, b, l);
            }
        }
    }
    tlx_sema::visit::children(e, &mut |c| n += local_uses(prog, c, l));
    n
}

/// The LET definitions in `e`.
fn collect_lets(e: &hir::Expr, out: &mut Vec<hir::DefId>) {
    if let H::Let { defs, .. } = &*e.kind {
        out.extend(defs);
    }
    tlx_sema::visit::children(e, &mut |c| collect_lets(c, out));
}

/// Number of syntactic calls of definition `d` in `e`.
fn self_calls(e: &hir::Expr, d: hir::DefId) -> usize {
    let here = matches!(&*e.kind, H::Apply { op: OpRef::Def(x), .. } if *x == d) as usize;
    let mut n = here;
    tlx_sema::visit::children(e, &mut |c| n += self_calls(c, d));
    n
}

/// `max(a, b)` of two integer expressions, both evaluated (in order).
fn imax(a: Expr, b: Expr) -> Expr {
    let lt = Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Lt, a.clone(), b.clone()));
    Expr::new(Ty::Int, ExprKind::If(lt, b, a))
}

/// `min(a, b)` of two integer expressions, both evaluated (in order).
fn imin(a: Expr, b: Expr) -> Expr {
    let lt = Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Lt, a.clone(), b.clone()));
    Expr::new(Ty::Int, ExprKind::If(lt, a, b))
}

/// Whether every quantifier of `e` loops over a source the code generators
/// can iterate: a boxed source makes the whole quantifier one host region,
/// whatever its body (a boxed body alone becomes regions of its own).
fn loops_native(e: &Expr) -> bool {
    let here = match &*e.kind {
        ExprKind::Exists { set, .. } | ExprKind::Forall { set, .. } | ExprKind::Choose { set, .. } => set.is_typed_source(),
        _ => true,
    };
    let mut ok = here;
    e.for_each_child(&mut |c| ok = ok && loops_native(c));
    ok
}
