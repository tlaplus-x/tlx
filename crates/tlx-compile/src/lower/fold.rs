//! Folds (`MapThenFoldSet` from the Folds module, which `FoldSet`,
//! `FoldFunction`, `SumSet`, ... are built on), unrolled when the order of
//! the elements is known at compile time.
//!
//! `MapThenFoldSet(op, base, f, choose, S)` takes x1 = choose(S),
//! x2 = choose(S \ {x1}), ... and computes op(f(x1), op(f(x2), ... base)).
//! With the usual `choose(s) == CHOOSE x \in s : TRUE` the elements come in
//! ascending (TLC) order, so the fold is unrolled from the largest element
//! down. `S` may be a constant set or `1..Len(s)` of an encoded sequence
//! (unrolled up to its capacity, each step guarded by the length).
//!
//! `FoldFunction(op, base, fun)` / `FoldSeq(op, base, seq)` (Java overrides
//! in TLC: `acc = op(fun[i], acc)` for `i` in `DOMAIN fun` in TLC order) are
//! unrolled over the domain of an encoded function, tuple, record or
//! sequence (up to its capacity, each step guarded by the length).

use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{self, BoundVars, ExprKind as H, OpRef};
use tlx_value::Value;

use super::*;

impl Lowerer<'_> {
    pub(super) fn typed_fold(&mut self, args: &[hir::Expr], env: &LEnv, st: &St) -> Option<Expr> {
        let [op, base, f, choose, set] = args else { return None };
        if !self.is_min_chooser(choose, env) {
            return None;
        }
        let op = self.op_arg(op, env).ok()?;
        let f = self.op_arg(f, env).ok()?;
        let s = self.expr(set, env, st);
        // The elements, in ascending order, each with an optional guard.
        let mut len_bind = None;
        let elems: Vec<(Expr, Option<Expr>)> = match &*s.kind {
            ExprKind::Const(v) => {
                let es = tlx_value::ops::enumerate_normalized(v).ok()?;
                if es.len() > 64 {
                    return None;
                }
                es.into_iter().map(|e| (const_expr(e), None)).collect()
            }
            ExprKind::ValOp { op: B::DotDot, args } => {
                let lo = self.as_int(args[0].clone()).ok()?;
                let hi = self.as_int(args[1].clone()).ok()?;
                let (ExprKind::Const(Value::Int(1)), ExprKind::SeqLen(seq)) = (&*lo.kind, &*hi.kind) else { return None };
                let Some(Shape::Seq { max_len, .. }) = self.shape_of(seq.ty).cloned() else { return None };
                if max_len > 64 {
                    return None;
                }
                let (len, bind) = self.share(hi.clone());
                len_bind = bind;
                (1..=max_len as i64)
                    .map(|i| (int_lit(i), Some(Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Le, int_lit(i), len.clone())))))
                    .collect()
            }
            _ => return self.sum_fold(&op, base, Some(&f), s, env, st),
        };
        // The accumulator takes the encoding of f(x).
        let (first, _) = elems.first()?;
        let probe = self.apply_op_lowered(&f, vec![first.clone()], env, st, None)?;
        let Ty::Enc(sid) = probe.ty else { return None };
        let b = self.expr_into(base, env, st, sid);
        let mut acc = self.coerce_enc(b, sid);
        for (x, guard) in elems.into_iter().rev() {
            let fx = self.apply_op_lowered(&f, vec![x], env, st, None)?;
            let (prev, bind) = self.share(acc);
            let step = self.apply_op_lowered(&op, vec![fx, prev.clone()], env, st, Some(sid))?;
            let step = self.coerce_enc(step, sid);
            let next = match guard {
                Some(g) => Expr::new(Ty::Enc(sid), ExprKind::If(g, step, prev)),
                None => step,
            };
            acc = let_in(bind, next);
        }
        Some(let_in(len_bind, acc))
    }

    /// `FoldSet(op, base, S)` (FiniteSetsExt): `acc = op(x, acc)` over S in
    /// TLC's order; a sum over an encoded set (see `sum_fold`).
    pub(super) fn typed_fold_set(&mut self, args: &[hir::Expr], env: &LEnv, st: &St) -> Option<Expr> {
        let [op, base, set] = args else { return None };
        let op = self.op_arg(op, env).ok()?;
        let s = self.expr(set, env, st);
        self.sum_fold(&op, base, None, s, env, st)
    }

    /// `base + f(x1) + f(x2) + ...` over the elements of the encoded set
    /// `s` (`f` absent: the elements themselves) when `op` is the integer
    /// `+`: a `Fold` in the encoded order. Only when the base and every
    /// addend have the same sign by their static ranges: the partial sums
    /// then grow monotonically, so they overflow in any order exactly when
    /// the total does (as it does in TLC's order).
    fn sum_fold(&mut self, op: &LOp, base: &hir::Expr, f: Option<&LOp>, s: Expr, env: &LEnv, st: &St) -> Option<Expr> {
        if !matches!(op, LOp::Ref(OpRef::Builtin(B::Plus))) || self.ip.is_builtin_overridden(B::Plus) {
            return None;
        }
        let s = self.set_operand(s);
        if !matches!(self.shape_of(s.ty), Some(Shape::Set { .. })) {
            return None;
        }
        let (src, ety) = self.typed_iter_in(s, true);
        if !src.is_typed_source() {
            return None;
        }
        let t = self.iter_temp(ety, &src);
        let x = temp_ref(ety, t);
        let body = match f {
            Some(f) => self.apply_op_lowered(f, vec![x], env, st, None)?,
            None => x,
        };
        let body = self.as_int(body).ok()?;
        let b = self.expr(base, env, st);
        let b = self.as_int(b).ok()?;
        let ((bl, bh), (xl, xh)) = (self.int_range(&b)?, self.int_range(&body)?);
        if !(bl >= 0 && xl >= 0 || bh <= 0 && xh <= 0) {
            return None;
        }
        let sum = Expr::new(Ty::Int, ExprKind::Fold { product: false, bind: t, set: src, body });
        Some(Expr::new(Ty::Int, ExprKind::IntBin(IntOp::Add, b, sum)))
    }

    /// `FoldFunctionOnSet(op, base, fun, indices)` with `indices` the whole
    /// (fixed) domain of an encoded `fun` (e.g. `SumFunction`): as
    /// `FoldFunction(op, base, fun)`, which folds over the domain in the
    /// same order.
    pub(super) fn typed_fold_function_on_set(&mut self, args: &[hir::Expr], env: &LEnv, st: &St) -> Option<Expr> {
        let [op, base, fun, indices] = args else { return None };
        let f = self.expr(fun, env, st);
        let f = self.encode_const_fn(f);
        let shape = self.shape_of(f.ty)?.clone();
        if !matches!(shape, Shape::Fcn { .. } | Shape::Tuple(_) | Shape::Record(_)) {
            return None;
        }
        let dom = Value::set_from(self.slots(&shape)?.into_iter().map(|(d, _, _)| d).collect()).ok()?;
        let idx = self.expr(indices, env, st);
        let ExprKind::Const(iv) = &*idx.kind else { return None };
        if iv.normalize().ok()? != dom.normalize().ok()? {
            return None;
        }
        self.typed_fold_function(&[op.clone(), base.clone(), fun.clone()], env, st)
    }

    /// `FoldFunction(op, base, fun)` and `FoldSeq(op, base, fun)`: unrolled
    /// over the domain of `fun` when its encoding fixes the domain (or
    /// bounds a sequence's length). The accumulator takes the encoding of
    /// the range (an integer when the range is one).
    pub(super) fn typed_fold_function(&mut self, args: &[hir::Expr], env: &LEnv, st: &St) -> Option<Expr> {
        let [op, base, fun] = args else { return None };
        let op = self.op_arg(op, env).ok()?;
        if self.is_literal_op(&op, env) {
            return None;
        }
        let f = self.expr(fun, env, st);
        let f = self.encode_const_fn(f);
        let shape = self.shape_of(f.ty)?.clone();
        let (f, f_bind) = self.share(f);
        // The elements f[i] in TLC's order of the domain, each with an
        // optional guard.
        let mut len_bind = None;
        let elems: Vec<(Expr, Option<Expr>)> = match &shape {
            Shape::Seq { elem, max_len } => {
                if *max_len > 64 {
                    return None;
                }
                let (len, bind) = self.share(Expr::new(Ty::Int, ExprKind::SeqLen(f.clone())));
                len_bind = bind;
                (1..=*max_len as i64)
                    .map(|i| {
                        let x = self.seq_index(f.clone(), int_lit(i), elem);
                        (x, Some(Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Le, int_lit(i), len.clone()))))
                    })
                    .collect()
            }
            Shape::Fcn { .. } | Shape::Tuple(_) | Shape::Record(_) => {
                let slots = self.slots(&shape)?;
                if slots.len() > 64 {
                    return None;
                }
                let dom = Value::set_from(slots.iter().map(|(d, _, _)| d.clone()).collect()).ok()?;
                let order = tlx_value::ops::enumerate_normalized(&dom).ok()?;
                let mut out = Vec::with_capacity(order.len());
                for k in order {
                    let (_, loc, sh) = slots.iter().find(|(d, _, _)| *d == k)?;
                    let ssid = self.sid(sh);
                    out.push((Expr::new(Ty::Enc(ssid), ExprKind::Slice { base: f.clone(), loc: *loc }), None));
                }
                out
            }
            _ => return None,
        };
        let binds = |x: Expr| let_in(f_bind.clone().into_iter().chain(len_bind.clone()), x);
        let Some((first, _)) = elems.first() else {
            return Some(binds(self.expr(base, env, st)));
        };
        let Ty::Enc(esid) = first.ty else { return None };
        // The accumulator: an unboxed integer or boolean when the base is
        // one; otherwise the encoding of the elements (or of the base, if
        // of another kind) with its integers widened to all TLC integers:
        // the accumulated values leave the ranges of the elements (e.g.
        // DyadicRationals sums).
        let b = self.expr(base, env, st);
        let kind = |l: &Self, s: ShapeId| l.typing.shape(s).kind_key();
        let acc_ty = match (b.ty, &*b.kind) {
            (Ty::Int, _) | (Ty::Val, ExprKind::Const(Value::Int(_))) => Ty::Int,
            (Ty::Bool, _) | (Ty::Val, ExprKind::Const(Value::Bool(_))) => Ty::Bool,
            (Ty::Enc(bs), _) if kind(self, bs) != kind(self, esid) => Ty::Enc(bs),
            _ => Ty::Enc(esid),
        };
        let acc_ty = match acc_ty {
            Ty::Enc(s) if matches!(self.typing.shape(s), Shape::Int { .. }) => Ty::Int,
            Ty::Enc(s) => {
                let wide = widen_ints(self.typing.shape(s));
                Ty::Enc(self.sid(&wide))
            }
            t => t,
        };
        let fit = |l: &mut Self, x: Expr| -> Option<Expr> {
            match acc_ty {
                Ty::Int => l.as_int(x).ok(),
                Ty::Bool => l.as_bool(x).ok(),
                Ty::Enc(s) => Some(l.coerce_enc(x, s)),
                _ => None,
            }
        };
        let mut acc = fit(self, b)?;
        for (x, guard) in elems {
            let (prev, bind) = self.share(acc);
            let into = match acc_ty {
                Ty::Enc(s) => Some(s),
                _ => None,
            };
            let step = self.apply_op_lowered(&op, vec![x, prev.clone()], env, st, into)?;
            let step = fit(self, step)?;
            let next = match guard {
                Some(g) => Expr::new(step.ty, ExprKind::If(g, step, prev)),
                None => step,
            };
            acc = let_in(bind, next);
        }
        Some(binds(acc))
    }

    /// `op` is a lambda or user operator whose body is a bare numeric or
    /// string literal, which TLC's native overrides reject upfront
    /// (`Interp::native_op_val`).
    fn is_literal_op(&self, op: &LOp, env: &LEnv) -> bool {
        match op {
            LOp::Lambda(_, body, _) => matches!(&*body.kind, H::Num(_) | H::Str(_)),
            LOp::Ref(OpRef::Def(d)) => self.def_target(*d, env).is_some_and(|(_, body, _, _)| matches!(&*body.kind, H::Num(_) | H::Str(_))),
            _ => false,
        }
    }

    /// `LAMBDA s : CHOOSE x \in s : TRUE` (or an operator defined so).
    fn is_min_chooser(&self, choose: &hir::Expr, env: &LEnv) -> bool {
        let (params, body) = match &*choose.kind {
            H::Lambda { params, body } => (params.clone(), body.clone()),
            _ => match self.op_arg(choose, env) {
                Ok(LOp::Ref(OpRef::Def(d))) => match self.def_target(d, env) {
                    Some((params, body, _, _)) => (params.to_vec(), body),
                    None => return false,
                },
                Ok(LOp::Lambda(params, body, _)) => (params.to_vec(), body),
                _ => return false,
            },
        };
        let [p] = &params[..] else { return false };
        let H::Choose { vars: BoundVars::Many(vs), set: Some(set), body } = &*body.kind else { return false };
        vs.len() == 1 && matches!(&*set.kind, H::Local(l) if l == p) && self.const_value(body, env) == Some(Value::TRUE)
    }

    /// An operator (argument) applied to lowered values; with `into`, its
    /// body is built in that encoding.
    pub(super) fn apply_op_lowered(&mut self, op: &LOp, args: Vec<Expr>, env: &LEnv, st: &St, into: Option<ShapeId>) -> Option<Expr> {
        let (params, body, base) = match op {
            LOp::Ref(OpRef::Def(d)) => {
                let (params, body, base, _) = self.def_target(*d, env)?;
                (params.to_vec(), body, base)
            }
            LOp::Lambda(params, body, lenv) => (params.to_vec(), body.clone(), lenv.clone()),
            // Integer `+`, `-`, `*` of the standard modules (e.g. `FoldFunction(+, 0, f)`).
            LOp::Ref(OpRef::Builtin(b @ (B::Plus | B::Minus | B::Mul))) if args.len() == 2 && !self.ip.is_builtin_overridden(*b) => {
                let iop = match b {
                    B::Plus => IntOp::Add,
                    B::Minus => IntOp::Sub,
                    _ => IntOp::Mul,
                };
                let mut it = args.into_iter();
                let (x, y) = (it.next()?, it.next()?);
                let (x, y) = (self.as_int(x).ok()?, self.as_int(y).ok()?);
                return Some(Expr::new(Ty::Int, ExprKind::IntBin(iop, x, y)));
            }
            _ => return None,
        };
        if params.len() != args.len() {
            return None;
        }
        let mut env2 = base;
        let mut binds = Vec::new();
        for (p, a) in params.iter().zip(args) {
            let (a, b) = self.share(a);
            binds.extend(b);
            env2 = env2.bind(*p, LBind::Ir(a));
        }
        let out = match into {
            Some(sid) => self.expr_into(&body, &env2, st, sid),
            None => self.expr(&body, &env2, st),
        };
        Some(let_in(binds.into_iter().rev(), out))
    }
}

/// `s` with the integer ranges of its record and tuple components widened
/// to all TLC integers.
fn widen_ints(s: &Shape) -> Shape {
    match s {
        Shape::Int { .. } => Shape::Int { lo: i32::MIN as i64, hi: i32::MAX as i64 },
        Shape::Record(fs) => Shape::Record(fs.iter().map(|(n, f)| (*n, widen_ints(f))).collect()),
        Shape::Tuple(es) => Shape::Tuple(es.iter().map(widen_ints).collect()),
        _ => s.clone(),
    }
}
