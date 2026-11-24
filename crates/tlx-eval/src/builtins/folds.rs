//! The `Folds` family (`Folds.java`): `FoldSet`, `FoldFunction`,
//! `FoldFunctionOnSet`, `FoldSeq`, `FoldLeft`, `FoldRight`,
//! `FoldLeftDomain`, `FoldRightDomain` and `MapThenFoldSet`, with the
//! element/domain helpers they share.

use std::sync::Arc;

use tlx_sema::hir::{BoundVars, DefKind, Expr, ExprKind, LocalId, OpRef, Span};
use tlx_value::{ops, Value};

use crate::env::{Env, OpVal};
use crate::error::{EResult, EvalError};
use crate::eval::Ctx;
use crate::interp::Interp;

impl Interp {
    /// `MapThenFoldSet(op, base, f, choose, S)` (Folds): elements are taken
    /// in the order `choose` picks them (x1 = choose(S), x2 = choose(S \ {x1}),
    /// ...) and combined as op(f(x1), op(f(x2), ... op(f(xn), base))).
    pub(super) fn map_then_fold_set(self: &Arc<Self>, args: &[Expr], env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        let op = self.op_val(&args[0], env)?;
        let base = self.eval(&args[1], env, cx)?;
        let f = self.op_val(&args[2], env)?;
        let choose = self.op_val(&args[3], env)?;
        let set = self.eval(&args[4], env, cx)?;
        if !set.is_set() {
            // (TLC evaluates the definition: `iter[S]` with `iter[s \in SUBSET S]`.)
            return Err(EvalError::at(format!("Attempted to check if the non-enumerable value\n{set}\nis element of\nSUBSET {set}"), span));
        }
        let mut rest = ops::enumerate_normalized(&set)?;
        let mut order = Vec::with_capacity(rest.len());
        if self.chooses_first(&choose) {
            // `CHOOSE x \in s : TRUE` picks the first element of `s` in TLC's
            // normalized order, and `s \ {x}` keeps that order: the elements
            // are taken in sorted order (linear, instead of a set difference
            // and a CHOOSE per element).
            order = std::mem::take(&mut rest);
        }
        while !rest.is_empty() {
            let x = self.apply_opval_values(&choose, vec![Value::set_from(rest.clone())?], cx, span)?;
            let Some(i) = rest.iter().position(|e| *e == x) else {
                return Err(EvalError::at(format!("MapThenFoldSet: choose returned {x}, which is not in the set"), span));
            };
            order.push(rest.remove(i));
        }
        let mut acc = base;
        for x in order.into_iter().rev() {
            let fx = self.apply_opval_values(&f, vec![x], cx, span)?;
            acc = self.apply_opval_values(&op, vec![fx, acc], cx, span)?;
        }
        Ok(acc)
    }

    /// Whether operator `op` is `LAMBDA s : CHOOSE x \in s : TRUE` (or a
    /// definition with that body), the `choose` that FiniteSetsExt's
    /// `MapThenSumSet` and similar definitions pass to `MapThenFoldSet`.
    fn chooses_first(&self, op: &OpVal) -> bool {
        let (params, body): (&[LocalId], &Expr) = match op {
            OpVal::Lambda { params, body, .. } => (params, body),
            OpVal::Ref(OpRef::Def(d)) => {
                if self.has_def_value(*d) {
                    return false;
                }
                let d = self.redirect_def(*d);
                if self.has_def_value(d) {
                    return false;
                }
                let def = &self.prog.defs[d.idx()];
                match &def.kind {
                    DefKind::Op(body) if def.builtin.is_none() => (&def.params, body),
                    _ => return false,
                }
            }
            _ => return false,
        };
        let [p] = params else { return false };
        match &*body.kind {
            ExprKind::Choose { vars: BoundVars::Many(vars), set: Some(set), body } => {
                vars.len() == 1 && matches!(&*set.kind, ExprKind::Local(l) if l == p) && matches!(&*body.kind, ExprKind::Bool(true))
            }
            _ => false,
        }
    }

    /// The elements of a fold's set argument, in TLC's order (what the Java
    /// overrides see from `Enumerable.elements()`, i.e. the normalized one).
    fn fold_set_elems(&self, v: &Value, op: &str, which: &str) -> EResult<Vec<Value>> {
        if !matches!(v, Value::Set(_) | Value::Interval(..) | Value::LazySet(_)) {
            let msg = format!("The {which} argument of {op} should be a set, but instead it is:\n{v}");
            return Err(EvalError::of_kind(tlx_runtime::ErrorKind::ArgumentError, msg));
        }
        Ok(ops::enumerate_normalized(v)?)
    }

    /// Whether `v` is a function (TLC's `FunctionValue`): a tuple, record,
    /// function or a lazy one.
    fn is_fcn(v: &Value) -> bool {
        matches!(v, Value::Tuple(_) | Value::Record(_) | Value::Fcn(..) | Value::LazyFcn(_))
    }

    /// `op(f(i), acc)` for every `i` of `fun`'s domain in TLC's order
    /// (Functions.foldFunction / foldFunctionOnSet).
    fn fold_over_domain(self: &Arc<Self>, op: &OpVal, mut acc: Value, fun: &Value, op_name: &str, cx: &Ctx, span: Span) -> EResult<Value> {
        if !Self::is_fcn(fun) {
            let msg = format!("The third argument of {op_name} should be a function, but instead it is:\n{fun}");
            return Err(EvalError::of_kind(tlx_runtime::ErrorKind::ArgumentError, msg).with_span(span));
        }
        for i in ops::enumerate_normalized(&ops::domain(fun)?)? {
            let v = ops::apply(fun, &i)?;
            acc = self.apply_opval_values(op, vec![v, acc], cx, span)?;
        }
        Ok(acc)
    }

    /// The elements of a sequence argument (TLC's `Value.toTuple()`: a
    /// function with domain `1..n`; a record or another function is not one).
    fn fold_seq_elems(&self, v: Value, op: &str, which: &str) -> EResult<Vec<Value>> {
        let v = crate::eval::force_seq(v)?;
        match &v {
            Value::Tuple(t) => Ok(t.to_vec()),
            _ => {
                let msg = format!("The {which} argument of {op} should be a sequence, but instead it is:\n{v}");
                Err(EvalError::of_kind(tlx_runtime::ErrorKind::ArgumentError, msg))
            }
        }
    }

    /// `FoldSet(op, base, set)` (FiniteSetsExt.java `foldSet`): `acc = op(x, acc)`
    /// for the elements in TLC's normalized (sorted) order.
    pub(super) fn fold_set(self: &Arc<Self>, args: &[Expr], env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        let op = self.native_op_val(&args[0], env, "first", "FoldSet", span)?;
        let mut acc = self.eval(&args[1], env, cx)?;
        let set = self.eval(&args[2], env, cx)?;
        for x in self.fold_set_elems(&set, "FoldSet", "third").map_err(|e| e.with_span(span))? {
            acc = self.apply_opval_values(&op, vec![x, acc], cx, span)?;
        }
        Ok(acc)
    }

    /// `FoldFunction(op, base, fun)` (Functions.java `foldFunction`): over
    /// `DOMAIN fun`, `acc = op(f[i], acc)`.
    pub(super) fn fold_function(self: &Arc<Self>, args: &[Expr], env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        let op = self.native_op_val(&args[0], env, "first", "FoldFunction", span)?;
        let acc = self.eval(&args[1], env, cx)?;
        let fun = self.eval(&args[2], env, cx)?;
        self.fold_over_domain(&op, acc, &fun, "FoldFunction", cx, span)
    }

    /// `FoldFunctionOnSet(op, base, fun, indices)` (Functions.java):
    /// `acc = op(f[i], acc)` for `i` in `indices`, in TLC's order.
    pub(super) fn fold_function_on_set(self: &Arc<Self>, args: &[Expr], env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        let op = self.native_op_val(&args[0], env, "first", "FoldFunctionOnSet", span)?;
        let mut acc = self.eval(&args[1], env, cx)?;
        let fun = self.eval(&args[2], env, cx)?;
        if !Self::is_fcn(&fun) {
            let msg = format!("The third argument of FoldFunctionOnSet should be a function, but instead it is:\n{fun}");
            return Err(EvalError::of_kind(tlx_runtime::ErrorKind::ArgumentError, msg).with_span(span));
        }
        let idx = self.eval(&args[3], env, cx)?;
        for i in self.fold_set_elems(&idx, "FoldFunctionOnSet", "fourth").map_err(|e| e.with_span(span))? {
            let v = ops::apply(&fun, &i)?;
            acc = self.apply_opval_values(&op, vec![v, acc], cx, span)?;
        }
        Ok(acc)
    }

    /// `FoldSeq(op, base, seq)` (SequencesExt.java): `foldFunction(op, base, seq)`,
    /// i.e. over the sequence's domain, `acc = op(seq[i], acc)`.
    pub(super) fn fold_seq(self: &Arc<Self>, args: &[Expr], env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        let op = self.native_op_val(&args[0], env, "first", "FoldSeq", span)?;
        let acc = self.eval(&args[1], env, cx)?;
        let seq = crate::eval::force_lazy_fcn(self.eval(&args[2], env, cx)?)?;
        // (SequencesExt.java's foldSeq is Functions.foldFunction: its
        // errors name FoldFunction.)
        self.fold_over_domain(&op, acc, &seq, "FoldFunction", cx, span)
    }

    /// `FoldLeft(op, base, seq)` (SequencesExt.java): `acc = op(acc, seq[i])`,
    /// indices ascending.
    pub(super) fn fold_left(self: &Arc<Self>, args: &[Expr], env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        let op = self.native_op_val(&args[0], env, "first", "FoldLeft", span)?;
        let mut acc = self.eval(&args[1], env, cx)?;
        let seq = self.eval(&args[2], env, cx)?;
        for x in self.fold_seq_elems(seq, "FoldLeft", "third").map_err(|e| e.with_span(span))? {
            acc = self.apply_opval_values(&op, vec![acc, x], cx, span)?;
        }
        Ok(acc)
    }

    /// `FoldRight(op, seq, base)` (SequencesExt.java): `acc = op(seq[i], acc)`,
    /// indices descending. Note the argument order (`seq` before `base`).
    pub(super) fn fold_right(self: &Arc<Self>, args: &[Expr], env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        let op = self.native_op_val(&args[0], env, "first", "FoldRight", span)?;
        let seq = self.eval(&args[1], env, cx)?;
        let mut acc = self.eval(&args[2], env, cx)?;
        for x in self.fold_seq_elems(seq, "FoldRight", "second").map_err(|e| e.with_span(span))?.into_iter().rev() {
            acc = self.apply_opval_values(&op, vec![x, acc], cx, span)?;
        }
        Ok(acc)
    }

    /// `FoldLeftDomain(op, base, seq)`: `acc = op(acc, i)` for `i = 1..Len(seq)`.
    pub(super) fn fold_left_domain(self: &Arc<Self>, args: &[Expr], env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        let op = self.native_op_val(&args[0], env, "first", "FoldLeftDomain", span)?;
        let mut acc = self.eval(&args[1], env, cx)?;
        let seq = self.eval(&args[2], env, cx)?;
        let n = self.fold_seq_elems(seq, "FoldLeftDomain", "third").map_err(|e| e.with_span(span))?.len();
        for i in 1..=n as i64 {
            acc = self.apply_opval_values(&op, vec![acc, Value::Int(i)], cx, span)?;
        }
        Ok(acc)
    }

    /// `FoldRightDomain(op, seq, base)`: `acc = op(i, acc)` for `i = Len(seq)..1`.
    pub(super) fn fold_right_domain(self: &Arc<Self>, args: &[Expr], env: &Env, cx: &Ctx, span: Span) -> EResult<Value> {
        let op = self.native_op_val(&args[0], env, "first", "FoldRightDomain", span)?;
        let seq = self.eval(&args[1], env, cx)?;
        let mut acc = self.eval(&args[2], env, cx)?;
        let n = self.fold_seq_elems(seq, "FoldRightDomain", "second").map_err(|e| e.with_span(span))?.len();
        for i in (1..=n as i64).rev() {
            acc = self.apply_opval_values(&op, vec![Value::Int(i), acc], cx, span)?;
        }
        Ok(acc)
    }
}
