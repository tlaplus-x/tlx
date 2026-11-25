//! Typed fast paths over encoded states: `typed_expr` dispatches on the
//! construct and returns `None` when no specialization applies (the
//! caller then lowers with value semantics). Here: arithmetic and
//! comparisons on unboxed integers, equality of encodings, conditionals,
//! and `UNCHANGED`/`[A]_v`/`<<A>>_v` in expressions. Builtins overridden
//! by the model (`is_builtin_overridden`) are never specialized.

use tlx_base::diag::{self, Topic};
use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{self, ExprKind as H, OpRef};
use tlx_value::Value;

use super::*;

impl Lowerer<'_> {
    /// Typed lowering of `e`, if specialized.
    pub(super) fn typed_expr(&mut self, e: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        use B::*;
        let ip = self.ip;
        let overridden = |op: B| ip.is_builtin_overridden(op);
        match &*e.kind {
            H::Builtin { op: op @ (Plus | Minus | Mul | Div | Mod | Pow | Gcd), args } if !overridden(*op) => {
                let iop = match op {
                    Gcd => IntOp::Gcd,
                    Plus => IntOp::Add,
                    Minus => IntOp::Sub,
                    Mul => IntOp::Mul,
                    Pow => IntOp::Pow,
                    Div if self.ip.div_is_floor() => IntOp::DivFloor,
                    Div => IntOp::DivNat,
                    _ => IntOp::Mod,
                };
                Some(self.int_binary(*op, args, env, st, |a, b| Expr::new(Ty::Int, ExprKind::IntBin(iop, a, b))))
            }
            H::Builtin { op: op @ (Lt | Le | Gt | Ge), args } if !overridden(*op) => {
                let c = match op {
                    Lt => CmpOp::Lt,
                    Le => CmpOp::Le,
                    Gt => CmpOp::Gt,
                    _ => CmpOp::Ge,
                };
                Some(self.int_binary(*op, args, env, st, |a, b| Expr::new(Ty::Bool, ExprKind::IntCmp(c, a, b))))
            }
            H::Builtin { op: Neg, args } if !overridden(Neg) => {
                let a = self.expr(&args[0], env, st);
                Some(match self.as_int(a) {
                    Ok(a) => Expr::new(Ty::Int, ExprKind::Neg(a)),
                    Err(a) => self.val_op(Neg, vec![a]),
                })
            }
            H::Builtin { op: op @ (Eq | Neq), args } if self.const_vs_constructor(&args[0], &args[1], env).is_some() => {
                let (k, other) = self.const_vs_constructor(&args[0], &args[1], env)?;
                let eq = self.eq_const_into(&k, other, env, st)?;
                Some(if *op == Neq { not(eq) } else { eq })
            }
            H::Builtin { op: op @ (Eq | Neq), args } => {
                // A constructor is built in the other side's encoding (errors
                // do not depend on the order: the interpreter reports them).
                let (a, b) = if self.constructs(&args[0], env) && !self.constructs(&args[1], env) {
                    let b = self.expr(&args[1], env, st);
                    (self.expr_as(&args[0], b.ty, env, st), b)
                } else {
                    let a = self.expr(&args[0], env, st);
                    let b = self.expr_as(&args[1], a.ty, env, st);
                    (a, b)
                };
                let eq = self.typed_eq(a, b);
                Some(if *op == Neq { not(eq) } else { eq })
            }
            // Assert(c, msg): a failure is reported by the interpreter.
            H::Builtin { op: Assert, args } if !overridden(Assert) => {
                let c = self.bool_expr(&args[0], env, st);
                let fail = Expr::new(Ty::Bool, ExprKind::Fail("assertion failed".into()));
                Some(Expr::new(Ty::Bool, ExprKind::If(c, bool_lit(true), fail)))
            }
            // Encoded sets are finite (the operand is still evaluated: TLC
            // reports its errors, e.g. an out-of-domain application inside).
            H::Builtin { op: IsFiniteSet, args } if !overridden(IsFiniteSet) => {
                let x = self.expr(&args[0], env, st);
                match self.shape_of(x.ty) {
                    Some(Shape::Set { .. }) => {
                        let (_, bind) = self.share(x);
                        Some(let_in(bind, bool_lit(true)))
                    }
                    _ => Some(self.val_op(IsFiniteSet, vec![x])),
                }
            }
            H::Builtin { op: Equiv, args } => {
                let a = self.bool_expr(&args[0], env, st);
                let b = self.bool_expr(&args[1], env, st);
                Some(eq(a, b))
            }
            H::Field { record, field } => Some(self.typed_field(record, field, env, st)),
            H::Builtin { op: Len, args } if !overridden(Len) => Some(self.typed_len(&args[0], env, st)),
            H::Builtin { op: Head, args } if !overridden(Head) => Some(self.typed_head(&args[0], env, st)),
            H::Builtin { op: Tail, args } if !overridden(Tail) => Some(self.typed_tail(&args[0], env, st)),
            H::Builtin { op: Append, args } if !overridden(Append) => Some(self.typed_append(&args[0], &args[1], env, st)),
            H::Builtin { op: Concat, args } if !overridden(Concat) => Some(self.typed_concat(&args[0], &args[1], env, st)),
            H::Builtin { op: SelectSeq, args } if !overridden(SelectSeq) => self.typed_select_seq(&args[0], &args[1], env, st),
            H::Builtin { op: Domain, args } => self.typed_domain(&args[0], env, st),
            H::Builtin { op: MapThenFoldSet, args } => self.typed_fold(args, env, st),
            H::Builtin { op: FoldSet, args } => self.typed_fold_set(args, env, st),
            H::Builtin { op: IsInjective, args } if !overridden(IsInjective) => self.typed_is_injective(&args[0], env, st),
            H::Builtin { op: FoldFunctionOnSet, args } => self.typed_fold_function_on_set(args, env, st),
            H::Builtin { op: FoldFunction | FoldSeq, args } => self.typed_fold_function(args, env, st),
            H::Builtin { op: op @ (SetMax | SetMin), args } => self.typed_set_extremum(*op == SetMax, &args[0], env, st),
            H::Builtin { op: SubSeq, args } if !overridden(SubSeq) => self.typed_subseq(&args[0], &args[1], &args[2], env, st),
            H::SetMap { expr: f, bounds } => self.typed_set_map(f, bounds, env, st),
            H::FnApp { func, args } if args.len() == 1 => Some(self.typed_fn_app(func, &args[0], env, st)),
            H::FnApp { func, args } => {
                if let Some(x) = self.inline_fn_def(func, args, env, st) {
                    return Some(x);
                }
                // f[a, b] = f[<<a, b>>] on a product domain.
                let f = self.expr(func, env, st);
                let f = self.encode_const_fn(f);
                let comps: Vec<Expr> = args.iter().map(|a| self.expr(a, env, st)).collect();
                self.apply_product(f, comps)
            }
            H::Except { base, updates } => self.typed_except(base, updates, env, st),
            H::FnConstruct { bounds, body } => self.typed_fn_construct(bounds, body, env, st),
            H::SetEnum(es) if !es.is_empty() => self.typed_set_enum(es, env, st),
            H::Tuple(es) if !es.is_empty() => {
                let comps: Vec<(Option<tlx_value::Sym>, hir::Expr)> = es.iter().map(|e| (None, e.clone())).collect();
                self.typed_product(&comps, env, st)
            }
            H::Record(fs) if !fs.is_empty() => {
                let comps: Vec<(Option<tlx_value::Sym>, hir::Expr)> =
                    fs.iter().map(|(n, e)| (Some(tlx_value::Sym::new(n)), e.clone())).collect();
                self.typed_product(&comps, env, st)
            }
            H::At => self.at.clone(),
            H::Apply { op: OpRef::Def(d), args }
                if args.is_empty() && self.mat.is_some() && !self.inline_stack.contains(&self.ip.redirect_def(*d)) =>
            {
                self.materialized(*d, st)
            }
            H::Builtin { op: Enabled, args } if !st.init && !self.primed => self.typed_enabled(&args[0], env, st),
            H::Builtin { op: Unchanged, args } if !st.init && !self.primed => Some(self.unchanged_typed(&args[0], env, st)),
            H::BoxAction { action, sub } if !st.init && !self.primed => {
                let a = self.bool_expr(action, env, st);
                let u = self.unchanged_typed(sub, env, st);
                Some(or(vec![a, u]))
            }
            H::AngleAction { action, sub } if !st.init && !self.primed => {
                let a = self.bool_expr(action, env, st);
                let u = self.unchanged_typed(sub, env, st);
                Some(and(vec![a, not(u)]))
            }
            H::If { cond, then, els } => Some(self.typed_if(cond, then, els, env, st)),
            H::Case { arms, other } => Some(self.typed_case(arms, other.as_ref(), env, st)),
            H::SetFilter { bound, pred } if binders::single_binder(bound) => self.typed_filter(bound, pred, env, st),
            H::Builtin { op: op @ (In | NotIn), args } => {
                let m = self.typed_in(&args[0], &args[1], env, st);
                Some(if *op == NotIn { not(to_bool(m)) } else { m })
            }
            H::Builtin { op: SubsetEq, args } if !overridden(SubsetEq) => Some(self.typed_subseteq(&args[0], &args[1], env, st)),
            H::Builtin { op: Cup, args } => Some(self.typed_union(&args[0], &args[1], env, st)),
            H::Builtin { op: Times, args } if !overridden(Times) => self.typed_times(&args[0], &args[1], env, st),
            H::Builtin { op: op @ (Cap | SetMinus), args } => Some(self.typed_set_op(*op, &args[0], &args[1], env, st)),
            H::Builtin { op: Cardinality, args } if !overridden(Cardinality) => Some(self.typed_cardinality(&args[0], env, st)),
            H::Builtin { op: Union, args } if !overridden(Union) => self.typed_big_union(&args[0], env, st),
            _ => None,
        }
    }

    /// A binary integer operator: `int` builds the unboxed operation when
    /// both operands are integers, else the boxed builtin `op` is used.
    fn int_binary(&mut self, op: B, args: &[hir::Expr], env: &LEnv, st: &St, int: impl FnOnce(Expr, Expr) -> Expr) -> Expr {
        let a = self.expr(&args[0], env, st);
        let b = self.expr(&args[1], env, st);
        match (self.as_int(a), self.as_int(b)) {
            (Ok(a), Ok(b)) => int(a, b),
            (a, b) => self.val_op(op, vec![either(a), either(b)]),
        }
    }

    /// Lower `e` to be combined with a value of type `ty`: a constructor is
    /// built directly in `ty`'s encoding.
    pub(super) fn expr_as(&mut self, e: &hir::Expr, ty: Ty, env: &LEnv, st: &St) -> Expr {
        match ty {
            // (Not a constant outside that encoding: its runtime conversion
            // could be dropped by a consumer that only needs the shape, e.g.
            // `Len` of a fixed-length tuple, instead of failing with a
            // layout miss.)
            // (Through operator calls and LETs only into a shape of the
            // layout, which the values of state variables fit.)
            Ty::Enc(sid)
                if (self.constructs(e, env) || (self.typing.in_layout(sid) && self.builds(e, env, 4)))
                    && self.const_value(e, env).is_none_or(|v| self.const_words(&v, sid).is_some()) =>
            {
                self.expr_into(e, env, st, sid)
            }
            _ => self.expr(e, env, st),
        }
    }

    /// `IF c THEN t ELSE f` with both branches in a common representation.
    fn typed_if(&mut self, cond: &hir::Expr, then: &hir::Expr, els: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        if let Some(b) = self.const_bool(cond, env) {
            return self.expr(if b { then } else { els }, env, st);
        }
        let c = self.bool_expr(cond, env, st);
        // A constructor in the THEN branch and an encoded value in the ELSE
        // branch (`IF n > 0 THEN MkArray(n, f) ELSE file`): build the
        // constructor in the other branch's encoding, which a constructor of
        // its own choosing would not match. (Only a shape of the layout:
        // values of a state variable's shape fit it.)
        if self.builds(then, env, 4) && !self.constructs(els, env) {
            let f = self.expr(els, env, st);
            let t = match f.ty {
                Ty::Enc(sid) if self.typing.in_layout(sid) => self.expr_into(then, env, st, sid),
                _ => self.expr(then, env, st),
            };
            let (t, f) = self.unify_branches(t, f);
            return Expr::new(t.ty, ExprKind::If(c, t, f));
        }
        let t = self.expr(then, env, st);
        let f = self.expr_as(els, t.ty, env, st);
        let (t, f) = self.unify_branches(t, f);
        Expr::new(t.ty, ExprKind::If(c, t, f))
    }

    /// `CASE g1 -> e1 [] ... [] OTHER -> e`: guards in order, the first true
    /// one selects its value; no true guard and no OTHER is an error.
    fn typed_case(&mut self, arms: &[(hir::Expr, hir::Expr)], other: Option<&hir::Expr>, env: &LEnv, st: &St) -> Expr {
        let (arms, other) = self.live_case_arms(arms, other, env);
        let mut acc = match other {
            Some(o) => self.expr(o, env, st),
            None => Expr::new(Ty::Val, ExprKind::Fail("No CASE arm is true.".into())),
        };
        for (g, v) in arms.iter().rev() {
            let c = self.bool_expr(g, env, st);
            let t = self.expr(v, env, st);
            let (t, f) = self.unify_branches(t, acc);
            acc = Expr::new(t.ty, ExprKind::If(c, t, f));
        }
        acc
    }

    /// `Max(S)` / `Min(S)` (FiniteSetsExt) of a literal set of integers,
    /// or of an encoded set of integers.
    fn typed_set_extremum(&mut self, max: bool, s: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let (p, penv) = self.peel(s, env)?;
        let H::SetEnum(es) = &*p.kind else { return self.encoded_set_extremum(max, s, env, st) };
        let mut acc: Option<Expr> = None;
        for e in es {
            let x = self.expr(e, &penv, st);
            let x = self.as_int(x).ok()?;
            acc = Some(match acc {
                None => x,
                Some(m) => {
                    let (x, bx) = self.share(x);
                    let (m, bm) = self.share(m);
                    let better = Expr::new(Ty::Bool, ExprKind::IntCmp(if max { CmpOp::Gt } else { CmpOp::Lt }, x.clone(), m.clone()));
                    let pick = Expr::new(Ty::Int, ExprKind::If(better, x, m));
                    let_in(bx.into_iter().chain(bm), pick)
                }
            });
        }
        acc
    }

    /// `IsInjective(f)` (Functions) of an encoded fixed-domain function,
    /// tuple or record: no two slots equal, compared pairwise in TLC's
    /// order of the domain (as the Java override does).
    fn typed_is_injective(&mut self, f: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        const MAX_SLOTS: usize = 16;
        let x = self.expr(f, env, st);
        let x = self.encode_const_fn(x);
        let shape = self.shape_of(x.ty)?.clone();
        if !matches!(shape, Shape::Fcn { .. } | Shape::Tuple(_) | Shape::Record(_)) {
            return None;
        }
        let slots = self.slots(&shape)?;
        if slots.len() > MAX_SLOTS {
            return None;
        }
        let dom = Value::set_from(slots.iter().map(|(d, _, _)| d.clone()).collect()).ok()?;
        let (x, bind) = self.share(x);
        let mut vals = Vec::with_capacity(slots.len());
        for k in tlx_value::ops::enumerate_normalized(&dom).ok()? {
            let (_, loc, sh) = slots.iter().find(|(d, _, _)| *d == k)?;
            let ssid = self.sid(sh);
            vals.push(Expr::new(Ty::Enc(ssid), ExprKind::Slice { base: x.clone(), loc: *loc }));
        }
        let mut distinct = Vec::new();
        for (i, a) in vals.iter().enumerate() {
            for b in &vals[i + 1..] {
                distinct.push(not(self.typed_eq(a.clone(), b.clone())));
            }
        }
        let r = if distinct.is_empty() { bool_lit(true) } else { and(distinct) };
        Some(let_in(bind, r))
    }

    /// `Max(S)` / `Min(S)` of an encoded set of integers: the element not
    /// less (greater) than any other (as the module defines it; an empty
    /// set is a CHOOSE error, reported by the interpreter).
    fn encoded_set_extremum(&mut self, max: bool, s: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let x = self.expr(s, env, st);
        let x = self.set_operand(x);
        let Some(Shape::Set { elem, .. }) = self.shape_of(x.ty) else { return None };
        if !matches!(**elem, Shape::Int { .. }) {
            return None;
        }
        let (x, bind) = self.share(x);
        let (outer, ety) = self.typed_iter_in(x.clone(), true);
        let (inner, _) = self.typed_iter_in(x, true);
        if !outer.is_typed_source() || !inner.is_typed_source() {
            return None;
        }
        let (t1, t2) = (self.temp(ety), self.temp(ety));
        let a = self.as_int(temp_ref(ety, t1)).ok()?;
        let b = self.as_int(temp_ref(ety, t2)).ok()?;
        let cmp = Expr::new(Ty::Bool, ExprKind::IntCmp(if max { CmpOp::Ge } else { CmpOp::Le }, a, b));
        let all = Expr::new(Ty::Bool, ExprKind::Forall { bind: t2, set: inner, body: cmp });
        let pick = Expr::new(ety, ExprKind::Choose { bind: t1, set: outer, body: all });
        let r = self.as_int(pick).ok()?;
        Some(let_in(bind, r))
    }

    /// `(constant value, other side)` when one side of `=` is a constant
    /// record/tuple and the other a constructor (e.g. an operator building a
    /// record): the constant's shape then serves as the destination.
    fn const_vs_constructor<'e>(&self, a: &'e hir::Expr, b: &'e hir::Expr, env: &LEnv) -> Option<(Value, &'e hir::Expr)> {
        for (k, o) in [(a, b), (b, a)] {
            if let Some(v) = self.const_value(k, env) {
                if matches!(v, Value::Record(_) | Value::Tuple(_)) && self.const_value(o, env).is_none() && self.constructs(o, env) {
                    return Some((v, o));
                }
            }
        }
        None
    }

    fn eq_const_into(&mut self, k: &Value, other: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        // Tuples as sequences: the other side may be a sequence of another
        // capacity (or a tuple literal, which a sequence holds as well).
        let shape = seqify(&self.fit_shape(std::slice::from_ref(k))?);
        let sid = self.sid(&shape);
        let c = self.const_words(k, sid)?;
        let x = self.expr_into(other, env, st, sid);
        if x.ty != Ty::Enc(sid) {
            return None;
        }
        Some(eq(x, c))
    }

    /// Bring two conditional branches to one representation.
    pub(super) fn unify_branches(&mut self, t: Expr, f: Expr) -> (Expr, Expr) {
        // A failing branch (e.g. recursion beyond the unrolling) takes the
        // other branch's representation.
        let retype = |x: Expr, ty: Ty| match &*x.kind {
            ExprKind::Fail(m) => Expr::new(ty, ExprKind::Fail(m.clone())),
            _ => x,
        };
        let (tt, ft) = (t.ty, f.ty);
        let (t, f) = (retype(t, ft), retype(f, tt));
        if matches!((t.ty, f.ty), (Ty::Val, Ty::Enc(_)) | (Ty::Enc(_), Ty::Val)) {
            if let Some(x) = self.union_branches(&t, &f) {
                return x;
            }
        }
        let (t, f) = match (t.ty, f.ty) {
            // Two boxed constants (e.g. strings): encode both in a shape
            // holding them (preferably an atom universe of the state).
            (Ty::Val, Ty::Val) if matches!((&*t.kind, &*f.kind), (ExprKind::Const(_), ExprKind::Const(_))) => {
                let (ExprKind::Const(a), ExprKind::Const(b)) = (&*t.kind, &*f.kind) else { unreachable!() };
                match self.fit_shape(&[a.clone(), b.clone()]).filter(construct::is_scalarish) {
                    Some(sh) => {
                        let sid = self.sid(&sh);
                        match (self.const_words(a, sid), self.const_words(b, sid)) {
                            (Some(x), Some(y)) => (x, y),
                            _ => (t, f),
                        }
                    }
                    None => (t, f),
                }
            }
            (a, b) if a == b => (t, f),
            (Ty::Bool, _) | (_, Ty::Bool) => match (self.as_bool(t), self.as_bool(f)) {
                (Ok(t), Ok(f)) => (t, f),
                (t, f) => (to_val(either(t)), to_val(either(f))),
            },
            (Ty::Int, _) | (_, Ty::Int) => match (self.as_int(t), self.as_int(f)) {
                (Ok(t), Ok(f)) => (t, f),
                (t, f) => (to_val(either(t)), to_val(either(f))),
            },
            // A constant that fits the other branch's encoding. (Not
            // otherwise: a runtime conversion could be dropped by a consumer
            // that only needs the shape, e.g. DOMAIN of a fixed-length tuple,
            // instead of failing with a layout miss.)
            (Ty::Enc(a), _) if matches!(&*f.kind, ExprKind::Const(v) if self.const_words(v, a).is_some()) => {
                let f = self.coerce_enc(f, a);
                (t, f)
            }
            (Ty::Enc(a), Ty::Enc(b)) => match self.joined_scalarish(a, b) {
                // Different encodings of scalar(-ish) values: recode to the join.
                Some(j) => match (self.recode_to(t.clone(), j), self.recode_to(f.clone(), j)) {
                    (Some(t), Some(f)) => (t, f),
                    _ => (to_val(t), to_val(f)),
                },
                None => match self.joined_struct(a, b) {
                    // Records / tuples of scalars of other ranges: converted
                    // slot-wise to the join.
                    Some(j) => (self.coerce_enc(t, j), self.coerce_enc(f, j)),
                    None => match self.union_branches(&t, &f) {
                        Some(x) => x,
                        None => (to_val(t), to_val(f)),
                    },
                },
            },
            (Ty::Val, Ty::Enc(b)) | (Ty::Enc(b), Ty::Val)
                if matches!(&*t.kind, ExprKind::Const(_)) || matches!(&*f.kind, ExprKind::Const(_)) =>
            {
                // A constant and a scalar(-ish) value: meet at their join.
                let (c, other_is_t) = if t.ty == Ty::Val { (t.clone(), false) } else { (f.clone(), true) };
                let ExprKind::Const(v) = &*c.kind else { unreachable!() };
                // The constant fits the other branch's encoding.
                if let Some(k) = self.const_words(v, b) {
                    return if other_is_t { (t, k) } else { (k, f) };
                }
                match self.join_with_const(b, v) {
                    Some(j) => {
                        let (enc, konst) = if other_is_t { (t.clone(), c) } else { (f.clone(), c) };
                        match (
                            self.recode_to(enc, j),
                            self.const_words(
                                match &*konst.kind {
                                    ExprKind::Const(v) => v,
                                    _ => unreachable!(),
                                },
                                j,
                            ),
                        ) {
                            (Some(e), Some(k)) => {
                                if other_is_t {
                                    (e, k)
                                } else {
                                    (k, e)
                                }
                            }
                            _ => (to_val(t), to_val(f)),
                        }
                    }
                    None => (to_val(t), to_val(f)),
                }
            }
            _ => (to_val(t), to_val(f)),
        };
        (t, f)
    }

    /// Two branches (encoded, or a constant and an encoded value) whose
    /// shapes join into a union of tuples of different lengths (e.g.
    /// `<<n, r>>` and `<<>>`): both in that union, preferably an interned
    /// union covering it (e.g. a state variable's).
    fn union_branches(&mut self, t: &Expr, f: &Expr) -> Option<(Expr, Expr)> {
        let shape = |x: &Expr, me: &Self| match (x.ty, &*x.kind) {
            (Ty::Enc(_), _) => me.shape_of(x.ty).cloned(),
            (Ty::Val, ExprKind::Const(v)) => v.normalize().ok().map(|v| Shape::of(&v)),
            _ => None,
        };
        let (st, sf) = (shape(t, self)?, shape(f, self)?);
        let j = st.join(&sf);
        let Shape::Union(arms) = &j else { return None };
        if !arms.iter().all(|a| matches!(a, Shape::Tuple(_))) {
            return None;
        }
        let target = {
            // Else one with arms of the same kinds (e.g. a state variable's
            // with other integer ranges; a value outside it is a runtime
            // layout miss), else the join itself.
            let ty = &self.typing;
            let keys: Vec<_> = arms.iter().map(Shape::kind_key).collect();
            let unions = || (0..ty.num_shapes() as ShapeId).map(|sid| ty.shape(sid)).filter(|s| matches!(s, Shape::Union(_)));
            let same_kinds = |s: &Shape| matches!(s, Shape::Union(a) if a.iter().map(Shape::kind_key).eq(keys.iter().cloned()));
            unions().find(|s| s.join(&j) == **s).or_else(|| unions().find(|s| same_kinds(s))).cloned()
        };
        let target = target.unwrap_or(j);
        if let Shape::Union(arms) = &target {
            arms.iter().for_each(|a| {
                self.sid(a);
            });
        }
        let sid = self.sid(&target);
        let conv = |x: &Expr, me: &mut Self| -> Option<Expr> {
            match &*x.kind {
                ExprKind::Const(v) if x.ty == Ty::Val => me.const_words(v, sid),
                _ => {
                    let y = me.coerce_enc(x.clone(), sid);
                    (!matches!(&*y.kind, ExprKind::Convert(_))).then_some(y)
                }
            }
        };
        Some((conv(t, self)?, conv(f, self)?))
    }

    /// The join of scalar(-ish) shape `a` with the shape of constant `v`.
    fn join_with_const(&mut self, a: ShapeId, v: &Value) -> Option<ShapeId> {
        let sa = self.shape_of(Ty::Enc(a))?.clone();
        let sv = Shape::of(v);
        if !construct::is_scalarish(&sa) || !construct::is_scalarish(&sv) {
            return None;
        }
        let j = sa.join(&sv);
        if !construct::is_scalarish(&j) {
            return None;
        }
        if let Shape::Union(arms) = &j {
            arms.iter().for_each(|x| {
                self.sid(x);
            });
        }
        Some(self.sid(&j))
    }

    /// `UNCHANGED e` in an expression: `e' = e`, componentwise for tuples.
    fn unchanged_typed(&mut self, e: &hir::Expr, env: &LEnv, st: &St) -> Expr {
        if let Some((p, penv)) = self.peel(e, env) {
            if let H::Tuple(es) = &*p.kind {
                let parts = es.iter().map(|x| self.unchanged_typed(x, &penv, st)).collect();
                return self.strict_and(parts);
            }
        }
        let new = self.primed_expr(e, env, st);
        let old = self.expr(e, env, st);
        self.typed_eq(new, old)
    }

    /// The conjunction of the componentwise comparisons `parts` of two
    /// tuples, all evaluated: TLC evaluates both tuples entirely before
    /// comparing them, so an error in any component is an error (e.g. an
    /// unspecified primed variable in `<<A>>_<<x, y>>`).
    pub(super) fn strict_and(&mut self, parts: Vec<Expr>) -> Expr {
        if parts.len() < 2 {
            return and(parts);
        }
        let mut binds = Vec::new();
        let mut refs = Vec::with_capacity(parts.len());
        for p in parts {
            let (x, b) = self.share(p);
            refs.push(x);
            binds.extend(b);
        }
        // (`let_in` wraps the last binding outermost.)
        binds.reverse();
        let_in(binds, and(refs))
    }

    /// `x` as an unboxed integer, if its representation allows it.
    pub(super) fn as_int(&self, x: Expr) -> Result<Expr, Expr> {
        match (x.ty, &*x.kind) {
            (Ty::Int, _) => Ok(x),
            (_, ExprKind::Fail(m)) => Ok(Expr::new(Ty::Int, ExprKind::Fail(m.clone()))),
            (Ty::Val, ExprKind::Const(Value::Int(i))) => Ok(int_lit(*i)),
            (Ty::Enc(_), _) if matches!(self.shape_of(x.ty), Some(Shape::Int { .. })) => Ok(Expr::new(Ty::Int, ExprKind::Convert(x))),
            (Ty::Enc(_), _) if self.is_ref(x.ty) => Ok(self.ref_op(crate::ir::RefOp::ToInt, vec![x])),
            (Ty::Val, ExprKind::Convert(inner)) if inner.ty != Ty::Val => self.as_int(inner.clone()).map_err(|_| x),
            (Ty::Enc(_), _) => self.union_int(&x).ok_or(x),
            _ => Err(x),
        }
    }

    /// Static bounds of an unboxed integer expression, if known.
    pub(super) fn int_range(&mut self, x: &Expr) -> Option<(i64, i64)> {
        const LIMIT: i64 = 1 << 20;
        let r = match &*x.kind {
            ExprKind::Const(Value::Int(i)) => (*i, *i),
            ExprKind::Convert(inner) => match *self.shape_of(inner.ty)? {
                Shape::Int { lo, hi } => (lo, hi),
                _ => return None,
            },
            ExprKind::UnionFieldInt { base, entries } => {
                let Some(Shape::Union(arms)) = self.shape_of(base.ty).cloned() else { return None };
                let mut r: Option<(i64, i64)> = None;
                for (arm, e) in arms.iter().zip(entries.iter()) {
                    let (Shape::Record(fields), Some((loc, _))) = (arm, e) else { continue };
                    let fl = FieldLayout::of_shapes(fields.iter().map(|(_, fs)| fs));
                    let mut found = None;
                    for ((_, fs), &floc) in fields.iter().zip(fl.locs.iter()) {
                        if let (Shape::Int { lo, hi }, true) = (fs, floc == *loc) {
                            found = Some((*lo, *hi));
                            break;
                        }
                        self.sid(fs);
                    }
                    let (lo, hi) = found?;
                    r = Some(r.map_or((lo, hi), |(a, b)| (a.min(lo), b.max(hi))));
                }
                r?
            }
            // A failing branch takes no value.
            ExprKind::If(_, a, b) if matches!(&*b.kind, ExprKind::Fail(_)) => self.int_range(a)?,
            ExprKind::If(_, a, b) if matches!(&*a.kind, ExprKind::Fail(_)) => self.int_range(b)?,
            ExprKind::If(_, a, b) => {
                let (a, b) = (self.int_range(a)?, self.int_range(b)?);
                (a.0.min(b.0), a.1.max(b.1))
            }
            ExprKind::Neg(a) => {
                let (lo, hi) = self.int_range(a)?;
                (-hi, -lo)
            }
            ExprKind::IntBin(IntOp::Add, a, b) => {
                let (a, b) = (self.int_range(a)?, self.int_range(b)?);
                (a.0 + b.0, a.1 + b.1)
            }
            ExprKind::IntBin(IntOp::Sub, a, b) => {
                let (a, b) = (self.int_range(a)?, self.int_range(b)?);
                (a.0 - b.1, a.1 - b.0)
            }
            // (Operands are within LIMIT: the products cannot overflow.)
            ExprKind::IntBin(IntOp::Mul, a, b) => {
                let (a, b) = (self.int_range(a)?, self.int_range(b)?);
                let p = [a.0 * b.0, a.0 * b.1, a.1 * b.0, a.1 * b.1];
                (*p.iter().min().unwrap(), *p.iter().max().unwrap())
            }
            // A divisor of 0 is an error (`%`: below 1): a non-negative
            // divisor is positive. By a positive divisor both divisions are
            // monotonic in each operand: the extremes are at the corners.
            ExprKind::IntBin(op @ (IntOp::DivFloor | IntOp::DivNat), a, b) => {
                let (a, b) = (self.int_range(a)?, self.int_range(b)?);
                if b.0 < 0 || b.1 < 1 {
                    return None;
                }
                let b = (b.0.max(1), b.1);
                let div = |x: i64, y: i64| {
                    if *op == IntOp::DivFloor {
                        tlx_value::arith::div_floor(x, y).ok()
                    } else {
                        tlx_value::arith::div_naturals(x, y).ok()
                    }
                };
                let q = [div(a.0, b.0)?, div(a.0, b.1)?, div(a.1, b.0)?, div(a.1, b.1)?];
                (*q.iter().min().unwrap(), *q.iter().max().unwrap())
            }
            ExprKind::IntBin(IntOp::Mod, _, b) => {
                let b = self.int_range(b)?;
                if b.1 < 1 {
                    return None;
                }
                (0, b.1 - 1)
            }
            // gcd(a, b) <= max(|a|, |b|) (a result of 2^31 is an error).
            ExprKind::IntBin(IntOp::Gcd, a, b) => {
                let (a, b) = (self.int_range(a)?, self.int_range(b)?);
                let abs = |r: (i64, i64)| r.0.unsigned_abs().max(r.1.unsigned_abs());
                (0, abs(a).max(abs(b)).min(i32::MAX as u64) as i64)
            }
            ExprKind::Let { body, .. } => self.int_range(body)?,
            ExprKind::Temp(t) => *self.temp_ranges.get(t)?,
            ExprKind::Choose { set, .. } => match &*set.kind {
                ExprKind::IntRange(lo, hi) => {
                    let (a, b) = (self.int_range(lo)?, self.int_range(hi)?);
                    (a.0, b.1)
                }
                _ => return None,
            },
            ExprKind::SeqLen(s) => match self.shape_of(s.ty)? {
                Shape::Seq { max_len, .. } => (0, *max_len as i64),
                _ => return None,
            },
            ExprKind::BitCard(s) => match self.shape_of(s.ty)? {
                Shape::Set { elem, .. } if tlx_layout::layout::bitset_universe(elem).is_some() => (0, elem.cardinality()? as i64),
                _ => return None,
            },
            _ => return None,
        };
        (r.0 >= -LIMIT && r.1 <= LIMIT).then_some(r)
    }

    /// The integer arm of a union value (any other arm is a runtime error;
    /// used where TLC requires an integer anyway).
    fn union_int(&self, x: &Expr) -> Option<Expr> {
        let Some(Shape::Union(arms)) = self.shape_of(x.ty) else { return None };
        let ints: Vec<usize> = (0..arms.len()).filter(|&i| matches!(arms[i], Shape::Int { .. })).collect();
        let [i] = ints[..] else { return None };
        let asid = self.typing.lookup(&arms[i])?;
        let payload = Expr::new(Ty::Enc(asid), ExprKind::Slice { base: x.clone(), loc: FieldLoc::Words(1) });
        let tag = Expr::new(Ty::Int, ExprKind::Rank(x.clone()));
        let fail = Expr::new(Ty::Int, ExprKind::Fail("An integer was expected.".into()));
        Some(Expr::new(Ty::Int, ExprKind::If(eq(tag, int_lit(i as i64)), Expr::new(Ty::Int, ExprKind::Convert(payload)), fail)))
    }

    /// `u = i` for a union `u` with one integer arm and an integer `i`, if
    /// every other arm holds only untyped model values.
    fn union_int_eq(&mut self, u: &Expr, i: Expr) -> Option<Expr> {
        let Some(Shape::Union(arms)) = self.shape_of(u.ty).cloned() else { return None };
        let mut int_arm = None;
        for (k, a) in arms.iter().enumerate() {
            match a {
                Shape::Int { .. } if int_arm.is_none() => int_arm = Some(k),
                Shape::Atom(vs) if vs.iter().all(|v| matches!(v, Value::ModelValue(m) if m.model_value_type().is_none())) => {}
                _ => return None,
            }
        }
        let k = int_arm?;
        let asid = self.typing.lookup(&arms[k])?;
        // Both operands are evaluated (an error in `i` must not be skipped).
        let (i, bind_i) = self.share(i);
        let (u, bind) = self.share(u.clone());
        let tag = Expr::new(Ty::Int, ExprKind::Rank(u.clone()));
        let payload = Expr::new(Ty::Int, ExprKind::Convert(Expr::new(Ty::Enc(asid), ExprKind::Slice { base: u, loc: FieldLoc::Words(1) })));
        let x = and(vec![eq(tag, int_lit(k as i64)), eq(payload, i)]);
        Some(let_in(bind.into_iter().chain(bind_i), x))
    }

    /// Both values in one encoding where comparing them can never be a TLC
    /// error: atoms (strings / model values) of different universes, or a
    /// record and a union of records.
    fn common_encoding(&mut self, a: &Expr, b: &Expr) -> Option<(Expr, Expr)> {
        let (Ty::Enc(x), Ty::Enc(y)) = (a.ty, b.ty) else { return None };
        let (sx, sy) = (self.shape_of(a.ty)?.clone(), self.shape_of(b.ty)?.clone());
        let atoms_only = |s: &Shape| match s {
            Shape::Atom(_) => true,
            Shape::Union(arms) => arms.iter().all(|a| matches!(a, Shape::Atom(_))),
            _ => false,
        };
        if atoms_only(&sx) && atoms_only(&sy) {
            let j = self.joined_scalarish(x, y)?;
            return Some((self.recode_to(a.clone(), j)?, self.recode_to(b.clone(), j)?));
        }
        let records = |s: &Shape| match s {
            Shape::Union(arms) => arms.iter().all(|a| matches!(a, Shape::Record(_))),
            _ => false,
        };
        if records(&sx) && matches!(sy, Shape::Record(_)) {
            let w = self.union_arm_coerce(b, x)?;
            return Some((a.clone(), w));
        }
        if records(&sy) && matches!(sx, Shape::Record(_)) {
            let w = self.union_arm_coerce(a, y)?;
            return Some((w, b.clone()));
        }
        // Two unions: one embedded into the other.
        if let Some(a2) = self.union_to_union(a, y) {
            return Some((a2, b.clone()));
        }
        if let Some(b2) = self.union_to_union(b, x) {
            return Some((a.clone(), b2));
        }
        // A union and a value of the kind of one of its arms: the value
        // converted into that arm (a value not fitting the arm's encoding
        // is a runtime layout miss) and wrapped into the union.
        for (u, v, swap) in [(a, b, false), (b, a, true)] {
            let (Ty::Enc(us), Ty::Enc(_)) = (u.ty, v.ty) else { continue };
            let (Some(Shape::Union(arms)), Some(vs)) = (self.shape_of(u.ty).cloned(), self.shape_of(v.ty).cloned()) else { continue };
            if matches!(vs, Shape::Union(_)) {
                continue;
            }
            let Some(arm) = arms.iter().find(|a| a.kind_key() == vs.kind_key()) else { continue };
            let asid = self.sid(arm);
            let v2 = self.coerce_enc(v.clone(), asid);
            if matches!(&*v2.kind, ExprKind::Convert(y) if y.ty == Ty::Val || matches!(y.ty, Ty::Enc(_))) {
                continue;
            }
            let Some(w) = self.union_arm_coerce(&v2, us) else { continue };
            return Some(if swap { (w, u.clone()) } else { (u.clone(), w) });
        }
        if let Some(b2) = self.bitset_retype(b, x) {
            return Some((a.clone(), b2));
        }
        // Sequences (or homogeneous tuples) of one element encoding: as
        // sequences of the larger capacity.
        if let (Some((ex, mx)), Some((ey, my))) = (seq_like(&sx), seq_like(&sy)) {
            if ex == ey {
                let sid = self.sid(&Shape::Seq { elem: Box::new(ex), max_len: mx.max(my) });
                let (a2, b2) = (self.coerce_enc(a.clone(), sid), self.coerce_enc(b.clone(), sid));
                if matches!(&*a2.kind, ExprKind::Convert(_)) || matches!(&*b2.kind, ExprKind::Convert(_)) {
                    return None;
                }
                return Some((a2, b2));
            }
        }
        None
    }

    /// The join of two scalar(-ish) shapes, registered.
    pub(super) fn joined_scalarish(&mut self, a: ShapeId, b: ShapeId) -> Option<ShapeId> {
        let (sa, sb) = (self.shape_of(Ty::Enc(a))?.clone(), self.shape_of(Ty::Enc(b))?.clone());
        if !construct::is_scalarish(&sa) || !construct::is_scalarish(&sb) {
            return None;
        }
        let j = sa.join(&sb);
        if !construct::is_scalarish(&j) {
            return None;
        }
        if let Shape::Union(arms) = &j {
            arms.iter().for_each(|a| {
                self.sid(a);
            });
        }
        Some(self.sid(&j))
    }

    /// The join of two records with the same fields (or two tuples of the
    /// same length) whose slots are scalar(-ish) and join to scalar(-ish)
    /// slots (e.g. integers of other ranges): both convert to it slot-wise.
    fn joined_struct(&mut self, a: ShapeId, b: ShapeId) -> Option<ShapeId> {
        let (sa, sb) = (self.shape_of(Ty::Enc(a))?.clone(), self.shape_of(Ty::Enc(b))?.clone());
        let slots_ok = |s: &Shape| match s {
            Shape::Record(fs) => fs.iter().all(|(_, f)| construct::is_scalarish(f)),
            Shape::Tuple(es) => es.iter().all(construct::is_scalarish),
            _ => false,
        };
        let same_slots = match (&sa, &sb) {
            (Shape::Record(x), Shape::Record(y)) => x.len() == y.len() && x.iter().zip(y.iter()).all(|(p, q)| p.0 == q.0),
            (Shape::Tuple(x), Shape::Tuple(y)) => x.len() == y.len(),
            _ => false,
        };
        if !same_slots || !slots_ok(&sa) || !slots_ok(&sb) {
            return None;
        }
        let j = sa.join(&sb);
        if !slots_ok(&j) {
            return None;
        }
        Some(self.sid(&j))
    }

    pub(super) fn recode_to(&self, x: Expr, sid: ShapeId) -> Option<Expr> {
        if x.ty == Ty::Enc(sid) {
            return Some(x);
        }
        if let ExprKind::Fail(m) = &*x.kind {
            return Some(Expr::new(Ty::Enc(sid), ExprKind::Fail(m.clone())));
        }
        self.recode(&x, sid)
    }

    /// `x` as an unboxed boolean, if its representation allows it.
    pub(super) fn as_bool(&self, x: Expr) -> Result<Expr, Expr> {
        match (x.ty, &*x.kind) {
            (Ty::Bool, _) => Ok(x),
            (_, ExprKind::Fail(m)) => Ok(Expr::new(Ty::Bool, ExprKind::Fail(m.clone()))),
            (Ty::Enc(_), _) if matches!(self.shape_of(x.ty), Some(Shape::Bool)) => Ok(Expr::new(Ty::Bool, ExprKind::Convert(x))),
            (Ty::Enc(_), _) if self.is_ref(x.ty) => Ok(self.ref_op(crate::ir::RefOp::ToBool, vec![x])),
            (Ty::Val, ExprKind::Convert(inner)) if inner.ty != Ty::Val => self.as_bool(inner.clone()).map_err(|_| x),
            _ => Err(x),
        }
    }

    pub(super) fn int_like(&self, a: &Expr) -> bool {
        self.as_int(a.clone()).is_ok()
    }

    /// The boxed builtin `op` applied to `args`.
    /// Constant arguments are folded at compile time (unless the
    /// evaluation fails: the error is then reported at run time).
    pub(super) fn val_op(&self, op: B, args: Vec<Expr>) -> Expr {
        if let Some(v) = self.fold_op(op, &args) {
            return const_expr(v);
        }
        Expr::new(Ty::Val, ExprKind::ValOp { op, args: args.into_iter().map(to_val).collect() })
    }

    /// `op` applied to constant arguments, evaluated now (strict, pure,
    /// not overridden builtins only).
    fn fold_op(&self, op: B, args: &[Expr]) -> Option<Value> {
        if self.ip.is_builtin_overridden(op) || super::analysis::is_volatile_builtin(op) || op == B::Assert {
            return None;
        }
        let vs = args.iter().map(const_of).collect::<Option<Vec<Value>>>()?;
        // Not one that creates a string: strings are ordered by creation, as
        // in TLC, so it is created where the search first
        // evaluates it, not now in source order. (Sequences of
        // strings are concatenated or cut without creating any.)
        if tlx_eval::strings::makes_strings(op)
            && (!matches!(op, B::Concat | B::Tail | B::SubSeq) || vs.iter().any(|v| matches!(v, Value::Str(_))))
        {
            return None;
        }
        self.ip.builtin_on_values(op, vs, &tlx_eval::eval::Ctx::NONE).ok()
    }

    /// A bounded semantic table: 0/1 are values; -1 asks the interpreter to
    /// re-evaluate the original expression and report its error. The index
    /// is evaluated even for a constant result, and only in its original
    /// control-flow branch. Lookup consumes an encoded zero-based index.
    pub(super) fn truth_error_table(&mut self, index: Expr, table: Vec<i32>) -> Expr {
        let index = if index.ty == Ty::Int {
            let sid = self.sid(&Shape::Int { lo: 0, hi: table.len() as i64 - 1 });
            self.coerce_enc(index, sid)
        } else {
            index
        };
        let fallible = table.contains(&-1);
        let result = Expr::new(Ty::Int, ExprKind::Lookup { x: index, table: table.into() });
        if !fallible {
            return eq(result, int_lit(1));
        }
        let (result, bind) = self.share(result);
        let valid = Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Ge, result.clone(), int_lit(0)));
        let value = eq(result, int_lit(1));
        let error = Expr::new(Ty::Bool, ExprKind::Fail("incomparable atom comparison".into()));
        let_in(bind, Expr::new(Ty::Bool, ExprKind::If(valid, value, error)))
    }

    /// Equality across finite atom encodings whose comparisons are not
    /// total. Ranks select a semantic result, never stand in for values.
    fn atom_pair_eq(&mut self, a: &Expr, b: &Expr) -> Option<Expr> {
        let (Shape::Atom(xs), Shape::Atom(ys)) = (self.shape_of(a.ty)?, self.shape_of(b.ty)?) else { return None };
        let entries = xs.len().checked_mul(ys.len())?;
        if entries == 0 || entries > 4096 {
            return None;
        }
        let table = xs.iter().flat_map(|x| ys.iter().map(move |y| tlx_value::order::eq_tlc(x, y).map_or(-1, i32::from))).collect();
        let stride = ys.len() as i64;
        let ar = Expr::new(Ty::Int, ExprKind::Rank(a.clone()));
        let br = Expr::new(Ty::Int, ExprKind::Rank(b.clone()));
        let row = Expr::new(Ty::Int, ExprKind::IntBin(IntOp::Mul, ar, int_lit(stride)));
        let index = Expr::new(Ty::Int, ExprKind::IntBin(IntOp::Add, row, br));
        Some(self.truth_error_table(index, table))
    }

    /// `a = b` in the cheapest common representation.
    pub(super) fn typed_eq(&mut self, a: Expr, b: Expr) -> Expr {
        // Two constants: compared now (unless that is an error).
        if let Some(Value::Bool(r)) = self.fold_op(B::Eq, &[a.clone(), b.clone()]) {
            return bool_lit(r);
        }
        // A stored value: TLC's equality in the store (the other side as a
        // handle).
        if self.is_ref(a.ty) || self.is_ref(b.ty) {
            let (a, b) = (self.as_handle(a), self.as_handle(b));
            return self.ref_op(crate::ir::RefOp::Eq, vec![a, b]);
        }
        // Same encoding: word equality, when TLC compares any two values of
        // the shapes without an error; otherwise equal words are still
        // equal values, and different ones are compared by TLC's rules
        // (e.g. a `Dyn` boolean and set: an error).
        if let (Ty::Enc(x), Ty::Enc(y)) = (a.ty, b.ty) {
            let (ok, apart) = match (self.shape_of(a.ty), self.shape_of(b.ty)) {
                (Some(sx), Some(sy)) => (pair_comparable(sx, sy, true), no_common_value(sx, sy)),
                _ => (false, false),
            };
            if !ok {
                if let Some(result) = self.atom_pair_eq(&a, &b) {
                    return result;
                }
            }
            if x == y {
                if ok {
                    return eq(a, b);
                }
                let (a, bind_a) = self.share(a);
                let (b, bind_b) = self.share(b);
                let checked = or(vec![eq(a.clone(), b.clone()), eq(to_val(a), to_val(b))]);
                return let_in(bind_b.into_iter().chain(bind_a), checked);
            }
            if ok {
                if let Some((a2, b2)) = self.common_encoding(&a, &b) {
                    return eq(a2, b2);
                }
                // Kinds that hold no common value: every comparison is
                // `false` (so the encodings need not be brought together).
                // Both operands are still evaluated: TLC reports an error
                // inside either of them.
                if apart {
                    let (_, bind_a) = self.share(a);
                    let (_, bind_b) = self.share(b);
                    return let_in(bind_b.into_iter().chain(bind_a), bool_lit(false));
                }
            }
        }
        // Encoded vs constant: encode the constant (if it does not fit the
        // shape, fall back to TLC's general equality).
        for (enc, other) in [(&a, &b), (&b, &a)] {
            if let (Ty::Enc(sid), ExprKind::Const(v)) = (enc.ty, &*other.kind) {
                if let Some(Shape::Atom(atoms)) = self.shape_of(enc.ty) {
                    // Keep the cheaper word comparison when the universe is
                    // total; only rejected universes need a truth/error table.
                    if comparable(self.typing.shape(sid), v) {
                        if let Some(c) = self.const_words(v, sid) {
                            return eq(enc.clone(), c);
                        }
                    } else if atoms.len() <= 256 {
                        let table = atoms.iter().map(|a| tlx_value::order::eq_tlc(a, v).map_or(-1, i32::from)).collect();
                        return self.truth_error_table(enc.clone(), table);
                    }
                }
                if let Some(c) = self.const_words(v, sid) {
                    // A Dyn (also nested) accepts any constant, but unequal
                    // handles still need TLC's incomparable-value check.
                    return self.typed_eq(enc.clone(), c);
                }
                // A constant outside the shape, comparable with all its
                // values without a TLC error: never equal.
                if v.normalize().is_ok_and(|v| comparable(self.typing.shape(sid), &v)) {
                    let (_, bind) = self.share(enc.clone());
                    return let_in(bind, bool_lit(false));
                }
            }
        }
        // A union with an integer arm vs an integer: other arms holding only
        // untyped model values are unequal to any integer (no error).
        for (u, i) in [(&a, &b), (&b, &a)] {
            if let (Some(Shape::Union(_)), Ok(iv)) = (self.shape_of(u.ty), self.as_int(i.clone())) {
                if !matches!(self.shape_of(i.ty), Some(Shape::Union(_))) {
                    if let Some(x) = self.union_int_eq(u, iv) {
                        return x;
                    }
                }
            }
        }
        let a = match self.as_int(a) {
            Ok(ai) => match self.as_int(b.clone()) {
                Ok(bi) => return eq(ai, bi),
                Err(_) => to_val(ai),
            },
            Err(a) => a,
        };
        if let (Ok(x), Ok(y)) = (self.as_bool(a.clone()), self.as_bool(b.clone())) {
            return eq(x, y);
        }
        if diag::enabled(Topic::Eq) {
            diag::emit(Topic::Eq, format_args!("boxed: {:?} {:?} / {:?} {:?}", a.ty, self.shape_of(a.ty), b.ty, self.shape_of(b.ty)));
        }
        eq(to_val(a), to_val(b))
    }
}

/// The value of a constant expression (possibly converted).
pub(super) fn const_of(x: &Expr) -> Option<Value> {
    match &*x.kind {
        ExprKind::Const(v) => Some(v.clone()),
        ExprKind::Convert(y) => const_of(y),
        _ => None,
    }
}

/// `s` with homogeneous non-empty tuples (also nested in records and
/// tuples) replaced by sequences of their length.
fn seqify(s: &Shape) -> Shape {
    match s {
        Shape::Tuple(es) if !es.is_empty() && es.iter().all(|e| *e == es[0]) => {
            Shape::Seq { elem: Box::new(seqify(&es[0])), max_len: es.len() }
        }
        Shape::Tuple(es) => Shape::Tuple(es.iter().map(seqify).collect()),
        Shape::Record(fs) => Shape::Record(fs.iter().map(|(n, f)| (*n, seqify(f))).collect()),
        _ => s.clone(),
    }
}

/// Element shape and capacity of a sequence or non-empty homogeneous tuple.
fn seq_like(s: &Shape) -> Option<(Shape, usize)> {
    match s {
        Shape::Seq { elem, max_len } => Some(((**elem).clone(), *max_len)),
        Shape::Tuple(es) if !es.is_empty() && es.iter().all(|e| *e == es[0]) => Some((es[0].clone(), es.len())),
        _ => None,
    }
}

/// Whether TLC compares (`equals`, or `compareTo` in a set membership test)
/// every value of shape `a` with every value of shape `b` without an error,
/// so that comparing their encodings is exact. Conservative: `Dyn` and
/// pairs of different kinds (except untyped model values, which compare
/// with anything) are not. TLC fails on two values of different kinds
/// (`V/*Value.equals`), on a typed model value (`x_1`) and a value that is
/// not a model value of its type (`V/ModelValue.java:183-249`), and
/// compares sets of one size, records with the same fields and tuples of
/// one length elementwise.
pub(super) fn shapes_comparable(a: &Shape, b: &Shape) -> bool {
    pair_comparable(a, b, false)
}

/// `shapes_comparable`, and — with `unequal` — the pairs that are never
/// equal and never fail either (`no_common_value`): comparing them as
/// encodings is still exact, they answer `false`. Equality wants this
/// (`typed_eq`): a record against a tuple or a sequence is such a pair,
/// and its absence from `shapes_comparable` turned every comparison of a
/// union of records and tuples into `or(word equality, boxed equality)`,
/// whose boxed half becomes a host region. The other consumers of
/// `shapes_comparable` decide whether an operand may be *re-encoded* into
/// another shape's encoding, where a pair that is never equal but has no
/// conversion is not the same permission, so they keep the strict form.
fn pair_comparable(a: &Shape, b: &Shape, unequal: bool) -> bool {
    use Shape as S;
    let untyped_mv = |x: &Value| matches!(x, Value::ModelValue(m) if m.model_value_type().is_none());
    let mv_only = |s: &Shape| match s {
        S::Never => true,
        S::Atom(u) => u.iter().all(untyped_mv),
        _ => false,
    };
    let atoms = |x: &Value, y: &Value| {
        x == y
            || untyped_mv(x)
            || untyped_mv(y)
            || match (x, y) {
                (Value::Str(_), Value::Str(_)) => true,
                (Value::ModelValue(m), Value::ModelValue(n)) => m.model_value_type() == n.model_value_type(),
                _ => false,
            }
    };
    match (a, b) {
        _ if mv_only(a) || mv_only(b) => true,
        (S::Union(arms), _) => arms.iter().all(|x| pair_comparable(x, b, unequal)),
        (_, S::Union(arms)) => arms.iter().all(|y| pair_comparable(a, y, unequal)),
        (S::Bool, S::Bool) | (S::Int { .. }, S::Int { .. }) => true,
        (S::Atom(u), S::Atom(v)) => u.iter().all(|x| v.iter().all(|y| atoms(x, y))),
        (S::Set { elem: x, .. }, S::Set { elem: y, .. }) | (S::Seq { elem: x, .. }, S::Seq { elem: y, .. }) => {
            pair_comparable(x, y, unequal)
        }
        (S::Record(fs), S::Record(gs)) => {
            fs.len() != gs.len()
                || fs.iter().zip(gs.iter()).any(|(f, g)| f.0 != g.0)
                || fs.iter().zip(gs.iter()).all(|(f, g)| pair_comparable(&f.1, &g.1, unequal))
        }
        (S::Tuple(xs), S::Tuple(ys)) => xs.len() != ys.len() || xs.iter().zip(ys.iter()).all(|(x, y)| pair_comparable(x, y, unequal)),
        (S::Tuple(xs), S::Seq { elem, .. }) | (S::Seq { elem, .. }, S::Tuple(xs)) => xs.iter().all(|x| pair_comparable(x, elem, unequal)),
        (S::Fcn { dom: d, range: r }, S::Fcn { dom: e, range: s }) if d == e => pair_comparable(r, s, unequal),
        (S::Map { key: k, range: r }, S::Map { key: l, range: s }) if pair_comparable(k, l, unequal) => pair_comparable(r, s, unequal),
        _ if unequal && no_common_value(a, b) => true,
        _ => match (shape_fcn_like(a), shape_fcn_like(b)) {
            (Some(x), Some(y)) => x.comparable_with(&y, |r, s| pair_comparable(r, s, unequal)),
            _ => false,
        },
    }
}

/// Shapes that hold no common value: no value of `a` equals any value of
/// `b`, so a comparison of the two encodings can answer without bringing
/// them together. Only consulted where the comparison is already known
/// not to fail (`pair_comparable` with `unequal`); on its own it says
/// nothing about errors. Conservative: `false` wherever one value
/// could be in both shapes (a tuple and a sequence, two records of one
/// field set, two sets of other element encodings) and for the two empty
/// values, which TLC compares as equal whatever their kind.
fn no_common_value(a: &Shape, b: &Shape) -> bool {
    use Shape as S;
    match (a, b) {
        (S::Union(arms), _) => arms.iter().all(|x| no_common_value(x, b)),
        (_, S::Union(arms)) => arms.iter().all(|y| no_common_value(a, y)),
        (S::Record(fs), S::Record(gs)) => fs.len() != gs.len() || fs.iter().zip(gs.iter()).any(|(f, g)| f.0 != g.0),
        (S::Record(fs), S::Tuple(es)) | (S::Tuple(es), S::Record(fs)) => !fs.is_empty() || !es.is_empty(),
        (S::Record(fs), S::Seq { .. }) | (S::Seq { .. }, S::Record(fs)) => !fs.is_empty(),
        (S::Tuple(xs), S::Tuple(ys)) => xs.len() != ys.len(),
        _ => false,
    }
}

/// Domain keys of a function-like value, as far as TLC's function
/// comparison needs them.
#[derive(Clone, Copy, PartialEq)]
enum FcnKeys {
    Int,
    Str,
    Other,
}

/// A function-like shape or value (tuple, sequence, function; not a
/// record) seen by TLC's function comparison: its possible domain sizes,
/// the kind of its domain elements and its range shapes or values.
struct FcnLike<R> {
    min: usize,
    max: usize,
    keys: FcnKeys,
    ranges: Vec<R>,
}

impl<R> FcnLike<R> {
    /// Whether TLC compares any two such values without an error
    /// (`V/FcnRcdValue.equals` and `compareTo`, which tuples reach through
    /// `toFcnRcd`): domains of different sizes are unequal without looking
    /// at them; for one size the domain elements are compared first (an
    /// integer with a string is an error), then the values. Empty domains
    /// compare nothing. Records are left out: `V/RecordValue.equals` fails
    /// on any function whose domain is not all strings, whatever its size.
    fn comparable_with<S>(&self, other: &FcnLike<S>, range: impl Fn(&R, &S) -> bool) -> bool {
        let overlap = self.min.max(other.min).max(1) <= self.max.min(other.max);
        !overlap
            || (self.keys == other.keys
                && self.keys != FcnKeys::Other
                && self.ranges.iter().all(|r| other.ranges.iter().all(|s| range(r, s))))
    }
}

fn keys_of_values<'a>(mut ks: impl Iterator<Item = &'a Value>) -> FcnKeys {
    let mut keys = None;
    let all = ks.all(|k| {
        let kind = match k {
            Value::Int(_) => FcnKeys::Int,
            Value::Str(_) => FcnKeys::Str,
            _ => return false,
        };
        *keys.get_or_insert(kind) == kind
    });
    match keys {
        Some(k) if all => k,
        _ => FcnKeys::Other,
    }
}

fn shape_fcn_like(s: &Shape) -> Option<FcnLike<&Shape>> {
    Some(match s {
        Shape::Tuple(es) => FcnLike { min: es.len(), max: es.len(), keys: FcnKeys::Int, ranges: es.iter().collect() },
        Shape::Seq { elem, max_len } => FcnLike { min: 0, max: *max_len, keys: FcnKeys::Int, ranges: vec![&**elem] },
        Shape::Fcn { dom, range } => FcnLike { min: dom.len(), max: dom.len(), keys: keys_of_values(dom.iter()), ranges: vec![&**range] },
        Shape::Map { key, range } => {
            let keys = match &**key {
                Shape::Int { .. } => FcnKeys::Int,
                Shape::Atom(u) => keys_of_values(u.iter()),
                _ => FcnKeys::Other,
            };
            let max = key.cardinality().and_then(|n| usize::try_from(n).ok()).unwrap_or(usize::MAX);
            FcnLike { min: 0, max, keys, ranges: vec![&**range] }
        }
        _ => return None,
    })
}

fn value_fcn_like(v: &Value) -> Option<FcnLike<&Value>> {
    Some(match v {
        Value::Tuple(vs) => FcnLike { min: vs.len(), max: vs.len(), keys: FcnKeys::Int, ranges: vs.iter().collect() },
        Value::Fcn(ps, _) => FcnLike {
            min: ps.len(),
            max: ps.len(),
            keys: keys_of_values(ps.iter().map(|p| &p.0)),
            ranges: ps.iter().map(|p| &p.1).collect(),
        },
        _ => return None,
    })
}

/// Whether TLC compares every value of shape `s` with `v` without an error.
pub(super) fn comparable(s: &Shape, v: &Value) -> bool {
    let untyped_mv = |x: &Value| matches!(x, Value::ModelValue(m) if m.model_value_type().is_none());
    match (s, v) {
        _ if untyped_mv(v) => true,
        (Shape::Int { .. }, Value::Int(_)) | (Shape::Bool, Value::Bool(_)) => true,
        (Shape::Atom(_), Value::Str(_) | Value::ModelValue(_)) => shapes_comparable(s, &Shape::of(v)),
        (Shape::Atom(u), _) => u.iter().all(untyped_mv),
        (Shape::Set { elem, .. }, Value::Set(es)) => es.iter().all(|e| comparable(elem, e)),
        (Shape::Record(fs), Value::Record(vs)) => {
            fs.len() != vs.len()
                || fs.iter().zip(vs.iter()).any(|(f, x)| f.0 != x.0)
                || fs.iter().zip(vs.iter()).all(|(f, x)| comparable(&f.1, &x.1))
        }
        // Tuples of different lengths are unequal (no error).
        (Shape::Tuple(ss), Value::Tuple(vs)) => ss.len() != vs.len() || ss.iter().zip(vs.iter()).all(|(s, x)| comparable(s, x)),
        (Shape::Seq { elem, .. }, Value::Tuple(vs)) => vs.iter().all(|x| comparable(elem, x)),
        (Shape::Union(arms), _) => arms.iter().all(|a| comparable(a, v)),
        _ => match (shape_fcn_like(s), value_fcn_like(v)) {
            (Some(x), Some(y)) => x.comparable_with(&y, |r, x| comparable(r, x)),
            _ => false,
        },
    }
}
