//! Destination-driven construction: `expr_into` lowers an expression
//! directly into the encoding of a given shape (records, unions of records,
//! tuples, sequences, bitsets, functions with constant domains, set maps),
//! instead of building a boxed value and converting it. Anything else is
//! lowered normally and converted (`coerce_enc`); a value that does not fit
//! the shape is a layout miss at run time.

use tlx_layout::layout::bitset_universe;
use tlx_sema::builtins::Builtin as B;
use tlx_sema::hir::{self, BoundVars, ExprKind as H, OpRef};
use tlx_value::{Sym, Value};

use super::*;

/// Longest sequence capacity converted element by element.
const MAX_SEQ_COERCED: usize = 16;

impl Lowerer<'_> {
    /// Lower `e` directly into the encoding of shape `sid`.
    pub(super) fn expr_into(&mut self, e: &hir::Expr, env: &LEnv, st: &St, sid: ShapeId) -> Expr {
        let shape = self.typing.shape(sid).clone();
        if let Some(v) = self.const_value(e, env) {
            return self.coerce_enc(const_expr(v), sid);
        }
        if let Shape::Ref(_) = shape {
            return self.ref_expr(e, env, st);
        }
        let built = match (&*e.kind, &shape) {
            (H::Record(fields), Shape::Record(fs)) => self.record_into(fields, fs, env, st, sid),
            (H::Record(fields), Shape::Union(arms)) => self.union_record_into(e, fields, arms, env, st, sid),
            (H::Tuple(es), Shape::Tuple(shapes)) => self.tuple_into(es, shapes, env, st, sid),
            (H::Tuple(es), Shape::Seq { elem, max_len }) => self.seq_into(es, elem, *max_len, env, st, sid),
            (H::SetEnum(es), Shape::Set { elem, .. }) => self.set_enum_into(es, elem, env, st, sid),
            (H::FnConstruct { bounds, body }, Shape::Fcn { .. } | Shape::Tuple(_)) => self.fcn_into(bounds, body, env, st, sid),
            (H::FnConstruct { bounds, body }, Shape::Map { .. }) => self.map_build_into(bounds, body, env, st, sid),
            (H::FnConstruct { bounds, body }, Shape::Seq { elem, max_len }) => {
                self.seq_fcn_into(bounds, body, elem, *max_len, env, st, sid)
            }
            (H::Builtin { op: B::ColonGt, args }, Shape::Map { .. }) if !self.ip.is_builtin_overridden(B::ColonGt) => {
                self.map_single_into(&args[0], &args[1], env, st, sid)
            }
            (H::Builtin { op: B::AtAt, args }, Shape::Map { .. }) if !self.ip.is_builtin_overridden(B::AtAt) => {
                self.map_merge_into(&args[0], &args[1], env, st, sid)
            }
            (H::Builtin { op: B::AtAt, args }, Shape::Fcn { .. }) if !self.ip.is_builtin_overridden(B::AtAt) => {
                self.fcn_merge_into(&args[0], &args[1], env, st, sid)
            }
            (H::Builtin { op: B::DotDot, args }, Shape::Set { elem, .. }) if !self.ip.is_builtin_overridden(B::DotDot) => {
                self.interval_into(&args[0], &args[1], elem, env, st, sid)
            }
            (H::SetMap { expr: f, bounds }, Shape::Set { elem, .. }) => self.set_map_into(f, bounds, elem, env, st, sid),
            (H::Builtin { op: B::Union, args }, Shape::Set { .. }) if !self.ip.is_builtin_overridden(B::Union) => {
                self.big_union_into(&args[0], sid, env, st)
            }
            (H::Builtin { op: B::Cup, args }, Shape::Set { elem, .. })
                if !self.ip.is_builtin_overridden(B::Cup) && typed::shapes_comparable(elem, elem) =>
            {
                if self.is_bitset(Ty::Enc(sid)) {
                    // The destination consumes a normalized set, so lazy
                    // operands may be constructed directly into its bitset.
                    // General union expressions still retain their lazy
                    // enumeration (including duplicates) in typed_union.
                    let a = self.expr_into(&args[0], env, st, sid);
                    let b = self.expr_into(&args[1], env, st, sid);
                    let bound = self.bitset_bound(a.ty).zip(self.bitset_bound(b.ty)).map(|(a, b)| a + b);
                    let union = Expr::new(Ty::Enc(sid), ExprKind::BitSetOp(SetOp::Union, a, b));
                    Some(self.card_checked(union, bound))
                } else {
                    self.sorted_union_into(&args[0], &args[1], env, st, sid)
                }
            }
            (H::SetFilter { bound, pred }, Shape::Set { elem, .. }) => {
                let x = self.expr(e, env, st);
                if x.ty == Ty::Enc(sid) {
                    Some(x)
                } else {
                    self.set_filter_into(bound, pred, elem, env, st, sid)
                }
            }
            (H::Apply { op: OpRef::Def(d), args }, _) if args.is_empty() => self.def_into(e, *d, env, st, sid),
            (H::Apply { op, args }, _) if !args.is_empty() && !matches!(op, OpRef::Builtin(_)) => {
                self.inline_with(*op, args, env, st, Some(sid))
            }
            (H::If { cond, then, els }, _) => {
                if let Some(b) = self.const_bool(cond, env) {
                    return self.expr_into(if b { then } else { els }, env, st, sid);
                }
                let c = self.bool_expr(cond, env, st);
                let t = self.expr_into(then, env, st, sid);
                let f = self.expr_into(els, env, st, sid);
                Some(Expr::new(Ty::Enc(sid), ExprKind::If(c, t, f)))
            }
            (H::Except { base, updates }, _) => {
                // Build the base in the target encoding, then update it.
                let b = self.expr_into(base, env, st, sid);
                if b.ty != Ty::Enc(sid) {
                    None
                } else {
                    let mut cur = b;
                    let mut ok = true;
                    for (keys, val) in updates {
                        match self.except_path(cur.clone(), keys, val, env, st) {
                            Some(x) => cur = x,
                            None => {
                                ok = false;
                                break;
                            }
                        }
                    }
                    ok.then_some(cur)
                }
            }
            (H::Case { arms, other }, _) => {
                let (arms, other) = self.live_case_arms(arms, other.as_ref(), env);
                let mut acc = match other {
                    Some(o) => self.expr_into(o, env, st, sid),
                    None => Expr::new(Ty::Enc(sid), ExprKind::Fail("No CASE arm is true.".into())),
                };
                for (g, v) in arms.iter().rev() {
                    let c = self.bool_expr(g, env, st);
                    let t = self.expr_into(v, env, st, sid);
                    acc = Expr::new(Ty::Enc(sid), ExprKind::If(c, t, acc));
                }
                Some(acc)
            }
            (H::Let { defs, body }, _) => {
                let (env2, lets) = self.let_temps(defs, body, env, st);
                let out = self.expr_into(body, &env2, st, sid);
                Some(let_in(lets.into_iter().rev(), out))
            }
            (H::Local(l), _) => match env.lookup(*l, &self.ip.prog) {
                Some(LBind::Thunk(te, tenv)) => Some(self.expr_into(&te, &tenv, st, sid)),
                _ => None,
            },
            // A field of a record literal (e.g. behind an operator call).
            (H::Field { record, field }, _) => match self.peel_call(record, env) {
                Some((r, renv)) => match &*r.kind {
                    H::Record(fs) => {
                        let es: Vec<&hir::Expr> = fs.iter().map(|(_, e)| e).collect();
                        let i = fs.iter().position(|(n, _)| **n == **field).filter(|&i| self.others_infallible(&es, i, &renv));
                        i.map(|i| es[i].clone()).map(|fe| self.expr_into(&fe, &renv, st, sid))
                    }
                    _ => None,
                },
                None => None,
            },
            // A (recursive) function definition applied.
            (H::FnApp { func, args }, _) => self.inline_fn_def_into(func, args, env, st, Some(sid)).map(|x| self.coerce_enc(x, sid)),
            _ => None,
        };
        match built {
            Some(x) => self.regions_post(e, env, x),
            None => {
                let x = self.expr(e, env, st);
                self.coerce_enc(x, sid)
            }
        }
    }

    /// `x` in the encoding of shape `sid`: constants are encoded at compile
    /// time; other representations are converted at run time.
    pub(super) fn coerce_enc(&mut self, x: Expr, sid: ShapeId) -> Expr {
        if x.ty == Ty::Enc(sid) {
            return x;
        }
        if let ExprKind::Fail(m) = &*x.kind {
            return Expr::new(Ty::Enc(sid), ExprKind::Fail(m.clone()));
        }
        if self.is_ref(Ty::Enc(sid)) {
            return self.as_handle(x);
        }
        if self.is_ref(x.ty) {
            return self.handle_into(x, sid);
        }
        if let ExprKind::Const(v) = &*x.kind {
            if let Some(c) = self.const_words(v, sid) {
                return c;
            }
            // A constant outside the shape: converting it fails at run time
            // (e.g. the `<<>>` branch of an IF building a pair).
            if v.normalize().is_ok_and(|n| !self.typing.shape(sid).contains(&n)) {
                return Expr::new(Ty::Enc(sid), ExprKind::Fail("constant outside the layout".into()));
            }
        }
        if let Some(r) = self.recode(&x, sid) {
            return r;
        }
        if let Some(r) = self.bitset_retype(&x, sid) {
            let bound = self.bitset_bound(x.ty);
            return self.card_checked(r, bound);
        }
        if let Some(r) = self.union_arm_coerce(&x, sid) {
            return r;
        }
        if let Some(r) = self.seq_tuple_coerce(&x, sid) {
            return r;
        }
        if let Some(r) = self.map_coerce(&x, sid) {
            return r;
        }
        if let Some(r) = self.struct_coerce(&x, sid) {
            return r;
        }
        if let Some(r) = self.union_to_union(&x, sid) {
            return r;
        }
        if let Some(r) = self.set_recode(&x, sid) {
            return r;
        }
        // Re-encode scalars through their unboxed form.
        let x = match self.shape_of(Ty::Enc(sid)) {
            Some(Shape::Int { .. }) => either(self.as_int(x)),
            Some(Shape::Bool) => either(self.as_bool(x)),
            _ => x,
        };
        Expr::new(Ty::Enc(sid), ExprKind::Convert(x))
    }

    /// `x` (a scalar or union of scalars) re-encoded into shape `sid` by a
    /// static table.
    pub(super) fn recode(&self, x: &Expr, sid: ShapeId) -> Option<Expr> {
        let Ty::Enc(from) = x.ty else { return None };
        let t = &self.typing;
        let (src, dst) = (t.shape(from), t.shape(sid));
        if !is_scalarish(dst) || matches!(dst, Shape::Int { .. } | Shape::Bool) && !matches!(src, Shape::Union(_)) {
            return None;
        }
        let (codes, arm_base) = scalar_codes(src)?;
        let n = t.words(sid) as usize;
        let mut table = Vec::with_capacity(codes.len() * n);
        for v in &codes {
            let mut w = vec![0u64; n];
            match tlx_layout::layout::encode(dst, v, &mut w) {
                Ok(()) => table.extend(w),
                Err(_) => {
                    table.push(u64::MAX);
                    table.extend(std::iter::repeat_n(0, n - 1));
                }
            }
        }
        Some(Expr::new(Ty::Enc(sid), ExprKind::Recode { x: x.clone(), arm_base: arm_base.into(), table: table.into(), words: n as u32 }))
    }

    /// A union value narrowed to its arm of shape `sid` (other arms: runtime
    /// error), or an arm value wrapped into the union shape `sid`.
    pub(super) fn union_arm_coerce(&mut self, x: &Expr, sid: ShapeId) -> Option<Expr> {
        let Ty::Enc(from) = x.ty else { return None };
        let (src, dst) = (self.shape_of(Ty::Enc(from))?.clone(), self.shape_of(Ty::Enc(sid))?.clone());
        if let Shape::Union(arms) = &src {
            let Some(i) = arms.iter().position(|a| *a == dst) else {
                // The arm of the target's kind, then converted (e.g. a
                // tuple arm into a tuple of narrower integer ranges).
                if matches!(dst, Shape::Union(_)) {
                    return None;
                }
                let arm = arms.iter().find(|a| a.kind_key().is_some() && a.kind_key() == dst.kind_key())?.clone();
                let asid = self.sid(&arm);
                let narrowed = self.union_arm_coerce(x, asid)?;
                let conv = self.coerce_enc(narrowed, sid);
                return (!matches!(&*conv.kind, ExprKind::Convert(_))).then_some(conv);
            };
            let (x, bind) = self.share(x.clone());
            let payload = Expr::new(Ty::Enc(sid), ExprKind::Slice { base: x.clone(), loc: FieldLoc::Words(1) });
            let tag = Expr::new(Ty::Int, ExprKind::Rank(x));
            let fail = Expr::new(Ty::Enc(sid), ExprKind::Fail("value of an unexpected kind".into()));
            return Some(let_in(bind, Expr::new(Ty::Enc(sid), ExprKind::If(eq(tag, int_lit(i as i64)), payload, fail))));
        }
        if let Shape::Union(arms) = &dst {
            let Some(i) = arms.iter().position(|a| *a == src) else {
                // A value of the kind of one arm (e.g. a tuple of a narrower
                // shape than the arm of its length): converted into that arm
                // first (a value not fitting it is a runtime layout miss).
                if matches!(src, Shape::Union(_)) {
                    return None;
                }
                let arm = arms.iter().find(|a| a.kind_key().is_some() && a.kind_key() == src.kind_key())?.clone();
                let asid = self.sid(&arm);
                let conv = self.coerce_enc(x.clone(), asid);
                if conv.ty != Ty::Enc(asid) || matches!(&*conv.kind, ExprKind::Convert(_)) {
                    return None;
                }
                return self.union_arm_coerce(&conv, sid);
            };
            let pad = self.words(sid) as usize - 1 - self.words(from) as usize;
            let mut parts = vec![self.raw_word(i as u64), x.clone()];
            parts.extend(self.zero_pad(pad));
            return Some(Expr::new(Ty::Enc(sid), ExprKind::Concat(parts)));
        }
        None
    }

    /// A union value re-encoded into another union shape `sid`: each arm
    /// goes to the target arm of its kind (converted if the arm shapes
    /// differ; a value not fitting it is a runtime layout miss). None if an
    /// arm has no counterpart or cannot be converted natively.
    pub(super) fn union_to_union(&mut self, x: &Expr, sid: ShapeId) -> Option<Expr> {
        let (Some(Shape::Union(src)), Some(Shape::Union(dst))) = (self.shape_of(x.ty).cloned(), self.shape_of(Ty::Enc(sid)).cloned())
        else {
            return None;
        };
        if src.len() > 16 {
            return None;
        }
        let (xs, bind) = self.share(x.clone());
        let tag = self.int_word(xs.clone(), 0, src.len() as i64 - 1);
        let mut out = Expr::new(Ty::Enc(sid), ExprKind::Fail("value of an unexpected kind".into()));
        for (i, arm) in src.iter().enumerate().rev() {
            let target = dst.iter().find(|d| d.kind_key() == arm.kind_key())?;
            let (asid, tsid) = (self.sid(arm), self.sid(target));
            let payload = Expr::new(Ty::Enc(asid), ExprKind::Slice { base: xs.clone(), loc: FieldLoc::Words(1) });
            let conv = self.coerce_enc(payload, tsid);
            if matches!(&*conv.kind, ExprKind::Convert(y) if matches!(y.ty, Ty::Val | Ty::Enc(_))) {
                return None;
            }
            let wrapped = self.union_arm_coerce(&conv, sid)?;
            out = Expr::new(Ty::Enc(sid), ExprKind::If(eq(tag.clone(), int_lit(i as i64)), wrapped, out));
        }
        Some(let_in(bind, out))
    }

    /// `x` narrowed to its only union arm satisfying `want` (other arms:
    /// runtime error, as where TLC requires a value of that kind); `x`
    /// itself if it is not a union or no single arm qualifies.
    pub(super) fn narrow_union(&mut self, x: Expr, want: impl Fn(&Shape) -> bool) -> Expr {
        let Some(Shape::Union(arms)) = self.shape_of(x.ty).cloned() else { return x };
        let found: Vec<&Shape> = arms.iter().filter(|a| want(a)).collect();
        let [arm] = found[..] else { return x };
        let asid = self.sid(arm);
        let (xs, bind) = self.share(x.clone());
        match self.union_arm_coerce(&xs, asid) {
            Some(n) => let_in(bind, n),
            None => x,
        }
    }

    /// `x` as a set operand: a union narrowed to its set arm.
    pub(super) fn set_operand(&mut self, x: Expr) -> Expr {
        self.narrow_union(x, |a| matches!(a, Shape::Set { .. }))
    }

    /// Between a sequence and a fixed-length tuple of the same element
    /// encoding (a sequence of another length is a runtime error).
    fn seq_tuple_coerce(&mut self, x: &Expr, sid: ShapeId) -> Option<Expr> {
        let Ty::Enc(from) = x.ty else { return None };
        let (src, dst) = (self.shape_of(Ty::Enc(from))?.clone(), self.shape_of(Ty::Enc(sid))?.clone());
        match (&src, &dst) {
            (Shape::Seq { elem, max_len }, Shape::Tuple(es)) if es.iter().all(|e| e == &**elem) && es.len() <= *max_len => {
                let n = es.len() as i64;
                let (x, bind) = self.share(x.clone());
                let len = Expr::new(Ty::Int, ExprKind::SeqLen(x.clone()));
                let payload = Expr::new(Ty::Enc(sid), ExprKind::Slice { base: x, loc: FieldLoc::Words(1) });
                let fail = Expr::new(Ty::Enc(sid), ExprKind::Fail("sequence of an unexpected length".into()));
                Some(let_in(bind, Expr::new(Ty::Enc(sid), ExprKind::If(eq(len, int_lit(n)), payload, fail))))
            }
            (Shape::Seq { elem: e1, max_len: m1 }, Shape::Seq { elem: e2, max_len: m2 }) if e1 == e2 => {
                if m2 >= m1 {
                    let pad = self.words(sid) as usize - self.words(from) as usize;
                    let mut parts = vec![x.clone()];
                    parts.extend(self.zero_pad(pad));
                    Some(Expr::new(Ty::Enc(sid), ExprKind::Concat(parts)))
                } else {
                    // A shorter capacity: the prefix of the words, if it fits.
                    let (x, bind) = self.share(x.clone());
                    let len = Expr::new(Ty::Int, ExprKind::SeqLen(x.clone()));
                    let fits = Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Le, len, int_lit(*m2 as i64)));
                    let prefix = Expr::new(Ty::Enc(sid), ExprKind::Slice { base: x, loc: FieldLoc::Words(0) });
                    let fail = Expr::new(Ty::Enc(sid), ExprKind::Fail("sequence longer than the layout allows".into()));
                    Some(let_in(bind, Expr::new(Ty::Enc(sid), ExprKind::If(fits, prefix, fail))))
                }
            }
            (Shape::Tuple(es), Shape::Seq { elem, max_len }) if es.iter().all(|e| e == &**elem) && es.len() <= *max_len => {
                let pad = self.words(sid) as usize - 1 - self.words(from) as usize;
                let mut parts = vec![self.raw_word(es.len() as u64), x.clone()];
                parts.extend(self.zero_pad(pad));
                Some(Expr::new(Ty::Enc(sid), ExprKind::Concat(parts)))
            }
            // Other element shapes (e.g. a sequence of `0..6` into a tuple
            // of `1..4`): through the tuple of the source's (or
            // into the target's) element shape, component by component.
            (Shape::Seq { elem, max_len }, Shape::Tuple(es)) if es.len() <= *max_len => {
                let msid = self.sid(&Shape::Tuple(vec![(**elem).clone(); es.len()].into()));
                let t = self.seq_tuple_coerce(x, msid)?;
                let c = self.struct_coerce(&t, sid)?;
                Some(c)
            }
            (Shape::Tuple(es), Shape::Seq { elem, max_len }) if es.len() <= *max_len => {
                let msid = self.sid(&Shape::Tuple(vec![(**elem).clone(); es.len()].into()));
                let t = self.struct_coerce(x, msid)?;
                self.seq_tuple_coerce(&t, sid)
            }
            // Other element shapes (e.g. records whose integer fields have
            // other ranges): element by element, up to the length (a length
            // beyond the target's capacity is a runtime layout miss).
            (Shape::Seq { elem: e1, max_len: m1 }, Shape::Seq { elem: e2, max_len: m2 }) if *m1 <= MAX_SEQ_COERCED => {
                let (e1sid, e2sid) = (self.sid(e1), self.sid(e2));
                let s1 = SlotLayout::of(e1);
                let s2 = SlotLayout::of(e2);
                let (x, bind) = self.share(x.clone());
                let (n, bn) = self.share(Expr::new(Ty::Int, ExprKind::SeqLen(x.clone())));
                let lsid = self.sid(&Shape::Int { lo: 0, hi: *m2 as i64 });
                let mut locs = Vec::with_capacity(1 + *m2);
                let mut parts = Vec::with_capacity(1 + *m2);
                locs.push(FieldLoc::Words(0));
                parts.push(self.coerce_enc(n.clone(), lsid));
                for i in 1..=*m2 {
                    locs.push(s2.loc(1, i - 1));
                    if i > *m1 {
                        parts.push(self.zero_enc(e2sid));
                        continue;
                    }
                    let slot = Expr::new(Ty::Enc(e1sid), ExprKind::Slice { base: x.clone(), loc: s1.loc(1, i - 1) });
                    let c = self.coerce_enc(slot, e2sid);
                    if matches!(&*c.kind, ExprKind::Convert(y) if matches!(y.ty, Ty::Enc(_) | Ty::Val)) {
                        return None;
                    }
                    let inside = Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Le, int_lit(i as i64), n.clone()));
                    parts.push(Expr::new(Ty::Enc(e2sid), ExprKind::If(inside, c, self.zero_enc(e2sid))));
                }
                Some(let_in(bn.into_iter().chain(bind), self.pack_locs(sid, locs, parts)))
            }
            _ => None,
        }
    }

    /// A record / tuple / function re-encoded component by component into
    /// a shape of the same structure (same field names, length or domain),
    /// if every component can be converted natively.
    fn struct_coerce(&mut self, x: &Expr, sid: ShapeId) -> Option<Expr> {
        let Ty::Enc(from) = x.ty else { return None };
        let (src, dst) = (self.shape_of(Ty::Enc(from))?.clone(), self.shape_of(Ty::Enc(sid))?.clone());
        let src_fl = FieldLayout::of_shape(&src)?;
        let pairs: Vec<(Shape, Shape)> = match (&src, &dst) {
            (Shape::Record(a), Shape::Record(b)) if a.len() == b.len() && a.iter().zip(b.iter()).all(|(p, q)| p.0 == q.0) => {
                a.iter().zip(b.iter()).map(|(p, q)| (p.1.clone(), q.1.clone())).collect()
            }
            (Shape::Tuple(a), Shape::Tuple(b)) if a.len() == b.len() => a.iter().cloned().zip(b.iter().cloned()).collect(),
            (Shape::Fcn { dom: d1, range: r1 }, Shape::Fcn { dom: d2, range: r2 }) if d1 == d2 => {
                vec![((**r1).clone(), (**r2).clone()); d1.len()]
            }
            _ => return None,
        };
        let (xs, bind) = self.share(x.clone());
        let mut parts = Vec::with_capacity(pairs.len());
        for (&loc, (a, b)) in src_fl.locs.iter().zip(pairs) {
            let asid = self.sid(&a);
            let bsid = self.sid(&b);
            let slot = Expr::new(Ty::Enc(asid), ExprKind::Slice { base: xs.clone(), loc });
            let c = self.coerce_enc(slot, bsid);
            if matches!(&*c.kind, ExprKind::Convert(y) if matches!(y.ty, Ty::Enc(_) | Ty::Val)) {
                return None;
            }
            parts.push(c);
        }
        Some(let_in(bind, self.pack_shape(sid, parts)))
    }

    /// A set of scalars re-encoded element by element into a bitset of
    /// other scalars (e.g. atoms of another universe, integers of a larger
    /// range), or of elements convertible to rankable products / unions
    /// (e.g. sequences into tuples) into a bitset of those; an
    /// element outside the target universe is a runtime layout miss.
    fn set_recode(&mut self, x: &Expr, sid: ShapeId) -> Option<Expr> {
        let Ty::Enc(from) = x.ty else { return None };
        let (Some(Shape::Set { elem: e1, .. }), Some(Shape::Set { elem: e2, .. })) =
            (self.shape_of(Ty::Enc(from)).cloned(), self.shape_of(Ty::Enc(sid)).cloned())
        else {
            return None;
        };
        let scalarish = is_scalarish(&e1) && is_scalarish(&e2);
        if !(scalarish || rankable(&e2)) || !self.is_bitset(Ty::Enc(sid)) {
            return None;
        }
        let (src, ety) = self.typed_iter_in(x.clone(), true);
        if !src.is_typed_source() {
            return None;
        }
        let t = self.temp(ety);
        let probe = self.zero_enc(sid);
        let rank = match (&*e1, &*e2) {
            // Integers into a range that contains all of them: their rank
            // there (e.g. integers with an exact range into one with headroom).
            (Shape::Int { lo: l1, hi: h1 }, Shape::Int { lo: l2, hi: h2 }) => {
                if l1 < l2 || h1 > h2 {
                    return None;
                }
                self.bit_rank(&probe, &temp_ref(ety, t))?
            }
            _ if scalarish => {
                let e2sid = self.sid(&e2);
                let y = self.recode_to(temp_ref(ety, t), e2sid)?;
                self.bit_rank(&probe, &y)?
            }
            // Products and unions: each element converted.
            _ => {
                let e2sid = self.sid(&e2);
                let y = self.coerce_enc(temp_ref(ety, t), e2sid);
                if matches!(&*y.kind, ExprKind::Convert(_)) {
                    return None;
                }
                self.bit_rank(&probe, &y)?
            }
        };
        let bound = self.iter_bound(&src).map(|n| n as u64);
        Some(self.card_checked(Expr::new(Ty::Enc(sid), ExprKind::MapSet { bind: t, set: src, elem: rank, cond: None }), bound))
    }

    /// The all-zero encoding of shape `sid` (e.g. the empty bitset).
    pub(super) fn zero_enc(&self, sid: ShapeId) -> Expr {
        Expr::new(Ty::Enc(sid), ExprKind::ConstWords(vec![0u64; self.words(sid) as usize].into()))
    }

    /// One raw word (a union arm index or a sequence length) as a part of
    /// a `Concat`.
    fn raw_word(&mut self, w: u64) -> Expr {
        let sid = self.sid(&Shape::Int { lo: i64::MIN, hi: i64::MAX });
        Expr::new(Ty::Enc(sid), ExprKind::ConstWords(vec![w].into()))
    }

    /// `n` zero words padding a `Concat` (none if `n` is 0).
    fn zero_pad(&mut self, n: usize) -> Option<Expr> {
        if n == 0 {
            return None;
        }
        let sid = self.sid(&Shape::Tuple(vec![Shape::Int { lo: i64::MIN, hi: i64::MAX }; n].into()));
        Some(Expr::new(Ty::Enc(sid), ExprKind::ConstWords(vec![0u64; n].into())))
    }

    /// A record literal with exactly the fields of the record shape.
    fn record_into(&mut self, fields: &[(Arc<str>, hir::Expr)], fs: &[(Sym, Shape)], env: &LEnv, st: &St, sid: ShapeId) -> Option<Expr> {
        if fields.len() != fs.len() {
            return None;
        }
        let mut parts = Vec::new();
        for (name, fshape) in fs {
            let (_, fe) = fields.iter().find(|(n, _)| Sym::new(n) == *name)?;
            let fsid = self.sid(fshape);
            parts.push(self.expr_into(fe, env, st, fsid));
        }
        Some(self.pack_shape(sid, parts))
    }

    /// A record literal into a union: the arm with exactly its field names,
    /// after the arm index, padded to the width of the union.
    fn union_record_into(
        &mut self,
        e: &hir::Expr,
        fields: &[(Arc<str>, hir::Expr)],
        arms: &[Shape],
        env: &LEnv,
        st: &St,
        sid: ShapeId,
    ) -> Option<Expr> {
        let mut names: Vec<Sym> = fields.iter().map(|(n, _)| Sym::new(n)).collect();
        names.sort();
        let (i, arm) = arms
            .iter()
            .enumerate()
            .find(|(_, a)| matches!(a, Shape::Record(fs) if fs.len() == names.len() && fs.iter().map(|f| f.0).eq(names.iter().copied())))?;
        let asid = self.sid(arm);
        let rec = self.expr_into(e, env, st, asid);
        let pad = self.words(sid) as usize - 1 - self.words(asid) as usize;
        let mut parts = vec![self.raw_word(i as u64), rec];
        parts.extend(self.zero_pad(pad));
        Some(Expr::new(Ty::Enc(sid), ExprKind::Concat(parts)))
    }

    /// A tuple literal into a tuple shape of the same length.
    fn tuple_into(&mut self, es: &[hir::Expr], shapes: &[Shape], env: &LEnv, st: &St, sid: ShapeId) -> Option<Expr> {
        if es.len() != shapes.len() {
            return None;
        }
        let parts = es
            .iter()
            .zip(shapes)
            .map(|(x, xs)| {
                let xsid = self.sid(xs);
                self.expr_into(x, env, st, xsid)
            })
            .collect();
        Some(self.pack_shape(sid, parts))
    }

    /// A tuple literal into a sequence shape: length, elements, padding.
    fn seq_into(&mut self, es: &[hir::Expr], elem: &Shape, max_len: usize, env: &LEnv, st: &St, sid: ShapeId) -> Option<Expr> {
        if es.len() > max_len {
            return None;
        }
        let esid = self.sid(elem);
        match SlotLayout::of(elem) {
            SlotLayout::Words(ew) => {
                let mut parts = vec![self.raw_word(es.len() as u64)];
                for x in es {
                    parts.push(self.expr_into(x, env, st, esid));
                }
                parts.extend(self.zero_pad((max_len - es.len()) * ew));
                Some(Expr::new(Ty::Enc(sid), ExprKind::Concat(parts)))
            }
            slot @ SlotLayout::Bits(_) => {
                let mut locs = Vec::with_capacity(1 + es.len());
                let mut parts = Vec::with_capacity(1 + es.len());
                locs.push(FieldLoc::Words(0));
                parts.push(self.raw_word(es.len() as u64));
                for (i, x) in es.iter().enumerate() {
                    locs.push(slot.loc(1, i));
                    parts.push(self.expr_into(x, env, st, esid));
                }
                Some(Expr::new(Ty::Enc(sid), ExprKind::Pack { locs: locs.into(), parts }))
            }
        }
    }

    /// A set enumeration into a bitset: the ranks of its elements.
    fn set_enum_into(&mut self, es: &[hir::Expr], elem: &Shape, env: &LEnv, st: &St, sid: ShapeId) -> Option<Expr> {
        if !typed::shapes_comparable(elem, elem) {
            return None;
        }
        if !self.is_bitset(Ty::Enc(sid)) {
            // A sorted array: insert each element into the empty set.
            let (esid, ew, max_card) = self.sorted_elem(Ty::Enc(sid))?;
            let mut out = self.zero_enc(sid);
            for x in es {
                let lx = self.expr_into(x, env, st, esid);
                let lx = self.coerce_enc(lx, esid);
                out = Expr::new(Ty::Enc(sid), ExprKind::SortedInsert { set: out, elem: lx, elem_words: ew, max_card });
            }
            return Some(out);
        }
        let set_e = self.zero_enc(sid);
        let esid = self.sid(elem);
        let mut ranks = Vec::new();
        for x in es {
            let lx = if self.constructs(x, env) { self.expr_into(x, env, st, esid) } else { self.expr(x, env, st) };
            ranks.push(self.bit_rank(&set_e, &lx)?);
        }
        let bound = ranks.len() as u64;
        Some(self.card_checked(Expr::new(Ty::Enc(sid), ExprKind::BitSet(ranks)), Some(bound)))
    }

    /// `[x \in D |-> body]` for a constant domain equal to the domain of the
    /// function (or tuple) shape: the body for each key.
    fn fcn_into(&mut self, bounds: &[hir::Bound], body: &hir::Expr, env: &LEnv, st: &St, sid: ShapeId) -> Option<Expr> {
        if bounds.len() > 1 || matches!(&bounds.first()?.vars, BoundVars::Many(ls) if ls.len() > 1) {
            return self.fcn_product_into(bounds, body, env, st, sid);
        }
        let [b] = bounds else { return None };
        if self.const_domain(&b.set, env, st).is_none() {
            let BoundVars::Many(ls) = &b.vars else { return None };
            let [l] = &ls[..] else { return None };
            // A computed domain `1..n` into a tuple: n must be its length.
            let Some(Shape::Tuple(es)) = self.shape_of(Ty::Enc(sid)).cloned() else { return None };
            let n = self.seq_domain_len(&b.set, env, st)?;
            let k = es.len() as i64;
            let (n, bind) = self.share(n);
            let mut parts = Vec::new();
            for (i, xs) in es.iter().enumerate() {
                let env2 = env.bind(*l, LBind::Ir(int_lit(i as i64 + 1)));
                let xsid = self.sid(xs);
                let x = self.expr_into(body, &env2, st, xsid);
                parts.push(self.coerce_enc(x, xsid));
            }
            let built = self.pack_shape(sid, parts);
            let fail = Expr::new(Ty::Enc(sid), ExprKind::Fail("function of another length than the layout's tuple".into()));
            return Some(let_in(bind, Expr::new(Ty::Enc(sid), ExprKind::If(eq(n, int_lit(k)), built, fail))));
        }
        let dom = tlx_value::ops::enumerate_normalized(&self.const_domain(&b.set, env, st)?).ok()?;
        let (keys, slot_shapes): (Vec<Value>, Vec<Shape>) = match self.shape_of(Ty::Enc(sid))? {
            Shape::Fcn { dom: d, range } => (d.to_vec(), vec![(**range).clone(); d.len()]),
            Shape::Tuple(es) => ((1..=es.len() as i64).map(Value::Int).collect(), es.to_vec()),
            // A function over strings is a record (fields in shape order).
            Shape::Record(fs) => (fs.iter().map(|(n, _)| Value::Str(*n)).collect(), fs.iter().map(|(_, f)| f.clone()).collect()),
            _ => return None,
        };
        let mut sorted = keys.clone();
        sorted.sort();
        if sorted != dom || dom.len() > 64 {
            return None;
        }
        let mut parts = Vec::new();
        for (k, ks) in keys.into_iter().zip(slot_shapes) {
            let env2 = binders::bind_const(&b.vars, &k, env)?;
            let ksid = self.sid(&ks);
            parts.push(self.expr_into(body, &env2, st, ksid));
        }
        Some(self.pack_shape(sid, parts))
    }

    /// `[i \in 1..n |-> body]` into a sequence shape: the length, then the
    /// body for each index up to `n` (zero slots after it). A length beyond
    /// the capacity does not fit the layout (a runtime layout miss).
    #[allow(clippy::too_many_arguments)]
    fn seq_fcn_into(
        &mut self,
        bounds: &[hir::Bound],
        body: &hir::Expr,
        elem: &Shape,
        max_len: usize,
        env: &LEnv,
        st: &St,
        sid: ShapeId,
    ) -> Option<Expr> {
        let [b] = bounds else { return None };
        let BoundVars::Many(ls) = &b.vars else { return None };
        let [l] = &ls[..] else { return None };
        if max_len > 64 {
            return None;
        }
        let n = self.seq_domain_len(&b.set, env, st)?;
        if let ExprKind::Const(Value::Int(k)) = &*n.kind {
            if *k as usize > max_len {
                return None;
            }
        }
        let (n, bind) = self.share(n);
        let lsid = self.sid(&Shape::Int { lo: 0, hi: max_len as i64 });
        let slot_layout = SlotLayout::of(elem);
        let mut locs = Vec::with_capacity(1 + max_len);
        let mut parts = Vec::with_capacity(1 + max_len);
        locs.push(FieldLoc::Words(0));
        parts.push(self.coerce_enc(n.clone(), lsid));
        let esid = self.sid(elem);
        for i in 1..=max_len as i64 {
            locs.push(slot_layout.loc(1, (i - 1) as usize));
            let env2 = env.bind(*l, LBind::Ir(int_lit(i)));
            let x = self.expr_into(body, &env2, st, esid);
            let x = self.coerce_enc(x, esid);
            let slot = match &*n.kind {
                ExprKind::Const(Value::Int(k)) if i <= *k => x,
                ExprKind::Const(Value::Int(_)) => self.zero_enc(esid),
                _ => {
                    let inside = Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Le, int_lit(i), n.clone()));
                    Expr::new(Ty::Enc(esid), ExprKind::If(inside, x, self.zero_enc(esid)))
                }
            };
            parts.push(slot);
        }
        Some(let_in(bind, self.pack_locs(sid, locs, parts)))
    }

    /// The value of a set that is constant, or the fixed domain of an
    /// encoded function-like value (`DOMAIN f`).
    pub(super) fn const_domain(&mut self, set: &hir::Expr, env: &LEnv, st: &St) -> Option<Value> {
        if let Some(v) = self.const_value(set, env) {
            return Some(v);
        }
        let (p, penv) = self.peel(set, env)?;
        let H::Builtin { op: B::Domain, args } = &*p.kind else { return None };
        let d = self.typed_domain(&args[0], &penv, st)?;
        typed::const_of(&d)
    }

    /// The length `n` of a domain `1..n` (constant, or `1..hi` computed;
    /// an empty interval has length 0).
    pub(super) fn seq_domain_len(&mut self, set: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        Some(match self.const_domain(set, env, st) {
            Some(Value::Interval(1, k)) => int_lit(k.max(0)),
            Some(Value::Interval(lo, hi)) if hi < lo => int_lit(0),
            Some(v) if v.is_set() && tlx_value::ops::cardinality(&v).ok() == Some(0) => int_lit(0),
            Some(_) => return None,
            None => {
                // `DOMAIN s` over a sequence: its index range `1..Len(s)`.
                if let Some(n) = self.seq_domain_len_of_seq(set, env, st) {
                    return Some(n);
                }
                let (set, senv) = self.peel(set, env)?;
                let H::Builtin { op: B::DotDot, args } = &*set.kind else { return None };
                if self.ip.is_builtin_overridden(B::DotDot) || self.const_value(&args[0], &senv) != Some(Value::Int(1)) {
                    return None;
                }
                let hi = self.expr(&args[1], &senv, st);
                let hi = self.as_int(hi).ok()?;
                // 1..hi with hi < 1 is empty.
                let (hi, bind) = self.share(hi);
                let neg = Expr::new(Ty::Bool, ExprKind::IntCmp(CmpOp::Lt, hi.clone(), int_lit(0)));
                let_in(bind, Expr::new(Ty::Int, ExprKind::If(neg, int_lit(0), hi)))
            }
        })
    }

    /// `[x \in D |-> body]` without a target encoding, for a constant
    /// (enumerated) domain: the range encoding is inferred from the bodies
    /// (all of one encoding, booleans, or integers of known bounds), the
    /// function is a tuple for domains `1..n` and a function shape otherwise.
    /// Like the interpreter, every body is evaluated (in domain order).
    pub(super) fn typed_fn_construct(&mut self, bounds: &[hir::Bound], body: &hir::Expr, env: &LEnv, st: &St) -> Option<Expr> {
        let [b] = bounds else { return None };
        if !binders::single_binder(b) {
            return None;
        }
        let Some(dv) = self.const_domain(&b.set, env, st) else {
            let BoundVars::Many(ls) = &b.vars else { return None };
            return self.interval_fn_construct(bounds, ls[0], &b.set, body, env, st);
        };
        if !matches!(dv, Value::Set(_) | Value::Interval(..)) {
            return None; // a lazy function in TLC
        }
        let dom = tlx_value::ops::enumerate_normalized(&dv).ok()?;
        if dom.is_empty() || dom.len() > 64 {
            return None;
        }
        let mut xs = Vec::new();
        for k in &dom {
            let env2 = binders::bind_const(&b.vars, k, env)?;
            let x = self.expr(body, &env2, st);
            // A boxed body: give up early (lowering the others is wasted).
            if x.ty == Ty::Val && !matches!(&*x.kind, ExprKind::Const(_)) {
                return None;
            }
            xs.push(x);
        }
        let range = self.common_shape(&mut xs)?;
        let rsid = self.sid(&range);
        if SlotLayout::of(&range).array_words(dom.len()) > 1 << 12 {
            return None;
        }
        let parts: Vec<Expr> = xs.into_iter().map(|x| self.coerce_enc(x, rsid)).collect();
        if parts.iter().any(|p| matches!(&*p.kind, ExprKind::Convert(_)) && p.ty == Ty::Enc(rsid) && !self.is_scalar_conv(p)) {
            return None;
        }
        let ints = dom.iter().enumerate().all(|(i, d)| *d == Value::Int(i as i64 + 1));
        if dom.iter().all(|d| matches!(d, Value::Str(_))) {
            // A record: its fields in name order.
            let mut fields: Vec<(Sym, Expr)> =
                dom.iter().zip(parts).map(|(d, p)| (if let Value::Str(n) = d { *n } else { unreachable!() }, p)).collect();
            let (shared, binds): (Vec<(Sym, Expr)>, Vec<Option<(Temp, Expr)>>) = fields
                .drain(..)
                .map(|(n, p)| {
                    let (p, b) = self.share(p);
                    ((n, p), b)
                })
                .unzip();
            let mut fields = shared;
            fields.sort_by_key(|f| f.0);
            let shape = Shape::Record(fields.iter().map(|(n, _)| (*n, range.clone())).collect());
            let sid = self.sid(&shape);
            let body = self.pack_shape(sid, fields.into_iter().map(|(_, p)| p).collect());
            return Some(let_in(binds.into_iter().rev().flatten(), body));
        }
        let shape = if ints { Shape::Tuple(vec![range; dom.len()].into()) } else { Shape::Fcn { dom: dom.into(), range: Box::new(range) } };
        let sid = self.sid(&shape);
        Some(self.pack_shape(sid, parts))
    }

    /// A tuple / record literal without a target encoding: its components
    /// in their own encodings (booleans, integers of known bounds), else
    /// (tuples) a boxed tuple of the lowered components.
    pub(super) fn typed_product(&mut self, comps: &[(Option<Sym>, hir::Expr)], env: &LEnv, st: &St) -> Option<Expr> {
        let is_record = comps.first()?.0.is_some();
        let mut xs: Vec<Expr> = Vec::new();
        for (_, e) in comps {
            let x = self.expr(e, env, st);
            if is_record && x.ty == Ty::Val && !matches!(&*x.kind, ExprKind::Const(_)) {
                return None;
            }
            xs.push(x);
        }
        let mut shapes = Vec::new();
        let mut parts = Vec::new();
        let mut typed = true;
        for x in &xs {
            let sh = match x.ty {
                Ty::Enc(s) => Some(self.typing.shape(s).clone()),
                Ty::Bool => Some(Shape::Bool),
                // An integer of unknown range in a record: any TLC integer
                // (e.g. the numerators of DyadicRationals sums, whose
                // inferred ranges multiply). Records have no boxed fallback.
                Ty::Int => match self.int_range(x) {
                    Some((lo, hi)) => Some(Shape::Int { lo, hi }),
                    None if is_record => Some(Shape::Int { lo: i32::MIN as i64, hi: i32::MAX as i64 }),
                    None => None,
                },
                // A constant component: a shape holding it (preferably one
                // of the state's atom universes).
                Ty::Val => match &*x.kind {
                    ExprKind::Const(v) => self.fit_shape(std::slice::from_ref(v)),
                    _ => None,
                },
            };
            match sh {
                Some(sh) => {
                    let sid = self.sid(&sh);
                    parts.push(self.coerce_enc(x.clone(), sid));
                    shapes.push(sh);
                }
                None => typed = false,
            }
        }
        if !typed {
            return (!is_record).then(|| Expr::new(Ty::Val, ExprKind::Tuple(xs.into_iter().map(to_val).collect())));
        }
        if !is_record {
            let sid = self.sid(&Shape::Tuple(shapes.into()));
            return Some(self.pack_shape(sid, parts));
        }
        // Records: fields in name order (the evaluation order of the
        // literal is kept by binding the components first).
        let names: Vec<Sym> = comps.iter().map(|(n, _)| n.unwrap()).collect();
        let mut order: Vec<usize> = (0..names.len()).collect();
        order.sort_by_key(|&i| names[i]);
        if order.windows(2).any(|w| names[w[0]] == names[w[1]]) {
            return None;
        }
        let mut binds = Vec::new();
        let mut shared = Vec::new();
        for p in parts {
            let (p, b) = self.share(p);
            binds.push(b);
            shared.push(p);
        }
        let fields: Vec<(Sym, Shape)> = order.iter().map(|&i| (names[i], shapes[i].clone())).collect();
        let sid = self.sid(&Shape::Record(fields.into()));
        let body = self.pack_shape(sid, order.iter().map(|&i| shared[i].clone()).collect());
        Some(let_in(binds.into_iter().rev().flatten(), body))
    }

    /// `[x \in lo..hi |-> body]` with computed bounds of known ranges: a map
    /// over the integers the bounds allow, the range encoding inferred from
    /// the body (every element is built, as the interpreter does).
    fn interval_fn_construct(
        &mut self,
        bounds: &[hir::Bound],
        l: LocalId,
        set: &hir::Expr,
        body: &hir::Expr,
        env: &LEnv,
        st: &St,
    ) -> Option<Expr> {
        let s = self.expr(set, env, st);
        let ExprKind::ValOp { op: B::DotDot, args } = &*s.kind else { return None };
        if self.ip.is_builtin_overridden(B::DotDot) {
            return None;
        }
        let (lo, hi) = (self.as_int(args[0].clone()).ok()?, self.as_int(args[1].clone()).ok()?);
        let (klo, khi) = (self.int_range(&lo)?.0, self.int_range(&hi)?.1);
        if khi < klo || khi - klo >= 1024 {
            return None;
        }
        // The range encoding of the body, for a key of the possible range.
        let t = self.temp(Ty::Int);
        self.temp_ranges.insert(t, (klo, khi));
        let probe = self.expr(body, &env.bind(l, LBind::Ir(temp_ref(Ty::Int, t))), st);
        let range = match probe.ty {
            Ty::Enc(sid) => self.typing.shape(sid).clone(),
            Ty::Bool => Shape::Bool,
            Ty::Int => {
                let (a, b) = self.int_range(&probe)?;
                Shape::Int { lo: a, hi: b }
            }
            Ty::Val => return None,
        };
        let sid = self.sid(&Shape::Map { key: Box::new(Shape::Int { lo: klo, hi: khi }), range: Box::new(range) });
        if self.words(sid) > 1 << 12 {
            return None;
        }
        self.map_build_into(bounds, body, env, st, sid)
    }

    /// A conversion into an encoding that compiled code performs natively
    /// (an unboxed integer / boolean into its scalar encoding).
    fn is_scalar_conv(&self, p: &Expr) -> bool {
        match &*p.kind {
            ExprKind::Convert(x) => matches!(x.ty, Ty::Int | Ty::Bool),
            _ => true,
        }
    }

    /// One shape describing the values of all of `xs` (lowered values):
    /// a common encoding (scalars re-encoded to their join), booleans, or
    /// integers of statically known bounds. Re-encodes `xs` as needed.
    pub(super) fn common_shape(&mut self, xs: &mut [Expr]) -> Option<Shape> {
        // Mixed representations of scalars: unbox booleans and integers.
        if xs.iter().any(|x| x.ty != xs[0].ty) {
            for x in xs.iter_mut() {
                if matches!(self.shape_of(x.ty), Some(Shape::Bool)) {
                    *x = either(self.as_bool(x.clone()));
                } else if matches!(self.shape_of(x.ty), Some(Shape::Int { .. })) {
                    *x = either(self.as_int(x.clone()));
                }
            }
        }
        let first = xs.iter().find(|x| !(x.ty == Ty::Val && matches!(&*x.kind, ExprKind::Const(_))))?.ty;
        match first {
            Ty::Bool if xs.iter().all(|x| x.ty == Ty::Bool) => Some(Shape::Bool),
            Ty::Int if xs.iter().all(|x| x.ty == Ty::Int || matches!(&*x.kind, ExprKind::Const(Value::Int(_)))) => {
                let mut r: Option<(i64, i64)> = None;
                for x in xs.iter() {
                    // (Unknown bounds: any TLC integer; the encoding keeps
                    // the numeric order, which is TLC's.)
                    let (lo, hi) = self.int_range(x).unwrap_or((i32::MIN as i64, i32::MAX as i64));
                    r = Some(r.map_or((lo, hi), |(a, b)| (a.min(lo), b.max(hi))));
                }
                let (lo, hi) = r?;
                Some(Shape::Int { lo, hi })
            }
            Ty::Enc(s0) => {
                let mut j = s0;
                for x in xs.iter() {
                    match x.ty {
                        Ty::Enc(s) if s == j => {}
                        Ty::Enc(s) => j = self.joined_scalarish(j, s)?,
                        Ty::Val if matches!(&*x.kind, ExprKind::Const(_)) => {}
                        _ => return None,
                    }
                }
                for x in xs.iter_mut() {
                    if x.ty != Ty::Enc(j) {
                        let y = match &*x.kind {
                            ExprKind::Const(v) => self.const_words(v, j)?,
                            _ => self.recode_to(x.clone(), j)?,
                        };
                        *x = y;
                    }
                }
                Some(self.typing.shape(j).clone())
            }
            _ => None,
        }
    }

    /// `[x \in S, y \in T |-> e]`: one slot per tuple of the (constant)
    /// product domain, each built with the binders bound to its components.
    fn fcn_product_into(&mut self, bounds: &[hir::Bound], body: &hir::Expr, env: &LEnv, st: &St, sid: ShapeId) -> Option<Expr> {
        let Some(Shape::Fcn { dom, range }) = self.shape_of(Ty::Enc(sid)).cloned() else { return None };
        if dom.len() > 256 {
            return None;
        }
        let mut vars: Vec<(LocalId, Vec<Value>)> = Vec::new();
        for b in bounds {
            let BoundVars::Many(ls) = &b.vars else { return None };
            let set = tlx_value::ops::enumerate_normalized(&self.const_domain(&b.set, env, st)?).ok()?;
            for l in ls {
                vars.push((*l, set.clone()));
            }
        }
        // The product in lexicographic order must be the shape's domain.
        let mut keys: Vec<Vec<Value>> = vec![Vec::new()];
        for (_, set) in &vars {
            keys = keys.into_iter().flat_map(|k| set.iter().map(move |x| [k.clone(), vec![x.clone()]].concat())).collect();
        }
        if keys.len() != dom.len() || keys.iter().zip(dom.iter()).any(|(k, d)| *d != Value::Tuple(k.clone().into())) {
            return None;
        }
        let rsid = self.sid(&range);
        let mut parts = Vec::new();
        for k in keys {
            let mut env2 = env.clone();
            for ((l, _), x) in vars.iter().zip(k) {
                env2 = env2.bind(*l, LBind::Ir(const_expr(x)));
            }
            parts.push(self.expr_into(body, &env2, st, rsid));
        }
        Some(self.pack_shape(sid, parts))
    }

    /// `lo..hi` into a bitset of integers.
    fn interval_into(&mut self, lo: &hir::Expr, hi: &hir::Expr, elem: &Shape, env: &LEnv, st: &St, sid: ShapeId) -> Option<Expr> {
        let Shape::Int { lo: base, .. } = *elem else { return None };
        if !self.is_bitset(Ty::Enc(sid)) {
            return None;
        }
        let (l, h) = (self.expr(lo, env, st), self.expr(hi, env, st));
        let (l, h) = (self.as_int(l).ok()?, self.as_int(h).ok()?);
        let t = self.temp(Ty::Int);
        let rank = Expr::new(Ty::Int, ExprKind::IntBin(IntOp::Sub, temp_ref(Ty::Int, t), int_lit(base)));
        let src = Expr::new(Ty::Val, ExprKind::IntRange(l, h));
        let bound = self.iter_bound(&src).map(|n| n as u64);
        Some(self.card_checked(Expr::new(Ty::Enc(sid), ExprKind::MapSet { bind: t, set: src, elem: rank, cond: None }), bound))
    }

    /// `{f(x) : x \in S}` over an encoded or iterable `S`, each `f(x)` built
    /// in the element encoding (a rank, for bitsets).
    fn set_map_into(&mut self, f: &hir::Expr, bounds: &[hir::Bound], elem: &Shape, env: &LEnv, st: &St, sid: ShapeId) -> Option<Expr> {
        if !typed::shapes_comparable(elem, elem) {
            return None;
        }
        let [b] = bounds else { return None };
        if !binders::single_binder(b) {
            return None;
        }
        let bits = bitset_universe(elem).is_some();
        if bits && !rankable(elem) {
            return None;
        }
        let s = self.expr(&b.set, env, st);
        let (src, ety) = self.typed_iter_in(s, true);
        if !src.is_typed_source() {
            return None;
        }
        let t = self.iter_temp(ety, &src);
        let (env2, check) = self.bind_elem(&b.vars, &temp_ref(ety, t), env)?;
        let esid = self.sid(elem);
        let x = self.expr_into(f, &env2, st, esid);
        let x = binders::checked(check, self.coerce_enc(x, esid));
        let x = if bits {
            let probe = self.zero_enc(sid);
            self.bit_rank(&probe, &x)?
        } else {
            x
        };
        let bound = self.iter_bound(&src).map(|n| n as u64);
        Some(self.card_checked(Expr::new(Ty::Enc(sid), ExprKind::MapSet { bind: t, set: src, elem: x, cond: None }), bound))
    }

    /// `{x \in S : p}` built into the encoded set shape `sid` (S any typed
    /// iteration source, e.g. a constant set).
    pub(super) fn set_filter_into(
        &mut self,
        bound: &hir::Bound,
        pred: &hir::Expr,
        elem: &Shape,
        env: &LEnv,
        st: &St,
        sid: ShapeId,
    ) -> Option<Expr> {
        if !binders::single_binder(bound) {
            return None;
        }
        let bits = bitset_universe(elem).is_some();
        if bits && !rankable(elem) {
            return None;
        }
        let s = self.expr(&bound.set, env, st);
        let (src, ety) = self.typed_iter_in(s, true);
        if !src.is_typed_source() {
            return None;
        }
        let t = self.temp(ety);
        let x = temp_ref(ety, t);
        let (env2, check) = self.bind_elem(&bound.vars, &x, env)?;
        let cond = binders::checked(check, self.bool_expr(pred, &env2, st));
        let esid = self.sid(elem);
        let x = self.coerce_enc(x, esid);
        let x = if bits {
            let probe = self.zero_enc(sid);
            self.bit_rank(&probe, &x)?
        } else {
            x
        };
        let bound = self.iter_bound(&src).map(|n| n as u64);
        Some(self.card_checked(Expr::new(Ty::Enc(sid), ExprKind::MapSet { bind: t, set: src, elem: x, cond: Some(cond) }), bound))
    }

    /// Through a 0-ary definition (materialized ones are already encoded).
    fn def_into(&mut self, e: &hir::Expr, d: hir::DefId, env: &LEnv, st: &St, sid: ShapeId) -> Option<Expr> {
        if let Some(x) = self.materialized(d, st) {
            return Some(self.coerce_enc(x, sid));
        }
        let (b, benv) = self.peel(e, env)?;
        if let H::Apply { op, args } = &*b.kind {
            // A 0-ary definition standing for an operator call (`IncX ==
            // Inc("x")`): the call is built into the target too.
            if args.is_empty() || matches!(op, OpRef::Builtin(_)) {
                return None;
            }
            let def = self.ip.redirect_def(d);
            self.inline_stack.push(def);
            let x = self.inline_with(*op, args, &benv, st, Some(sid));
            self.inline_stack.pop();
            return x;
        }
        let def = self.ip.redirect_def(d);
        self.inline_stack.push(def);
        let x = self.expr_into(&b, &benv, st, sid);
        self.inline_stack.pop();
        Some(x)
    }
}

/// Syntactic value constructors that `expr_into` can build directly.
pub(super) fn is_constructor(e: &hir::Expr) -> bool {
    match &*e.kind {
        H::Let { body, .. } => is_constructor(body),
        // `UNION {f(x) : x \in S}` builds the destination's set directly.
        H::Builtin { op: B::Union, args } => matches!(&*args[0].kind, H::SetMap { .. }),
        k => matches!(
            k,
            H::Record(_)
                | H::Tuple(_)
                | H::SetEnum(_)
                | H::FnConstruct { .. }
                | H::If { .. }
                | H::Case { .. }
                | H::SetMap { .. }
                | H::SetFilter { .. }
        ),
    }
}

/// A scalar, or a union whose arms are all scalars.
pub(super) fn is_scalarish(s: &Shape) -> bool {
    match s {
        _ if s.is_scalar() => true,
        Shape::Union(arms) => arms.iter().all(Shape::is_scalar),
        _ => false,
    }
}

/// All values of a scalar(-ish) shape in code order (see `ExprKind::Recode`)
/// and, for a union, the first code of each arm.
fn scalar_codes(s: &Shape) -> Option<(Vec<Value>, Vec<u64>)> {
    fn arm(s: &Shape) -> Option<Vec<Value>> {
        match s {
            Shape::Int { lo, hi } if hi - lo < 1 << 16 => Some((*lo..=*hi).map(Value::Int).collect()),
            Shape::Atom(u) => Some(u.to_vec()),
            Shape::Bool => Some(vec![Value::FALSE, Value::TRUE]),
            _ => None,
        }
    }
    match s {
        Shape::Union(arms) => {
            let mut codes = Vec::new();
            let mut base = Vec::new();
            for a in arms.iter() {
                base.push(codes.len() as u64);
                codes.extend(arm(a)?);
            }
            Some((codes, base))
        }
        _ => Some((arm(s)?, Vec::new())),
    }
}
