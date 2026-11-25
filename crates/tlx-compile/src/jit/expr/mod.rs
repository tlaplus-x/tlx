//! Expressions (port of `cgen::expr`).

mod encoded;
mod maps;
mod refs;
mod sequences;
mod sets;

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{InstBuilder, Value};
use tlx_layout::layout::{bitset_universe, MapDims};
use tlx_layout::Shape;

use super::gen::{Buf, Gen, Known, MAX_SSA_WORDS};
use super::{no, Unsupported, I64, R};

/// Most operands of a conjunction / disjunction evaluated without branches
/// at a time, and the largest such operand (IR nodes): evaluating an
/// operand that a short-circuit would skip must stay cheap.
const MAX_EAGER: usize = 8;
const EAGER_NODES: usize = 12;
use crate::ir::*;
use crate::native_plan::site;
use crate::types::scalar_arm;

impl Gen<'_, '_, '_> {
    pub(super) fn bool_expr(&mut self, e: &Expr) -> R<Value> {
        match e.ty {
            Ty::Bool => self.expr(e),
            _ => no("non-boolean condition"),
        }
    }

    pub(super) fn int_expr(&mut self, e: &Expr) -> R<Value> {
        match e.ty {
            Ty::Int => self.expr(e),
            _ => no("non-integer operand"),
        }
    }

    fn words_of(&self, sid: ShapeId) -> usize {
        self.cx.ty.words(sid) as usize
    }

    /// A fresh buffer for the result of an expression of type `ty`, which
    /// must be encoded (else unsupported: `what`), and its size in words.
    fn result_buf(&mut self, ty: Ty, what: &str) -> R<(usize, Buf)> {
        let Ty::Enc(sid) = ty else { return no(what) };
        let n = self.words_of(sid);
        Ok((n, self.buf(n)))
    }

    /// Pointer to an encoding of `e` in shape `sid`.
    pub(super) fn encoded(&mut self, e: &Expr, sid: ShapeId) -> R<Value> {
        if e.ty == Ty::Enc(sid) {
            return self.expr(e);
        }
        match (e.ty, self.cx.ty.shape(sid).clone()) {
            (Ty::Int, Shape::Int { lo, hi }) => {
                let v = self.expr(e)?;
                let a = self.cmp_imm(IntCC::SignedGreaterThanOrEqual, v, lo);
                let b = self.cmp_imm(IntCC::SignedLessThanOrEqual, v, hi);
                let ok = self.b.ins().band(a, b);
                self.check(ok);
                let r = self.add_imm(v, lo.wrapping_neg());
                Ok(self.materialize(&[Known::Val(r)]))
            }
            (Ty::Bool, Shape::Bool) => {
                let v = self.expr(e)?;
                let c = self.cmp_imm(IntCC::NotEqual, v, 0);
                let c = self.b2i(c);
                Ok(self.materialize(&[Known::Val(c)]))
            }
            // The integer / boolean arm of a union (as `cgen`).
            (Ty::Int | Ty::Bool, Shape::Union(arms)) if scalar_arm(&arms, e.ty).is_some() => {
                let (k, lo, hi) = scalar_arm(&arms, e.ty).expect("arm");
                let v = self.expr(e)?;
                let a = self.cmp_imm(IntCC::SignedGreaterThanOrEqual, v, lo);
                let b = self.cmp_imm(IntCC::SignedLessThanOrEqual, v, hi);
                let ok = self.b.ins().band(a, b);
                self.check(ok);
                let r = self.add_imm(v, lo.wrapping_neg());
                let n = self.words_of(sid);
                let mut ws = vec![Known::Const(0); n];
                ws[0] = Known::Const(k as u64);
                ws[1] = Known::Val(r);
                if n <= MAX_SSA_WORDS {
                    return Ok(self.materialize(&ws));
                }
                let buf = self.buf(n);
                let p = self.addr(buf);
                self.zero(p, n);
                let kv = self.iconst(k as i64);
                self.store(kv, p, 0);
                self.store(r, p, 1);
                Ok(p)
            }
            // The host encodes it.
            _ if self.mixing && self.cx.has_region(site(e, true)) => {
                let rid = self.cx.take_region(site(e, true));
                self.region(rid, Ty::Enc(sid))
            }
            (t, s) => no(format!("representation change {t:?} -> {s:?}")),
        }
    }

    /// Pointer to the constant words `w` (their values are known).
    fn const_words(&mut self, w: &[u64]) -> Value {
        let a = self.cx.statics.words(w);
        let p = self.iconst(a);
        self.know(p, w.iter().map(|x| Known::Const(*x)).collect());
        p
    }

    /// A block taking one i64 parameter (the join of a value).
    fn join(&mut self) -> (cranelift_codegen::ir::Block, Value) {
        let j = self.b.create_block();
        let v = self.b.append_block_param(j, I64);
        (j, v)
    }

    /// The value of `e`: native code, or (mixed mode) a call of the region
    /// the C generator made of it.
    pub(super) fn expr(&mut self, e: &Expr) -> R<Value> {
        if self.mixing {
            let site = site(e, false);
            if self.cx.has_region(site) {
                let rid = self.cx.take_region(site);
                return self.region(rid, e.ty);
            }
            if e.has_boxed_operand() {
                return no("boxed operand");
            }
        }
        self.expr_native(e)
    }

    fn expr_native(&mut self, e: &Expr) -> R<Value> {
        if let (true, Ty::Enc(sid)) = (crate::inplace::is_update(e), e.ty) {
            // Copy the base once and update it in place (as `cgen`; small
            // encodings are built as words instead).
            let n = self.words_of(sid);
            if n > MAX_SSA_WORDS {
                let p = crate::inplace::plan(e, self.cx.ty);
                if !p.is_copy() {
                    let buf = self.buf(n);
                    let d = self.addr(buf);
                    self.plan_into(&p, d)?;
                    return Ok(d);
                }
            }
        }
        Ok(match &*e.kind {
            ExprKind::Const(v) => match (e.ty, v) {
                (Ty::Bool, tlx_value::Value::Bool(b)) => self.iconst(*b as i64),
                (Ty::Int, tlx_value::Value::Int(i)) => self.iconst(*i),
                (Ty::Enc(sid), v) => {
                    let mut w = vec![0u64; self.words_of(sid)];
                    tlx_layout::layout::encode(self.cx.ty.shape(sid), v, &mut w)
                        .map_err(|_| Unsupported("constant outside its shape".into()))?;
                    self.const_words(&w)
                }
                _ => return no("boxed constant"),
            },
            ExprKind::ConstWords(w) => self.const_words(w),
            ExprKind::ConstElems { .. } | ExprKind::IntRange(..) | ExprKind::Subsets(_) | ExprKind::OrderedSet { .. } => {
                return no("iteration source outside iteration")
            }
            ExprKind::Call { func, args } => {
                if !self.cx.fn_native.get(*func as usize).copied().unwrap_or(false) {
                    return no("call of a function that is not native");
                }
                let mut vals = Vec::new();
                for a in args {
                    if a.ty == Ty::Val {
                        return no("boxed value");
                    }
                    vals.push(self.expr(a)?);
                }
                // The outermost call starts the count of budgeted calls.
                let (depth, calls) = if self.in_fn {
                    let d = self.depth;
                    (self.b.ins().iadd_imm(d, 1), self.calls)
                } else {
                    let c = self.buf(1);
                    let p = self.addr(c);
                    let z = self.iconst(0);
                    self.store(z, p, 0);
                    (self.iconst(1), p)
                };
                let out = match e.ty {
                    Ty::Bool | Ty::Int => self.buf(1),
                    Ty::Enc(sid) => {
                        let n = self.words_of(sid);
                        self.buf(n)
                    }
                    Ty::Val => return no("boxed call"),
                };
                let op = self.addr(out);
                let (s0, s1) = (self.s0, self.s1);
                let mut all = vec![s0, s1, depth, calls];
                all.extend(vals);
                all.push(op);
                let rc = self.call_fn(*func, &all);
                let ok = self.cmp_imm(IntCC::Equal, rc, 0);
                self.check(ok);
                match e.ty {
                    Ty::Enc(_) => op,
                    _ => self.load(op, 0),
                }
            }
            ExprKind::Fail(_) => {
                if e.ty == Ty::Val && !self.mixing {
                    return no("boxed failure");
                }
                self.fail();
                self.iconst(0)
            }
            ExprKind::Var(i) => {
                let Ty::Enc(_) = e.ty else { return no("boxed variable read") };
                let s0 = self.s0;
                self.offset(s0, self.cx.ty.var_offset(*i as usize))
            }
            ExprKind::NextVar(i) => {
                let Ty::Enc(_) = e.ty else { return no("boxed variable read") };
                let s1 = self.s1;
                self.offset(s1, self.cx.ty.var_offset(*i as usize))
            }
            ExprKind::Temp(t) => self.temp(*t)?,
            ExprKind::Not(x) => {
                let v = self.bool_expr(x)?;
                let c = self.cmp_imm(IntCC::Equal, v, 0);
                self.b2i(c)
            }
            ExprKind::And(xs) | ExprKind::Or(xs) => {
                let and = matches!(&*e.kind, ExprKind::And(_));
                // Runs of cheap operands that cannot fail (`pure`) are
                // evaluated without branches. Constant operands fold: a
                // neutral one is skipped, a deciding one makes the rest
                // dead code.
                let mut join = None;
                let mut res = None;
                let mut k = 0;
                while k < xs.len() {
                    let mut end = k + 1;
                    if self.cheap(&xs[k]) {
                        while end < xs.len() && end - k < MAX_EAGER && self.cheap(&xs[end]) {
                            end += 1;
                        }
                    }
                    let mut c = self.bool_expr(&xs[k])?;
                    for x in &xs[k + 1..end] {
                        let d = self.bool_expr(x)?;
                        c = if and { self.and_i(c, d) } else { self.or_i(c, d) };
                    }
                    let last = end == xs.len();
                    match self.konst(c) {
                        Some(v) if (v != 0) != and => {
                            res = Some(c);
                            self.dead_code(|g| xs[end..].iter().try_for_each(|x| g.bool_expr(x).map(|_| ())))?;
                            break;
                        }
                        _ if last => res = Some(c),
                        Some(_) => {}
                        None => {
                            let (j, _) = *join.get_or_insert_with(|| self.join());
                            let next = self.b.create_block();
                            let short = self.iconst(!and as i64);
                            if and {
                                self.brif(c, next, &[], j, &[short.into()]);
                            } else {
                                self.brif(c, j, &[short.into()], next, &[]);
                            }
                            self.switch(next);
                        }
                    }
                    k = end;
                }
                let res = match res {
                    Some(c) => c,
                    None => self.iconst(and as i64),
                };
                match join {
                    None => res,
                    Some((j, r)) => {
                        self.b.ins().jump(j, &[res.into()]);
                        self.switch(j);
                        r
                    }
                }
            }
            ExprKind::If(c, t, f) => {
                if t.ty != f.ty {
                    return no("conditional with mixed representations");
                }
                if t.ty == Ty::Val && !self.mixing {
                    return no("boxed value");
                }
                let c = self.bool_expr(c)?;
                if let Some(k) = self.konst(c) {
                    let (live, dead) = if k != 0 { (t, f) } else { (f, t) };
                    let v = self.expr(live)?;
                    self.dead_code(|g| g.expr(dead).map(|_| ()))?;
                    return Ok(v);
                }
                let (tb, fb) = (self.b.create_block(), self.b.create_block());
                let (j, r) = self.join();
                self.brif(c, tb, &[], fb, &[]);
                self.switch(tb);
                let tv = self.expr(t)?;
                self.b.ins().jump(j, &[tv.into()]);
                self.switch(fb);
                let fv = self.expr(f)?;
                self.b.ins().jump(j, &[fv.into()]);
                self.switch(j);
                r
            }
            ExprKind::IntBin(op, a, b) => {
                let (a, b) = (self.int_expr(a)?, self.int_expr(b)?);
                self.int_bin(*op, a, b)
            }
            ExprKind::IntCmp(op, a, b) => {
                let cc = match op {
                    CmpOp::Lt => IntCC::SignedLessThan,
                    CmpOp::Le => IntCC::SignedLessThanOrEqual,
                    CmpOp::Gt => IntCC::SignedGreaterThan,
                    CmpOp::Ge => IntCC::SignedGreaterThanOrEqual,
                };
                let (a, b) = (self.int_expr(a)?, self.int_expr(b)?);
                let c = self.cmp(cc, a, b);
                self.b2i(c)
            }
            ExprKind::Neg(a) => {
                let a = self.int_expr(a)?;
                let r = self.b.ins().ineg(a);
                let ok = self.fits_i32(r);
                self.check(ok);
                r
            }
            ExprKind::Eq(a, b) => match (a.ty, b.ty) {
                (Ty::Enc(x), Ty::Enc(y)) if x == y => {
                    let n = self.words_of(x);
                    let (a, b) = (self.expr(a)?, self.expr(b)?);
                    self.eq_words(a, b, n)
                }
                (Ty::Int, Ty::Int) | (Ty::Bool, Ty::Bool) => {
                    let (a, b) = (self.expr(a)?, self.expr(b)?);
                    let c = self.cmp(IntCC::Equal, a, b);
                    self.b2i(c)
                }
                _ => return no("boxed equality"),
            },
            ExprKind::Convert(x) => match (x.ty, e.ty) {
                (Ty::Enc(sid), Ty::Int) => match self.cx.ty.shape(sid).clone() {
                    Shape::Int { lo, .. } => {
                        let p = self.expr(x)?;
                        let w = self.load(p, 0);
                        self.add_imm(w, lo)
                    }
                    _ => return no("conversion to integer"),
                },
                (Ty::Enc(sid), Ty::Bool) => match self.cx.ty.shape(sid) {
                    Shape::Bool => {
                        let p = self.expr(x)?;
                        let w = self.load(p, 0);
                        let c = self.cmp_imm(IntCC::NotEqual, w, 0);
                        self.b2i(c)
                    }
                    _ => return no("conversion to boolean"),
                },
                (_, Ty::Enc(sid)) => self.encoded(x, sid)?,
                (f, t) => return no(format!("conversion {f:?} -> {t:?}")),
            },
            ExprKind::Enabled(s) => {
                // The action over a scratch next state (shadowing `s1`).
                let words = self.cx.ty.layout.words;
                let scratch = self.buf(words);
                let sp = self.addr(scratch);
                self.zero(sp, words);
                let (j, r) = self.join();
                let saved_s1 = std::mem::replace(&mut self.s1, sp);
                let saved_en = self.enabled.replace(j);
                let res = self.stmt(s);
                self.s1 = saved_s1;
                self.enabled = saved_en;
                res?;
                let z = self.iconst(0);
                self.b.ins().jump(j, &[z.into()]);
                self.switch(j);
                r
            }
            ExprKind::Exists { bind, set, body } | ExprKind::Forall { bind, set, body } => {
                let want = matches!(&*e.kind, ExprKind::Exists { .. }) as i64;
                let (j, r) = self.join();
                self.foreach(*bind, set, None, Some((body, want == 0)), self.spec_exprs(&[body], *bind), &mut |g| {
                    let b = g.bool_expr(body)?;
                    let next = g.b.create_block();
                    let w = g.iconst(want);
                    if want == 1 {
                        g.brif(b, j, &[w.into()], next, &[]);
                    } else {
                        g.brif(b, next, &[], j, &[w.into()]);
                    }
                    g.switch(next);
                    Ok(())
                })?;
                let d = self.iconst(1 - want);
                self.b.ins().jump(j, &[d.into()]);
                self.switch(j);
                r
            }
            ExprKind::Choose { bind, set, body } if matches!(e.ty, Ty::Int | Ty::Bool) => {
                let (j, r) = self.join();
                self.foreach(*bind, set, None, Some((body, false)), self.spec_exprs(&[body], *bind), &mut |g| {
                    let b = g.bool_expr(body)?;
                    let next = g.b.create_block();
                    let t = g.temp(*bind)?;
                    g.brif(b, j, &[t.into()], next, &[]);
                    g.switch(next);
                    Ok(())
                })?;
                self.fail();
                self.switch(j);
                r
            }
            ExprKind::Choose { bind, set, body } => {
                let (en, out) = self.result_buf(e.ty, "boxed CHOOSE")?;
                let j = self.b.create_block();
                self.foreach(*bind, set, None, Some((body, false)), self.spec_exprs(&[body], *bind), &mut |g| {
                    let b = g.bool_expr(body)?;
                    let (yes, next) = (g.b.create_block(), g.b.create_block());
                    g.brif(b, yes, &[], next, &[]);
                    g.switch(yes);
                    // Copy the element out of the loop-scoped storage.
                    let t = g.temp(*bind)?;
                    let op = g.addr(out);
                    g.copy(op, t, en);
                    g.b.ins().jump(j, &[]);
                    g.switch(next);
                    Ok(())
                })?;
                self.fail();
                self.switch(j);
                self.addr(out)
            }
            ExprKind::Let { temp, value, body } => {
                if value.ty == Ty::Val && !self.mixing {
                    return no("boxed value");
                }
                let v = self.expr(value)?;
                self.with_temp(*temp, v, |g| g.expr(body))?
            }
            // ---- encoded values (`encoded.rs`)
            ExprKind::Slice { .. }
            | ExprKind::Index { .. }
            | ExprKind::ExceptAt { .. }
            | ExprKind::ExceptIndex { .. }
            | ExprKind::BitMember { .. }
            | ExprKind::BitSetOp { .. }
            | ExprKind::BitCard { .. }
            | ExprKind::Rank { .. }
            | ExprKind::SeqLen { .. }
            | ExprKind::Concat { .. }
            | ExprKind::Pack { .. }
            | ExprKind::BitSet { .. }
            | ExprKind::UnionField { .. }
            | ExprKind::UnionFieldInt { .. }
            | ExprKind::Filter { .. }
            | ExprKind::SeqFilter { .. }
            | ExprKind::MapGet { .. }
            | ExprKind::MapPut { .. }
            | ExprKind::MapBuild { .. }
            | ExprKind::MapMerge { .. }
            | ExprKind::SortedMember { .. }
            | ExprKind::Recode { .. }
            | ExprKind::RankUnion { .. }
            | ExprKind::Lookup { .. }
            | ExprKind::RankFlat { .. }
            | ExprKind::MapSet { .. }
            | ExprKind::Fold { .. }
            | ExprKind::UnionFold { .. }
            | ExprKind::Collect { .. }
            | ExprKind::SortedInsert { .. }
            | ExprKind::SeqIndex { .. }
            | ExprKind::SeqTail { .. }
            | ExprKind::SeqSub { .. }
            | ExprKind::SortedOp { .. }
            | ExprKind::SeqConcat { .. }
            | ExprKind::SeqAppend { .. } => return self.expr_encoded(e),
            ExprKind::Apply(..) | ExprKind::ValField(..) | ExprKind::Tuple(_) | ExprKind::ValOp { .. } | ExprKind::Interp { .. } => {
                return no("boxed operation")
            }
            ExprKind::RefOp { op, args } => return self.ref_op(e, op, args),
            ExprKind::RefElems(_) => return no("iteration source used as a value"),
        })
    }

    /// `pure` and small.
    fn cheap(&self, e: &Expr) -> bool {
        fn size(e: &Expr, n: &mut usize) {
            *n += 1;
            if *n <= EAGER_NODES {
                e.for_each_child(&mut |x| size(x, n));
            }
        }
        let mut n = 0;
        size(e, &mut n);
        n <= EAGER_NODES && self.pure(e)
    }

    /// Whether `e` is translated as straight-line code that cannot fail
    /// and has no effect (no check, call or region), so that evaluating it
    /// when a short-circuit would skip it is harmless.
    fn pure(&self, e: &Expr) -> bool {
        if self.mixing && self.cx.has_region_at(e) {
            return false;
        }
        let enc_words = |ty: Ty| match ty {
            Ty::Enc(sid) => Some(self.words_of(sid)),
            _ => None,
        };
        match &*e.kind {
            ExprKind::Const(_) | ExprKind::ConstWords(_) => e.ty != Ty::Val,
            ExprKind::Var(_) | ExprKind::NextVar(_) => enc_words(e.ty).is_some(),
            ExprKind::Temp(t) => e.ty != Ty::Val && self.temps.get(*t as usize).is_some_and(|t| *t != Ty::Val),
            ExprKind::Slice { base, .. } | ExprKind::Rank(base) | ExprKind::SeqLen(base) | ExprKind::RankFlat { x: base, .. } => {
                self.pure(base)
            }
            ExprKind::Convert(x) => match (x.ty, e.ty) {
                (Ty::Enc(sid), Ty::Int | Ty::Bool) => {
                    matches!((self.cx.ty.shape(sid), e.ty), (Shape::Int { .. }, Ty::Int) | (Shape::Bool, Ty::Bool)) && self.pure(x)
                }
                _ => false,
            },
            ExprKind::Not(x) => self.pure(x),
            ExprKind::And(xs) | ExprKind::Or(xs) => xs.iter().all(|x| self.pure(x)),
            ExprKind::IntCmp(_, a, b) => self.pure(a) && self.pure(b),
            ExprKind::Eq(a, b) => {
                let ok = match (a.ty, b.ty) {
                    (Ty::Int, Ty::Int) | (Ty::Bool, Ty::Bool) => true,
                    (Ty::Enc(x), Ty::Enc(y)) => x == y && self.words_of(x) <= 8,
                    _ => false,
                };
                ok && self.pure(a) && self.pure(b)
            }
            ExprKind::BitMember { set, rank } => enc_words(set.ty).is_some() && self.pure(set) && self.pure(rank),
            _ => false,
        }
    }

    /// `{bind \in s : pred}` over the sorted-array set / sequence `s` of
    /// `en`-word elements into `buf` (already zeroed).
    fn filter_sorted(&mut self, bind: Temp, s: Value, pred: &Expr, en: usize, buf: Buf) -> R<()> {
        let zero = self.iconst(0);
        let l = self.var(zero);
        let len = self.load(s, 0);
        self.for_range(zero, len, false, &mut |g, i| {
            let base = g.offset(s, 1);
            let t = g.index(base, i, en);
            let sc = g.scope();
            let p = g.with_temp(bind, t, |g| g.bool_expr(pred))?;
            g.end_scope(sc);
            let (yes, after) = (g.b.create_block(), g.b.create_block());
            g.brif(p, yes, &[], after, &[]);
            g.switch(yes);
            let lv = g.b.use_var(l);
            let bp = g.addr(buf);
            let d0 = g.offset(bp, 1);
            let dst = g.index(d0, lv, en);
            g.copy(dst, t, en);
            let l1 = g.b.ins().iadd_imm(lv, 1);
            g.b.def_var(l, l1);
            g.b.ins().jump(after, &[]);
            g.switch(after);
            Ok(())
        })?;
        let lv = self.b.use_var(l);
        let bp = self.addr(buf);
        self.store(lv, bp, 0);
        Ok(())
    }

    /// `x[0] < len ? (i64)tbl[x[0]] : -1` for the i32 table `items` at
    /// `tbl`.
    fn table_i32(&mut self, x: Value, tbl: i64, items: &[i32]) -> Value {
        let i = self.load(x, 0);
        self.table_i32_at(i, tbl, items)
    }

    fn table_i32_at(&mut self, i: Value, tbl: i64, items: &[i32]) -> Value {
        let len = items.len();
        if let Some(k) = self.konst(i) {
            return self.iconst(if (k as u64) < len as u64 { items[k as usize] as i64 } else { -1 });
        }
        if self.bound(i).is_some_and(|b| b <= len as u64) {
            let off = self.b.ins().ishl_imm(i, 2);
            let base = self.iconst(tbl);
            let p = self.b.ins().iadd(base, off);
            return self.b.ins().sload32(Self::flags(), p, 0);
        }
        let inside = self.cmp_imm(IntCC::UnsignedLessThan, i, len as i64);
        let zero = self.iconst(0);
        let idx = self.b.ins().select(inside, i, zero);
        let off = self.b.ins().ishl_imm(idx, 2);
        let base = self.iconst(tbl);
        let p = self.b.ins().iadd(base, off);
        let v = self.b.ins().sload32(Self::flags(), p, 0);
        let m1 = self.iconst(-1);
        self.b.ins().select(inside, v, m1)
    }

    fn int_bin(&mut self, op: IntOp, a: Value, b: Value) -> Value {
        match op {
            IntOp::Add | IntOp::Sub | IntOp::Mul => {
                if let (Some(x), Some(y)) = (self.konst(a), self.konst(b)) {
                    let r = match op {
                        IntOp::Add => x.checked_add(y),
                        IntOp::Sub => x.checked_sub(y),
                        _ => x.checked_mul(y),
                    };
                    if let Some(r) = r.filter(|r| *r == *r as i32 as i64) {
                        return self.iconst(r);
                    }
                }
                let r = match op {
                    IntOp::Add => self.b.ins().iadd(a, b),
                    IntOp::Sub => self.b.ins().isub(a, b),
                    _ => self.b.ins().imul(a, b),
                };
                let ok = self.fits_i32(r);
                self.check(ok);
                r
            }
            IntOp::DivFloor => {
                self.check(b);
                let q = self.b.ins().sdiv(a, b);
                let m = self.b.ins().srem(a, b);
                let inexact = self.cmp_imm(IntCC::NotEqual, m, 0);
                let x = self.b.ins().bxor(a, b);
                let neg = self.cmp_imm(IntCC::SignedLessThan, x, 0);
                let adj = self.b.ins().band(inexact, neg);
                let adj = self.b2i(adj);
                let q = self.b.ins().isub(q, adj);
                let ok = self.fits_i32(q);
                self.check(ok);
                q
            }
            IntOp::Mod => {
                let ok = self.cmp_imm(IntCC::SignedGreaterThan, b, 0);
                self.check(ok);
                let m = self.b.ins().srem(a, b);
                let neg = self.cmp_imm(IntCC::SignedLessThan, m, 0);
                let mb = self.b.ins().iadd(m, b);
                self.b.ins().select(neg, mb, m)
            }
            IntOp::DivNat | IntOp::Pow | IntOp::Gcd => {
                let f = match op {
                    IntOp::DivNat => super::rt::divn as *const u8,
                    IntOp::Pow => super::rt::pow as *const u8,
                    _ => super::rt::gcd as *const u8,
                };
                let out = self.buf(1);
                let op_ = self.addr(out);
                let ok = self.call_rt(f, &[a, b, op_]);
                self.check(ok);
                self.load(op_, 0)
            }
        }
    }

    /// Size of the element universe of the bitset shape of `ty`.
    fn universe(&self, ty: Ty) -> R<u64> {
        let Ty::Enc(sid) = ty else { return no("boxed set") };
        match self.cx.ty.shape(sid) {
            Shape::Set { elem, .. } => bitset_universe(elem).ok_or(Unsupported("not a bitset".into())),
            _ => no("not a set shape"),
        }
    }

    fn map_dims(&self, ty: Ty) -> R<MapDims> {
        let Ty::Enc(sid) = ty else { return no("boxed map") };
        crate::types::map_dims(self.cx.ty.shape(sid)).ok_or(Unsupported("not a map shape".into()))
    }

    /// Slot index of a function argument: out of domain is a runtime error
    /// if `strict`, else -1.
    pub(super) fn slot(&mut self, arg: &Expr, map: &IndexMap, strict: bool) -> R<Value> {
        let a = match map {
            IndexMap::IntRange { lo, n } => {
                let a = self.int_expr(arg)?;
                let a = self.b.ins().iadd_imm(a, lo.wrapping_neg());
                let inside = self.cmp_imm(IntCC::UnsignedLessThan, a, *n as i64);
                if strict {
                    self.check(inside);
                    return Ok(a);
                }
                let m1 = self.iconst(-1);
                self.b.ins().select(inside, a, m1)
            }
            IndexMap::Table(t) => {
                let Ty::Enc(_) = arg.ty else { return no("boxed function argument") };
                let tbl = self.cx.statics.i32s(t);
                let x = self.expr(arg)?;
                self.table_i32(x, tbl, t)
            }
        };
        if strict {
            let ok = self.cmp_imm(IntCC::SignedGreaterThanOrEqual, a, 0);
            self.check(ok);
        }
        Ok(a)
    }
}
