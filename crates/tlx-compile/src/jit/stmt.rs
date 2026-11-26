//! Statements and loops over iteration sources (port of `cgen::stmt`).

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{InstBuilder, StackSlotData, StackSlotKind, Value};
use tlx_layout::layout::bitset_universe;
use tlx_layout::Shape;

use super::gen::{Gen, HostFn, Known};
use super::{no, I32, I64, R};
use crate::inplace::Plan;
use crate::ir::*;

/// Whether an `UNCHANGED` variable copy should read its byte size from
/// `var_offsets` so widening that variable preserves identical Cranelift IR
/// for actions that only copy it unchanged.
fn is_dynamic_copy_shape(shape: &Shape, words: usize) -> bool {
    words > 16 || matches!(shape, Shape::Set { .. } | Shape::Seq { .. } | Shape::Map { .. } | Shape::Union(_) | Shape::Dyn | Shape::Ref(_))
}

/// Most copies of code specialized per union arm, nested loops included
/// (`Gen::for_bitset`, `Gen::by_arm`).
const MAX_SPEC: usize = 16;
/// Instructions after which the remaining arms of a loop are not
/// specialized.
const SPEC_INSTS: usize = 6000;

impl Gen<'_, '_, '_> {
    pub(super) fn stmt(&mut self, s: &Stmt) -> R<()> {
        match s {
            Stmt::Compose { .. } => return no("action composition uses the compiled executor"),
            Stmt::Stop => {}
            Stmt::Emit => match self.emit_target {
                Some((done, true)) => {
                    let one = self.iconst(1);
                    self.b.ins().jump(done, &[one.into()]);
                    self.dead();
                }
                Some((done, false)) => {
                    self.b.ins().jump(done, &[]);
                    self.dead();
                }
                None => self.emit(),
            },
            Stmt::Branches(bs) => {
                for b in bs {
                    self.stmt(b)?;
                }
            }
            Stmt::Guard { cond, then } => {
                let c = self.bool_expr(cond)?;
                let (yes, after) = (self.b.create_block(), self.b.create_block());
                self.brif(c, yes, &[], after, &[]);
                self.switch(yes);
                self.stmt(then)?;
                self.b.ins().jump(after, &[]);
                self.switch(after);
            }
            Stmt::If { cond, then, els } => {
                let c = self.bool_expr(cond)?;
                let (yes, no_, after) = (self.b.create_block(), self.b.create_block(), self.b.create_block());
                self.brif(c, yes, &[], no_, &[]);
                self.switch(yes);
                self.stmt(then)?;
                self.b.ins().jump(after, &[]);
                self.switch(no_);
                self.stmt(els)?;
                self.b.ins().jump(after, &[]);
                self.switch(after);
            }
            Stmt::Then { first, rest, .. } => {
                let join = self.b.create_block();
                let after = self.b.create_block();
                let saved = self.emit_target.replace((join, false));
                let res = self.stmt(first);
                self.emit_target = saved;
                res?;
                self.b.ins().jump(after, &[]);
                self.switch(join);
                self.stmt(rest)?;
                self.b.ins().jump(after, &[]);
                self.switch(after);
            }
            Stmt::Let { temp, value, body } => {
                if value.ty == Ty::Val && !self.mixing {
                    return no("boxed value");
                }
                let v = self.expr(value)?;
                self.with_temp(*temp, v, |g| g.stmt(body))?;
            }
            Stmt::ForEach { bind, set, iter, body } => {
                // A guarded body does nothing where its guard is false.
                let pred = match &**body {
                    Stmt::Guard { cond, .. } => Some((cond, false)),
                    _ => None,
                };
                let spec = self.spec_stmt(body, *bind);
                let sorted = match iter {
                    IterMode::Enumerate => Some(false),
                    IterMode::Normalized => Some(true),
                    // A quantifier's bound domain: in mixed mode `HostFn::Elems`
                    // calls `ops::enumerate`, which enforces `-maxSetSize` and
                    // falls back to the interpreter on overflow or streaming
                    // domains (`SUBSET S`).
                    IterMode::Bound => Some(false),
                };
                self.foreach(*bind, set, sorted, pred, spec, &mut |g| g.stmt(body))?;
            }
            Stmt::Assign { var, value, body } => {
                // Computed in place into the next state, nothing restored
                // (as `cgen::stmt`).
                let i = *var as usize;
                let sid = self.cx.ty.var_sid[i];
                let n = self.cx.ty.words(sid) as usize;
                let unchanged_dynamic = matches!(&*value.kind, ExprKind::Var(u) if *u == *var)
                    && value.ty == Ty::Enc(sid)
                    && is_dynamic_copy_shape(self.cx.ty.shape(sid), n)
                    && !(self.mixing && self.cx.has_region_at(value));
                if unchanged_dynamic {
                    let (s0, s1) = (self.s0, self.s1);
                    let src = self.var_ptr(s0, i);
                    let dst = self.var_ptr(s1, i);
                    let o0 = self.var_byte_off(i);
                    let o1 = self.var_byte_off(i + 1);
                    let bytes = self.b.ins().isub(o1, o0);
                    self.copy_dyn(dst, src, bytes);
                } else if value.ty == Ty::Enc(sid) {
                    let p = crate::inplace::plan(value, self.cx.ty);
                    let s1 = self.s1;
                    let dst = self.var_ptr(s1, i);
                    self.plan_into(&p, dst)?;
                } else {
                    let src = self.encoded(value, sid)?;
                    let s1 = self.s1;
                    let dst = self.var_ptr(s1, i);
                    self.copy(dst, src, n);
                }
                self.stmt(body)?;
            }
            Stmt::Error(_) => self.fail(),
            Stmt::Count(id) => {
                let Some(&c) = self.counts.get(id) else { return no("count outside its repeat") };
                let v = self.b.use_var(c);
                let v = self.b.ins().iadd_imm(v, 1);
                self.b.def_var(c, v);
            }
            Stmt::Repeat { id, bind, set, body, rest } => {
                // tot = product over the elements of the paths through body
                // (stopping at 0); then run rest tot times.
                let one = self.iconst(1);
                let tot = self.var(one);
                let done = self.b.create_block();
                let spec = self.spec_stmt(body, *bind);
                self.foreach(*bind, set, Some(false), None, spec, &mut |g| {
                    let zero = g.iconst(0);
                    let cnt = g.var(zero);
                    let saved = g.counts.insert(*id, cnt);
                    let r = g.stmt(body);
                    match saved {
                        Some(s) => g.counts.insert(*id, s),
                        None => g.counts.remove(id),
                    };
                    r?;
                    let (t, c) = (g.b.use_var(tot), g.b.use_var(cnt));
                    let nonzero = g.b.create_block();
                    let is_zero = g.b.create_block();
                    g.brif(c, nonzero, &[], is_zero, &[]);
                    g.switch(is_zero);
                    let zero = g.iconst(0);
                    g.b.def_var(tot, zero);
                    g.b.ins().jump(done, &[]);
                    g.switch(nonzero);
                    let max = g.iconst(u64::MAX as i64);
                    let lim = g.b.ins().udiv(max, c);
                    let ovf = g.cmp(IntCC::UnsignedGreaterThan, t, lim);
                    let prod = g.b.ins().imul(t, c);
                    let next = g.b.ins().select(ovf, max, prod);
                    g.b.def_var(tot, next);
                    Ok(())
                })?;
                self.b.ins().jump(done, &[]);
                self.switch(done);
                let zero = self.iconst(0);
                let rr = self.var(zero);
                let t = self.b.use_var(tot);
                let (head, blk, exit) = (self.b.create_block(), self.b.create_block(), self.b.create_block());
                self.b.ins().jump(head, &[]);
                self.switch(head);
                let iv = self.b.use_var(rr);
                let c = self.cmp(IntCC::UnsignedLessThan, iv, t);
                self.brif(c, blk, &[], exit, &[]);
                self.switch(blk);
                let sc = self.scope();
                self.stmt(rest)?;
                self.end_scope(sc);
                let next = self.b.ins().iadd_imm(iv, 1);
                self.b.def_var(rr, next);
                self.b.ins().jump(head, &[]);
                self.switch(exit);
            }
        }
        Ok(())
    }

    /// Compute the plan `p` into the words at `d` (see `inplace`; as
    /// `cgen::stmt`).
    pub(super) fn plan_into(&mut self, p: &Plan, d: Value) -> R<()> {
        match p {
            Plan::Keep => {}
            Plan::Copy(e) => {
                let Ty::Enc(sid) = e.ty else { return no("boxed update") };
                let n = self.cx.ty.words(sid) as usize;
                let v = self.expr(e)?;
                self.copy(d, v, n);
            }
            Plan::Let { temp, value, body } => {
                if value.ty == Ty::Val && !self.mixing {
                    return no("boxed value");
                }
                let v = self.expr(value)?;
                self.with_temp(*temp, v, |g| g.plan_into(body, d))?;
            }
            Plan::LetHere { temp, value, body } => {
                self.plan_into(value, d)?;
                self.with_temp(*temp, d, |g| g.plan_into(body, d))?;
            }
            Plan::At { base, update } => {
                self.plan_into(base, d)?;
                match update {
                    crate::inplace::AtUpdate::Word { offset, value } => {
                        let d1 = self.offset(d, *offset);
                        self.plan_into(value, d1)?;
                    }
                    crate::inplace::AtUpdate::Bits { pos, value: Some(ve) } => {
                        let v = self.expr(ve)?;
                        let val = self.load(v, 0);
                        self.store_bitpos(d, *pos, val);
                    }
                    crate::inplace::AtUpdate::Bits { value: None, .. } => {}
                }
            }
            Plan::AtIndex { base, arg, map, update } => {
                self.plan_into(base, d)?;
                let sl = self.slot(arg, map, false)?;
                match update {
                    crate::inplace::IndexUpdate::Words { elem_words, value } => {
                        let (yes, after) = (self.b.create_block(), self.b.create_block());
                        let c = self.cmp_imm(IntCC::SignedGreaterThanOrEqual, sl, 0);
                        self.brif(c, yes, &[], after, &[]);
                        self.switch(yes);
                        let d1 = self.index(d, sl, *elem_words);
                        self.plan_into(value, d1)?;
                        self.b.ins().jump(after, &[]);
                        self.switch(after);
                    }
                    crate::inplace::IndexUpdate::Bits { bits, value: Some(ve) } => {
                        let (yes, after) = (self.b.create_block(), self.b.create_block());
                        let c = self.cmp_imm(IntCC::SignedGreaterThanOrEqual, sl, 0);
                        self.brif(c, yes, &[], after, &[]);
                        self.switch(yes);
                        let v = self.expr(ve)?;
                        let val = self.load(v, 0);
                        self.store_slot_bits(d, *bits, sl, val);
                        self.b.ins().jump(after, &[]);
                        self.switch(after);
                    }
                    crate::inplace::IndexUpdate::Bits { value: None, .. } => {}
                }
            }
            Plan::If { cond, then, els } => {
                let c = self.bool_expr(cond)?;
                let (yes, no_, after) = (self.b.create_block(), self.b.create_block(), self.b.create_block());
                self.brif(c, yes, &[], no_, &[]);
                self.switch(yes);
                self.plan_into(then, d)?;
                self.b.ins().jump(after, &[]);
                self.switch(no_);
                self.plan_into(els, d)?;
                self.b.ins().jump(after, &[]);
                self.switch(after);
            }
            Plan::Concat(parts) => {
                for (off, part) in parts {
                    let d1 = self.offset(d, *off);
                    self.plan_into(part, d1)?;
                }
            }
            Plan::Insert { set, elem, elem_words, max_card } => {
                self.plan_into(set, d)?;
                let x = self.expr(elem)?;
                let (k, m) = (self.iconst(*elem_words as i64), self.iconst(*max_card as i64));
                let ok = self.call_rt(super::rt::sorted_add as *const u8, &[d, x, k, m]);
                self.check(ok);
            }
            Plan::Bits { op, a, b } => {
                self.plan_into(a, d)?;
                let Ty::Enc(sid) = b.ty else { return no("boxed set") };
                let n = self.cx.ty.words(sid) as usize;
                let y = self.expr(b)?;
                for i in 0..n {
                    let (u, v) = (self.load(d, i), self.load(y, i));
                    let w = match op {
                        SetOp::Union => self.b.ins().bor(u, v),
                        SetOp::Inter => self.b.ins().band(u, v),
                        SetOp::Diff => self.b.ins().band_not(u, v),
                    };
                    self.store(w, d, i);
                }
            }
        }
        Ok(())
    }

    /// Loop over the elements of an iteration source, binding `bind` and
    /// running `body`, which releases the handles it makes (mixed mode).
    /// `sorted`: a statement loop (in normalized order if true), which
    /// (mixed mode) may loop over the elements of a boxed set; None: an
    /// expression loop (over typed sources only). `body` does nothing for
    /// an element on which `pred` is `noop`, and depends on the union arm
    /// of the element if `spec` (see `for_bitset`).
    pub(super) fn foreach(
        &mut self,
        bind: Temp,
        set: &Expr,
        sorted: Option<bool>,
        pred: Option<(&Expr, bool)>,
        spec: bool,
        body: &mut dyn FnMut(&mut Self) -> R<()>,
    ) -> R<()> {
        let body = &mut |g: &mut Self| {
            let sc = g.scope();
            body(g)?;
            g.end_scope(sc);
            Ok(())
        };
        // (A stored set's elements are normalized: also the sorted order.)
        if let ExprKind::RefElems(x) = &*set.kind {
            return self.ref_elems_loop(bind, x, body);
        }
        if !set.is_typed_source() || sorted == Some(true) {
            if !self.mixing || sorted.is_none() || set.ty != Ty::Val || self.temps[bind as usize] != Ty::Val {
                return no(if sorted == Some(true) { "sorted enumeration" } else { "iteration over a boxed set" });
            }
            // The elements as consecutive handles.
            let s = self.expr(set)?;
            self.handles += 1;
            let (fb, nb) = (self.buf(1), self.buf(1));
            let (fp, np) = (self.addr(fb), self.addr(nb));
            let so = self.b.ins().iconst(I32, (sorted == Some(true)) as i64);
            let rc = self.call_host(HostFn::Elems, &[s, so, fp, np]).expect("elems returns a code");
            let ok = self.cmp_imm(IntCC::Equal, rc, 0);
            self.check(ok);
            let (first, n) = (self.load(fp, 0), self.load(np, 0));
            let zero = self.iconst(0);
            return self.for_range(zero, n, false, &mut |g, i| {
                let t = g.b.ins().iadd(first, i);
                g.with_temp(bind, t, |g| body(g))
            });
        }
        if let ExprKind::OrderedSet { set, plan } = &*set.kind {
            let Ty::Enc(sid) = set.ty else { return no("ordered boxed set") };
            let Shape::Set { elem, max_card } = self.cx.ty.shape(sid).clone() else { return no("ordered non-set") };
            if let Some(u) = bitset_universe(&elem) {
                let ib = self.buf(u as usize);
                let ip = self.addr(ib);
                let pa = self.cx.statics.words(&plan[plan[crate::encoded_order::schema::SPAN] as usize..]);
                let keys = self.iconst(pa);
                let s = self.expr(set)?;
                let nw = self.iconst(self.cx.ty.words(sid) as i64);
                let universe = self.iconst(u as i64);
                let len = self.call_rt(super::rt::order_bit_indices as *const u8, &[keys, s, nw, ip, universe]);
                let zero = self.iconst(0);
                return self.for_range(zero, len, false, &mut |g, i| {
                    let slot = g.index(ip, i, 1);
                    let rank = g.load(slot, 0);
                    let t = g.unrank(&elem, rank)?;
                    g.with_temp(bind, t, |g| body(g))
                });
            }
            let ib = self.buf(max_card.max(1));
            let ip = self.addr(ib);
            let en = plan[crate::encoded_order::schema::WIDTH] as usize;
            let pa = self.cx.statics.words(plan);
            let p = self.iconst(pa);
            let s = self.expr(set)?;
            self.call_rt(super::rt::order_indices as *const u8, &[p, s, ip]);
            let (zero, len) = (self.iconst(0), self.load(s, 0));
            return self.for_range(zero, len, false, &mut |g, i| {
                let slot = g.index(ip, i, 1);
                let rank = g.load(slot, 0);
                let base = g.offset(s, 1);
                let t = g.index(base, rank, en);
                g.with_temp(bind, t, |g| body(g))
            });
        }
        if let ExprKind::ConstElems { elem, words, count } = &*set.kind {
            let n = self.cx.ty.words(*elem) as usize;
            let arr = self.cx.statics.words(words);
            let (zero, cnt) = (self.iconst(0), self.iconst(*count as i64));
            return self.for_range(zero, cnt, false, &mut |g, i| {
                let base = g.iconst(arr);
                let t = g.index(base, i, n);
                g.with_temp(bind, t, |g| body(g))
            });
        }
        if let ExprKind::IntRange(lo, hi) = &*set.kind {
            let (lo, hi) = (self.int_expr(lo)?, self.int_expr(hi)?);
            return self.for_range(lo, hi, true, &mut |g, i| g.with_temp(bind, i, |g| body(g)));
        }
        if let ExprKind::Subsets(x) = &*set.kind {
            let Ty::Enc(sid) = x.ty else { return no("subsets of a boxed set") };
            let n = self.cx.ty.words(sid) as usize;
            let s = self.expr(x)?;
            let it = self.b.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, super::rt::SUBSETS_ITER_BYTES, 3));
            let itp = self.b.ins().stack_addr(I64, it, 0);
            let nw = self.iconst(n as i64);
            let ok = self.call_rt(super::rt::subsets_init as *const u8, &[itp, s, nw]);
            self.check(ok);
            let t = self.buf(n);
            let (head, blk, exit) = (self.b.create_block(), self.b.create_block(), self.b.create_block());
            self.b.ins().jump(head, &[]);
            self.switch(head);
            let (itp, tp) = (self.b.ins().stack_addr(I64, it, 0), self.addr(t));
            let nw = self.iconst(n as i64);
            let more = self.call_rt(super::rt::subsets_next as *const u8, &[itp, tp, nw]);
            self.brif(more, blk, &[], exit, &[]);
            self.switch(blk);
            self.with_temp(bind, tp, |g| body(g))?;
            self.b.ins().jump(head, &[]);
            self.switch(exit);
            return Ok(());
        }
        let Ty::Enc(sid) = set.ty else { return no("iteration over a boxed set") };
        let Shape::Set { elem, .. } = self.cx.ty.shape(sid).clone() else { return no("iteration over a non-set") };
        let s = self.expr(set)?;
        if bitset_universe(&elem).is_some() {
            let n = self.cx.ty.words(sid) as usize;
            let skip = pred.map(|(p, noop)| (bind, p, noop));
            self.for_bitset(&elem, s, n, skip, spec, &mut |g, _, rp| g.with_temp(bind, rp, |g| body(g)))
        } else {
            let esid = self.find_sid(&elem)?;
            let en = self.cx.ty.words(esid) as usize;
            let arms = match &*elem {
                Shape::Union(a) if spec && a.len() > 1 && self.spec * a.len() <= MAX_SPEC => a.len(),
                _ => 0,
            };
            let (zero, len) = (self.iconst(0), self.load(s, 0));
            self.for_range(zero, len, false, &mut |g, i| {
                let base = g.offset(s, 1);
                let t = g.index(base, i, en);
                if arms > 0 {
                    return g.by_arm(t, en, arms, &mut |g, t| g.with_temp(bind, t, |g| body(g)));
                }
                g.with_temp(bind, t, |g| body(g))
            })
        }
    }

    /// `body(t)` for the `en`-word element at `t` of a union of `arms`
    /// arms, specialized per arm: a branch on the tag runs a copy of
    /// `body` where the tag is a constant (as `for_bitset` does for
    /// bitsets). Arms stop being specialized past `SPEC_INSTS` instructions;
    /// the others run a generic copy.
    fn by_arm(&mut self, t: Value, en: usize, arms: usize, body: &mut dyn FnMut(&mut Self, Value) -> R<()>) -> R<()> {
        let saved = self.spec;
        self.spec *= arms;
        let start = self.b.func.dfg.num_insts();
        let tag = self.load(t, 0);
        let next = self.b.create_block();
        let mut all = true;
        let mut r = Ok(());
        for i in 0..arms {
            if self.b.func.dfg.num_insts() - start > SPEC_INSTS {
                all = false;
                break;
            }
            let (yes, no_) = (self.b.create_block(), self.b.create_block());
            let c = self.cmp_imm(IntCC::Equal, tag, i as i64);
            self.brif(c, yes, &[], no_, &[]);
            self.switch(yes);
            // A pointer of its own, whose words are known: the tag, and
            // the others loaded once (unused loads are removed).
            let ti = self.b.ins().iadd_imm(t, 0);
            let mut ws = vec![Known::Const(i as u64)];
            for k in 1..en {
                ws.push(Known::Val(self.b.ins().load(I64, Self::flags(), t, (k * 8) as i32)));
            }
            self.know(ti, ws);
            r = body(self, ti);
            if r.is_err() {
                break;
            }
            self.b.ins().jump(next, &[]);
            self.switch(no_);
        }
        self.spec = saved;
        r?;
        if all {
            // Not a tag of the union.
            self.fail();
        } else {
            body(self, t)?;
            self.b.ins().jump(next, &[]);
        }
        self.switch(next);
        Ok(())
    }

    /// Words of the element encoding produced by `unrank` for `elem`.
    pub(super) fn unrank_words(&mut self, elem: &Shape) -> R<usize> {
        if elem.is_scalar()
            || crate::lower::flat_radices(elem).is_some()
            || crate::lower::union_radices(elem).is_some()
            || crate::lower::rankable(elem)
        {
            return Ok(tlx_layout::layout::words(elem));
        }
        no("bitset of composite elements")
    }

    /// Pack flat mixed-radix `digits` into the encoded words of `shape`, also
    /// returning known bitfield entries shifted by `base_word`.
    fn pack_digits(&mut self, shape: &Shape, digits: &[Known], base_word: u32) -> (Vec<Known>, Vec<(BitPos, Known)>) {
        let parts: Option<Vec<&Shape>> = match shape {
            Shape::Tuple(es) => Some(es.iter().collect()),
            Shape::Record(fs) => Some(fs.iter().map(|(_, f)| f).collect()),
            _ => None,
        };
        if let (Some(fl), Some(ps)) = (FieldLayout::of_shape(shape), parts) {
            let mut ws = vec![Known::Const(0); fl.words];
            let mut bits = Vec::new();
            for (i, &d) in digits.iter().enumerate() {
                if tlx_layout::layout::words(ps[i]) == 0 {
                    continue;
                }
                match fl.locs[i] {
                    FieldLoc::Words(w) => ws[w] = d,
                    FieldLoc::Bits(pos) => {
                        ws[pos.word] = self.or_known_bits(ws[pos.word], pos, d);
                        bits.push((pos.offset_words(base_word as usize), d));
                    }
                }
            }
            (ws, bits)
        } else if tlx_layout::layout::words(shape) == 0 {
            (Vec::new(), Vec::new())
        } else {
            (vec![digits[0]], Vec::new())
        }
    }

    /// For each element of the `n`-word bitset at `s` of elements of shape
    /// `elem`, in rank order: `body(rank, element)`.
    ///
    /// Over a union of flat arms (messages of several types), if the code
    /// depends on the arm of the element (`spec`), the loop is specialized
    /// per arm: each arm's ranks are a range of bits, so the
    /// arm's code loops over its range and knows the tag (a constant) and
    /// that the other words are zero; tests of the tag and field offsets in
    /// the body then fold (`Gen::konst`). This duplicates the body per arm:
    /// arms stop being specialized when the specialized copies grew past
    /// `SPEC_INSTS` instructions (the remaining ranks are then one generic
    /// loop), and nested specializations at most multiply to `MAX_SPEC`.
    ///
    /// `skip`: `(bind, pred, noop)` where `body` does nothing for an
    /// element bound to `bind` on which `pred` is `noop` (the predicate of
    /// a filter, an existential quantifier...). An arm on which `pred` is
    /// the constant `noop` without any possible error is not looped over.
    /// With `noop` false, the leading tests of `pred` comparing a field of
    /// the element with a constant (`m.type = "2b"`) also select the ranks
    /// looped over (a mask of the bitset's words).
    pub(super) fn for_bitset(
        &mut self,
        elem: &Shape,
        s: Value,
        n: usize,
        skip: Option<(Temp, &Expr, bool)>,
        spec: bool,
        body: &mut dyn FnMut(&mut Self, Value, Value) -> R<()>,
    ) -> R<()> {
        // (Ranks past the universe are never set.)
        let universe = bitset_universe(elem).map_or(n as u64 * 64, |u| u.min(n as u64 * 64));
        let union = crate::lower::union_radices(elem);
        let mask = match skip {
            Some((bind, pred, false)) => crate::rankmask::rank_mask(self.cx.ty, elem, n, bind, pred),
            _ => None,
        };
        let mask = mask.as_deref();
        // No rank in [lo, hi) is selected by the mask.
        let none_in = |lo: u64, hi: u64| mask.is_some_and(|m| (lo..hi).all(|r| m[(r / 64) as usize] >> (r % 64) & 1 == 0));
        let mut lo = 0;
        if let Some(arms) = union.filter(|a| spec && a.len() > 1 && self.spec * a.len() <= MAX_SPEC) {
            let Shape::Union(arm_shapes) = elem else { unreachable!() };
            let w = self.cx.ty.words(self.find_sid(elem)?) as usize;
            let saved = self.spec;
            self.spec *= arms.len();
            let start = self.b.func.dfg.num_insts();
            let mut r = Ok(());
            for (i, radices) in arms.iter().enumerate() {
                if self.b.func.dfg.num_insts() - start > SPEC_INSTS {
                    break;
                }
                let card: u64 = radices.iter().product();
                let hi = (lo + card).min(universe);
                if none_in(lo, hi) {
                    lo = hi;
                    continue;
                }
                let arm_shape = &arm_shapes[i];
                match skip.map(|sk| self.arm_is_noop((i, arm_shape, radices, w), sk)) {
                    Some(Ok(true)) => {
                        lo = hi;
                        continue;
                    }
                    Some(Err(e)) => {
                        r = Err(e);
                        break;
                    }
                    _ => {}
                }
                r = self.for_bits_range(s, lo, hi, mask, &mut |g, q| {
                    let k = g.add_imm(q, -(lo as i64));
                    let ds: Vec<Known> = g.digits(radices, k, card).into_iter().map(Known::Val).collect();
                    let (arm_ws, arm_bits) = g.pack_digits(arm_shape, &ds, 1);
                    let mut ws = vec![Known::Const(i as u64)];
                    ws.extend(arm_ws);
                    ws.resize(w, Known::Const(0));
                    let p = g.materialize(&ws);
                    g.know_bits(p, arm_bits);
                    body(g, q, p)
                });
                lo = hi;
                if r.is_err() {
                    break;
                }
            }
            self.spec = saved;
            r?;
        }
        if lo >= universe {
            return Ok(());
        }
        self.unrank_words(elem)?;
        self.for_bits_range(s, lo, universe, mask, &mut |g, q| {
            let rp = g.unrank(elem, q)?;
            body(g, q, rp)
        })
    }

    /// Whether `pred` is the constant `noop`, without possible errors, on
    /// all elements of arm `i` (of `radices`, encoded in `w` words) bound
    /// to `bind`: it is translated (as dead code) on an element with
    /// unknown digits.
    fn arm_is_noop(
        &mut self,
        (i, arm_shape, radices, w): (usize, &Shape, &[u64], usize),
        (bind, pred, noop): (Temp, &Expr, bool),
    ) -> R<bool> {
        if self.mixing && self.regions_in(pred) {
            return Ok(false);
        }
        let mut is_noop = false;
        self.dead_code(|g| {
            let blk = g.b.current_block().expect("a block");
            let mut ds = Vec::with_capacity(radices.len());
            for c in radices {
                if *c == 1 {
                    ds.push(Known::Const(0));
                    continue;
                }
                let d = g.b.append_block_param(blk, I64);
                g.set_bound(d, *c);
                ds.push(Known::Val(d));
            }
            let (arm_ws, arm_bits) = g.pack_digits(arm_shape, &ds, 1);
            let mut ws = vec![Known::Const(i as u64)];
            ws.extend(arm_ws);
            ws.resize(w, Known::Const(0));
            let p = g.materialize(&ws);
            g.know_bits(p, arm_bits);
            let e0 = g.effects;
            let c = g.with_temp(bind, p, |g| g.bool_expr(pred))?;
            is_noop = g.effects == e0 && g.konst(c) == Some(noop as i64);
            Ok(())
        })?;
        Ok(is_noop)
    }

    /// Whether to specialize per union arm code made of `es` reading the
    /// element `bind` (`for_bitset`, `by_arm`): if it depends on the arm,
    /// and calls no host region (each region has one call site).
    pub(super) fn spec_exprs(&self, es: &[&Expr], bind: Temp) -> bool {
        es.iter().any(|e| arm_dependent(e, bind)) && !(self.mixing && es.iter().any(|e| self.regions_in(e)))
    }

    /// `spec_exprs` for the expressions of a statement tree.
    pub(super) fn spec_stmt(&self, s: &Stmt, bind: Temp) -> bool {
        let (mut dep, mut regions) = (false, false);
        s.for_each_expr_deep(&mut |e| {
            dep = dep || arm_dependent(e, bind);
            regions = regions || (self.mixing && self.regions_in(e));
        });
        dep && !regions
    }

    /// Whether `e` has a call site of a host region (mixed mode).
    pub(super) fn regions_in(&self, e: &Expr) -> bool {
        if self.cx.has_region_at(e) {
            return true;
        }
        let mut found = false;
        e.for_each_child(&mut |x| found = found || self.regions_in(x));
        found
    }

    /// The encoding of the element of rank `q` of `elem` (`CGen::unrank_code`):
    /// its words as values (`Gen::materialize`), or written into a buffer.
    /// (`q` is less than the cardinality of `elem`.)
    pub(super) fn unrank(&mut self, elem: &Shape, q: Value) -> R<Value> {
        if elem.is_scalar() {
            let c = elem.cardinality().unwrap_or(1);
            let ds: Vec<Known> = self.digits(&[c], q, c).into_iter().map(Known::Val).collect();
            let (ws, _) = self.pack_digits(elem, &ds, 0);
            return Ok(self.materialize(&ws));
        }
        if let Some(r) = crate::lower::flat_radices(elem) {
            let ds: Vec<Known> = self.digits(&r, q, r.iter().product()).into_iter().map(Known::Val).collect();
            let (ws, bits) = self.pack_digits(elem, &ds, 0);
            let p = self.materialize(&ws);
            self.know_bits(p, bits);
            return Ok(p);
        }
        if let Some(arms) = crate::lower::union_radices(elem) {
            // Tag, then the arm's digits, zero-padded (all zero if out of range).
            let Shape::Union(arm_shapes) = elem else { unreachable!() };
            let w = self.cx.ty.words(self.find_sid(elem)?) as usize;
            let done = self.b.create_block();
            let params: Vec<Value> = (0..w).map(|_| self.b.append_block_param(done, I64)).collect();
            let mut q = q;
            for (i, r) in arms.iter().enumerate() {
                let card: u64 = r.iter().product();
                let (yes, no_) = (self.b.create_block(), self.b.create_block());
                let c = self.cmp_imm(IntCC::UnsignedLessThan, q, card as i64);
                self.brif(c, yes, &[], no_, &[]);
                self.switch(yes);
                let ds: Vec<Known> = self.digits(r, q, card).into_iter().map(Known::Val).collect();
                let (arm_ws, _) = self.pack_digits(&arm_shapes[i], &ds, 1);
                let mut args = vec![self.iconst(i as i64)];
                for kw in arm_ws {
                    args.push(match kw {
                        Known::Const(c) => self.iconst(c as i64),
                        Known::Val(v) => v,
                    });
                }
                while args.len() < w {
                    args.push(self.iconst(0));
                }
                let args: Vec<_> = args.into_iter().map(|v| v.into()).collect();
                self.b.ins().jump(done, &args);
                self.switch(no_);
                q = self.b.ins().iadd_imm(q, -(card as i64));
            }
            let zero = self.iconst(0);
            let args: Vec<_> = (0..w).map(|_| zero.into()).collect();
            self.b.ins().jump(done, &args);
            self.switch(done);
            let ws: Vec<Known> = params.into_iter().map(Known::Val).collect();
            return Ok(self.materialize(&ws));
        }
        if crate::lower::rankable(elem) {
            let w = self.cx.ty.words(self.find_sid(elem)?) as usize;
            let buf = self.buf(w);
            let out = self.addr(buf);
            self.zero(out, w);
            self.unrank_nested(elem, q, out, 0)?;
            return Ok(out);
        }
        no("bitset of composite elements")
    }

    /// The digits of `q` in mixed radix `radices` (most significant first).
    /// (`q < bound`.)
    fn digits(&mut self, radices: &[u64], q: Value, bound: u64) -> Vec<Value> {
        let (mut q, mut bound) = (q, bound);
        let mut ds = vec![q; radices.len()];
        for (i, c) in radices.iter().enumerate().rev() {
            let (quot, rem) = self.udivrem(q, *c, bound);
            ds[i] = rem;
            q = quot;
            bound = bound.div_ceil(*c);
        }
        ds
    }

    fn unrank_nested(&mut self, s: &Shape, q: Value, out: Value, off: usize) -> R<()> {
        match s {
            Shape::Int { .. } | Shape::Atom(_) | Shape::Bool => {
                if tlx_layout::layout::words(s) > 0 {
                    self.store(q, out, off);
                }
            }
            // A set whose rank is its bitset (none: a set over an empty
            // universe has no words).
            Shape::Set { .. } if crate::lower::word_ranked_set(s) => {
                if self.cx.ty.words(self.find_sid(s)?) > 0 {
                    self.store(q, out, off);
                }
            }
            Shape::Tuple(_) | Shape::Record(_) => {
                let parts: Vec<Shape> = match s {
                    Shape::Tuple(es) => es.to_vec(),
                    Shape::Record(fs) => fs.iter().map(|(_, f)| f.clone()).collect(),
                    _ => unreachable!(),
                };
                let fl = FieldLayout::of_shape(s).expect("Tuple or Record");
                let mut q = q;
                for (p, loc) in parts.iter().zip(fl.locs.iter().copied()).rev() {
                    let Some(c) = p.cardinality() else { return no("unranked part without cardinality") };
                    let v = self.b.ins().urem_imm(q, c as i64);
                    q = self.b.ins().udiv_imm(q, c as i64);
                    match loc {
                        FieldLoc::Bits(pos) => self.store_bitpos(out, pos.offset_words(off), v),
                        FieldLoc::Words(w) => {
                            if tlx_layout::layout::words(p) > 0 {
                                self.unrank_nested(p, v, out, off + w)?;
                            }
                        }
                    }
                }
            }
            Shape::Union(arms) => {
                let done = self.b.create_block();
                let mut q = q;
                for (i, a) in arms.iter().enumerate() {
                    let Some(c) = a.cardinality() else { return no("unranked arm without cardinality") };
                    let (yes, no_) = (self.b.create_block(), self.b.create_block());
                    let cnd = self.cmp_imm(IntCC::UnsignedLessThan, q, c as i64);
                    self.brif(cnd, yes, &[], no_, &[]);
                    self.switch(yes);
                    let iv = self.iconst(i as i64);
                    self.store(iv, out, off);
                    self.unrank_nested(a, q, out, off + 1)?;
                    self.b.ins().jump(done, &[]);
                    self.switch(no_);
                    q = self.b.ins().iadd_imm(q, -(c as i64));
                }
                self.b.ins().jump(done, &[]);
                self.switch(done);
            }
            _ => return no("bitset of composite elements"),
        }
        Ok(())
    }

    pub(super) fn find_sid(&self, s: &Shape) -> R<ShapeId> {
        self.cx.ty.lookup(s).ok_or(super::Unsupported("unregistered shape".into()))
    }
}

/// Whether code reading the union element `bind` depends on its arm (its
/// tag or payload, a field, a rank, a recoding): what specializing a loop
/// per arm folds.
fn arm_dependent(e: &Expr, bind: Temp) -> bool {
    match &*e.kind {
        ExprKind::UnionField { base, .. }
        | ExprKind::UnionFieldInt { base, .. }
        | ExprKind::RankUnion { x: base, .. }
        | ExprKind::Recode { x: base, .. }
        | ExprKind::Slice { base, .. }
            if matches!(&*base.kind, ExprKind::Temp(t) if *t == bind) =>
        {
            true
        }
        _ => {
            let mut found = false;
            e.for_each_child(&mut |x| found = found || arm_dependent(x, bind));
            found
        }
    }
}
