//! Cranelift generation of the value family of encoded expressions: slices, indexing, EXCEPT updates, the loop builders
//! and the sequence operations (moved verbatim from `encoded.rs`).

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{InstBuilder, Value};
use tlx_layout::layout::bitset_universe;
use tlx_layout::Shape;

use super::super::gen::{Gen, Known, MAX_SSA_WORDS};
use super::super::{no, R};
use crate::ir::*;

impl Gen<'_, '_, '_> {
    /// The value family.
    pub(super) fn seq_expr(&mut self, e: &Expr) -> R<Value> {
        Ok(match &*e.kind {
            ExprKind::Slice { base, loc } => {
                let b = self.expr(base)?;
                match *loc {
                    FieldLoc::Words(offset) => self.offset(b, offset),
                    FieldLoc::Bits(pos) => {
                        let v = self.extract_bitpos(b, pos);
                        self.materialize(&[Known::Val(v)])
                    }
                }
            }
            ExprKind::Index { base, arg, map, slot } => {
                let b = self.expr(base)?;
                let sl = self.slot(arg, map, true)?;
                match *slot {
                    SlotLayout::Words(elem_words) => self.index(b, sl, elem_words),
                    SlotLayout::Bits(bits) => {
                        let v = self.load_slot_bits(b, bits, sl);
                        self.materialize(&[Known::Val(v)])
                    }
                }
            }
            ExprKind::ExceptAt { base, loc, value } => {
                let Ty::Enc(bsid) = e.ty else { return no("boxed EXCEPT") };
                let Ty::Enc(vsid) = value.ty else { return no("boxed EXCEPT value") };
                let (n, vn) = (self.words_of(bsid), self.words_of(vsid));
                let v = self.expr(value)?;
                let b = self.expr(base)?;
                match *loc {
                    FieldLoc::Words(offset) => {
                        let off = offset;
                        if n <= MAX_SSA_WORDS {
                            let mut ws = self.words(b, off);
                            ws.extend(self.words(v, vn));
                            let rest = self.offset(b, off + vn);
                            ws.extend(self.words(rest, n - off - vn));
                            return Ok(self.materialize(&ws));
                        }
                        let buf = self.buf(n);
                        let bp = self.addr(buf);
                        self.copy(bp, b, n);
                        let dst = self.offset(bp, off);
                        self.copy(dst, v, vn);
                        bp
                    }
                    FieldLoc::Bits(pos) => {
                        let val = self.load(v, 0);
                        if n <= MAX_SSA_WORDS {
                            let mut ws = self.words(b, n);
                            let (nw, mv) = self.insert_known_bits(ws[pos.word], pos, val);
                            ws[pos.word] = nw;
                            let p = self.materialize(&ws);
                            let mut bits: Vec<(BitPos, Known)> = self
                                .known_bits_of(b)
                                .into_iter()
                                .filter(|(bp, _)| bp.word != pos.word || (bp.shifted_mask() & pos.shifted_mask()) == 0)
                                .collect();
                            bits.push((pos, mv));
                            self.know_bits(p, bits);
                            return Ok(p);
                        }
                        let buf = self.buf(n);
                        let bp = self.addr(buf);
                        self.copy(bp, b, n);
                        self.store_bitpos(bp, pos, val);
                        bp
                    }
                }
            }
            ExprKind::ExceptIndex { base, arg, map, slot, value } => {
                let (n, buf) = self.result_buf(e.ty, "boxed EXCEPT")?;
                let b = self.expr(base)?;
                let sl = self.slot(arg, map, false)?;
                let bp = self.addr(buf);
                self.copy(bp, b, n);
                let (yes, after) = (self.b.create_block(), self.b.create_block());
                let c = self.cmp_imm(IntCC::SignedGreaterThanOrEqual, sl, 0);
                self.brif(c, yes, &[], after, &[]);
                self.switch(yes);
                let v = self.expr(value)?;
                match *slot {
                    SlotLayout::Words(elem_words) => {
                        let ew = elem_words;
                        let dst = self.index(bp, sl, ew);
                        self.copy(dst, v, ew);
                    }
                    SlotLayout::Bits(bits) => {
                        let val = self.load(v, 0);
                        self.store_slot_bits(bp, bits, sl, val);
                    }
                }
                self.b.ins().jump(after, &[]);
                self.switch(after);
                bp
            }
            ExprKind::SeqLen(x) => {
                // A sequence shape always has at least the length word, so
                // `Rank`'s zero-word special case cannot apply.
                let s = self.expr(x)?;
                self.load(s, 0)
            }
            ExprKind::Filter { bind, set, pred } => {
                let Ty::Enc(sid) = e.ty else { return no("boxed filter") };
                let Shape::Set { elem, .. } = self.cx.ty.shape(sid).clone() else { return no("filter over a non-set") };
                let n = self.words_of(sid);
                let buf = self.buf(n);
                let s = self.expr(set)?;
                let bp = self.addr(buf);
                self.zero(bp, n);
                if bitset_universe(&elem).is_some() {
                    self.for_bitset(&elem, s, n, Some((*bind, pred, false)), self.spec_exprs(&[pred], *bind), &mut |g, q, rp| {
                        let sc = g.scope();
                        let p = g.with_temp(*bind, rp, |g| g.bool_expr(pred))?;
                        g.end_scope(sc);
                        let (yes, after) = (g.b.create_block(), g.b.create_block());
                        g.brif(p, yes, &[], after, &[]);
                        g.switch(yes);
                        let bp = g.addr(buf);
                        g.set_bit(bp, q);
                        g.b.ins().jump(after, &[]);
                        g.switch(after);
                        Ok(())
                    })?;
                } else {
                    let en = self.words_of(self.find_sid(&elem)?);
                    self.filter_sorted(*bind, s, pred, en, buf)?;
                }
                self.addr(buf)
            }
            ExprKind::SeqFilter { bind, seq, pred, slot } => {
                let (n, buf) = self.result_buf(e.ty, "boxed sequence")?;
                let s = self.expr(seq)?;
                let bp = self.addr(buf);
                self.zero(bp, n);
                match *slot {
                    SlotLayout::Words(elem_words) => self.filter_sorted(*bind, s, pred, elem_words, buf)?,
                    SlotLayout::Bits(bits) => {
                        let zero = self.iconst(0);
                        let l = self.var(zero);
                        let len = self.load(s, 0);
                        self.for_range(zero, len, false, &mut |g, i| {
                            let base = g.offset(s, 1);
                            let val = g.load_slot_bits(base, bits, i);
                            let t = g.materialize(&[Known::Val(val)]);
                            let sc = g.scope();
                            let p = g.with_temp(*bind, t, |g| g.bool_expr(pred))?;
                            g.end_scope(sc);
                            let (yes, after) = (g.b.create_block(), g.b.create_block());
                            g.brif(p, yes, &[], after, &[]);
                            g.switch(yes);
                            let lv = g.b.use_var(l);
                            let bp = g.addr(buf);
                            let d0 = g.offset(bp, 1);
                            g.store_slot_bits(d0, bits, lv, val);
                            let l1 = g.b.ins().iadd_imm(lv, 1);
                            g.b.def_var(l, l1);
                            g.b.ins().jump(after, &[]);
                            g.switch(after);
                            Ok(())
                        })?;
                        let lv = self.b.use_var(l);
                        let bp = self.addr(buf);
                        self.store(lv, bp, 0);
                    }
                }
                self.addr(buf)
            }
            ExprKind::MapSet { bind, set, elem, cond } => {
                let Ty::Enc(sid) = e.ty else { return no("boxed set") };
                let Shape::Set { elem: es, max_card } = self.cx.ty.shape(sid).clone() else { return no("map into a non-set") };
                let n = self.words_of(sid);
                let buf = self.buf(n);
                let bp = self.addr(buf);
                self.zero(bp, n);
                let universe = bitset_universe(&es);
                let ew = if universe.is_none() { self.words_of(self.find_sid(&es)?) } else { 0 };
                let spec = self.spec_exprs(&[Some(elem), cond.as_ref()].into_iter().flatten().collect::<Vec<_>>(), *bind);
                self.foreach(*bind, set, None, cond.as_ref().map(|c| (c, false)), spec, &mut |g| {
                    let after = g.b.create_block();
                    if let Some(c) = cond {
                        let c = g.bool_expr(c)?;
                        let yes = g.b.create_block();
                        g.brif(c, yes, &[], after, &[]);
                        g.switch(yes);
                    }
                    if let Some(u) = universe {
                        let r = g.int_expr(elem)?;
                        let ok = g.cmp_imm(IntCC::UnsignedLessThan, r, u as i64);
                        g.check(ok);
                        let bp = g.addr(buf);
                        g.set_bit(bp, r);
                    } else {
                        let x = g.expr(elem)?;
                        let bp = g.addr(buf);
                        let (k, m) = (g.iconst(ew as i64), g.iconst(max_card as i64));
                        let ok = g.call_rt(super::super::rt::sorted_add as *const u8, &[bp, x, k, m]);
                        g.check(ok);
                    }
                    g.b.ins().jump(after, &[]);
                    g.switch(after);
                    Ok(())
                })?;
                self.addr(buf)
            }
            ExprKind::Fold { product, bind, set, body } => {
                let init = self.iconst(*product as i64);
                let acc = self.var(init);
                let done = self.b.create_block();
                self.foreach(*bind, set, None, None, self.spec_exprs(&[body], *bind), &mut |g| {
                    if *product {
                        let a = g.b.use_var(acc);
                        let cont = g.b.create_block();
                        g.brif(a, cont, &[], done, &[]);
                        g.switch(cont);
                    }
                    let v = g.int_expr(body)?;
                    let a = g.b.use_var(acc);
                    let r = if *product { g.b.ins().imul(a, v) } else { g.b.ins().iadd(a, v) };
                    let ok = g.fits_i32(r);
                    g.check(ok);
                    g.b.def_var(acc, r);
                    Ok(())
                })?;
                self.b.ins().jump(done, &[]);
                self.switch(done);
                self.b.use_var(acc)
            }
            ExprKind::UnionFold { bind, set, body } => {
                let Ty::Enc(sid) = e.ty else { return no("boxed union") };
                let n = self.words_of(sid);
                let buf = self.buf(n);
                let bp = self.addr(buf);
                self.zero(bp, n);
                self.foreach(*bind, set, None, None, self.spec_exprs(&[body], *bind), &mut |g| {
                    let x = g.expr(body)?;
                    let bp = g.addr(buf);
                    let ws: Vec<Value> = (0..n).map(|i| g.load(bp, i)).collect();
                    for (i, w) in ws.into_iter().enumerate() {
                        let v = g.load(x, i);
                        let o = g.b.ins().bor(w, v);
                        g.store(o, bp, i);
                    }
                    Ok(())
                })?;
                self.addr(buf)
            }
            ExprKind::Collect { bind, set, elem } => {
                let Ty::Enc(sid) = e.ty else { return no("boxed sequence") };
                let Shape::Seq { elem: es, max_len } = self.cx.ty.shape(sid).clone() else { return no("collect into a non-sequence") };
                let slot = SlotLayout::of(&es);
                let n = self.words_of(sid);
                let buf = self.buf(n);
                let bp = self.addr(buf);
                self.zero(bp, n);
                self.foreach(*bind, set, None, None, self.spec_exprs(&[elem], *bind), &mut |g| {
                    let x = g.expr(elem)?;
                    let bp = g.addr(buf);
                    let len = g.load(bp, 0);
                    let ok = g.cmp_imm(IntCC::UnsignedLessThan, len, max_len as i64);
                    g.check(ok);
                    let p = g.offset(bp, 1);
                    match slot {
                        SlotLayout::Words(ew) => {
                            let dst = g.index(p, len, ew);
                            g.copy(dst, x, ew);
                        }
                        SlotLayout::Bits(bits) => {
                            let val = g.load(x, 0);
                            g.store_slot_bits(p, bits, len, val);
                        }
                    }
                    let l1 = g.b.ins().iadd_imm(len, 1);
                    g.store(l1, bp, 0);
                    Ok(())
                })?;
                self.addr(buf)
            }
            ExprKind::SeqIndex { base, arg, slot } => {
                let s = self.expr(base)?;
                let i = self.int_expr(arg)?;
                let len = self.load(s, 0);
                let i1 = self.b.ins().iadd_imm(i, -1);
                // 1 <= i <= len  <=>  (i - 1) < len unsigned (i >= 1 as signed first)
                let pos = self.cmp_imm(IntCC::SignedGreaterThanOrEqual, i, 1);
                let le = self.cmp(IntCC::UnsignedLessThan, i1, len);
                let ok = self.b.ins().band(pos, le);
                self.check(ok);
                let p = self.offset(s, 1);
                match *slot {
                    SlotLayout::Words(elem_words) => self.index(p, i1, elem_words),
                    SlotLayout::Bits(bits) => {
                        let v = self.load_slot_bits(p, bits, i1);
                        self.materialize(&[Known::Val(v)])
                    }
                }
            }
            ExprKind::SeqTail { base, slot } => {
                let (n, buf) = self.result_buf(e.ty, "boxed sequence")?;
                let s = self.expr(base)?;
                let len = self.load(s, 0);
                self.check(len);
                let l1 = self.b.ins().iadd_imm(len, -1);
                match *slot {
                    SlotLayout::Words(elem_words) => {
                        let ew = elem_words;
                        let bp = self.addr(buf);
                        self.copy(bp, s, n);
                        let dst = self.offset(bp, 1);
                        let src = self.offset(bp, 1 + ew);
                        let bytes = self.b.ins().imul_imm(l1, (ew * 8) as i64);
                        self.copy_dyn(dst, src, bytes);
                        let last = self.index(dst, l1, ew);
                        self.zero(last, ew);
                        self.store(l1, bp, 0);
                        bp
                    }
                    SlotLayout::Bits(bits) => {
                        let bp = self.addr(buf);
                        self.zero(bp, n);
                        let zero = self.iconst(0);
                        self.for_range(zero, l1, false, &mut |g, j| {
                            let sp = g.offset(s, 1);
                            let j1 = g.b.ins().iadd_imm(j, 1);
                            let v = g.load_slot_bits(sp, bits, j1);
                            let bp = g.addr(buf);
                            let dp = g.offset(bp, 1);
                            g.store_slot_bits(dp, bits, j, v);
                            Ok(())
                        })?;
                        let bp = self.addr(buf);
                        self.store(l1, bp, 0);
                        bp
                    }
                }
            }
            ExprKind::SeqSub { base, lo, hi, slot } => {
                let (n, buf) = self.result_buf(e.ty, "boxed sequence")?;
                let s = self.expr(base)?;
                let (m, k) = (self.int_expr(lo)?, self.int_expr(hi)?);
                let bp = self.addr(buf);
                self.zero(bp, n);
                let (yes, after) = (self.b.create_block(), self.b.create_block());
                let c = self.cmp(IntCC::SignedGreaterThanOrEqual, k, m);
                self.brif(c, yes, &[], after, &[]);
                self.switch(yes);
                let len = self.load(s, 0);
                let a = self.cmp_imm(IntCC::SignedGreaterThanOrEqual, m, 1);
                let b = self.cmp(IntCC::SignedLessThanOrEqual, k, len);
                let ok = self.b.ins().band(a, b);
                self.check(ok);
                let cnt = self.b.ins().isub(k, m);
                let cnt = self.b.ins().iadd_imm(cnt, 1);
                let m1 = self.b.ins().iadd_imm(m, -1);
                match *slot {
                    SlotLayout::Words(elem_words) => {
                        let ew = elem_words;
                        let sp = self.offset(s, 1);
                        let src = self.index(sp, m1, ew);
                        let bp = self.addr(buf);
                        let dst = self.offset(bp, 1);
                        let bytes = self.b.ins().imul_imm(cnt, (ew * 8) as i64);
                        self.copy_dyn(dst, src, bytes);
                    }
                    SlotLayout::Bits(bits) => {
                        let zero = self.iconst(0);
                        self.for_range(zero, cnt, false, &mut |g, j| {
                            let sp = g.offset(s, 1);
                            let si = g.b.ins().iadd(m1, j);
                            let v = g.load_slot_bits(sp, bits, si);
                            let bp = g.addr(buf);
                            let dp = g.offset(bp, 1);
                            g.store_slot_bits(dp, bits, j, v);
                            Ok(())
                        })?;
                    }
                }
                let bp = self.addr(buf);
                self.store(cnt, bp, 0);
                self.b.ins().jump(after, &[]);
                self.switch(after);
                self.addr(buf)
            }
            ExprKind::SeqConcat { a, b, slot, max_len } => {
                let (n, buf) = self.result_buf(e.ty, "boxed sequence")?;
                let (a, b) = (self.expr(a)?, self.expr(b)?);
                let (la, lb) = (self.load(a, 0), self.load(b, 0));
                let l = self.b.ins().iadd(la, lb);
                let ok = self.cmp_imm(IntCC::UnsignedLessThanOrEqual, l, *max_len as i64);
                self.check(ok);
                let bp = self.addr(buf);
                self.copy(bp, a, n);
                match *slot {
                    SlotLayout::Words(elem_words) => {
                        let ew = elem_words;
                        let d0 = self.offset(bp, 1);
                        let dst = self.index(d0, la, ew);
                        let src = self.offset(b, 1);
                        let bytes = self.b.ins().imul_imm(lb, (ew * 8) as i64);
                        self.copy_dyn(dst, src, bytes);
                    }
                    SlotLayout::Bits(bits) => {
                        let zero = self.iconst(0);
                        self.for_range(zero, lb, false, &mut |g, j| {
                            let sp = g.offset(b, 1);
                            let v = g.load_slot_bits(sp, bits, j);
                            let bp = g.addr(buf);
                            let dp = g.offset(bp, 1);
                            let di = g.b.ins().iadd(la, j);
                            g.store_slot_bits(dp, bits, di, v);
                            Ok(())
                        })?;
                    }
                }
                let bp = self.addr(buf);
                self.store(l, bp, 0);
                bp
            }
            ExprKind::SeqAppend { base, value, slot, max_len } => {
                let (n, buf) = self.result_buf(e.ty, "boxed sequence")?;
                let s = self.expr(base)?;
                let v = self.expr(value)?;
                let len = self.load(s, 0);
                let ok = self.cmp_imm(IntCC::UnsignedLessThan, len, *max_len as i64);
                self.check(ok);
                let bp = self.addr(buf);
                self.copy(bp, s, n);
                let d0 = self.offset(bp, 1);
                match *slot {
                    SlotLayout::Words(elem_words) => {
                        let ew = elem_words;
                        let dst = self.index(d0, len, ew);
                        self.copy(dst, v, ew);
                    }
                    SlotLayout::Bits(bits) => {
                        let val = self.load(v, 0);
                        self.store_slot_bits(d0, bits, len, val);
                    }
                }
                let l1 = self.b.ins().iadd_imm(len, 1);
                self.store(l1, bp, 0);
                bp
            }
            _ => unreachable!("not an encoded-value expression"),
        })
    }
}
