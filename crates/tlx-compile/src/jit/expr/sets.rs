//! Cranelift generation of the set family of encoded expressions: bit sets, sorted sets, the
//! ranks, the recodes, union field access and the boxed builders (moved verbatim from
//! `encoded.rs`).

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{InstBuilder, Value};
use tlx_layout::Shape;

use super::super::gen::{Gen, Known, MAX_SSA_WORDS};
use super::super::{no, R};
use crate::ir::encoding::{
    union_loc_desc, RecodeTable, UnionArms, UNION_DESC_BIT_SHIFT, UNION_DESC_FIELD_MASK, UNION_DESC_MISSING, UNION_DESC_WORD_SHIFT,
};
use crate::ir::*;

impl Gen<'_, '_, '_> {
    /// The set family.
    pub(super) fn set_expr(&mut self, e: &Expr) -> R<Value> {
        Ok(match &*e.kind {
            ExprKind::BitMember { set, rank } => {
                let Ty::Enc(sid) = set.ty else { return no("boxed membership") };
                let n = self.words_of(sid);
                let (s, r) = (self.expr(set)?, self.int_expr(rank)?);
                self.bit(s, n, r)
            }
            ExprKind::BitSetOp(op, a, b) => {
                let (n, buf) = self.result_buf(e.ty, "boxed set")?;
                let (x, y) = (self.expr(a)?, self.expr(b)?);
                let mut ws = Vec::with_capacity(n);
                for i in 0..n {
                    let (u, v) = (self.load(x, i), self.load(y, i));
                    ws.push(match op {
                        SetOp::Union => self.b.ins().bor(u, v),
                        SetOp::Inter => self.b.ins().band(u, v),
                        SetOp::Diff => self.b.ins().band_not(u, v),
                    });
                }
                if n <= MAX_SSA_WORDS {
                    let ws: Vec<Known> = ws.into_iter().map(Known::Val).collect();
                    return Ok(self.materialize(&ws));
                }
                let bp = self.addr(buf);
                for (i, w) in ws.into_iter().enumerate() {
                    self.store(w, bp, i);
                }
                bp
            }
            ExprKind::BitCard(s) => {
                let Ty::Enc(sid) = s.ty else { return no("boxed cardinality") };
                let n = self.words_of(sid);
                let p = self.expr(s)?;
                let mut acc = self.iconst(0);
                for i in 0..n {
                    let w = self.load(p, i);
                    let c = self.b.ins().popcnt(w);
                    acc = self.b.ins().iadd(acc, c);
                }
                acc
            }
            ExprKind::Rank(x) => {
                let p = self.expr(x)?;
                if matches!(x.ty, Ty::Enc(sid) if self.words_of(sid) == 0) {
                    // A zero-word encoding (a set over an empty universe)
                    // has a single value: rank 0.
                    self.iconst(0)
                } else {
                    self.load(p, 0)
                }
            }
            ExprKind::Concat(xs) => {
                let (total, buf) = self.result_buf(e.ty, "boxed construction")?;
                let mut parts = Vec::new();
                for x in xs {
                    let Ty::Enc(xs_) = x.ty else { return no("boxed part") };
                    let n = self.words_of(xs_);
                    parts.push((self.expr(x)?, n));
                }
                if total <= MAX_SSA_WORDS {
                    let mut ws = Vec::with_capacity(total);
                    for (v, n) in parts {
                        ws.extend(self.words(v, n));
                    }
                    return Ok(self.materialize(&ws));
                }
                let bp = self.addr(buf);
                let mut off = 0;
                for (v, n) in parts {
                    let dst = self.offset(bp, off);
                    self.copy(dst, v, n);
                    off += n;
                }
                bp
            }
            ExprKind::Pack { locs, parts } => {
                let (total, buf) = self.result_buf(e.ty, "boxed construction")?;
                let mut evals = Vec::with_capacity(parts.len());
                for x in parts {
                    let Ty::Enc(xs_) = x.ty else { return no("boxed part") };
                    let n = self.words_of(xs_);
                    evals.push((self.expr(x)?, n));
                }
                if total <= MAX_SSA_WORDS {
                    let mut ws = vec![Known::Const(0); total];
                    let mut kbits = Vec::new();
                    for (loc, (v, n)) in locs.iter().zip(evals) {
                        match *loc {
                            FieldLoc::Words(off) => {
                                for (k, kw) in self.words(v, n).into_iter().enumerate() {
                                    ws[off + k] = kw;
                                }
                            }
                            FieldLoc::Bits(pos) => {
                                let val = self.load(v, 0);
                                let mv = self.mask_bits(val, pos.bits);
                                ws[pos.word] = self.or_known_bits(ws[pos.word], pos, mv);
                                kbits.push((pos, mv));
                            }
                        }
                    }
                    let p = self.materialize(&ws);
                    self.know_bits(p, kbits);
                    return Ok(p);
                }
                let bp = self.addr(buf);
                self.zero(bp, total);
                for (loc, (v, n)) in locs.iter().zip(evals) {
                    match *loc {
                        FieldLoc::Words(off) => {
                            if n > 0 {
                                let dst = self.offset(bp, off);
                                self.copy(dst, v, n);
                            }
                        }
                        FieldLoc::Bits(pos) => {
                            let val = self.load(v, 0);
                            self.store_bitpos(bp, pos, val);
                        }
                    }
                }
                bp
            }
            ExprKind::BitSet(rs) => {
                let (n, buf) = self.result_buf(e.ty, "boxed set")?;
                let u = self.universe(e.ty)?;
                let bp = self.addr(buf);
                self.zero(bp, n);
                for r in rs {
                    let r = self.int_expr(r)?;
                    let ok = self.cmp_imm(IntCC::UnsignedLessThan, r, u as i64);
                    self.check(ok);
                    let bp = self.addr(buf);
                    self.set_bit(bp, r);
                }
                self.addr(buf)
            }
            ExprKind::UnionField { base, locs } => {
                let u = self.expr(base)?;
                let tag = self.load(u, 0);
                if let Some(t) = self.konst(tag) {
                    return Ok(match locs.get(t as usize).copied().flatten() {
                        Some(FieldLoc::Words(off)) => self.offset(u, 1 + off),
                        Some(FieldLoc::Bits(pos)) => {
                            let v = self.extract_bitpos(u, pos.offset_words(1));
                            self.materialize(&[Known::Val(v)])
                        }
                        None => {
                            self.fail();
                            self.iconst(0)
                        }
                    });
                }
                if locs.iter().all(|o| !matches!(o, Some(FieldLoc::Bits(_)))) {
                    let items: Vec<i32> = locs
                        .iter()
                        .map(|o| match o {
                            Some(FieldLoc::Words(x)) => {
                                i32::try_from(*x).map_err(|_| super::super::Unsupported("union field offset exceeds i32".into()))
                            }
                            _ => Ok(-1),
                        })
                        .collect::<R<_>>()?;
                    let tbl = self.cx.statics.i32s(&items);
                    let o = self.table_i32(u, tbl, &items);
                    let ok = self.cmp_imm(IntCC::SignedGreaterThanOrEqual, o, 0);
                    self.check(ok);
                    let p = self.offset(u, 1);
                    self.index(p, o, 1)
                } else {
                    let descs: Vec<i64> = locs
                        .iter()
                        .map(|o| union_loc_desc(*o).ok_or_else(|| super::super::Unsupported("union field descriptor overflow".into())))
                        .collect::<R<_>>()?;
                    let v = self.union_scalar_field(u, tag, &descs);
                    self.materialize(&[Known::Val(v)])
                }
            }
            ExprKind::UnionFieldInt { base, entries } => {
                let u = self.expr(base)?;
                let tag = self.load(u, 0);
                if let Some(t) = self.konst(tag) {
                    return Ok(match entries.get(t as usize).copied().flatten() {
                        Some((FieldLoc::Words(off), lo)) => {
                            let w = self.load(u, 1 + off);
                            self.add_imm(w, lo)
                        }
                        Some((FieldLoc::Bits(pos), lo)) => {
                            let w = self.extract_bitpos(u, pos.offset_words(1));
                            self.add_imm(w, lo)
                        }
                        None => {
                            self.fail();
                            self.iconst(0)
                        }
                    });
                }
                let descs: Vec<i64> = entries
                    .iter()
                    .map(|o| {
                        union_loc_desc(o.map(|x| x.0)).ok_or_else(|| super::super::Unsupported("union field descriptor overflow".into()))
                    })
                    .collect::<R<_>>()?;
                let los: Vec<i64> = entries.iter().map(|o| o.map_or(0, |x| x.1)).collect();
                let tl = self.cx.statics.i64s(&los);
                let w = self.union_scalar_field(u, tag, &descs);
                let tlv = self.iconst(tl);
                let lp = self.index(tlv, tag, 1);
                let lo = self.load(lp, 0);
                self.b.ins().iadd(w, lo)
            }
            ExprKind::SortedMember { set, elem, elem_words } => {
                let (s, x) = (self.expr(set)?, self.expr(elem)?);
                let n = self.iconst(*elem_words as i64);
                self.call_rt(super::super::rt::sorted_member as *const u8, &[s, x, n])
            }
            ExprKind::Recode { x, arm_base, table, words } => {
                let v = self.expr(x)?;
                let tbl = self.cx.statics.words(table);
                let words = *words as usize;
                let codes = RecodeTable { arm_base, table, words }.codes() as i64;
                let code = if arm_base.is_empty() {
                    self.load(v, 0)
                } else {
                    let base = self.cx.statics.words(arm_base);
                    let tag = self.load(v, 0);
                    let inside = self.cmp_imm(IntCC::UnsignedLessThan, tag, arm_base.len() as i64);
                    let (yes, no_) = (self.b.create_block(), self.b.create_block());
                    let (j, r) = self.join();
                    self.brif(inside, yes, &[], no_, &[]);
                    self.switch(yes);
                    let bv = self.iconst(base);
                    let bp = self.index(bv, tag, 1);
                    let b0 = self.load(bp, 0);
                    let x1 = self.load(v, 1);
                    let c = self.b.ins().iadd(b0, x1);
                    self.b.ins().jump(j, &[c.into()]);
                    self.switch(no_);
                    let m = self.iconst(-1);
                    self.b.ins().jump(j, &[m.into()]);
                    self.switch(j);
                    r
                };
                let ok = self.cmp_imm(IntCC::UnsignedLessThan, code, codes);
                self.check(ok);
                let p = match self.konst(code).filter(|c| (0..codes).contains(c)) {
                    Some(c) => {
                        // A known entry of the table: its words are known.
                        let at = c as usize * words;
                        let p = self.iconst(tbl + (at * 8) as i64);
                        self.know(p, table[at..at + words].iter().map(|w| Known::Const(*w)).collect());
                        p
                    }
                    None => {
                        let tv = self.iconst(tbl);
                        self.index(tv, code, words)
                    }
                };
                let w0 = self.load(p, 0);
                let ok = self.cmp_imm(IntCC::NotEqual, w0, -1);
                self.check(ok);
                p
            }
            ExprKind::RankUnion { x, arms } => {
                let Ty::Enc(xsid) = x.ty else { return no("boxed union") };
                let Shape::Union(arm_shapes) = self.cx.ty.shape(xsid).clone() else { return no("RankUnion of non-union") };
                let v = self.expr(x)?;
                let tag = self.load(v, 0);
                let (j, r) = self.join();
                for (i, (base, radices)) in UnionArms::new(arms).enumerate() {
                    let locs: Box<[FieldLoc]> =
                        FieldLayout::of_shape(&arm_shapes[i]).map_or_else(|| Box::from([FieldLoc::Words(0)]), |fl| fl.locs);
                    let (yes, next) = (self.b.create_block(), self.b.create_block());
                    let c = self.cmp_imm(IntCC::Equal, tag, i as i64);
                    self.brif(c, yes, &[], next, &[]);
                    self.switch(yes);
                    // The arm offset plus the mixed-radix rank within the arm.
                    let mut acc = self.iconst(0);
                    for (k, c) in radices.iter().enumerate() {
                        let d = match locs[k] {
                            FieldLoc::Words(w) => self.load(v, 1 + w),
                            FieldLoc::Bits(pos) => self.extract_bitpos(v, pos.offset_words(1)),
                        };
                        let m = self.b.ins().imul_imm(acc, *c as i64);
                        acc = self.b.ins().iadd(m, d);
                    }
                    let res = self.b.ins().iadd_imm(acc, base as i64);
                    self.b.ins().jump(j, &[res.into()]);
                    self.switch(next);
                }
                self.fail();
                self.switch(j);
                r
            }
            ExprKind::Lookup { x, table } => {
                let tbl = self.cx.statics.i32s(table);
                let v = self.expr(x)?;
                self.table_i32(v, tbl, table)
            }
            ExprKind::RankFlat { x, radices } => {
                let Ty::Enc(xsid) = x.ty else { return no("boxed product") };
                let fl = FieldLayout::of_shape(self.cx.ty.shape(xsid))
                    .ok_or_else(|| super::super::Unsupported("RankFlat of non-product".into()))?;
                let v = self.expr(x)?;
                let mut acc = self.iconst(0);
                for (i, c) in radices.iter().enumerate() {
                    let d = match fl.locs[i] {
                        FieldLoc::Words(w) => self.load(v, w),
                        FieldLoc::Bits(pos) => self.extract_bitpos(v, pos),
                    };
                    let m = self.b.ins().imul_imm(acc, *c as i64);
                    acc = self.b.ins().iadd(m, d);
                }
                acc
            }
            ExprKind::SortedInsert { set, elem, elem_words, max_card } => {
                let (n, buf) = self.result_buf(e.ty, "boxed set")?;
                let (s, x) = (self.expr(set)?, self.expr(elem)?);
                let bp = self.addr(buf);
                let (nw, k, m) = (self.iconst(n as i64), self.iconst(*elem_words as i64), self.iconst(*max_card as i64));
                let ok = self.call_rt(super::super::rt::sorted_insert as *const u8, &[bp, nw, s, x, k, m]);
                self.check(ok);
                bp
            }
            ExprKind::SortedOp { op, a, b, elem_words, max_card } => {
                let opn = match op {
                    SetOp::Union => 0,
                    SetOp::Inter => 1,
                    SetOp::Diff => 2,
                };
                let (n, buf) = self.result_buf(e.ty, "boxed set")?;
                let (a, b) = (self.expr(a)?, self.expr(b)?);
                let bp = self.addr(buf);
                let (o, nw, k, m) =
                    (self.iconst(opn), self.iconst(n as i64), self.iconst(*elem_words as i64), self.iconst(*max_card as i64));
                let ok = self.call_rt(super::super::rt::sorted_op as *const u8, &[o, bp, nw, a, b, k, m]);
                self.check(ok);
                bp
            }
            _ => unreachable!("not an encoded-value expression"),
        })
    }

    /// Look up `descs[tag]` (`union_loc_desc`, `< 0` on missing arm -> error)
    /// and extract the scalar value from union `u` (at runtime `tag`).
    fn union_scalar_field(&mut self, u: Value, tag: Value, descs: &[i64]) -> Value {
        let len = descs.len();
        let tbl = self.cx.statics.i64s(descs);
        let d = if self.bound(tag).is_some_and(|b| b <= len as u64) {
            let tv = self.iconst(tbl);
            let tp = self.index(tv, tag, 1);
            self.load(tp, 0)
        } else {
            let inside = self.cmp_imm(IntCC::UnsignedLessThan, tag, len as i64);
            let zero = self.iconst(0);
            let idx = self.b.ins().select(inside, tag, zero);
            let tv = self.iconst(tbl);
            let tp = self.index(tv, idx, 1);
            let v = self.load(tp, 0);
            let m1 = self.iconst(UNION_DESC_MISSING);
            self.b.ins().select(inside, v, m1)
        };
        let ok = self.cmp_imm(IntCC::SignedGreaterThanOrEqual, d, 0);
        self.check(ok);
        let widx = self.b.ins().ushr_imm(d, UNION_DESC_WORD_SHIFT as i64);
        let wp = self.index(u, widx, 1);
        let word = self.load(wp, 0);
        let sh = self.b.ins().ushr_imm(d, UNION_DESC_BIT_SHIFT as i64);
        let sh = self.b.ins().band_imm(sh, UNION_DESC_FIELD_MASK);
        let rtrim = self.b.ins().band_imm(d, UNION_DESC_FIELD_MASK);
        let ones = self.iconst(-1);
        let mask = self.b.ins().ushr(ones, rtrim);
        let shifted = self.b.ins().ushr(word, sh);
        self.b.ins().band(shifted, mask)
    }
}
