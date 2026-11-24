//! Cranelift generation of the map family of encoded expressions:
//! `MapGet`, `MapPut`, `MapBuild` and `MapMerge` (moved verbatim from
//! `encoded.rs`).

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{InstBuilder, Value};
use tlx_layout::layout::MapDims;

use super::super::gen::{Gen, Known};
use super::super::{no, R};
use crate::ir::*;

impl Gen<'_, '_, '_> {
    /// The map family.
    pub(super) fn map_expr(&mut self, e: &Expr) -> R<Value> {
        Ok(match &*e.kind {
            ExprKind::MapGet { base, rank } => {
                let MapDims { universe: u, bitset_words: bw, slot } = self.map_dims(base.ty)?;
                let (m, r) = (self.expr(base)?, self.int_expr(rank)?);
                let present = self.bit(m, bw, r);
                let inside = self.cmp_imm(IntCC::SignedLessThan, r, u as i64);
                let inside = self.b2i(inside);
                let ok = self.b.ins().band(present, inside);
                self.check(ok);
                let p = self.offset(m, bw);
                match slot {
                    SlotLayout::Words(w) => self.index(p, r, w),
                    SlotLayout::Bits(bits) => {
                        let v = self.load_slot_bits(p, bits, r);
                        self.materialize(&[Known::Val(v)])
                    }
                }
            }
            ExprKind::MapPut { base, rank, value, plan } => self.map_put(e.ty, base, rank, value, plan)?,
            ExprKind::MapBuild { bind, set, rank, value, witness } => {
                let Ty::Enc(rsid) = value.ty else { return no("boxed map entry") };
                let MapDims { universe: u, bitset_words: bw, slot } = self.map_dims(e.ty)?;
                let (n, buf) = self.result_buf(e.ty, "boxed map")?;
                let bp = self.addr(buf);
                self.zero(bp, n);
                if let Some(wv) = *witness {
                    if wv != 0 {
                        let wval = self.iconst(wv as i64);
                        self.store(wval, bp, n - 1);
                    }
                }
                let spec = self.spec_exprs(&[rank, value], *bind);
                self.foreach(*bind, set, None, None, spec, &mut |g| {
                    let r = g.int_expr(rank)?;
                    let ok = g.cmp_imm(IntCC::UnsignedLessThan, r, u as i64);
                    g.check(ok);
                    let v = g.encoded(value, rsid)?;
                    let bp = g.addr(buf);
                    g.set_bit(bp, r);
                    let p = g.offset(bp, bw);
                    match slot {
                        SlotLayout::Words(w) => {
                            let dst = g.index(p, r, w);
                            g.copy(dst, v, w);
                        }
                        SlotLayout::Bits(bits) => {
                            let val = g.load(v, 0);
                            g.store_slot_bits(p, bits, r, val);
                        }
                    }
                    Ok(())
                })?;
                self.addr(buf)
            }
            ExprKind::MapMerge(a, b) => {
                let d @ MapDims { bitset_words: bw, slot, .. } = self.map_dims(e.ty)?;
                let (n, buf) = self.result_buf(e.ty, "boxed map")?;
                let dyn_witness = n > d.words();
                let (f, g_) = (self.expr(a)?, self.expr(b)?);
                let bp = self.addr(buf);
                self.copy(bp, g_, n);
                for i in 0..bw {
                    let (x, y) = (self.load(bp, i), self.load(f, i));
                    let z = self.b.ins().bor(x, y);
                    self.store(z, bp, i);
                }
                self.for_bits(f, bw, &mut |g, r| {
                    let bp = g.addr(buf);
                    let dp = g.offset(bp, bw);
                    let sp = g.offset(f, bw);
                    match slot {
                        SlotLayout::Words(w) => {
                            let dst = g.index(dp, r, w);
                            let src = g.index(sp, r, w);
                            g.copy(dst, src, w);
                        }
                        SlotLayout::Bits(bits) => {
                            let val = g.load_slot_bits(sp, bits, r);
                            g.store_slot_bits(dp, bits, r, val);
                        }
                    }
                    Ok(())
                })?;
                if dyn_witness {
                    let bp = self.addr(buf);
                    let one = self.iconst(1);
                    self.store(one, bp, n - 1);
                }
                self.addr(buf)
            }
            _ => unreachable!("not a map expression"),
        })
    }

    fn map_put(&mut self, ty: Ty, base: &Expr, rank: &Expr, value: &Expr, plan: &MapPutPlan) -> R<Value> {
        let insert = plan.inserts();
        let Ty::Enc(rsid) = value.ty else { return no("boxed map entry") };
        let d @ MapDims { universe: u, bitset_words: bw, slot } = self.map_dims(ty)?;
        let (n, buf) = self.result_buf(ty, "boxed map")?;
        let dyn_witness = n > d.words();
        let r = self.int_expr(rank)?;
        let b = self.expr(base)?;
        let bp = self.addr(buf);
        self.copy(bp, b, n);
        // Empty-tuple key types are checked only on a lookup miss.
        let cond = if insert {
            let c = self.cmp_imm(IntCC::UnsignedLessThan, r, u as i64);
            self.b2i(c)
        } else {
            let present = self.bit(bp, bw, r);
            let inside = self.cmp_imm(IntCC::SignedLessThan, r, u as i64);
            let inside = self.b2i(inside);
            self.b.ins().band(present, inside)
        };
        let (yes, miss, after) = (self.b.create_block(), self.b.create_block(), self.b.create_block());
        self.brif(cond, yes, &[], miss, &[]);
        self.switch(yes);
        let v = self.encoded(value, rsid)?;
        let bp = self.addr(buf);
        self.set_bit(bp, r);
        let p = self.offset(bp, bw);
        match slot {
            SlotLayout::Words(w) => {
                let dst = self.index(p, r, w);
                self.copy(dst, v, w);
            }
            SlotLayout::Bits(bits) => {
                let val = self.load(v, 0);
                self.store_slot_bits(p, bits, r, val);
            }
        }
        if let Some(wv) = plan.insert_witness {
            let wval = self.iconst(wv as i64);
            self.store(wval, bp, n - 1);
        }
        self.b.ins().jump(after, &[]);
        self.switch(miss);
        if insert {
            self.fail();
        } else {
            let reject_canon = &plan.reject_when_canonical;
            let reject_empty = &plan.reject_when_empty;
            if !reject_canon.is_empty() || !reject_empty.is_empty() {
                let mut in_ranges = |ranks: &[std::ops::Range<u64>]| {
                    let mut hit = self.iconst(0);
                    for range in ranks {
                        let lo = self.cmp_imm(IntCC::SignedGreaterThanOrEqual, r, range.start as i64);
                        let hi = self.cmp_imm(IntCC::SignedLessThan, r, range.end as i64);
                        let in_r = self.b.ins().band(lo, hi);
                        let in_r = self.b2i(in_r);
                        hit = self.b.ins().bor(hit, in_r);
                    }
                    hit
                };
                let mut bad = in_ranges(reject_canon);
                if !reject_empty.is_empty() {
                    let hit_empty = in_ranges(reject_empty);
                    let bp = self.addr(buf);
                    let mut bits = self.iconst(0);
                    for i in 0..bw {
                        let word = self.load(bp, i);
                        bits = self.b.ins().bor(bits, word);
                    }
                    let is_empty = self.cmp_imm(IntCC::Equal, bits, 0);
                    let is_empty = self.b2i(is_empty);
                    let empty_bad = self.b.ins().band(hit_empty, is_empty);
                    bad = self.b.ins().bor(bad, empty_bad);
                }
                if dyn_witness {
                    let bp = self.addr(buf);
                    let wword = self.load(bp, n - 1);
                    let is_canon = self.cmp_imm(IntCC::Equal, wword, 0);
                    let is_canon = self.b2i(is_canon);
                    bad = self.b.ins().band(bad, is_canon);
                }
                let ok = self.b.ins().bxor_imm(bad, 1);
                self.check(ok);
            }
            self.b.ins().jump(after, &[]);
        }
        self.switch(after);
        Ok(self.addr(buf))
    }
}
