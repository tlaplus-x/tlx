//! Map family of the closure compiler: `MapGet`, `MapPut`, `MapBuild` and
//! `MapMerge` (moved verbatim from `encoded.rs`).

use super::super::super::words;
use super::super::Code;
use super::*;
use crate::ir::*;

impl<'c> Compiler<'c> {
    /// The map family.
    pub(super) fn map_expr(&mut self, e: &Expr) -> C<Code> {
        let ty = e.ty;
        Ok(match &*e.kind {
            ExprKind::MapGet { base, rank } => self.map_get(base, rank)?,
            ExprKind::MapPut { base, rank, value, plan } => self.map_put(ty, base, rank, value, plan)?,
            ExprKind::MapBuild { bind, set, rank, value } => {
                let MapDims { universe: u, bitset_words: bw, slot } = self.map_dims(ty)?;
                let n = self.words(ty)?;
                let src = self.src(set, false)?;
                let bind = self.slots[*bind as usize];
                let r = self.int_(rank)?;
                let (v, _) = self.enc(value)?;
                let out = self.alloc(n);
                self.fresh(
                    Box::new(move |fx| {
                        fx.fr.w[out..out + n].fill(0);
                        src.run(fx, bind, &mut |fx| {
                            let r = r(fx)?;
                            if r < 0 || r as usize >= u {
                                return err("function argument outside the layout");
                            }
                            let lv = v.at(fx)?;
                            words::bit_set(&mut fx.fr.w[out..out + bw], r as usize);
                            match slot {
                                SlotLayout::Words(w) => {
                                    fx.copy_to(lv, out + bw + r as usize * w, w);
                                }
                                SlotLayout::Bits(bits) => {
                                    let val = fx.word(lv, 0);
                                    SlotLayout::insert(bits, &mut fx.fr.w[out + bw..out + n], r as usize, val);
                                }
                            }
                            Ok(true)
                        })?;
                        Ok(Loc::frame(out))
                    }),
                    n,
                    out,
                )
            }
            ExprKind::MapMerge(a, b) => {
                let MapDims { bitset_words: bw, slot, .. } = self.map_dims(ty)?;
                let n = self.words(ty)?;
                let (a, _) = self.enc(a)?;
                let (b, _) = self.enc(b)?;
                let fstage = self.alloc(n);
                let out = self.alloc(n);
                self.fresh(
                    Box::new(move |fx| {
                        let lf = a.at(fx)?;
                        fx.copy_to(lf, fstage, n);
                        let lm = b.at(fx)?;
                        fx.copy_to(lm, out, n);
                        let (lo, hi) = fx.fr.w.split_at_mut(out);
                        let f = &lo[fstage..fstage + n];
                        let m = &mut hi[..n];
                        for r in words::bit_ranks(&f[..bw]) {
                            words::bit_set(m, r);
                            match slot {
                                SlotLayout::Words(w) => {
                                    let off = bw + r * w;
                                    m[off..off + w].copy_from_slice(&f[off..off + w]);
                                }
                                SlotLayout::Bits(bits) => {
                                    let val = SlotLayout::extract(bits, &f[bw..], r);
                                    SlotLayout::insert(bits, &mut m[bw..], r, val);
                                }
                            }
                        }
                        Ok(Loc::frame(out))
                    }),
                    n,
                    out,
                )
            }
            _ => unreachable!("not a map expression"),
        })
    }

    fn map_get(&mut self, base: &Expr, rank: &Expr) -> C<Code> {
        let MapDims { universe: u, bitset_words: bw, slot } = self.map_dims(base.ty)?;
        let (b, _) = self.enc(base)?;
        let r = self.int_(rank)?;
        Ok(match slot {
            SlotLayout::Words(w) => Code::E(
                Box::new(move |fx| {
                    let m = b.at(fx)?;
                    let r = r(fx)?;
                    if r < 0 || r as usize >= u || (fx.word(m, r as usize / 64) >> (r % 64)) & 1 == 0 {
                        return err(NOT_IN_DOMAIN);
                    }
                    Ok(m.plus(bw + r as usize * w))
                }),
                w,
            ),
            SlotLayout::Bits(bits) => {
                let out = self.alloc(1);
                self.fresh(
                    Box::new(move |fx| {
                        let m = b.at(fx)?;
                        let r = r(fx)?;
                        if r < 0 || r as usize >= u || (fx.word(m, r as usize / 64) >> (r % 64)) & 1 == 0 {
                            return err(NOT_IN_DOMAIN);
                        }
                        let (sw, sh) = SlotLayout::bit_pos(bits, r as usize);
                        fx.fr.w[out] = tlx_layout::layout::extract_bits(fx.word(m, bw + sw), sh, bits);
                        Ok(Loc::frame(out))
                    }),
                    1,
                    out,
                )
            }
        })
    }

    fn map_put(&mut self, ty: Ty, base: &Expr, rank: &Expr, value: &Expr, plan: &MapPutPlan) -> C<Code> {
        let MapDims { universe: u, bitset_words: bw, slot } = self.map_dims(ty)?;
        let n = self.words(ty)?;
        let r = self.int_(rank)?;
        let (b, _) = self.enc(base)?;
        let place = self.last;
        let (v, _) = self.enc(value)?;
        let insert = plan.inserts();
        let non_integer = plan.reject_when_empty.clone();
        let out = self.out_slot(place, n);
        Ok(self.fresh(
            Box::new(move |fx| {
                let r = r(fx)?;
                let l = b.at(fx)?;
                fx.copy_to(l, out, n);
                let inside = r >= 0 && (r as usize) < u;
                if insert && !inside {
                    return err("function argument outside the layout");
                }
                if inside && (insert || words::bit_test(&fx.fr.w[out..out + bw], r)) {
                    let lv = v.at(fx)?;
                    words::bit_set(&mut fx.fr.w[out..out + bw], r as usize);
                    match slot {
                        SlotLayout::Words(w) => {
                            fx.copy_to(lv, out + bw + r as usize * w, w);
                        }
                        SlotLayout::Bits(bits) => {
                            let val = fx.word(lv, 0);
                            SlotLayout::insert(bits, &mut fx.fr.w[out + bw..out + n], r as usize, val);
                        }
                    }
                } else if !insert
                    && non_integer.iter().any(|range| range.contains(&(r as u64)))
                    && fx.fr.w[out..out + bw].iter().all(|w| *w == 0)
                {
                    return err("Attempted to access tuple at a non integral index");
                }
                Ok(Loc::frame(out))
            }),
            n,
            out,
        ))
    }
}
