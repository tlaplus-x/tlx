//! Set family of the closure compiler: bit sets, sorted sets, the ranks, the recodes,
//! union field access and the boxed builders (moved verbatim from `encoded.rs`).

use super::super::super::words;
use super::*;
use crate::ir::*;

impl<'c> Compiler<'c> {
    /// The set family.
    pub(super) fn set_expr(&mut self, e: &Expr) -> C<Code> {
        let ty = e.ty;

        Ok(match &*e.kind {
            // ---- encoded sets
            ExprKind::Concat(xs) => {
                let n = self.words(ty)?;
                let parts = xs.iter().map(|x| self.enc(x)).collect::<C<Vec<_>>>()?;
                let out = self.alloc(n);
                self.fresh(
                    Box::new(move |fx| {
                        let mut at = out;
                        for (p, k) in &parts {
                            let l = p.at(fx)?;
                            fx.copy_to(l, at, *k);
                            at += k;
                        }
                        Ok(Loc::frame(out))
                    }),
                    n,
                    out,
                )
            }
            ExprKind::Pack { locs, parts } => {
                let n = self.words(ty)?;
                let locs = locs.clone();
                let parts = parts.iter().map(|x| self.enc(x)).collect::<C<Vec<_>>>()?;
                let out = self.alloc(n);
                self.fresh(
                    Box::new(move |fx| {
                        fx.fr.w[out..out + n].fill(0);
                        for (loc, (p, k)) in locs.iter().zip(&parts) {
                            let l = p.at(fx)?;
                            match *loc {
                                FieldLoc::Words(off) => fx.copy_to(l, out + off, *k),
                                FieldLoc::Bits(pos) => {
                                    let val = fx.word(l, 0);
                                    pos.set_zeroed(&mut fx.fr.w[out..out + n], val);
                                }
                            }
                        }
                        Ok(Loc::frame(out))
                    }),
                    n,
                    out,
                )
            }
            ExprKind::Rank(x) => {
                let (x, n) = self.enc(x)?;
                if n == 0 {
                    // A zero-word encoding (a set over an empty universe)
                    // has a single value: rank 0.
                    return Ok(Code::I(Box::new(move |fx| {
                        x.at(fx)?;
                        Ok(0)
                    })));
                }
                if let Some(w) = self.word_at(0) {
                    return Ok(self.int_at(IntAt::W(w, 0)));
                }
                Code::I(Box::new(move |fx| {
                    let l = x.at(fx)?;
                    Ok(fx.word(l, 0) as i64)
                }))
            }
            ExprKind::Recode { x, arm_base, table, words: k } => {
                let (x, _) = self.enc(x)?;
                let (arm_base, table, k) = (arm_base.clone(), table.clone(), *k as usize);
                let out = self.alloc(k);
                self.fresh(
                    Box::new(move |fx| {
                        let l = x.at(fx)?;
                        let recode = RecodeTable { arm_base: &arm_base, table: &table, words: k };
                        match recode.lookup(|index| fx.word(l, index)) {
                            Some(t) => {
                                fx.fr.w[out..out + k].copy_from_slice(t);
                                Ok(Loc::frame(out))
                            }
                            _ => err("value does not fit the target encoding"),
                        }
                    }),
                    k,
                    out,
                )
            }
            ExprKind::RankUnion { x, arms } => {
                let Shape::Union(arm_shapes) = self.shape(x.ty)?.clone() else { return Err("RankUnion of non-union".into()) };
                let arm_locs: Vec<Box<[FieldLoc]>> = arm_shapes
                    .iter()
                    .map(|a| FieldLayout::of_shape(a).map_or_else(|| Box::from([FieldLoc::Words(0)]), |fl| fl.locs))
                    .collect();
                let (x, _) = self.enc(x)?;
                let arms = arms.clone();
                let bases: Vec<u64> = UnionArms::new(&arms).map(|(base, _)| base).collect();
                Code::I(Box::new(move |fx| {
                    let l = x.at(fx)?;
                    let tag = fx.word(l, 0) as usize;
                    if tag >= arms.len() {
                        return err("unknown union tag");
                    }
                    let locs = &arm_locs[tag];
                    let r = rank_with(&arms[tag], |index| match locs.get(index).copied() {
                        Some(FieldLoc::Words(w)) => fx.word(l, 1 + w),
                        Some(FieldLoc::Bits(pos)) => tlx_layout::layout::extract_bits(fx.word(l, 1 + pos.word), pos.shift, pos.bits),
                        None => 0,
                    });
                    Ok((bases[tag] + r) as i64)
                }))
            }
            ExprKind::Lookup { x, table } => {
                let (x, _) = self.enc(x)?;
                let table = table.clone();
                Code::I(Box::new(move |fx| {
                    let l = x.at(fx)?;
                    Ok(table.get(fx.word(l, 0) as usize).copied().unwrap_or(-1) as i64)
                }))
            }
            ExprKind::RankFlat { x, radices } => {
                let locs = FieldLayout::of_shape(self.shape(x.ty)?).ok_or("RankFlat of non-product")?.locs;
                let (x, _) = self.enc(x)?;
                let radices = radices.clone();
                Code::I(Box::new(move |fx| {
                    let l = x.at(fx)?;
                    let r = rank_with(&radices, |index| match locs.get(index).copied() {
                        Some(FieldLoc::Words(w)) => fx.word(l, w),
                        Some(FieldLoc::Bits(pos)) => tlx_layout::layout::extract_bits(fx.word(l, pos.word), pos.shift, pos.bits),
                        None => 0,
                    });
                    Ok(r as i64)
                }))
            }
            ExprKind::UnionField { base, locs } => {
                let n = self.words(ty)?;
                let (b, _) = self.enc(base)?;
                let locs = locs.clone();
                if locs.iter().all(|o| !matches!(o, Some(FieldLoc::Bits(_)))) {
                    return Ok(Code::E(
                        Box::new(move |fx| {
                            let l = b.at(fx)?;
                            match locs.get(fx.word(l, 0) as usize).copied().flatten() {
                                Some(FieldLoc::Words(off)) => Ok(l.plus(1 + off)),
                                _ => err(NO_FIELD),
                            }
                        }),
                        n,
                    ));
                }
                let out = self.alloc(n);
                self.fresh(
                    Box::new(move |fx| {
                        let l = b.at(fx)?;
                        match locs.get(fx.word(l, 0) as usize).copied().flatten() {
                            Some(FieldLoc::Words(off)) => {
                                fx.copy_to(l.plus(1 + off), out, n);
                                Ok(Loc::frame(out))
                            }
                            Some(FieldLoc::Bits(pos)) => {
                                fx.fr.w[out] = tlx_layout::layout::extract_bits(fx.word(l, 1 + pos.word), pos.shift, pos.bits);
                                Ok(Loc::frame(out))
                            }
                            None => err(NO_FIELD),
                        }
                    }),
                    n,
                    out,
                )
            }
            ExprKind::UnionFieldInt { base, entries } => {
                let (b, _) = self.enc(base)?;
                let entries = entries.clone();
                Code::I(Box::new(move |fx| {
                    let l = b.at(fx)?;
                    match entries.get(fx.word(l, 0) as usize).copied().flatten() {
                        Some((FieldLoc::Words(off), lo)) => Ok(lo + fx.word(l, 1 + off) as i64),
                        Some((FieldLoc::Bits(pos), lo)) => {
                            Ok(lo + tlx_layout::layout::extract_bits(fx.word(l, 1 + pos.word), pos.shift, pos.bits) as i64)
                        }
                        None => err(NO_FIELD),
                    }
                }))
            }

            ExprKind::BitMember { set, rank } => {
                let (s, n) = self.enc(set)?;
                let known = self.known_loc();
                let r = self.int_src(rank)?;
                if let Some(l) = known {
                    return Ok(Code::B(Box::new(move |fx| {
                        let r = r.get(fx)?;
                        Ok(r >= 0 && (r as usize) < n * 64 && (fx.word(l, r as usize / 64) >> (r % 64)) & 1 == 1)
                    })));
                }
                Code::B(Box::new(move |fx| {
                    let l = s.at(fx)?;
                    let r = r.get(fx)?;
                    Ok(r >= 0 && (r as usize) < n * 64 && (fx.word(l, r as usize / 64) >> (r % 64)) & 1 == 1)
                }))
            }
            ExprKind::BitSetOp(op, a, b) => {
                let n = self.words(ty)?;
                let (a, _) = self.enc(a)?;
                let place = self.last;
                let (b, _) = self.enc(b)?;
                let out = self.out_slot(place, n);
                let op = *op;
                self.fresh(
                    Box::new(move |fx| {
                        let la = a.at(fx)?;
                        fx.copy_to(la, out, n);
                        let lb = b.at(fx)?;
                        for i in 0..n {
                            let y = fx.word(lb, i);
                            let x = &mut fx.fr.w[out + i];
                            *x = match op {
                                SetOp::Union => *x | y,
                                SetOp::Inter => *x & y,
                                SetOp::Diff => *x & !y,
                            };
                        }
                        Ok(Loc::frame(out))
                    }),
                    n,
                    out,
                )
            }
            ExprKind::BitCard(s) => {
                let (s, n) = self.enc(s)?;
                Code::I(Box::new(move |fx| {
                    let l = s.at(fx)?;
                    Ok(fx.get(l, n).iter().map(|w| w.count_ones() as i64).sum())
                }))
            }
            ExprKind::BitSet(rs) => {
                let n = self.words(ty)?;
                let Ty::Enc(sid) = ty else { unreachable!() };
                let u = self.t.node(sid).set_elem().and_then(|e| e.bitset_universe()).ok_or("BitSet of a non-bitset")?;
                let rs = rs.iter().map(|r| self.int_(r)).collect::<C<Vec<_>>>()?;
                let out = self.alloc(n);
                self.fresh(
                    Box::new(move |fx| {
                        fx.fr.w[out..out + n].fill(0);
                        for r in &rs {
                            let r = r(fx)?;
                            if r < 0 || r as u64 >= u {
                                return err("set element outside the layout");
                            }
                            words::bit_set(&mut fx.fr.w[out..out + n], r as usize);
                        }
                        Ok(Loc::frame(out))
                    }),
                    n,
                    out,
                )
            }
            ExprKind::SortedMember { set, elem, elem_words } => {
                let (s, _) = self.enc(set)?;
                let (x, _) = self.enc(elem)?;
                let k = *elem_words as usize;
                Code::B(Box::new(move |fx| {
                    let ls = s.at(fx)?;
                    let lx = x.at(fx)?;
                    let len = fx.word(ls, 0) as usize;
                    Ok(crate::exec::encops::sorted_member(fx.get(ls, 1 + len * k), fx.get(lx, k), k))
                }))
            }
            ExprKind::SortedInsert { set, elem, elem_words, max_card } => {
                let n = self.words(ty)?;
                let (s, _) = self.enc(set)?;
                let (x, _) = self.enc(elem)?;
                let (k, max_card) = (*elem_words as usize, *max_card as usize);
                let xstage = self.alloc(k);
                let out = self.alloc(n);
                self.fresh(
                    Box::new(move |fx| {
                        let ls = s.at(fx)?;
                        fx.copy_to(ls, out, n);
                        let lx = x.at(fx)?;
                        fx.copy_to(lx, xstage, k);
                        let (lo, hi) = fx.fr.w.split_at_mut(out);
                        if !crate::exec::encops::sorted_add(&mut hi[..n], &lo[xstage..xstage + k], k, max_card as u64) {
                            return err(SET_TOO_LARGE);
                        }
                        Ok(Loc::frame(out))
                    }),
                    n,
                    out,
                )
            }
            ExprKind::SortedOp { op, a, b, elem_words, max_card } => {
                let n = self.words(ty)?;
                let (a, na) = self.enc(a)?;
                let (b, nb) = self.enc(b)?;
                let (k, max_card, op) = (*elem_words as usize, *max_card as usize, *op);
                let sa = self.alloc(na);
                let sb = self.alloc(nb);
                let out = self.alloc(n);
                self.fresh(
                    Box::new(move |fx| {
                        let la = a.at(fx)?;
                        fx.copy_to(la, sa, na);
                        let lb = b.at(fx)?;
                        fx.copy_to(lb, sb, nb);
                        let (lo, hi) = fx.fr.w.split_at_mut(out);
                        if !crate::exec::encops::sorted_op(op, &lo[sa..sa + na], &lo[sb..sb + nb], k, max_card as u64, &mut hi[..n]) {
                            return err(SET_TOO_LARGE);
                        }
                        Ok(Loc::frame(out))
                    }),
                    n,
                    out,
                )
            }
            _ => unreachable!("not an encoded-value expression"),
        })
    }
}
