//! C generation of the map family of encoded expressions: `MapGet`,
//! `MapPut`, `MapBuild` and `MapMerge` (moved verbatim from `encoded.rs`).

use tlx_layout::layout::MapDims;

use super::super::{no, CGen, R};
use crate::ir::*;

impl CGen<'_> {
    /// The map family.
    pub(super) fn map_expr(&mut self, e: &Expr) -> R<String> {
        Ok(match &*e.kind {
            ExprKind::MapGet { base, rank } => {
                let MapDims { universe: u, bitset_words: bw, slot } = self.map_dims(base.ty)?;
                let (b, r) = (self.expr(base)?, self.int_expr(rank)?);
                let k = self.fresh();
                match slot {
                    SlotLayout::Words(w) => format!(
                        "({{ const uint64_t *m{k} = {b}; int64_t r{k} = {r}; if (!tlx_bit(m{k}, {bw}, r{k}) || r{k} >= {u}) return TLX_ERR; m{k} + {bw} + r{k} * {w}; }})"
                    ),
                    SlotLayout::Bits(bits) => {
                        let buf = self.buf(1);
                        format!(
                            "({{ const uint64_t *m{k} = {b}; int64_t r{k} = {r}; if (!tlx_bit(m{k}, {bw}, r{k}) || r{k} >= {u}) return TLX_ERR; {buf}[0] = tlx_sget(m{k} + {bw}, {bits}, (uint64_t)r{k}); (const uint64_t *){buf}; }})"
                        )
                    }
                }
            }
            ExprKind::MapPut { base, rank, value, plan } => {
                let insert = &plan.inserts();
                let Ty::Enc(rsid) = value.ty else { return no("boxed map entry") };
                let MapDims { universe: u, bitset_words: bw, slot } = self.map_dims(e.ty)?;
                let (n, buf) = self.result_buf(e.ty, "boxed map")?;
                let (b, r, v) = (self.expr(base)?, self.int_expr(rank)?, self.encoded(value, rsid)?);
                let k = self.fresh();
                // Check empty-tuple key types only after the ordinary map lookup misses.
                let (cond, miss) = if *insert {
                    (format!("r{k} >= 0 && r{k} < {u}"), "else return TLX_ERR;")
                } else {
                    (format!("tlx_bit({buf}, {bw}, r{k}) && r{k} < {u}"), "")
                };
                let miss = if !insert {
                    let ranks = &plan.reject_when_empty;
                    if ranks.is_empty() {
                        String::new()
                    } else {
                        let non_int =
                            ranks.iter().map(|r| format!("(r{k} >= {} && r{k} < {})", r.start, r.end)).collect::<Vec<_>>().join(" || ");
                        let empty = (0..bw).map(|i| format!("{buf}[{i}] == 0")).collect::<Vec<_>>().join(" && ");
                        format!("else if (({non_int}) && ({empty})) return TLX_ERR;")
                    }
                } else {
                    miss.to_owned()
                };
                let write_slot = match slot {
                    SlotLayout::Words(w) => format!("memcpy({buf} + {bw} + r{k} * {w}, v{k}, {w} * 8);"),
                    SlotLayout::Bits(bits) => format!("tlx_sset({buf} + {bw}, {bits}, (uint64_t)r{k}, v{k}[0]);"),
                };
                format!(
                    "({{ int64_t r{k} = {r}; memcpy({buf}, {b}, {n} * 8); if ({cond}) {{ const uint64_t *v{k} = {v}; {buf}[r{k} >> 6] |= 1ULL << (r{k} & 63); {write_slot} }} {miss} (const uint64_t *){buf}; }})"
                )
            }
            ExprKind::MapBuild { bind, set, rank, value } => {
                let Ty::Enc(rsid) = value.ty else { return no("boxed map entry") };
                let MapDims { universe: u, bitset_words: bw, slot } = self.map_dims(e.ty)?;
                let (n, buf) = self.result_buf(e.ty, "boxed map")?;
                let h0 = self.loop_start(set)?;
                let (r, v) = (self.int_expr(rank)?, self.encoded(value, rsid)?);
                let k = self.fresh();
                let write_slot = match slot {
                    SlotLayout::Words(w) => format!("memcpy({buf} + {bw} + r{k} * {w}, v{k}, {w} * 8);"),
                    SlotLayout::Bits(bits) => format!("tlx_sset({buf} + {bw}, {bits}, (uint64_t)r{k}, v{k}[0]);"),
                };
                let body = format!(
                    "      {{ int64_t r{k} = {r}; if (r{k} < 0 || r{k} >= {u}) return TLX_ERR; const uint64_t *v{k} = {v}; {buf}[r{k} >> 6] |= 1ULL << (r{k} & 63); {write_slot} }}\n"
                );
                let lp = self.foreach(*bind, set, &body, 3, h0, None, None)?;
                format!("({{ memset({buf}, 0, {n} * 8); {{\n{lp} }} (const uint64_t *){buf}; }})")
            }
            ExprKind::MapMerge(a, b) => {
                let MapDims { bitset_words: bw, slot, .. } = self.map_dims(e.ty)?;
                let (n, buf) = self.result_buf(e.ty, "boxed map")?;
                let (a, b) = (self.expr(a)?, self.expr(b)?);
                let k = self.fresh();
                let copy_slot = match slot {
                    SlotLayout::Words(w) => format!("memcpy({buf} + {bw} + r{k} * {w}, f{k} + {bw} + r{k} * {w}, {w} * 8);"),
                    SlotLayout::Bits(bits) => format!("tlx_sset({buf} + {bw}, {bits}, r{k}, tlx_sget(f{k} + {bw}, {bits}, r{k}));"),
                };
                format!(
                    "({{ const uint64_t *f{k} = {a}; memcpy({buf}, {b}, {n} * 8); for (uint32_t w{k} = 0; w{k} < {bw}; w{k}++) {{ uint64_t B{k} = f{k}[w{k}]; {buf}[w{k}] |= B{k}; \
                     while (B{k}) {{ uint64_t r{k} = w{k} * 64 + (uint64_t)__builtin_ctzll(B{k}); B{k} &= B{k} - 1; {copy_slot} }} }} (const uint64_t *){buf}; }})"
                )
            }
            _ => unreachable!("not a map expression"),
        })
    }
}
