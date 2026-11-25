//! C generation of the set family of encoded expressions: bit sets, sorted sets, the ranks,
//! the recodes, union field access and the boxed builders (moved verbatim from
//! `encoded.rs`).

use tlx_layout::Shape;

use super::super::{no, CGen, R};
use crate::ir::encoding::{
    union_loc_desc, RecodeTable, UnionArms, UNION_DESC_BIT_SHIFT, UNION_DESC_FIELD_MASK, UNION_DESC_MISSING, UNION_DESC_WORD_SHIFT,
};
use crate::ir::*;

fn c_union_scalar_extract(u: &str, d: &str) -> String {
    format!(
        "({u}[(uint64_t){d} >> {UNION_DESC_WORD_SHIFT}] >> (({d} >> {UNION_DESC_BIT_SHIFT}) & {UNION_DESC_FIELD_MASK})) & (~(uint64_t)0 >> ({d} & {UNION_DESC_FIELD_MASK}))"
    )
}

fn c_read_loc(ptr: &str, loc: FieldLoc) -> String {
    match loc {
        FieldLoc::Words(w) => format!("{ptr}[{w}]"),
        FieldLoc::Bits(pos) => format!("tlx_bget({ptr}, {}, {}, {})", pos.word, pos.shift, pos.bits),
    }
}

impl CGen<'_> {
    /// The set family.
    pub(super) fn set_expr(&mut self, e: &Expr) -> R<String> {
        Ok(match &*e.kind {
            ExprKind::BitMember { set, rank } => {
                let Ty::Enc(sid) = set.ty else { return no("boxed membership") };
                let n = self.words(sid);
                format!("tlx_bit({}, {n}, {})", self.expr(set)?, self.int_expr(rank)?)
            }
            ExprKind::BitSetOp(op, a, b) => {
                let (n, buf) = self.result_buf(e.ty, "boxed set")?;
                let o = match op {
                    SetOp::Union => "x_[i_] | y_[i_]",
                    SetOp::Inter => "x_[i_] & y_[i_]",
                    SetOp::Diff => "x_[i_] & ~y_[i_]",
                };
                format!(
                    "({{ const uint64_t *x_ = {}, *y_ = {}; for (int i_ = 0; i_ < {n}; i_++) {buf}[i_] = {o}; {buf}; }})",
                    self.expr(a)?,
                    self.expr(b)?
                )
            }
            ExprKind::BitCard(s) => {
                let Ty::Enc(sid) = s.ty else { return no("boxed cardinality") };
                let n = self.words(sid);
                format!("tlx_card({}, {n})", self.expr(s)?)
            }
            ExprKind::Rank(x) => {
                // A zero-word encoding (a set over an empty universe) has a
                // single value: rank 0.
                if matches!(x.ty, Ty::Enc(sid) if self.words(sid) == 0) {
                    format!("((void)({}), (int64_t)0)", self.expr(x)?)
                } else {
                    format!("((int64_t)({})[0])", self.expr(x)?)
                }
            }
            ExprKind::Concat(xs) => {
                let (_, buf) = self.result_buf(e.ty, "boxed construction")?;
                let mut code = String::from("({ ");
                let mut off = 0;
                for x in xs {
                    let Ty::Enc(xs_) = x.ty else { return no("boxed part") };
                    let n = self.words(xs_);
                    let v = self.expr(x)?;
                    code.push_str(&format!("memcpy({buf} + {off}, {v}, {n} * 8); "));
                    off += n;
                }
                code.push_str(&format!("(const uint64_t *){buf}; }})"));
                code
            }
            ExprKind::Pack { locs, parts } => self.cgen_pack(e.ty, locs, parts)?,
            ExprKind::BitSet(rs) => {
                let (n, buf) = self.result_buf(e.ty, "boxed set")?;
                let u = self.universe(e.ty)?;
                let mut code = format!("({{ memset({buf}, 0, {n} * 8); ");
                for r in rs {
                    let r = self.int_expr(r)?;
                    code.push_str(&format!(
                        "{{ int64_t r_ = {r}; if (r_ < 0 || r_ >= {u}) return TLX_ERR; {buf}[r_ >> 6] |= 1ULL << (r_ & 63); }} "
                    ));
                }
                code.push_str(&format!("(const uint64_t *){buf}; }})"));
                code
            }
            ExprKind::UnionField { base, locs } => self.cgen_union_field(base, locs)?,
            ExprKind::UnionFieldInt { base, entries } => self.cgen_union_field_int(base, entries)?,
            ExprKind::SortedMember { set, elem, elem_words } => {
                let (s_, x) = (self.expr(set)?, self.expr(elem)?);
                format!("tlx_sorted_member({s_}, {x}, {elem_words})")
            }
            ExprKind::Recode { x, arm_base, table, words } => {
                let v = self.expr(x)?;
                let tbl = self.static_words(table);
                let codes = RecodeTable { arm_base, table, words: *words as usize }.codes();
                let code = if arm_base.is_empty() {
                    "x_[0]".to_string()
                } else {
                    let base = self.static_words(arm_base);
                    format!("(x_[0] < {} ? {base}[x_[0]] + x_[1] : (uint64_t)-1)", arm_base.len())
                };
                format!("({{ const uint64_t *x_ = {v}; uint64_t c_ = {code}; if (c_ >= {codes} || {tbl}[c_ * {words}] == (uint64_t)-1) return TLX_ERR; {tbl} + c_ * {words}; }})")
            }
            ExprKind::RankUnion { x, arms } => {
                let Ty::Enc(xsid) = x.ty else { return no("boxed union") };
                let Shape::Union(arm_shapes) = self.ty.shape(xsid).clone() else { return no("RankUnion of non-union") };
                let v = self.expr(x)?;
                let mut code = format!("({{ const uint64_t *x_ = {v}; uint64_t r_ = 0; switch (x_[0]) {{ ");
                for (i, (base, radices)) in UnionArms::new(arms).enumerate() {
                    let locs: Box<[FieldLoc]> =
                        FieldLayout::of_shape(&arm_shapes[i]).map_or_else(|| Box::from([FieldLoc::Words(0)]), |fl| fl.locs);
                    code.push_str(&format!("case {i}: r_ = {base}ULL; "));
                    // The arm offset plus the mixed-radix rank within the arm.
                    let mut inner = String::from("0ULL");
                    for (j, c) in radices.iter().enumerate() {
                        let digit = c_read_loc("x_", locs[j].offset_words(1));
                        inner = format!("(({inner}) * {c}ULL + {digit})");
                    }
                    code.push_str(&format!("r_ += {inner}; break; "));
                }
                code.push_str("default: return TLX_ERR; } (int64_t)r_; })");
                code
            }
            ExprKind::Lookup { x, table } => {
                let v = self.expr(x)?;
                let items: Vec<String> = table.iter().map(|x| x.to_string()).collect();
                let tbl = self.static_array("tbl", "int32_t", &items, "-1");
                format!("({{ uint64_t r_ = ({v})[0]; r_ < {} ? (int64_t){tbl}[r_] : (int64_t)-1; }})", table.len())
            }
            ExprKind::RankFlat { x, radices } => {
                let Ty::Enc(xsid) = x.ty else { return no("boxed product") };
                let fl = FieldLayout::of_shape(self.ty.shape(xsid))
                    .ok_or_else(|| super::super::Unsupported("RankFlat of non-product".into()))?;
                let v = self.expr(x)?;
                let mut code = format!("({{ const uint64_t *x_ = {v}; uint64_t r_ = 0; ");
                for (i, c) in radices.iter().enumerate() {
                    let digit = c_read_loc("x_", fl.locs[i]);
                    code.push_str(&format!("r_ = r_ * {c}ULL + {digit}; "));
                }
                code.push_str("(int64_t)r_; })");
                code
            }
            ExprKind::SortedInsert { set, elem, elem_words, max_card } => {
                let (n, buf) = self.result_buf(e.ty, "boxed set")?;
                let (s_, x) = (self.expr(set)?, self.expr(elem)?);
                format!("({{ if (!tlx_sorted_insert({buf}, {n}, {s_}, {x}, {elem_words}, {max_card})) return TLX_ERR; (const uint64_t *){buf}; }})")
            }
            ExprKind::SortedOp { op, a, b, elem_words, max_card } => {
                let opn = match op {
                    SetOp::Union => 0,
                    SetOp::Inter => 1,
                    SetOp::Diff => 2,
                };
                let (n, buf) = self.result_buf(e.ty, "boxed set")?;
                let (a, b) = (self.expr(a)?, self.expr(b)?);
                format!("({{ if (!tlx_sorted_op({opn}, {buf}, {n}, {a}, {b}, {elem_words}, {max_card})) return TLX_ERR; (const uint64_t *){buf}; }})")
            }
            _ => unreachable!("not an encoded-value expression"),
        })
    }

    fn cgen_pack(&mut self, ty: Ty, locs: &[FieldLoc], parts: &[Expr]) -> R<String> {
        let (total, buf) = self.result_buf(ty, "boxed construction")?;
        let mut code = format!("({{ memset({buf}, 0, {total} * 8); ");
        for (loc, x) in locs.iter().zip(parts) {
            let Ty::Enc(xs_) = x.ty else { return no("boxed part") };
            let n = self.words(xs_);
            let v = self.expr(x)?;
            match *loc {
                FieldLoc::Words(off) => {
                    if n > 0 {
                        code.push_str(&format!("memcpy({buf} + {off}, {v}, {n} * 8); "));
                    } else {
                        // Still evaluate zero-width parts so runtime errors and
                        // layout misses (e.g. a set observed empty in pre-run
                        // becoming non-empty) are never suppressed.
                        code.push_str(&format!("(void)({v}); "));
                    }
                }
                FieldLoc::Bits(pos) => {
                    code.push_str(&format!("tlx_bset({buf}, {}, {}, {}, ({v})[0]); ", pos.word, pos.shift, pos.bits));
                }
            }
        }
        code.push_str(&format!("(const uint64_t *){buf}; }})"));
        Ok(code)
    }

    fn cgen_union_field(&mut self, base: &Expr, locs: &[Option<FieldLoc>]) -> R<String> {
        if locs.iter().all(|o| !matches!(o, Some(FieldLoc::Bits(_)))) {
            let items: Vec<String> = locs
                .iter()
                .map(|o| match o {
                    Some(FieldLoc::Words(x)) => i32::try_from(*x)
                        .map(|n| n.to_string())
                        .map_err(|_| super::super::Unsupported("union field offset exceeds i32".into())),
                    _ => Ok("-1".to_string()),
                })
                .collect::<R<_>>()?;
            let tbl = self.static_array("uo", "int32_t", &items, "");
            let b = self.expr(base)?;
            Ok(format!(
                "({{ const uint64_t *u_ = {b}; int32_t o_ = u_[0] < {} ? {tbl}[u_[0]] : -1; if (o_ < 0) return TLX_ERR; u_ + 1 + o_; }})",
                items.len()
            ))
        } else {
            let items: Vec<String> = locs
                .iter()
                .map(|o| {
                    union_loc_desc(*o)
                        .map(|d| format!("{d}LL"))
                        .ok_or_else(|| super::super::Unsupported("union field descriptor overflow".into()))
                })
                .collect::<R<_>>()?;
            let tbl = self.static_array("uo", "int64_t", &items, "-1");
            let b = self.expr(base)?;
            let buf = self.buf(1);
            let extract = c_union_scalar_extract("u_", "d_");
            Ok(format!(
                "({{ const uint64_t *u_ = {b}; int64_t d_ = u_[0] < {} ? {tbl}[u_[0]] : {UNION_DESC_MISSING}; if (d_ < 0) return TLX_ERR; {buf}[0] = {extract}; (const uint64_t *){buf}; }})",
                items.len()
            ))
        }
    }

    fn cgen_union_field_int(&mut self, base: &Expr, entries: &[Option<(FieldLoc, i64)>]) -> R<String> {
        let descs: Vec<String> = entries
            .iter()
            .map(|o| {
                union_loc_desc(o.map(|x| x.0))
                    .map(|d| format!("{d}LL"))
                    .ok_or_else(|| super::super::Unsupported("union field descriptor overflow".into()))
            })
            .collect::<R<_>>()?;
        let los: Vec<String> = entries.iter().map(|o| o.map_or("0".to_string(), |x| format!("{}LL", x.1))).collect();
        let to = self.static_array("ufo", "int64_t", &descs, "-1");
        let tl = self.static_array("ufl", "int64_t", &los, "0");
        let b = self.expr(base)?;
        let extract = c_union_scalar_extract("u_", "d_");
        Ok(format!(
            "({{ const uint64_t *u_ = {b}; int64_t d_ = u_[0] < {} ? {to}[u_[0]] : {UNION_DESC_MISSING}; if (d_ < 0) return TLX_ERR; uint64_t v_ = {extract}; (int64_t)v_ + {tl}[u_[0]]; }})",
            descs.len()
        ))
    }
}
