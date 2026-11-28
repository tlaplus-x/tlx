//! Value store operations (`ExprKind::RefOp`) in generated C: the
//! arguments are evaluated in order into locals, then `host->ref_op` runs
//! the operation of the model's table (`exec::refops::RefOpTable`, ABI v5).

use std::fmt::Write;

use tlx_layout::scalar::{IMM_INT_BITS, TAG_BITS, TAG_BOOL, TAG_INT, TAG_MASK, TAG_STR};

use super::{no, CGen, Unsupported, R};
use crate::ir::*;

impl CGen<'_> {
    pub(super) fn ref_op(&mut self, e: &Expr, op: &RefOp, args: &[Expr]) -> R<String> {
        match op {
            RefOp::DynEqInt | RefOp::DynEqBool => {
                let k = self.fresh();
                let h = format!("({})[0]", self.expr(&args[0])?);
                let scalar = if *op == RefOp::DynEqInt { self.int_expr(&args[1])? } else { self.bool_expr(&args[1])? };
                let tag = if *op == RefOp::DynEqInt { TAG_INT } else { TAG_BOOL };
                let payload =
                    if *op == RefOp::DynEqInt { format!("((int64_t)h{k} >> {TAG_BITS})") } else { format!("((h{k} >> {TAG_BITS}) != 0)") };
                return Ok(format!(
                    "({{ uint64_t h{k} = {h}; uint64_t t{k} = h{k} & {TAG_MASK}; if (t{k} != {tag}) return TLX_ERR; if ({tag} == {TAG_BOOL} && (h{k} >> {TAG_BITS}) > 1) return TLX_ERR; (int64_t)({payload} == ({scalar})); }})"
                ));
            }
            RefOp::DynToInt | RefOp::DynToBool => {
                let k = self.fresh();
                let h = format!("({})[0]", self.expr(&args[0])?);
                let tag = if *op == RefOp::DynToInt { TAG_INT } else { TAG_BOOL };
                let value = if *op == RefOp::DynToInt {
                    format!("((int64_t)h{k} >> {TAG_BITS})")
                } else {
                    format!("(int64_t)(h{k} >> {TAG_BITS})")
                };
                let canonical =
                    if *op == RefOp::DynToBool { format!("if ((h{k} >> {TAG_BITS}) > 1) return TLX_ERR; ") } else { String::new() };
                return Ok(format!("({{ uint64_t h{k} = {h}; if ((h{k} & {TAG_MASK}) != {tag}) return TLX_ERR; {canonical}{value}; }})"));
            }
            _ => {}
        }
        if self.in_fn {
            return no("value store operation in a compiled function");
        }
        // Immediate scalars inline (handle schema: tlx_layout::scalar).
        match op {
            RefOp::ToInt => {
                let k = self.fresh();
                return Ok(format!(
                    "({{ uint64_t h{k} = ({})[0]; if ((h{k} & {m}) != {t}) return TLX_ERR; (int64_t)h{k} >> {s}; }})",
                    self.expr(&args[0])?,
                    m = TAG_MASK,
                    t = TAG_INT,
                    s = TAG_BITS,
                ));
            }
            RefOp::ToBool => {
                let k = self.fresh();
                return Ok(format!(
                    "({{ uint64_t h{k} = ({})[0]; if ((h{k} & {m}) != {t}) return TLX_ERR; (int64_t)(h{k} >> {s}); }})",
                    self.expr(&args[0])?,
                    m = TAG_MASK,
                    t = TAG_BOOL,
                    s = TAG_BITS,
                ));
            }
            RefOp::FromInt => {
                let (_, buf) = self.result_buf(e.ty, "value store result")?;
                let k = self.fresh();
                let x = self.int_expr(&args[0])?;
                return Ok(format!(
                    "({{ int64_t i{k} = {x}; if (i{k} < -(1LL << {ib}) || i{k} >= (1LL << {ib})) return TLX_ERR; {buf}[0] = (uint64_t)i{k} << {s} | {t}; (const uint64_t *){buf}; }})",
                    ib = IMM_INT_BITS,
                    s = TAG_BITS,
                    t = TAG_INT,
                ));
            }
            RefOp::FromBool => {
                let (_, buf) = self.result_buf(e.ty, "value store result")?;
                let x = self.bool_expr(&args[0])?;
                return Ok(format!(
                    "({{ {buf}[0] = (uint64_t)(({x}) != 0) << {s} | {t}; (const uint64_t *){buf}; }})",
                    s = TAG_BITS,
                    t = TAG_BOOL,
                ));
            }
            _ => {}
        }
        let table = self.refops.clone().ok_or_else(|| Unsupported("no value store operation table".into()))?;
        let id = table.id(op, args.len()).ok_or_else(|| Unsupported("value store operation not in the table".into()))?;
        let h = self.ty.ref_sid();
        let k = self.fresh();
        let mut decl = String::new();
        for (i, a) in args.iter().enumerate() {
            let v = match a.ty {
                Ty::Int => format!("(uint64_t)({})", self.int_expr(a)?),
                Ty::Bool => format!("(uint64_t)({})", self.bool_expr(a)?),
                Ty::Enc(s) if Some(s) == h => format!("({})[0]", self.expr(a)?),
                Ty::Enc(_) => format!("(uint64_t)(uintptr_t)({})", self.expr(a)?),
                Ty::Val => return no("boxed argument of a value store operation"),
            };
            write!(decl, "uint64_t a{k}_{i} = {v}; ").unwrap();
        }
        let list: Vec<String> = (0..args.len()).map(|i| format!("a{k}_{i}")).collect();
        let list = if list.is_empty() { "0".to_string() } else { list.join(", ") };
        write!(decl, "uint64_t a{k}[{}] = {{{list}}};", args.len().max(1)).unwrap();
        if *op == RefOp::Eq {
            // Equal handles are equal values; two immediates of one kind
            // (integers, strings, Booleans) with different payloads are
            // not; model values and nodes follow TLC's rules in the store.
            return Ok(format!(
                "({{ {decl} uint64_t r{k}; uint64_t x{k} = a{k}_0, y{k} = a{k}_1; \
                 if (x{k} == y{k}) r{k} = 1; else if (((x{k} ^ y{k}) & {m}) == 0 && ((x{k} & {m}) == {st} || (x{k} & {m}) == {bt} || (x{k} & {m}) == {it})) r{k} = 0; \
                 else if (h->ref_op(cx, {id}, a{k}, &r{k})) return TLX_ERR; (int64_t)(r{k} != 0); }})",
                m = TAG_MASK,
                st = TAG_STR,
                bt = TAG_BOOL,
                it = TAG_INT,
            ));
        }
        Ok(match e.ty {
            Ty::Int => format!("({{ {decl} uint64_t r{k}; if (h->ref_op(cx, {id}, a{k}, &r{k})) return TLX_ERR; (int64_t)r{k}; }})"),
            Ty::Bool => {
                format!("({{ {decl} uint64_t r{k}; if (h->ref_op(cx, {id}, a{k}, &r{k})) return TLX_ERR; (int64_t)(r{k} != 0); }})")
            }
            Ty::Enc(_) => {
                let (_, buf) = self.result_buf(e.ty, "value store result")?;
                format!("({{ {decl} if (h->ref_op(cx, {id}, a{k}, {buf})) return TLX_ERR; (const uint64_t *){buf}; }})")
            }
            Ty::Val => return no("boxed value store result"),
        })
    }

    /// A loop binding `t` to the handles of the elements of the stored
    /// set `set` (`ExprKind::RefElems`).
    pub(in crate::cgen) fn ref_elems_loop(&mut self, set: &Expr, t: &str, body: &str, pad: &str) -> R<String> {
        if self.in_fn {
            return no("value store iteration in a compiled function");
        }
        if self.refops.is_none() {
            return no("no value store operation table");
        }
        let s = self.expr(set)?;
        let k = self.fresh();
        Ok(format!(
            "{pad}{{ const uint64_t *F{k}; uint64_t N{k}; if (h->ref_elems(cx, ({s})[0], &F{k}, &N{k})) return TLX_ERR;\n{pad}for (uint64_t i{k} = 0; i{k} < N{k}; i{k}++) {{ const uint64_t *{t} = F{k} + i{k};\n{body}{pad}}} }}\n"
        ))
    }
}
