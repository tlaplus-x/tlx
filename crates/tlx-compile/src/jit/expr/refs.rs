//! Value store operations (`ExprKind::RefOp`) in JIT code: as in the
//! generated C (`cgen::expr::refs`), the arguments are evaluated in order,
//! then `host->ref_op` runs the operation of the model's table.

use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_codegen::ir::{InstBuilder, Value};
use tlx_layout::scalar::{IMM_INT_BITS, TAG_BITS, TAG_BOOL, TAG_INT, TAG_MASK, TAG_STR};

use super::super::gen::{Gen, HostFn};
use super::super::{no, Unsupported, I32, R};
use crate::ir::*;

impl Gen<'_, '_, '_> {
    pub(super) fn ref_op(&mut self, e: &Expr, op: &RefOp, args: &[Expr]) -> R<Value> {
        match op {
            RefOp::DynEqInt | RefOp::DynEqBool => {
                let p = self.expr(&args[0])?;
                let h = self.load(p, 0);
                let scalar = if *op == RefOp::DynEqInt { self.int_expr(&args[1])? } else { self.bool_expr(&args[1])? };
                let want = if *op == RefOp::DynEqInt { TAG_INT } else { TAG_BOOL };
                let tag = self.b.ins().band_imm(h, TAG_MASK as i64);
                let expected = self.cmp_imm(IntCC::Equal, tag, want as i64);
                self.check(expected);
                let payload = if *op == RefOp::DynEqInt {
                    self.b.ins().sshr_imm(h, TAG_BITS as i64)
                } else {
                    let payload = self.b.ins().ushr_imm(h, TAG_BITS as i64);
                    let canonical = self.cmp_imm(IntCC::UnsignedLessThanOrEqual, payload, 1);
                    self.check(canonical);
                    self.b.ins().ushr_imm(h, TAG_BITS as i64)
                };
                let same = self.cmp(IntCC::Equal, payload, scalar);
                let result = self.b.ins().band(expected, same);
                return Ok(self.b2i(result));
            }
            RefOp::DynToInt | RefOp::DynToBool => {
                let p = self.expr(&args[0])?;
                let h = self.load(p, 0);
                let tag = self.b.ins().band_imm(h, TAG_MASK as i64);
                let want = if *op == RefOp::DynToInt { TAG_INT } else { TAG_BOOL };
                let valid = self.cmp_imm(IntCC::Equal, tag, want as i64);
                self.check(valid);
                return Ok(if *op == RefOp::DynToInt {
                    self.b.ins().sshr_imm(h, TAG_BITS as i64)
                } else {
                    let payload = self.b.ins().ushr_imm(h, TAG_BITS as i64);
                    let canonical = self.cmp_imm(IntCC::UnsignedLessThanOrEqual, payload, 1);
                    self.check(canonical);
                    payload
                });
            }
            _ => {}
        }
        if self.in_fn {
            return no("value store operation in a compiled function");
        }
        // Immediate scalars inline (handle schema: tlx_layout::scalar), as in C.
        match op {
            RefOp::ToInt | RefOp::ToBool => {
                let p = self.expr(&args[0])?;
                let h = self.load(p, 0);
                let tag = self.b.ins().band_imm(h, TAG_MASK as i64);
                let want = if *op == RefOp::ToInt { TAG_INT } else { TAG_BOOL };
                let ok = self.cmp_imm(IntCC::Equal, tag, want as i64);
                self.check(ok);
                let sh = TAG_BITS as i64;
                return Ok(if *op == RefOp::ToInt { self.b.ins().sshr_imm(h, sh) } else { self.b.ins().ushr_imm(h, sh) });
            }
            RefOp::FromInt | RefOp::FromBool => {
                let (x, tag) = if *op == RefOp::FromInt {
                    let x = self.int_expr(&args[0])?;
                    let lo = self.cmp_imm(IntCC::SignedGreaterThanOrEqual, x, -(1i64 << IMM_INT_BITS));
                    let hi = self.cmp_imm(IntCC::SignedLessThan, x, 1i64 << IMM_INT_BITS);
                    let ok = self.b.ins().band(lo, hi);
                    self.check(ok);
                    (x, TAG_INT as i64)
                } else {
                    let b = self.bool_expr(&args[0])?;
                    let nz = self.cmp_imm(IntCC::NotEqual, b, 0);
                    (self.b2i(nz), TAG_BOOL as i64)
                };
                let sh = self.b.ins().ishl_imm(x, TAG_BITS as i64);
                let h = self.b.ins().bor_imm(sh, tag);
                let ob = self.buf(1);
                let op = self.addr(ob);
                self.store(h, op, 0);
                return Ok(self.addr(ob));
            }
            _ => {}
        }
        let table = self.cx.refops.clone().ok_or_else(|| Unsupported("no value store operation table".into()))?;
        let id = table.id(op, args.len()).ok_or_else(|| Unsupported("value store operation not in the table".into()))?;
        let h = self.cx.ty.ref_sid();
        let mut vals = Vec::with_capacity(args.len());
        for a in args {
            vals.push(match a.ty {
                Ty::Int => self.int_expr(a)?,
                Ty::Bool => self.bool_expr(a)?,
                Ty::Enc(s) if Some(s) == h => {
                    let p = self.expr(a)?;
                    self.load(p, 0)
                }
                Ty::Enc(_) => self.expr(a)?,
                Ty::Val => return no("boxed argument of a value store operation"),
            });
        }
        let ab = self.buf(vals.len().max(1));
        let ap = self.addr(ab);
        for (i, v) in vals.into_iter().enumerate() {
            self.store(v, ap, i);
        }
        let n = match e.ty {
            Ty::Enc(sid) => self.cx.ty.words(sid) as usize,
            Ty::Int | Ty::Bool => 1,
            Ty::Val => return no("boxed value store result"),
        };
        let ob = self.buf(n);
        let outp = self.addr(ob);
        if *op == RefOp::Eq {
            // Equal handles are equal values; two immediates of one kind
            // (integers, strings, Booleans) with different payloads are
            // not; anything else is decided in the store.
            let (x, y) = (self.load(ap, 0), self.load(ap, 1));
            let same = self.cmp(IntCC::Equal, x, y);
            let same = self.b2i(same);
            let diff = self.b.ins().bxor(x, y);
            let dt = self.b.ins().band_imm(diff, TAG_MASK as i64);
            let one_kind = self.cmp_imm(IntCC::Equal, dt, 0);
            let tag = self.b.ins().band_imm(x, TAG_MASK as i64);
            let s = self.cmp_imm(IntCC::Equal, tag, TAG_STR as i64);
            let bl = self.cmp_imm(IntCC::Equal, tag, TAG_BOOL as i64);
            let i = self.cmp_imm(IntCC::Equal, tag, TAG_INT as i64);
            let scalar = self.b.ins().bor(s, bl);
            let scalar = self.b.ins().bor(scalar, i);
            let unequal = self.b.ins().band(one_kind, scalar);
            let unequal = self.b2i(unequal);
            let decided = self.b.ins().bor(same, unequal);
            let (j, r) = self.join();
            let call = self.b.create_block();
            self.brif(decided, j, &[same.into()], call, &[]);
            self.switch(call);
            let idv = self.b.ins().iconst(I32, id as i64);
            let rc = self.call_host(HostFn::RefOp, &[idv, ap, outp]).expect("ref_op returns a code");
            let ok = self.cmp_imm(IntCC::Equal, rc, 0);
            self.check(ok);
            let v = self.load(outp, 0);
            let nz = self.cmp_imm(IntCC::NotEqual, v, 0);
            let v = self.b2i(nz);
            self.b.ins().jump(j, &[v.into()]);
            self.switch(j);
            return Ok(r);
        }
        let op = outp;
        let idv = self.b.ins().iconst(I32, id as i64);
        let rc = self.call_host(HostFn::RefOp, &[idv, ap, op]).expect("ref_op returns a code");
        let ok = self.cmp_imm(IntCC::Equal, rc, 0);
        self.check(ok);
        Ok(match e.ty {
            Ty::Enc(_) => self.addr(ob),
            _ => self.load(op, 0),
        })
    }

    /// `body` for each element of the stored set `set` (handles bound to
    /// `bind` as pointers to their words, `ExprKind::RefElems`).
    pub(in crate::jit) fn ref_elems_loop(&mut self, bind: Temp, set: &Expr, body: &mut dyn FnMut(&mut Self) -> R<()>) -> R<()> {
        if self.in_fn {
            return no("value store iteration in a compiled function");
        }
        if self.cx.refops.is_none() {
            return no("no value store operation table");
        }
        let s = self.expr(set)?;
        let hv = self.load(s, 0);
        let (fb, nb) = (self.buf(1), self.buf(1));
        let (fp, np) = (self.addr(fb), self.addr(nb));
        let rc = self.call_host(HostFn::RefElems, &[hv, fp, np]).expect("ref_elems returns a code");
        let ok = self.cmp_imm(IntCC::Equal, rc, 0);
        self.check(ok);
        let (first, n) = (self.load(fp, 0), self.load(np, 0));
        let zero = self.iconst(0);
        self.for_range(zero, n, false, &mut |g, i| {
            let off = g.b.ins().ishl_imm(i, 3);
            let t = g.b.ins().iadd(first, off);
            g.with_temp(bind, t, |g| body(g))
        })
    }
}
