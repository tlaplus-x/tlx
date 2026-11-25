//! C generation for expressions (GCC/clang statement expressions).

mod encoded;
mod maps;
mod refs;
mod sequences;
mod sets;

use tlx_layout::layout::{self, bitset_universe, MapDims};
use tlx_layout::Shape;

use super::{no, temp, CGen, Unsupported, R};
use crate::enc::mixed::RegionCtx;
use crate::ir::*;
use crate::types::scalar_arm;

impl CGen<'_> {
    pub(super) fn bool_expr(&mut self, e: &Expr) -> R<String> {
        match e.ty {
            Ty::Bool => self.expr(e),
            _ => no("non-boolean condition"),
        }
    }

    pub(super) fn int_expr(&mut self, e: &Expr) -> R<String> {
        match e.ty {
            Ty::Int => self.expr(e),
            _ => no("non-integer operand"),
        }
    }

    /// Pointer to an encoding of `e` in shape `sid`.
    pub(super) fn encoded(&mut self, e: &Expr, sid: ShapeId) -> R<String> {
        if e.ty == Ty::Enc(sid) {
            return self.expr(e);
        }
        match (e.ty, self.ty.shape(sid).clone()) {
            (Ty::Int, Shape::Int { lo, hi }) => {
                let v = self.expr(e)?;
                let b = self.buf(1);
                Ok(format!(
                    "({{ int64_t v_ = {v}; if (v_ < {lo}LL || v_ > {hi}LL) return TLX_ERR; {b}[0] = (uint64_t)(v_ - ({lo}LL)); {b}; }})"
                ))
            }
            (Ty::Bool, Shape::Bool) => {
                let v = self.expr(e)?;
                let b = self.buf(1);
                Ok(format!("({{ {b}[0] = ({v}) ? 1 : 0; {b}; }})"))
            }
            // The integer / boolean arm of a union.
            (Ty::Int | Ty::Bool, Shape::Union(arms)) if scalar_arm(&arms, e.ty).is_some() => {
                let (k, lo, hi) = scalar_arm(&arms, e.ty).expect("arm");
                let v = self.expr(e)?;
                let n = self.words(sid);
                let b = self.buf(n);
                Ok(format!("({{ int64_t v_ = {v}; if (v_ < {lo}LL || v_ > {hi}LL) return TLX_ERR; memset({b}, 0, {n} * 8); {b}[0] = {k}; {b}[1] = (uint64_t)(v_ - ({lo}LL)); {b}; }})"))
            }
            // The host encodes it.
            _ if self.mixing => self.region_at(&Expr::new(Ty::Enc(sid), ExprKind::Convert(e.clone())), crate::native_plan::site(e, true)),
            (t, s) => no(format!("representation change {t:?} -> {s:?}")),
        }
    }

    /// C code of `e` without making `e` itself a region (its children may
    /// be: `expr`).
    pub(super) fn expr_native(&mut self, e: &Expr) -> R<String> {
        if self.mixing && e.has_boxed_operand() {
            return no("boxed operand");
        }
        if let (true, Ty::Enc(sid)) = (crate::inplace::is_update(e), e.ty) {
            // Copy the base once and update it in place.
            let p = crate::inplace::plan(e, self.ty);
            if !p.is_copy() {
                let snap = self.snapshot();
                let buf = self.buf(self.words(sid));
                let d = format!("d{}", self.fresh());
                let mut code = String::new();
                match self.plan_into(&p, &d, 3, &mut code) {
                    Ok(()) => return Ok(format!("({{ uint64_t *{d} = {buf};\n{code}      (const uint64_t *){d}; }})")),
                    Err(_) => self.rollback(snap),
                }
            }
        }
        Ok(match &*e.kind {
            ExprKind::Const(v) => match (e.ty, v) {
                (Ty::Bool, tlx_value::Value::Bool(b)) => (if *b { "1" } else { "0" }).to_string(),
                (Ty::Int, tlx_value::Value::Int(i)) => format!("({i}LL)"),
                (Ty::Enc(sid), v) => {
                    let mut w = vec![0u64; self.words(sid)];
                    layout::encode(self.ty.shape(sid), v, &mut w).map_err(|_| Unsupported("constant outside its shape".into()))?;
                    self.static_words(&w)
                }
                _ => return no("boxed constant"),
            },
            ExprKind::ConstWords(w) => self.static_words(w),
            ExprKind::ConstElems { .. } | ExprKind::IntRange(..) | ExprKind::Subsets(_) | ExprKind::OrderedSet { .. } => {
                return no("iteration source outside iteration")
            }
            ExprKind::Call { func, args } => {
                if !self.fn_native.get(*func as usize).copied().unwrap_or(false) {
                    return no("call of a function that is not native");
                }
                // The outermost call starts the count of budgeted calls.
                let (depth, calls, start) = if self.in_fn { ("depth + 1", "calls", "") } else { ("1", "&calls_", "uint64_t calls_ = 0; ") };
                let mut parts = vec!["s0".to_string(), "s1".to_string(), depth.to_string(), calls.to_string()];
                for a in args {
                    self.c_ty(a.ty)?;
                    parts.push(self.expr(a)?);
                }
                match e.ty {
                    Ty::Bool | Ty::Int => {
                        format!("({{ {start}int64_t r_; if (fn_{func}({}, &r_)) return TLX_ERR; r_; }})", parts.join(", "))
                    }
                    Ty::Enc(sid) => {
                        let b = self.buf(self.words(sid));
                        format!("({{ {start}if (fn_{func}({}, {b})) return TLX_ERR; (const uint64_t *){b}; }})", parts.join(", "))
                    }
                    Ty::Val => return no("boxed call"),
                }
            }
            ExprKind::Fail(_) => {
                let zero = match e.ty {
                    Ty::Bool | Ty::Int => "0",
                    Ty::Enc(_) => "(const uint64_t *)0",
                    Ty::Val if self.mixing => "(uint64_t)0",
                    Ty::Val => return no("boxed failure"),
                };
                format!("({{ return TLX_ERR; {zero}; }})")
            }
            ExprKind::Var(i) => {
                let Ty::Enc(_) = e.ty else { return no("boxed variable read") };
                format!("(s0 + {})", self.ty.var_offset(*i as usize))
            }
            ExprKind::NextVar(i) => {
                let Ty::Enc(_) = e.ty else { return no("boxed variable read") };
                format!("(s1 + {})", self.ty.var_offset(*i as usize))
            }
            ExprKind::Temp(t) => {
                self.c_ty(self.temps[*t as usize])?;
                temp(*t)
            }
            ExprKind::Not(x) => format!("(!{})", self.bool_expr(x)?),
            ExprKind::And(xs) => {
                let parts = xs.iter().map(|x| self.bool_expr(x)).collect::<R<Vec<_>>>()?;
                if parts.is_empty() {
                    "1".into()
                } else {
                    format!("({})", parts.join(" && "))
                }
            }
            ExprKind::Or(xs) => {
                let parts = xs.iter().map(|x| self.bool_expr(x)).collect::<R<Vec<_>>>()?;
                if parts.is_empty() {
                    "0".into()
                } else {
                    format!("({})", parts.join(" || "))
                }
            }
            ExprKind::If(c, t, f) => {
                if t.ty != f.ty {
                    return no("conditional with mixed representations");
                }
                self.c_ty(t.ty)?;
                format!("({} ? {} : {})", self.bool_expr(c)?, self.expr(t)?, self.expr(f)?)
            }
            ExprKind::IntBin(op, a, b) => {
                let (a, b) = (self.int_expr(a)?, self.int_expr(b)?);
                let f = match op {
                    IntOp::Add => "tlx_add",
                    IntOp::Sub => "tlx_sub",
                    IntOp::Mul => "tlx_mul",
                    IntOp::DivFloor => "tlx_divf",
                    IntOp::DivNat => "tlx_divn",
                    IntOp::Pow => "tlx_pow",
                    IntOp::Gcd => "tlx_gcd",
                    IntOp::Mod => "tlx_mod",
                };
                format!("({{ int64_t r_; if (!{f}({a}, {b}, &r_)) return TLX_ERR; r_; }})")
            }
            ExprKind::IntCmp(op, a, b) => {
                let o = match op {
                    CmpOp::Lt => "<",
                    CmpOp::Le => "<=",
                    CmpOp::Gt => ">",
                    CmpOp::Ge => ">=",
                };
                format!("({} {o} {})", self.int_expr(a)?, self.int_expr(b)?)
            }
            ExprKind::Neg(a) => {
                let a = self.int_expr(a)?;
                format!("({{ int64_t r_; if (!tlx_sub(0, {a}, &r_)) return TLX_ERR; r_; }})")
            }
            ExprKind::Eq(a, b) => match (a.ty, b.ty) {
                (Ty::Enc(x), Ty::Enc(y)) if x == y => {
                    let n = self.words(x);
                    format!("(memcmp({}, {}, {n} * 8) == 0)", self.expr(a)?, self.expr(b)?)
                }
                (Ty::Int, Ty::Int) | (Ty::Bool, Ty::Bool) => format!("({} == {})", self.expr(a)?, self.expr(b)?),
                _ => return no("boxed equality"),
            },
            ExprKind::Convert(x) => match (x.ty, e.ty) {
                (Ty::Enc(sid), Ty::Int) => match self.ty.shape(sid) {
                    Shape::Int { lo, .. } => format!("((int64_t)({})[0] + ({lo}LL))", self.expr(x)?),
                    _ => return no("conversion to integer"),
                },
                (Ty::Enc(sid), Ty::Bool) => match self.ty.shape(sid) {
                    Shape::Bool => format!("(({})[0] != 0)", self.expr(x)?),
                    _ => return no("conversion to boolean"),
                },
                (_, Ty::Enc(sid)) => self.encoded(x, sid)?,
                (f, t) => {
                    let shape = match f {
                        Ty::Enc(s) => Some(self.ty.shape(s)),
                        _ => None,
                    };
                    let what: String = format!("{:?}", x.kind).chars().take(300).collect();
                    return no(format!("conversion {f:?} -> {t:?} ({shape:?}) of {what}"));
                }
            },
            ExprKind::Enabled(s) => {
                // Regions inside see the current state (none in Init).
                if self.mixing && self.rctx == RegionCtx::Init {
                    return no("ENABLED in Init");
                }
                // The action over a scratch next state (shadowing `s1`).
                let n = self.fresh();
                let (flag, label) = (format!("en{n}"), format!("en{n}_done"));
                let saved = self.enabled.replace((flag.clone(), label.clone()));
                let assigned = std::mem::replace(&mut self.assigned, vec![false; self.ty.layout.vars.len()]);
                let mut body = String::new();
                let r = self.stmt(s, 2, &mut body);
                self.enabled = saved;
                self.assigned = assigned;
                r?;
                let words = self.ty.layout.words.max(1);
                format!("({{ int64_t {flag} = 0; {{ uint64_t s1[{words}]; memset(s1, 0, sizeof s1);\n{body} }} {label}: ; {flag}; }})")
            }
            ExprKind::Exists { bind, set, body } | ExprKind::Forall { bind, set, body } => {
                let want = matches!(&*e.kind, ExprKind::Exists { .. });
                let h0 = self.loop_start(set)?;
                let r = format!("q{}", self.fresh());
                let b = self.bool_expr(body)?;
                let inner = format!("      if (({b}) == {}) {{ {r} = {}; goto {r}_done; }}\n", want as i32, want as i32);
                let lp = self.foreach(*bind, set, &inner, 3, h0, None, Some(body).filter(|_| want))?;
                format!("({{ int64_t {r} = {}; {{\n{lp} }} {r}_done: ; {r}; }})", !want as i32)
            }
            ExprKind::Choose { bind, set, body } if matches!(e.ty, Ty::Int | Ty::Bool) => {
                // An unboxed element (e.g. CHOOSE i \in lo..hi : P).
                let h0 = self.loop_start(set)?;
                let r = format!("q{}", self.fresh());
                let b = self.bool_expr(body)?;
                let inner = format!("      if ({b}) {{ {r}_v = {}; {r} = 1; goto {r}_done; }}\n", temp(*bind));
                let lp = self.foreach(*bind, set, &inner, 3, h0, None, Some(body))?;
                format!("({{ int {r} = 0; int64_t {r}_v = 0; {{\n{lp} }} {r}_done: ; if (!{r}) return TLX_ERR; {r}_v; }})")
            }
            ExprKind::Choose { bind, set, body } => {
                let (en, out) = self.result_buf(e.ty, "boxed CHOOSE")?;
                let h0 = self.loop_start(set)?;
                let r = format!("q{}", self.fresh());
                let b = self.bool_expr(body)?;
                // Copy the element out of the loop-scoped storage.
                let inner = format!("      if ({b}) {{ memcpy({out}, {}, {en} * 8); {r} = 1; goto {r}_done; }}\n", temp(*bind));
                let lp = self.foreach(*bind, set, &inner, 3, h0, None, Some(body))?;
                format!("({{ int {r} = 0; {{\n{lp} }} {r}_done: ; if (!{r}) return TLX_ERR; (const uint64_t *){out}; }})")
            }
            ExprKind::Let { temp: t, value, body } => {
                let ct = self.c_ty(value.ty)?;
                let v = self.expr(value)?;
                let b = self.expr(body)?;
                format!("({{ {ct} {} = {v}; {b}; }})", temp(*t))
            }
            // ---- encoded values (`encoded.rs`)
            ExprKind::Slice { .. }
            | ExprKind::Index { .. }
            | ExprKind::ExceptAt { .. }
            | ExprKind::ExceptIndex { .. }
            | ExprKind::BitMember { .. }
            | ExprKind::BitSetOp { .. }
            | ExprKind::BitCard { .. }
            | ExprKind::Rank { .. }
            | ExprKind::Concat { .. }
            | ExprKind::Pack { .. }
            | ExprKind::BitSet { .. }
            | ExprKind::SeqLen { .. }
            | ExprKind::UnionField { .. }
            | ExprKind::UnionFieldInt { .. }
            | ExprKind::Filter { .. }
            | ExprKind::MapGet { .. }
            | ExprKind::MapPut { .. }
            | ExprKind::MapBuild { .. }
            | ExprKind::MapMerge { .. }
            | ExprKind::SortedMember { .. }
            | ExprKind::Recode { .. }
            | ExprKind::RankUnion { .. }
            | ExprKind::Lookup { .. }
            | ExprKind::RankFlat { .. }
            | ExprKind::MapSet { .. }
            | ExprKind::Fold { .. }
            | ExprKind::UnionFold { .. }
            | ExprKind::Collect { .. }
            | ExprKind::SortedInsert { .. }
            | ExprKind::SeqIndex { .. }
            | ExprKind::SeqTail { .. }
            | ExprKind::SeqSub { .. }
            | ExprKind::SortedOp { .. }
            | ExprKind::SeqFilter { .. }
            | ExprKind::SeqConcat { .. }
            | ExprKind::SeqAppend { .. } => return self.expr_encoded(e),
            ExprKind::Apply(..) | ExprKind::ValField(..) | ExprKind::Tuple(_) | ExprKind::ValOp { .. } | ExprKind::Interp { .. } => {
                return no("boxed operation")
            }
            ExprKind::RefOp { op, args } => return self.ref_op(e, op, args),
            ExprKind::RefElems(_) => return no("iteration source used as a value"),
        })
    }

    /// A fresh buffer for the result of an expression of type `ty`, which
    /// must be encoded (else unsupported: `what`), and its size in words.
    fn result_buf(&mut self, ty: Ty, what: &str) -> R<(usize, String)> {
        let Ty::Enc(sid) = ty else { return no(what) };
        let n = self.words(sid);
        Ok((n, self.buf(n)))
    }

    /// Size of the element universe of the bitset shape of `ty` (ranks
    /// beyond it would set padding bits, breaking canonicity).
    fn universe(&self, ty: Ty) -> R<u64> {
        let Ty::Enc(sid) = ty else { return no("boxed set") };
        match self.ty.shape(sid) {
            Shape::Set { elem, .. } => bitset_universe(elem).ok_or(Unsupported("not a bitset".into())),
            _ => no("not a set shape"),
        }
    }

    /// The encoding of the map shape of `ty`.
    fn map_dims(&self, ty: Ty) -> R<MapDims> {
        let Ty::Enc(sid) = ty else { return no("boxed map") };
        crate::types::map_dims(self.ty.shape(sid)).ok_or(Unsupported("not a map shape".into()))
    }

    /// Slot index of a function argument (out of domain = runtime error).
    fn slot(&mut self, arg: &Expr, map: &IndexMap) -> R<String> {
        self.slot_or(arg, map, "")
    }

    /// Like `slot`, but yields `fallback` (if non-empty) instead of erroring.
    pub(super) fn slot_or(&mut self, arg: &Expr, map: &IndexMap, fallback: &str) -> R<String> {
        let miss = if fallback.is_empty() { "return TLX_ERR;".to_string() } else { format!("a_ = {fallback};") };
        match map {
            IndexMap::IntRange { lo, n } => {
                let a = self.int_expr(arg)?;
                Ok(format!("({{ int64_t a_ = {a} - ({lo}LL); if (a_ < 0 || a_ >= {n}) {{ {miss} }} a_; }})"))
            }
            IndexMap::Table(t) => {
                let Ty::Enc(_) = arg.ty else { return no("boxed function argument") };
                let tbl = format!("tbl{}", self.fresh_static());
                let items: Vec<String> = t.iter().map(|x| x.to_string()).collect();
                self.static_array(&tbl, "int32_t", &items, "-1");
                let a = self.expr(arg)?;
                Ok(format!("({{ uint64_t i_ = ({a})[0]; int64_t a_ = i_ < {} ? {tbl}[i_] : -1; if (a_ < 0) {{ {miss} }} a_; }})", t.len()))
            }
        }
    }
}
