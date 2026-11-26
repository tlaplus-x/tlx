//! Operation-family builders of the closure compiler: equality, representation conversion, quantifiers, CHOOSE, calls of compiled functions, set filters and maps.

use tlx_eval::EvalError;
use tlx_layout::Shape;
use tlx_value::{order, Value};

use super::super::super::words;
use super::super::{copy_words, move_words, BoolF, Code, Fx, Loc, R};
use super::*;
use crate::ir::*;

impl<'c> Compiler<'c> {
    pub(super) fn eq(&mut self, a: &Expr, b: &Expr) -> C<BoolF> {
        Ok(match (a.ty, b.ty) {
            (Ty::Enc(x), Ty::Enc(y)) if x == y => {
                let (a, n) = self.enc(a)?;
                let (wa, ka) = (self.word_at(0), self.known_loc());
                let (b, _) = self.enc(b)?;
                let (wb, kb) = (self.word_at(0), self.known_loc());
                match (n, wa, wb, ka, kb) {
                    (1, Some(wa), Some(wb), ..) => Box::new(move |fx| Ok(wa.get(fx) == wb.get(fx))),
                    (1, Some(wa), None, ..) => Box::new(move |fx| {
                        let lb = b.at(fx)?;
                        Ok(fx.word(lb, 0) == wa.get(fx))
                    }),
                    (1, None, Some(wb), ..) => Box::new(move |fx| {
                        let la = a.at(fx)?;
                        Ok(fx.word(la, 0) == wb.get(fx))
                    }),
                    (_, _, _, Some(la), Some(lb)) => Box::new(move |fx| Ok(fx.get(la, n) == fx.get(lb, n))),
                    (_, _, _, None, Some(lb)) => Box::new(move |fx| {
                        let la = a.at(fx)?;
                        Ok(fx.get(la, n) == fx.get(lb, n))
                    }),
                    _ => Box::new(move |fx| {
                        let la = a.at(fx)?;
                        let lb = b.at(fx)?;
                        Ok(fx.get(la, n) == fx.get(lb, n))
                    }),
                }
            }
            (Ty::Int, Ty::Int) => {
                let (a, b) = (self.int_src(a)?, self.int_src(b)?);
                Box::new(move |fx| {
                    let x = a.get(fx)?;
                    Ok(x == b.get(fx)?)
                })
            }
            _ => match (self.expr(a)?, self.expr(b)?) {
                (Code::I(a), Code::I(b)) => Box::new(move |fx| {
                    let x = a(fx)?;
                    Ok(x == b(fx)?)
                }),
                (Code::B(a), Code::B(b)) => Box::new(move |fx| {
                    let x = a(fx)?;
                    Ok(x == b(fx)?)
                }),
                (ca, cb) => {
                    let (va, vb) = (self.to_val(ca, a.ty), self.to_val(cb, b.ty));
                    Box::new(move |fx| {
                        let x = va(fx)?;
                        let y = vb(fx)?;
                        Ok(order::eq_tlc(&x, &y)?)
                    })
                }
            },
        })
    }

    /// `x` converted to representation `to`.
    pub(super) fn convert(&mut self, x: &Expr, to: Ty) -> C<Code> {
        let from = x.ty;
        Ok(match to {
            Ty::Val => Code::V(self.val(x)?),
            Ty::Bool => match from {
                Ty::Enc(sid) if Some(sid) == self.t.ref_sid() => {
                    let (f, _) = self.enc(x)?;
                    Code::B(Box::new(move |fx| {
                        let l = f.at(fx)?;
                        tlx_layout::store::as_bool(fx.word(l, 0))
                            .ok_or_else(|| EvalError::new("A non-boolean value was used as a boolean."))
                    }))
                }
                Ty::Enc(sid) if matches!(self.t.shape(sid), Shape::Bool) => {
                    let (f, _) = self.enc(x)?;
                    if let Some(w) = self.word_at(0) {
                        return Ok(Code::B(Box::new(move |fx| Ok(w.get(fx) != 0))));
                    }
                    Code::B(Box::new(move |fx| {
                        let l = f.at(fx)?;
                        Ok(fx.word(l, 0) != 0)
                    }))
                }
                _ => Code::B(self.bool_(x)?),
            },
            Ty::Int => match from {
                Ty::Enc(sid) if Some(sid) == self.t.ref_sid() => {
                    let (f, _) = self.enc(x)?;
                    Code::I(Box::new(move |fx| {
                        let l = f.at(fx)?;
                        tlx_layout::store::as_int(fx.word(l, 0))
                            .ok_or_else(|| EvalError::new("A non-integer value was used as an integer."))
                    }))
                }
                Ty::Enc(sid) if matches!(self.t.shape(sid), Shape::Int { .. }) => {
                    let Shape::Int { lo, .. } = self.t.shape(sid) else { unreachable!() };
                    let lo = *lo;
                    let (f, _) = self.enc(x)?;
                    match self.word_at(0) {
                        Some(W1::K(c)) => return Ok(self.int_at(IntAt::K(lo + c as i64))),
                        Some(w) => return Ok(self.int_at(IntAt::W(w, lo))),
                        None => {}
                    }
                    Code::I(Box::new(move |fx| {
                        let l = f.at(fx)?;
                        Ok(lo + fx.word(l, 0) as i64)
                    }))
                }
                _ => Code::I(self.int_(x)?),
            },
            Ty::Enc(sid) => {
                let t = self.t;
                let n = t.words(sid) as usize;
                let out = self.alloc(n);
                let shape = t.shape(sid).clone();
                match self.expr(x)? {
                    Code::I(f) => self.fresh(
                        Box::new(move |fx| {
                            let i = f(fx)?;
                            match &shape {
                                Shape::Int { lo, hi } if i >= *lo && i <= *hi => fx.fr.w[out] = (i - lo) as u64,
                                _ => encode_into(fx, &Value::Int(i), sid, out, n)?,
                            }
                            Ok(Loc::frame(out))
                        }),
                        n,
                        out,
                    ),
                    Code::B(f) => self.fresh(
                        Box::new(move |fx| {
                            let b = f(fx)?;
                            match &shape {
                                Shape::Bool => fx.fr.w[out] = b as u64,
                                _ => encode_into(fx, &Value::Bool(b), sid, out, n)?,
                            }
                            Ok(Loc::frame(out))
                        }),
                        n,
                        out,
                    ),
                    code => {
                        // (An encoding of another shape is decoded first.)
                        let v = self.to_val(code, from);
                        self.fresh(
                            Box::new(move |fx| {
                                let v = v(fx)?.normalize()?;
                                encode_into(fx, &v, sid, out, n)?;
                                Ok(Loc::frame(out))
                            }),
                            n,
                            out,
                        )
                    }
                }
            }
        })
    }

    /// `\E` (`want` = true) or `\A` (`want` = false).
    pub(super) fn quantifier(&mut self, want: bool, bind: Temp, set: &Expr, body: &Expr) -> C<BoolF> {
        let src = self.src_how(set, super::super::stmt::ValIter::Bound)?;
        let bind = self.slots[bind as usize];
        let body = self.bool_(body)?;
        Ok(Box::new(move |fx| {
            let mut found = !want;
            src.run(fx, bind, &mut |fx| {
                if body(fx)? == want {
                    found = want;
                    return Ok(false);
                }
                Ok(true)
            })?;
            Ok(found)
        }))
    }

    /// `CHOOSE bind \in set : body` (TLC order: normalized for boxed sets).
    pub(super) fn choose(&mut self, ty: Ty, bind: Temp, set: &Expr, body: &Expr) -> C<Code> {
        let src = self.src(set, true)?;
        let slot = self.slots[bind as usize];
        let body = self.bool_(body)?;
        let found = move |fx: &mut Fx| -> R<()> {
            let mut hit = false;
            src.run(fx, slot, &mut |fx| {
                if body(fx)? {
                    hit = true;
                    return Ok(false);
                }
                Ok(true)
            })?;
            if hit {
                Ok(())
            } else {
                err(CHOOSE_NONE)
            }
        };
        // The chosen element is the binding's value.
        let read = self.temp(bind, ty)?;
        // (The CHOOSE must run before the binding is read: its value has
        // no known place.)
        self.mark = None;
        Ok(match read {
            Code::B(r) => Code::B(Box::new(move |fx| {
                found(fx)?;
                r(fx)
            })),
            Code::I(r) => Code::I(Box::new(move |fx| {
                found(fx)?;
                r(fx)
            })),
            Code::E(r, n) => Code::E(
                Box::new(move |fx| {
                    found(fx)?;
                    r(fx)
                }),
                n,
            ),
            Code::V(r) => Code::V(Box::new(move |fx| {
                found(fx)?;
                r(fx)
            })),
        })
    }

    /// Call of compiled function `func`.
    pub(super) fn call(&mut self, ty: Ty, func: u32, args: &[Expr]) -> C<Code> {
        let t = self.t;
        let def = &t.funcs[func as usize];
        match &mut self.callees {
            Some(cs) => cs.push(func),
            None => {
                if self.funcs.get(func as usize).is_none_or(|f| f.is_none()) {
                    return Err(format!("call of uncompiled function {}", def.name));
                }
            }
        }
        // Arguments are evaluated in the caller's frame, then copied into
        // the callee's.
        let mut params = Vec::new();
        for (p, a) in def.params.iter().zip(args) {
            let pty = def.temps[*p as usize];
            params.push(self.typed(a, pty)?);
        }
        let ret_n = match ty {
            Ty::Enc(_) => self.words(ty)?,
            _ => 0,
        };
        let out = self.alloc(ret_n);
        let k = func as usize;
        let run = move |fx: &mut Fx| -> R<Code1> {
            let funcs = fx.funcs;
            let f = funcs[k].as_ref().expect("checked at compile time");
            let mut fr = fx.pool.pop().unwrap_or_default();
            fr.fit(f.frame);
            for (code, slot) in params.iter().zip(&f.params) {
                if let Err(e) = store_into(fx, code, &mut fr, *slot) {
                    fx.pool.push(fr);
                    return Err(e);
                }
            }
            if tlx_base::stack::too_deep(fx.depth, super::super::super::eval::MAX_CALL_DEPTH) {
                fx.pool.push(fr);
                return err("compiled recursion too deep");
            }
            if fx.depth == 0 {
                fx.calls = 0;
            }
            if f.budgeted {
                fx.calls += 1;
                if fx.calls > super::super::super::eval::MAX_BUDGETED_CALLS {
                    fx.pool.push(fr);
                    return err("compiled recursive function: too many calls");
                }
            }
            std::mem::swap(&mut fx.fr, &mut fr);
            let consts = std::mem::replace(&mut fx.consts, &f.consts);
            fx.depth += 1;
            let r = match &f.body {
                Code::B(b) => b(fx).map(Code1::B),
                Code::I(b) => b(fx).map(Code1::I),
                Code::V(b) => b(fx).map(Code1::V),
                Code::E(b, n) => b(fx).map(|l| {
                    // Copy the result out of the callee's frame.
                    // (`fx.fr` is the callee's frame here, `fr` the caller's.)
                    copy_words(&mut fr.w[out..out + *n], fx.get(l, *n));
                    Code1::E
                }),
            };
            fx.depth -= 1;
            fx.consts = consts;
            std::mem::swap(&mut fx.fr, &mut fr);
            fx.pool.push(fr);
            r
        };
        Ok(match ty {
            Ty::Bool => Code::B(Box::new(move |fx| match run(fx)? {
                Code1::B(b) => Ok(b),
                Code1::V(Value::Bool(b)) => Ok(b),
                _ => err("A non-boolean expression was used as a boolean."),
            })),
            Ty::Int => Code::I(Box::new(move |fx| match run(fx)? {
                Code1::I(i) => Ok(i),
                Code1::V(Value::Int(i)) => Ok(i),
                _ => err("A non-integer expression was used as an integer."),
            })),
            Ty::Enc(_) => self.fresh(
                Box::new(move |fx| match run(fx)? {
                    Code1::E => Ok(Loc::frame(out)),
                    _ => err("internal: compiled function result representation"),
                }),
                ret_n,
                out,
            ),
            Ty::Val => Code::V(Box::new(move |fx| match run(fx)? {
                Code1::V(v) => Ok(v),
                Code1::B(b) => Ok(Value::Bool(b)),
                Code1::I(i) => Ok(Value::Int(i)),
                Code1::E => err("internal: compiled function result representation"),
            })),
        })
    }

    pub(super) fn filter(&mut self, ty: Ty, bind: Temp, set: &Expr, pred: &Expr) -> C<Code> {
        let n = self.words(ty)?;
        let Ty::Enc(sid) = ty else { unreachable!() };
        let t = self.t;
        let elem = t.node(sid).set_elem().ok_or("Filter of a non-set")?;
        let (s, _) = self.enc(set)?;
        let slot = self.slots[bind as usize];
        let pred = self.bool_(pred)?;
        let stage = self.alloc(n);
        let out = self.alloc(n);
        if elem.bitset_universe().is_some() {
            let el = super::super::stmt::BitElem::new(t, sid)?;
            let Slot::W(boff, bn) = slot else { return Err("Filter binding a non-encoded temp".into()) };
            return Ok(self.fresh(
                Box::new(move |fx| {
                    let l = s.at(fx)?;
                    fx.copy_to(l, stage, n);
                    fx.fr.w[out..out + n].fill(0);
                    for i in 0..n {
                        let mut b = fx.fr.w[stage + i];
                        while b != 0 {
                            let r = i * 64 + b.trailing_zeros() as usize;
                            b &= b - 1;
                            el.write(fx, r, boff, bn);
                            if pred(fx)? {
                                fx.fr.w[out + r / 64] |= 1 << (r % 64);
                            }
                        }
                    }
                    Ok(Loc::frame(out))
                }),
                n,
                out,
            ));
        }
        let k = elem.words();
        let Slot::W(boff, _) = slot else { return Err("Filter binding a non-encoded temp".into()) };
        Ok(self.fresh(
            Box::new(move |fx| {
                let l = s.at(fx)?;
                fx.copy_to(l, stage, n);
                fx.fr.w[out..out + n].fill(0);
                let mut len = 0usize;
                for i in 0..fx.fr.w[stage] as usize {
                    let at = stage + 1 + i * k;
                    move_words(&mut fx.fr.w, at, k, boff);
                    if pred(fx)? {
                        move_words(&mut fx.fr.w, at, k, out + 1 + len * k);
                        len += 1;
                    }
                }
                fx.fr.w[out] = len as u64;
                Ok(Loc::frame(out))
            }),
            n,
            out,
        ))
    }

    pub(super) fn map_set(&mut self, ty: Ty, bind: Temp, set: &Expr, elem: &Expr, cond: Option<&Expr>) -> C<Code> {
        let n = self.words(ty)?;
        let Ty::Enc(sid) = ty else { unreachable!() };
        let t = self.t;
        let Shape::Set { max_card, .. } = t.shape(sid) else { return Err("MapSet into a non-set".into()) };
        let max_card = *max_card;
        let es = t.node(sid).set_elem().ok_or("MapSet into a non-set")?;
        let src = self.src(set, false)?;
        let slot = self.slots[bind as usize];
        let cond = cond.map(|c| self.bool_(c)).transpose()?;
        if let Some(u) = es.bitset_universe() {
            let x = self.int_(elem)?;
            let out = self.alloc(n);
            return Ok(self.fresh(
                Box::new(move |fx| {
                    fx.fr.w[out..out + n].fill(0);
                    src.run(fx, slot, &mut |fx| {
                        if let Some(c) = &cond {
                            if !c(fx)? {
                                return Ok(true);
                            }
                        }
                        let r = x(fx)?;
                        if r < 0 || r as u64 >= u {
                            return err("set element outside the layout universe");
                        }
                        words::bit_set(&mut fx.fr.w[out..out + n], r as usize);
                        Ok(true)
                    })?;
                    Ok(Loc::frame(out))
                }),
                n,
                out,
            ));
        }
        let k = es.words();
        let (x, _) = self.enc(elem)?;
        // (The staged element must precede the output: see `split_at_mut`.)
        let xstage = self.alloc(k);
        let out = self.alloc(n);
        Ok(self.fresh(
            Box::new(move |fx| {
                fx.fr.w[out..out + n].fill(0);
                // Insert as we go (distinct, sorted); more distinct elements
                // than `max_card` is an error, as after sorting.
                src.run(fx, slot, &mut |fx| {
                    if let Some(c) = &cond {
                        if !c(fx)? {
                            return Ok(true);
                        }
                    }
                    let l = x.at(fx)?;
                    fx.copy_to(l, xstage, k);
                    let (lo, hi) = fx.fr.w.split_at_mut(out);
                    if !crate::exec::encops::sorted_add(&mut hi[..n], &lo[xstage..xstage + k], k, max_card as u64) {
                        return err(SET_TOO_LARGE);
                    }
                    Ok(true)
                })?;
                Ok(Loc::frame(out))
            }),
            n,
            out,
        ))
    }
}

/// A compiled function's result (`E`: copied into the caller's slot).
enum Code1 {
    B(bool),
    I(i64),
    E,
    V(Value),
}

/// Evaluate `code` (in `fx`'s frame) into `slot` of frame `fr`.
fn store_into(fx: &mut Fx, code: &Code, fr: &mut super::super::Frame, slot: Slot) -> R<()> {
    match (code, slot) {
        (Code::B(f), Slot::I(i)) => fr.iv[i] = f(fx)? as i64,
        (Code::I(f), Slot::I(i)) => fr.iv[i] = f(fx)?,
        (Code::V(f), Slot::I(i)) => {
            fr.iv[i] = match f(fx)? {
                Value::Bool(b) => b as i64,
                Value::Int(x) => x,
                other => return Err(EvalError::new(format!("internal: boxed value {other} in a scalar parameter"))),
            }
        }
        (Code::V(f), Slot::V(i)) => fr.vv[i] = Some(f(fx)?),
        (Code::B(f), Slot::V(i)) => fr.vv[i] = Some(Value::Bool(f(fx)?)),
        (Code::I(f), Slot::V(i)) => fr.vv[i] = Some(Value::Int(f(fx)?)),
        (Code::E(f, n), Slot::W(off, m)) if *n == m => {
            let l = f(fx)?;
            copy_words(&mut fr.w[off..off + m], fx.get(l, m));
        }
        _ => return err("internal: parameter representation mismatch"),
    }
    Ok(())
}

/// Encode `v` into shape `sid` at frame offset `out` (a layout miss is an
/// error: the caller falls back).
fn encode_into(fx: &mut Fx, v: &Value, sid: ShapeId, out: usize, n: usize) -> R<()> {
    let t = fx.typing();
    let w = &mut fx.fr.w[out..out + n];
    w.fill(0);
    t.node(sid).encode(v, w).map_err(|m| EvalError::new(format!("layout miss at {}", m.path)))
}
