//! Value store operations (`ExprKind::RefOp`) in the closure executor:
//! the arguments are evaluated in order, then `exec::refops::run` computes
//! the result (the same function the native code calls).

use tlx_eval::EvalError;
use tlx_layout::scalar;
use tlx_layout::store::StoreRef;

use super::{Code, Compiler, Fx, LocF, C, IS, R};
use crate::exec::refops::{self, RArg};
use crate::ir::*;

/// How one argument is read.
enum A {
    W(LocF),
    I(IS),
    B(super::BoolF),
    E(LocF, usize),
}

impl A {
    #[inline]
    fn get(&self, fx: &mut Fx) -> R<Arg> {
        Ok(match self {
            A::W(l) => {
                let at = l.at(fx)?;
                Arg::W(fx.word(at, 0))
            }
            A::I(i) => Arg::W(i.get(fx)? as u64),
            A::B(b) => Arg::W(b(fx)? as u64),
            A::E(l, n) => {
                let at = l.at(fx)?;
                Arg::E(fx.get(at, *n).to_vec())
            }
        })
    }
}

/// An evaluated argument (an encoding is copied: evaluating the next
/// argument may reuse its frame slot).
enum Arg {
    W(u64),
    E(Vec<u64>),
}

impl Arg {
    fn word_i(&self) -> R<i64> {
        match self {
            Arg::W(w) => Ok(*w as i64),
            Arg::E(_) => Err(EvalError::new("dynamic scalar operation requires a scalar argument")),
        }
    }
}

fn store_err(e: tlx_layout::store::RefOpError) -> EvalError {
    EvalError::new(match e {
        tlx_layout::store::RefOpError::Eval => "value store operation failed (the interpreter decides)",
        tlx_layout::store::RefOpError::Full => "the value store is full",
    })
}

impl Compiler<'_> {
    pub(super) fn ref_op(&mut self, op: &RefOp, args: &[Expr], ty: Ty) -> C<Code> {
        if matches!(op, RefOp::DynEqInt | RefOp::DynEqBool | RefOp::DynToInt | RefOp::DynToBool) {
            let mut srcs = Vec::with_capacity(args.len());
            for a in args {
                srcs.push(match a.ty {
                    Ty::Int => A::I(self.int_src(a)?),
                    Ty::Bool => A::B(self.bool_(a)?),
                    Ty::Enc(sid) if matches!(self.t.shape(sid), tlx_layout::Shape::Dyn) => A::W(self.enc(a)?.0),
                    _ => return Err("dynamic scalar operation requires a dynamic encoding".into()),
                });
            }
            let op = op.clone();
            let eval = move |fx: &mut Fx| -> R<u64> {
                let vals: Vec<Arg> = srcs.iter().map(|s| s.get(fx)).collect::<R<_>>()?;
                let h = match vals[0] {
                    Arg::W(h) => h,
                    Arg::E(_) => return Err(EvalError::new("dynamic scalar operation requires one word")),
                };
                let tag = scalar::tag(h);
                match op {
                    RefOp::DynEqInt if tag == scalar::TAG_INT => {
                        Ok((scalar::as_int(h).ok_or_else(|| EvalError::new("invalid integer scalar"))? == vals[1].word_i()?) as u64)
                    }
                    RefOp::DynEqBool if tag == scalar::TAG_BOOL => {
                        let want = vals[1].word_i()? != 0;
                        Ok((scalar::as_bool(h).ok_or_else(|| EvalError::new("invalid Boolean scalar"))? == want) as u64)
                    }
                    RefOp::DynToInt => Ok(scalar::as_int(h).ok_or_else(|| EvalError::new("expected integer scalar"))? as u64),
                    RefOp::DynToBool => Ok(scalar::as_bool(h).ok_or_else(|| EvalError::new("expected Boolean scalar"))? as u64),
                    _ => Err(EvalError::new("incomparable dynamic scalar")),
                }
            };
            return Ok(match ty {
                Ty::Int => Code::I(Box::new(move |fx| Ok(eval(fx)? as i64))),
                Ty::Bool => Code::B(Box::new(move |fx| Ok(eval(fx)? != 0))),
                _ => return Err("invalid dynamic scalar result type".into()),
            });
        }
        let store = self.t.ref_store().ok_or("value store operation without a store")?;
        let mut srcs = Vec::with_capacity(args.len());
        for a in args {
            srcs.push(match a.ty {
                Ty::Int => A::I(self.int_src(a)?),
                Ty::Bool => A::B(self.bool_(a)?),
                Ty::Enc(sid) if Some(sid) == self.t.ref_sid() => A::W(self.enc(a)?.0),
                Ty::Enc(_) => {
                    let (l, n) = self.enc(a)?;
                    A::E(l, n)
                }
                Ty::Val => return Err("boxed argument of a value store operation".into()),
            });
        }
        let op = op.clone();
        let eval = move |fx: &mut Fx, out: &mut [u64]| -> R<()> {
            let mut vals = Vec::with_capacity(srcs.len());
            for s in &srcs {
                vals.push(s.get(fx)?);
            }
            let rargs: Vec<RArg> = vals
                .iter()
                .map(|v| match v {
                    Arg::W(x) => RArg::W(*x),
                    Arg::E(w) => RArg::E(w),
                })
                .collect();
            refops::count(false);
            refops::run(&store, fx.typing(), &op, &rargs, out).map_err(store_err)
        };
        Ok(match ty {
            Ty::Int => Code::I(Box::new(move |fx| {
                let mut out = [0u64; 1];
                eval(fx, &mut out)?;
                Ok(out[0] as i64)
            })),
            Ty::Bool => Code::B(Box::new(move |fx| {
                let mut out = [0u64; 1];
                eval(fx, &mut out)?;
                Ok(out[0] != 0)
            })),
            Ty::Enc(sid) => {
                let n = self.t.words(sid) as usize;
                let out = self.alloc(n);
                self.fresh(
                    Box::new(move |fx| {
                        let mut buf = vec![0u64; n];
                        eval(fx, &mut buf)?;
                        fx.fr.w[out..out + n].copy_from_slice(&buf);
                        Ok(super::super::Loc::frame(out))
                    }),
                    n,
                    out,
                )
            }
            Ty::Val => return Err("boxed value store operation".into()),
        })
    }
}

/// The store of a `RefElems` source.
pub(crate) fn elems_store(c: &Compiler<'_>) -> C<StoreRef> {
    c.t.ref_store().ok_or_else(|| "value store iteration without a store".to_string())
}
