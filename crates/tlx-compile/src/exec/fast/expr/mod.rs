//! Compilation of IR expressions into closures.

mod encoded;
mod family;
mod interp;
mod maps;
mod refs;
mod sequences;
mod sets;

pub(crate) use self::refs::elems_store as refs_store;

use std::sync::Arc;

use tlx_eval::EvalError;
use tlx_layout::layout::MapDims;
use tlx_layout::Shape;
use tlx_value::{arith, ops, Value};

use self::interp::{InterpBind, InterpNode};
use super::{BoolF, Code, EncF, FnProg, FrameSize, Fx, IntF, Loc, NotCovered, ValF, R};
use crate::ir::encoding::{rank_with, RecodeTable, UnionArms};
use crate::ir::*;
use crate::types::Typing;

const CHOOSE_NONE: &str = "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.";
const NO_FIELD: &str = "Attempted to access a field that the record does not have.";
pub(super) const SET_TOO_LARGE: &str = "set larger than the layout allows";
const NOT_IN_DOMAIN: &str = "Attempted to apply a function to an argument not in its domain.";
const SEQ_TOO_LONG: &str = "sequence longer than the layout allows";

pub(crate) type C<T> = Result<T, NotCovered>;

fn err<T>(msg: &str) -> R<T> {
    Err(EvalError::new(msg.to_string()))
}

/// Where a temp lives in the frame.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Slot {
    /// `iv[i]` (booleans as 0/1, integers).
    I(usize),
    /// `w[off..off + n]`.
    W(usize, usize),
    /// `vv[i]`.
    V(usize),
    /// An encoded temp bound by a `Let` to a value that stays where it was
    /// computed (read-only; see `Compiler::bind_let`).
    A(Loc, usize),
    /// An encoded temp bound by a `Let` to a value whose location is only
    /// known when it is computed: the location is kept in `iv[i]` (the
    /// value is copied to `w[off..off + n]` if it is in the next state).
    P(usize, usize, usize),
}

/// What the compiler knows about where an encoded expression's value is.
#[derive(Clone, Copy, Debug)]
pub(crate) enum Place {
    /// Nothing.
    Dyn,
    /// Always in this frame slot, which only the expression writes (it may
    /// be modified in place by its parent, or kept as a `Let` temp).
    Fresh(usize),
    /// Always at this location of the current state or the constant pool
    /// (not modified while the function runs).
    Fixed(Loc),
    /// Always at this frame offset (a temp, or a part of one), which holds
    /// it when the expression is evaluated.
    Temp(usize),
    /// An integer read without evaluating an expression.
    Int(IntAt),
}

/// Where an integer expression's value is (`Place::Int`).
#[derive(Clone, Copy, Debug)]
pub(crate) enum IntAt {
    /// A constant.
    K(i64),
    /// An integer temp (`iv[i]`).
    T(usize),
    /// An encoded integer (`lo` plus the word).
    W(W1, i64),
}

/// The location of an encoded operand: known, or computed.
pub(crate) enum LocF {
    K(Loc),
    F(EncF),
}

impl LocF {
    #[inline(always)]
    pub(crate) fn at(&self, fx: &mut Fx) -> R<Loc> {
        match self {
            LocF::K(l) => Ok(*l),
            LocF::F(f) => f(fx),
        }
    }
}

/// An integer operand: read in place, or computed.
pub(crate) enum IS {
    At(IntAt),
    F(IntF),
}

impl IS {
    #[inline(always)]
    pub(crate) fn get(&self, fx: &mut Fx) -> R<i64> {
        match self {
            IS::At(IntAt::K(c)) => Ok(*c),
            IS::At(IntAt::T(i)) => Ok(fx.fr.iv[*i]),
            IS::At(IntAt::W(w, lo)) => Ok(lo + w.get(fx) as i64),
            IS::F(f) => f(fx),
        }
    }
}

/// A word read without evaluating an expression (its place is known).
#[derive(Clone, Copy, Debug)]
pub(crate) enum W1 {
    /// A constant.
    K(u64),
    /// Of the current state.
    S0(usize),
    /// Of the frame.
    Fr(usize),
}

impl W1 {
    #[inline(always)]
    pub(crate) fn get(self, fx: &Fx) -> u64 {
        match self {
            W1::K(c) => c,
            W1::S0(o) => fx.s0[o],
            W1::Fr(o) => fx.fr.w[o],
        }
    }
}

pub(crate) struct Compiler<'c> {
    pub(super) t: &'c Typing,
    pub(super) slots: Vec<Slot>,
    pub(crate) scoped_state: bool,
    size: FrameSize,
    funcs: &'c [Option<FnProg>],
    /// Compiling a `FnDef`: calls are not checked yet (`compile_fn`), their
    /// targets are recorded.
    pub(super) callees: Option<Vec<u32>>,
    /// Encoded constants (`Loc::cnst`).
    consts: Vec<u64>,
    /// The `Place` of the expression being compiled, set by its node
    /// after its children are compiled (`fresh`, `fixed`).
    mark: Option<Place>,
    /// The `Place` of the expression compiled last (`expr`).
    pub(super) last: Place,
}

impl<'c> Compiler<'c> {
    pub(crate) fn new(t: &'c Typing, temps: &[Ty], funcs: &'c [Option<FnProg>]) -> Compiler<'c> {
        let mut c = Compiler {
            t,
            slots: Vec::with_capacity(temps.len()),
            scoped_state: false,
            size: FrameSize::default(),
            funcs,
            callees: None,
            consts: Vec::new(),
            mark: None,
            last: Place::Dyn,
        };
        for ty in temps {
            let s = match *ty {
                Ty::Bool | Ty::Int => {
                    c.size.ints += 1;
                    Slot::I(c.size.ints - 1)
                }
                Ty::Val => {
                    c.size.vals += 1;
                    Slot::V(c.size.vals - 1)
                }
                Ty::Enc(sid) => {
                    let n = t.words(sid) as usize;
                    Slot::W(c.alloc(n), n)
                }
            };
            c.slots.push(s);
        }
        c
    }

    pub(crate) fn frame_size(&self) -> FrameSize {
        self.size
    }

    pub(crate) fn take_consts(&mut self) -> Box<[u64]> {
        std::mem::take(&mut self.consts).into()
    }

    /// A fresh scratch slot of `n` words.
    pub(super) fn alloc(&mut self, n: usize) -> usize {
        self.size.words += n;
        self.size.words - n
    }

    /// An encoded expression computing its `n` words into its own frame
    /// slot `out` (`Place::Fresh`).
    pub(super) fn fresh(&mut self, f: EncF, n: usize, out: usize) -> Code {
        self.mark = Some(Place::Fresh(out));
        Code::E(f, n)
    }

    /// An encoded expression whose `n` words are always at frame offset
    /// `off` (`Place::Temp`).
    fn at_temp(&mut self, off: usize, n: usize) -> Code {
        self.mark = Some(Place::Temp(off));
        Code::E(Box::new(move |_| Ok(Loc::frame(off))), n)
    }

    /// An encoded expression whose `n` words are always at `l`, a location
    /// of the current state or the constant pool (`Place::Fixed`).
    fn fixed(&mut self, l: Loc, n: usize) -> Code {
        self.mark = Some(Place::Fixed(l));
        Code::E(Box::new(move |_| Ok(l)), n)
    }

    /// Word `i` of the expression compiled last, if its place is known
    /// (it then need not be evaluated).
    pub(super) fn word_at(&self, i: usize) -> Option<W1> {
        match self.last {
            Place::Fixed(l) if l.space() == super::SP_CONST => self.consts.get(l.off() + i).map(|c| W1::K(*c)),
            Place::Fixed(l) => Some(W1::S0(l.off() + i)),
            Place::Temp(off) => Some(W1::Fr(off + i)),
            Place::Dyn | Place::Fresh(_) | Place::Int(_) => None,
        }
    }

    /// The integer expression `e` as an operand (read in place if its
    /// place is known).
    pub(super) fn int_src(&mut self, e: &Expr) -> C<IS> {
        let f = self.int_(e)?;
        Ok(match self.last {
            Place::Int(at) => IS::At(at),
            _ => IS::F(f),
        })
    }

    /// An integer expression whose value is at `at`.
    fn int_at(&mut self, at: IntAt) -> Code {
        self.mark = Some(Place::Int(at));
        Code::I(match at {
            IntAt::K(c) => Box::new(move |_| Ok(c)),
            IntAt::T(i) => Box::new(move |fx| Ok(fx.fr.iv[i])),
            IntAt::W(w, lo) => Box::new(move |fx| Ok(lo + w.get(fx) as i64)),
        })
    }

    /// The location of the expression compiled last, if it is known (it
    /// then need not be evaluated).
    pub(super) fn known_loc(&self) -> Option<Loc> {
        match self.last {
            Place::Fixed(l) => Some(l),
            Place::Temp(off) => Some(Loc::frame(off)),
            Place::Dyn | Place::Fresh(_) | Place::Int(_) => None,
        }
    }

    /// The output slot of `place` if it may be modified in place to compute
    /// a value of `n` words, else a new one.
    fn out_slot(&mut self, place: Place, n: usize) -> usize {
        match place {
            Place::Fresh(off) => off,
            _ => self.alloc(n),
        }
    }

    /// Bind `Let` temp `t` to the value `code` (just compiled, at
    /// `self.last`): an encoded value computed into its own slot or at a
    /// fixed location stays there (the temp is an alias, nothing is
    /// copied). Returns the closure evaluating the binding and the temp's
    /// previous slot (to restore after the body is compiled).
    pub(super) fn bind_let(&mut self, t: Temp, code: Code) -> C<(Box<dyn Fn(&mut Fx) -> R<()> + Send + Sync>, Slot)> {
        let old = self.slots[t as usize];
        let alias = match (old, &code, self.last) {
            _ if self.scoped_state => None,
            (Slot::W(_, n), Code::E(_, m), Place::Fresh(off)) if n == *m => Some(Slot::A(Loc::frame(off), n)),
            (Slot::W(_, n), Code::E(_, m), Place::Fixed(l)) if n == *m => Some(Slot::A(l, n)),
            // (Copying a few words is cheaper than reading through a
            // location known only at run time.)
            (Slot::W(off, n), Code::E(_, m), Place::Dyn) if n == *m && n > 8 => {
                self.size.ints += 1;
                Some(Slot::P(self.size.ints - 1, off, n))
            }
            _ => None,
        };
        match (alias, code) {
            (Some(Slot::P(i, off, n)), Code::E(f, _)) => {
                self.slots[t as usize] = Slot::P(i, off, n);
                // A value computed anywhere but in the next state stays
                // where it is while the temp is in scope: it is the result
                // of an expression outside the `Let`'s body, of a temp
                // bound around the `Let`, or of the current state or the
                // constant pool. The next state is copied: `ENABLED`
                // replaces it.
                Ok((
                    Box::new(move |fx| {
                        let l = f(fx)?;
                        if l.space() == super::SP_S1 {
                            fx.copy_to(l, off, n);
                            fx.fr.iv[i] = Loc::frame(off).0 as i64;
                        } else {
                            fx.fr.iv[i] = l.0 as i64;
                        }
                        Ok(())
                    }),
                    old,
                ))
            }
            (Some(a), Code::E(f, _)) => {
                self.slots[t as usize] = a;
                Ok((
                    Box::new(move |fx| {
                        f(fx)?;
                        Ok(())
                    }),
                    old,
                ))
            }
            (_, code) => Ok((self.store(old, code)?, old)),
        }
    }

    /// Make encoded temp `t` read the location stored (at run time) in
    /// `iv[i]`; returns `i` and the temp's previous slot (to restore after
    /// its scope is compiled).
    pub(super) fn bind_loc(&mut self, t: Temp) -> C<(usize, Slot)> {
        let old = self.slots[t as usize];
        let Slot::W(off, n) = old else { return Err(format!("temp representation mismatch ({old:?})")) };
        self.size.ints += 1;
        let i = self.size.ints - 1;
        self.slots[t as usize] = Slot::P(i, off, n);
        Ok((i, old))
    }

    pub(super) fn words(&self, ty: Ty) -> C<usize> {
        match ty {
            Ty::Enc(sid) => Ok(self.t.words(sid) as usize),
            _ => Err(format!("expected an encoded type, got {ty:?}")),
        }
    }

    fn shape(&self, ty: Ty) -> C<&'c Shape> {
        match ty {
            Ty::Enc(sid) => Ok(self.t.shape(sid)),
            _ => Err(format!("expected an encoded type, got {ty:?}")),
        }
    }

    // ------------------------------------------------------------------
    // representations

    pub(crate) fn bool_(&mut self, e: &Expr) -> C<BoolF> {
        Ok(match self.expr(e)? {
            Code::B(f) => f,
            Code::V(f) => Box::new(move |fx| match f(fx)? {
                Value::Bool(b) => Ok(b),
                other => Err(EvalError::new(format!("A non-boolean expression ({other}) was used as a boolean."))),
            }),
            Code::I(_) | Code::E(..) => Box::new(|_| err("A non-boolean expression was used as a boolean.")),
        })
    }

    pub(super) fn int_(&mut self, e: &Expr) -> C<IntF> {
        let ty = e.ty;
        Ok(match self.expr(e)? {
            Code::I(f) => f,
            Code::V(f) => Box::new(move |fx| match f(fx)? {
                Value::Int(i) => Ok(i),
                other => Err(EvalError::new(format!("Expected an integer, found {other}"))),
            }),
            Code::E(f, n) => {
                let Ty::Enc(sid) = ty else { return Err("internal: encoded code of a non-encoded type".into()) };
                Box::new(move |fx| {
                    let l = f(fx)?;
                    // SAFETY: the matching encoder/program produced these words.
                    // Active Dyn handles were published before this call.
                    match unsafe { fx.typing().node(sid).decode_unchecked(fx.get(l, n)) } {
                        Value::Int(i) => Ok(i),
                        other => Err(EvalError::new(format!("Expected an integer, found {other}"))),
                    }
                })
            }
            Code::B(_) => Box::new(|_| err("A non-integer expression was used as an integer.")),
        })
    }

    /// The encoded expression `e` (its location without evaluating it if
    /// it is known) and its number of words.
    pub(super) fn enc(&mut self, e: &Expr) -> C<(LocF, usize)> {
        match self.expr(e)? {
            Code::E(f, n) => Ok((self.loc_f(f), n)),
            _ => Err(format!("expected an encoded expression ({:?})", e.ty)),
        }
    }

    /// `f`, the encoded expression compiled last, as a `LocF`.
    pub(super) fn loc_f(&self, f: EncF) -> LocF {
        match self.known_loc() {
            Some(l) => LocF::K(l),
            None => LocF::F(f),
        }
    }

    pub(super) fn val(&mut self, e: &Expr) -> C<ValF> {
        let ty = e.ty;
        let code = self.expr(e)?;
        Ok(self.to_val(code, ty))
    }

    pub(super) fn to_val(&self, code: Code, ty: Ty) -> ValF {
        match code {
            Code::V(f) => f,
            Code::B(f) => Box::new(move |fx| Ok(Value::Bool(f(fx)?))),
            Code::I(f) => Box::new(move |fx| Ok(Value::Int(f(fx)?))),
            Code::E(f, n) => {
                let Ty::Enc(sid) = ty else { panic!("internal: encoded code of type {ty:?}") };
                Box::new(move |fx| {
                    let l = f(fx)?;
                    Ok(
                        // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
                        unsafe { fx.typing().node(sid).decode_unchecked(fx.get(l, n)) },
                    )
                })
            }
        }
    }

    /// `e` in the representation of `ty` (a boxed value where the code is boxed).
    pub(super) fn typed(&mut self, e: &Expr, ty: Ty) -> C<Code> {
        let code = self.expr(e)?;
        Ok(match (code, ty) {
            (c @ Code::B(_), Ty::Bool) | (c @ Code::I(_), Ty::Int) | (c @ Code::E(..), Ty::Enc(_)) | (c @ Code::V(_), _) => c,
            (c, Ty::Val) => Code::V(self.to_val(c, e.ty)),
            (c, _) => c,
        })
    }

    /// A closure storing the value of `code` into `slot`.
    pub(super) fn store(&self, slot: Slot, code: Code) -> C<Box<dyn Fn(&mut Fx) -> R<()> + Send + Sync>> {
        Ok(match (slot, code) {
            (Slot::I(i), Code::B(f)) => Box::new(move |fx| {
                fx.fr.iv[i] = f(fx)? as i64;
                Ok(())
            }),
            (Slot::I(i), Code::I(f)) => Box::new(move |fx| {
                fx.fr.iv[i] = f(fx)?;
                Ok(())
            }),
            (Slot::I(i), Code::V(f)) => Box::new(move |fx| {
                fx.fr.iv[i] = match f(fx)? {
                    Value::Bool(b) => b as i64,
                    Value::Int(x) => x,
                    other => return Err(EvalError::new(format!("internal: boxed value {other} in a scalar temp"))),
                };
                Ok(())
            }),
            (Slot::V(i), c) => {
                let f = match c {
                    Code::V(f) => f,
                    Code::B(f) => Box::new(move |fx: &mut Fx| Ok(Value::Bool(f(fx)?))) as ValF,
                    Code::I(f) => Box::new(move |fx: &mut Fx| Ok(Value::Int(f(fx)?))) as ValF,
                    Code::E(..) => return Err("encoded value in a boxed temp".into()),
                };
                Box::new(move |fx| {
                    let v = f(fx)?;
                    fx.fr.vv[i] = Some(v);
                    Ok(())
                })
            }
            (Slot::W(off, n), Code::E(f, m)) if n == m => {
                let f = self.loc_f(f);
                Box::new(move |fx| {
                    let l = f.at(fx)?;
                    fx.copy_to(l, off, n);
                    Ok(())
                })
            }
            (s, _) => return Err(format!("temp representation mismatch ({s:?})")),
        })
    }

    /// Reading a temp of type `ty`.
    fn temp(&mut self, t: Temp, ty: Ty) -> C<Code> {
        Ok(match (self.slots[t as usize], ty) {
            (Slot::I(i), Ty::Bool) => Code::B(Box::new(move |fx| Ok(fx.fr.iv[i] != 0))),
            (Slot::I(i), _) => self.int_at(IntAt::T(i)),
            (Slot::V(i), _) => Code::V(Box::new(move |fx| Ok(fx.fr.vv[i].clone().expect("temp read before definition")))),
            (Slot::W(off, n), _) => self.at_temp(off, n),
            (Slot::A(l, n), _) if l.space() != super::SP_FRAME => self.fixed(l, n),
            (Slot::A(l, n), _) => self.at_temp(l.off(), n),
            (Slot::P(i, _, n), _) => Code::E(Box::new(move |fx| Ok(Loc(fx.fr.iv[i] as u32))), n),
        })
    }

    /// A runtime error of the representation of `ty`.
    fn fail(&self, ty: Ty, msg: Arc<str>) -> C<Code> {
        Ok(match ty {
            Ty::Bool => Code::B(Box::new(move |_| err(&msg))),
            Ty::Int => Code::I(Box::new(move |_| err(&msg))),
            Ty::Enc(_) => Code::E(Box::new(move |_| err(&msg)), self.words(ty)?),
            Ty::Val => Code::V(Box::new(move |_| err(&msg))),
        })
    }

    // ------------------------------------------------------------------
    // expressions

    pub(crate) fn expr(&mut self, e: &Expr) -> C<Code> {
        self.mark = None;
        let code = self.node(e)?;
        self.last = self.mark.take().unwrap_or(Place::Dyn);
        Ok(code)
    }

    fn node(&mut self, e: &Expr) -> C<Code> {
        let ty = e.ty;
        Ok(match &*e.kind {
            ExprKind::Const(v) => match (ty, v) {
                (Ty::Bool, Value::Bool(b)) => {
                    let b = *b;
                    Code::B(Box::new(move |_| Ok(b)))
                }
                (Ty::Int, Value::Int(i)) => self.int_at(IntAt::K(*i)),
                (Ty::Enc(sid), v) => {
                    let t = self.t;
                    let n = t.words(sid) as usize;
                    let mut w = vec![0u64; n];
                    let enc = v
                        .normalize()
                        .map_err(|e| e.to_string())
                        .and_then(|v| t.node(sid).encode(&v, &mut w).map_err(|m| format!("layout miss at {}", m.path)));
                    match enc {
                        Ok(()) => self.const_words(w.into()),
                        Err(m) => return self.fail(ty, m.into()),
                    }
                }
                _ => {
                    let v = v.clone();
                    Code::V(Box::new(move |_| Ok(v.clone())))
                }
            },
            ExprKind::ConstWords(w) => self.const_words(w.clone()),
            ExprKind::Fail(msg) => return self.fail(ty, msg.clone()),
            ExprKind::ConstElems { .. } | ExprKind::IntRange(..) | ExprKind::Subsets(_) | ExprKind::OrderedSet { .. } => {
                return self.fail(ty, "internal: iteration source evaluated as a value".into())
            }
            ExprKind::Var(i) => {
                let i = *i as usize;
                match ty {
                    Ty::Enc(sid) => self.fixed(Loc::s0(self.t.var_offset(i)), self.t.words(sid) as usize),
                    _ => Code::V(Box::new(move |fx| Ok(fx.s0_values()?[i].clone()))),
                }
            }
            ExprKind::NextVar(i) => {
                let i = *i as usize;
                match ty {
                    Ty::Enc(sid) => {
                        let off = self.t.var_offset(i);
                        Code::E(Box::new(move |_| Ok(Loc::s1(off))), self.t.words(sid) as usize)
                    }
                    _ => Code::V(Box::new(move |fx| {
                        if fx.s1_dec[i].is_none() {
                            let t = fx.typing();
                            fx.s1_dec[i] = Some(
                                // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
                                unsafe { t.layout.node(i).decode_unchecked(&fx.s1w()[t.var_range(i)]) },
                            );
                        }
                        Ok(fx.s1_dec[i].clone().expect("decoded above"))
                    })),
                }
            }
            ExprKind::Temp(t) => self.temp(*t, ty)?,

            // ---- scalars
            ExprKind::Not(x) => {
                let x = self.bool_(x)?;
                Code::B(Box::new(move |fx| Ok(!x(fx)?)))
            }
            ExprKind::And(xs) => {
                let xs = xs.iter().map(|x| self.bool_(x)).collect::<C<Vec<_>>>()?;
                Code::B(match xs.len() {
                    2 => {
                        let mut it = xs.into_iter();
                        let (a, b) = (it.next().unwrap(), it.next().unwrap());
                        Box::new(move |fx| Ok(a(fx)? && b(fx)?))
                    }
                    _ => Box::new(move |fx| {
                        for x in &xs {
                            if !x(fx)? {
                                return Ok(false);
                            }
                        }
                        Ok(true)
                    }),
                })
            }
            ExprKind::Or(xs) => {
                let xs = xs.iter().map(|x| self.bool_(x)).collect::<C<Vec<_>>>()?;
                Code::B(Box::new(move |fx| {
                    for x in &xs {
                        if x(fx)? {
                            return Ok(true);
                        }
                    }
                    Ok(false)
                }))
            }
            ExprKind::If(c, a, b) => {
                let c = self.bool_(c)?;
                match (self.typed(a, ty)?, self.typed(b, ty)?) {
                    (Code::B(a), Code::B(b)) => Code::B(Box::new(move |fx| if c(fx)? { a(fx) } else { b(fx) })),
                    (Code::I(a), Code::I(b)) => Code::I(Box::new(move |fx| if c(fx)? { a(fx) } else { b(fx) })),
                    (Code::E(a, n), Code::E(b, _)) => Code::E(Box::new(move |fx| if c(fx)? { a(fx) } else { b(fx) }), n),
                    (a, b) => {
                        let (a, b) = (self.to_val(a, ty), self.to_val(b, ty));
                        Code::V(Box::new(move |fx| if c(fx)? { a(fx) } else { b(fx) }))
                    }
                }
            }
            ExprKind::IntBin(op, a, b) => {
                let (a, b) = (self.int_src(a)?, self.int_src(b)?);
                macro_rules! bin {
                    ($f:path) => {
                        Code::I(Box::new(move |fx| {
                            let x = a.get(fx)?;
                            let y = b.get(fx)?;
                            Ok($f(x, y)?)
                        }))
                    };
                }
                match op {
                    IntOp::Add => bin!(arith::add),
                    IntOp::Sub => bin!(arith::sub),
                    IntOp::Mul => bin!(arith::mul),
                    IntOp::DivFloor => bin!(arith::div_floor),
                    IntOp::DivNat => bin!(arith::div_naturals),
                    IntOp::Pow => bin!(arith::pow),
                    IntOp::Gcd => bin!(arith::gcd),
                    IntOp::Mod => bin!(arith::modulo),
                }
            }
            ExprKind::IntCmp(op, a, b) => {
                let (a, b) = (self.int_src(a)?, self.int_src(b)?);
                macro_rules! cmp {
                    ($o:tt) => {
                        Code::B(Box::new(move |fx| {
                            let x = a.get(fx)?;
                            let y = b.get(fx)?;
                            Ok(x $o y)
                        }))
                    };
                }
                match op {
                    CmpOp::Lt => cmp!(<),
                    CmpOp::Le => cmp!(<=),
                    CmpOp::Gt => cmp!(>),
                    CmpOp::Ge => cmp!(>=),
                }
            }
            ExprKind::Neg(a) => {
                let a = self.int_(a)?;
                Code::I(Box::new(move |fx| Ok(arith::neg(a(fx)?)?)))
            }
            ExprKind::Eq(a, b) => Code::B(self.eq(a, b)?),
            ExprKind::Convert(x) => self.convert(x, ty)?,

            // ---- binders
            ExprKind::Exists { bind, set, body } => Code::B(self.quantifier(true, *bind, set, body)?),
            ExprKind::Forall { bind, set, body } => Code::B(self.quantifier(false, *bind, set, body)?),
            ExprKind::Choose { bind, set, body } => self.choose(ty, *bind, set, body)?,
            ExprKind::Let { temp, value, body } => {
                let code = self.expr(value)?;
                let (st, old) = self.bind_let(*temp, code)?;
                let body = self.expr(body);
                self.slots[*temp as usize] = old;
                match body? {
                    Code::B(f) => Code::B(Box::new(move |fx| {
                        st(fx)?;
                        f(fx)
                    })),
                    Code::I(f) => Code::I(Box::new(move |fx| {
                        st(fx)?;
                        f(fx)
                    })),
                    Code::E(f, n) => Code::E(
                        Box::new(move |fx| {
                            st(fx)?;
                            f(fx)
                        }),
                        n,
                    ),
                    Code::V(f) => Code::V(Box::new(move |fx| {
                        st(fx)?;
                        f(fx)
                    })),
                }
            }

            // ---- boxed values
            ExprKind::Apply(f, a) => {
                let (f, a) = (self.val(f)?, self.val(a)?);
                Code::V(Box::new(move |fx| {
                    let f = f(fx)?;
                    let a = a(fx)?;
                    Ok(ops::apply(&f, &a)?)
                }))
            }
            ExprKind::ValField(r, field) => {
                let (r, field) = (self.val(r)?, *field);
                Code::V(Box::new(move |fx| Ok(ops::field(&r(fx)?, field)?)))
            }
            ExprKind::Tuple(xs) => {
                let xs = xs.iter().map(|x| self.val(x)).collect::<C<Vec<_>>>()?;
                Code::V(Box::new(move |fx| {
                    let vs = xs.iter().map(|x| x(fx)).collect::<R<Vec<_>>>()?;
                    Ok(Value::tuple(vs))
                }))
            }
            ExprKind::RefOp { op, args } => self.ref_op(op, args, ty)?,
            ExprKind::RefElems(_) => return Err("iteration source used as a value".into()),
            ExprKind::ValOp { op, args } => {
                let args = args.iter().map(|x| self.val(x)).collect::<C<Vec<_>>>()?;
                let op = *op;
                Code::V(Box::new(move |fx| {
                    let vs = args.iter().map(|x| x(fx)).collect::<R<Vec<_>>>()?;
                    fx.with_ctx(|ip, cx| ip.builtin_on_values(op, vs, cx))
                }))
            }
            ExprKind::Interp { expr, binds, deferred, env } => {
                let codes = binds
                    .iter()
                    .map(|(l, x)| Ok(InterpBind { local: *l, def: tlx_eval::env::def_of_value_key(*l), code: self.expr(x)?, ty: x.ty }))
                    .collect::<C<Vec<_>>>()?;
                let n = InterpNode {
                    // The node's address identifies it in the memo table.
                    node: &*e.kind as *const ExprKind as usize,
                    expr: expr.clone(),
                    binds: binds.clone(),
                    codes,
                    deferred: deferred.clone(),
                    env: env.clone(),
                };
                Code::V(Box::new(move |fx| n.eval(fx)))
            }
            ExprKind::Enabled(s) => {
                let body = self.stmt(s)?;
                Code::B(Box::new(move |fx| {
                    // A fresh next state for the action (the enclosing
                    // one's is restored afterwards; buffers are reused:
                    // a run undoes all its assignments).
                    let nvars = fx.assigned.len();
                    let words = fx.t.layout.words;
                    let (mut w, mut a, mut d) = fx.spare_s1.pop().unwrap_or_default();
                    if w.len() != words || a.len() != nvars {
                        (w, a, d) = (vec![0; words], vec![false; nvars], vec![None; nvars]);
                    }
                    let s1 = std::mem::replace(&mut fx.s1, w);
                    // (The next-state reads of an enclosing region do not
                    // apply to ENABLED's own next state.)
                    let s1_ext = fx.s1_ext.take();
                    let s1_reads = fx.s1_reads.take();
                    let assigned = std::mem::replace(&mut fx.assigned, a);
                    let s1_dec = std::mem::replace(&mut fx.s1_dec, d);
                    let has_s1 = std::mem::replace(&mut fx.has_s1, true);
                    // (Next-state values cached for a complete next state
                    // do not hold in ENABLED's.)
                    let cache = fx.cache.take();
                    let cache_primed = std::mem::replace(&mut fx.cache_primed, false);
                    let mut found = false;
                    let r = body(fx, &mut |_| {
                        found = true;
                        Ok(false)
                    });
                    let w = std::mem::replace(&mut fx.s1, s1);
                    fx.s1_ext = s1_ext;
                    fx.s1_reads = s1_reads;
                    let a = std::mem::replace(&mut fx.assigned, assigned);
                    let d = std::mem::replace(&mut fx.s1_dec, s1_dec);
                    fx.spare_s1.push((w, a, d));
                    fx.has_s1 = has_s1;
                    fx.cache = cache;
                    fx.cache_primed = cache_primed;
                    r?;
                    Ok(found)
                }))
            }
            ExprKind::Call { func, args } => self.call(ty, *func, args)?,

            // ---- encoded values (`encoded.rs`)
            ExprKind::Slice { .. }
            | ExprKind::Index { .. }
            | ExprKind::ExceptAt { .. }
            | ExprKind::ExceptIndex { .. }
            | ExprKind::Concat { .. }
            | ExprKind::Pack { .. }
            | ExprKind::Rank { .. }
            | ExprKind::Recode { .. }
            | ExprKind::RankUnion { .. }
            | ExprKind::Lookup { .. }
            | ExprKind::RankFlat { .. }
            | ExprKind::UnionField { .. }
            | ExprKind::UnionFieldInt { .. }
            | ExprKind::MapGet { .. }
            | ExprKind::MapPut { .. }
            | ExprKind::MapBuild { .. }
            | ExprKind::MapMerge { .. }
            | ExprKind::BitMember { .. }
            | ExprKind::BitSetOp { .. }
            | ExprKind::BitCard { .. }
            | ExprKind::BitSet { .. }
            | ExprKind::SortedMember { .. }
            | ExprKind::SortedInsert { .. }
            | ExprKind::Filter { .. }
            | ExprKind::MapSet { .. }
            | ExprKind::Fold { .. }
            | ExprKind::UnionFold { .. }
            | ExprKind::Collect { .. }
            | ExprKind::SeqLen { .. }
            | ExprKind::SeqIndex { .. }
            | ExprKind::SeqTail { .. }
            | ExprKind::SeqAppend { .. }
            | ExprKind::SeqSub { .. }
            | ExprKind::SortedOp { .. }
            | ExprKind::SeqFilter { .. }
            | ExprKind::SeqConcat { .. } => return self.encoded(e),
        })
    }

    /// A constant encoding (in the function's constant pool).
    fn const_words(&mut self, w: Arc<[u64]>) -> Code {
        let n = w.len();
        let off = self.consts.len();
        self.consts.extend_from_slice(&w);
        self.fixed(Loc::cnst(off), n)
    }

    fn map_dims(&self, ty: Ty) -> C<MapDims> {
        crate::types::map_dims(self.shape(ty)?).ok_or_else(|| "not a map shape".to_string())
    }

    /// Slot selected by a function argument (None: outside the domain).
    pub(super) fn slot_in(&mut self, arg: &Expr, map: &IndexMap) -> C<Box<dyn Fn(&mut Fx) -> R<Option<usize>> + Send + Sync>> {
        Ok(match map {
            IndexMap::IntRange { lo, n } => {
                if arg.ty != Ty::Int {
                    return Err("internal: integer index must be unboxed".into());
                }
                let a = self.int_src(arg)?;
                let (lo, n) = (*lo, *n as i64);
                Box::new(move |fx| {
                    let i = a.get(fx)?;
                    Ok((i >= lo && i < lo + n).then(|| (i - lo) as usize))
                })
            }
            IndexMap::Table(t) => {
                let t = t.clone();
                match self.expr(arg)? {
                    Code::E(a, _) => Box::new(move |fx| {
                        let l = a(fx)?;
                        Ok(t.get(fx.word(l, 0) as usize).copied().filter(|&x| x >= 0).map(|x| x as usize))
                    }),
                    Code::B(a) => Box::new(move |fx| {
                        a(fx)?;
                        Ok(None)
                    }),
                    Code::I(a) => Box::new(move |fx| {
                        a(fx)?;
                        Ok(None)
                    }),
                    Code::V(a) => Box::new(move |fx| {
                        a(fx)?;
                        Ok(None)
                    }),
                }
            }
        })
    }
}

/// Compile a `FnDef` (its calls are checked by `Program::new`).
pub(crate) fn compile_fn(t: &Typing, f: &FnDef) -> C<(FnProg, Vec<u32>)> {
    let mut c = Compiler::new(t, &f.temps, &[]);
    c.scoped_state = f.body.has_composition();
    c.callees = Some(Vec::new());
    let params = f.params.iter().map(|p| c.slots[*p as usize]).collect();
    let body = c.typed(&f.body, f.ret)?;
    let callees = c.callees.take().unwrap_or_default();
    Ok((FnProg { params, body, frame: c.frame_size(), consts: c.take_consts(), budgeted: f.budgeted }, callees))
}
