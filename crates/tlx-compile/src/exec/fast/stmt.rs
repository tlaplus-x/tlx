//! Statements and iteration sources.

use std::sync::{Arc, OnceLock};

use tlx_eval::EvalError;
use tlx_layout::Shape;
use tlx_value::{ops, Value};

use super::expr::{Compiler, LocF, Place, Slot, C, SET_TOO_LARGE};
use super::{copy_words, move_words, Code, Fx, IntF, Loc, StmtF, ValF, R};
use crate::exec::encops::{for_each_combination, sorted_add};
use crate::inplace::{self, Plan};
use crate::ir::*;
use crate::types::Typing;

/// Writes an assigned variable's value into the next state.
type Put = Box<dyn Fn(&mut Fx) -> R<()> + Send + Sync>;

/// Writes a value into the next state at a word offset (`Compiler::into_s1`).
type IntoS1 = Box<dyn Fn(&mut Fx, usize) -> R<()> + Send + Sync>;
/// How boxed sets are enumerated (as the tree-walking executor does).
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum ValIter {
    /// A quantifier's bound domain, as the interpreter's `bound_elems`
    /// materializes it (`ops::enumerate`, so `-maxSetSize` applies); a
    /// `SUBSET S` too large to hold and an interval stream instead.
    Bound,
    /// `ops::enumerate` order, streamed by `ops::for_each_enumerated`
    /// (`x' \in S`: a set filter over a set that is not enumerated is not
    /// materialized, as in the interpreter).
    Enumerate,
    /// `ops::enumerate_normalized` (CHOOSE, sorted `ForEach`).
    Normalized,
}

/// Largest bitset universe whose element encodings are tabulated.
const MAX_TABLE_WORDS: u64 = 1 << 22;

/// How the element of rank `r` of a bitset is encoded.
pub(crate) enum BitElem {
    /// A scalar: its rank.
    Scalar,
    /// A compound element: from a table built on first use (or unranked
    /// and encoded each time if the universe is too large).
    Table { set_sid: ShapeId, k: usize, table: OnceLock<Option<Arc<[u64]>>> },
}

impl BitElem {
    pub(crate) fn new(t: &Typing, set_sid: ShapeId) -> C<BitElem> {
        let Shape::Set { elem, .. } = t.shape(set_sid) else { return Err("not a set shape".into()) };
        if elem.is_scalar() {
            return Ok(BitElem::Scalar);
        }
        let k = t.node(set_sid).set_elem().ok_or("not a set shape")?.words();
        Ok(BitElem::Table { set_sid, k, table: OnceLock::new() })
    }

    /// Write the encoding of the element of rank `r` at frame offset `off`
    /// (`n` words).
    #[inline]
    pub(crate) fn write(&self, fx: &mut Fx, r: usize, off: usize, n: usize) {
        match self {
            BitElem::Scalar => fx.fr.w[off] = r as u64,
            BitElem::Table { set_sid, k, table } => {
                // (The table once it is built, without looking up the
                // element's layout.)
                if let Some(Some(tab)) = table.get() {
                    return copy_words(&mut fx.fr.w[off..off + n], &tab[r * k..r * k + n]);
                }
                let t = fx.typing();
                let elem = t.node(*set_sid).set_elem().expect("set shape");
                let tab = table.get_or_init(|| {
                    let u = elem.bitset_universe()?;
                    if u.saturating_mul(*k as u64) > MAX_TABLE_WORDS {
                        return None;
                    }
                    let mut w = vec![0u64; u as usize * k];
                    for i in 0..u as usize {
                        let v = elem.unrank(i as u64);
                        elem.encode(&v, &mut w[i * k..(i + 1) * k]).expect("unranked element fits its shape");
                    }
                    Some(w.into())
                });
                match tab {
                    Some(tab) => copy_words(&mut fx.fr.w[off..off + n], &tab[r * k..r * k + n]),
                    None => {
                        let v = elem.unrank(r as u64);
                        let w = &mut fx.fr.w[off..off + n];
                        w.fill(0);
                        elem.encode(&v, w).expect("unranked element fits its shape");
                    }
                }
            }
        }
    }
}

/// An iteration source.
pub(crate) enum Src {
    Const {
        words: Arc<[u64]>,
        k: usize,
        count: usize,
    },
    Ordered {
        set: LocF,
        n: usize,
        stage: usize,
        plan: Arc<[u64]>,
        bits: Option<BitElem>,
    },
    Ints(IntF, IntF),
    Subsets {
        set: LocF,
        n: usize,
    },
    Bits {
        set: LocF,
        n: usize,
        stage: usize,
        elem: BitElem,
    },
    Sorted {
        set: LocF,
        n: usize,
        stage: usize,
        k: usize,
    },
    /// A bitset at a location that does not change while it is iterated
    /// (`Place::Fixed`: not staged).
    FixedBits {
        set: Loc,
        n: usize,
        elem: BitElem,
    },
    /// A sorted-array set at such a location.
    FixedSorted {
        set: Loc,
        k: usize,
    },
    Val {
        set: ValF,
        how: ValIter,
    },
    /// The elements of a stored set (a value store handle).
    Refs {
        set: LocF,
        store: tlx_layout::store::StoreRef,
    },
}

fn bind_mismatch<T>() -> R<T> {
    Err(EvalError::new("internal: iteration binding representation mismatch"))
}

impl Src {
    /// Bind each element to `bind` and call `f` (false: stop). False if
    /// stopped early.
    pub(crate) fn run(&self, fx: &mut Fx, bind: Slot, f: &mut dyn FnMut(&mut Fx) -> R<bool>) -> R<bool> {
        match self {
            Src::Const { words, k, count } => {
                let Slot::W(off, _) = bind else { return bind_mismatch() };
                for i in 0..*count {
                    copy_words(&mut fx.fr.w[off..off + k], &words[i * k..(i + 1) * k]);
                    if !f(fx)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Src::Ints(lo, hi) => {
                let Slot::I(slot) = bind else { return bind_mismatch() };
                let (lo, hi) = (lo(fx)?, hi(fx)?);
                if hi.saturating_sub(lo) > 1i64 << 24 {
                    return Err(EvalError::new("integer range too large for compiled iteration"));
                }
                for i in lo..=hi {
                    fx.fr.iv[slot] = i;
                    if !f(fx)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Src::Ordered { set, n, stage, plan, bits } => {
                let Slot::W(off, _) = bind else { return bind_mismatch() };
                let l = set.at(fx)?;
                fx.copy_to(l, *stage, *n);
                if let Some(elem) = bits {
                    let keys = &plan[plan[crate::encoded_order::schema::SPAN] as usize..];
                    let mut idx = vec![0; keys.len()];
                    let count = crate::encoded_order::bit_indices(keys, &fx.fr.w[*stage..*stage + *n], &mut idx);
                    let k = plan[crate::encoded_order::schema::WIDTH] as usize;
                    for &rank in &idx[..count] {
                        elem.write(fx, rank as usize, off, k);
                        if !f(fx)? {
                            return Ok(false);
                        }
                    }
                    return Ok(true);
                }
                let count = fx.fr.w[*stage] as usize;
                let mut idx = vec![0; count];
                crate::encoded_order::indices(plan, &fx.fr.w[*stage..*stage + *n], &mut idx);
                let k = plan[crate::encoded_order::schema::WIDTH] as usize;
                for i in idx {
                    move_words(&mut fx.fr.w, stage + 1 + i as usize * k, k, off);
                    if !f(fx)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Src::Subsets { set, n } => {
                let Slot::W(off, _) = bind else { return bind_mismatch() };
                let l = set.at(fx)?;
                let ranks: Vec<usize> = super::super::words::bit_ranks(fx.get(l, *n)).collect();
                if ranks.len() > 24 {
                    return Err(EvalError::new("too many subsets for compiled iteration"));
                }
                let mut subsets: Vec<u64> = Vec::with_capacity((1 << ranks.len()) * n);
                for_each_combination(ranks.len() as u32, |idx| {
                    let at = subsets.len();
                    subsets.resize(at + n, 0);
                    for &i in idx {
                        let r = ranks[i as usize];
                        subsets[at + r / 64] |= 1 << (r % 64);
                    }
                });
                for s in subsets.chunks(*n) {
                    fx.fr.w[off..off + n].copy_from_slice(s);
                    if !f(fx)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Src::Bits { set, n, stage, elem } => {
                let Slot::W(off, bn) = bind else { return bind_mismatch() };
                let (n, stage) = (*n, *stage);
                let l = set.at(fx)?;
                fx.copy_to(l, stage, n);
                for i in 0..n {
                    let mut b = fx.fr.w[stage + i];
                    while b != 0 {
                        let r = i * 64 + b.trailing_zeros() as usize;
                        b &= b - 1;
                        elem.write(fx, r, off, bn);
                        if !f(fx)? {
                            return Ok(false);
                        }
                    }
                }
                Ok(true)
            }
            Src::FixedBits { set, n, elem } => {
                let Slot::W(off, bn) = bind else { return bind_mismatch() };
                for i in 0..*n {
                    let mut b = fx.word(*set, i);
                    while b != 0 {
                        let r = i * 64 + b.trailing_zeros() as usize;
                        b &= b - 1;
                        elem.write(fx, r, off, bn);
                        if !f(fx)? {
                            return Ok(false);
                        }
                    }
                }
                Ok(true)
            }
            Src::FixedSorted { set, k } => {
                let Slot::W(off, _) = bind else { return bind_mismatch() };
                let k = *k;
                for i in 0..fx.word(*set, 0) as usize {
                    fx.copy_to(set.plus(1 + i * k), off, k);
                    if !f(fx)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Src::Sorted { set, n, stage, k } => {
                let Slot::W(off, _) = bind else { return bind_mismatch() };
                let (n, stage, k) = (*n, *stage, *k);
                let l = set.at(fx)?;
                fx.copy_to(l, stage, n);
                for i in 0..fx.fr.w[stage] as usize {
                    let at = stage + 1 + i * k;
                    move_words(&mut fx.fr.w, at, k, off);
                    if !f(fx)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Src::Refs { set, store } => {
                let Slot::W(off, _) = bind else { return bind_mismatch() };
                let at = set.at(fx)?;
                let h = fx.word(at, 0);
                let pin = store.pin();
                let Some(es) = pin.set_elems(h) else {
                    return Err(EvalError::new("value store iteration over a non-set (the interpreter decides)"));
                };
                for &e in es {
                    fx.fr.w[off] = e;
                    if !f(fx)? {
                        return Ok(false);
                    }
                }
                Ok(true)
            }
            Src::Val { set, how } => {
                let v = set(fx)?;
                let put = |fx: &mut Fx, x: Value| -> R<()> {
                    match bind {
                        Slot::V(i) => fx.fr.vv[i] = Some(x),
                        Slot::I(i) => {
                            fx.fr.iv[i] = match x {
                                Value::Int(x) => x,
                                Value::Bool(b) => b as i64,
                                _ => return bind_mismatch(),
                            }
                        }
                        Slot::W(..) | Slot::A(..) | Slot::P(..) => return bind_mismatch(),
                    }
                    Ok(())
                };
                match how {
                    ValIter::Bound | ValIter::Enumerate => {
                        let mut done = true;
                        let mut err = None;
                        let mut visit = |x: Value| {
                            let r = put(fx, x).and_then(|()| f(fx));
                            match r {
                                Ok(true) => Ok(true),
                                Ok(false) => {
                                    done = false;
                                    Ok(false)
                                }
                                Err(e) => {
                                    err = Some(e);
                                    Ok(false)
                                }
                            }
                        };
                        if *how == ValIter::Bound {
                            // A quantifier's domain, exactly as the
                            // interpreter's `bound_elems`: `ops::bound_kind`
                            // decides whether TLC streams the domain, shares
                            // it, or materializes it (where the `-maxSetSize`
                            // bound applies, and an error anywhere in the
                            // domain surfaces before the body runs). Sharing
                            // and streaming both iterate without building the
                            // set.
                            match ops::bound_kind(&v) {
                                ops::BoundKind::Share | ops::BoundKind::Stream => {
                                    ops::for_each_enumerated(&v, &mut visit)?;
                                }
                                ops::BoundKind::Materialize => {
                                    for x in ops::enumerate(&v)? {
                                        if !visit(x)? {
                                            break;
                                        }
                                    }
                                }
                                ops::BoundKind::Overflow => {
                                    return Err(tlx_value::limits::too_many_elements().into());
                                }
                            }
                        } else {
                            ops::for_each_enumerated(&v, &mut visit)?;
                        }
                        match err {
                            Some(e) => Err(e),
                            None => Ok(done),
                        }
                    }
                    ValIter::Normalized => {
                        for x in ops::enumerate_normalized(&v)? {
                            put(fx, x)?;
                            if !f(fx)? {
                                return Ok(false);
                            }
                        }
                        Ok(true)
                    }
                }
            }
        }
    }
}

impl Compiler<'_> {
    /// The iteration source `set` (boxed sets enumerated as `how` says).
    pub(crate) fn src_how(&mut self, set: &Expr, how: ValIter) -> C<Src> {
        Ok(match &*set.kind {
            ExprKind::OrderedSet { set, plan } => {
                let Ty::Enc(sid) = set.ty else { return Err("ordered boxed set".into()) };
                let bits = match self.t.shape(sid) {
                    Shape::Set { elem, .. } if tlx_layout::layout::bitset_universe(elem).is_some() => Some(BitElem::new(self.t, sid)?),
                    _ => None,
                };
                let (set, n) = self.enc(set)?;
                let stage = self.alloc(n);
                Src::Ordered { set, n, stage, plan: plan.clone(), bits }
            }
            ExprKind::ConstElems { elem, words, count } => {
                let k = self.t.words(*elem) as usize;
                Src::Const { words: words.clone(), k, count: *count as usize }
            }
            ExprKind::IntRange(lo, hi) => Src::Ints(self.int_(lo)?, self.int_(hi)?),
            ExprKind::RefElems(x) => {
                let store = super::expr::refs_store(self)?;
                Src::Refs { set: self.enc(x)?.0, store }
            }
            ExprKind::Subsets(x) => {
                let (s, n) = self.enc(x)?;
                Src::Subsets { set: s, n }
            }
            _ => match set.ty {
                Ty::Enc(sid) => {
                    let t = self.t;
                    let elem = t.node(sid).set_elem().ok_or("iteration over a non-set encoding")?;
                    let (s, n) = self.enc(set)?;
                    if let Place::Fixed(l) = self.last {
                        return Ok(if elem.bitset_universe().is_some() {
                            Src::FixedBits { set: l, n, elem: BitElem::new(t, sid)? }
                        } else {
                            Src::FixedSorted { set: l, k: elem.words() }
                        });
                    }
                    let stage = self.alloc(n);
                    if elem.bitset_universe().is_some() {
                        Src::Bits { set: s, n, stage, elem: BitElem::new(t, sid)? }
                    } else {
                        Src::Sorted { set: s, n, stage, k: elem.words() }
                    }
                }
                _ => Src::Val { set: self.val(set)?, how },
            },
        })
    }

    /// `src_how` for quantifiers (`sorted` = false) and CHOOSE (true).
    pub(crate) fn src(&mut self, set: &Expr, sorted: bool) -> C<Src> {
        self.src_how(set, if sorted { ValIter::Normalized } else { ValIter::Enumerate })
    }

    pub(crate) fn stmt(&mut self, s: &Stmt) -> C<StmtF> {
        Ok(match s {
            Stmt::Stop => Box::new(|_, _| Ok(true)),
            Stmt::Emit => Box::new(|fx, emit| emit(fx)),
            Stmt::Branches(bs) => {
                let bs = bs.iter().map(|b| self.stmt(b)).collect::<C<Vec<_>>>()?;
                Box::new(move |fx, emit| {
                    for b in &bs {
                        if !b(fx, emit)? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                })
            }
            Stmt::Guard { cond, then } => {
                let c = self.bool_(cond)?;
                let then = self.stmt(then)?;
                Box::new(move |fx, emit| if c(fx)? { then(fx, emit) } else { Ok(true) })
            }
            Stmt::If { cond, then, els } => {
                let c = self.bool_(cond)?;
                let then = self.stmt(then)?;
                let els = self.stmt(els)?;
                Box::new(move |fx, emit| if c(fx)? { then(fx, emit) } else { els(fx, emit) })
            }
            Stmt::Then { first, rest, .. } => {
                let first = self.stmt(first)?;
                let rest = self.stmt(rest)?;
                Box::new(move |fx, emit| first(fx, &mut |fx| rest(fx, emit)))
            }
            Stmt::Let { temp, value, body } => {
                let code = self.expr(value)?;
                let (st, old) = self.bind_let(*temp, code)?;
                let body = self.stmt(body);
                self.slots[*temp as usize] = old;
                let body = body?;
                Box::new(move |fx, emit| {
                    st(fx)?;
                    body(fx, emit)
                })
            }
            Stmt::ForEach { bind, set, iter, body } => {
                let how = match iter {
                    IterMode::Enumerate => ValIter::Enumerate,
                    IterMode::Bound => ValIter::Bound,
                    IterMode::Normalized => ValIter::Normalized,
                };
                let src = self.src_how(set, how)?;
                let slot = self.slots[*bind as usize];
                let body = self.stmt(body)?;
                Box::new(move |fx, emit| src.run(fx, slot, &mut |fx| body(fx, emit)))
            }
            Stmt::Assign { var, value, body } => self.assign(*var as usize, value, body)?,
            Stmt::Error(msg) => {
                let msg = msg.clone();
                Box::new(move |_, _| Err(EvalError::new(msg.to_string())))
            }
            Stmt::Compose { first, second, paths, count } => {
                let first = self.stmt(first)?;
                let second = self.stmt(second)?;
                let paths = paths.iter().map(|p| Ok((p.assigned.clone(), self.stmt(&p.rest)?))).collect::<C<Vec<_>>>()?;
                let count = *count;
                Box::new(move |fx, emit| {
                    let (mids, frame) = {
                        let mut inner = fx.composition_frame(fx.s0, true);
                        let mut mids = Vec::new();
                        first(&mut inner, &mut |inner| {
                            let mut mid = inner.s1.clone();
                            for (i, a) in inner.assigned.iter().enumerate() {
                                if !a {
                                    mid[inner.t.var_range(i)].copy_from_slice(&inner.s0[inner.t.var_range(i)]);
                                }
                            }
                            mids.push(mid);
                            Ok(true)
                        })?;
                        (mids, inner.finish_composition())
                    };
                    fx.fr = frame;
                    if count {
                        fx.composed += mids.len() as u64;
                    }
                    for mid in mids {
                        let (fins, frame) = {
                            let mut inner = fx.composition_frame(&mid, false);
                            let mut fins = Vec::new();
                            second(&mut inner, &mut |inner| {
                                fins.push((inner.s1.clone(), inner.assigned.clone()));
                                Ok(true)
                            })?;
                            (fins, inner.finish_composition())
                        };
                        fx.fr = frame;
                        for (fin, assigned) in fins {
                            let (_, rest) = paths.iter().find(|(mask, _)| mask == &assigned).expect("verified composition mask");
                            let mut compatible = true;
                            for (i, a) in assigned.iter().enumerate() {
                                if *a && fx.assigned[i] {
                                    let range = fx.t.var_range(i);
                                    // SAFETY: both buffers were encoded by the verified program.
                                    let (a, b) = unsafe {
                                        (
                                            fx.t.layout.node(i).decode_unchecked(&fx.s1w()[range.clone()]),
                                            fx.t.layout.node(i).decode_unchecked(&fin[range]),
                                        )
                                    };
                                    if a != b {
                                        compatible = false;
                                        break;
                                    }
                                }
                            }
                            if !compatible {
                                continue;
                            }
                            let saved = fx.s1.clone();
                            let saved_assigned = fx.assigned.clone();
                            for (i, a) in assigned.iter().enumerate() {
                                if *a {
                                    fx.s1[fx.t.var_range(i)].copy_from_slice(&fin[fx.t.var_range(i)]);
                                    fx.assigned[i] = true;
                                }
                            }
                            fx.s1_dec.fill(None);
                            let result = rest(fx, emit);
                            fx.s1 = saved;
                            fx.assigned = saved_assigned;
                            fx.s1_dec.fill(None);
                            if !result? {
                                return Ok(false);
                            }
                        }
                    }
                    Ok(true)
                })
            }
            Stmt::Count(id) => {
                let id = *id as usize;
                Box::new(move |fx, _| {
                    fx.counts[id] += 1;
                    Ok(true)
                })
            }
            Stmt::Repeat { id, bind, set, body, rest } => {
                let id = *id as usize;
                let src = self.src(set, false)?;
                let slot = self.slots[*bind as usize];
                let body = self.stmt(body)?;
                let rest = self.stmt(rest)?;
                Box::new(move |fx, emit| {
                    if fx.counts.len() <= id {
                        fx.counts.resize(id + 1, 0);
                    }
                    let mut total: u64 = 1;
                    src.run(fx, slot, &mut |fx| {
                        let saved = std::mem::replace(&mut fx.counts[id], 0);
                        let r = body(fx, emit);
                        let n = std::mem::replace(&mut fx.counts[id], saved);
                        r?;
                        total = total.saturating_mul(n);
                        Ok(total != 0)
                    })?;
                    for _ in 0..total {
                        if !rest(fx, emit)? {
                            return Ok(false);
                        }
                    }
                    Ok(true)
                })
            }
        })
    }

    /// Assign next-state variable `var`, run `body`, undo the assignment.
    fn assign(&mut self, var: usize, value: &Expr, body: &Stmt) -> C<StmtF> {
        let vt = value.ty;
        let t = self.t;
        if vt == Ty::Enc(t.var_sid[var]) && !value.contains_enabled() {
            // `x' = [f EXCEPT ...]`: built in the next state itself.
            let p = inplace::plan(value, t);
            if !p.is_copy() {
                let off = t.var_range(var).start;
                let put = self.into_s1(&p)?;
                return self.assigned_body(var, Box::new(move |fx| put(fx, off)), body);
            }
        }
        let code = self.expr(value)?;
        let sid = t.var_sid[var];
        let range = t.var_range(var);
        let (off, n) = (range.start, range.len());
        let shape = t.shape(sid).clone();
        // Writes the value into s1[off..off + n].
        let encode = move |fx: &mut Fx, v: &Value| -> R<()> {
            let w = &mut fx.s1[off..off + n];
            w.fill(0);
            fx.t.node(sid).encode(v, w).map_err(|m| EvalError::new(format!("layout miss at {}", m.path)))
        };
        let put: Put = match code {
            Code::E(f, m) if vt == Ty::Enc(sid) && m == n => {
                let f = self.loc_f(f);
                Box::new(move |fx| {
                    let l = f.at(fx)?;
                    let src = l.off();
                    match l.space() {
                        super::SP_FRAME => copy_words(&mut fx.s1[off..off + n], &fx.fr.w[src..src + n]),
                        super::SP_S0 => copy_words(&mut fx.s1[off..off + n], &fx.s0[src..src + n]),
                        super::SP_S1 => move_words(&mut fx.s1, src, n, off),
                        _ => copy_words(&mut fx.s1[off..off + n], &fx.consts[src..src + n]),
                    }
                    Ok(())
                })
            }
            Code::I(f) => Box::new(move |fx| {
                let i = f(fx)?;
                match &shape {
                    Shape::Int { lo, hi } if i >= *lo && i <= *hi => {
                        fx.s1[off] = (i - lo) as u64;
                        Ok(())
                    }
                    _ => encode(fx, &Value::Int(i)),
                }
            }),
            Code::B(f) => Box::new(move |fx| {
                let b = f(fx)?;
                match &shape {
                    Shape::Bool => {
                        fx.s1[off] = b as u64;
                        Ok(())
                    }
                    _ => encode(fx, &Value::Bool(b)),
                }
            }),
            code => {
                let v = self.to_val(code, vt);
                Box::new(move |fx| {
                    let v = v(fx)?.normalize()?;
                    encode(fx, &v)
                })
            }
        };
        self.assigned_body(var, put, body)
    }

    /// Writing the plan `p` (see `inplace`) into the next state at the
    /// word offset given at run time: the base of an update is copied
    /// there once and its slots are written in place. The plan's
    /// expression has no `ENABLED` (which replaces the next state while a
    /// `LetHere` temp may point into it).
    #[allow(clippy::wrong_self_convention)] // compiles a plan into a closure (needs &mut self); not a conversion of self
    fn into_s1(&mut self, p: &Plan) -> C<IntoS1> {
        Ok(match p {
            Plan::Keep => Box::new(|_, _| Ok(())),
            Plan::Copy(e) => {
                let (f, n) = self.enc(e)?;
                Box::new(move |fx, d| {
                    let l = f.at(fx)?;
                    fx.copy_to_s1(l, d, n);
                    Ok(())
                })
            }
            Plan::Let { temp, value, body } => {
                let code = self.expr(value)?;
                let (st, old) = self.bind_let(*temp, code)?;
                let put = self.into_s1(body);
                self.slots[*temp as usize] = old;
                let put = put?;
                Box::new(move |fx, d| {
                    st(fx)?;
                    put(fx, d)
                })
            }
            Plan::LetHere { temp, value, body } => {
                let v = self.into_s1(value)?;
                let (i, old) = self.bind_loc(*temp)?;
                let put = self.into_s1(body);
                self.slots[*temp as usize] = old;
                let put = put?;
                Box::new(move |fx, d| {
                    v(fx, d)?;
                    fx.fr.iv[i] = Loc::s1(d).0 as i64;
                    put(fx, d)
                })
            }
            Plan::At { base, update } => self.plan_at(base, update)?,
            Plan::AtIndex { base, arg, map, update } => self.plan_at_index(base, arg, map, update)?,
            Plan::If { cond, then, els } => {
                let c = self.bool_(cond)?;
                let (t, f) = (self.into_s1(then)?, self.into_s1(els)?);
                Box::new(move |fx, d| if c(fx)? { t(fx, d) } else { f(fx, d) })
            }
            Plan::Concat(parts) => {
                let parts = parts.iter().map(|(off, part)| Ok((*off, self.into_s1(part)?))).collect::<C<Vec<_>>>()?;
                Box::new(move |fx, d| {
                    for (off, part) in &parts {
                        part(fx, d + off)?;
                    }
                    Ok(())
                })
            }
            Plan::Insert { set, elem, elem_words, max_card } => {
                let s = self.into_s1(set)?;
                let (x, k) = self.enc(elem)?;
                let (m, n) = (*max_card as u64, 1 + *max_card as usize * *elem_words as usize);
                Box::new(move |fx, d| {
                    s(fx, d)?;
                    let l = x.at(fx)?;
                    // (The element is not in the destination; it may be
                    // elsewhere in the next state.)
                    let (o, w) = (l.off(), &mut fx.s1[d..d + n]);
                    let ok = match l.space() {
                        super::SP_FRAME => sorted_add(w, &fx.fr.w[o..o + k], k, m),
                        super::SP_S0 => sorted_add(w, &fx.s0[o..o + k], k, m),
                        super::SP_S1 => {
                            let x = fx.s1[o..o + k].to_vec();
                            sorted_add(&mut fx.s1[d..d + n], &x, k, m)
                        }
                        _ => sorted_add(w, &fx.consts[o..o + k], k, m),
                    };
                    if ok {
                        Ok(())
                    } else {
                        Err(EvalError::new(SET_TOO_LARGE.to_string()))
                    }
                })
            }
            Plan::Bits { op, a, b } => {
                let a = self.into_s1(a)?;
                let (y, n) = self.enc(b)?;
                let op = *op;
                Box::new(move |fx, d| {
                    a(fx, d)?;
                    let l = y.at(fx)?;
                    for i in 0..n {
                        let w = fx.word(l, i);
                        let x = &mut fx.s1[d + i];
                        *x = match op {
                            SetOp::Union => *x | w,
                            SetOp::Inter => *x & w,
                            SetOp::Diff => *x & !w,
                        };
                    }
                    Ok(())
                })
            }
        })
    }

    fn plan_at(&mut self, base: &Plan, update: &crate::inplace::AtUpdate) -> C<IntoS1> {
        let b = self.into_s1(base)?;
        Ok(match update {
            crate::inplace::AtUpdate::Word { offset, value } => {
                let v = self.into_s1(value)?;
                let off = *offset;
                Box::new(move |fx, d| {
                    b(fx, d)?;
                    v(fx, d + off)
                })
            }
            crate::inplace::AtUpdate::Bits { value: None, .. } => b,
            crate::inplace::AtUpdate::Bits { pos, value: Some(ve) } => {
                let pos = *pos;
                let (vf, _) = self.enc(ve)?;
                Box::new(move |fx, d| {
                    b(fx, d)?;
                    let lv = vf.at(fx)?;
                    let val = fx.word(lv, 0);
                    pos.insert(&mut fx.s1[d..], val);
                    Ok(())
                })
            }
        })
    }

    fn plan_at_index(&mut self, base: &Plan, arg: &Expr, map: &IndexMap, update: &crate::inplace::IndexUpdate) -> C<IntoS1> {
        let b = self.into_s1(base)?;
        let slot_fn = self.slot_in(arg, map)?;
        Ok(match update {
            crate::inplace::IndexUpdate::Words { elem_words, value } => {
                let v = self.into_s1(value)?;
                let k = *elem_words;
                Box::new(move |fx, d| {
                    b(fx, d)?;
                    match slot_fn(fx)? {
                        Some(s) => v(fx, d + s * k),
                        None => Ok(()),
                    }
                })
            }
            crate::inplace::IndexUpdate::Bits { value: None, .. } => Box::new(move |fx, d| {
                b(fx, d)?;
                slot_fn(fx)?;
                Ok(())
            }),
            crate::inplace::IndexUpdate::Bits { bits, value: Some(ve) } => {
                let bits = *bits;
                let (vf, _) = self.enc(ve)?;
                Box::new(move |fx, d| {
                    b(fx, d)?;
                    if let Some(s) = slot_fn(fx)? {
                        let lv = vf.at(fx)?;
                        let val = fx.word(lv, 0);
                        SlotLayout::insert(bits, &mut fx.s1[d..], s, val);
                    }
                    Ok(())
                })
            }
        })
    }

    /// Assign next-state variable `var` with `put`, run `body`, undo the
    /// assignment.
    fn assigned_body(&mut self, var: usize, put: Put, body: &Stmt) -> C<StmtF> {
        let body = self.stmt(body)?;
        // The words of an unassigned variable are never read (`NextVar`
        // only reads assigned ones, `Emit` runs when all are assigned), so
        // undoing an assignment only clears its flag.
        Ok(Box::new(move |fx, emit| {
            put(fx)?;
            debug_assert!(!fx.assigned[var], "IR assigned variable {var} twice on one path");
            fx.assigned[var] = true;
            fx.s1_dec[var] = None;
            let r = body(fx, emit);
            fx.assigned[var] = false;
            fx.s1_dec[var] = None;
            r
        }))
    }
}
