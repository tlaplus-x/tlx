//! Shared memo tables of equivalent host regions: two regions
//! whose results are the same function of the same memo key share one
//! memo node, so a value computed by one region (say, `Partitions(I, p,
//! seq)` in an action) is a hit for the other (the same computation in a
//! liveness transition predicate).
//!
//! Two memoizable regions are equivalent if their keys are laid out alike
//! (same input representations, same state variables read, current state
//! present in both or neither) and their expressions are the same up to a
//! consistent renaming of temps (a bijection that preserves the temps'
//! types and maps the inputs positionally), with interpreter fallbacks of
//! the same HIR node (by identity) in environments that bind the same
//! locals to equal values (`Env::same_bindings`). Memoizable regions are
//! pure, so such regions compute the same value from the same key wherever
//! they are called; errors are not memoized, so an error message (which
//! names the source position) is always the region's own.

use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use tlx_sema::Program;

use super::mixed::{Region, RegionCtx};
use crate::ir::{Deferred, Expr, ExprKind, Temp, Ty};

/// Per region, the region whose memo node it uses: the first of its
/// equivalence class (itself if it is not memoizable).
pub(crate) fn memo_classes(regions: &[Region], memo_ok: &[bool], s1_reads: &[Option<Vec<u32>>], prog: &Program) -> Vec<u32> {
    let mut classes: Vec<u32> = (0..regions.len() as u32).collect();
    // Candidates by a hash of what equivalence preserves; each bucket
    // holds the representatives of its classes.
    let mut buckets: HashMap<u64, Vec<u32>> = HashMap::new();
    for (rid, r) in regions.iter().enumerate() {
        if !memo_ok[rid] {
            continue;
        }
        let mut h = std::collections::hash_map::DefaultHasher::new();
        key_layout(r, &s1_reads[rid]).hash(&mut h);
        skeleton(&r.expr, &mut h);
        let reps = buckets.entry(h.finish()).or_default();
        match reps.iter().find(|&&q| equivalent(&regions[q as usize], r, &s1_reads[q as usize], &s1_reads[rid], prog)) {
            Some(&q) => classes[rid] = q,
            None => reps.push(rid as u32),
        }
    }
    classes
}

/// What lays out a region's memo key (besides its inputs' types): whether
/// it has a current state, the variables it reads, and whether it is
/// inside `ENABLED`.
fn key_layout<'a>(r: &'a Region, s1_reads: &'a Option<Vec<u32>>) -> (bool, bool, &'a Option<super::mixed::Reads>, &'a Option<Vec<u32>>) {
    (r.ctx == RegionCtx::Init, r.info.enabled, &r.info.reads, s1_reads)
}

/// Feed the node kinds and types of `e` to `h` (invariant under temp
/// renaming), and the identity of interpreter fallbacks.
fn skeleton(e: &Expr, h: &mut impl Hasher) {
    std::mem::discriminant(&*e.kind).hash(h);
    e.ty.hash(h);
    if let ExprKind::Interp { expr, .. } = &*e.kind {
        (Arc::as_ptr(&expr.kind) as usize).hash(h);
    }
    e.for_each_child(&mut |c| skeleton(c, h));
}

/// Whether regions `a` and `b` (both memoizable) compute the same value
/// from the same memo key.
fn equivalent(a: &Region, b: &Region, a_s1: &Option<Vec<u32>>, b_s1: &Option<Vec<u32>>, prog: &Program) -> bool {
    if key_layout(a, a_s1) != key_layout(b, b_s1) || a.inputs.len() != b.inputs.len() {
        return false;
    }
    // A region that reads the next state sees the variables assigned at
    // its call site.
    if a_s1.as_ref().is_some_and(|v| !v.is_empty()) && (a.ctx != b.ctx || a.assigned != b.assigned) {
        return false;
    }
    let mut m = Renaming { ta: &a.temps, tb: &b.temps, ab: HashMap::new(), ba: HashMap::new(), prog };
    a.inputs.iter().zip(&b.inputs).all(|(&x, &y)| m.bind(x, y)) && m.expr(&a.expr, &b.expr)
}

/// A bijection between the temps of two regions, built while comparing
/// their expressions.
struct Renaming<'a> {
    ta: &'a [Ty],
    tb: &'a [Ty],
    ab: HashMap<Temp, Temp>,
    ba: HashMap<Temp, Temp>,
    prog: &'a Program,
}

impl Renaming<'_> {
    /// Map `x` to `y` (a binder or an input): consistent with the mapping
    /// so far, and of the same type.
    fn bind(&mut self, x: Temp, y: Temp) -> bool {
        match (self.ab.get(&x), self.ba.get(&y)) {
            (Some(&y2), Some(&x2)) => y2 == y && x2 == x,
            (None, None) => {
                let same = matches!((self.ta.get(x as usize), self.tb.get(y as usize)), (Some(s), Some(t)) if s == t);
                if same {
                    self.ab.insert(x, y);
                    self.ba.insert(y, x);
                }
                same
            }
            _ => false,
        }
    }

    /// A temp read: it must be mapped already.
    fn temp(&self, x: Temp, y: Temp) -> bool {
        self.ab.get(&x) == Some(&y)
    }

    fn all(&mut self, xs: &[Expr], ys: &[Expr]) -> bool {
        xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| self.expr(x, y))
    }

    fn expr(&mut self, a: &Expr, b: &Expr) -> bool {
        use ExprKind::*;
        if a.ty != b.ty {
            return false;
        }
        match (&*a.kind, &*b.kind) {
            (OrderedSet { set: x, plan: a }, OrderedSet { set: y, plan: b }) => a == b && self.expr(x, y),
            (Const(x), Const(y)) => same_constant(x, y),
            (ConstWords(x), ConstWords(y)) => x == y,
            (Var(x), Var(y)) | (NextVar(x), NextVar(y)) => x == y,
            (Temp(x), Temp(y)) => self.temp(*x, *y),
            (Not(x), Not(y))
            | (Neg(x), Neg(y))
            | (Convert(x), Convert(y))
            | (BitCard(x), BitCard(y))
            | (Rank(x), Rank(y))
            | (SeqLen(x), SeqLen(y))
            | (Subsets(x), Subsets(y)) => self.expr(x, y),
            (And(xs), And(ys)) | (Or(xs), Or(ys)) | (Concat(xs), Concat(ys)) | (BitSet(xs), BitSet(ys)) | (Tuple(xs), Tuple(ys)) => {
                self.all(xs, ys)
            }
            (Pack { locs: la, parts: xs }, Pack { locs: lb, parts: ys }) => la == lb && self.all(xs, ys),
            (If(x1, x2, x3), If(y1, y2, y3)) => self.expr(x1, y1) && self.expr(x2, y2) && self.expr(x3, y3),
            (IntBin(o, x1, x2), IntBin(p, y1, y2)) => o == p && self.expr(x1, y1) && self.expr(x2, y2),
            (IntCmp(o, x1, x2), IntCmp(p, y1, y2)) => o == p && self.expr(x1, y1) && self.expr(x2, y2),
            (BitSetOp(o, x1, x2), BitSetOp(p, y1, y2)) => o == p && self.expr(x1, y1) && self.expr(x2, y2),
            (Eq(x1, x2), Eq(y1, y2))
            | (Apply(x1, x2), Apply(y1, y2))
            | (IntRange(x1, x2), IntRange(y1, y2))
            | (MapMerge(x1, x2), MapMerge(y1, y2)) => self.expr(x1, y1) && self.expr(x2, y2),
            (Exists { bind: t, set: x1, body: x2 }, Exists { bind: u, set: y1, body: y2 })
            | (Forall { bind: t, set: x1, body: x2 }, Forall { bind: u, set: y1, body: y2 })
            | (Choose { bind: t, set: x1, body: x2 }, Choose { bind: u, set: y1, body: y2 })
            | (Let { temp: t, value: x1, body: x2 }, Let { temp: u, value: y1, body: y2 })
            | (Filter { bind: t, set: x1, pred: x2 }, Filter { bind: u, set: y1, pred: y2 })
            | (Collect { bind: t, set: x1, elem: x2 }, Collect { bind: u, set: y1, elem: y2 }) => {
                self.bind(*t, *u) && self.expr(x1, y1) && self.expr(x2, y2)
            }
            (Fold { product: p, bind: t, set: x1, body: x2 }, Fold { product: q, bind: u, set: y1, body: y2 }) => {
                p == q && self.bind(*t, *u) && self.expr(x1, y1) && self.expr(x2, y2)
            }
            (UnionFold { bind: t, set: x1, body: x2 }, UnionFold { bind: u, set: y1, body: y2 }) => {
                self.bind(*t, *u) && self.expr(x1, y1) && self.expr(x2, y2)
            }
            (MapSet { bind: t, set: x1, elem: x2, cond: x3 }, MapSet { bind: u, set: y1, elem: y2, cond: y3 }) => {
                self.bind(*t, *u)
                    && self.expr(x1, y1)
                    && self.expr(x2, y2)
                    && match (x3, y3) {
                        (None, None) => true,
                        (Some(x), Some(y)) => self.expr(x, y),
                        _ => false,
                    }
            }
            (SeqFilter { bind: t, seq: x1, pred: x2, slot: w }, SeqFilter { bind: u, seq: y1, pred: y2, slot: v }) => {
                w == v && self.bind(*t, *u) && self.expr(x1, y1) && self.expr(x2, y2)
            }
            (MapBuild { bind: t, set: x1, rank: x2, value: x3 }, MapBuild { bind: u, set: y1, rank: y2, value: y3 }) => {
                self.bind(*t, *u) && self.expr(x1, y1) && self.expr(x2, y2) && self.expr(x3, y3)
            }
            (ValField(x, f), ValField(y, g)) => f == g && self.expr(x, y),
            (Slice { base: x, loc: o }, Slice { base: y, loc: p }) => o == p && self.expr(x, y),
            (Index { base: x1, arg: x2, map: m, slot: w }, Index { base: y1, arg: y2, map: n, slot: v }) => {
                w == v && m == n && self.expr(x1, y1) && self.expr(x2, y2)
            }
            (ExceptAt { base: x1, loc: o, value: x2 }, ExceptAt { base: y1, loc: p, value: y2 }) => {
                o == p && self.expr(x1, y1) && self.expr(x2, y2)
            }
            (
                ExceptIndex { base: x1, arg: x2, map: m, slot: w, value: x3 },
                ExceptIndex { base: y1, arg: y2, map: n, slot: v, value: y3 },
            ) => w == v && m == n && self.expr(x1, y1) && self.expr(x2, y2) && self.expr(x3, y3),
            (BitMember { set: x1, rank: x2 }, BitMember { set: y1, rank: y2 })
            | (MapGet { base: x1, rank: x2 }, MapGet { base: y1, rank: y2 }) => self.expr(x1, y1) && self.expr(x2, y2),
            (SeqIndex { base: x1, arg: x2, slot: w }, SeqIndex { base: y1, arg: y2, slot: v }) => {
                w == v && self.expr(x1, y1) && self.expr(x2, y2)
            }
            (SortedMember { set: x1, elem: x2, elem_words: w }, SortedMember { set: y1, elem: y2, elem_words: v }) => {
                w == v && self.expr(x1, y1) && self.expr(x2, y2)
            }
            (SeqTail { base: x, slot: w }, SeqTail { base: y, slot: v }) => w == v && self.expr(x, y),
            (SeqAppend { base: x1, value: x2, slot: w, max_len: l }, SeqAppend { base: y1, value: y2, slot: v, max_len: k })
            | (SeqConcat { a: x1, b: x2, slot: w, max_len: l }, SeqConcat { a: y1, b: y2, slot: v, max_len: k }) => {
                w == v && l == k && self.expr(x1, y1) && self.expr(x2, y2)
            }
            (
                SortedInsert { set: x1, elem: x2, elem_words: w, max_card: l },
                SortedInsert { set: y1, elem: y2, elem_words: v, max_card: k },
            ) => w == v && l == k && self.expr(x1, y1) && self.expr(x2, y2),
            (SeqSub { base: x1, lo: x2, hi: x3, slot: w }, SeqSub { base: y1, lo: y2, hi: y3, slot: v }) => {
                w == v && self.expr(x1, y1) && self.expr(x2, y2) && self.expr(x3, y3)
            }
            (
                SortedOp { op: o, a: x1, b: x2, elem_words: w, max_card: l },
                SortedOp { op: p, a: y1, b: y2, elem_words: v, max_card: k },
            ) => o == p && w == v && l == k && self.expr(x1, y1) && self.expr(x2, y2),
            (UnionField { base: x, locs: o }, UnionField { base: y, locs: p }) => o == p && self.expr(x, y),
            (UnionFieldInt { base: x, entries: o }, UnionFieldInt { base: y, entries: p }) => o == p && self.expr(x, y),
            (ConstElems { elem: s, words: w, count: n }, ConstElems { elem: t, words: v, count: k }) => s == t && w == v && n == k,
            (Fail(x), Fail(y)) => x == y,
            (RankFlat { x, radices: r }, RankFlat { x: y, radices: s }) => r == s && self.expr(x, y),
            (Recode { x, arm_base: a1, table: t1, words: w }, Recode { x: y, arm_base: a2, table: t2, words: v }) => {
                a1 == a2 && t1 == t2 && w == v && self.expr(x, y)
            }
            (RankUnion { x, arms: r }, RankUnion { x: y, arms: s }) => r == s && self.expr(x, y),
            (Lookup { x, table: r }, Lookup { x: y, table: s }) => r == s && self.expr(x, y),
            (MapPut { base: x1, rank: x2, value: x3, plan: i }, MapPut { base: y1, rank: y2, value: y3, plan: j }) => {
                i == j && self.expr(x1, y1) && self.expr(x2, y2) && self.expr(x3, y3)
            }
            (Call { func: f, args: xs }, Call { func: g, args: ys }) => f == g && self.all(xs, ys),
            (ValOp { op: o, args: xs }, ValOp { op: p, args: ys }) => o == p && self.all(xs, ys),
            (RefOp { op: o, args: xs }, RefOp { op: p, args: ys }) => o == p && self.all(xs, ys),
            (RefElems(x), RefElems(y)) => self.expr(x, y),
            (Interp { expr: x, binds: xb, deferred: xd, env: xe }, Interp { expr: y, binds: yb, deferred: yd, env: ye }) => {
                Arc::ptr_eq(&x.kind, &y.kind)
                    && x.span == y.span
                    && xb.len() == yb.len()
                    && xb.iter().zip(yb).all(|((l, x), (k, y))| l == k && self.expr(x, y))
                    && xd.len() == yd.len()
                    && xd.iter().zip(yd).all(|(x, y)| same_deferred(x, y))
                    && xe.same_bindings(ye, self.prog)
            }
            // Different kinds, or `ENABLED` (its statement tree is not
            // compared: a region with one has no twin).
            (
                OrderedSet { .. }
                | Const(_)
                | ConstWords(_)
                | Var(_)
                | NextVar(_)
                | Temp(_)
                | Not(_)
                | And(_)
                | Or(_)
                | If(..)
                | IntBin(..)
                | IntCmp(..)
                | Neg(_)
                | Eq(..)
                | Convert(_)
                | Exists { .. }
                | Forall { .. }
                | Choose { .. }
                | Let { .. }
                | Apply(..)
                | ValField(..)
                | Slice { .. }
                | Index { .. }
                | ExceptAt { .. }
                | ExceptIndex { .. }
                | BitMember { .. }
                | BitSetOp(..)
                | BitCard(_)
                | Rank(_)
                | Concat(_)
                | Pack { .. }
                | BitSet(_)
                | SeqLen(_)
                | SeqIndex { .. }
                | SeqTail { .. }
                | SeqAppend { .. }
                | SeqSub { .. }
                | SortedOp { .. }
                | SeqFilter { .. }
                | SeqConcat { .. }
                | UnionField { .. }
                | UnionFieldInt { .. }
                | ConstElems { .. }
                | IntRange(..)
                | Subsets(_)
                | Fail(_)
                | Filter { .. }
                | MapSet { .. }
                | Collect { .. }
                | Fold { .. }
                | UnionFold { .. }
                | RankFlat { .. }
                | Recode { .. }
                | RankUnion { .. }
                | Lookup { .. }
                | SortedMember { .. }
                | SortedInsert { .. }
                | MapGet { .. }
                | MapPut { .. }
                | MapBuild { .. }
                | MapMerge(..)
                | Enabled(_)
                | Tuple(_)
                | Call { .. }
                | ValOp { .. }
                | RefOp { .. }
                | RefElems(_)
                | Interp { .. },
                _,
            ) => false,
        }
    }
}

/// The same call-by-name or operator argument (by HIR node identity).
fn same_deferred(x: &Deferred, y: &Deferred) -> bool {
    match (x, y) {
        (Deferred::Thunk(l, a), Deferred::Thunk(k, b)) | (Deferred::Once(l, a), Deferred::Once(k, b)) => {
            l == k && Arc::ptr_eq(&a.kind, &b.kind)
        }
        (Deferred::Lambda(l, p, a), Deferred::Lambda(k, q, b)) => l == k && p == q && Arc::ptr_eq(&a.kind, &b.kind),
        (Deferred::OpRef(l, a), Deferred::OpRef(k, b)) => l == k && a == b,
        _ => false,
    }
}

/// Extensional equality discards lookup witnesses, including nested FcnDom.
/// Reuse the memo key's exact representation policy without forcing lazy values.
fn same_constant(x: &tlx_value::Value, y: &tlx_value::Value) -> bool {
    let (mut a, mut b) = (Vec::new(), Vec::new());
    crate::exec::memo::push_value(x, &mut a) && crate::exec::memo::push_value(y, &mut b) && a == b
}

#[cfg(test)]
mod tests {
    use super::same_constant;
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };
    use tlx_value::{lazy::LazyFcn, Value};

    #[derive(Debug)]
    struct Effect(Arc<AtomicUsize>);
    impl LazyFcn for Effect {
        fn domain(&self) -> tlx_value::Result<Value> {
            self.0.fetch_add(1, Ordering::Relaxed);
            Ok(Value::Interval(0, 0))
        }
        fn apply(&self, _: &Value) -> tlx_value::Result<Value> {
            self.0.fetch_add(1, Ordering::Relaxed);
            Ok(Value::Int(7))
        }
    }

    #[test]
    fn constant_equivalence_does_not_force_lazy_values() {
        let calls = Arc::new(AtomicUsize::new(0));
        let a = Value::tuple(vec![Value::LazyFcn(Arc::new(Effect(calls.clone())))]);
        let b = Value::tuple(vec![Value::LazyFcn(Arc::new(Effect(calls.clone())))]);
        assert!(!same_constant(&a, &b));
        assert_eq!(calls.load(Ordering::Relaxed), 0);
    }
}
