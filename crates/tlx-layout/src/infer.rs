//! Speculative shape inference from observed states (design.md §6.5).
//!
//! Headroom policy (applied by `Observer::finalize` to every node, and by
//! `widen` to the nodes that a miss changed):
//! - integer ranges: see `widen_int` (include 0, pad by max(2, 50%));
//! - set `max_card` and sequence `max_len`: `max(2n, n + 2)` (a set's
//!   `max_card` is capped at the size of its element universe, when finite);
//!   a bitset-encoded set that is not part of a set element admits every
//!   subset of its universe (see `set_headroom`); a bound that a miss grew
//!   gets the same (see `grow_len`);
//! - atom universes: extended with the hint atoms of the same kind
//!   (`finalize` only); a typed model value (`T_x`) is only extended with
//!   hint model values of its own TLC type (see `extend_atoms`).

use crate::decisions::{in_slot, Slot};
use std::sync::Arc;

use tlx_value::{Sym, Value};

use crate::shape::{fcn_dom_matches_record, fcn_dom_matches_tuple, set_shape, Shape};

/// Static information that widens observed shapes.
#[derive(Clone, Debug, Default)]
pub struct Hints {
    /// Atoms (model values, strings) that may appear anywhere: atom universes
    /// are extended with all hint atoms of the same kind (model values with
    /// model values, strings with strings), and a typed model value only with
    /// hint model values of its own TLC type (see `extend_atoms`).
    pub atoms: Vec<Value>,
    /// Integer ranges that values plausibly span (e.g. `1..N` from constant
    /// definitions): an observed range is extended to the hint ranges it
    /// overlaps or touches before headroom is added.
    pub int_ranges: Vec<(i64, i64)>,
}

fn extend_int(mut lo: i64, mut hi: i64, hints: &Hints) -> (i64, i64) {
    loop {
        let (olo, ohi) = (lo, hi);
        for &(a, b) in &hints.int_ranges {
            if a <= hi.saturating_add(1) && b >= lo.saturating_sub(1) {
                lo = lo.min(a);
                hi = hi.max(b);
            }
        }
        if (lo, hi) == (olo, ohi) {
            return (lo, hi);
        }
    }
}

/// Accumulates observations per variable.
#[derive(Clone, Debug)]
pub struct Observer {
    pub shapes: Vec<Shape>,
    /// The layout slot of each observed position, for `decisions` (None:
    /// position i is variable i).
    slots: Option<Arc<[Slot]>>,
}

impl Observer {
    pub fn new(nvars: usize) -> Observer {
        Observer { shapes: vec![Shape::Never; nvars], slots: None }
    }

    /// An observer of the values of `slots` (e.g. materialized
    /// definitions), position by position.
    pub fn for_slots(slots: Vec<Slot>) -> Observer {
        Observer { shapes: vec![Shape::Never; slots.len()], slots: Some(slots.into()) }
    }

    fn slot(slots: &Option<Arc<[Slot]>>, i: usize) -> Slot {
        slots.as_ref().map_or(Slot::Var(i as u32), |s| s[i])
    }

    /// Observe a state; true if that changed some shape.
    pub fn observe(&mut self, state: &[Value]) -> bool {
        let mut changed = false;
        for (i, (s, v)) in self.shapes.iter_mut().zip(state).enumerate() {
            // Fast path: joining a contained value does not change the shape.
            if !s.contains(v) {
                *s = in_slot(Self::slot(&self.slots, i), || s.join(&Shape::of(v)));
                changed = true;
            }
        }
        changed
    }

    /// `observe`, where an atom universe that holds more than
    /// `MAX_OBSERVED_STRINGS` computed strings (atoms that are not `hints`)
    /// becomes `Dyn`: such universes are open-ended (every state may make
    /// new strings, e.g. `s' = s \o ToString(i)`), and observing and
    /// choosing layouts from them costs time linear in their size per new
    /// string (the pre-run spent its whole budget on 10k strings).
    pub fn observe_with(&mut self, state: &[Value], hints: &Hints) -> bool {
        let mut changed = false;
        for (i, (s, v)) in self.shapes.iter_mut().zip(state).enumerate() {
            if !s.contains(v) {
                *s = in_slot(Self::slot(&self.slots, i), || {
                    let j = s.join(&Shape::of(v));
                    cap_strings(&j, hints).unwrap_or(j)
                });
                changed = true;
            }
        }
        changed
    }

    /// Turn observed shapes into layout shapes: widen integer ranges
    /// (`widen_int`), extend atom universes with hints, give sets/sequences
    /// headroom on `max_card`/`max_len`.
    pub fn finalize(&self, hints: &Hints) -> Vec<Shape> {
        self.shapes.iter().enumerate().map(|(i, s)| in_slot(Self::slot(&self.slots, i), || headroom(&s.homogenize(), hints))).collect()
    }
}

/// Most computed strings an observed atom universe holds (see
/// `Observer::observe_with`).
pub const MAX_OBSERVED_STRINGS: usize = 1024;

/// `s` with the atom universes holding more than `MAX_OBSERVED_STRINGS`
/// computed strings replaced by `Dyn` (None: no such universe). As in
/// `escalate`, a `Dyn` element makes a union or a map `Dyn` as a whole.
fn cap_strings(s: &Shape, hints: &Hints) -> Option<Shape> {
    let cap = |s: &Shape| cap_strings(s, hints);
    match s {
        // (Computed strings are at least the atoms that are not hints.)
        Shape::Atom(u) => (u.len() > MAX_OBSERVED_STRINGS + hints.atoms.len()).then(|| {
            crate::decisions::note(|| format!("Dyn: more than {MAX_OBSERVED_STRINGS} computed strings observed"));
            Shape::Dyn
        }),
        Shape::Never | Shape::Bool | Shape::Int { .. } | Shape::Dyn | Shape::Ref(_) => None,
        Shape::Set { elem, max_card } => Some(set_shape(cap(elem)?, *max_card)),
        Shape::Seq { elem, max_len } => Some(Shape::Seq { elem: Box::new(cap(elem)?), max_len: *max_len }),
        Shape::Fcn { dom, range, witness, key_variants } => {
            Some(Shape::Fcn { dom: dom.clone(), range: Box::new(cap(range)?), witness: *witness, key_variants: key_variants.clone() })
        }
        Shape::Map { key, range, witness } => {
            let (k, r) = (cap(key), cap(range));
            if k.is_none() && r.is_none() {
                return None;
            }
            Some(crate::shape::map_shape(k.unwrap_or_else(|| (**key).clone()), r.unwrap_or_else(|| (**range).clone()), *witness))
        }
        Shape::Record(fs) => {
            let capped: Vec<Option<Shape>> = fs.iter().map(|(_, f)| cap(f)).collect();
            if capped.iter().all(Option::is_none) {
                return None;
            }
            Some(Shape::Record(fs.iter().zip(capped).map(|((k, f), c)| (*k, c.unwrap_or_else(|| f.clone()))).collect()))
        }
        Shape::Tuple(es) => {
            let capped: Vec<Option<Shape>> = es.iter().map(cap).collect();
            if capped.iter().all(Option::is_none) {
                return None;
            }
            Some(Shape::Tuple(es.iter().zip(capped).map(|(e, c)| c.unwrap_or_else(|| e.clone())).collect()))
        }
        Shape::Union(arms) => arms.iter().any(|a| cap(a).is_some()).then_some(Shape::Dyn),
    }
}

/// Widen a shape so that it also contains `v` (after a layout miss), with
/// headroom to avoid repeated misses (e.g. doubling integer ranges).
///
/// Only the parts of the shape that had to change get new headroom; parts
/// that already contained the corresponding sub-values are kept as is.
pub fn widen(s: &Shape, v: &Value) -> Shape {
    widen_with(s, v, &Hints::default())
}

/// `widen` using static hints for the parts that grow.
pub fn widen_with(s: &Shape, v: &Value, hints: &Hints) -> Shape {
    let o = Shape::of(v).homogenize();
    let j = s.join(&o).homogenize();
    grow(s, &j, Some(&o), hints)
}

/// `widen_with` for a shape that already missed `prior` times, such that
/// open-ended growth converges in a few misses:
/// - an integer range in a value position (not a set element or map key,
///   whose ranges size the encoding) that grows again is extended by its
///   span times `4^prior` beyond the value on the side that grew (a
///   counter running far beyond what the pre-run saw), then gets the usual
///   headroom;
/// - an atom universe that grows by a string is replaced by `Dyn` when it
///   already held a computed string (one that is not a hint, i.e. not a
///   literal of the spec: values of `ToString`, `\o`, ...), or when the
///   shape missed twice before: such universes are open-ended, and every
///   new value would miss again. Model values are finite (the hints hold
///   all of them) and keep their universe. A `Dyn` element makes a union
///   (arms need a kind) or a map key `Dyn` as a whole.
pub fn widen_repeated(s: &Shape, v: &Value, hints: &Hints, prior: u32) -> Shape {
    let o = Shape::of(v).homogenize();
    let j = s.join(&o).homogenize();
    let e = escalate(s, &j, hints, prior, true);
    grow(s, &e, Some(&o), hints)
}

/// Whether atom universe `u0`, grown to `u`, is open-ended (see
/// `widen_repeated`).
fn open_ended(u0: &[Value], u: &[Value], hints: &Hints, prior: u32) -> bool {
    let computed = |a: &Value| matches!(a, Value::Str(_)) && !hints.atoms.contains(a);
    let grew_by_string = u.iter().any(|a| matches!(a, Value::Str(_)) && u0.binary_search(a).is_err());
    grew_by_string && (prior >= 2 || u0.iter().any(computed))
}

fn open_dyn() -> Shape {
    crate::decisions::note(|| "Dyn: open-ended string universe grew on a layout miss".to_string());
    Shape::Dyn
}

/// The parts of `new` (the join of `old` and a value that missed) that
/// grew, escalated as described in `widen_repeated` (before the usual
/// headroom); `value` = in a value position.
fn escalate(old: &Shape, new: &Shape, hints: &Hints, prior: u32, value: bool) -> Shape {
    if old == new {
        return new.clone();
    }
    match (old, new) {
        (Shape::Int { lo: l0, hi: h0 }, Shape::Int { lo, hi }) if value && prior > 0 => {
            let span = (hi - lo).max(1);
            let pad = span.saturating_mul(1i64 << (2 * prior.min(15)));
            let (mut lo, mut hi) = (*lo, *hi);
            if hi > *h0 {
                hi = hi.max(hi.saturating_add(pad).min(i32::MAX as i64));
            }
            if lo < *l0 {
                lo = lo.min(lo.saturating_sub(pad).max(i32::MIN as i64));
            }
            Shape::Int { lo, hi }
        }
        (Shape::Atom(u0), Shape::Atom(u)) if open_ended(u0, u, hints, prior) => open_dyn(),
        (Shape::Never, Shape::Atom(u)) if open_ended(&[], u, hints, prior) => open_dyn(),
        (Shape::Set { elem: e1, .. }, Shape::Set { elem: e2, max_card }) => set_shape(escalate(e1, e2, hints, prior, false), *max_card),
        (Shape::Seq { elem: e1, .. }, Shape::Seq { elem: e2, max_len }) => {
            Shape::Seq { elem: Box::new(escalate(e1, e2, hints, prior, true)), max_len: *max_len }
        }
        (Shape::Fcn { range: r1, .. }, Shape::Fcn { dom, range: r2, witness, key_variants }) => Shape::Fcn {
            dom: dom.clone(),
            range: Box::new(escalate(r1, r2, hints, prior, true)),
            witness: *witness,
            key_variants: key_variants.clone(),
        },
        (Shape::Map { key: k1, range: r1, .. }, Shape::Map { key: k2, range: r2, witness }) => {
            crate::shape::map_shape(escalate(k1, k2, hints, prior, false), escalate(r1, r2, hints, prior, true), *witness)
        }
        (Shape::Record(f1), Shape::Record(f2)) if f1.len() == f2.len() => {
            Shape::Record(f1.iter().zip(f2.iter()).map(|(a, b)| (b.0, escalate(&a.1, &b.1, hints, prior, value))).collect())
        }
        (Shape::Tuple(t1), Shape::Tuple(t2)) if t1.len() == t2.len() => {
            Shape::Tuple(t1.iter().zip(t2.iter()).map(|(a, b)| escalate(a, b, hints, prior, value)).collect())
        }
        (_, Shape::Union(arms)) => {
            let old_arms: &[Shape] = match old {
                Shape::Union(a) => a,
                _ => std::slice::from_ref(old),
            };
            let arms: Vec<Shape> = arms
                .iter()
                .map(|a| match old_arms.iter().find(|o| o.kind_key() == a.kind_key()) {
                    Some(o) => escalate(o, a, hints, prior, value),
                    None => escalate(&Shape::Never, a, hints, prior, value),
                })
                .collect();
            if arms.contains(&Shape::Dyn) {
                Shape::Dyn
            } else {
                Shape::Union(Arc::from(arms))
            }
        }
        _ => new.clone(),
    }
}

/// Headroom for an observed integer range `lo..=hi`: the range is extended
/// to include 0; the upper bound is padded by `max(2, (hi - lo) / 2)` unless
/// the range is negative (then it becomes 0), and the lower bound is padded
/// likewise only if it is negative (a non-negative range stays non-negative;
/// `{0}` grows upwards). The result is clamped to the 32-bit range of TLC
/// integers (never narrower than the input).
pub fn widen_int(lo: i64, hi: i64) -> (i64, i64) {
    let pad = ((hi.saturating_sub(lo)) / 2).max(2);
    let nlo = if lo >= 0 { 0 } else { lo.saturating_sub(pad).max(i32::MIN as i64).min(lo) };
    let nhi = if hi < 0 { 0 } else { hi.saturating_add(pad).min(i32::MAX as i64).max(hi) };
    (nlo, nhi)
}

/// Headroom for a cardinality (or sequence length) `n`, both for an
/// observation and for a bound that a layout miss grew.
///
/// After a miss, a smaller step (`n` plus a quarter, at least 4) was tried:
/// it shrinks layouts that overshoot when the missing value is a rare deep
/// state (MultiPaxos_MC_small: `msgs` 24 -> 31 instead of 50, 321 instead of
/// 473 state words, instructions within 4%), but a value that keeps growing
/// with the depth then misses again, later in a larger search, and late
/// misses are the expensive ones: once the archive of visited states is over
/// `TLX_RETAIN_MB` the search starts over instead of resuming. MultiPaxos_MC
/// (37M states) went 24 -> 31, missed again at 32 after 15.8M states and
/// started over: 54M states expanded instead of 37M, 1.45x the CPU time. A
/// bound that overshoots costs a few words per state; one that undershoots
/// can cost the whole search so far.
fn grow_len(n: usize) -> usize {
    n.saturating_mul(2).max(n.saturating_add(2))
}

/// Headroom for a set of `max_card` elements. A set encoded as a bitset
/// takes the same words whatever its `max_card`, which then only bounds
/// the values the layout admits: compiled code checks it where a set may
/// grow, and a set that keeps growing (a message set) misses and
/// restarts the search once or twice. Unless the set is part of a set
/// element (`in_elem`: there `max_card` sizes the enclosing set's universe
/// and the ranks of its elements), it admits every subset.
fn set_headroom(elem: Shape, max_card: usize, in_elem: bool) -> Shape {
    let mut m = grow_len(max_card);
    if let Some(n) = elem.cardinality() {
        let n_usize = usize::try_from(n).unwrap_or(usize::MAX);
        m = m.min(n_usize).max(max_card);
        if crate::layout::bitset_universe(&elem).is_some() {
            if !in_elem {
                m = n_usize.max(max_card);
            } else if n <= 62 {
                // When the full powerset (2^n) fits in the same 64-bit bitset
                // word count as the capped subset universe (within
                // MAX_BITSET_UNIVERSE), widening max_card to n costs zero extra
                // words and enables direct bitmask ranking (`word_ranked_set`)
                // for nested bitsets.
                let full_card = 1u64 << n;
                if full_card <= crate::shape::MAX_BITSET_UNIVERSE {
                    let cur_card = set_shape(elem.clone(), m).cardinality().unwrap_or(u64::MAX);
                    if full_card.div_ceil(64) <= cur_card.div_ceil(64) && full_card <= cur_card.saturating_mul(2) {
                        m = n_usize.max(max_card);
                    }
                }
            }
        }
    }
    set_shape(elem, m)
}

/// The hint atoms that extend an observed atom universe: the strings when the
/// universe holds one, the model values when it holds one, and — for the
/// typed model values — only those of a type the universe already holds.
///
/// TLC refuses to compare two typed model values of different types
/// (`V/ModelValue.java`), so a value of another type is not a value of a
/// field that holds values of one type, and widening it in would only make
/// the field's shape incomparable without saving a miss: `tlx-compile`'s
/// `shapes_comparable` then rejects every set whose elements are records with
/// that field (CCF's `{history[i] : ...}` is a union of such records) and the
/// whole set stays in the interpreter. A field that does take a value of
/// another type is a layout miss, widened by `widen`/`widen_repeated` to the
/// universe that holds both types. Untyped model values compare with
/// anything, so they keep extending any universe that holds a model value.
fn extend_atoms(u: &Arc<[Value]>, hints: &Hints) -> Arc<[Value]> {
    let has_mv = u.iter().any(|a| matches!(a, Value::ModelValue(_)));
    let has_str = u.iter().any(|a| matches!(a, Value::Str(_)));
    let mv_types: Vec<char> = u
        .iter()
        .filter_map(|a| match a {
            Value::ModelValue(m) => m.model_value_type(),
            _ => None,
        })
        .collect();
    let extra: Vec<&Value> = hints
        .atoms
        .iter()
        .filter(|h| match h {
            Value::ModelValue(m) => has_mv && m.model_value_type().is_none_or(|t| mv_types.contains(&t)),
            Value::Str(_) => has_str,
            _ => false,
        })
        .filter(|h| u.binary_search(h).is_err())
        .collect();
    if extra.is_empty() {
        return u.clone();
    }
    let mut all: Vec<Value> = u.iter().cloned().chain(extra.into_iter().cloned()).collect();
    all.sort();
    all.dedup();
    Arc::from(all)
}

/// Apply the headroom policy to every node of `s`.
fn headroom(s: &Shape, hints: &Hints) -> Shape {
    headroom_at(s, hints, false)
}

/// `headroom`; `in_elem`: `s` is part of a set element or map key.
fn headroom_at(s: &Shape, hints: &Hints, in_elem: bool) -> Shape {
    let headroom = |s: &Shape, hints: &Hints| headroom_at(s, hints, in_elem);
    match s {
        Shape::Never | Shape::Bool | Shape::Dyn | Shape::Ref(_) => s.clone(),
        Shape::Int { lo, hi } => {
            let (lo, hi) = extend_int(*lo, *hi, hints);
            let (lo, hi) = widen_int(lo, hi);
            Shape::Int { lo, hi }
        }
        Shape::Atom(u) => Shape::Atom(extend_atoms(u, hints)),
        Shape::Set { elem, max_card } => set_headroom(headroom_at(elem, hints, true), *max_card, in_elem),
        Shape::Fcn { dom, range, witness, key_variants } => {
            Shape::Fcn { dom: dom.clone(), range: Box::new(headroom(range, hints)), witness: *witness, key_variants: key_variants.clone() }
        }
        Shape::Map { key, range, witness } => {
            // Widen the key universe only while the map stays compact, and
            // keys that are strings not by the spec's strings: a map over
            // strings is usually a record built with `:>` and `@@` (its
            // keys are the strings observed; another one is a layout miss,
            // whose widening adds them all, see `grow_at`). (Atoms inside
            // composite keys, e.g. message records of a bag, do take them:
            // the arms of a union key then share one atom universe.)
            let range = headroom(range, hints);
            let strings = matches!(&**key, Shape::Atom(u) if u.iter().all(|a| matches!(a, Value::Str(_))));
            let key_hints = match strings {
                true => Hints { atoms: hints.atoms.iter().filter(|a| !matches!(a, Value::Str(_))).cloned().collect(), ..hints.clone() },
                false => hints.clone(),
            };
            [headroom_at(key, &key_hints, true), (**key).clone()]
                .into_iter()
                .map(|k| crate::shape::map_shape(k, range.clone(), *witness))
                .find(|m| *m != Shape::Dyn)
                .unwrap_or_else(|| s.clone())
        }
        Shape::Record(fs) => Shape::Record(fs.iter().map(|(k, f)| (*k, headroom(f, hints))).collect()),
        Shape::Tuple(es) => Shape::Tuple(es.iter().map(|e| headroom(e, hints)).collect()),
        Shape::Seq { elem, max_len } => Shape::Seq { elem: Box::new(headroom(elem, hints)), max_len: grow_len(*max_len) },
        Shape::Union(arms) => Shape::Union(arms.iter().map(|a| headroom(a, hints)).collect()),
    }
}

/// Headroom for the parts of `new` (a widening of `old` by a value of
/// shape `obs`, when known) that differ from `old`.
fn grow(old: &Shape, new: &Shape, obs: Option<&Shape>, hints: &Hints) -> Shape {
    grow_at(old, new, obs, hints, false)
}

/// The part of the observed shape `obs` that corresponds to the part `f`
/// selects (None where their structures differ).
fn obs_part<'a>(obs: Option<&'a Shape>, f: impl Fn(&'a Shape) -> Option<&'a Shape>) -> Option<&'a Shape> {
    obs.and_then(f)
}

/// `grow`; `in_elem`: part of a set element or map key (see `set_headroom`).
fn grow_at(old: &Shape, new: &Shape, obs: Option<&Shape>, hints: &Hints, in_elem: bool) -> Shape {
    let grow = |old: &Shape, new: &Shape, obs: Option<&Shape>, hints: &Hints| grow_at(old, new, obs, hints, in_elem);
    let headroom = |s: &Shape, hints: &Hints| headroom_at(s, hints, in_elem);
    if old == new {
        return new.clone();
    }
    match (old, new) {
        (Shape::Int { .. }, Shape::Int { .. }) | (Shape::Atom(_), Shape::Atom(_)) => headroom(new, hints),
        (Shape::Set { elem: e1, max_card: m1 }, Shape::Set { elem: e2, max_card: m2 }) => {
            let oset = obs_part(obs, |o| matches!(o, Shape::Set { .. }).then_some(o));
            let elem = grow_at(e1, e2, obs_part(oset, |o| if let Shape::Set { elem, .. } = o { Some(&**elem) } else { None }), hints, true);
            let was_full = crate::layout::bitset_universe(e1).is_some_and(|u| *m1 as u64 >= u);
            let bitset = crate::layout::bitset_universe(&elem).is_some();
            if was_full && !bitset && !in_elem {
                // Now a sorted array, whose size `max_card` sets: from the
                // value that missed (the bitset admitted every subset).
                let n = match oset {
                    Some(Shape::Set { max_card, .. }) => *max_card,
                    _ => *m2,
                };
                set_headroom(elem, n, in_elem)
            } else if m1 == m2 && (in_elem || !bitset) {
                set_shape(elem, *m2)
            } else {
                set_headroom(elem, *m2, in_elem)
            }
        }
        (Shape::Seq { elem: e1, max_len: l1 }, Shape::Seq { elem: e2, max_len: l2 }) => Shape::Seq {
            elem: Box::new(grow(e1, e2, obs_part(obs, |o| if let Shape::Seq { elem, .. } = o { Some(&**elem) } else { None }), hints)),
            max_len: if l1 == l2 { *l2 } else { grow_len(*l2) },
        },
        (Shape::Fcn { range: r1, .. }, Shape::Fcn { dom, range: r2, witness, key_variants }) => {
            let o = obs_part(obs, |o| if let Shape::Fcn { range, .. } = o { Some(&**range) } else { None });
            Shape::Fcn { dom: dom.clone(), range: Box::new(grow(r1, r2, o, hints)), witness: *witness, key_variants: key_variants.clone() }
        }
        (Shape::Map { key: k1, range: r1, .. }, Shape::Map { key: k2, range: r2, witness }) => {
            // Keys get headroom only while the map stays compact.
            let range = grow(r1, r2, obs_part(obs, |o| if let Shape::Map { range, .. } = o { Some(&**range) } else { None }), hints);
            [
                grow_at(k1, k2, obs_part(obs, |o| if let Shape::Map { key, .. } = o { Some(&**key) } else { None }), hints, true),
                (**k2).clone(),
            ]
            .into_iter()
            .map(|k| crate::shape::map_shape(k, range.clone(), *witness))
            .find(|m| *m != Shape::Dyn)
            .unwrap_or_else(|| new.clone())
        }
        (Shape::Record(f1), Shape::Record(f2)) if f1.len() == f2.len() => Shape::Record(
            f1.iter()
                .zip(f2.iter())
                .map(|(a, b)| {
                    let o = obs_part(obs, |o| if let Shape::Record(fs) = o { fs.iter().find(|f| f.0 == b.0).map(|f| &f.1) } else { None });
                    (b.0, grow(&a.1, &b.1, o, hints))
                })
                .collect(),
        ),
        (Shape::Tuple(t1), Shape::Tuple(t2)) if t1.len() == t2.len() => Shape::Tuple(
            t1.iter()
                .zip(t2.iter())
                .enumerate()
                .map(|(i, (a, b))| grow(a, b, obs_part(obs, |o| if let Shape::Tuple(ts) = o { ts.get(i) } else { None }), hints))
                .collect(),
        ),
        (_, Shape::Union(arms)) => {
            let old_arms: &[Shape] = match old {
                Shape::Union(a) => a,
                _ => std::slice::from_ref(old),
            };
            let obs_arms: &[Shape] = match obs {
                Some(Shape::Union(a)) => a,
                Some(o) => std::slice::from_ref(o),
                None => &[],
            };
            Shape::Union(
                arms.iter()
                    .map(|a| match old_arms.iter().find(|o| o.kind_key() == a.kind_key()) {
                        Some(o) => grow(o, a, obs_arms.iter().find(|x| x.kind_key() == a.kind_key()), hints),
                        None => headroom(a, hints),
                    })
                    .collect(),
            )
        }
        _ => headroom(new, hints),
    }
}

/// Make records with the same field names alike across `shapes` (state
/// variables and materialized definitions): each becomes the join of all of
/// them. Records with the same fields usually hold the same kind of data
/// (messages, a variable's value and the copy sent in a message, ...);
/// compiled code moves such values between slots by plain copies only if
/// their encodings agree, and one miss widens them all at once.
///
/// A join that is not a record (it can only be `Dyn`) leaves the records
/// as they were.
pub fn unify_records(shapes: &mut [Shape]) {
    // Records nested in records may change in a second round.
    for _ in 0..4 {
        let mut joined: Vec<(Vec<Sym>, Shape)> = Vec::new();
        for s in shapes.iter() {
            collect_records(s, &mut joined);
        }
        let mut changed = false;
        for s in shapes.iter_mut() {
            let n = replace_records(s, &joined);
            if n != *s {
                *s = n;
                changed = true;
            }
        }
        if !changed {
            return;
        }
    }
}

fn record_key(fs: &[(Sym, Shape)]) -> Vec<Sym> {
    fs.iter().map(|f| f.0).collect()
}

fn collect_records(s: &Shape, out: &mut Vec<(Vec<Sym>, Shape)>) {
    if let Shape::Record(fs) = s {
        let k = record_key(fs);
        match out.iter_mut().find(|e| e.0 == k) {
            Some(e) => e.1 = e.1.join(s),
            None => out.push((k, s.clone())),
        }
    }
    s.for_each_child(|c| collect_records(c, out));
}

fn replace_records(s: &Shape, joined: &[(Vec<Sym>, Shape)]) -> Shape {
    match s {
        Shape::Record(fs) => {
            let k = record_key(fs);
            match joined.iter().find(|e| e.0 == k) {
                Some((_, j @ Shape::Record(_))) => j.clone(),
                _ => Shape::Record(fs.iter().map(|(k, f)| (*k, replace_records(f, joined))).collect()),
            }
        }
        Shape::Set { elem, max_card } => {
            let e = replace_records(elem, joined);
            // A larger element universe may allow more elements.
            if e == **elem {
                s.clone()
            } else {
                set_shape(e, *max_card)
            }
        }
        Shape::Seq { elem, max_len } => Shape::Seq { elem: Box::new(replace_records(elem, joined)), max_len: *max_len },
        Shape::Fcn { dom, range, witness, key_variants } => Shape::Fcn {
            dom: dom.clone(),
            range: Box::new(replace_records(range, joined)),
            witness: *witness,
            key_variants: key_variants.clone(),
        },
        Shape::Map { key, range, witness } => {
            let m = crate::shape::map_shape(replace_records(key, joined), replace_records(range, joined), *witness);
            if m == Shape::Dyn {
                s.clone()
            } else {
                m
            }
        }
        Shape::Tuple(es) => Shape::Tuple(es.iter().map(|e| replace_records(e, joined)).collect()),
        Shape::Union(es) => Shape::Union(es.iter().map(|e| replace_records(e, joined)).collect()),
        Shape::Never | Shape::Bool | Shape::Int { .. } | Shape::Atom(_) | Shape::Dyn | Shape::Ref(_) => s.clone(),
    }
}

/// Replace the integer ranges of `s` in value positions (variables,
/// function and map ranges, record fields, tuple and sequence elements; not
/// set elements or map keys, whose ranges size the encoding) by `f(lo, hi)`
/// where it gives one.
pub fn map_value_ints(s: &Shape, f: &mut dyn FnMut(i64, i64) -> Option<(i64, i64)>) -> Shape {
    match s {
        Shape::Int { lo, hi } => match f(*lo, *hi) {
            Some((lo, hi)) => Shape::Int { lo, hi },
            None => s.clone(),
        },
        Shape::Seq { elem, max_len } => Shape::Seq { elem: Box::new(map_value_ints(elem, f)), max_len: *max_len },
        Shape::Fcn { dom, range, witness, key_variants } => Shape::Fcn {
            dom: dom.clone(),
            range: Box::new(map_value_ints(range, f)),
            witness: *witness,
            key_variants: key_variants.clone(),
        },
        Shape::Map { key, range, witness } => {
            let m = crate::shape::map_shape((**key).clone(), map_value_ints(range, f), *witness);
            if m == Shape::Dyn {
                s.clone()
            } else {
                m
            }
        }
        Shape::Record(fs) => Shape::Record(fs.iter().map(|(k, x)| (*k, map_value_ints(x, f))).collect()),
        Shape::Tuple(es) => Shape::Tuple(es.iter().map(|e| map_value_ints(e, f)).collect()),
        Shape::Union(es) => Shape::Union(es.iter().map(|e| map_value_ints(e, f)).collect()),
        Shape::Never | Shape::Bool | Shape::Atom(_) | Shape::Dyn | Shape::Ref(_) | Shape::Set { .. } => s.clone(),
    }
}

/// The integer ranges of `old` that grew in `new` (a widening of it), as
/// `(old range, new range)`, found where both have the same structure.
pub fn grown_ints(old: &Shape, new: &Shape, out: &mut Vec<((i64, i64), (i64, i64))>) {
    match (old, new) {
        (Shape::Int { lo: l0, hi: h0 }, Shape::Int { lo: l1, hi: h1 }) => {
            if (l0, h0) != (l1, h1) {
                out.push(((*l0, *h0), (*l1, *h1)));
            }
        }
        (Shape::Set { elem: a, .. }, Shape::Set { elem: b, .. })
        | (Shape::Seq { elem: a, .. }, Shape::Seq { elem: b, .. })
        | (Shape::Fcn { range: a, .. }, Shape::Fcn { range: b, .. }) => grown_ints(a, b, out),
        (Shape::Map { key: k1, range: a, .. }, Shape::Map { key: k2, range: b, .. }) => {
            grown_ints(k1, k2, out);
            grown_ints(a, b, out);
        }
        (Shape::Record(a), Shape::Record(b)) if a.len() == b.len() => a.iter().zip(b.iter()).for_each(|(x, y)| grown_ints(&x.1, &y.1, out)),
        (Shape::Tuple(a), Shape::Tuple(b)) if a.len() == b.len() => a.iter().zip(b.iter()).for_each(|(x, y)| grown_ints(x, y, out)),
        (Shape::Union(a), Shape::Union(b)) => {
            for x in a.iter() {
                if let Some(y) = b.iter().find(|y| y.kind_key() == x.kind_key()) {
                    grown_ints(x, y, out);
                }
            }
        }
        _ => {}
    }
}

/// Most elements of a constant set whose element shapes are joined one by
/// one (larger sets give no bound).
const MAX_BOUND_ELEMS: usize = 1 << 16;

/// A bound on the elements of the constant set `set` (e.g. the right side of
/// a type invariant `x \in S`): a shape containing every element, `Dyn` where
/// nothing useful is known (infinite sets, sets computed by the evaluator).
/// Lazy sets (`SUBSET`, `[S -> T]`, record sets, products, `Seq`, `\cup`,
/// ...) are bounded structurally, without enumerating them. Unbounded
/// sequence lengths and set cardinalities are `usize::MAX` (see `refine`).
pub fn set_elem_bound(set: &Value) -> Shape {
    use tlx_value::LazySet as L;
    match set {
        Value::Set(es) if es.len() <= MAX_BOUND_ELEMS => crate::shape::join_all(es.iter().map(Shape::of)),
        Value::Interval(lo, hi) => {
            if hi < lo {
                Shape::Never
            } else {
                Shape::Int { lo: *lo, hi: *hi }
            }
        }
        Value::LazySet(l) => match &**l {
            L::Enum(es) if es.len() <= MAX_BOUND_ELEMS => crate::shape::join_all(es.iter().map(Shape::of)),
            L::Enum(_) => Shape::Dyn,
            L::Subset(s) => match set_elem_bound(s) {
                Shape::Dyn => Shape::Dyn,
                elem => {
                    let max_card = tlx_value::ops::cardinality(s).ok().and_then(|n| usize::try_from(n).ok()).unwrap_or(usize::MAX);
                    set_shape(elem, max_card)
                }
            },
            // (Sets of at most |S| elements, as `SUBSET S`.)
            L::KSubset(_, s) => match set_elem_bound(s) {
                Shape::Dyn => Shape::Dyn,
                elem => {
                    let max_card = tlx_value::ops::cardinality(s).ok().and_then(|n| usize::try_from(n).ok()).unwrap_or(usize::MAX);
                    set_shape(elem, max_card)
                }
            },
            L::FcnSet(d, r) => fcn_bound(d, set_elem_bound(r)),
            L::Product(ss) => Shape::Tuple(ss.iter().map(set_elem_bound).collect()),
            L::RecordSet(fs) => Shape::Record(fs.iter().map(|(k, s)| (*k, set_elem_bound(s))).collect()),
            L::Seq(s) => Shape::Seq { elem: Box::new(set_elem_bound(s)), max_len: usize::MAX },
            L::Union(s) => match s {
                Value::Set(es) if es.len() <= MAX_BOUND_ELEMS => crate::shape::join_all(es.iter().map(set_elem_bound)),
                _ => Shape::Dyn,
            },
            L::Cup(a, b) => set_elem_bound(a).join(&set_elem_bound(b)),
            L::Cap(a, b) => match set_elem_bound(a) {
                Shape::Dyn => set_elem_bound(b),
                x => x,
            },
            L::Diff(a, _) => set_elem_bound(a),
            L::Nat | L::Int | L::StringSet | L::Any | L::Custom(_) => Shape::Dyn,
        },
        _ => Shape::Dyn,
    }
}

/// Bound on the functions from the constant set `dom` to values bounded by
/// `range`, in the representation such functions have (tuples for `1..n`,
/// records for strings, functions otherwise).
fn fcn_bound(dom: &Value, range: Shape) -> Shape {
    if range == Shape::Dyn {
        return Shape::Dyn;
    }
    let small = tlx_value::ops::cardinality(dom).is_ok_and(|n| (0..=crate::shape::MAX_BITSET_UNIVERSE as i64).contains(&n));
    let Some(keys) = small.then(|| tlx_value::ops::enumerate_normalized(dom).ok()).flatten() else { return Shape::Dyn };
    // The shape of a function with these keys, with the range filled in.
    let Ok(sample) = Value::fcn_over(dom, keys.into_iter().map(|k| (k, Value::Bool(false))).collect()) else { return Shape::Dyn };
    match Shape::of(&sample) {
        Shape::Tuple(es) => Shape::Tuple(vec![range; es.len()].into()),
        Shape::Record(fs) => Shape::Record(fs.iter().map(|(k, _)| (*k, range.clone())).collect()),
        Shape::Fcn { dom, witness, key_variants, .. } => Shape::Fcn { dom, range: Box::new(range), witness, key_variants },
        _ => Shape::Dyn,
    }
}

/// Whether every value of the observed shape `o` is in the bound `b` (a
/// `Dyn` bound part covers anything: nothing is known there).
pub fn bound_covers(b: &Shape, o: &Shape) -> bool {
    let arms = |s: &Shape| -> Vec<Shape> {
        match s {
            Shape::Union(a) => a.to_vec(),
            _ => vec![s.clone()],
        }
    };
    if matches!(o, Shape::Union(_)) || matches!(b, Shape::Union(_)) {
        let barms = arms(b);
        return arms(o)
            .iter()
            .all(|x| barms.iter().any(|y| !matches!(y, Shape::Union(_)) && !matches!(x, Shape::Union(_)) && bound_covers(y, x)));
    }
    match (b, o) {
        (_, Shape::Never) | (Shape::Dyn, _) => true,
        (Shape::Bool, Shape::Bool) => true,
        (Shape::Int { lo: bl, hi: bh }, Shape::Int { lo: ol, hi: oh }) => bl <= ol && oh <= bh,
        (Shape::Atom(bu), Shape::Atom(ou)) => ou.iter().all(|a| bu.binary_search(a).is_ok()),
        (Shape::Set { elem: be, max_card: bm }, Shape::Set { elem: oe, max_card: om }) => om <= bm && bound_covers(be, oe),
        (Shape::Fcn { dom: bd, range: br, .. }, Shape::Fcn { dom: od, range: or, .. }) => bd == od && bound_covers(br, or),
        (Shape::Fcn { dom: bd, range: br, .. }, Shape::Tuple(ot)) => {
            fcn_dom_matches_tuple(bd, ot.len()) && ot.iter().all(|y| bound_covers(br, y))
        }
        (Shape::Fcn { dom: bd, range: br, .. }, Shape::Record(of)) => {
            fcn_dom_matches_record(bd, of) && of.iter().all(|(_, y)| bound_covers(br, y))
        }
        (Shape::Tuple(bt), Shape::Fcn { dom: od, range: or, .. }) => {
            fcn_dom_matches_tuple(od, bt.len()) && bt.iter().all(|x| bound_covers(x, or))
        }
        (Shape::Record(bf), Shape::Fcn { dom: od, range: or, .. }) => {
            fcn_dom_matches_record(od, bf) && bf.iter().all(|(_, x)| bound_covers(x, or))
        }
        (Shape::Map { key: bk, range: br, .. }, Shape::Map { key: ok, range: or, .. }) => bound_covers(bk, ok) && bound_covers(br, or),
        (Shape::Record(bf), Shape::Record(of)) => {
            crate::shape::same_field_names(bf, of) && bf.iter().zip(of.iter()).all(|(x, y)| bound_covers(&x.1, &y.1))
        }
        (Shape::Tuple(bt), Shape::Tuple(ot)) => bt.len() == ot.len() && bt.iter().zip(ot.iter()).all(|(x, y)| bound_covers(x, y)),
        (Shape::Seq { elem, max_len }, Shape::Tuple(ot)) => ot.len() <= *max_len && ot.iter().all(|y| bound_covers(elem, y)),
        (Shape::Seq { elem: be, max_len: bl }, Shape::Seq { elem: oe, max_len: ol }) => ol <= bl && bound_covers(be, oe),
        _ => false,
    }
}

/// Refine the layout shape `s` (observed values with headroom) with the
/// bound `b` known to hold for every value that matters (from a type
/// invariant). The change is kept to what makes the layout better without
/// making values harder to move between variables:
/// - a set becomes a bitset over fewer words if the bound on its elements
///   allows it (the elements get the union arms of the bound the pre-run
///   did not see, and the bound's exact integer ranges and atom universes
///   where needed);
/// - cardinalities of sets kept as sorted arrays and sequence lengths: the
///   smaller of the two;
/// - integer ranges in value positions grow to include the bound's (no
///   miss when a counter outgrows what the pre-run saw);
/// - everything else (atom universes, bitset elements, map keys) stays.
///
/// Parts where the bound says nothing (`Dyn`) or has another structure keep
/// `s`. Values outside the bound violate the invariant: they still only
/// cause a layout miss (the search widens and restarts, then reports the
/// violation).
pub fn refine(s: &Shape, b: &Shape) -> Shape {
    match (s, b) {
        (_, Shape::Dyn) | (Shape::Never | Shape::Dyn, _) => s.clone(),
        (Shape::Int { lo: sl, hi: sh }, Shape::Int { lo: bl, hi: bh }) => Shape::Int { lo: (*sl).min(*bl), hi: (*sh).max(*bh) },
        (Shape::Set { elem: se, max_card: sm }, Shape::Set { elem: be, max_card: bm }) => {
            let now = match crate::layout::bitset_universe(se) {
                Some(m) => m.div_ceil(64),
                None => 1 + ((*sm).min(*bm) * crate::layout::words(se)) as u64,
            };
            // Elements as close as possible to the other values of the
            // spec (whose encodings they share without conversion): the
            // bound's exact integer ranges and atom universes only where
            // the looser elements would take more than twice the words.
            let cands: Vec<(Shape, u64)> =
                [Exact { ints: false, atoms: false }, Exact { ints: false, atoms: true }, Exact { ints: true, atoms: true }]
                    .into_iter()
                    .filter_map(|exact| {
                        let elem = refine_elem(se, be, exact);
                        let n = crate::layout::bitset_universe(&elem).filter(|n| n.div_ceil(64) < now)?;
                        Some((elem, n))
                    })
                    .collect();
            if let Some(least) = cands.iter().map(|c| c.1.div_ceil(64)).min() {
                let (elem, n) = cands.into_iter().find(|c| c.1.div_ceil(64) <= 2 * least).unwrap();
                // A bitset holds any subset: only the bound limits it.
                return Shape::Set { elem: Box::new(elem), max_card: (*bm).min(usize::try_from(n).unwrap_or(usize::MAX)) };
            }
            match crate::layout::bitset_universe(se) {
                None => Shape::Set { elem: se.clone(), max_card: (*sm).min(*bm) },
                // (Its cardinality bound costs nothing.)
                Some(_) => s.clone(),
            }
        }
        (Shape::Fcn { dom: sd, range: sr, witness, key_variants }, Shape::Fcn { dom: bd, range: br, .. }) if sd == bd => {
            Shape::Fcn { dom: sd.clone(), range: Box::new(refine(sr, br)), witness: *witness, key_variants: key_variants.clone() }
        }
        (Shape::Record(sf), Shape::Fcn { dom: bd, range: br, .. }) if fcn_dom_matches_record(bd, sf) => {
            Shape::Record(sf.iter().map(|(k, x)| (*k, refine(x, br))).collect())
        }
        (Shape::Tuple(st), Shape::Fcn { dom: bd, range: br, .. }) if fcn_dom_matches_tuple(bd, st.len()) => {
            Shape::Tuple(st.iter().map(|x| refine(x, br)).collect())
        }
        (Shape::Map { key, range: sr, witness }, Shape::Map { range: br, .. }) => {
            match crate::shape::map_shape((**key).clone(), refine(sr, br), *witness) {
                Shape::Dyn => s.clone(),
                m => m,
            }
        }
        (Shape::Record(sf), Shape::Record(bf)) if crate::shape::same_field_names(sf, bf) => {
            Shape::Record(sf.iter().zip(bf.iter()).map(|(x, y)| (x.0, refine(&x.1, &y.1))).collect())
        }
        (Shape::Tuple(st), Shape::Tuple(bt)) if st.len() == bt.len() => {
            Shape::Tuple(st.iter().zip(bt.iter()).map(|(x, y)| refine(x, y)).collect())
        }
        (Shape::Tuple(st), Shape::Seq { elem: be, .. }) => Shape::Tuple(st.iter().map(|x| refine(x, be)).collect()),
        (Shape::Seq { elem: se, max_len: sl }, Shape::Seq { elem: be, max_len: bl }) => {
            Shape::Seq { elem: Box::new(refine(se, be)), max_len: (*sl).min(*bl) }
        }
        (Shape::Union(arms), _) => {
            // Each arm with the bound's arm of its kind (no arms added: they
            // would widen the encoding of every value).
            let barms: &[Shape] = match b {
                Shape::Union(a) => a,
                _ => std::slice::from_ref(b),
            };
            Shape::Union(
                arms.iter()
                    .map(|a| barms.iter().find(|y| y.kind_key() == a.kind_key()).map_or_else(|| a.clone(), |y| refine(a, y)))
                    .collect(),
            )
        }
        (_, Shape::Union(barms)) => barms.iter().find(|y| y.kind_key() == s.kind_key()).map_or_else(|| s.clone(), |y| refine(s, y)),
        _ => s.clone(),
    }
}

/// Which parts of an element shape take the bound's exact values (rather
/// than the hull of the layout's and the bound's).
#[derive(Clone, Copy)]
struct Exact {
    ints: bool,
    atoms: bool,
}

/// The element shape of a set refined with the bound `b` on its elements
/// (integer ranges and atom universes as `exact` says; they size the bitset
/// universe), union arms of the bound added.
fn refine_elem(s: &Shape, b: &Shape, exact: Exact) -> Shape {
    match (s, b) {
        (_, Shape::Dyn) | (Shape::Never | Shape::Dyn, _) => s.clone(),
        (Shape::Int { lo: sl, hi: sh }, Shape::Int { lo: bl, hi: bh }) => {
            if exact.ints {
                b.clone()
            } else {
                Shape::Int { lo: (*sl).min(*bl), hi: (*sh).max(*bh) }
            }
        }
        (Shape::Atom(_), Shape::Atom(_)) => {
            if exact.atoms {
                b.clone()
            } else {
                s.join(b)
            }
        }
        (Shape::Set { elem: se, max_card: sm }, Shape::Set { elem: be, max_card: bm }) => {
            let elem = refine_elem(se, be, exact);
            let max_card = match crate::layout::bitset_universe(&elem) {
                Some(n) => (*bm).min(usize::try_from(n).unwrap_or(usize::MAX)),
                None => (*sm).min(*bm),
            };
            set_shape(elem, max_card)
        }
        (Shape::Fcn { dom: sd, range: sr, witness, key_variants }, Shape::Fcn { dom: bd, range: br, .. }) if sd == bd => Shape::Fcn {
            dom: sd.clone(),
            range: Box::new(refine_elem(sr, br, exact)),
            witness: *witness,
            key_variants: key_variants.clone(),
        },
        (Shape::Record(sf), Shape::Fcn { dom: bd, range: br, .. }) if fcn_dom_matches_record(bd, sf) => {
            Shape::Record(sf.iter().map(|(k, x)| (*k, refine_elem(x, br, exact))).collect())
        }
        (Shape::Tuple(st), Shape::Fcn { dom: bd, range: br, .. }) if fcn_dom_matches_tuple(bd, st.len()) => {
            Shape::Tuple(st.iter().map(|x| refine_elem(x, br, exact)).collect())
        }
        (Shape::Map { key: sk, range: sr, witness }, Shape::Map { key: bk, range: br, .. }) => {
            match crate::shape::map_shape(refine_elem(sk, bk, exact), refine_elem(sr, br, exact), *witness) {
                Shape::Dyn => s.clone(),
                m => m,
            }
        }
        (Shape::Record(sf), Shape::Record(bf)) if crate::shape::same_field_names(sf, bf) => {
            Shape::Record(sf.iter().zip(bf.iter()).map(|(x, y)| (x.0, refine_elem(&x.1, &y.1, exact))).collect())
        }
        (Shape::Tuple(st), Shape::Tuple(bt)) if st.len() == bt.len() => {
            Shape::Tuple(st.iter().zip(bt.iter()).map(|(x, y)| refine_elem(x, y, exact)).collect())
        }
        (Shape::Tuple(st), Shape::Seq { elem: be, .. }) => Shape::Tuple(st.iter().map(|x| refine_elem(x, be, exact)).collect()),
        (Shape::Seq { elem: se, max_len: sl }, Shape::Seq { elem: be, max_len: bl }) => {
            Shape::Seq { elem: Box::new(refine_elem(se, be, exact)), max_len: (*sl).min(*bl) }
        }
        (Shape::Union(_), _) | (_, Shape::Union(_)) => refine_union(s, b, exact),
        _ => s.clone(),
    }
}

fn refine_union(s: &Shape, b: &Shape, exact: Exact) -> Shape {
    let arms_of = |x: &Shape| -> Vec<Shape> {
        match x {
            Shape::Union(a) => a.to_vec(),
            _ => vec![x.clone()],
        }
    };
    let (sarms, barms) = (arms_of(s), arms_of(b));
    let partner =
        |a: &Shape| barms.iter().position(|y| y.kind_key() == a.kind_key() || matches!((a, y), (Shape::Tuple(_), Shape::Seq { .. })));
    let mut used = vec![false; barms.len()];
    let mut arms: Vec<Shape> = Vec::with_capacity(sarms.len());
    for a in &sarms {
        match partner(a) {
            Some(i) => {
                used[i] = true;
                arms.push(refine_elem(a, &barms[i], exact));
            }
            None => arms.push(a.clone()),
        }
    }
    // Alternatives the pre-run did not see yet, if their encoding is bounded.
    for (y, _) in barms.iter().zip(&used).filter(|(_, u)| !**u) {
        if arms.len() < crate::shape::MAX_UNION_ARMS
            && y.cardinality().is_some()
            && y.kind_key().is_some()
            && !arms.iter().any(|a| a.kind_key() == y.kind_key())
        {
            arms.push(y.clone());
        }
    }
    if arms.len() == 1 {
        return arms.pop().unwrap();
    }
    arms.sort_by_cached_key(|a| a.kind_key());
    align_union_fields(&mut arms);
    Shape::Union(arms.into())
}

/// Give a field that several record arms of a union have the same shape in
/// all of them (their join), except for integer fields: compiled code reads
/// `r.f` of a union value without converting it only then (integer fields
/// are read at their per-arm offsets and bases). Exact bounds give each arm
/// its own atom universe (e.g. `type` is `{"phase1a"}` in one arm and
/// `{"phase2a"}` in another).
fn align_union_fields(arms: &mut [Shape]) {
    let mut joined: Vec<(Sym, Shape)> = Vec::new();
    for a in arms.iter() {
        if let Shape::Record(fs) = a {
            for (k, f) in fs.iter() {
                match joined.iter_mut().find(|j| j.0 == *k) {
                    Some(j) => j.1 = j.1.join(f),
                    None => joined.push((*k, f.clone())),
                }
            }
        }
    }
    for a in arms.iter_mut() {
        if let Shape::Record(fs) = a {
            *a = Shape::Record(
                fs.iter()
                    .map(|(k, f)| match joined.iter().find(|j| j.0 == *k) {
                        Some((_, j)) if !matches!(f, Shape::Int { .. }) && !matches!(j, Shape::Dyn | Shape::Union(_)) => (*k, j.clone()),
                        _ => (*k, f.clone()),
                    })
                    .collect(),
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn mv(s: &str) -> Value {
        Value::model_value(s)
    }
    fn st(s: &str) -> Value {
        Value::str(s)
    }
    fn int(n: i64) -> Value {
        Value::Int(n)
    }
    fn rec(fs: &[(&str, Value)]) -> Value {
        Value::record(fs.iter().map(|(k, v)| (Sym::new(k), v.clone())).collect())
    }
    /// The universe of an atom shape, by name (independent of `Value`'s order).
    fn names(s: &Shape) -> Vec<String> {
        let Shape::Atom(u) = s else { panic!("not an atom: {s:?}") };
        let mut out: Vec<String> = u
            .iter()
            .map(|v| match v {
                Value::Str(s) => s.as_str().to_string(),
                _ => format!("{v}"),
            })
            .collect();
        out.sort();
        out
    }
    fn field(s: &Shape, name: &str) -> Shape {
        let Shape::Record(fs) = s else { panic!("not a record: {s:?}") };
        fs.iter().find(|(k, _)| *k == Sym::new(name)).expect("field").1.clone()
    }

    /// A typed model value (`T_a`) is only extended with hint model values of
    /// its own TLC type; an untyped one extends any universe that holds a
    /// model value; strings keep extending any universe that holds a string.
    #[test]
    fn typed_model_values_are_widened_only_by_their_own_type() {
        let hints = Hints { atoms: vec![mv("T_b"), mv("S_c"), mv("plain"), st("s")], ..Hints::default() };
        let obs = |v: Value| {
            let mut o = Observer::new(1);
            o.observe(&[v]);
            names(&o.finalize(&hints)[0])
        };
        assert_eq!(obs(mv("T_a")), ["T_a", "T_b", "plain"]);
        // An untyped model value compares with anything: it keeps taking every
        // untyped hint, and no typed one (a typed hint would make the two
        // incomparable).
        assert_eq!(obs(mv("plain2")), ["plain", "plain2"]);
        assert_eq!(obs(st("a")), ["a", "s"]);
    }

    /// The same for a field of a record: CCF's `history[i].type` holds one
    /// model-value type per record arm, and the arm's shape must say so, or
    /// `tlx-compile` cannot encode any set of those records.
    #[test]
    fn a_record_field_keeps_one_model_value_type() {
        let hints = Hints { atoms: vec![mv("T_b"), mv("S_c")], ..Hints::default() };
        let mut o = Observer::new(1);
        o.observe(&[rec(&[("tx", int(1)), ("type", mv("T_a"))])]);
        let s = &o.finalize(&hints)[0];
        assert_eq!(names(&field(s, "type")), ["T_a", "T_b"]);
        // A value of another type in that field is a layout miss, and the
        // widened shape holds both types: the run continues, not wrongly.
        let w = widen_repeated(s, &rec(&[("tx", int(1)), ("type", mv("S_c"))]), &hints, 0);
        assert_eq!(names(&field(&w, "type")), ["S_c", "T_a", "T_b"]);
    }

    /// A nested bitset whose full powerset (`2^n`) fits in the same 64-bit
    /// word count as its capped universe (e.g. pairs from 5 atoms: 31 -> 32,
    /// both 1 word) widens `max_card` to `n` so compiled code can rank inner
    /// sets directly by bitmask, while larger universes stay capped.
    #[test]
    fn nested_small_bitset_widens_to_full_powerset_in_same_word_count() {
        let hints5 = Hints { atoms: ["n1", "n2", "n3", "n4", "n5"].into_iter().map(mv).collect(), ..Hints::default() };
        let pair = Value::set_enum(vec![mv("n1"), mv("n2")]).unwrap();
        let edges = Value::set_enum(vec![pair]).unwrap();
        let mut o = Observer::new(1);
        o.observe(&[edges]);
        let finalized = &o.finalize(&hints5)[0];
        let Shape::Set { elem, .. } = finalized else { panic!("expected outer set: {finalized:?}") };
        let Shape::Set { max_card, .. } = &**elem else { panic!("expected inner set: {elem:?}") };
        assert_eq!(*max_card, 5);
        assert_eq!(elem.cardinality(), Some(32));

        // Large element universe (12 atoms, max_card 2 -> 4): 2^12 = 4096 needs
        // 64 words vs 13 words for capped universe, so it must NOT widen to 12.
        let hints12 = Hints { atoms: (1..=12).map(|i| mv(&format!("a{i}"))).collect(), ..Hints::default() };
        let pair12 = Value::set_enum(vec![mv("a1"), mv("a2")]).unwrap();
        let edges12 = Value::set_enum(vec![pair12]).unwrap();
        let mut o12 = Observer::new(1);
        o12.observe(&[edges12]);
        let finalized12 = &o12.finalize(&hints12)[0];
        let Shape::Set { elem: elem12, .. } = finalized12 else { panic!("expected outer set") };
        let Shape::Set { max_card: max_card12, .. } = &**elem12 else { panic!("expected inner set") };
        assert_eq!(*max_card12, 4);
    }
}
