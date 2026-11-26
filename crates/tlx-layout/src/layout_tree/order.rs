//! TLC-order comparison directly on canonical encoded `LayoutNode` words.
//!
//! `LayoutNode::cmp_tlc_words` returns `Some(ord)` only when
//! `tlx_value::order::cmp_tlc(&decode(a), &decode(b))` is guaranteed to return
//! `Ok(ord)` without raising a TLC incomparable-value error. Otherwise it
//! returns `None` so callers fall back to `Value` comparison.

use std::cmp::Ordering;

use crate::layout::{FieldLoc, MapDims, SlotLayout};
use crate::shape::FcnWitness;
use tlx_value::Value;

use super::{Kind, LayoutNode};

/// Precomputed ordering invariants for a [`LayoutNode`].
#[derive(Clone, Copy, Debug)]
pub(super) struct OrderFacts {
    /// Raw unsigned slice comparison (`a[..words].cmp(&b[..words])`) agrees
    /// unconditionally with `tlx_value::order::cmp_tlc` on canonical encodings.
    pub(super) raw_word_order: bool,
    /// Finite `unrank(0..card)` is strictly increasing in `cmp_tlc` and every
    /// pair in the universe is TLC-comparable (used for bitset sets and `Map`
    /// key domains).
    pub(super) rank_in_tlc_order: bool,
    /// Every valid pair of encodings of this node (including images under any
    /// type-preserving model-value permutation) is guaranteed TLC-comparable
    /// and ordered by `cmp_tlc_words` without error or `None` fallback.
    pub(super) orbit_cmp_safe: bool,
    /// This node or an active child may hold a `Dyn` or `Ref` handle.
    pub(super) has_dyn_or_ref: bool,
}

impl OrderFacts {
    pub(super) fn of(kind: &Kind, card: Option<u64>) -> OrderFacts {
        match kind {
            Kind::Never => OrderFacts { raw_word_order: false, rank_in_tlc_order: false, orbit_cmp_safe: false, has_dyn_or_ref: false },
            Kind::Bool => OrderFacts { raw_word_order: true, rank_in_tlc_order: true, orbit_cmp_safe: true, has_dyn_or_ref: false },
            Kind::Int { lo, hi } => {
                let ok = lo <= hi;
                OrderFacts { raw_word_order: ok, rank_in_tlc_order: ok, orbit_cmp_safe: ok, has_dyn_or_ref: false }
            }
            Kind::Atom(u) => {
                let ok = !u.is_empty() && atom_all_comparable(u);
                OrderFacts { raw_word_order: ok, rank_in_tlc_order: ok, orbit_cmp_safe: ok, has_dyn_or_ref: false }
            }
            Kind::Dyn | Kind::Ref(_) => {
                OrderFacts { raw_word_order: false, rank_in_tlc_order: false, orbit_cmp_safe: false, has_dyn_or_ref: true }
            }
            Kind::Set { elem, max_card, bitset, .. } => OrderFacts {
                raw_word_order: bitset.is_none() && (*max_card == 0 || elem.order.raw_word_order),
                rank_in_tlc_order: false,
                orbit_cmp_safe: match bitset {
                    Some(_) => elem.order.rank_in_tlc_order,
                    None => *max_card == 0 || elem.order.raw_word_order || (*max_card <= 64 && elem.order.orbit_cmp_safe),
                },
                has_dyn_or_ref: *max_card > 0 && elem.order.has_dyn_or_ref,
            },
            Kind::Fcn { dom, range, witness, key_variants, .. } => {
                let no_extra = *witness != FcnWitness::Dynamic && key_variants.is_empty();
                OrderFacts {
                    raw_word_order: no_extra && (dom.is_empty() || range.order.raw_word_order),
                    rank_in_tlc_order: card.is_some() && no_extra && (dom.is_empty() || range.order.rank_in_tlc_order),
                    orbit_cmp_safe: key_variants.is_empty()
                        && (dom.is_empty() || (fcn_dom_orbit_cmp_safe(dom) && range.order.orbit_cmp_safe)),
                    has_dyn_or_ref: !dom.is_empty() && range.order.has_dyn_or_ref,
                }
            }
            Kind::Map { key, range, .. } => OrderFacts {
                raw_word_order: false,
                rank_in_tlc_order: false,
                orbit_cmp_safe: key.order.rank_in_tlc_order && range.order.orbit_cmp_safe,
                has_dyn_or_ref: key.order.has_dyn_or_ref || range.order.has_dyn_or_ref,
            },
            Kind::Record { fields, .. } => OrderFacts {
                raw_word_order: fields.iter().all(|(_, n, _)| n.order.raw_word_order),
                rank_in_tlc_order: card.is_some() && fields.iter().all(|(_, n, _)| n.order.rank_in_tlc_order),
                orbit_cmp_safe: fields.iter().all(|(_, n, _)| n.order.orbit_cmp_safe),
                has_dyn_or_ref: fields.iter().any(|(_, n, _)| n.order.has_dyn_or_ref),
            },
            Kind::Tuple { elems, .. } => OrderFacts {
                raw_word_order: elems.iter().all(|(n, _)| n.order.raw_word_order),
                rank_in_tlc_order: card.is_some() && elems.iter().all(|(n, _)| n.order.rank_in_tlc_order),
                orbit_cmp_safe: elems.iter().all(|(n, _)| n.order.orbit_cmp_safe),
                has_dyn_or_ref: elems.iter().any(|(n, _)| n.order.has_dyn_or_ref),
            },
            Kind::Seq { elem, max_len, .. } => OrderFacts {
                raw_word_order: *max_len == 0 || elem.order.raw_word_order,
                rank_in_tlc_order: card.is_some() && (*max_len == 0 || elem.order.rank_in_tlc_order),
                orbit_cmp_safe: *max_len == 0 || elem.order.orbit_cmp_safe,
                has_dyn_or_ref: *max_len > 0 && elem.order.has_dyn_or_ref,
            },
            Kind::Union { arms, .. } => {
                let ordered = !arms.is_empty() && union_arms_strictly_tlc_ordered(arms);
                OrderFacts {
                    raw_word_order: ordered && arms.iter().all(|a| a.order.raw_word_order),
                    rank_in_tlc_order: card.is_some() && ordered && arms.iter().all(|a| a.order.rank_in_tlc_order),
                    orbit_cmp_safe: ordered && arms.iter().all(|a| a.order.orbit_cmp_safe),
                    has_dyn_or_ref: arms.iter().any(|a| a.order.has_dyn_or_ref),
                }
            }
        }
    }
}

impl LayoutNode {
    /// Whether this node or any active child may hold a `Dyn` or `Ref` handle.
    #[inline]
    pub fn has_dyn_or_ref(&self) -> bool {
        self.order.has_dyn_or_ref
    }

    /// Whether raw unsigned slice comparison agrees unconditionally with
    /// `cmp_tlc` on canonical encodings of this node.
    #[inline]
    pub fn is_raw_word_order(&self) -> bool {
        self.order.raw_word_order
    }

    /// Whether every valid pair of encodings of this node (including images
    /// under any type-preserving model-value permutation) is guaranteed
    /// TLC-comparable and ordered by `cmp_tlc_words` without error.
    #[inline]
    pub fn is_orbit_cmp_safe(&self) -> bool {
        self.order.orbit_cmp_safe
    }

    /// Compare two canonical encodings of this node's shape in TLC's value
    /// order (`tlx_value::order::cmp_tlc`) directly on encoded words, without
    /// decoding into heap `Value`s.
    ///
    /// Returns `Some(ord)` only when `cmp_tlc(&decode(a), &decode(b))` is
    /// guaranteed to return `Ok(ord)`. Returns `None` when TLC comparison
    /// would error (e.g. incomparable union arms, mixed typed model values, or
    /// maps with incomparable key pairs) or when the representation does not
    /// directly expose TLC order (`Dyn`, large non-word-ordered sets, or
    /// exotic cross-arm unions), so callers can fall back to `Value`
    /// comparison.
    pub fn cmp_tlc_words(&self, a: &[u64], b: &[u64]) -> Option<Ordering> {
        if a.len() < self.words || b.len() < self.words {
            return None;
        }
        self.cmp_words(a, b)
    }

    fn cmp_words(&self, a: &[u64], b: &[u64]) -> Option<Ordering> {
        if self.order.raw_word_order {
            if let Kind::Seq { max_len, slot, .. } = &self.kind {
                return cmp_seq_raw(*max_len, *slot, a, b);
            }
            return Some(a[..self.words].cmp(&b[..self.words]));
        }
        match &self.kind {
            Kind::Never | Kind::Dyn => None,
            Kind::Bool | Kind::Int { .. } => Some(a[0].cmp(&b[0])),
            Kind::Atom(u) => cmp_atom(u, a[0], b[0]),
            Kind::Ref(store) => crate::store::cmp_tlc(store, a[0], b[0]).ok(),
            Kind::Set { elem, max_card, bitset: Some(n), .. } => cmp_set_bitset(elem, *max_card, *n, a, b),
            Kind::Set { elem, max_card, bitset: None, .. } => cmp_set_sorted(elem, *max_card, a, b),
            Kind::Fcn { dom, range, slot, .. } => cmp_fcn(dom.len(), range, *slot, a, b),
            Kind::Map { key, range, universe, dims, .. } => cmp_map(key, range, *universe, *dims, a, b),
            Kind::Record { fields, .. } => cmp_locs(fields.iter().map(|(_, n, loc)| (n, *loc)), a, b),
            Kind::Tuple { elems, .. } => cmp_locs(elems.iter().map(|(n, loc)| (n, *loc)), a, b),
            Kind::Seq { elem, max_len, slot, .. } => cmp_seq(elem, *max_len, *slot, a, b),
            Kind::Union { arms, .. } => cmp_union(arms, a, b),
        }
    }

    #[inline]
    fn cmp_loc(&self, a: &[u64], b: &[u64], loc: FieldLoc) -> Option<Ordering> {
        match loc {
            FieldLoc::Words(o) => self.cmp_words(&a[o..], &b[o..]),
            FieldLoc::Bits(pos) => self.cmp_scalar_raw(pos.extract(a), pos.extract(b)),
        }
    }

    #[inline]
    fn cmp_scalar_raw(&self, a: u64, b: u64) -> Option<Ordering> {
        match &self.kind {
            Kind::Bool | Kind::Int { .. } => Some(a.cmp(&b)),
            Kind::Atom(_) if self.order.raw_word_order => Some(a.cmp(&b)),
            Kind::Atom(u) => cmp_atom(u, a, b),
            _ => None,
        }
    }
}

#[inline]
fn cmp_atom(u: &[Value], a: u64, b: u64) -> Option<Ordering> {
    let va = u.get(a as usize)?;
    let vb = u.get(b as usize)?;
    if a == b {
        Some(Ordering::Equal)
    } else {
        tlx_value::order::cmp_tlc(va, vb).ok()
    }
}

fn cmp_locs<'a>(locs: impl Iterator<Item = (&'a LayoutNode, FieldLoc)>, a: &[u64], b: &[u64]) -> Option<Ordering> {
    for (n, loc) in locs {
        let c = n.cmp_loc(a, b, loc)?;
        if c != Ordering::Equal {
            return Some(c);
        }
    }
    Some(Ordering::Equal)
}

fn cmp_set_bitset(elem: &LayoutNode, max_card: usize, universe: u64, a: &[u64], b: &[u64]) -> Option<Ordering> {
    let bw = universe.div_ceil(64) as usize;
    let (sa, sb) = (&a[..bw], &b[..bw]);
    if elem.order.rank_in_tlc_order {
        return Some(cmp_bitset_tlc(sa, sb));
    }
    let ca: u32 = sa.iter().map(|w| w.count_ones()).sum();
    let cb: u32 = sb.iter().map(|w| w.count_ones()).sum();
    if ca as usize > max_card || cb as usize > max_card {
        return None;
    }
    let c = ca.cmp(&cb);
    if c != Ordering::Equal {
        return Some(c);
    }
    (sa == sb).then_some(Ordering::Equal)
}

fn cmp_set_sorted(elem: &LayoutNode, max_card: usize, a: &[u64], b: &[u64]) -> Option<Ordering> {
    let la = usize::try_from(a[0]).ok()?;
    let lb = usize::try_from(b[0]).ok()?;
    if la > max_card || lb > max_card {
        return None;
    }
    let c = la.cmp(&lb);
    if c != Ordering::Equal || la == 0 {
        return Some(c);
    }
    let ew = elem.words;
    if ew == 0 {
        return None;
    }
    if elem.order.raw_word_order {
        return Some(a[1..1 + la * ew].cmp(&b[1..1 + la * ew]));
    }
    if la == 1 {
        return elem.cmp_words(&a[1..], &b[1..]);
    }
    if !elem.order.has_dyn_or_ref && a[1..1 + la * ew] == b[1..1 + la * ew] {
        return Some(Ordering::Equal);
    }
    if la > 64 {
        return None;
    }
    let mut oa = [0usize; 64];
    let mut ob = [0usize; 64];
    sort_elem_indices(elem, &a[1..], ew, la, &mut oa[..la])?;
    sort_elem_indices(elem, &b[1..], ew, la, &mut ob[..la])?;
    for i in 0..la {
        let c = elem.cmp_words(&a[1 + oa[i] * ew..], &b[1 + ob[i] * ew..])?;
        if c != Ordering::Equal {
            return Some(c);
        }
    }
    Some(Ordering::Equal)
}

fn cmp_fcn(dom_len: usize, range: &LayoutNode, slot: SlotLayout, a: &[u64], b: &[u64]) -> Option<Ordering> {
    if dom_len == 0 {
        return Some(Ordering::Equal);
    }
    if range.order.raw_word_order {
        let payload = slot.array_words(dom_len);
        return Some(a[..payload].cmp(&b[..payload]));
    }
    for i in 0..dom_len {
        let c = range.cmp_loc(a, b, slot.loc(0, i))?;
        if c != Ordering::Equal {
            return Some(c);
        }
    }
    Some(Ordering::Equal)
}

fn cmp_map(key: &LayoutNode, range: &LayoutNode, universe: u64, dims: MapDims, a: &[u64], b: &[u64]) -> Option<Ordering> {
    // Only compare map domains directly when every pair of keys in the key
    // universe is TLC-comparable in rank order; otherwise TLC's domain
    // comparison can raise an incomparable-value error (e.g. a tuple key
    // aligning a typed model value against a string).
    if !key.order.rank_in_tlc_order {
        return None;
    }
    let bw = dims.bitset_words;
    let (da, db) = (&a[..bw], &b[..bw]);
    let c = cmp_bitset_tlc(da, db);
    if c != Ordering::Equal {
        return Some(c);
    }
    for (wi, &word) in da.iter().enumerate() {
        let mut m = word;
        while m != 0 {
            let r = wi * 64 + m.trailing_zeros() as usize;
            m &= m - 1;
            if r >= universe as usize {
                return None;
            }
            let c = range.cmp_loc(a, b, dims.slot_loc(r))?;
            if c != Ordering::Equal {
                return Some(c);
            }
        }
    }
    Some(Ordering::Equal)
}

fn cmp_seq_raw(max_len: usize, slot: SlotLayout, a: &[u64], b: &[u64]) -> Option<Ordering> {
    let la = usize::try_from(a[0]).ok()?;
    let lb = usize::try_from(b[0]).ok()?;
    if la > max_len || lb > max_len {
        return None;
    }
    let c = la.cmp(&lb);
    if c != Ordering::Equal || la == 0 {
        return Some(c);
    }
    let active = slot.array_words(la);
    Some(a[1..1 + active].cmp(&b[1..1 + active]))
}

fn cmp_seq(elem: &LayoutNode, max_len: usize, slot: SlotLayout, a: &[u64], b: &[u64]) -> Option<Ordering> {
    let la = usize::try_from(a[0]).ok()?;
    let lb = usize::try_from(b[0]).ok()?;
    if la > max_len || lb > max_len {
        return None;
    }
    let c = la.cmp(&lb);
    if c != Ordering::Equal || la == 0 {
        return Some(c);
    }
    for i in 0..la {
        let c = elem.cmp_loc(a, b, slot.loc(1, i))?;
        if c != Ordering::Equal {
            return Some(c);
        }
    }
    Some(Ordering::Equal)
}

fn cmp_union(arms: &[LayoutNode], a: &[u64], b: &[u64]) -> Option<Ordering> {
    let ia = usize::try_from(a[0]).ok()?;
    let ib = usize::try_from(b[0]).ok()?;
    let arm_a = arms.get(ia)?;
    let arm_b = arms.get(ib)?;
    if ia == ib {
        return arm_a.cmp_words(&a[1..], &b[1..]);
    }
    if let Some(c) = cmp_static_union_arms(&arm_a.kind, &arm_b.kind) {
        return Some(c);
    }
    // Runtime untyped model value inside a mixed Atom arm (e.g. untyped MV + Str).
    if is_untyped_mv_in_atom(&arm_a.kind, &a[1..]) && !is_atom_or_open(&arm_b.kind) {
        return Some(Ordering::Less);
    }
    if is_untyped_mv_in_atom(&arm_b.kind, &b[1..]) && !is_atom_or_open(&arm_a.kind) {
        return Some(Ordering::Greater);
    }
    // Runtime sequence length vs fixed record field count (Int keys < Str keys).
    match (&arm_a.kind, &arm_b.kind) {
        (Kind::Record { fields: fa, .. }, Kind::Seq { max_len, .. }) => {
            let lb = usize::try_from(b[1]).ok()?;
            (lb <= *max_len).then(|| cmp_record_vs_len(fa.len(), lb))
        }
        (Kind::Seq { max_len, .. }, Kind::Record { fields: fb, .. }) => {
            let la = usize::try_from(a[1]).ok()?;
            (la <= *max_len).then(|| cmp_record_vs_len(fb.len(), la).reverse())
        }
        _ => None,
    }
}

/// Static TLC order between two distinct union arms when the order depends
/// solely on the arm kinds (shared by union classification and runtime
/// cross-arm comparison).
fn cmp_static_union_arms(a: &Kind, b: &Kind) -> Option<Ordering> {
    match (a, b) {
        (Kind::Atom(u), other) if all_untyped_model_values(u) && !is_atom_or_open(other) => Some(Ordering::Less),
        (other, Kind::Atom(u)) if all_untyped_model_values(u) && !is_atom_or_open(other) => Some(Ordering::Greater),
        (Kind::Record { fields: fa, .. }, Kind::Record { fields: fb, .. }) => {
            let c = fa.len().cmp(&fb.len()).then_with(|| fa.iter().map(|f| f.0).cmp(fb.iter().map(|f| f.0)));
            (c != Ordering::Equal).then_some(c)
        }
        (Kind::Tuple { elems: ta, .. }, Kind::Tuple { elems: tb, .. }) => (ta.len() != tb.len()).then(|| ta.len().cmp(&tb.len())),
        (Kind::Record { fields: fa, .. }, Kind::Tuple { elems: tb, .. }) => Some(cmp_record_vs_len(fa.len(), tb.len())),
        (Kind::Tuple { elems: ta, .. }, Kind::Record { fields: fb, .. }) => Some(cmp_record_vs_len(fb.len(), ta.len()).reverse()),
        _ => None,
    }
}

#[inline]
fn cmp_record_vs_len(record_len: usize, tuple_len: usize) -> Ordering {
    record_len.cmp(&tuple_len).then_with(|| if record_len == 0 { Ordering::Equal } else { Ordering::Greater })
}

#[inline]
fn is_atom_or_open(kind: &Kind) -> bool {
    matches!(kind, Kind::Atom(_) | Kind::Dyn | Kind::Ref(_) | Kind::Union { .. })
}

#[inline]
fn all_untyped_model_values(u: &[Value]) -> bool {
    !u.is_empty() && u.iter().all(|v| matches!(v, Value::ModelValue(s) if s.model_value_type().is_none()))
}

#[inline]
fn is_untyped_mv_in_atom(kind: &Kind, words: &[u64]) -> bool {
    match kind {
        Kind::Atom(u) => matches!(u.get(words[0] as usize), Some(Value::ModelValue(s)) if s.model_value_type().is_none()),
        _ => false,
    }
}

/// Whether `arms` are strictly increasing in TLC's value order across every
/// pair of distinct arm indices `i < j`.
fn union_arms_strictly_tlc_ordered(arms: &[LayoutNode]) -> bool {
    arms.windows(2).all(|w| cmp_static_union_arms(&w[0].kind, &w[1].kind) == Some(Ordering::Less))
}

/// Whether `dom` of a `Shape::Fcn` is strictly ascending in `cmp_tlc` and
/// every pair of keys (including images under any type-preserving model-value
/// permutation) is guaranteed TLC-comparable.
fn fcn_dom_orbit_cmp_safe(dom: &[Value]) -> bool {
    if !dom.iter().all(tlx_value::order::self_comparison_is_inert)
        || !dom.windows(2).all(|w| tlx_value::order::cmp_tlc(&w[0], &w[1]).ok() == Some(Ordering::Less))
    {
        return false;
    }
    // Scalar domain: all non-untyped-model-value entries must share one TLC kind.
    let mut kind: Option<u8> = None;
    let mut mv_ty: Option<char> = None;
    let mut all_scalar = true;
    for v in dom {
        match v {
            Value::Bool(_) => {
                if kind.is_some_and(|k| k != 1) {
                    return false;
                }
                kind = Some(1);
            }
            Value::Int(_) => {
                if kind.is_some_and(|k| k != 2) {
                    return false;
                }
                kind = Some(2);
            }
            Value::Str(_) => {
                if kind.is_some_and(|k| k != 3) {
                    return false;
                }
                kind = Some(3);
            }
            Value::ModelValue(s) => {
                if let Some(t) = s.model_value_type() {
                    if kind.is_some_and(|k| k != 4) || mv_ty.is_some_and(|p| p != t) {
                        return false;
                    }
                    kind = Some(4);
                    mv_ty = Some(t);
                }
            }
            _ => {
                all_scalar = false;
                break;
            }
        }
    }
    if all_scalar {
        return true;
    }
    // Compound domain keys: safe unconditionally when no model value appears
    // (fixed under all symmetry permutations).
    fn has_model_value(v: &Value) -> bool {
        match v {
            Value::ModelValue(_) => true,
            Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => false,
            Value::Set(es) | Value::Tuple(es) => es.iter().any(has_model_value),
            Value::Record(fs) => fs.iter().any(|(_, e)| has_model_value(e)),
            Value::Fcn(ps, _) => ps.iter().any(|(k, e)| has_model_value(k) || has_model_value(e)),
            Value::LazySet(_) | Value::LazyFcn(_) => true,
        }
    }
    !dom.iter().any(has_model_value)
}

/// Whether every pair of atoms in `u` (already sorted by `Value::cmp`) is
/// comparable under `tlx_value::order::cmp_tlc` (so index order agrees with
/// TLC order unconditionally).
fn atom_all_comparable(u: &[Value]) -> bool {
    let mut has_str = false;
    let mut mv_type: Option<char> = None;
    for v in u {
        match v {
            Value::Str(_) => {
                has_str = true;
                if mv_type.is_some() {
                    return false;
                }
            }
            Value::ModelValue(s) => {
                if let Some(t) = s.model_value_type() {
                    if has_str || mv_type.is_some_and(|prev| prev != t) {
                        return false;
                    }
                    mv_type = Some(t);
                }
            }
            _ => return false,
        }
    }
    true
}

/// Compare two equal-length bitsets in TLC set/domain order: cardinality
/// (popcount) first, then lowest differing set bit (smaller element wins).
#[inline]
fn cmp_bitset_tlc(a: &[u64], b: &[u64]) -> Ordering {
    if a.len() == 1 {
        let (wa, wb) = (a[0], b[0]);
        let c = wa.count_ones().cmp(&wb.count_ones());
        if c != Ordering::Equal || wa == wb {
            return c;
        }
        let bit = 1u64 << (wa ^ wb).trailing_zeros();
        return if wa & bit != 0 { Ordering::Less } else { Ordering::Greater };
    }
    let ca: u32 = a.iter().map(|w| w.count_ones()).sum();
    let cb: u32 = b.iter().map(|w| w.count_ones()).sum();
    let c = ca.cmp(&cb);
    if c != Ordering::Equal {
        return c;
    }
    for (&wa, &wb) in a.iter().zip(b) {
        let diff = wa ^ wb;
        if diff != 0 {
            let bit = 1u64 << diff.trailing_zeros();
            return if wa & bit != 0 { Ordering::Less } else { Ordering::Greater };
        }
    }
    Ordering::Equal
}

/// Insertion-sort element indices `0..len` of a sorted-array set into TLC
/// order using `elem.cmp_words`; returns `None` if any comparison fails.
fn sort_elem_indices(elem: &LayoutNode, data: &[u64], ew: usize, len: usize, out: &mut [usize]) -> Option<()> {
    for i in 0..len {
        let mut j = i;
        let cur = &data[i * ew..];
        while j > 0 {
            let prev = out[j - 1];
            if elem.cmp_words(cur, &data[prev * ew..])? != Ordering::Less {
                break;
            }
            out[j] = prev;
            j -= 1;
        }
        out[j] = i;
    }
    Some(())
}
