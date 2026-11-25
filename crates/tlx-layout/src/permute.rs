//! Applying a permutation of model values (a SYMMETRY element) directly to
//! encoded values, guided by their shape.
//!
//! A `PermPlan` is compiled once per (shape, permutation): atoms map through
//! a table, bitsets map their bit ranks, sorted-array sets permute their
//! elements and re-sort, functions over atom domains move their slots, maps
//! move their presence bits and slots, `Dyn` handles are permuted as values
//! and re-interned. The result is the canonical encoding of the permuted
//! value, so comparing or hashing it is equivalent to doing so on the
//! permuted value.
//!
//! Plans of fixed-position shapes (records, tuples, functions of atoms,
//! ints, atoms) are flattened into word-level copy / atom-map runs
//! (`PermPlan::Flat`), which is what most state variables become.

use std::cell::RefCell;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use tlx_value::Value;

use crate::dynval;
use crate::layout::{bitset_universe, rank, unrank, words, BitPos, FieldGroup, FieldLayout, FieldLoc, MapDims, SlotLayout};
use crate::Shape;

/// Numbers of the `PermPlan::Dyn` plans (from 1: 0 marks an empty memo
/// entry).
static NEXT_DYN_PLAN: AtomicU64 = AtomicU64::new(1);

/// Log2 of the entries of `DYN_MEMO`.
const DYN_MEMO_BITS: u32 = 12;

thread_local! {
    /// Images of `Dyn` handles, direct-mapped: (plan number, handle, image).
    static DYN_MEMO: RefCell<Vec<(u64, u64, u64)>> = const { RefCell::new(Vec::new()) };
}

/// A permutation of atoms (identity on everything but model values).
pub type AtomPerm = Arc<dyn Fn(&Value) -> Value + Send + Sync>;

/// How to permute one encoded value of a given shape. Applying a plan
/// writes exactly the value's words.
#[derive(Clone)]
pub enum PermPlan {
    /// Unaffected by the permutation: copy `n` words.
    Copy(usize),
    /// An atom: map its index.
    Atom(Arc<[u64]>),
    /// Fixed word positions: copies and atom maps (see `FlatOp`).
    Flat(Box<[FlatOp]>),
    /// A bitset: bit `r` moves to bit `map[r]`.
    Bitset { map: Box<[u32]>, words: usize },
    /// A sorted array of `elem_words`-word elements: permute each element
    /// and re-sort.
    Sorted { elem: Box<PermPlan>, elem_words: usize, words: usize },
    /// Fixed slots (records, tuples, functions): slot `i` of the input,
    /// permuted with `plans[i]`, goes to word offset `dst[i]`. The slots
    /// cover all words.
    Slots { src: Box<[usize]>, dst: Box<[usize]>, plans: Box<[PermPlan]> },
    /// A sequence: length word, then elements.
    Seq { elem: Box<PermPlan>, elem_words: usize, words: usize },
    /// A sequence of packed sub-word atoms: length word, then `bits`-wide elements.
    SeqBits { bits: u8, map: Arc<[u64]>, words: usize },
    /// A union: arm index word, then the arm's payload (padded).
    Union { arms: Box<[PermPlan]>, words: usize },
    /// A map: presence bitset (`bitset_words`) over the key universe, then
    /// one `range_words` slot per key. Key rank `r` moves to `keys[r]`.
    Map { keys: Box<[u32]>, bitset_words: usize, range: Box<PermPlan>, range_words: usize, words: usize },
    /// A map with sub-word packed values (`bits`-wide, mapped through `map` if atoms).
    MapBits { keys: Box<[u32]>, bitset_words: usize, bits: u8, map: Option<Arc<[u64]>>, words: usize },
    /// A `Dyn` handle: permute the interned value and re-intern it (memoized
    /// per thread by handle; the number identifies the plan, see
    /// `DYN_MEMO`).
    Dyn(AtomPerm, u64),
    /// A value store handle: permute the stored value and store it (memoized
    /// like `Dyn`; handles of a store are never reused either).
    Ref(AtomPerm, crate::store::StoreRef, u64),
}

/// One step of a flat plan.
#[derive(Clone, Debug)]
pub enum FlatOp {
    /// Zero `len` words starting at `dst`.
    Zero { dst: u32, len: u32 },
    /// Copy `len` words from `src` to `dst`.
    Copy { src: u32, dst: u32, len: u32 },
    /// `dst = map[src]` (one word).
    Atom { src: u32, dst: u32, map: Arc<[u64]> },
    /// Copy sub-word bitfield `src` into zeroed `dst`.
    BitCopy { src: BitPos, dst: BitPos },
    /// Map sub-word atom bitfield `src` through `map` into zeroed `dst`.
    BitAtom { src: BitPos, dst: BitPos, map: Arc<[u64]> },
}

impl std::fmt::Debug for PermPlan {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PermPlan::Copy(n) => write!(f, "Copy({n})"),
            PermPlan::Atom(m) => write!(f, "Atom({m:?})"),
            PermPlan::Flat(ops) => write!(f, "Flat({ops:?})"),
            PermPlan::Bitset { map, .. } => write!(f, "Bitset({map:?})"),
            PermPlan::Sorted { elem, .. } => write!(f, "Sorted({elem:?})"),
            PermPlan::Slots { src, dst, plans } => write!(f, "Slots({src:?} -> {dst:?}, {plans:?})"),
            PermPlan::Seq { elem, .. } => write!(f, "Seq({elem:?})"),
            PermPlan::SeqBits { bits, map, .. } => write!(f, "SeqBits({bits}, {map:?})"),
            PermPlan::Union { arms, .. } => write!(f, "Union({arms:?})"),
            PermPlan::Map { keys, range, .. } => write!(f, "Map({keys:?}, {range:?})"),
            PermPlan::MapBits { keys, bits, map, .. } => write!(f, "MapBits({keys:?}, {bits}, {map:?})"),
            PermPlan::Dyn(..) => write!(f, "Dyn"),
            PermPlan::Ref(..) => write!(f, "Ref"),
        }
    }
}

impl PermPlan {
    /// Plan for permuting values of `shape` with `perm` (on atoms). `None`
    /// if the shape cannot be permuted in place (an atom universe or a
    /// function domain not closed under the permutation).
    pub fn compile(shape: &Shape, perm: &AtomPerm) -> Option<PermPlan> {
        let n = words(shape);
        let permute_value = |v: &Value| tlx_value::ops::permute(v, &|m| Some(perm(&Value::ModelValue(m)))).ok();
        Some(match shape {
            Shape::Never | Shape::Bool | Shape::Int { .. } => PermPlan::Copy(n),
            Shape::Atom(u) => {
                let map: Vec<u64> = u.iter().map(|a| u.binary_search(&perm(a)).ok().map(|i| i as u64)).collect::<Option<_>>()?;
                if is_identity(map.iter().map(|m| *m as usize)) {
                    PermPlan::Copy(n)
                } else {
                    PermPlan::Atom(map.into())
                }
            }
            Shape::Set { elem, .. } if bitset_universe(elem).is_some() => {
                let map = rank_map(elem, &permute_value)?;
                if is_identity(map.iter().map(|m| *m as usize)) {
                    PermPlan::Copy(n)
                } else {
                    PermPlan::Bitset { map: map.into(), words: n }
                }
            }
            Shape::Set { elem, .. } => match PermPlan::compile(elem, perm)? {
                PermPlan::Copy(_) => PermPlan::Copy(n),
                p => PermPlan::Sorted { elem: Box::new(p), elem_words: words(elem), words: n },
            },
            Shape::Seq { elem, .. } => match PermPlan::compile(elem, perm)? {
                PermPlan::Copy(_) => PermPlan::Copy(n),
                p => match SlotLayout::of(elem) {
                    SlotLayout::Words(ew) => PermPlan::Seq { elem: Box::new(p), elem_words: ew, words: n },
                    SlotLayout::Bits(bits) => {
                        let PermPlan::Atom(map) = p else { unreachable!("packed non-copy scalar must be Atom") };
                        PermPlan::SeqBits { bits, map, words: n }
                    }
                },
            },
            Shape::Record(fs) => {
                let parts: Vec<&Shape> = fs.iter().map(|(_, f)| f).collect();
                product_slots(&parts, perm, n)?
            }
            Shape::Tuple(es) => {
                let parts: Vec<&Shape> = es.iter().collect();
                product_slots(&parts, perm, n)?
            }
            Shape::Fcn { dom, range } => {
                // Slot of key k moves to the slot of perm(k).
                let mut moved = Vec::with_capacity(dom.len());
                for k in dom.iter() {
                    let pk = permute_value(k)?;
                    moved.push(dom.iter().position(|d| *d == pk)?);
                }
                fcn_slots(range, dom.len(), &moved, perm, n)?
            }
            Shape::Map { key, range } => {
                let keys = rank_map(key, &permute_value)?;
                let d = MapDims::new(keys.len(), SlotLayout::of(range));
                let range_plan = PermPlan::compile(range, perm)?;
                if is_identity(keys.iter().map(|k| *k as usize)) && matches!(range_plan, PermPlan::Copy(_)) {
                    PermPlan::Copy(n)
                } else {
                    match d.slot {
                        SlotLayout::Words(rw) => PermPlan::Map {
                            keys: keys.into(),
                            bitset_words: d.bitset_words,
                            range: Box::new(range_plan),
                            range_words: rw,
                            words: n,
                        },
                        SlotLayout::Bits(bits) => {
                            let map = match range_plan {
                                PermPlan::Copy(_) => None,
                                PermPlan::Atom(m) => Some(m),
                                _ => unreachable!("packed scalar plan must be Copy or Atom"),
                            };
                            PermPlan::MapBits { keys: keys.into(), bitset_words: d.bitset_words, bits, map, words: n }
                        }
                    }
                }
            }
            Shape::Union(arms) => {
                let plans: Vec<PermPlan> = arms.iter().map(|a| PermPlan::compile(a, perm)).collect::<Option<_>>()?;
                if plans.iter().all(|p| matches!(p, PermPlan::Copy(_))) {
                    PermPlan::Copy(n)
                } else {
                    PermPlan::Union { arms: plans.into(), words: n }
                }
            }
            Shape::Dyn => PermPlan::Dyn(perm.clone(), NEXT_DYN_PLAN.fetch_add(1, Ordering::Relaxed)),
            Shape::Ref(store) => PermPlan::Ref(perm.clone(), store.clone(), NEXT_DYN_PLAN.fetch_add(1, Ordering::Relaxed)),
        })
    }

    /// Whether the plan leaves every value unchanged.
    pub fn is_identity(&self) -> bool {
        matches!(self, PermPlan::Copy(_))
    }

    /// Write the permutation of `src` (an encoding of the plan's shape)
    /// into `dst` (same length).
    pub fn apply(&self, src: &[u64], dst: &mut [u64]) {
        // SAFETY: the false instantiation validates any handle it decodes.
        unsafe { self.apply_impl::<false>(src, dst) }
    }

    /// Apply a permutation to trusted encoded words.
    ///
    /// # Safety
    /// `src` must have this plan's encoding; active Dyn handles must satisfy
    /// `dynval::lookup_unchecked`'s publication contract.
    pub unsafe fn apply_unchecked(&self, src: &[u64], dst: &mut [u64]) {
        // SAFETY: the caller guarantees valid and published source handles.
        unsafe { self.apply_impl::<true>(src, dst) }
    }

    unsafe fn apply_impl<const TRUSTED: bool>(&self, src: &[u64], dst: &mut [u64]) {
        // SAFETY: trusted recursive slots inherit the valid-encoding contract;
        // the safe instantiation checks every handle before constructing a value.
        unsafe {
            match self {
                PermPlan::Copy(1) => dst[0] = src[0],
                PermPlan::Copy(n) => dst[..*n].copy_from_slice(&src[..*n]),
                PermPlan::Atom(map) => dst[0] = map[src[0] as usize],
                PermPlan::Flat(ops) => apply_flat(ops, src, dst),
                PermPlan::Bitset { map, words } => {
                    dst[..*words].fill(0);
                    for (i, &w) in src[..*words].iter().enumerate() {
                        let mut b = w;
                        while b != 0 {
                            let r = i * 64 + b.trailing_zeros() as usize;
                            b &= b - 1;
                            let t = map[r] as usize;
                            dst[t / 64] |= 1 << (t % 64);
                        }
                    }
                }
                PermPlan::Sorted { elem, elem_words, words } => {
                    let (n, ew) = (src[0] as usize, *elem_words);
                    dst[0] = src[0];
                    for i in 0..n {
                        let o = 1 + i * ew;
                        elem.apply_impl::<TRUSTED>(&src[o..o + ew], &mut dst[o..o + ew]);
                    }
                    dst[1 + n * ew..*words].fill(0);
                    sort_elems(&mut dst[1..1 + n * ew], ew);
                }
                PermPlan::Seq { elem, elem_words, words } => {
                    let (n, ew) = (src[0] as usize, *elem_words);
                    dst[0] = src[0];
                    for i in 0..n {
                        let o = 1 + i * ew;
                        elem.apply_impl::<TRUSTED>(&src[o..o + ew], &mut dst[o..o + ew]);
                    }
                    dst[1 + n * ew..*words].fill(0);
                }
                PermPlan::SeqBits { bits, map, words } => {
                    let n = src[0] as usize;
                    dst[0] = src[0];
                    dst[1..*words].fill(0);
                    for i in 0..n {
                        let raw = SlotLayout::extract(*bits, &src[1..], i);
                        SlotLayout::set_zeroed(*bits, &mut dst[1..], i, map[raw as usize]);
                    }
                }
                PermPlan::Slots { src: so, dst: d, plans } => {
                    for ((s, t), p) in so.iter().zip(d.iter()).zip(plans.iter()) {
                        p.apply_impl::<TRUSTED>(&src[*s..], &mut dst[*t..]);
                    }
                }
                PermPlan::Union { arms, words } => {
                    dst[..*words].fill(0);
                    dst[0] = src[0];
                    arms[src[0] as usize].apply_impl::<TRUSTED>(&src[1..*words], &mut dst[1..*words]);
                }
                PermPlan::Map { keys, bitset_words, range, range_words, words } => {
                    let (bw, rw) = (*bitset_words, *range_words);
                    dst[..*words].fill(0);
                    for (i, &w) in src[..bw].iter().enumerate() {
                        let mut b = w;
                        while b != 0 {
                            let r = i * 64 + b.trailing_zeros() as usize;
                            b &= b - 1;
                            let t = keys[r] as usize;
                            dst[t / 64] |= 1 << (t % 64);
                            range.apply_impl::<TRUSTED>(&src[bw + r * rw..bw + (r + 1) * rw], &mut dst[bw + t * rw..bw + (t + 1) * rw]);
                        }
                    }
                }
                PermPlan::MapBits { keys, bitset_words, bits, map, words } => {
                    let bw = *bitset_words;
                    dst[..*words].fill(0);
                    for (i, &w) in src[..bw].iter().enumerate() {
                        let mut b = w;
                        while b != 0 {
                            let r = i * 64 + b.trailing_zeros() as usize;
                            b &= b - 1;
                            let t = keys[r] as usize;
                            dst[t / 64] |= 1 << (t % 64);
                            let raw = SlotLayout::extract(*bits, &src[bw..], r);
                            let mapped = map.as_ref().map_or(raw, |m| m[raw as usize]);
                            SlotLayout::set_zeroed(*bits, &mut dst[bw..], t, mapped);
                        }
                    }
                }
                PermPlan::Dyn(perm, id) | PermPlan::Ref(perm, _, id) => {
                    // Handles are never reused for other values, and the states
                    // of a search share most of their values: the image of a
                    // handle under this plan is looked up first.
                    let slot =
                        (src[0] ^ id.wrapping_mul(0x9e37_79b9_7f4a_7c15)).wrapping_mul(0xff51_afd7_ed55_8ccd) >> (64 - DYN_MEMO_BITS);
                    let hit = DYN_MEMO.with(|m| {
                        let m = m.borrow();
                        m.get(slot as usize).filter(|e| e.0 == *id && e.1 == src[0]).map(|e| e.2)
                    });
                    if let Some(h) = hit {
                        dst[0] = h;
                        return;
                    }
                    let store = match self {
                        PermPlan::Ref(_, store, _) => Some(store),
                        _ => None,
                    };
                    let v = match store {
                        Some(s) if TRUSTED => s.thaw(src[0]),
                        Some(s) => s.try_thaw(src[0]).expect("valid value store handle"),
                        None if TRUSTED => dynval::lookup_unchecked(src[0]),
                        None => dynval::lookup(src[0]),
                    };
                    // Permuting a normalized value cannot fail in practice; keep
                    // the value if it does.
                    let image = |m| {
                        let x = Value::ModelValue(m);
                        let y = perm(&x);
                        (y != x).then_some(y)
                    };
                    dst[0] = match tlx_value::ops::permute_shared(&v, &image) {
                        // (A full store keeps the handle: the run stops on it.)
                        Ok(Some(p)) => match store {
                            Some(s) => s.freeze(&p).unwrap_or(src[0]),
                            None => dynval::intern(&p),
                        },
                        _ => src[0],
                    };
                    DYN_MEMO.with(|m| {
                        let mut m = m.borrow_mut();
                        if m.is_empty() {
                            m.resize(1 << DYN_MEMO_BITS, (0, 0, 0));
                        }
                        m[slot as usize] = (*id, src[0], dst[0]);
                    });
                }
            }
        }
    }
}

fn apply_flat(ops: &[FlatOp], src: &[u64], dst: &mut [u64]) {
    for op in ops {
        match op {
            FlatOp::Zero { dst: d, len } => {
                let (d, l) = (*d as usize, *len as usize);
                dst[d..d + l].fill(0);
            }
            FlatOp::Copy { src: s, dst: d, len } => {
                let (s, d, l) = (*s as usize, *d as usize, *len as usize);
                if l <= 4 {
                    // Short runs (typically single slots): no memmove call.
                    #[allow(clippy::manual_memcpy)] // short runs: a plain loop, no memmove call
                    for k in 0..l {
                        dst[d + k] = src[s + k];
                    }
                } else {
                    dst[d..d + l].copy_from_slice(&src[s..s + l]);
                }
            }
            FlatOp::Atom { src: s, dst: d, map } => dst[*d as usize] = map[src[*s as usize] as usize],
            FlatOp::BitCopy { src: s, dst: d } => d.set_zeroed(dst, s.extract(src)),
            FlatOp::BitAtom { src: s, dst: d, map } => d.set_zeroed(dst, map[s.extract(src) as usize]),
        }
    }
}

fn is_identity(map: impl Iterator<Item = usize>) -> bool {
    map.enumerate().all(|(i, m)| i == m)
}

/// The permutation of ranks in the (finite, bitset-sized) universe of
/// `elem` induced by `permute_value`; `None` if the universe is not closed
/// under it.
fn rank_map(elem: &Shape, permute_value: &dyn Fn(&Value) -> Option<Value>) -> Option<Vec<u32>> {
    let card = bitset_universe(elem)?;
    let mut map = Vec::with_capacity(card as usize);
    for r in 0..card {
        let p = permute_value(&unrank(elem, r))?;
        map.push(rank(elem, &p).ok()? as u32);
    }
    Some(map)
}

/// Plan for a `Record` or `Tuple` (`parts` in field/position order).
fn product_slots(parts: &[&Shape], perm: &AtomPerm, n: usize) -> Option<PermPlan> {
    let fl = FieldLayout::of_shapes(parts.iter().copied());
    let plans: Vec<PermPlan> = parts.iter().map(|p| PermPlan::compile(p, perm)).collect::<Option<_>>()?;
    if plans.iter().all(PermPlan::is_identity) {
        return Some(PermPlan::Copy(n));
    }
    // Group into disjoint word-aligned units using `FieldLayout::word_groups`
    // so zero-storage children between packed scalars keep them in one word.
    let mut unit_offs: Vec<usize> = Vec::new();
    let mut unit_plans: Vec<PermPlan> = Vec::new();
    for group in fl.word_groups() {
        match group {
            FieldGroup::Word { index, offset, .. } => {
                unit_offs.push(*offset);
                unit_plans.push(plans[*index].clone());
            }
            FieldGroup::Packed { word, fields } => {
                unit_offs.push(*word);
                if fields.iter().all(|&(i, _)| plans[i].is_identity()) {
                    unit_plans.push(PermPlan::Copy(1));
                } else {
                    let mut bops = vec![FlatOp::Zero { dst: 0, len: 1 }];
                    for &(i, pos) in fields.iter() {
                        let rel = BitPos::new(0, pos.shift, pos.bits);
                        match &plans[i] {
                            PermPlan::Copy(_) => bops.push(FlatOp::BitCopy { src: rel, dst: rel }),
                            PermPlan::Atom(map) => bops.push(FlatOp::BitAtom { src: rel, dst: rel, map: map.clone() }),
                            _ => unreachable!("packed scalar plan must be Copy or Atom"),
                        }
                    }
                    unit_plans.push(PermPlan::Flat(bops.into()));
                }
            }
        }
    }
    let mut ops = Vec::new();
    if unit_plans.iter().zip(&unit_offs).all(|(p, &o)| flatten(p, o, o, &mut ops)) {
        return Some(PermPlan::Flat(merge_flat_ops(ops).into()));
    }
    let src: Box<[usize]> = unit_offs.clone().into();
    let dst: Box<[usize]> = unit_offs.into();
    Some(PermPlan::Slots { src, dst, plans: unit_plans.into() })
}

/// Plan for a `Fcn` over `len` domain elements where slot `i` moves to `moved[i]`.
fn fcn_slots(range: &Shape, len: usize, moved: &[usize], perm: &AtomPerm, n: usize) -> Option<PermPlan> {
    let rp = PermPlan::compile(range, perm)?;
    let identity_moves = is_identity(moved.iter().copied());
    if identity_moves && rp.is_identity() {
        return Some(PermPlan::Copy(n));
    }
    match SlotLayout::of(range) {
        SlotLayout::Words(rw) => {
            if rw == 0 {
                return Some(PermPlan::Copy(0));
            }
            let offs: Vec<usize> = (0..len).map(|i| i * rw).collect();
            let dst: Vec<usize> = (0..len).map(|i| moved[i] * rw).collect();
            let mut ops = Vec::new();
            if offs.iter().zip(&dst).all(|(&s, &d)| flatten(&rp, s, d, &mut ops)) {
                return Some(PermPlan::Flat(merge_flat_ops(ops).into()));
            }
            let plans: Vec<PermPlan> = vec![rp; len];
            Some(PermPlan::Slots { src: offs.into(), dst: dst.into(), plans: plans.into() })
        }
        SlotLayout::Bits(bits) => {
            let mut ops = vec![FlatOp::Zero { dst: 0, len: n as u32 }];
            for (i, &target) in moved.iter().enumerate() {
                let FieldLoc::Bits(s) = SlotLayout::Bits(bits).loc(0, i) else { unreachable!() };
                let FieldLoc::Bits(d) = SlotLayout::Bits(bits).loc(0, target) else { unreachable!() };
                match &rp {
                    PermPlan::Copy(_) => ops.push(FlatOp::BitCopy { src: s, dst: d }),
                    PermPlan::Atom(map) => ops.push(FlatOp::BitAtom { src: s, dst: d, map: map.clone() }),
                    _ => unreachable!("packed scalar plan must be Copy or Atom"),
                }
            }
            Some(PermPlan::Flat(merge_flat_ops(ops).into()))
        }
    }
}

/// Append the flat ops of plan `p` applied from word `s` to word `d`; false
/// if `p` is not at fixed word positions.
fn flatten(p: &PermPlan, s: usize, d: usize, ops: &mut Vec<FlatOp>) -> bool {
    let (Ok(s32), Ok(d32)) = (u32::try_from(s), u32::try_from(d)) else {
        return false;
    };
    match p {
        PermPlan::Copy(0) => {}
        PermPlan::Copy(n) => {
            let Ok(len) = u32::try_from(*n) else {
                return false;
            };
            ops.push(FlatOp::Copy { src: s32, dst: d32, len });
        }
        PermPlan::Atom(map) => ops.push(FlatOp::Atom { src: s32, dst: d32, map: map.clone() }),
        PermPlan::Flat(inner) => {
            for op in inner.iter() {
                let shifted = match op {
                    FlatOp::Zero { dst, len } => dst.checked_add(d32).map(|dst| FlatOp::Zero { dst, len: *len }),
                    FlatOp::Copy { src, dst, len } => {
                        src.checked_add(s32).zip(dst.checked_add(d32)).map(|(src, dst)| FlatOp::Copy { src, dst, len: *len })
                    }
                    FlatOp::Atom { src, dst, map } => {
                        src.checked_add(s32).zip(dst.checked_add(d32)).map(|(src, dst)| FlatOp::Atom { src, dst, map: map.clone() })
                    }
                    FlatOp::BitCopy { src, dst } => Some(FlatOp::BitCopy { src: src.offset_words(s), dst: dst.offset_words(d) }),
                    FlatOp::BitAtom { src, dst, map } => {
                        Some(FlatOp::BitAtom { src: src.offset_words(s), dst: dst.offset_words(d), map: map.clone() })
                    }
                };
                let Some(shifted) = shifted else { return false };
                ops.push(shifted);
            }
        }
        _ => return false,
    }
    true
}

/// Hoist `Zero` ops before bit writes when contiguous or adjacent, and merge
/// adjacent `Copy` / `Zero` runs.
fn merge_flat_ops(ops: Vec<FlatOp>) -> Vec<FlatOp> {
    let mut out: Vec<FlatOp> = Vec::with_capacity(ops.len());
    for op in ops {
        match (out.last_mut(), &op) {
            (Some(FlatOp::Copy { src: s0, dst: d0, len: l0 }), FlatOp::Copy { src, dst, len })
                if *s0 + *l0 == *src && *d0 + *l0 == *dst =>
            {
                *l0 += len;
                continue;
            }
            (Some(FlatOp::Zero { dst: d0, len: l0 }), FlatOp::Zero { dst, len }) if *d0 + *l0 == *dst => {
                *l0 += len;
                continue;
            }
            _ => {}
        }
        out.push(op);
    }
    out
}

/// Sort `n`-word elements lexicographically (insertion sort: sets are small).
fn sort_elems(w: &mut [u64], n: usize) {
    let len = w.len() / n;
    for i in 1..len {
        let mut j = i;
        while j > 0 && w[(j - 1) * n..j * n] > w[j * n..(j + 1) * n] {
            for k in 0..n {
                w.swap((j - 1) * n + k, j * n + k);
            }
            j -= 1;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::layout::{decode, encode};
    use tlx_value::Sym;

    fn mv(s: &str) -> Value {
        Value::ModelValue(Sym::new(s))
    }

    fn atoms(xs: &[&str]) -> Shape {
        let mut v: Vec<Value> = xs.iter().map(|x| mv(x)).collect();
        v.sort();
        Shape::Atom(v.into())
    }

    /// The swap a <-> b.
    fn swap(a: &'static str, b: &'static str) -> AtomPerm {
        Arc::new(move |v: &Value| match v {
            Value::ModelValue(m) if m.as_str() == a => mv(b),
            Value::ModelValue(m) if m.as_str() == b => mv(a),
            _ => v.clone(),
        })
    }

    /// `plan(encode(v)) == encode(permute(v))` for every value of `shape`.
    fn check_all(shape: &Shape, perm: &AtomPerm) {
        let plan = PermPlan::compile(shape, perm).expect("plan");
        let n = words(shape);
        let card = shape.cardinality().expect("finite shape");
        for r in 0..card {
            let v = unrank(shape, r);
            let mut src = vec![0u64; n];
            encode(shape, &v, &mut src).unwrap();
            let mut dst = vec![u64::MAX; n];
            plan.apply(&src, &mut dst);
            let want = tlx_value::ops::permute(&v, &|m| Some(perm(&Value::ModelValue(m)))).unwrap();
            let mut enc_want = vec![0u64; n];
            encode(shape, &want, &mut enc_want).unwrap();
            assert_eq!(dst, enc_want, "permuting {v} (got {})", decode(shape, &dst));
        }
    }

    #[test]
    fn maps_permute_keys_and_values() {
        let a = atoms(&["a", "b", "c"]);
        let m = Shape::Map { key: Box::new(a.clone()), range: Box::new(a.clone()) };
        check_all(&m, &swap("a", "c"));
        let m2 = Shape::Map { key: Box::new(Shape::Int { lo: 0, hi: 2 }), range: Box::new(a.clone()) };
        check_all(&m2, &swap("a", "b"));
    }

    #[test]
    fn records_and_functions_flatten() {
        let a = atoms(&["a", "b"]);
        // Fields and domain in `Sym` order: the tests of this binary share
        // the intern table, so another test may have interned "b" or "y"
        // first.
        let mut fields = vec![(Sym::new("x"), a.clone()), (Sym::new("y"), Shape::Int { lo: 0, hi: 2 })];
        fields.sort_by_key(|f| f.0);
        let mut dom = vec![mv("a"), mv("b")];
        dom.sort();
        let r = Shape::Record(fields.into());
        let f = Shape::Fcn { dom: dom.into(), range: Box::new(r) };
        let p = PermPlan::compile(&f, &swap("a", "b")).unwrap();
        assert!(matches!(p, PermPlan::Flat(_)), "{p:?}");
        check_all(&f, &swap("a", "b"));
    }

    #[test]
    fn unions_sets_and_sequences() {
        let a = atoms(&["a", "b", "c"]);
        let u = Shape::Union(vec![a.clone(), Shape::Record(vec![(Sym::new("n"), a.clone())].into())].into());
        check_all(&Shape::Seq { elem: Box::new(u.clone()), max_len: 2 }, &swap("a", "b"));
        check_all(&Shape::Set { elem: Box::new(a.clone()), max_card: 3 }, &swap("b", "c"));
        let pairs = Shape::Tuple(vec![a.clone(), Shape::Bool].into());
        check_all(&Shape::Set { elem: Box::new(pairs), max_card: 2 }, &swap("a", "c"));
    }

    #[test]
    fn dyn_handles() {
        let perm = swap("a", "b");
        let plan = PermPlan::compile(&Shape::Dyn, &perm).unwrap();
        let v = Value::set_from(vec![mv("a"), mv("c")]).unwrap();
        let mut dst = [0u64];
        plan.apply(&[dynval::intern(&v)], &mut dst);
        assert_eq!(dynval::lookup(dst[0]), Value::set_from(vec![mv("b"), mv("c")]).unwrap());
    }

    #[test]
    fn store_handles() {
        let store = crate::store::StoreRef::new(usize::MAX);
        let shape = Shape::Tuple(vec![Shape::Bool, Shape::Ref(store.clone())].into());
        let perm = swap("a", "b");
        let plan = PermPlan::compile(&shape, &perm).unwrap();
        let rec = |x: &str| Value::record(vec![(Sym::new("src"), mv(x)), (Sym::new("log"), Value::tuple(vec![mv("c"), mv(x)]))]);
        let bag = |x: &str, y: &str| {
            tlx_value::ops::fcn_merge(
                &tlx_value::ops::single_fcn(rec(x), Value::Int(1)).unwrap(),
                &tlx_value::ops::single_fcn(rec(y), Value::Int(2)).unwrap(),
            )
            .unwrap()
        };
        for (v, want) in [(bag("a", "c"), bag("b", "c")), (bag("b", "a"), bag("a", "b"))] {
            let src = [1, store.freeze(&v).unwrap()];
            let mut dst = [0u64; 2];
            plan.apply(&src, &mut dst);
            assert_eq!(dst[0], 1);
            // (The image is the permuted value as stored: same node, same
            // representation; memoized the second time.)
            assert_eq!(dst[1], store.freeze(&want).unwrap());
            assert_eq!(store.thaw(dst[1]), want);
            let mut again = [0u64; 2];
            plan.apply(&src, &mut again);
            assert_eq!(again, dst);
        }
    }

    #[test]
    fn not_closed() {
        let a = atoms(&["a", "b"]);
        assert!(PermPlan::compile(&a, &swap("a", "c")).is_none());
    }
}
