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

use tlx_value::{Sym, Value};

use crate::dynval;
use crate::layout::{bitset_universe, rank, unrank, words, BitPos, FieldGroup, FieldLayout, FieldLoc, MapDims, SlotLayout};
use crate::shape::{binom, FcnWitness};
use crate::Shape;

/// Numbers of the `PermPlan::Dyn` plans (from 1: 0 marks an empty memo
/// entry).
static NEXT_DYN_PLAN: AtomicU64 = AtomicU64::new(1);

/// Log2 of the entries of `DYN_MEMO`.
const DYN_MEMO_BITS: u32 = 12;

thread_local! {
    /// Images of `Dyn` / `Ref` handles, direct-mapped: (plan number, gc generation, handle, image).
    /// `Dyn` uses generation 0; `Ref` keys on `store.gc_gen()` so entries whose
    /// output handle was swept are never returned after a GC cycle.
    static DYN_MEMO: RefCell<Vec<(u64, u64, u64, u64)>> = const { RefCell::new(Vec::new()) };
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
    /// one `range_words` slot per key, plus an optional trailing witness word.
    /// Key rank `r` moves to `keys[r]`.
    Map { keys: Box<[u32]>, bitset_words: usize, range: Box<PermPlan>, range_words: usize, words: usize, dynamic_witness: bool },
    /// A map with sub-word packed values (`bits`-wide, mapped through `map` if atoms),
    /// plus an optional trailing witness word.
    MapBits { keys: Box<[u32]>, bitset_words: usize, bits: u8, map: Option<Arc<[u64]>>, words: usize, dynamic_witness: bool },
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
            Shape::Fcn { dom, range, witness, key_variants } => {
                // Slot of key k moves to the slot of perm(k).
                let extra = witness.extra_words() + key_variants.len();
                let mut moved = Vec::with_capacity(dom.len());
                if key_variants.is_empty() {
                    for k in dom.iter() {
                        let pk = permute_value(k)?;
                        moved.push(dom.iter().position(|d| d.exact_eq(&pk))?);
                    }
                } else {
                    // Key-variant indices are fixed per position; only permute in
                    // place when every key (and every variant) is fixed by `perm`.
                    for (i, k) in dom.iter().enumerate() {
                        if !permute_value(k)?.exact_eq(k) {
                            return None;
                        }
                        moved.push(i);
                    }
                    for (_, vs) in key_variants.iter() {
                        for k in vs.iter() {
                            if !permute_value(k)?.exact_eq(k) {
                                return None;
                            }
                        }
                    }
                }
                fcn_slots(range, dom.len(), &moved, extra, perm, n)?
            }
            Shape::Map { key, range, witness } => {
                let keys = rank_map(key, &permute_value)?;
                let d = MapDims::new(keys.len(), SlotLayout::of(range));
                let range_plan = PermPlan::compile(range, perm)?;
                let dynamic_witness = *witness == crate::FcnWitness::Dynamic;
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
                            dynamic_witness,
                        },
                        SlotLayout::Bits(bits) => {
                            let map = match range_plan {
                                PermPlan::Copy(_) => None,
                                PermPlan::Atom(m) => Some(m),
                                _ => unreachable!("packed scalar plan must be Copy or Atom"),
                            };
                            PermPlan::MapBits { keys: keys.into(), bitset_words: d.bitset_words, bits, map, words: n, dynamic_witness }
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
                PermPlan::Map { keys, bitset_words, range, range_words, words, dynamic_witness } => {
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
                    if *dynamic_witness {
                        dst[*words - 1] = src[*words - 1];
                    }
                }
                PermPlan::MapBits { keys, bitset_words, bits, map, words, dynamic_witness } => {
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
                    if *dynamic_witness {
                        dst[*words - 1] = src[*words - 1];
                    }
                }
                PermPlan::Dyn(perm, id) | PermPlan::Ref(perm, _, id) => {
                    // Handles are never reused for other values, and the states
                    // of a search share most of their values: the image of a
                    // handle under this plan is looked up first (keyed by
                    // `gc_gen` for `Ref` so swept nodes are never returned).
                    let store = match self {
                        PermPlan::Ref(_, store, _) => Some(store),
                        _ => None,
                    };
                    let gen = store.map_or(0, |s| s.gc_gen());
                    let slot =
                        (src[0] ^ id.wrapping_mul(0x9e37_79b9_7f4a_7c15)).wrapping_mul(0xff51_afd7_ed55_8ccd) >> (64 - DYN_MEMO_BITS);
                    let hit = DYN_MEMO.with(|m| {
                        let m = m.borrow();
                        m.get(slot as usize).filter(|e| e.0 == *id && e.1 == gen && e.2 == src[0]).map(|e| e.3)
                    });
                    if let Some(h) = hit {
                        dst[0] = h;
                        return;
                    }
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
                    let mut cacheable = true;
                    dst[0] = match tlx_value::ops::permute_shared(&v, &image) {
                        // (A full store keeps the handle and records STORE_FULL_HIT;
                        // do not memoize it so a retry after GC computes the image.)
                        Ok(Some(p)) => match store {
                            Some(s) => match s.freeze(&p) {
                                Ok(h) => h,
                                Err(_) => {
                                    cacheable = false;
                                    src[0]
                                }
                            },
                            None => dynval::intern_exact(&p),
                        },
                        _ => src[0],
                    };
                    if cacheable {
                        DYN_MEMO.with(|m| {
                            let mut m = m.borrow_mut();
                            if m.is_empty() {
                                m.resize(1 << DYN_MEMO_BITS, (0, 0, 0, 0));
                            }
                            m[slot as usize] = (*id, gen, src[0], dst[0]);
                        });
                    }
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

/// Plan for a `Fcn` over `len` domain elements where slot `i` moves to `moved[i]`,
/// followed by `extra` invariant trailing witness / key-variant words.
fn fcn_slots(range: &Shape, len: usize, moved: &[usize], extra: usize, perm: &AtomPerm, n: usize) -> Option<PermPlan> {
    let rp = PermPlan::compile(range, perm)?;
    let identity_moves = is_identity(moved.iter().copied());
    if identity_moves && rp.is_identity() {
        return Some(PermPlan::Copy(n));
    }
    let slot = SlotLayout::of(range);
    let payload_words = slot.array_words(len);
    match slot {
        SlotLayout::Words(rw) => {
            if rw == 0 {
                return Some(PermPlan::Copy(n));
            }
            let mut offs: Vec<usize> = (0..len).map(|i| i * rw).collect();
            let mut dst: Vec<usize> = (0..len).map(|i| moved[i] * rw).collect();
            let mut ops = Vec::new();
            if offs.iter().zip(&dst).all(|(&s, &d)| flatten(&rp, s, d, &mut ops))
                && (extra == 0 || flatten(&PermPlan::Copy(extra), payload_words, payload_words, &mut ops))
            {
                return Some(PermPlan::Flat(merge_flat_ops(ops).into()));
            }
            let mut plans: Vec<PermPlan> = vec![rp; len];
            if extra > 0 {
                offs.push(payload_words);
                dst.push(payload_words);
                plans.push(PermPlan::Copy(extra));
            }
            Some(PermPlan::Slots { src: offs.into(), dst: dst.into(), plans: plans.into() })
        }
        SlotLayout::Bits(bits) => {
            let mut ops = vec![FlatOp::Zero { dst: 0, len: payload_words as u32 }];
            for (i, &target) in moved.iter().enumerate() {
                let FieldLoc::Bits(s) = SlotLayout::Bits(bits).loc(0, i) else { unreachable!() };
                let FieldLoc::Bits(d) = SlotLayout::Bits(bits).loc(0, target) else { unreachable!() };
                match &rp {
                    PermPlan::Copy(_) => ops.push(FlatOp::BitCopy { src: s, dst: d }),
                    PermPlan::Atom(map) => ops.push(FlatOp::BitAtom { src: s, dst: d, map: map.clone() }),
                    _ => unreachable!("packed scalar plan must be Copy or Atom"),
                }
            }
            if extra > 0 {
                ops.push(FlatOp::Copy { src: payload_words as u32, dst: payload_words as u32, len: extra as u32 });
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

// ---------------------------------------------------------------------------
// Factorized disjoint-product symmetry plans (`prod_g Sym(K_g)`)
// ---------------------------------------------------------------------------

/// One full symmetric-group factor `Sym(K_g)` over `keys` sorted strictly
/// ascending in TLC order (`Sym::cmp`).
#[derive(Clone, Debug)]
pub struct FactorDesc {
    pub keys: Box<[Sym]>,
    /// Pre-built `Value::ModelValue(k)` matching `keys` for zero-alloc lookup.
    pub values: Box<[Value]>,
    /// Start offset of this factor in flat per-key target-index tables (`img`).
    pub offset: usize,
}

/// Read-only descriptor of a disjoint product `S_{n_1} x ... x S_{n_k}` used to
/// compile and apply per-variable [`FactorPlan`]s without materializing `|G|`
/// explicit permutation tables.
#[derive(Clone, Debug)]
pub struct FactorGroupSpec {
    pub factors: Box<[FactorDesc]>,
    /// Sorted by `sym.id()`: `(sym_id, factor_idx, key_idx)`.
    key_index: Box<[(u32, u16, u16)]>,
    min_id: u32,
    max_id: u32,
    pub total_keys: usize,
}

impl FactorGroupSpec {
    /// Build a factorized group descriptor from per-factor sorted `Sym` slices.
    pub fn new(raw_factors: &[&[Sym]]) -> Self {
        let mut factors = Vec::with_capacity(raw_factors.len());
        let mut key_index = Vec::new();
        let mut offset = 0usize;
        for (g, &keys) in raw_factors.iter().enumerate() {
            debug_assert!(keys.len() >= 2);
            debug_assert!(keys.windows(2).all(|w| w[0] < w[1]));
            for (k, &s) in keys.iter().enumerate() {
                key_index.push((s.id(), g as u16, k as u16));
            }
            let values: Box<[Value]> = keys.iter().copied().map(Value::ModelValue).collect();
            factors.push(FactorDesc { keys: keys.into(), values, offset });
            offset += keys.len();
        }
        key_index.sort_unstable_by_key(|&(id, _, _)| id);
        let min_id = key_index.first().map_or(u32::MAX, |&(id, _, _)| id);
        let max_id = key_index.last().map_or(0, |&(id, _, _)| id);
        Self { factors: factors.into(), key_index: key_index.into(), min_id, max_id, total_keys: offset }
    }

    #[inline]
    pub fn lookup(&self, m: Sym) -> Option<(usize, usize)> {
        let id = m.id();
        if id < self.min_id || id > self.max_id {
            return None;
        }
        if self.key_index.len() <= 8 {
            for &(k, g, ki) in self.key_index.iter() {
                if k == id {
                    return Some((g as usize, ki as usize));
                }
                if k > id {
                    return None;
                }
            }
            return None;
        }
        let idx = self.key_index.binary_search_by_key(&id, |&(k, _, _)| k).ok()?;
        let (_, g, k) = self.key_index[idx];
        Some((g as usize, k as usize))
    }

    /// Fill `dst[..self.total_keys]` with the identity target-index table.
    #[inline]
    pub fn fill_identity_img(&self, dst: &mut [u16]) {
        for f in self.factors.iter() {
            let off = f.offset;
            for i in 0..f.keys.len() {
                dst[off + i] = i as u16;
            }
        }
    }

    pub fn identity_img(&self) -> Vec<u16> {
        let mut img = vec![0u16; self.total_keys];
        self.fill_identity_img(&mut img);
        img
    }

    /// Image of model value `m` under flat image table `img`, or `None` when
    /// fixed (for `tlx_value::ops::permute_shared`).
    #[inline]
    pub fn map_sym(&self, m: Sym, img: &[u16]) -> Option<&Value> {
        let (g, k) = self.lookup(m)?;
        let f = &self.factors[g];
        let t = img[f.offset + k] as usize;
        (t != k).then_some(&f.values[t])
    }
}

/// Compiled atom-code mapping for `Shape::Atom(u)` under a [`FactorGroupSpec`].
#[derive(Clone, Debug)]
pub struct AtomTable {
    /// For each atom code `c in 0..u.len()`: `Some((factor_idx, key_idx))` if
    /// moved by `G`, else `None` (fixed atom).
    pub code_to_key: Box<[Option<(u16, u16)>]>,
    /// Indexed by `factor.offset + key_idx`: atom code in `u` (`u64::MAX` if
    /// that factor does not occur in `u`).
    pub key_to_code: Box<[u64]>,
    /// Factor indices that occur in `u`.
    pub active_factors: Box<[u16]>,
    /// `Some(g)` iff `u` consists solely of factor `g`'s keys with `code == key_idx`.
    pub direct_factor: Option<u16>,
}

impl AtomTable {
    /// Compile an atom table for sorted universe `u`.
    /// Returns `None` if `u` is not closed under `fg` (contains a proper
    /// non-empty subset of some factor `K_g`), `Some(None)` if `u` contains no
    /// moved atoms, and `Some(Some(table))` otherwise.
    pub fn compile(u: &[Value], fg: &FactorGroupSpec) -> Option<Option<Arc<AtomTable>>> {
        let mut code_to_key = vec![None; u.len()];
        let mut key_to_code = vec![u64::MAX; fg.total_keys];
        let mut counts = vec![0usize; fg.factors.len()];
        for (code, v) in u.iter().enumerate() {
            if let Value::ModelValue(m) = v {
                if let Some((g, k)) = fg.lookup(*m) {
                    code_to_key[code] = Some((g as u16, k as u16));
                    key_to_code[fg.factors[g].offset + k] = code as u64;
                    counts[g] += 1;
                }
            }
        }
        let mut active_factors = Vec::new();
        for (g, &cnt) in counts.iter().enumerate() {
            if cnt == 0 {
                continue;
            }
            if cnt != fg.factors[g].keys.len() {
                return None;
            }
            active_factors.push(g as u16);
        }
        if active_factors.is_empty() {
            return Some(None);
        }
        let direct_factor = if active_factors.len() == 1 {
            let g = active_factors[0] as usize;
            let f = &fg.factors[g];
            if u.len() == f.keys.len() && (0..f.keys.len()).all(|k| key_to_code[f.offset + k] == k as u64) {
                Some(g as u16)
            } else {
                None
            }
        } else {
            None
        };
        Some(Some(Arc::new(AtomTable {
            code_to_key: code_to_key.into(),
            key_to_code: key_to_code.into(),
            active_factors: active_factors.into(),
            direct_factor,
        })))
    }

    #[inline]
    pub fn map_code(&self, fg: &FactorGroupSpec, img: &[u16], code: u64) -> u64 {
        if let Some(g) = self.direct_factor {
            return img[fg.factors[g as usize].offset + code as usize] as u64;
        }
        match self.code_to_key[code as usize] {
            None => code,
            Some((g, k)) => {
                let off = fg.factors[g as usize].offset;
                self.key_to_code[off + img[off + k as usize] as usize]
            }
        }
    }
}

/// How a `Shape::Fcn` domain permutes under a [`FactorGroupSpec`].
#[derive(Clone, Debug)]
pub enum DomMap {
    /// Domain contains no moved atoms (slot `i` stays at slot `i`).
    Fixed(usize),
    /// Domain is identically factor `factor`'s sorted key list `K_g`.
    DirectFactor { factor: u16, len: usize },
    /// Domain is a closed set of atoms (multi-factor or mixed with fixed atoms).
    AtomDom(Arc<AtomTable>),
    /// Compound finite domain mapped via a [`RankPlan`].
    Ranked { slot_to_rank: Box<[u64]>, rank_to_slot: Box<[u32]>, plan: Box<RankPlan> },
    /// General compound domain (rare: non-bitset-sized shape) mapped via sorted binary search.
    ValueDom(Arc<[Value]>),
}

impl DomMap {
    #[inline]
    pub fn len(&self) -> usize {
        match self {
            DomMap::Fixed(n) | DomMap::DirectFactor { len: n, .. } => *n,
            DomMap::AtomDom(t) => t.code_to_key.len(),
            DomMap::Ranked { slot_to_rank, .. } => slot_to_rank.len(),
            DomMap::ValueDom(d) => d.len(),
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[inline]
    pub fn is_identity(&self) -> bool {
        matches!(self, DomMap::Fixed(_))
    }

    #[inline]
    pub fn map_slot(&self, fg: &FactorGroupSpec, img: &[u16], slot: usize) -> usize {
        match self {
            DomMap::Fixed(_) => slot,
            DomMap::DirectFactor { factor, .. } => img[fg.factors[*factor as usize].offset + slot] as usize,
            DomMap::AtomDom(t) => t.map_code(fg, img, slot as u64) as usize,
            DomMap::Ranked { slot_to_rank, rank_to_slot, plan } => {
                let nr = plan.map_rank(fg, img, slot_to_rank[slot]);
                rank_to_slot[nr as usize] as usize
            }
            DomMap::ValueDom(dom) => {
                let v = &dom[slot];
                match tlx_value::ops::permute_shared(v, &|m| fg.map_sym(m, img).cloned()) {
                    Ok(Some(p)) => dom.iter().position(|d| d.exact_eq(&p)).expect("closed domain"),
                    _ => slot,
                }
            }
        }
    }

    pub fn for_each_moved_key(&self, fg: &FactorGroupSpec, f: &mut impl FnMut(usize, usize)) {
        match self {
            DomMap::Fixed(_) => {}
            DomMap::DirectFactor { factor, len } => {
                let g = *factor as usize;
                for k in 0..*len {
                    f(g, k);
                }
            }
            DomMap::AtomDom(t) => {
                for &g in t.active_factors.iter() {
                    let g = g as usize;
                    for k in 0..fg.factors[g].keys.len() {
                        f(g, k);
                    }
                }
            }
            DomMap::Ranked { slot_to_rank, plan, .. } => {
                for &r in slot_to_rank.iter() {
                    plan.for_each_moved_key(fg, r, f);
                }
            }
            DomMap::ValueDom(dom) => {
                for v in dom.iter() {
                    for_each_moved_in_value(v, fg, f);
                }
            }
        }
    }

    fn compile(dom: &[Value], fg: &FactorGroupSpec) -> Option<DomMap> {
        if dom.is_empty() || !dom.iter().any(|d| value_has_moved(d, fg)) {
            return Some(DomMap::Fixed(dom.len()));
        }
        if dom.iter().all(|d| matches!(d, Value::ModelValue(_) | Value::Str(_))) {
            let table = AtomTable::compile(dom, fg)?.expect("moved atoms present");
            if let Some(factor) = table.direct_factor {
                return Some(DomMap::DirectFactor { factor, len: dom.len() });
            }
            return Some(DomMap::AtomDom(table));
        }
        // Compound domain keys: closed under prod_g Sym(K_g) iff closed under
        // every adjacent transposition generator (k, k+1) of each factor.
        let mut gen_img = fg.identity_img();
        for factor in fg.factors.iter() {
            let off = factor.offset;
            for k in 0..factor.keys.len() - 1 {
                gen_img[off + k] = (k + 1) as u16;
                gen_img[off + k + 1] = k as u16;
                for d in dom {
                    let pk = tlx_value::ops::permute_shared(d, &|m| fg.map_sym(m, &gen_img).cloned()).ok()?;
                    if let Some(pk) = pk {
                        if !dom.iter().any(|x| x.exact_eq(&pk)) {
                            return None;
                        }
                    }
                }
                gen_img[off + k] = k as u16;
                gen_img[off + k + 1] = (k + 1) as u16;
            }
        }
        // Try building an O(1) RankPlan over the domain's joined finite shape.
        let mut joined = Shape::Never;
        for d in dom {
            joined = joined.join(&Shape::of(d));
        }
        if let Some(card) = bitset_universe(&joined) {
            if let Some(plan) = RankPlan::compile(&joined, fg) {
                let mut slot_to_rank = Vec::with_capacity(dom.len());
                let mut rank_to_slot = vec![u32::MAX; card as usize];
                let mut ok = true;
                for (i, d) in dom.iter().enumerate() {
                    if let Ok(r) = rank(&joined, d) {
                        if (r as usize) < rank_to_slot.len() && rank_to_slot[r as usize] == u32::MAX {
                            slot_to_rank.push(r);
                            rank_to_slot[r as usize] = i as u32;
                            continue;
                        }
                    }
                    ok = false;
                    break;
                }
                if ok {
                    return Some(DomMap::Ranked {
                        slot_to_rank: slot_to_rank.into(),
                        rank_to_slot: rank_to_slot.into(),
                        plan: Box::new(plan),
                    });
                }
            }
        }
        Some(DomMap::ValueDom(dom.into()))
    }
}

/// Pure integer permutation of ranks in a finite bitset-sized universe
/// (`<= MAX_BITSET_UNIVERSE`) under a [`FactorGroupSpec`].
#[derive(Clone, Debug)]
pub enum RankPlan {
    Identity,
    Atom(Arc<AtomTable>),
    Product { cards: Box<[u64]>, plans: Box<[RankPlan]> },
    Fcn { dom: DomMap, range_card: u64, range: Box<RankPlan> },
    Map { universe: usize, key: Box<RankPlan>, range_card: u64, range: Box<RankPlan> },
    Seq { elem_card: u64, elem: Box<RankPlan>, shorter: Box<[u64]> },
    SetMask { elem: Box<RankPlan> },
    SetComb { n: u64, by_size: Box<[u64]>, elem: Box<RankPlan> },
    Union { base: Box<[u64]>, arms: Box<[RankPlan]> },
}

impl RankPlan {
    /// Compile a factorized rank permutation plan for finite shape `shape`.
    /// Returns `None` if `shape` has no finite universe or is not closed under `fg`.
    pub fn compile(shape: &Shape, fg: &FactorGroupSpec) -> Option<RankPlan> {
        let _card = shape.cardinality()?;
        Some(match shape {
            Shape::Never | Shape::Bool | Shape::Int { .. } => RankPlan::Identity,
            Shape::Atom(u) => match AtomTable::compile(u, fg)? {
                None => RankPlan::Identity,
                Some(t) => RankPlan::Atom(t),
            },
            Shape::Record(fs) => {
                let plans: Vec<RankPlan> = fs.iter().map(|(_, f)| RankPlan::compile(f, fg)).collect::<Option<_>>()?;
                let cards: Vec<u64> = fs.iter().map(|(_, f)| f.cardinality().unwrap()).collect();
                compact_rank_product(cards, plans)
            }
            Shape::Tuple(es) => {
                let plans: Vec<RankPlan> = es.iter().map(|e| RankPlan::compile(e, fg)).collect::<Option<_>>()?;
                let cards: Vec<u64> = es.iter().map(|e| e.cardinality().unwrap()).collect();
                compact_rank_product(cards, plans)
            }
            Shape::Fcn { dom, range, witness, key_variants } => {
                if *witness == FcnWitness::Dynamic || !key_variants.is_empty() {
                    return None;
                }
                let dm = DomMap::compile(dom, fg)?;
                let rp = RankPlan::compile(range, fg)?;
                if dm.is_identity() && rp.is_identity() {
                    RankPlan::Identity
                } else {
                    RankPlan::Fcn { dom: dm, range_card: range.cardinality()?, range: Box::new(rp) }
                }
            }
            Shape::Map { key, range, witness } => {
                if *witness == FcnWitness::Dynamic {
                    return None;
                }
                let universe = bitset_universe(key)? as usize;
                let kp = RankPlan::compile(key, fg)?;
                let rp = RankPlan::compile(range, fg)?;
                if kp.is_identity() && rp.is_identity() {
                    RankPlan::Identity
                } else {
                    RankPlan::Map { universe, key: Box::new(kp), range_card: range.cardinality()?, range: Box::new(rp) }
                }
            }
            Shape::Seq { elem, max_len } => {
                let ep = RankPlan::compile(elem, fg)?;
                if ep.is_identity() || *max_len == 0 {
                    RankPlan::Identity
                } else {
                    let c = elem.cardinality()?;
                    let mut acc = 0u64;
                    let shorter: Box<[u64]> = (0..=*max_len)
                        .map(|l| {
                            let r = acc;
                            if l < *max_len {
                                acc = acc.wrapping_add(c.wrapping_pow(l as u32));
                            }
                            r
                        })
                        .collect();
                    RankPlan::Seq { elem_card: c, elem: Box::new(ep), shorter }
                }
            }
            Shape::Set { elem, max_card } => {
                let ep = RankPlan::compile(elem, fg)?;
                if ep.is_identity() || *max_card == 0 {
                    RankPlan::Identity
                } else {
                    let n = elem.cardinality()?;
                    if *max_card as u64 >= n {
                        RankPlan::SetMask { elem: Box::new(ep) }
                    } else {
                        let by_size: Box<[u64]> = (0..=*max_card as u64)
                            .scan(0u64, |acc, k| {
                                let r = *acc;
                                *acc = acc.wrapping_add(binom(n, k).unwrap_or(0));
                                Some(r)
                            })
                            .collect();
                        RankPlan::SetComb { n, by_size, elem: Box::new(ep) }
                    }
                }
            }
            Shape::Union(arms) => {
                let plans: Vec<RankPlan> = arms.iter().map(|a| RankPlan::compile(a, fg)).collect::<Option<_>>()?;
                if plans.iter().all(RankPlan::is_identity) {
                    RankPlan::Identity
                } else {
                    let mut acc = 0u64;
                    let base: Box<[u64]> = arms
                        .iter()
                        .map(|a| {
                            let r = acc;
                            acc += a.cardinality().unwrap();
                            r
                        })
                        .collect();
                    RankPlan::Union { base, arms: plans.into() }
                }
            }
            Shape::Dyn | Shape::Ref(_) => return None,
        })
    }

    #[inline]
    pub fn is_identity(&self) -> bool {
        matches!(self, RankPlan::Identity)
    }

    #[inline]
    pub fn atom_table(&self) -> Option<&Arc<AtomTable>> {
        match self {
            RankPlan::Atom(t) => Some(t),
            _ => None,
        }
    }

    /// Map rank `r` under `img` in pure integer arithmetic.
    pub fn map_rank(&self, fg: &FactorGroupSpec, img: &[u16], mut r: u64) -> u64 {
        match self {
            RankPlan::Identity => r,
            RankPlan::Atom(t) => t.map_code(fg, img, r),
            RankPlan::Product { cards, plans } => {
                let n = cards.len();
                let mut digits = [0u64; 16];
                if n <= digits.len() {
                    for i in (0..n).rev() {
                        let c = cards[i];
                        digits[i] = r % c;
                        r /= c;
                    }
                    let mut out = 0u64;
                    for i in 0..n {
                        out = out * cards[i] + plans[i].map_rank(fg, img, digits[i]);
                    }
                    out
                } else {
                    let mut v = vec![0u64; n];
                    for i in (0..n).rev() {
                        let c = cards[i];
                        v[i] = r % c;
                        r /= c;
                    }
                    let mut out = 0u64;
                    for i in 0..n {
                        out = out * cards[i] + plans[i].map_rank(fg, img, v[i]);
                    }
                    out
                }
            }
            RankPlan::Fcn { dom, range_card, range } => {
                let n = dom.len();
                let c = *range_card;
                let mut src = vec![0u64; n];
                for i in (0..n).rev() {
                    src[i] = r % c;
                    r /= c;
                }
                let mut dst = vec![0u64; n];
                for (i, &v) in src.iter().enumerate() {
                    let t = dom.map_slot(fg, img, i);
                    dst[t] = range.map_rank(fg, img, v);
                }
                dst.iter().fold(0u64, |acc, &d| acc * c + d)
            }
            RankPlan::Map { universe, key, range_card, range } => {
                let c = *range_card + 1;
                let mut src = vec![0u64; *universe];
                for i in (0..*universe).rev() {
                    src[i] = r % c;
                    r /= c;
                }
                let mut dst = vec![0u64; *universe];
                for (i, &d) in src.iter().enumerate() {
                    if d != 0 {
                        let nk = key.map_rank(fg, img, i as u64) as usize;
                        dst[nk] = 1 + range.map_rank(fg, img, d - 1);
                    }
                }
                dst.iter().fold(0u64, |acc, &d| acc * c + d)
            }
            RankPlan::Seq { elem_card, elem, shorter } => {
                let len = shorter.partition_point(|&b| b <= r) - 1;
                let mut rem = r - shorter[len];
                let c = *elem_card;
                let mut digits = vec![0u64; len];
                for i in (0..len).rev() {
                    digits[i] = rem % c;
                    rem /= c;
                }
                let mut m = 0u64;
                for &d in &digits {
                    m = m * c + elem.map_rank(fg, img, d);
                }
                shorter[len] + m
            }
            RankPlan::SetMask { elem } => {
                let mut out = 0u64;
                while r != 0 {
                    let b = r.trailing_zeros() as u64;
                    r &= r - 1;
                    out |= 1u64 << elem.map_rank(fg, img, b);
                }
                out
            }
            RankPlan::SetComb { n, by_size, elem } => {
                let k = by_size.partition_point(|&b| b <= r) - 1;
                let mut rem = r - by_size[k];
                let mut ranks = Vec::with_capacity(k);
                for i in (1..=k as u64).rev() {
                    let (mut lo, mut hi) = (i - 1, *n - 1);
                    while lo < hi {
                        let mid = lo + (hi - lo).div_ceil(2);
                        if binom(mid, i).unwrap_or(u64::MAX) <= rem {
                            lo = mid;
                        } else {
                            hi = mid - 1;
                        }
                    }
                    rem -= binom(lo, i).unwrap();
                    ranks.push(elem.map_rank(fg, img, lo));
                }
                ranks.sort_unstable();
                let mut out = by_size[k];
                for (i, &c) in ranks.iter().enumerate() {
                    out += binom(c, i as u64 + 1).unwrap();
                }
                out
            }
            RankPlan::Union { base, arms } => {
                let i = base.partition_point(|&b| b <= r) - 1;
                base[i] + arms[i].map_rank(fg, img, r - base[i])
            }
        }
    }

    /// Visit every moved `(factor_idx, key_idx)` occurring in the value of rank `r`.
    pub fn for_each_moved_key(&self, fg: &FactorGroupSpec, mut r: u64, f: &mut impl FnMut(usize, usize)) {
        match self {
            RankPlan::Identity => {}
            RankPlan::Atom(t) => {
                if let Some((g, k)) = t.code_to_key[r as usize] {
                    f(g as usize, k as usize);
                }
            }
            RankPlan::Product { cards, plans } => {
                for i in (0..cards.len()).rev() {
                    let c = cards[i];
                    let d = r % c;
                    r /= c;
                    plans[i].for_each_moved_key(fg, d, f);
                }
            }
            RankPlan::Fcn { dom, range_card, range } => {
                let n = dom.len();
                let c = *range_card;
                for _ in 0..n {
                    let d = r % c;
                    r /= c;
                    range.for_each_moved_key(fg, d, f);
                }
                dom.for_each_moved_key(fg, f);
            }
            RankPlan::Map { universe, key, range_card, range } => {
                let c = *range_card + 1;
                for i in (0..*universe).rev() {
                    let d = r % c;
                    r /= c;
                    if d != 0 {
                        key.for_each_moved_key(fg, i as u64, f);
                        range.for_each_moved_key(fg, d - 1, f);
                    }
                }
            }
            RankPlan::Seq { elem_card, elem, shorter } => {
                let len = shorter.partition_point(|&b| b <= r) - 1;
                let mut rem = r - shorter[len];
                let c = *elem_card;
                for _ in 0..len {
                    let d = rem % c;
                    rem /= c;
                    elem.for_each_moved_key(fg, d, f);
                }
            }
            RankPlan::SetMask { elem } => {
                while r != 0 {
                    let b = r.trailing_zeros() as u64;
                    r &= r - 1;
                    elem.for_each_moved_key(fg, b, f);
                }
            }
            RankPlan::SetComb { n, by_size, elem } => {
                let k = by_size.partition_point(|&b| b <= r) - 1;
                let mut rem = r - by_size[k];
                for i in (1..=k as u64).rev() {
                    let (mut lo, mut hi) = (i - 1, *n - 1);
                    while lo < hi {
                        let mid = lo + (hi - lo).div_ceil(2);
                        if binom(mid, i).unwrap_or(u64::MAX) <= rem {
                            lo = mid;
                        } else {
                            hi = mid - 1;
                        }
                    }
                    rem -= binom(lo, i).unwrap();
                    elem.for_each_moved_key(fg, lo, f);
                }
            }
            RankPlan::Union { base, arms } => {
                let i = base.partition_point(|&b| b <= r) - 1;
                arms[i].for_each_moved_key(fg, r - base[i], f);
            }
        }
    }
}

/// Deterministic, allocation-free 64-bit value digest for `Shape::Dyn` orbit
/// comparison and fingerprinting without interning candidates into `dynval`.
#[inline]
fn orbit_dyn_digest(v: &Value) -> u64 {
    use std::hash::BuildHasher;
    tlx_base::hash::fmix64(tlx_base::hash::FxBuildHasher::default().hash_one(v))
}

/// One compiled word-aligned unit of a [`FactorPlan::Product`] (`Record`/`Tuple`).
#[derive(Clone)]
pub enum ProductUnit {
    /// Contiguous invariant words: `dst[offset..offset + len] = src[offset..offset + len]`.
    Copy { offset: usize, len: usize },
    /// One word-aligned field with moved atoms at `offset`, indexing into
    /// `FactorPlan::Product::fields[field_idx]`.
    Word { field_idx: usize, offset: usize },
    /// One packed `u64` word at `word`: invariant bits are preserved via
    /// `src[word] & fixed_mask`, and each `(pos, field_idx)` atom bitfield
    /// indexes its owned `FactorPlan::Atom` in `FactorPlan::Product::fields`.
    Packed { word: usize, fixed_mask: u64, atoms: Box<[(BitPos, usize)]> },
}

/// Factorized per-shape permutation plan compiled once per variable for a
/// [`FactorGroupSpec`], applicable for any permutation `img: &[u16]` without
/// materializing `|G|` explicit [`PermPlan`] vectors.
#[derive(Clone)]
pub enum FactorPlan {
    /// Unaffected by any permutation in `G`: copy `n` words.
    Copy(usize),
    /// An atom word mapped through `AtomTable`.
    Atom(Arc<AtomTable>),
    /// A bitset over a `Shape::Atom` universe.
    BitsetAtom { table: Arc<AtomTable>, words: usize },
    /// A bitset over a compound finite universe (`<= MAX_BITSET_UNIVERSE`).
    BitsetRank { rank: Box<RankPlan>, words: usize },
    /// A sorted-array set of `elem_words`-word elements.
    Sorted { elem: Box<FactorPlan>, elem_words: usize, words: usize },
    /// A sequence of word-aligned elements.
    Seq { elem: Box<FactorPlan>, elem_words: usize, words: usize },
    /// A sequence of packed sub-word atoms.
    SeqBits { bits: u8, table: Arc<AtomTable>, words: usize },
    /// A record or tuple: `fields` in field order for refinement, and merged
    /// word-aligned `units` for fast permutation application.
    Product { fields: Box<[(FieldLoc, FactorPlan)]>, units: Box<[ProductUnit]>, words: usize },
    /// A fixed-domain function `[dom -> range]` with optional trailing words.
    Fcn { dom: DomMap, slot: SlotLayout, range: Box<FactorPlan>, extra: usize, dynamic_witness: bool, words: usize },
    /// A partial map over a bitset key universe.
    Map { key: Box<RankPlan>, dims: MapDims, range: Box<FactorPlan>, dynamic_witness: bool, words: usize },
    /// A union: arm index word, then arm payload padded to `words`.
    Union { arms: Box<[FactorPlan]>, words: usize },
    /// A `Dyn` handle.
    Dyn,
    /// A value store handle.
    Ref(crate::store::StoreRef),
}

impl FactorPlan {
    /// Compile a factorized permutation plan for `shape` under `fg`.
    /// Returns `None` if `shape` is not closed under `fg`.
    pub fn compile(shape: &Shape, fg: &FactorGroupSpec) -> Option<FactorPlan> {
        let n = words(shape);
        Some(match shape {
            Shape::Never | Shape::Bool | Shape::Int { .. } => FactorPlan::Copy(n),
            Shape::Atom(u) => match AtomTable::compile(u, fg)? {
                None => FactorPlan::Copy(n),
                Some(table) => FactorPlan::Atom(table),
            },
            Shape::Set { elem, .. } if bitset_universe(elem).is_some() => {
                let rp = RankPlan::compile(elem, fg)?;
                match rp {
                    RankPlan::Identity => FactorPlan::Copy(n),
                    RankPlan::Atom(table) => FactorPlan::BitsetAtom { table, words: n },
                    other => FactorPlan::BitsetRank { rank: Box::new(other), words: n },
                }
            }
            Shape::Set { elem, .. } => match FactorPlan::compile(elem, fg)? {
                FactorPlan::Copy(_) => FactorPlan::Copy(n),
                p => FactorPlan::Sorted { elem: Box::new(p), elem_words: words(elem), words: n },
            },
            Shape::Seq { elem, .. } => match FactorPlan::compile(elem, fg)? {
                FactorPlan::Copy(_) => FactorPlan::Copy(n),
                p => match SlotLayout::of(elem) {
                    SlotLayout::Words(ew) => FactorPlan::Seq { elem: Box::new(p), elem_words: ew, words: n },
                    SlotLayout::Bits(bits) => {
                        let FactorPlan::Atom(table) = p else {
                            unreachable!("packed non-copy scalar must be Atom");
                        };
                        FactorPlan::SeqBits { bits, table, words: n }
                    }
                },
            },
            Shape::Record(fs) => {
                let parts: Vec<&Shape> = fs.iter().map(|(_, f)| f).collect();
                compile_factor_product(&parts, fg, n)?
            }
            Shape::Tuple(es) => {
                let parts: Vec<&Shape> = es.iter().collect();
                compile_factor_product(&parts, fg, n)?
            }
            Shape::Fcn { dom, range, witness, key_variants } => {
                let extra = witness.extra_words() + key_variants.len();
                let dynamic_witness = *witness == FcnWitness::Dynamic;
                let dm = if key_variants.is_empty() {
                    DomMap::compile(dom, fg)?
                } else {
                    if dom.iter().any(|k| value_has_moved(k, fg))
                        || key_variants.iter().any(|(_, vs)| vs.iter().any(|k| value_has_moved(k, fg)))
                    {
                        return None;
                    }
                    DomMap::Fixed(dom.len())
                };
                let rp = FactorPlan::compile(range, fg)?;
                let slot = SlotLayout::of(range);
                if (dm.is_identity() && rp.is_identity()) || matches!(slot, SlotLayout::Words(0)) {
                    FactorPlan::Copy(n)
                } else {
                    FactorPlan::Fcn { dom: dm, slot, range: Box::new(rp), extra, dynamic_witness, words: n }
                }
            }
            Shape::Map { key, range, witness } => {
                let kp = RankPlan::compile(key, fg)?;
                let rp = FactorPlan::compile(range, fg)?;
                let dims = MapDims::of_parts(key, range);
                let dynamic_witness = *witness == FcnWitness::Dynamic;
                if kp.is_identity() && rp.is_identity() {
                    FactorPlan::Copy(n)
                } else {
                    FactorPlan::Map { key: Box::new(kp), dims, range: Box::new(rp), dynamic_witness, words: n }
                }
            }
            Shape::Union(arms) => {
                let plans: Vec<FactorPlan> = arms.iter().map(|a| FactorPlan::compile(a, fg)).collect::<Option<_>>()?;
                if plans.iter().all(FactorPlan::is_identity) {
                    FactorPlan::Copy(n)
                } else {
                    FactorPlan::Union { arms: plans.into(), words: n }
                }
            }
            Shape::Dyn => FactorPlan::Dyn,
            Shape::Ref(store) => FactorPlan::Ref(store.clone()),
        })
    }

    #[inline]
    pub fn is_identity(&self) -> bool {
        matches!(self, FactorPlan::Copy(_))
    }

    #[inline]
    pub fn words(&self) -> usize {
        match self {
            FactorPlan::Copy(n) => *n,
            FactorPlan::Atom(_) | FactorPlan::Dyn | FactorPlan::Ref(_) => 1,
            FactorPlan::BitsetAtom { words, .. }
            | FactorPlan::BitsetRank { words, .. }
            | FactorPlan::Sorted { words, .. }
            | FactorPlan::Seq { words, .. }
            | FactorPlan::SeqBits { words, .. }
            | FactorPlan::Product { words, .. }
            | FactorPlan::Fcn { words, .. }
            | FactorPlan::Map { words, .. }
            | FactorPlan::Union { words, .. } => *words,
        }
    }

    /// True iff this plan or any descendant contains a multi-word (`>= 2` words)
    /// bitset (for `Set` or `Map`), where little-endian multi-word bitset order
    /// differs from plain slice `.cmp()`.
    pub fn has_wide_bitset(&self) -> bool {
        match self {
            FactorPlan::Copy(_) | FactorPlan::Atom(_) | FactorPlan::SeqBits { .. } | FactorPlan::Dyn | FactorPlan::Ref(_) => false,
            FactorPlan::BitsetAtom { words, .. } | FactorPlan::BitsetRank { words, .. } => *words > 1,
            FactorPlan::Sorted { elem, .. } | FactorPlan::Seq { elem, .. } => elem.has_wide_bitset(),
            FactorPlan::Product { fields, .. } => fields.iter().any(|(_, p)| p.has_wide_bitset()),
            FactorPlan::Fcn { range, .. } => range.has_wide_bitset(),
            FactorPlan::Map { dims, range, .. } => dims.bitset_words > 1 || range.has_wide_bitset(),
            FactorPlan::Union { arms, .. } => arms.iter().any(FactorPlan::has_wide_bitset),
        }
    }

    /// True iff this plan or any descendant contains a `Shape::Dyn` slot.
    pub fn has_dyn(&self) -> bool {
        match self {
            FactorPlan::Dyn => true,
            FactorPlan::Sorted { elem, .. } | FactorPlan::Seq { elem, .. } => elem.has_dyn(),
            FactorPlan::Product { fields, .. } => fields.iter().any(|(_, p)| p.has_dyn()),
            FactorPlan::Fcn { range, .. } | FactorPlan::Map { range, .. } => range.has_dyn(),
            FactorPlan::Union { arms, .. } => arms.iter().any(FactorPlan::has_dyn),
            _ => false,
        }
    }

    /// Apply permutation `img` to `src` into `dst` (safe, validates handles).
    pub fn apply(&self, fg: &FactorGroupSpec, img: &[u16], src: &[u64], dst: &mut [u64]) {
        // SAFETY: `TRUSTED = false` validates any decoded handle.
        unsafe { self.apply_impl::<false, false>(fg, img, src, dst) }
    }

    /// Apply permutation `img` to trusted encoded words `src` into `dst`.
    ///
    /// # Safety
    /// `src` must be a valid encoding of this plan's shape; active Dyn handles
    /// must satisfy `dynval::lookup_unchecked`'s publication contract.
    pub unsafe fn apply_unchecked(&self, fg: &FactorGroupSpec, img: &[u16], src: &[u64], dst: &mut [u64]) {
        // SAFETY: caller upholds valid encoding and handle publication contract.
        unsafe { self.apply_impl::<true, false>(fg, img, src, dst) }
    }

    /// Apply permutation `img` to trusted encoded words `src` into `dst` in
    /// orbit-canonical form: `Ref` slots write semantic digests directly without
    /// mutating the value store, and trailing dynamic witness words are zeroed.
    ///
    /// # Safety
    /// Same contract as [`Self::apply_unchecked`].
    pub unsafe fn apply_orbit_unchecked(&self, fg: &FactorGroupSpec, img: &[u16], src: &[u64], dst: &mut [u64]) {
        // SAFETY: caller upholds valid encoding and handle publication contract.
        unsafe { self.apply_impl::<true, true>(fg, img, src, dst) }
    }

    unsafe fn apply_impl<const TRUSTED: bool, const ORBIT_CANON: bool>(
        &self,
        fg: &FactorGroupSpec,
        img: &[u16],
        src: &[u64],
        dst: &mut [u64],
    ) {
        // SAFETY: recursive child slices follow the validated layout contract.
        unsafe {
            match self {
                FactorPlan::Copy(0) => {}
                FactorPlan::Copy(1) => dst[0] = src[0],
                FactorPlan::Copy(n) => dst[..*n].copy_from_slice(&src[..*n]),
                FactorPlan::Atom(table) => dst[0] = table.map_code(fg, img, src[0]),
                FactorPlan::BitsetAtom { table, words } => {
                    dst[..*words].fill(0);
                    for (i, &w) in src[..*words].iter().enumerate() {
                        let mut b = w;
                        while b != 0 {
                            let r = (i * 64 + b.trailing_zeros() as usize) as u64;
                            b &= b - 1;
                            let t = table.map_code(fg, img, r) as usize;
                            dst[t / 64] |= 1u64 << (t % 64);
                        }
                    }
                }
                FactorPlan::BitsetRank { rank, words } => {
                    dst[..*words].fill(0);
                    for (i, &w) in src[..*words].iter().enumerate() {
                        let mut b = w;
                        while b != 0 {
                            let r = (i * 64 + b.trailing_zeros() as usize) as u64;
                            b &= b - 1;
                            let t = rank.map_rank(fg, img, r) as usize;
                            dst[t / 64] |= 1u64 << (t % 64);
                        }
                    }
                }
                FactorPlan::Sorted { elem, elem_words, words } => {
                    let (n, ew) = (src[0] as usize, *elem_words);
                    dst[0] = src[0];
                    for i in 0..n {
                        let o = 1 + i * ew;
                        elem.apply_impl::<TRUSTED, ORBIT_CANON>(fg, img, &src[o..o + ew], &mut dst[o..o + ew]);
                    }
                    dst[1 + n * ew..*words].fill(0);
                    sort_elems(&mut dst[1..1 + n * ew], ew);
                }
                FactorPlan::Seq { elem, elem_words, words } => {
                    let (n, ew) = (src[0] as usize, *elem_words);
                    dst[0] = src[0];
                    for i in 0..n {
                        let o = 1 + i * ew;
                        elem.apply_impl::<TRUSTED, ORBIT_CANON>(fg, img, &src[o..o + ew], &mut dst[o..o + ew]);
                    }
                    dst[1 + n * ew..*words].fill(0);
                }
                FactorPlan::SeqBits { bits, table, words } => {
                    let n = src[0] as usize;
                    dst[0] = src[0];
                    dst[1..*words].fill(0);
                    for i in 0..n {
                        let raw = SlotLayout::extract(*bits, &src[1..], i);
                        SlotLayout::set_zeroed(*bits, &mut dst[1..], i, table.map_code(fg, img, raw));
                    }
                }
                FactorPlan::Product { fields, units, .. } => {
                    for unit in units.iter() {
                        match unit {
                            ProductUnit::Copy { offset, len: 1 } => dst[*offset] = src[*offset],
                            ProductUnit::Copy { offset, len } => {
                                let o = *offset;
                                dst[o..o + *len].copy_from_slice(&src[o..o + *len]);
                            }
                            ProductUnit::Word { field_idx, offset } => {
                                fields[*field_idx].1.apply_impl::<TRUSTED, ORBIT_CANON>(fg, img, &src[*offset..], &mut dst[*offset..]);
                            }
                            ProductUnit::Packed { word, fixed_mask, atoms } => {
                                let sw = src[*word];
                                let mut w = sw & *fixed_mask;
                                for &(pos, field_idx) in atoms.iter() {
                                    let FactorPlan::Atom(table) = &fields[field_idx].1 else {
                                        unreachable!("packed atom unit must reference Atom field");
                                    };
                                    let raw = (sw >> pos.shift) & pos.mask();
                                    w |= table.map_code(fg, img, raw) << pos.shift;
                                }
                                dst[*word] = w;
                            }
                        }
                    }
                }
                FactorPlan::Fcn { dom, slot, range, extra, dynamic_witness, words } => {
                    let len = dom.len();
                    let payload_words = slot.array_words(len);
                    match *slot {
                        SlotLayout::Words(rw) => {
                            for i in 0..len {
                                let t = dom.map_slot(fg, img, i);
                                range.apply_impl::<TRUSTED, ORBIT_CANON>(
                                    fg,
                                    img,
                                    &src[i * rw..(i + 1) * rw],
                                    &mut dst[t * rw..(t + 1) * rw],
                                );
                            }
                        }
                        SlotLayout::Bits(bits) => {
                            dst[..payload_words].fill(0);
                            for i in 0..len {
                                let t = dom.map_slot(fg, img, i);
                                let raw = SlotLayout::extract(bits, src, i);
                                let mapped = match range.as_ref() {
                                    FactorPlan::Copy(_) => raw,
                                    FactorPlan::Atom(table) => table.map_code(fg, img, raw),
                                    _ => unreachable!("packed scalar plan must be Copy or Atom"),
                                };
                                SlotLayout::set_zeroed(bits, dst, t, mapped);
                            }
                        }
                    }
                    if *extra > 0 {
                        if ORBIT_CANON {
                            dst[payload_words..*words].fill(0);
                        } else {
                            dst[payload_words..*words].copy_from_slice(&src[payload_words..*words]);
                        }
                    }
                    let _ = dynamic_witness;
                }
                FactorPlan::Map { key, dims, range, dynamic_witness, words } => {
                    let bw = dims.bitset_words;
                    dst[..*words].fill(0);
                    match dims.slot {
                        SlotLayout::Words(rw) => {
                            for (i, &w) in src[..bw].iter().enumerate() {
                                let mut b = w;
                                while b != 0 {
                                    let r = i * 64 + b.trailing_zeros() as usize;
                                    b &= b - 1;
                                    let t = key.map_rank(fg, img, r as u64) as usize;
                                    dst[t / 64] |= 1u64 << (t % 64);
                                    range.apply_impl::<TRUSTED, ORBIT_CANON>(
                                        fg,
                                        img,
                                        &src[bw + r * rw..bw + (r + 1) * rw],
                                        &mut dst[bw + t * rw..bw + (t + 1) * rw],
                                    );
                                }
                            }
                        }
                        SlotLayout::Bits(bits) => {
                            for (i, &w) in src[..bw].iter().enumerate() {
                                let mut b = w;
                                while b != 0 {
                                    let r = i * 64 + b.trailing_zeros() as usize;
                                    b &= b - 1;
                                    let t = key.map_rank(fg, img, r as u64) as usize;
                                    dst[t / 64] |= 1u64 << (t % 64);
                                    let raw = SlotLayout::extract(bits, &src[bw..], r);
                                    let mapped = match range.as_ref() {
                                        FactorPlan::Copy(_) => raw,
                                        FactorPlan::Atom(table) => table.map_code(fg, img, raw),
                                        _ => unreachable!("packed scalar plan must be Copy or Atom"),
                                    };
                                    SlotLayout::set_zeroed(bits, &mut dst[bw..], t, mapped);
                                }
                            }
                        }
                    }
                    if *dynamic_witness {
                        dst[*words - 1] = if ORBIT_CANON { 0 } else { src[*words - 1] };
                    }
                }
                FactorPlan::Union { arms, words } => {
                    dst[..*words].fill(0);
                    dst[0] = src[0];
                    arms[src[0] as usize].apply_impl::<TRUSTED, ORBIT_CANON>(fg, img, &src[1..*words], &mut dst[1..*words]);
                }
                FactorPlan::Dyn => {
                    let v = if TRUSTED { dynval::lookup_unchecked(src[0]) } else { dynval::lookup(src[0]) };
                    if ORBIT_CANON {
                        dst[0] = match tlx_value::ops::permute_shared(&v, &|m| fg.map_sym(m, img).cloned()) {
                            Ok(Some(p)) => orbit_dyn_digest(&p),
                            _ => orbit_dyn_digest(&v),
                        };
                    } else {
                        dst[0] = match tlx_value::ops::permute_shared(&v, &|m| fg.map_sym(m, img).cloned()) {
                            Ok(Some(p)) => dynval::intern_exact(&p),
                            _ => src[0],
                        };
                    }
                }
                FactorPlan::Ref(store) => {
                    let v = if TRUSTED { store.thaw(src[0]) } else { store.try_thaw(src[0]).expect("valid value store handle") };
                    match tlx_value::ops::permute_shared(&v, &|m| fg.map_sym(m, img).cloned()) {
                        Ok(Some(p)) => {
                            dst[0] = if ORBIT_CANON {
                                crate::store::digest_of_value(&p).unwrap_or_else(|_| store.digest(src[0]))
                            } else {
                                store.freeze(&p).unwrap_or(src[0])
                            };
                        }
                        _ => {
                            dst[0] = if ORBIT_CANON { store.digest(src[0]) } else { src[0] };
                        }
                    }
                }
            }
        }
    }
}

/// Merge adjacent `Identity` factors in a `RankPlan::Product` so mixed-radix
/// decomposition does the minimum number of divisions per rank.
fn compact_rank_product(cards: Vec<u64>, plans: Vec<RankPlan>) -> RankPlan {
    if plans.iter().all(RankPlan::is_identity) {
        return RankPlan::Identity;
    }
    let mut out_cards: Vec<u64> = Vec::with_capacity(cards.len());
    let mut out_plans: Vec<RankPlan> = Vec::with_capacity(plans.len());
    for (c, p) in cards.into_iter().zip(plans) {
        if c == 1 && p.is_identity() {
            continue;
        }
        if p.is_identity() && out_plans.last().is_some_and(RankPlan::is_identity) {
            if let Some(prod) = out_cards.last().and_then(|prev| prev.checked_mul(c)) {
                *out_cards.last_mut().unwrap() = prod;
                continue;
            }
        }
        out_cards.push(c);
        out_plans.push(p);
    }
    if out_plans.iter().all(RankPlan::is_identity) {
        return RankPlan::Identity;
    }
    RankPlan::Product { cards: out_cards.into(), plans: out_plans.into() }
}

fn compile_factor_product(parts: &[&Shape], fg: &FactorGroupSpec, n: usize) -> Option<FactorPlan> {
    let fl = FieldLayout::of_shapes(parts.iter().copied());
    let plans: Vec<FactorPlan> = parts.iter().map(|p| FactorPlan::compile(p, fg)).collect::<Option<_>>()?;
    if plans.iter().all(FactorPlan::is_identity) {
        return Some(FactorPlan::Copy(n));
    }
    let mut units: Vec<ProductUnit> = Vec::new();
    let push_copy = |units: &mut Vec<ProductUnit>, offset: usize, len: usize| {
        if len == 0 {
            return;
        }
        if let Some(ProductUnit::Copy { offset: o0, len: l0 }) = units.last_mut() {
            if *o0 + *l0 == offset {
                *l0 += len;
                return;
            }
        }
        units.push(ProductUnit::Copy { offset, len });
    };
    for group in fl.word_groups() {
        match group {
            FieldGroup::Word { index, offset, words: w } => {
                if plans[*index].is_identity() {
                    push_copy(&mut units, *offset, *w);
                } else {
                    units.push(ProductUnit::Word { field_idx: *index, offset: *offset });
                }
            }
            FieldGroup::Packed { word, fields } => {
                let mut fixed_mask = 0u64;
                let mut atoms = Vec::new();
                for &(i, pos) in fields.iter() {
                    match &plans[i] {
                        FactorPlan::Copy(_) => fixed_mask |= pos.shifted_mask(),
                        FactorPlan::Atom(_) => atoms.push((pos, i)),
                        _ => unreachable!("packed scalar plan must be Copy or Atom"),
                    }
                }
                if atoms.is_empty() {
                    push_copy(&mut units, *word, 1);
                } else {
                    units.push(ProductUnit::Packed { word: *word, fixed_mask, atoms: atoms.into() });
                }
            }
        }
    }
    let fields: Box<[(FieldLoc, FactorPlan)]> = fl.locs.iter().copied().zip(plans).collect();
    Some(FactorPlan::Product { fields, units: units.into(), words: n })
}

fn value_has_moved(v: &Value, fg: &FactorGroupSpec) -> bool {
    match v {
        Value::ModelValue(m) => fg.lookup(*m).is_some(),
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => false,
        Value::Set(es) | Value::Tuple(es) => es.iter().any(|e| value_has_moved(e, fg)),
        Value::Record(fs) => fs.iter().any(|(_, e)| value_has_moved(e, fg)),
        Value::Fcn(ps, _) => ps.iter().any(|(k, e)| value_has_moved(k, fg) || value_has_moved(e, fg)),
        Value::LazySet(_) | Value::LazyFcn(_) => true,
    }
}

fn for_each_moved_in_value(v: &Value, fg: &FactorGroupSpec, f: &mut impl FnMut(usize, usize)) {
    match v {
        Value::ModelValue(m) => {
            if let Some((g, k)) = fg.lookup(*m) {
                f(g, k);
            }
        }
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => {}
        Value::Set(es) | Value::Tuple(es) => {
            for e in es.iter() {
                for_each_moved_in_value(e, fg, f);
            }
        }
        Value::Record(fs) => {
            for (_, e) in fs.iter() {
                for_each_moved_in_value(e, fg, f);
            }
        }
        Value::Fcn(ps, _) => {
            for (k, e) in ps.iter() {
                for_each_moved_in_value(k, fg, f);
                for_each_moved_in_value(e, fg, f);
            }
        }
        Value::LazySet(_) | Value::LazyFcn(_) => {
            for (g, factor) in fg.factors.iter().enumerate() {
                for k in 0..factor.keys.len() {
                    f(g, k);
                }
            }
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
        let m = Shape::Map { key: Box::new(a.clone()), range: Box::new(a.clone()), witness: crate::FcnWitness::Enumerated };
        check_all(&m, &swap("a", "c"));
        let m2 =
            Shape::Map { key: Box::new(Shape::Int { lo: 0, hi: 2 }), range: Box::new(a.clone()), witness: crate::FcnWitness::Enumerated };
        check_all(&m2, &swap("a", "b"));
        // Dynamic-witness map preserves its trailing witness word under permutation.
        let md = Shape::Map { key: Box::new(a.clone()), range: Box::new(a.clone()), witness: crate::FcnWitness::Dynamic };
        let perm = swap("a", "c");
        let plan = PermPlan::compile(&md, &perm).unwrap();
        let v = Value::fcn_rcd_from_pairs(vec![(mv("a"), mv("b"))]).unwrap();
        let mut src = vec![0u64; words(&md)];
        encode(&md, &v, &mut src).unwrap();
        let mut dst = vec![u64::MAX; words(&md)];
        plan.apply(&src, &mut dst);
        let want = Value::fcn_rcd_from_pairs(vec![(mv("c"), mv("b"))]).unwrap();
        assert_eq!(decode(&md, &dst), want);
        assert!(matches!(decode(&md, &dst), Value::Fcn(_, tlx_value::FcnDom::Enumerated)));
        assert_eq!(dst[words(&md) - 1], 1);
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
        let f = Shape::Fcn { dom: dom.into(), range: Box::new(r), witness: crate::FcnWitness::Enumerated, key_variants: Arc::from([]) };
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

    fn sorted_syms(xs: &[&str]) -> Vec<Sym> {
        let mut s: Vec<Sym> = xs.iter().map(|x| Sym::new(x)).collect();
        s.sort_unstable();
        s
    }

    fn check_factor_all(shape: &Shape, fg: &FactorGroupSpec, img: &[u16]) {
        let plan = FactorPlan::compile(shape, fg).expect("factor plan");
        let n = words(shape);
        let card = shape.cardinality().expect("finite shape");
        for r in 0..card {
            let v = unrank(shape, r);
            let mut src = vec![0u64; n];
            encode(shape, &v, &mut src).unwrap();
            let mut dst = vec![u64::MAX; n];
            plan.apply(fg, img, &src, &mut dst);
            let want = tlx_value::ops::permute(&v, &|m| fg.map_sym(m, img).cloned()).unwrap();
            let mut enc_want = vec![0u64; n];
            encode(shape, &want, &mut enc_want).unwrap();
            assert_eq!(dst, enc_want, "factor permuting {v} (got {})", decode(shape, &dst));
        }
    }

    #[test]
    fn factor_plans_cover_compound_shapes_and_rank_maps() {
        let k1 = sorted_syms(&["p1", "p2", "p3"]);
        let k2 = sorted_syms(&["q1", "q2"]);
        let fg = FactorGroupSpec::new(&[&k1, &k2]);
        // Cycle (0 1 2) on k1 and swap (0 1) on k2.
        let img = [1u16, 2, 0, 1, 0];

        let a1 = atoms(&["p1", "p2", "p3"]);
        let a2 = atoms(&["q1", "q2"]);
        let mixed = atoms(&["p1", "p2", "p3", "q1", "q2", "fixed"]);
        check_factor_all(&a1, &fg, &img);
        check_factor_all(&mixed, &fg, &img);
        check_factor_all(&Shape::Set { elem: Box::new(a1.clone()), max_card: 3 }, &fg, &img);
        check_factor_all(&Shape::Set { elem: Box::new(mixed.clone()), max_card: 3 }, &fg, &img);
        let pair = Shape::Tuple(vec![a1.clone(), Shape::Bool].into());
        check_factor_all(&Shape::Set { elem: Box::new(pair.clone()), max_card: 2 }, &fg, &img);
        check_factor_all(&Shape::Seq { elem: Box::new(a1.clone()), max_len: 2 }, &fg, &img);
        let mut rec_fields = vec![(Sym::new("a"), a1.clone()), (Sym::new("b"), a2.clone())];
        rec_fields.sort_by_key(|f| f.0);
        let rec = Shape::Record(rec_fields.into());
        check_factor_all(&rec, &fg, &img);
        let mut dom: Vec<Value> = k1.iter().copied().map(Value::ModelValue).collect();
        dom.sort();
        let fcn = Shape::Fcn { dom: dom.into(), range: Box::new(a2.clone()), witness: FcnWitness::Enumerated, key_variants: Arc::from([]) };
        check_factor_all(&fcn, &fg, &img);
        let map_atom = Shape::Map { key: Box::new(a1.clone()), range: Box::new(a2.clone()), witness: FcnWitness::Enumerated };
        check_factor_all(&map_atom, &fg, &img);
        let map_pair = Shape::Map { key: Box::new(pair), range: Box::new(Shape::Int { lo: 0, hi: 1 }), witness: FcnWitness::Enumerated };
        check_factor_all(&map_pair, &fg, &img);
        let u = Shape::Union(vec![a1.clone(), Shape::Record(vec![(Sym::new("n"), a2.clone())].into())].into());
        check_factor_all(&u, &fg, &img);
        // Set with Comb rank (max_card < universe) inside a bitset.
        let sub_set = Shape::Set { elem: Box::new(a1.clone()), max_card: 2 };
        let rp = RankPlan::compile(&sub_set, &fg).unwrap();
        for r in 0..sub_set.cardinality().unwrap() {
            let v = unrank(&sub_set, r);
            let want = tlx_value::ops::permute(&v, &|m| fg.map_sym(m, &img).cloned()).unwrap();
            assert_eq!(rp.map_rank(&fg, &img, r), rank(&sub_set, &want).unwrap());
        }
        // Not closed under fg: partial factor rejected.
        let partial = atoms(&["p1", "p2"]);
        assert!(FactorPlan::compile(&partial, &fg).is_none());
    }

    #[test]
    fn deep_nested_product_plan_is_linear_in_depth() {
        fn count_nodes(plan: &FactorPlan) -> usize {
            match plan {
                FactorPlan::Product { fields, .. } => 1 + fields.iter().map(|(_, p)| count_nodes(p)).sum::<usize>(),
                _ => 1,
            }
        }
        let k = sorted_syms(&["a1", "a2"]);
        let fg = FactorGroupSpec::new(&[&k]);
        let mut s = atoms(&["a1", "a2"]);
        // Depth 24 would take ~2^24 (~16M) nodes if units cloned child plans.
        for _ in 0..24 {
            s = Shape::Tuple(vec![s].into());
        }
        let plan = FactorPlan::compile(&s, &fg).expect("nested tuple plan");
        assert_eq!(count_nodes(&plan), 25, "nested product plan must be O(depth) with no cloned subtrees");
        // Verify execution under swap (a1 <-> a2).
        let layout = crate::Layout::new(vec![s]);
        let mut v = Value::ModelValue(k[0]);
        let mut want = Value::ModelValue(k[1]);
        for _ in 0..24 {
            v = Value::tuple(vec![v]);
            want = Value::tuple(vec![want]);
        }
        let mut src = vec![0u64; layout.words];
        let mut dst = vec![0u64; layout.words];
        layout.encode_state(&[v], &mut src).unwrap();
        plan.apply(&fg, &[1, 0], &src, &mut dst);
        assert_eq!(layout.decode_state(&dst)[0], want);
    }

    #[test]
    fn apply_orbit_dyn_does_not_intern_candidates() {
        fn has_probe_sym(v: &Value, syms: &[Sym]) -> bool {
            match v {
                Value::ModelValue(m) => syms.contains(m),
                Value::Set(es) | Value::Tuple(es) => es.iter().any(|e| has_probe_sym(e, syms)),
                Value::Record(fs) => fs.iter().any(|(_, e)| has_probe_sym(e, syms)),
                Value::Fcn(ps, _) => ps.iter().any(|(k, e)| has_probe_sym(k, syms) || has_probe_sym(e, syms)),
                _ => false,
            }
        }
        let keys: Vec<Sym> = (1..=8).map(|i| Sym::new(&format!("dyn_probe_layout_{i}"))).collect();
        let mut sorted = keys.clone();
        sorted.sort_unstable();
        let fg = FactorGroupSpec::new(&[&sorted]);
        let plan = FactorPlan::compile(&Shape::Dyn, &fg).expect("Dyn plan");
        assert!(plan.has_dyn());
        let tup = Value::tuple(sorted.iter().copied().map(Value::ModelValue).collect());
        let h = dynval::intern(&tup);
        let probe_count = || -> usize { dynval::snapshot().iter().flat_map(|s| s.iter()).filter(|v| has_probe_sym(v, &sorted)).count() };
        assert_eq!(probe_count(), 1, "only the pre-interned base tuple should exist in dynval");
        let mut dst = [0u64; 1];
        let mut img = fg.identity_img();
        for k in 0..sorted.len() - 1 {
            img.swap(k, k + 1);
            // SAFETY: `h` came from `dynval::intern` on this thread.
            unsafe { plan.apply_orbit_unchecked(&fg, &img, &[h], &mut dst) };
            img.swap(k, k + 1);
        }
        assert_eq!(probe_count(), 1, "apply_orbit_unchecked on Dyn must not intern losing candidates");
    }
}
