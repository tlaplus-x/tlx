//! Precomputed layout trees: a `Shape` compiled once into a `LayoutNode`
//! that caches, at every node, what the `Shape`-based functions of `layout`
//! recompute on each call (word sizes and offsets, cardinalities, bitset
//! universes, ranking tables, union arm offsets).
//!
//! `LayoutNode::encode` / `decode` / `rank` / `unrank` produce exactly the
//! same results as `layout::encode` / `decode` / `rank` / `unrank` on the
//! node's shape (see the module docs of `layout` for the representation);
//! they are used on the host's hot paths (interpreter fallbacks, VIEW,
//! paranoid checks, trace printing, re-encoding).

use std::sync::{Arc, OnceLock};

use crate::dynval;
use crate::layout::{same_domain, sorted_set, FieldLayout, FieldLoc, MapDims, Miss, SlotLayout};
use crate::shape::{binom, fit_repr, force, set_elems, set_len, Shape, MAX_BITSET_UNIVERSE};
use tlx_value::{Sym, Value};

/// A shape with its layout facts precomputed.
#[derive(Clone, Debug)]
pub struct LayoutNode {
    /// Number of words of the encoding (`layout::words`).
    words: usize,
    /// `Shape::cardinality`.
    card: Option<u64>,
    kind: Kind,
    /// All values of a compound shape with a bitset universe, by rank
    /// (built on first use by `universe_value`).
    values: OnceLock<Box<[Value]>>,
}

/// Nodes are equal iff their shapes are (everything else is derived).
impl PartialEq for LayoutNode {
    fn eq(&self, other: &LayoutNode) -> bool {
        self.kind == other.kind
    }
}

impl Eq for LayoutNode {}

#[derive(Clone, Debug, PartialEq, Eq)]
enum Kind {
    Never,
    Bool,
    Int {
        lo: i64,
        hi: i64,
    },
    Atom(Arc<[Value]>),
    Set {
        elem: Box<LayoutNode>,
        max_card: usize,
        /// Element universe size if encoded as a bitset.
        bitset: Option<u64>,
        rank: SetRank,
    },
    Fcn {
        dom: Arc<[Value]>,
        range: Box<LayoutNode>,
        slot: SlotLayout,
    },
    Map {
        key: Box<LayoutNode>,
        range: Box<LayoutNode>,
        /// Key universe size.
        universe: u64,
        dims: MapDims,
    },
    /// Fields with the storage location of each, plus bitmasks for packed words.
    Record {
        fields: Box<[(Sym, LayoutNode, FieldLoc)]>,
        bit_words: Box<[(usize, u64)]>,
    },
    /// Positions with the storage location of each, plus bitmasks for packed words.
    Tuple {
        elems: Box<[(LayoutNode, FieldLoc)]>,
        bit_words: Box<[(usize, u64)]>,
    },
    Seq {
        elem: Box<LayoutNode>,
        max_len: usize,
        slot: SlotLayout,
        /// `shorter[l]` = number of sequences shorter than `l` (for
        /// `l <= max_len`; only if the shape has a finite cardinality).
        shorter: Option<Box<[u64]>>,
    },
    Union {
        arms: Box<[LayoutNode]>,
        /// `base[i]` = sum of the cardinalities of the arms before `i` (only
        /// if the shape has a finite cardinality).
        base: Option<Box<[u64]>>,
    },
    Dyn,
    Ref(crate::store::StoreRef),
}

/// How sets are ranked (see `layout::rank`).
#[derive(Clone, Debug, PartialEq, Eq)]
enum SetRank {
    /// The shape has no finite cardinality.
    None,
    /// Every subset is admitted: the bitmask of the element ranks.
    Mask,
    /// By size, then by the combinatorial number system:
    /// `by_size[k]` = number of subsets with fewer than `k` elements.
    Comb { n: u64, by_size: Box<[u64]> },
}

impl LayoutNode {
    pub fn new(s: &Shape) -> LayoutNode {
        let card = s.cardinality();
        let (words, kind) = match s {
            Shape::Never => (0, Kind::Never),
            Shape::Bool => (1, Kind::Bool),
            Shape::Int { lo, hi } => (1, Kind::Int { lo: *lo, hi: *hi }),
            Shape::Atom(u) => (1, Kind::Atom(u.clone())),
            Shape::Dyn => (1, Kind::Dyn),
            Shape::Ref(store) => (1, Kind::Ref(store.clone())),
            Shape::Set { elem, max_card } => {
                let elem = Box::new(LayoutNode::new(elem));
                let bitset = elem.card.filter(|&n| n <= MAX_BITSET_UNIVERSE);
                let words = match bitset {
                    Some(n) => n.div_ceil(64) as usize,
                    None => 1 + max_card * elem.words,
                };
                let rank = match (card, elem.card) {
                    (Some(_), Some(n)) if *max_card as u64 >= n => SetRank::Mask,
                    (Some(_), Some(n)) => SetRank::Comb {
                        n,
                        by_size: (0..=*max_card as u64)
                            .scan(0u64, |acc, k| {
                                let r = *acc;
                                *acc = acc.wrapping_add(binom(n, k).unwrap_or(0));
                                Some(r)
                            })
                            .collect(),
                    },
                    _ => SetRank::None,
                };
                (words, Kind::Set { elem, max_card: *max_card, bitset, rank })
            }
            Shape::Fcn { dom, range: range_shape } => {
                let slot = SlotLayout::of(range_shape);
                let range = Box::new(LayoutNode::new(range_shape));
                (slot.array_words(dom.len()), Kind::Fcn { dom: dom.clone(), range, slot })
            }
            Shape::Map { key, range: range_shape } => {
                let slot = SlotLayout::of(range_shape);
                let key = Box::new(LayoutNode::new(key));
                let range = Box::new(LayoutNode::new(range_shape));
                let universe = key.bitset_universe().expect("map key universe");
                let dims = MapDims::new(universe as usize, slot);
                (dims.words(), Kind::Map { key, range, universe, dims })
            }
            Shape::Record(fs) => {
                let fl = FieldLayout::of_shapes(fs.iter().map(|(_, f)| f));
                let fields: Box<[_]> = fs.iter().zip(fl.locs.iter()).map(|((k, f), &loc)| (*k, LayoutNode::new(f), loc)).collect();
                (fl.words, Kind::Record { fields, bit_words: fl.bit_words })
            }
            Shape::Tuple(es) => {
                let fl = FieldLayout::of_shapes(es.iter());
                let elems: Box<[_]> = es.iter().zip(fl.locs.iter()).map(|(e, &loc)| (LayoutNode::new(e), loc)).collect();
                (fl.words, Kind::Tuple { elems, bit_words: fl.bit_words })
            }
            Shape::Seq { elem: elem_shape, max_len } => {
                let slot = SlotLayout::of(elem_shape);
                let elem = Box::new(LayoutNode::new(elem_shape));
                let shorter = card.map(|_| {
                    let c = elem.card.unwrap();
                    let mut acc = 0u64;
                    (0..=*max_len)
                        .map(|l| {
                            let r = acc;
                            if l < *max_len {
                                acc = acc.wrapping_add(c.wrapping_pow(l as u32));
                            }
                            r
                        })
                        .collect()
                });
                (1usize.saturating_add(slot.array_words(*max_len)), Kind::Seq { elem, max_len: *max_len, slot, shorter })
            }
            Shape::Union(arms) => {
                let arms: Box<[LayoutNode]> = arms.iter().map(LayoutNode::new).collect();
                let words = 1 + arms.iter().map(|a| a.words).max().unwrap_or(0);
                let base = card.map(|_| {
                    let mut acc = 0u64;
                    arms.iter()
                        .map(|a| {
                            let r = acc;
                            acc += a.card.unwrap();
                            r
                        })
                        .collect()
                });
                (words, Kind::Union { arms, base })
            }
        };
        LayoutNode { words, card, kind, values: OnceLock::new() }
    }

    /// Number of words used by values of this shape (`layout::words`).
    #[inline]
    pub fn words(&self) -> usize {
        self.words
    }

    /// Number of values of this shape (`Shape::cardinality`).
    #[inline]
    pub fn cardinality(&self) -> Option<u64> {
        self.card
    }

    /// Size of the element universe if sets of this node's shape (as
    /// elements) are encoded as bitsets (`layout::bitset_universe`).
    #[inline]
    pub fn bitset_universe(&self) -> Option<u64> {
        self.card.filter(|&n| n <= MAX_BITSET_UNIVERSE)
    }

    /// The value of rank `r` of a shape with a bitset universe (bitset
    /// elements, map keys): scalars directly, compound values from a table
    /// of the whole universe.
    #[inline]
    fn universe_value(&self, r: u64) -> Value {
        match &self.kind {
            Kind::Bool | Kind::Int { .. } | Kind::Atom(_) => self.unrank_finite(r),
            _ => self.values.get_or_init(|| (0..self.card.unwrap()).map(|i| self.unrank_finite(i)).collect())[r as usize].clone(),
        }
    }

    /// The element node of a set shape.
    pub fn set_elem(&self) -> Option<&LayoutNode> {
        match &self.kind {
            Kind::Set { elem, .. } => Some(elem),
            _ => None,
        }
    }

    /// Encode `v` into `out[..self.words()]` (later words of `out` are
    /// untouched), as `layout::encode`.
    pub fn encode(&self, v: &Value, out: &mut [u64]) -> Result<(), Miss> {
        out[..self.words].fill(0);
        self.enc(v, out)
    }

    /// `encode` into an already zeroed `out`.
    pub(crate) fn enc(&self, v: &Value, out: &mut [u64]) -> Result<(), Miss> {
        if let Kind::Dyn = self.kind {
            out[0] = dynval::intern(v);
            return Ok(());
        }
        if let Kind::Ref(store) = &self.kind {
            out[0] = store.freeze(v).map_err(|_| Miss::new(v))?;
            return Ok(());
        }
        let Some(v) = force(v) else { return Err(Miss::new(v)) };
        let v = self.fit(v);
        let v = &*v;
        match (&self.kind, v) {
            (Kind::Bool, Value::Bool(b)) => out[0] = *b as u64,
            (Kind::Int { lo, hi }, Value::Int(n)) if lo <= n && n <= hi => out[0] = n.wrapping_sub(*lo) as u64,
            (Kind::Atom(u), Value::Str(_) | Value::ModelValue(_)) => match u.binary_search(v) {
                Ok(i) => out[0] = i as u64,
                Err(_) => return Err(Miss::new(v)),
            },
            (Kind::Set { elem, max_card, bitset, .. }, Value::Set(_) | Value::Interval(..)) => {
                if set_len(v).unwrap() > *max_card as u64 {
                    return Err(Miss::new(v));
                }
                let es = set_elems(v).unwrap();
                if bitset.is_some() {
                    for e in es.iter() {
                        let r = elem.rank_finite(e).map_err(|m| m.under("{}"))?;
                        out[(r / 64) as usize] |= 1u64 << (r % 64);
                    }
                } else {
                    let ew = elem.words;
                    out[0] = es.len() as u64;
                    if ew == 0 {
                        // Only possible for the empty set (elements of shape Never).
                        if let Some(e) = es.first() {
                            return Err(Miss::new(e).under("{}"));
                        }
                        return Ok(());
                    }
                    let mut buf = vec![0u64; es.len() * ew];
                    for (i, e) in es.iter().enumerate() {
                        elem.enc(e, &mut buf[i * ew..]).map_err(|m| m.under("{}"))?;
                    }
                    let mut chunks: Vec<&[u64]> = buf.chunks(ew).collect();
                    chunks.sort_unstable();
                    for (i, c) in chunks.iter().enumerate() {
                        out[1 + i * ew..1 + (i + 1) * ew].copy_from_slice(c);
                    }
                }
            }
            (Kind::Fcn { dom, range, slot }, Value::Fcn(ps, _)) => {
                if !same_domain(ps, dom) {
                    return Err(Miss::new(v));
                }
                for (i, (k, x)) in ps.iter().enumerate() {
                    range.enc_loc(x, out, slot.loc(0, i)).map_err(|m| m.under(format_args!("[{k}]")))?;
                }
            }
            (Kind::Map { key, range, dims, .. }, Value::Fcn(..) | Value::Tuple(_) | Value::Record(_)) => {
                for_each_pair(v, |k, x| {
                    let r = key.rank_finite(k).map_err(|m| m.under("DOMAIN"))?;
                    out[(r / 64) as usize] |= 1u64 << (r % 64);
                    range.enc_loc(x, out, dims.slot_loc(r as usize)).map_err(|m| m.under(format_args!("[{k}]")))
                })?;
            }
            (Kind::Record { fields: fs, .. }, Value::Record(vs)) => {
                if fs.len() != vs.len() || !fs.iter().zip(vs.iter()).all(|(f, x)| f.0 == x.0) {
                    return Err(Miss::new(v));
                }
                for (f, x) in fs.iter().zip(vs.iter()) {
                    f.1.enc_loc(&x.1, out, f.2).map_err(|m| m.under(format_args!(".{}", f.0.as_str())))?;
                }
            }
            (Kind::Tuple { elems: ss, .. }, Value::Tuple(vs)) => {
                if ss.len() != vs.len() {
                    return Err(Miss::new(v));
                }
                for (i, (s, x)) in ss.iter().zip(vs.iter()).enumerate() {
                    s.0.enc_loc(x, out, s.1).map_err(|m| m.under(format_args!("[{}]", i + 1)))?;
                }
            }
            (Kind::Seq { elem, max_len, slot, .. }, Value::Tuple(vs)) => {
                if vs.len() > *max_len {
                    return Err(Miss::new(v));
                }
                out[0] = vs.len() as u64;
                for (i, x) in vs.iter().enumerate() {
                    elem.enc_loc(x, out, slot.loc(1, i)).map_err(|m| m.under(format_args!("[{}]", i + 1)))?;
                }
            }
            (Kind::Union { arms, .. }, _) => match arm_for(arms, v) {
                Some(i) => {
                    out[0] = i as u64;
                    arms[i].enc(v, &mut out[1..])?;
                }
                None => return Err(Miss::new(v)),
            },
            _ => return Err(Miss::new(v)),
        }
        Ok(())
    }

    #[inline]
    fn enc_loc(&self, v: &Value, out: &mut [u64], loc: FieldLoc) -> Result<(), Miss> {
        match loc {
            FieldLoc::Words(w) => self.enc(v, &mut out[w..]),
            FieldLoc::Bits(pos) => {
                let mut tmp = [0u64];
                self.enc(v, &mut tmp)?;
                pos.set_zeroed(out, tmp[0]);
                Ok(())
            }
        }
    }

    #[inline]
    fn validate_scalar_raw(&self, raw: u64) -> Result<(), String> {
        match &self.kind {
            Kind::Never => Err("no value has shape Never".into()),
            Kind::Bool if raw <= 1 => Ok(()),
            Kind::Bool => Err("invalid Bool encoding".into()),
            Kind::Int { lo, hi } if lo <= hi && (raw as u128) <= (*hi as i128 - *lo as i128) as u128 => Ok(()),
            Kind::Int { .. } => Err("Int encoding out of range".into()),
            Kind::Atom(u) if raw < u.len() as u64 => Ok(()),
            Kind::Atom(_) => Err("Atom encoding out of range".into()),
            _ => Err("non-scalar in packed bitfield".into()),
        }
    }

    /// Decode raw words, validating every active Dyn handle first.
    /// Panics for an invalid encoding; no invalid symbol can be constructed.
    pub fn decode(&self, words: &[u64]) -> Value {
        self.validate_words(words).unwrap_or_else(|e| panic!("{e}"));
        // SAFETY: validation checks all active Dyn payloads and synchronizes
        // with their writers; other reads use checked Rust indexing.
        unsafe { self.decode_unchecked(words) }
    }

    /// Validate the word layout, scalar ranges, bitfield padding and every
    /// active dynamic handle. Word-aligned inactive sequence/map slots are not
    /// values and need not contain valid handles, whereas unused bits in
    /// sub-word packed words must be zero.
    pub fn validate_words(&self, words: &[u64]) -> Result<(), String> {
        self.validate_words_impl::<false>(words)
    }

    /// Strict canonical validation for untrusted external/checkpoint states:
    /// runs all checks of [`Self::validate_words`] and additionally requires
    /// zero words in all inactive word-aligned sequence/set/union tails and
    /// absent map slots.
    pub fn validate_canonical_words(&self, words: &[u64]) -> Result<(), String> {
        self.validate_words_impl::<true>(words)
    }

    fn validate_words_impl<const STRICT: bool>(&self, words: &[u64]) -> Result<(), String> {
        let words = words.get(..self.words).ok_or("short encoded value")?;
        match &self.kind {
            Kind::Never => return Err("no value has shape Never".into()),
            Kind::Bool | Kind::Int { .. } | Kind::Atom(_) => self.validate_scalar_raw(words[0])?,
            Kind::Dyn => {
                dynval::try_lookup(words[0]).ok_or("invalid Dyn handle")?;
            }
            Kind::Ref(store) => {
                if !store.is_valid(words[0]) {
                    return Err("invalid value store handle".into());
                }
            }
            Kind::Set { max_card, bitset: Some(n), .. } => {
                let rem = (*n % 64) as u32;
                if rem != 0 && (words[self.words - 1] >> rem) != 0 {
                    return Err("non-zero padding bits in bitset".into());
                }
                let ones: usize = words.iter().map(|w| w.count_ones() as usize).sum();
                if ones > *max_card {
                    return Err("set cardinality exceeds max_card".into());
                }
            }
            Kind::Set { elem, max_card, bitset: None, .. } => {
                let n = usize::try_from(words[0]).map_err(|_| "invalid set length")?;
                if n > *max_card {
                    return Err("invalid set length".into());
                }
                for i in 0..n {
                    elem.validate_words_impl::<STRICT>(&words[1 + i * elem.words..])?;
                }
                if STRICT && words[1 + n * elem.words..].iter().any(|&w| w != 0) {
                    return Err("non-zero inactive set tail words".into());
                }
            }
            Kind::Seq { elem, max_len, slot, .. } => {
                let n = usize::try_from(words[0]).map_err(|_| "invalid sequence length")?;
                if n > *max_len {
                    return Err("invalid sequence length".into());
                }
                match *slot {
                    SlotLayout::Words(ew) => {
                        for i in 0..n {
                            elem.validate_words_impl::<STRICT>(&words[1 + i * ew..])?;
                        }
                        if STRICT && words[1 + n * ew..].iter().any(|&w| w != 0) {
                            return Err("non-zero inactive sequence tail words".into());
                        }
                    }
                    SlotLayout::Bits(b) => {
                        let data = &words[1..];
                        for (w, &word) in data.iter().enumerate() {
                            if (word & !SlotLayout::word_active_mask(b, n, w)) != 0 {
                                return Err("non-zero padding bits in packed sequence".into());
                            }
                        }
                        for i in 0..n {
                            elem.validate_scalar_raw(SlotLayout::extract(b, data, i))?;
                        }
                    }
                }
            }
            Kind::Fcn { dom, range, slot } => match *slot {
                SlotLayout::Words(rw) => {
                    for i in 0..dom.len() {
                        range.validate_words_impl::<STRICT>(&words[i * rw..])?;
                    }
                }
                SlotLayout::Bits(b) => {
                    for (w, &word) in words.iter().enumerate() {
                        if (word & !SlotLayout::word_active_mask(b, dom.len(), w)) != 0 {
                            return Err("non-zero padding bits in packed function".into());
                        }
                    }
                    for i in 0..dom.len() {
                        range.validate_scalar_raw(SlotLayout::extract(b, words, i))?;
                    }
                }
            },
            Kind::Map { range, universe, dims, .. } => {
                let rem = (*universe % 64) as u32;
                if rem != 0 && dims.bitset_words > 0 && (words[dims.bitset_words - 1] >> rem) != 0 {
                    return Err("non-zero padding bits in map domain".into());
                }
                match dims.slot {
                    SlotLayout::Words(rw) => {
                        for r in 0..*universe as usize {
                            let start = dims.bitset_words + r * rw;
                            if words[r / 64] >> (r % 64) & 1 != 0 {
                                range.validate_words_impl::<STRICT>(&words[start..])?;
                            } else if STRICT && words[start..start + rw].iter().any(|&w| w != 0) {
                                return Err("non-zero absent map slot words".into());
                            }
                        }
                    }
                    SlotLayout::Bits(b) => {
                        let data = &words[dims.bitset_words..];
                        let mut active_masks = vec![0u64; data.len()];
                        for r in 0..*universe as usize {
                            if words[r / 64] >> (r % 64) & 1 != 0 {
                                let (w, shift) = SlotLayout::bit_pos(b, r);
                                active_masks[w] |= crate::layout::bit_mask(b) << shift;
                                range.validate_scalar_raw(SlotLayout::extract(b, data, r))?;
                            }
                        }
                        for (&word, &mask) in data.iter().zip(active_masks.iter()) {
                            if (word & !mask) != 0 {
                                return Err("non-zero padding or absent-slot bits in packed map".into());
                            }
                        }
                    }
                }
            }
            Kind::Record { fields, bit_words } => {
                for &(w, mask) in bit_words.iter() {
                    if (words[w] & !mask) != 0 {
                        return Err("non-zero padding bits in packed record".into());
                    }
                }
                for (_, n, loc) in fields.iter() {
                    match *loc {
                        FieldLoc::Words(o) => n.validate_words_impl::<STRICT>(&words[o..])?,
                        FieldLoc::Bits(pos) => n.validate_scalar_raw(pos.extract(words))?,
                    }
                }
            }
            Kind::Tuple { elems, bit_words } => {
                for &(w, mask) in bit_words.iter() {
                    if (words[w] & !mask) != 0 {
                        return Err("non-zero padding bits in packed tuple".into());
                    }
                }
                for (n, loc) in elems.iter() {
                    match *loc {
                        FieldLoc::Words(o) => n.validate_words_impl::<STRICT>(&words[o..])?,
                        FieldLoc::Bits(pos) => n.validate_scalar_raw(pos.extract(words))?,
                    }
                }
            }
            Kind::Union { arms, .. } => {
                let i = usize::try_from(words[0]).map_err(|_| "invalid union tag")?;
                let arm = arms.get(i).ok_or("invalid union tag")?;
                arm.validate_words_impl::<STRICT>(&words[1..1 + arm.words])?;
                if STRICT && words[1 + arm.words..].iter().any(|&w| w != 0) {
                    return Err("non-zero union padding words".into());
                }
            }
        }
        Ok(())
    }

    #[inline]
    unsafe fn decode_loc_unchecked(&self, words: &[u64], loc: FieldLoc) -> Value {
        // SAFETY: `loc` selects an active child within `words`, upholding `decode_unchecked`'s contract.
        unsafe {
            match loc {
                FieldLoc::Words(o) => self.decode_unchecked(&words[o..]),
                FieldLoc::Bits(pos) => {
                    let tmp = [pos.extract(words)];
                    self.decode_unchecked(&tmp)
                }
            }
        }
    }

    /// Decode the value encoded in `words` (as `layout::decode`).
    ///
    /// # Safety
    /// The words must encode a value of this node's shape. Every Dyn handle
    /// must satisfy `dynval::lookup_unchecked`'s publication contract.
    pub unsafe fn decode_unchecked(&self, words: &[u64]) -> Value {
        // SAFETY: child slices use this node's offsets and the caller
        // guarantees all active payloads, including Dyn handles, are valid.
        unsafe {
            match &self.kind {
                Kind::Never => panic!("decode: no value has shape Never"),
                Kind::Bool => Value::Bool(words[0] != 0),
                Kind::Int { lo, .. } => Value::Int(lo.wrapping_add(words[0] as i64)),
                Kind::Atom(u) => u[words[0] as usize].clone(),
                Kind::Set { elem, bitset, .. } => {
                    let mut es: Vec<Value> = Vec::new();
                    if let Some(n) = bitset {
                        for (wi, &w) in words[..n.div_ceil(64) as usize].iter().enumerate() {
                            let mut bits = w;
                            while bits != 0 {
                                let b = bits.trailing_zeros() as u64;
                                bits &= bits - 1;
                                es.push(elem.universe_value(wi as u64 * 64 + b));
                            }
                        }
                    } else {
                        let ew = elem.words;
                        let len = words[0] as usize;
                        es.extend((0..len).map(|i| elem.decode_unchecked(&words[1 + i * ew..])));
                    }
                    sorted_set(es)
                }
                Kind::Fcn { dom, range, slot } => Value::fcn_decoded(
                    dom.iter().enumerate().map(|(i, d)| (d.clone(), range.decode_loc_unchecked(words, slot.loc(0, i)))).collect(),
                ),
                Kind::Map { key, range, universe, dims } => {
                    let bw = dims.bitset_words;
                    let mut pairs = Vec::new();
                    for (wi, &word) in words[..bw].iter().enumerate() {
                        let mut m = word;
                        while m != 0 {
                            let r = wi as u64 * 64 + m.trailing_zeros() as u64;
                            m &= m - 1;
                            if r < *universe {
                                pairs.push((key.universe_value(r), range.decode_loc_unchecked(words, dims.slot_loc(r as usize))));
                            }
                        }
                    }
                    // Keys come in TLC order; the constructor picks the canonical
                    // representation (`<<>>`, a tuple for `1..n`, ...).
                    Value::fcn_from_pairs(pairs).expect("distinct keys").with_decoded_dom()
                }
                Kind::Record { fields: fs, .. } => Value::Record(fs.iter().map(|f| (f.0, f.1.decode_loc_unchecked(words, f.2))).collect()),
                Kind::Tuple { elems: ss, .. } => Value::Tuple(ss.iter().map(|s| s.0.decode_loc_unchecked(words, s.1)).collect()),
                Kind::Seq { elem, slot, .. } => {
                    let len = words[0] as usize;
                    Value::Tuple((0..len).map(|i| elem.decode_loc_unchecked(words, slot.loc(1, i))).collect())
                }
                Kind::Union { arms, .. } => arms[words[0] as usize].decode_unchecked(&words[1..]),
                Kind::Dyn => dynval::lookup_unchecked(words[0]),
                Kind::Ref(store) => store.thaw_slot(words[0]),
            }
        }
    }

    /// Rank of `v` within the finite universe of this shape (as
    /// `layout::rank`).
    pub fn rank(&self, v: &Value) -> Result<u64, Miss> {
        if self.card.is_none() {
            let mut m = Miss::new(v);
            m.path.push_str("<shape has no finite universe>");
            return Err(m);
        }
        self.rank_finite(v)
    }

    /// `rank` for a shape whose cardinality is known to fit in u64.
    fn rank_finite(&self, v: &Value) -> Result<u64, Miss> {
        // Scalars first (the common case of bitset elements and map keys),
        // without `force`.
        match (&self.kind, v) {
            (Kind::Bool, Value::Bool(b)) => return Ok(*b as u64),
            (Kind::Int { lo, hi }, Value::Int(n)) if lo <= n && n <= hi => return Ok(n.wrapping_sub(*lo) as u64),
            (Kind::Atom(u), Value::Str(_) | Value::ModelValue(_)) => {
                return u.binary_search(v).map(|i| i as u64).map_err(|_| Miss::new(v));
            }
            _ => {}
        }
        let Some(v) = force(v) else { return Err(Miss::new(v)) };
        let v = self.fit(v);
        let v = &*v;
        Ok(match (&self.kind, v) {
            (Kind::Bool, Value::Bool(b)) => *b as u64,
            (Kind::Int { lo, hi }, Value::Int(n)) if lo <= n && n <= hi => n.wrapping_sub(*lo) as u64,
            (Kind::Atom(u), Value::Str(_) | Value::ModelValue(_)) => u.binary_search(v).map_err(|_| Miss::new(v))? as u64,
            (Kind::Set { elem, max_card, rank, .. }, Value::Set(_) | Value::Interval(..)) => {
                if set_len(v).unwrap() > *max_card as u64 {
                    return Err(Miss::new(v));
                }
                let es = set_elems(v).unwrap();
                match rank {
                    SetRank::Mask => {
                        let mut r = 0u64;
                        for e in es.iter() {
                            r |= 1u64 << elem.rank_finite(e).map_err(|m| m.under("{}"))?;
                        }
                        r
                    }
                    SetRank::Comb { by_size, .. } => {
                        let mut ranks = Vec::with_capacity(es.len());
                        for e in es.iter() {
                            ranks.push(elem.rank_finite(e).map_err(|m| m.under("{}"))?);
                        }
                        ranks.sort_unstable();
                        let mut r = by_size[ranks.len()];
                        for (i, &c) in ranks.iter().enumerate() {
                            r += binom(c, i as u64 + 1).unwrap();
                        }
                        r
                    }
                    SetRank::None => unreachable!("rank: set shape without finite universe"),
                }
            }
            (Kind::Fcn { dom, range, .. }, Value::Fcn(ps, _)) => {
                if !same_domain(ps, dom) {
                    return Err(Miss::new(v));
                }
                let c = range.card.unwrap();
                let mut r = 0u64;
                for (k, x) in ps.iter() {
                    r = r * c + range.rank_finite(x).map_err(|m| m.under(format_args!("[{k}]")))?;
                }
                r
            }
            (Kind::Map { key, range, universe, .. }, Value::Fcn(..) | Value::Tuple(_) | Value::Record(_)) => {
                // Mixed radix over the universe: digit 0 = absent, 1 + rank otherwise.
                let c = range.card.unwrap() + 1;
                let mut digits = vec![0u64; *universe as usize];
                for_each_pair(v, |k, x| {
                    let r = key.rank_finite(k).map_err(|m| m.under("DOMAIN"))?;
                    digits[r as usize] = 1 + range.rank_finite(x).map_err(|m| m.under(format_args!("[{k}]")))?;
                    Ok(())
                })?;
                digits.iter().fold(0u64, |acc, d| acc * c + d)
            }
            (Kind::Record { fields: fs, .. }, Value::Record(vs)) => {
                if fs.len() != vs.len() || !fs.iter().zip(vs.iter()).all(|(f, x)| f.0 == x.0) {
                    return Err(Miss::new(v));
                }
                let mut r = 0u64;
                for (f, x) in fs.iter().zip(vs.iter()) {
                    r = r * f.1.card.unwrap() + f.1.rank_finite(&x.1).map_err(|m| m.under(format_args!(".{}", f.0.as_str())))?;
                }
                r
            }
            (Kind::Tuple { elems: ss, .. }, Value::Tuple(vs)) => {
                if ss.len() != vs.len() {
                    return Err(Miss::new(v));
                }
                let mut r = 0u64;
                for (i, (s, x)) in ss.iter().zip(vs.iter()).enumerate() {
                    r = r * s.0.card.unwrap() + s.0.rank_finite(x).map_err(|m| m.under(format_args!("[{}]", i + 1)))?;
                }
                r
            }
            (Kind::Seq { elem, max_len, shorter, .. }, Value::Tuple(vs)) => {
                if vs.len() > *max_len {
                    return Err(Miss::new(v));
                }
                let c = elem.card.unwrap();
                let mut m = 0u64;
                for (i, x) in vs.iter().enumerate() {
                    m = m * c + elem.rank_finite(x).map_err(|e| e.under(format_args!("[{}]", i + 1)))?;
                }
                shorter.as_ref().expect("rank: finite sequence shape")[vs.len()] + m
            }
            (Kind::Union { arms, base }, _) => {
                let i = arm_for(arms, v).ok_or_else(|| Miss::new(v))?;
                base.as_ref().expect("rank: finite union shape")[i] + arms[i].rank_finite(v)?
            }
            _ => return Err(Miss::new(v)),
        })
    }

    /// Inverse of `rank` (as `layout::unrank`). Panics if the shape has no
    /// finite universe or `r >= cardinality`.
    pub fn unrank(&self, r: u64) -> Value {
        let card = self.card.expect("unrank: shape without finite universe");
        assert!(r < card, "unrank: rank {r} out of range (cardinality {card})");
        self.unrank_finite(r)
    }

    fn unrank_finite(&self, mut r: u64) -> Value {
        match &self.kind {
            Kind::Bool => Value::Bool(r != 0),
            Kind::Int { lo, .. } => Value::Int(lo.wrapping_add(r as i64)),
            Kind::Atom(u) => u[r as usize].clone(),
            Kind::Set { elem, rank, .. } => {
                let mut ranks = Vec::new();
                match rank {
                    SetRank::Mask => {
                        while r != 0 {
                            ranks.push(r.trailing_zeros() as u64);
                            r &= r - 1;
                        }
                    }
                    SetRank::Comb { n, by_size } => {
                        let n = *n;
                        // The size: the last k with by_size[k] <= r.
                        let k = by_size.partition_point(|&b| b <= r) - 1;
                        r -= by_size[k];
                        // Combinatorial number system: the i-th largest element
                        // rank is the largest c with C(c, i) <= remaining rank.
                        for i in (1..=k as u64).rev() {
                            let (mut lo, mut hi) = (i - 1, n - 1);
                            while lo < hi {
                                let mid = lo + (hi - lo).div_ceil(2);
                                if binom(mid, i).unwrap_or(u64::MAX) <= r {
                                    lo = mid;
                                } else {
                                    hi = mid - 1;
                                }
                            }
                            r -= binom(lo, i).unwrap();
                            ranks.push(lo);
                        }
                    }
                    SetRank::None => unreachable!("unrank: set shape without finite universe"),
                }
                sorted_set(ranks.into_iter().map(|e| elem.unrank_finite(e)).collect())
            }
            Kind::Fcn { dom, range, .. } => {
                let c = range.card.unwrap();
                let vals = mixed_radix(r, dom.iter().map(|_| (range.as_ref(), c)));
                Value::fcn_decoded(dom.iter().cloned().zip(vals).collect())
            }
            Kind::Record { fields: fs, .. } => {
                let vals = mixed_radix(r, fs.iter().map(|f| (&f.1, f.1.card.unwrap())));
                Value::Record(fs.iter().map(|f| f.0).zip(vals).collect())
            }
            Kind::Tuple { elems: ss, .. } => Value::Tuple(mixed_radix(r, ss.iter().map(|s| (&s.0, s.0.card.unwrap()))).into()),
            Kind::Seq { elem, shorter, .. } => {
                let c = elem.card.unwrap();
                let shorter = shorter.as_ref().expect("unrank: finite sequence shape");
                // The length: the last l with shorter[l] <= r.
                let len = shorter.partition_point(|&b| b <= r) - 1;
                r -= shorter[len];
                Value::Tuple(mixed_radix(r, (0..len).map(|_| (elem.as_ref(), c))).into())
            }
            Kind::Union { arms, base } => {
                let base = base.as_ref().expect("unrank: finite union shape");
                // The last arm starting at or before `r` (empty arms share
                // their base with the next arm, which is the one found).
                let i = base.partition_point(|&b| b <= r) - 1;
                arms[i].unrank_finite(r - base[i])
            }
            Kind::Map { key, range, universe, .. } => {
                let c = range.card.unwrap() + 1;
                let mut digits = vec![0u64; *universe as usize];
                for d in digits.iter_mut().rev() {
                    *d = r % c;
                    r /= c;
                }
                let pairs = digits
                    .iter()
                    .enumerate()
                    .filter(|(_, d)| **d > 0)
                    .map(|(k, d)| (key.unrank_finite(k as u64), range.unrank_finite(d - 1)))
                    .collect();
                Value::fcn_from_pairs(pairs).expect("distinct keys").with_decoded_dom()
            }
            Kind::Never | Kind::Dyn | Kind::Ref(_) => unreachable!("unrank: shape without finite universe"),
        }
    }
}

/// Re-encode the encoding `src` of a value of layout `old` as layout `new`
/// into `dst` (zeroed): word by word where the encodings correspond (equal
/// shapes, shifted integer ranges, the same structure around them), else
/// through the value. False if the value does not fit `new`.
pub fn transcode(old: &LayoutNode, new: &LayoutNode, src: &[u64], dst: &mut [u64]) -> bool {
    // SAFETY: the false instantiation checks handles before materializing them.
    unsafe { transcode_impl::<false>(old, new, src, dst) }
}

/// Transcode a trusted value, preserving its valid Dyn handles.
///
/// # Safety
/// `src` must satisfy `old.decode_unchecked`'s valid-encoding and publication
/// contract. The destination must have space for `new.words()` words.
pub unsafe fn transcode_unchecked(old: &LayoutNode, new: &LayoutNode, src: &[u64], dst: &mut [u64]) -> bool {
    // SAFETY: the caller guarantees the original active payloads are valid.
    unsafe { transcode_impl::<true>(old, new, src, dst) }
}

unsafe fn transcode_impl<const TRUSTED: bool>(old: &LayoutNode, new: &LayoutNode, src: &[u64], dst: &mut [u64]) -> bool {
    // SAFETY: recursive active slots inherit the trusted contract, or the
    // false instantiation uses checked decoding when materializing a value.
    unsafe {
        if old == new {
            let w = new.words;
            dst[..w].copy_from_slice(&src[..w]);
            return true;
        }
        match (&old.kind, &new.kind) {
            (Kind::Int { lo: l0, .. }, Kind::Int { lo: l1, hi: h1 }) => {
                let v = l0.wrapping_add(src[0] as i64);
                dst[0] = v.wrapping_sub(*l1) as u64;
                *l1 <= v && v <= *h1
            }
            (Kind::Fcn { dom: d0, range: r0, slot: s0 }, Kind::Fcn { dom: d1, range: r1, slot: s1 }) if d0 == d1 => {
                (0..d0.len()).all(|i| transcode_field::<TRUSTED>(r0, src, s0.loc(0, i), r1, dst, s1.loc(0, i)))
            }
            (Kind::Record { fields: f0, .. }, Kind::Record { fields: f1, .. })
                if f0.len() == f1.len() && f0.iter().zip(f1.iter()).all(|(a, b)| a.0 == b.0) =>
            {
                f0.iter().zip(f1.iter()).all(|(a, b)| transcode_field::<TRUSTED>(&a.1, src, a.2, &b.1, dst, b.2))
            }
            (Kind::Tuple { elems: t0, .. }, Kind::Tuple { elems: t1, .. }) if t0.len() == t1.len() => {
                t0.iter().zip(t1.iter()).all(|(a, b)| transcode_field::<TRUSTED>(&a.0, src, a.1, &b.0, dst, b.1))
            }
            (Kind::Seq { elem: e0, slot: s0, .. }, Kind::Seq { elem: e1, max_len, slot: s1, .. }) => {
                let n = src[0] as usize;
                dst[0] = src[0];
                n <= *max_len && (0..n).all(|i| transcode_field::<TRUSTED>(e0, src, s0.loc(1, i), e1, dst, s1.loc(1, i)))
            }
            // Maps on the same keys, or on integer ranges: each present slot.
            (Kind::Map { key: k0, range: r0, universe: u0, dims: d0 }, Kind::Map { key: k1, range: r1, universe: u1, dims: d1 })
                if k0 == k1 || matches!((&k0.kind, &k1.kind), (Kind::Int { .. }, Kind::Int { .. })) =>
            {
                // Rank in the new universe of the key of rank `r` in the old one.
                let shift = match (&k0.kind, &k1.kind) {
                    (Kind::Int { lo: l0, .. }, Kind::Int { lo: l1, .. }) => l0 - l1,
                    _ => 0,
                };
                for r in 0..*u0 as usize {
                    if src[r / 64] >> (r % 64) & 1 == 1 {
                        let Some(q) = usize::try_from(r as i64 + shift).ok().filter(|&q| (q as u64) < *u1) else { return false };
                        dst[q / 64] |= 1 << (q % 64);
                        if !transcode_field::<TRUSTED>(r0, src, d0.slot_loc(r), r1, dst, d1.slot_loc(q)) {
                            return false;
                        }
                    }
                }
                true
            }
            // Sets of the same elements: the same bitset, or the same sorted
            // elements with another maximal cardinality (which a bitset must
            // respect too, as `encode` checks).
            (Kind::Set { elem: e0, bitset, .. }, Kind::Set { elem: e1, max_card, .. }) if e0 == e1 => match bitset {
                Some(n) => {
                    let w = n.div_ceil(64) as usize;
                    dst[..w].copy_from_slice(&src[..w]);
                    src[..w].iter().map(|x| x.count_ones() as usize).sum::<usize>() <= *max_card
                }
                None => {
                    let w = 1 + src[0] as usize * e0.words;
                    dst[..w].copy_from_slice(&src[..w]);
                    src[0] as usize <= *max_card
                }
            },
            _ => new.encode(&if TRUSTED { old.decode_unchecked(src) } else { old.decode(src) }, dst).is_ok(),
        }
    }
}

/// Transcode a single child slot (word-aligned or bit-packed) inside a zeroed
/// composite destination `dst`.
unsafe fn transcode_field<const TRUSTED: bool>(
    old: &LayoutNode,
    src: &[u64],
    old_loc: FieldLoc,
    new: &LayoutNode,
    dst: &mut [u64],
    new_loc: FieldLoc,
) -> bool {
    // SAFETY: active child slots inherit `transcode_impl`'s contract; packed
    // bitfields are always scalars (never Dyn/Ref handles).
    unsafe {
        let src_tmp;
        let src_slice = match old_loc {
            FieldLoc::Words(o0) => &src[o0..],
            FieldLoc::Bits(p0) => {
                src_tmp = [p0.extract(src)];
                &src_tmp[..]
            }
        };
        match new_loc {
            FieldLoc::Words(o1) => transcode_impl::<TRUSTED>(old, new, src_slice, &mut dst[o1..]),
            FieldLoc::Bits(p1) => {
                let mut d_buf = [0u64];
                if !transcode_impl::<TRUSTED>(old, new, src_slice, &mut d_buf) {
                    return false;
                }
                p1.set_zeroed(dst, d_buf[0]);
                true
            }
        }
    }
}

/// Call `f` on the (key, value) pairs of a function value (tuples and
/// records are functions too), in order, without copying them.
fn for_each_pair(v: &Value, mut f: impl FnMut(&Value, &Value) -> Result<(), Miss>) -> Result<(), Miss> {
    match v {
        Value::Fcn(ps, _) => ps.iter().try_for_each(|(k, x)| f(k, x)),
        Value::Tuple(es) => es.iter().enumerate().try_for_each(|(i, x)| f(&Value::Int(i as i64 + 1), x)),
        Value::Record(fs) => fs.iter().try_for_each(|(k, x)| f(&Value::Str(*k), x)),
        _ => panic!("function value expected"),
    }
}

impl LayoutNode {
    /// `v` in this node's function representation (`shape::fit_repr`).
    fn fit<'a>(&self, v: std::borrow::Cow<'a, Value>) -> std::borrow::Cow<'a, Value> {
        match self.kind {
            Kind::Fcn { .. } => fit_repr(true, v),
            Kind::Tuple { .. } | Kind::Seq { .. } | Kind::Record { .. } => fit_repr(false, v),
            _ => v,
        }
    }
}

/// Index of the union arm whose kind matches the (normalized) value `v`
/// (as `shape::arm_for`).
fn arm_for(arms: &[LayoutNode], v: &Value) -> Option<usize> {
    let direct = arms.iter().position(|a| match (&a.kind, v) {
        (Kind::Bool, Value::Bool(_))
        | (Kind::Int { .. }, Value::Int(_))
        | (Kind::Atom(_), Value::Str(_) | Value::ModelValue(_))
        | (Kind::Set { .. }, Value::Set(_) | Value::Interval(..))
        | (Kind::Seq { .. }, Value::Tuple(_))
        | (Kind::Fcn { .. } | Kind::Map { .. }, Value::Fcn(..)) => true,
        (Kind::Tuple { elems: ss, .. }, Value::Tuple(vs)) => ss.len() == vs.len(),
        (Kind::Record { fields: fs, .. }, Value::Record(vs)) => fs.len() == vs.len() && fs.iter().zip(vs.iter()).all(|(f, x)| f.0 == x.0),
        _ => false,
    });
    // Tuples and records are functions too: a map arm takes them otherwise,
    // or a function arm over their domain; a function over an enumerated
    // `1..n` or set of strings goes to a tuple / sequence / record arm (see
    // `shape::fit_repr`).
    direct.or_else(|| match v {
        Value::Tuple(_) | Value::Record(_) => arms.iter().position(|a| matches!(a.kind, Kind::Map { .. })).or_else(|| {
            let Value::Fcn(ps, _) = v.clone().into_fcn_rcd() else { return None };
            arms.iter().position(|a| matches!(&a.kind, Kind::Fcn { dom, .. } if same_domain(&ps, dom)))
        }),
        Value::Fcn(..) => v.fcn_canonical().and_then(|c| arm_for(arms, &c)),
        _ => None,
    })
}

/// Decode a mixed-radix number (first digit most significant).
fn mixed_radix<'a>(mut r: u64, digits: impl DoubleEndedIterator<Item = (&'a LayoutNode, u64)>) -> Vec<Value> {
    let mut out: Vec<Value> = digits
        .rev()
        .map(|(s, c)| {
            let d = r % c;
            r /= c;
            s.unrank_finite(d)
        })
        .collect();
    out.reverse();
    out
}
