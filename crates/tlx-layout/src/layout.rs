//! Fixed-width encoding of values of a given shape into `u64` words.
//!
//! Encodings are canonical: for values `a`, `b` of shape `s`,
//! `encode(a) == encode(b)` iff `a == b`. Unused words (e.g. past the length
//! of a sequence) are zero.
//!
//! Representation per shape (one or more words):
//! - `Bool`: 0/1. `Int{lo,..}`: `v - lo`. `Atom(U)`: index of `v` in `U`.
//! - `Set` whose element universe has at most `MAX_BITSET_UNIVERSE` elements:
//!   a bitset over the element ranks (see `rank`); otherwise `len` followed
//!   by `max_card` element encodings sorted by rank-compatible order
//!   (lexicographic on encodings), zero-padded.
//! - `Fcn{dom, r}`: the encodings of `f[d]` for `d` in `dom` order.
//! - `Map{key, range}`: a presence bitset over the key ranks, then one slot
//!   per key rank (see `MapDims`).
//! - `Record`: field encodings in field order. `Tuple`: element encodings.
//! - `Seq{max_len}`: `len` then `max_len` element slots (zero-padded).
//! - `Union(arms)`: arm index, then the arm's encoding padded to the widest arm.
//! - `Dyn`: a handle from `dynval::intern`.
//! - `Never`: zero words (no value can be encoded).

use std::sync::Arc;

use crate::dynval;
use crate::layout_tree::LayoutNode;
pub use crate::pack::{
    bit_mask, bits_for_max, extract_bits, insert_bits, scalar_bits, BitPos, FieldGroup, FieldLayout, FieldLoc, SlotLayout,
};
use crate::shape::{
    arm_for, arm_for_semantic, binom, fcn_dom_matches_record, fcn_dom_matches_tuple, fcn_key_at, fit_shape, force, match_fcn_keys_exact,
    same_field_names, set_elems, set_len, FcnWitness, Shape, MAX_BITSET_UNIVERSE,
};
use tlx_value::{FcnDom, Value};

/// A value does not fit the layout (speculation failed); the host widens the
/// shape and recompiles.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Miss {
    /// Path from the variable to the offending sub-value, for diagnostics.
    pub path: String,
    pub value: Value,
}

impl Miss {
    pub(crate) fn new(v: &Value) -> Miss {
        Miss { path: String::new(), value: v.clone() }
    }

    /// Prepend a path segment (the error travels from the leaf upwards).
    pub(crate) fn under(mut self, seg: impl std::fmt::Display) -> Miss {
        let mut p = seg.to_string();
        p.push_str(&self.path);
        self.path = p;
        self
    }

    /// For misses reported by `Layout::encode_state`: the index of the
    /// variable whose value did not fit (such paths start with `#<index>`).
    pub fn var_index(&self) -> Option<usize> {
        let rest = self.path.strip_prefix('#')?;
        let end = rest.find(|c: char| !c.is_ascii_digit()).unwrap_or(rest.len());
        rest[..end].parse().ok()
    }
}

/// Layout of a whole state: one shape per variable, concatenated.
#[derive(Clone, Debug)]
pub struct Layout {
    pub vars: Vec<Shape>,
    /// Word offset of each variable.
    pub offsets: Vec<usize>,
    pub words: usize,
    /// Whether any variable's shape carries a dynamic function-domain witness.
    pub has_dynamic_witness: bool,
    /// The precomputed layout tree of each variable's shape.
    nodes: Vec<LayoutNode>,
}

impl Layout {
    pub fn new(vars: Vec<Shape>) -> Layout {
        let nodes: Vec<LayoutNode> = vars.iter().map(LayoutNode::new).collect();
        let has_dynamic_witness = nodes.iter().any(LayoutNode::has_dynamic_witness);
        let mut offsets = Vec::with_capacity(vars.len());
        let mut total = 0;
        for n in &nodes {
            offsets.push(total);
            total += n.words();
        }
        Layout { vars, offsets, words: total, has_dynamic_witness, nodes }
    }

    /// Zero every trailing dynamic function-domain witness word in an encoded
    /// state so semantically equal states have identical canonical words.
    pub fn canonicalize_state(&self, words: &mut [u64]) {
        if !self.has_dynamic_witness {
            return;
        }
        for (n, &o) in self.nodes.iter().zip(&self.offsets) {
            if n.has_dynamic_witness() {
                n.canonicalize_words(&mut words[o..]);
            }
        }
    }

    /// The layout tree of variable `i`.
    pub fn node(&self, i: usize) -> &LayoutNode {
        &self.nodes[i]
    }

    /// Word range of variable `i` in an encoded state.
    pub fn var_range(&self, i: usize) -> std::ops::Range<usize> {
        self.offsets[i]..self.offsets[i] + self.nodes[i].words()
    }

    /// Encode a state (values in variable order) into `out` (length `words`).
    ///
    /// On a miss, `Miss::path` starts with `#<variable index>` (see
    /// `Miss::var_index`) and the contents of `out` are unspecified.
    pub fn encode_state(&self, vals: &[Value], out: &mut [u64]) -> Result<(), Miss> {
        assert_eq!(vals.len(), self.vars.len(), "state has the wrong number of variables");
        let out = &mut out[..self.words];
        out.fill(0);
        for (i, (n, v)) in self.nodes.iter().zip(vals).enumerate() {
            let o = self.offsets[i];
            n.enc(v, &mut out[o..]).map_err(|m| m.under(format_args!("#{i}")))?;
        }
        Ok(())
    }

    pub fn decode_state(&self, words: &[u64]) -> Vec<Value> {
        self.nodes.iter().zip(&self.offsets).map(|(n, &o)| n.decode(&words[o..])).collect()
    }

    /// Check active handles before accepting external encoded state words.
    pub fn validate_words(&self, words: &[u64]) -> Result<(), String> {
        for (n, &o) in self.nodes.iter().zip(&self.offsets) {
            n.validate_words(words.get(o..).ok_or("short encoded state")?)?;
        }
        Ok(())
    }

    /// Strict canonical validation for checkpoint/external state boundaries:
    /// also rejects non-zero inactive tail and absent map slot words.
    pub fn validate_canonical_words(&self, words: &[u64]) -> Result<(), String> {
        for (n, &o) in self.nodes.iter().zip(&self.offsets) {
            n.validate_canonical_words(words.get(o..).ok_or("short encoded state")?)?;
        }
        Ok(())
    }

    /// Decode state words from the encoder or trusted generated code.
    ///
    /// # Safety
    /// Each variable must satisfy `LayoutNode::decode_unchecked`'s contract
    /// for this layout, including publication of all active Dyn handles.
    pub unsafe fn decode_state_unchecked(&self, words: &[u64]) -> Vec<Value> {
        // SAFETY: node offsets partition the caller's valid state encoding.
        self.nodes.iter().zip(&self.offsets).map(|(n, &o)| unsafe { n.decode_unchecked(&words[o..]) }).collect()
    }
}

/// Size of the element universe if sets of `elem` are encoded as bitsets
/// (`None`: sorted-array representation).
pub fn bitset_universe(elem: &Shape) -> Option<u64> {
    elem.cardinality().filter(|&n| n <= MAX_BITSET_UNIVERSE)
}

/// The encoding of a map (`Shape::Map`): a presence bitset over the key
/// universe (bit `r` set: the key of rank `r` is in the domain), then one
/// slot per key rank (`slot`, packed MSB-first when sub-word), zero for
/// absent keys. Every executor of encoded maps (the layout functions, the IR
/// executors, the JIT and the generated C) follows it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MapDims {
    /// Number of keys (the size of the key universe).
    pub universe: usize,
    /// Words of the presence bitset.
    pub bitset_words: usize,
    /// Layout of each value slot.
    pub slot: SlotLayout,
}

impl MapDims {
    pub fn new(universe: usize, slot: SlotLayout) -> MapDims {
        MapDims { universe, bitset_words: universe.div_ceil(64), slot }
    }

    /// The dimensions of map shape `s` (None: not a map shape, or keys
    /// without a bitset universe).
    pub fn of(s: &Shape) -> Option<MapDims> {
        let Shape::Map { key, range, .. } = s else { return None };
        Some(MapDims::new(bitset_universe(key)? as usize, SlotLayout::of(range)))
    }

    /// The dimensions of maps with keys `key` and values `range`.
    pub fn of_parts(key: &Shape, range: &Shape) -> MapDims {
        MapDims::new(bitset_universe(key).expect("map key universe") as usize, SlotLayout::of(range))
    }

    /// Words of the bitset and slots (excluding any trailing dynamic witness word).
    #[inline]
    pub fn words(&self) -> usize {
        self.bitset_words.saturating_add(self.slot.array_words(self.universe))
    }

    /// Storage location of the value slot for key rank `r`.
    #[inline]
    pub fn slot_loc(&self, r: usize) -> FieldLoc {
        self.slot.loc(self.bitset_words, r)
    }
}

/// Number of words used by values of this shape.
pub fn words(s: &Shape) -> usize {
    match s {
        Shape::Never => 0,
        Shape::Bool | Shape::Int { .. } | Shape::Atom(_) | Shape::Dyn | Shape::Ref(_) => 1,
        Shape::Set { elem, max_card } => match bitset_universe(elem) {
            Some(n) => n.div_ceil(64) as usize,
            None => 1usize.saturating_add(max_card.saturating_mul(words(elem))),
        },
        Shape::Fcn { dom, range, witness, key_variants } => {
            SlotLayout::of(range).array_words(dom.len()) + witness.extra_words() + key_variants.len()
        }
        Shape::Map { key, range, witness } => MapDims::of_parts(key, range).words() + witness.extra_words(),
        Shape::Record(fs) => FieldLayout::of_shapes(fs.iter().map(|(_, f)| f)).words,
        Shape::Tuple(es) => FieldLayout::of_shapes(es.iter()).words,
        Shape::Seq { elem, max_len } => 1usize.saturating_add(SlotLayout::of(elem).array_words(*max_len)),
        Shape::Union(arms) => 1 + arms.iter().map(words).max().unwrap_or(0),
    }
}

/// The word offsets (from `base`) of the value store handles in encodings
/// of `s`: a `Ref` at the top or in fixed positions (record fields, tuple
/// components, fixed-domain function slots). None if `s` holds one at a
/// variable position (in a set, sequence, map or union), where encodings
/// would not be canonical; layouts never build such shapes.
pub fn ref_offsets(s: &Shape, base: usize, out: &mut Vec<usize>) -> Option<()> {
    match s {
        Shape::Ref(_) => out.push(base),
        Shape::Record(fs) => {
            let fl = FieldLayout::of_shapes(fs.iter().map(|(_, f)| f));
            for ((_, f), loc) in fs.iter().zip(fl.locs.iter()) {
                if let FieldLoc::Words(w) = loc {
                    ref_offsets(f, base + *w, out)?;
                }
            }
        }
        Shape::Tuple(es) => {
            let fl = FieldLayout::of_shapes(es.iter());
            for (e, loc) in es.iter().zip(fl.locs.iter()) {
                if let FieldLoc::Words(w) = loc {
                    ref_offsets(e, base + *w, out)?;
                }
            }
        }
        Shape::Fcn { dom, range, .. } => {
            if let SlotLayout::Words(w) = SlotLayout::of(range) {
                for i in 0..dom.len() {
                    ref_offsets(range, base + i * w, out)?;
                }
            }
        }
        Shape::Set { elem: x, .. } | Shape::Seq { elem: x, .. } | Shape::Map { range: x, .. } if has_ref(x) => return None,
        Shape::Map { key, .. } if has_ref(key) => return None,
        Shape::Union(arms) if arms.iter().any(has_ref) => return None,
        _ => {}
    }
    Some(())
}

/// Whether `s` contains a `Ref`.
pub fn has_ref(s: &Shape) -> bool {
    let mut found = matches!(s, Shape::Ref(_));
    s.for_each_child(|c| found |= has_ref(c));
    found
}

/// The value store of the `Ref`s in `shapes`, if any. A run has one store:
/// panics if the shapes hold `Ref`s of two (a layout mixing runs).
pub fn store_of<'a>(shapes: impl IntoIterator<Item = &'a Shape>) -> Option<crate::store::StoreRef> {
    fn walk(s: &Shape, found: &mut Option<crate::store::StoreRef>) {
        if let Shape::Ref(st) = s {
            match found {
                Some(f) => assert!(f == st, "value store handles of two stores in one run ({:?}, {:?})", f.0, st.0),
                None => *found = Some(st.clone()),
            }
        }
        s.for_each_child(|c| walk(c, found));
    }
    let mut found = None;
    for s in shapes {
        walk(s, &mut found);
    }
    found
}

/// Sort fixed-width `ew`-word chunks from `src` into `dst`.
pub(crate) fn sort_word_chunks(src: &[u64], ew: usize, dst: &mut [u64]) {
    let mut chunks: Vec<&[u64]> = src.chunks_exact(ew).collect();
    chunks.sort_unstable();
    for (i, c) in chunks.into_iter().enumerate() {
        dst[i * ew..(i + 1) * ew].copy_from_slice(c);
    }
}

/// Encode `v` into `out[..words(s)]` (later words of `out` are untouched),
/// preserving function-domain construction witnesses.
pub fn encode(s: &Shape, v: &Value, out: &mut [u64]) -> Result<(), Miss> {
    out[..words(s)].fill(0);
    enc::<false>(s, v, out)
}

/// Encode `v` into `out[..words(s)]` ignoring function-domain construction
/// witnesses (for semantic equality/membership probes; trailing dynamic witness
/// words are written as 0).
pub fn encode_semantic(s: &Shape, v: &Value, out: &mut [u64]) -> Result<(), Miss> {
    out[..words(s)].fill(0);
    enc::<true>(s, v, out)
}

/// `encode` into an already zeroed `out`.
fn enc<const SEMANTIC: bool>(s: &Shape, v: &Value, out: &mut [u64]) -> Result<(), Miss> {
    if let Shape::Dyn = s {
        out[0] = if SEMANTIC { dynval::intern(v) } else { dynval::intern_exact(v) };
        return Ok(());
    }
    if let Shape::Ref(store) = s {
        // (A value the store cannot hold, or a full store, is a miss of
        // this slot; the compiled tier reports a full store as such.)
        out[0] = store.freeze(v).map_err(|_| Miss::new(v))?;
        return Ok(());
    }
    let Some(v) = force(v) else { return Err(Miss::new(v)) };
    let v = if SEMANTIC { fit_shape(s, v) } else { v };
    let v = &*v;
    match (s, v) {
        (Shape::Bool, Value::Bool(b)) => out[0] = *b as u64,
        (Shape::Int { lo, hi }, Value::Int(n)) if lo <= n && n <= hi => out[0] = n.wrapping_sub(*lo) as u64,
        (Shape::Atom(u), Value::Str(_) | Value::ModelValue(_)) => match u.binary_search(v) {
            Ok(i) => out[0] = i as u64,
            Err(_) => return Err(Miss::new(v)),
        },
        (Shape::Set { elem, max_card }, Value::Set(_) | Value::Interval(..)) => {
            if !SEMANTIC && matches!(v, Value::Interval(..)) {
                return Err(Miss::new(v));
            }
            if set_len(v).unwrap() > *max_card as u64 {
                return Err(Miss::new(v));
            }
            let es = set_elems(v).unwrap();
            if bitset_universe(elem).is_some() {
                for e in es.iter() {
                    let r = rank_finite::<SEMANTIC>(elem, e).map_err(|m| m.under("{}"))?;
                    out[(r / 64) as usize] |= 1u64 << (r % 64);
                }
            } else {
                let ew = words(elem);
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
                    enc::<SEMANTIC>(elem, e, &mut buf[i * ew..]).map_err(|m| m.under("{}"))?;
                }
                sort_word_chunks(&buf, ew, &mut out[1..]);
            }
        }
        (Shape::Fcn { dom, range, witness, key_variants }, Value::Fcn(ps, d)) => {
            if !(SEMANTIC || witness.accepts_dom(*d)) {
                return Err(Miss::new(v));
            }
            let slot = SlotLayout::of(range);
            let payload_words = slot.array_words(dom.len());
            let kv_base = payload_words + witness.extra_words();
            let dom_ok = if SEMANTIC {
                same_domain(ps, dom)
            } else {
                match_fcn_keys_exact(ps.iter().map(|(k, _)| k), dom, key_variants, |slot, idx| {
                    out[kv_base + slot] = idx as u64;
                })
            };
            if !dom_ok {
                return Err(Miss::new(v));
            }
            for (i, (k, x)) in ps.iter().enumerate() {
                enc_loc::<SEMANTIC>(range, x, out, slot.loc(0, i)).map_err(|m| m.under(format_args!("[{k}]")))?;
            }
            if *witness == FcnWitness::Dynamic {
                out[payload_words] = u64::from(!SEMANTIC && *d == FcnDom::Enumerated);
            }
        }
        (Shape::Fcn { dom, range, witness: FcnWitness::Dynamic, key_variants }, Value::Tuple(vs)) => {
            if (!SEMANTIC && !key_variants.is_empty()) || !fcn_dom_matches_tuple(dom, vs.len()) {
                return Err(Miss::new(v));
            }
            let slot = SlotLayout::of(range);
            let payload_words = slot.array_words(dom.len());
            for (i, x) in vs.iter().enumerate() {
                enc_loc::<SEMANTIC>(range, x, out, slot.loc(0, i)).map_err(|m| m.under(format_args!("[{}]", i + 1)))?;
            }
            out[payload_words] = 0;
        }
        (Shape::Fcn { dom, range, witness: FcnWitness::Dynamic, key_variants }, Value::Record(fs)) => {
            if (!SEMANTIC && !key_variants.is_empty()) || !fcn_dom_matches_record(dom, fs) {
                return Err(Miss::new(v));
            }
            let slot = SlotLayout::of(range);
            let payload_words = slot.array_words(dom.len());
            for (i, (k, x)) in fs.iter().enumerate() {
                enc_loc::<SEMANTIC>(range, x, out, slot.loc(0, i)).map_err(|m| m.under(format_args!(".{}", k.as_str())))?;
            }
            out[payload_words] = 0;
        }
        (Shape::Map { key, range, witness }, Value::Fcn(..) | Value::Tuple(_) | Value::Record(_)) => {
            if !(SEMANTIC || witness.accepts_map_value(v)) {
                return Err(Miss::new(v));
            }
            let d = MapDims::of_parts(key, range);
            for (k, x) in crate::shape::fcn_pairs(v).expect("function value") {
                let r = rank_finite::<SEMANTIC>(key, &k).map_err(|m| m.under("DOMAIN"))?;
                out[(r / 64) as usize] |= 1u64 << (r % 64);
                enc_loc::<SEMANTIC>(range, &x, out, d.slot_loc(r as usize)).map_err(|m| m.under(format_args!("[{k}]")))?;
            }
            if *witness == FcnWitness::Dynamic {
                out[d.words()] = u64::from(!SEMANTIC && matches!(v, Value::Fcn(_, FcnDom::Enumerated)));
            }
        }
        (Shape::Record(fs), Value::Record(vs)) => {
            if !same_field_names(fs, vs) {
                return Err(Miss::new(v));
            }
            let fl = FieldLayout::of_shapes(fs.iter().map(|(_, f)| f));
            for ((f, x), &loc) in fs.iter().zip(vs.iter()).zip(fl.locs.iter()) {
                enc_loc::<SEMANTIC>(&f.1, &x.1, out, loc).map_err(|m| m.under(format_args!(".{}", f.0.as_str())))?;
            }
        }
        (Shape::Tuple(ss), Value::Tuple(vs)) => {
            if ss.len() != vs.len() {
                return Err(Miss::new(v));
            }
            let fl = FieldLayout::of_shapes(ss.iter());
            for (i, ((s, x), &loc)) in ss.iter().zip(vs.iter()).zip(fl.locs.iter()).enumerate() {
                enc_loc::<SEMANTIC>(s, x, out, loc).map_err(|m| m.under(format_args!("[{}]", i + 1)))?;
            }
        }
        (Shape::Seq { elem, max_len }, Value::Tuple(vs)) => {
            if vs.len() > *max_len {
                return Err(Miss::new(v));
            }
            out[0] = vs.len() as u64;
            let slot = SlotLayout::of(elem);
            for (i, x) in vs.iter().enumerate() {
                enc_loc::<SEMANTIC>(elem, x, out, slot.loc(1, i)).map_err(|m| m.under(format_args!("[{}]", i + 1)))?;
            }
        }
        (Shape::Union(arms), _) => match if SEMANTIC { arm_for_semantic(arms, v) } else { arm_for(arms, v) } {
            Some(i) => {
                out[0] = i as u64;
                enc::<SEMANTIC>(&arms[i], v, &mut out[1..])?;
            }
            None => return Err(Miss::new(v)),
        },
        _ => return Err(Miss::new(v)),
    }
    Ok(())
}

pub fn decode(s: &Shape, words: &[u64]) -> Value {
    LayoutNode::new(s).validate_words(words).unwrap_or_else(|e| panic!("{e}"));
    // SAFETY: all active Dyn handles are checked and published; malformed
    // scalar encodings can only panic through checked Rust indexing.
    unsafe { decode_unchecked(s, words) }
}

/// Decode a trusted encoding of `s` without checking Dyn publication.
///
/// # Safety
/// `words` must encode a value of `s`; every Dyn handle must satisfy
/// `dynval::lookup_unchecked`'s publication contract.
pub unsafe fn decode_unchecked(s: &Shape, words: &[u64]) -> Value {
    // SAFETY: recursive payloads inherit the caller's valid-encoding contract.
    unsafe {
        match s {
            Shape::Never => panic!("decode: no value has shape Never"),
            Shape::Bool => Value::Bool(words[0] != 0),
            Shape::Int { lo, .. } => Value::Int(lo.wrapping_add(words[0] as i64)),
            Shape::Atom(u) => u[words[0] as usize].clone(),
            Shape::Set { elem, .. } => {
                let mut es: Vec<Value> = Vec::new();
                if let Some(n) = bitset_universe(elem) {
                    for (wi, &w) in words[..n.div_ceil(64) as usize].iter().enumerate() {
                        let mut bits = w;
                        while bits != 0 {
                            let b = bits.trailing_zeros() as u64;
                            bits &= bits - 1;
                            es.push(unrank_finite(elem, wi as u64 * 64 + b));
                        }
                    }
                } else {
                    let ew = self::words(elem);
                    let len = words[0] as usize;
                    es.extend((0..len).map(|i| decode_unchecked(elem, &words[1 + i * ew..])));
                }
                sorted_set(es)
            }
            Shape::Fcn { dom, range, witness, key_variants } => {
                let slot = SlotLayout::of(range);
                let payload_words = slot.array_words(dom.len());
                let kv_base = payload_words + witness.extra_words();
                let mut kv_slot = 0usize;
                let pairs: Vec<(Value, Value)> = (0..dom.len())
                    .map(|i| {
                        let key = fcn_key_at(dom, key_variants, &mut kv_slot, i, |slot, _| words[kv_base + slot] as usize).clone();
                        (key, decode_loc_unchecked(range, words, slot.loc(0, i)))
                    })
                    .collect();
                witness.decode_fcn(pairs, || words[payload_words])
            }
            Shape::Map { key, range, witness } => {
                let d = MapDims::of_parts(key, range);
                let mut pairs = Vec::new();
                for r in 0..d.universe as u64 {
                    if words[(r / 64) as usize] >> (r % 64) & 1 == 1 {
                        pairs.push((unrank_finite(key, r), decode_loc_unchecked(range, words, d.slot_loc(r as usize))));
                    }
                }
                witness.decode_map(pairs, || words[d.words()])
            }
            Shape::Record(fs) => {
                let fl = FieldLayout::of_shapes(fs.iter().map(|(_, f)| f));
                Value::Record(fs.iter().zip(fl.locs.iter()).map(|(f, &loc)| (f.0, decode_loc_unchecked(&f.1, words, loc))).collect())
            }
            Shape::Tuple(ss) => {
                let fl = FieldLayout::of_shapes(ss.iter());
                Value::Tuple(ss.iter().zip(fl.locs.iter()).map(|(s, &loc)| decode_loc_unchecked(s, words, loc)).collect())
            }
            Shape::Seq { elem, .. } => {
                let slot = SlotLayout::of(elem);
                let len = words[0] as usize;
                Value::Tuple((0..len).map(|i| decode_loc_unchecked(elem, words, slot.loc(1, i))).collect())
            }
            Shape::Union(arms) => decode_unchecked(&arms[words[0] as usize], &words[1..]),
            Shape::Dyn => dynval::lookup_unchecked(words[0]),
            Shape::Ref(store) => store.thaw_slot(words[0]),
        }
    }
}

fn enc_loc<const SEMANTIC: bool>(s: &Shape, v: &Value, out: &mut [u64], loc: FieldLoc) -> Result<(), Miss> {
    match loc {
        FieldLoc::Words(w) => enc::<SEMANTIC>(s, v, &mut out[w..]),
        FieldLoc::Bits(pos) => {
            let mut tmp = [0u64];
            enc::<SEMANTIC>(s, v, &mut tmp)?;
            pos.set_zeroed(out, tmp[0]);
            Ok(())
        }
    }
}

unsafe fn decode_loc_unchecked(s: &Shape, words: &[u64], loc: FieldLoc) -> Value {
    // SAFETY: `loc` selects an active child within `words`, upholding `decode_unchecked`'s contract.
    unsafe {
        match loc {
            FieldLoc::Words(w) => decode_unchecked(s, &words[w..]),
            FieldLoc::Bits(pos) => {
                let tmp = [pos.extract(words)];
                decode_unchecked(s, &tmp)
            }
        }
    }
}

/// Whether function pairs `ps` have exactly the domain `dom` (in order).
#[inline]
pub(crate) fn same_domain(ps: &[(Value, Value)], dom: &[Value]) -> bool {
    ps.len() == dom.len() && ps.iter().zip(dom).all(|(p, d)| p.0 == *d)
}

/// Canonical set value from distinct elements in any order.
pub(crate) fn sorted_set(mut es: Vec<Value>) -> Value {
    if !es.windows(2).all(|w| w[0] < w[1]) {
        es.sort_unstable();
        es.dedup();
    }
    Value::Set(Arc::from(es))
}

/// Rank of `v` within the (finite) universe of shape `s`: a bijection onto
/// `0..cardinality(s)`, monotone w.r.t. TLC order for Bool/Int/Atom/Record/
/// Tuple shapes (mixed radix, first field/element most significant).
///
/// Sets: if `max_card` admits every subset of the element universe, the rank
/// is the bitmask of the element ranks; otherwise subsets are ranked by size
/// (all smaller sizes first), then by the combinatorial number system over
/// the element ranks. Sequences: all shorter sequences first, then mixed
/// radix. Functions: mixed radix in domain order. Unions: the ranks of
/// earlier arms first. Fails (with `Miss`) if `v` is not in `s` or `s` has no
/// finite universe of at most `u64::MAX` values (`cardinality() == None`).
pub fn rank(s: &Shape, v: &Value) -> Result<u64, Miss> {
    if s.cardinality().is_none() {
        let mut m = Miss::new(v);
        m.path.push_str("<shape has no finite universe>");
        return Err(m);
    }
    rank_finite::<false>(s, v)
}

/// Rank of `v` within `s` ignoring function-domain construction witnesses
/// (for membership/lookup probes against sets and map domains).
pub fn rank_semantic(s: &Shape, v: &Value) -> Result<u64, Miss> {
    if s.cardinality().is_none() {
        let mut m = Miss::new(v);
        m.path.push_str("<shape has no finite universe>");
        return Err(m);
    }
    rank_finite::<true>(s, v)
}

/// `rank` for a shape whose cardinality is known to fit in u64.
fn rank_finite<const SEMANTIC: bool>(s: &Shape, v: &Value) -> Result<u64, Miss> {
    let Some(v) = force(v) else { return Err(Miss::new(v)) };
    let v = if SEMANTIC { fit_shape(s, v) } else { v };
    let v = &*v;
    Ok(match (s, v) {
        (Shape::Bool, Value::Bool(b)) => *b as u64,
        (Shape::Int { lo, hi }, Value::Int(n)) if lo <= n && n <= hi => n.wrapping_sub(*lo) as u64,
        (Shape::Atom(u), Value::Str(_) | Value::ModelValue(_)) => u.binary_search(v).map_err(|_| Miss::new(v))? as u64,
        (Shape::Set { elem, max_card }, Value::Set(_) | Value::Interval(..)) => {
            if !SEMANTIC && matches!(v, Value::Interval(..)) {
                return Err(Miss::new(v));
            }
            if set_len(v).unwrap() > *max_card as u64 {
                return Err(Miss::new(v));
            }
            let n = elem.cardinality().unwrap();
            let es = set_elems(v).unwrap();
            let mut ranks = Vec::with_capacity(es.len());
            for e in es.iter() {
                ranks.push(rank_finite::<SEMANTIC>(elem, e).map_err(|m| m.under("{}"))?);
            }
            if *max_card as u64 >= n {
                ranks.iter().fold(0u64, |acc, r| acc | (1u64 << r))
            } else {
                ranks.sort_unstable();
                let k = ranks.len() as u64;
                let mut r: u64 = (0..k).map(|j| binom(n, j).unwrap()).sum();
                for (i, &c) in ranks.iter().enumerate() {
                    r += binom(c, i as u64 + 1).unwrap();
                }
                r
            }
        }
        (Shape::Fcn { dom, range, witness, key_variants }, Value::Fcn(ps, d)) => {
            debug_assert!(*witness != FcnWitness::Dynamic && key_variants.is_empty(), "dynamic witness has no finite cardinality");
            let dom_ok =
                if SEMANTIC { same_domain(ps, dom) } else { match_fcn_keys_exact(ps.iter().map(|(k, _)| k), dom, key_variants, |_, _| {}) };
            if !(SEMANTIC || witness.accepts_dom(*d)) || !dom_ok {
                return Err(Miss::new(v));
            }
            let c = range.cardinality().unwrap();
            let mut r = 0u64;
            for (k, x) in ps.iter() {
                r = r * c + rank_finite::<SEMANTIC>(range, x).map_err(|m| m.under(format_args!("[{k}]")))?;
            }
            r
        }
        (Shape::Map { key, range, witness }, Value::Fcn(..) | Value::Tuple(_) | Value::Record(_)) => {
            debug_assert!(*witness != FcnWitness::Dynamic, "dynamic witness has no finite cardinality");
            if !(SEMANTIC || witness.accepts_map_value(v)) {
                return Err(Miss::new(v));
            }
            // Mixed radix over the universe: digit 0 = absent, 1 + rank otherwise.
            let u = key.cardinality().unwrap();
            let c = range.cardinality().unwrap() + 1;
            let mut digits = vec![0u64; u as usize];
            for (k, x) in crate::shape::fcn_pairs(v).expect("function value") {
                let r = rank_finite::<SEMANTIC>(key, &k).map_err(|m| m.under("DOMAIN"))?;
                digits[r as usize] = 1 + rank_finite::<SEMANTIC>(range, &x).map_err(|m| m.under(format_args!("[{k}]")))?;
            }
            digits.iter().fold(0u64, |acc, d| acc * c + d)
        }
        (Shape::Record(fs), Value::Record(vs)) => {
            if !same_field_names(fs, vs) {
                return Err(Miss::new(v));
            }
            let mut r = 0u64;
            for (f, x) in fs.iter().zip(vs.iter()) {
                let c = f.1.cardinality().unwrap();
                r = r * c + rank_finite::<SEMANTIC>(&f.1, &x.1).map_err(|m| m.under(format_args!(".{}", f.0.as_str())))?;
            }
            r
        }
        (Shape::Tuple(ss), Value::Tuple(vs)) => {
            if ss.len() != vs.len() {
                return Err(Miss::new(v));
            }
            let mut r = 0u64;
            for (i, (s, x)) in ss.iter().zip(vs.iter()).enumerate() {
                let c = s.cardinality().unwrap();
                r = r * c + rank_finite::<SEMANTIC>(s, x).map_err(|m| m.under(format_args!("[{}]", i + 1)))?;
            }
            r
        }
        (Shape::Seq { elem, max_len }, Value::Tuple(vs)) => {
            if vs.len() > *max_len {
                return Err(Miss::new(v));
            }
            let c = elem.cardinality().unwrap();
            let shorter: u64 = (0..vs.len()).map(|l| c.pow(l as u32)).sum();
            let mut m = 0u64;
            for (i, x) in vs.iter().enumerate() {
                m = m * c + rank_finite::<SEMANTIC>(elem, x).map_err(|e| e.under(format_args!("[{}]", i + 1)))?;
            }
            shorter + m
        }
        (Shape::Union(arms), _) => {
            let i = if SEMANTIC { arm_for_semantic(arms, v) } else { arm_for(arms, v) }.ok_or_else(|| Miss::new(v))?;
            let off: u64 = arms[..i].iter().map(|a| a.cardinality().unwrap()).sum();
            off + rank_finite::<SEMANTIC>(&arms[i], v)?
        }
        _ => return Err(Miss::new(v)),
    })
}

/// Inverse of `rank`. Panics if `s` has no finite universe or
/// `r >= cardinality(s)`.
pub fn unrank(s: &Shape, r: u64) -> Value {
    let card = s.cardinality().expect("unrank: shape without finite universe");
    assert!(r < card, "unrank: rank {r} out of range (cardinality {card})");
    unrank_finite(s, r)
}

fn unrank_finite(s: &Shape, mut r: u64) -> Value {
    match s {
        Shape::Bool => Value::Bool(r != 0),
        Shape::Int { lo, .. } => Value::Int(lo.wrapping_add(r as i64)),
        Shape::Atom(u) => u[r as usize].clone(),
        Shape::Set { elem, max_card } => {
            let n = elem.cardinality().unwrap();
            let mut ranks = Vec::new();
            if *max_card as u64 >= n {
                while r != 0 {
                    ranks.push(r.trailing_zeros() as u64);
                    r &= r - 1;
                }
            } else {
                let mut k = 0u64;
                loop {
                    let c = binom(n, k).unwrap();
                    if r < c {
                        break;
                    }
                    r -= c;
                    k += 1;
                }
                // Combinatorial number system: the i-th largest element rank is
                // the largest c with C(c, i) <= remaining rank.
                for i in (1..=k).rev() {
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
            sorted_set(ranks.into_iter().map(|e| unrank_finite(elem, e)).collect())
        }
        Shape::Fcn { dom, range, witness, key_variants } => {
            debug_assert!(key_variants.is_empty(), "unrank: dynamic key variants have no finite universe");
            let c = range.cardinality().unwrap();
            let vals = mixed_radix(r, dom.iter().map(|_| (range.as_ref(), c)));
            let pairs = dom.iter().cloned().zip(vals).collect();
            match witness {
                FcnWitness::Enumerated => Value::fcn_with_dom(pairs, FcnDom::Enumerated),
                FcnWitness::Interval => Value::fcn_with_dom(pairs, FcnDom::Interval),
                FcnWitness::Dynamic => unreachable!("unrank: dynamic witness has no finite universe"),
            }
        }
        Shape::Record(fs) => {
            let vals = mixed_radix(r, fs.iter().map(|f| (&f.1, f.1.cardinality().unwrap())));
            Value::Record(fs.iter().map(|f| f.0).zip(vals).collect())
        }
        Shape::Tuple(ss) => Value::Tuple(mixed_radix(r, ss.iter().map(|s| (s, s.cardinality().unwrap()))).into()),
        Shape::Seq { elem, .. } => {
            let c = elem.cardinality().unwrap();
            let mut len = 0usize;
            loop {
                let n = c.pow(len as u32);
                if r < n {
                    break;
                }
                r -= n;
                len += 1;
            }
            Value::Tuple(mixed_radix(r, (0..len).map(|_| (elem.as_ref(), c))).into())
        }
        Shape::Union(arms) => {
            for a in arms.iter() {
                let c = a.cardinality().unwrap();
                if r < c {
                    return unrank_finite(a, r);
                }
                r -= c;
            }
            unreachable!("unrank: rank out of range")
        }
        Shape::Map { key, range, witness } => {
            let u = key.cardinality().unwrap();
            let c = range.cardinality().unwrap() + 1;
            let mut digits = vec![0u64; u as usize];
            for d in digits.iter_mut().rev() {
                *d = r % c;
                r /= c;
            }
            let pairs = digits
                .iter()
                .enumerate()
                .filter(|(_, d)| **d > 0)
                .map(|(k, d)| (unrank_finite(key, k as u64), unrank_finite(range, d - 1)))
                .collect();
            match witness {
                FcnWitness::Enumerated => Value::fcn_with_dom(pairs, FcnDom::Enumerated),
                FcnWitness::Interval => Value::fcn_over_interval_sorted(pairs),
                FcnWitness::Dynamic => unreachable!("unrank: dynamic witness has no finite universe"),
            }
        }
        Shape::Never | Shape::Dyn | Shape::Ref(_) => unreachable!("unrank: shape without finite universe"),
    }
}

/// Decode a mixed-radix number (first digit most significant).
fn mixed_radix<'a>(mut r: u64, digits: impl DoubleEndedIterator<Item = (&'a Shape, u64)>) -> Vec<Value> {
    let mut out: Vec<Value> = digits
        .rev()
        .map(|(s, c)| {
            let d = r % c;
            r /= c;
            unrank_finite(s, d)
        })
        .collect();
    out.reverse();
    out
}
