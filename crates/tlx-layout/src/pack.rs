//! Sub-word bit-packing schema for fixed-width composite encodings (`Record`,
//! `Tuple`, `Fcn`, `Map`, `Seq`).
//!
//! `tlx-layout` is the single authoritative owner of scalar bit widths, bit
//! shifts, masks, field locations and homogeneous array slot layouts; lowered
//! IR, the closure executor, C codegen and the Cranelift JIT all consume these
//! descriptors directly without recomputing layout rules.
//!
//! Within each shared `u64` word, sub-word fields and array elements are packed
//! **MSB-first** (the first field/element occupies the most significant bits of
//! word 0, down toward bit 0, never straddling a `u64` boundary), with all
//! unused tail/padding bits canonicalized to `0`. Because every scalar's raw
//! unsigned code (`0/1` for `Bool`, `v - lo` for `Int`, universe index for
//! `Atom`) is monotone in TLC value order, plain unsigned `u64` slice
//! comparison (`a[..w].cmp(&b[..w])`) on packed `Record`, `Tuple`, `Fcn` and
//! `Seq` encodings preserves exact TLC lexicographic order.

use crate::layout::words;
use crate::Shape;

/// Bit mask of `bits` (`1 <= bits <= 63`) low bits.
#[inline]
pub const fn bit_mask(bits: u8) -> u64 {
    debug_assert!(bits >= 1 && bits <= 63);
    (1u64 << bits) - 1
}

/// Extract a `bits`-wide unsigned field at `shift` from `word`.
#[inline]
pub const fn extract_bits(word: u64, shift: u8, bits: u8) -> u64 {
    (word >> shift) & bit_mask(bits)
}

/// Replace the `bits`-wide field at `shift` in `word` with `val` (masked).
#[inline]
pub const fn insert_bits(word: u64, shift: u8, bits: u8, val: u64) -> u64 {
    let m = bit_mask(bits);
    (word & !(m << shift)) | ((val & m) << shift)
}

/// Number of bits (`1..=63`) required to represent unsigned integers `0..=max_val`
/// where `max_val < (1 << 63)`. Singleton ranges (`max_val == 0`) use `1` bit so
/// every inhabited packed scalar has a non-zero width in `1..=63`.
#[inline]
pub const fn bits_for_max(max_val: u64) -> u8 {
    debug_assert!(max_val < (1u64 << 63));
    if max_val <= 1 {
        1
    } else {
        (64 - max_val.leading_zeros()) as u8
    }
}

/// Sub-word bit width (`0..=63`) when `s` is a packable scalar leaf inside a
/// composite shape, or `None` when `s` requires word-aligned storage (`1` full
/// 64-bit word for full-span `Int`, `Dyn`, `Ref`, or `words(s)` words for
/// composites).
///
/// Standalone state variables and temporaries of scalar `Shape` still occupy
/// `words(s)` (`1` word, or `0` for `Never`), avoiding bit-extraction overhead
/// on narrow scalar specs.
pub fn scalar_bits(s: &Shape) -> Option<u8> {
    match s {
        Shape::Never => Some(0),
        Shape::Bool => Some(1),
        Shape::Atom(u) => {
            if u.is_empty() {
                Some(0)
            } else {
                let max_val = (u.len() - 1) as u64;
                (max_val < (1u64 << 63)).then(|| bits_for_max(max_val))
            }
        }
        Shape::Int { lo, hi } => {
            if hi < lo {
                Some(0)
            } else {
                let span = (*hi as i128 - *lo as i128) as u128;
                (span < (1u128 << 63)).then(|| bits_for_max(span as u64))
            }
        }
        _ => None,
    }
}

/// Position of a sub-word scalar field (`1 <= bits <= 63`, `shift + bits <= 64`)
/// inside a composite encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct BitPos {
    pub word: usize,
    pub shift: u8,
    pub bits: u8,
}

impl BitPos {
    #[inline]
    pub const fn new(word: usize, shift: u8, bits: u8) -> Self {
        Self { word, shift, bits }
    }

    #[inline]
    pub const fn mask(self) -> u64 {
        bit_mask(self.bits)
    }

    #[inline]
    pub const fn shifted_mask(self) -> u64 {
        bit_mask(self.bits) << self.shift
    }

    #[inline]
    pub const fn clear_mask(self) -> u64 {
        !self.shifted_mask()
    }

    #[inline]
    pub const fn valid_in(self, total_words: usize) -> bool {
        self.bits >= 1 && self.bits <= 63 && (self.shift as u16 + self.bits as u16) <= 64 && self.word < total_words
    }

    #[inline]
    pub const fn offset_words(self, base_word: usize) -> Self {
        Self { word: base_word.saturating_add(self.word), shift: self.shift, bits: self.bits }
    }

    #[inline]
    pub fn extract(self, words: &[u64]) -> u64 {
        extract_bits(words[self.word], self.shift, self.bits)
    }

    #[inline]
    pub fn insert(self, words: &mut [u64], val: u64) {
        let w = &mut words[self.word];
        *w = insert_bits(*w, self.shift, self.bits, val);
    }

    #[inline]
    pub fn set_zeroed(self, words: &mut [u64], val: u64) {
        words[self.word] |= (val & bit_mask(self.bits)) << self.shift;
    }
}

/// Storage location of a field or element inside a composite encoding.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum FieldLoc {
    /// Word-aligned child starting at `word` (`words(child)` words long).
    Words(usize),
    /// Sub-word packed scalar at `BitPos` (`1` word when standalone).
    Bits(BitPos),
}

impl FieldLoc {
    #[inline]
    pub const fn offset_words(self, base_word: usize) -> Self {
        match self {
            FieldLoc::Words(w) => FieldLoc::Words(base_word.saturating_add(w)),
            FieldLoc::Bits(pos) => FieldLoc::Bits(pos.offset_words(base_word)),
        }
    }
}

/// One occupied word-aligned group of fields inside a [`FieldLayout`].
///
/// Zero-storage children (such as `Shape::Never` or an empty tuple/record) are
/// omitted; every `FieldLoc::Bits` sharing physical word `word` is yielded
/// together in a single [`FieldGroup::Packed`] even when zero-storage children
/// sit between them.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FieldGroup {
    /// A non-empty word-aligned child at field `index`, occupying `offset..offset + words`.
    Word { index: usize, offset: usize, words: usize },
    /// One packed `u64` word at `word` containing `(field_index, pos)` in field order.
    Packed { word: usize, fields: Box<[(usize, BitPos)]> },
}

/// Precomputed field layout of a heterogeneous product (`Record`, `Tuple`) or
/// fixed-domain `Fcn`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FieldLayout {
    pub locs: Box<[FieldLoc]>,
    pub words: usize,
    /// `(word_index, used_bitmask)` for every word containing at least one
    /// `FieldLoc::Bits` entry. Unused bits (`!used_bitmask`) in these words
    /// must be `0` in every valid encoding.
    pub bit_words: Box<[(usize, u64)]>,
    groups: Box<[FieldGroup]>,
}

impl FieldLayout {
    /// Compute the packed layout of a sequence of child shapes.
    pub fn of_shapes<'a>(shapes: impl IntoIterator<Item = &'a Shape>) -> Self {
        let mut locs = Vec::new();
        let mut bit_words: Vec<(usize, u64)> = Vec::new();
        let mut groups: Vec<FieldGroup> = Vec::new();
        let mut cur_packed: Vec<(usize, BitPos)> = Vec::new();
        let mut cur_word: usize = 0;
        let mut used_bits: u8 = 0;

        let flush_packed = |groups: &mut Vec<FieldGroup>, cur_packed: &mut Vec<(usize, BitPos)>, word: usize| {
            if !cur_packed.is_empty() {
                groups.push(FieldGroup::Packed { word, fields: std::mem::take(cur_packed).into_boxed_slice() });
            }
        };

        for (index, s) in shapes.into_iter().enumerate() {
            match scalar_bits(s) {
                Some(0) => {
                    locs.push(FieldLoc::Words(cur_word));
                }
                Some(b) => {
                    if used_bits + b > 64 {
                        flush_packed(&mut groups, &mut cur_packed, cur_word);
                        cur_word = cur_word.saturating_add(1);
                        used_bits = 0;
                    }
                    let shift = 64 - used_bits - b;
                    let pos = BitPos::new(cur_word, shift, b);
                    locs.push(FieldLoc::Bits(pos));
                    cur_packed.push((index, pos));
                    match bit_words.last_mut() {
                        Some((w, mask)) if *w == cur_word => *mask |= pos.shifted_mask(),
                        _ => bit_words.push((cur_word, pos.shifted_mask())),
                    }
                    used_bits += b;
                    if used_bits == 64 {
                        flush_packed(&mut groups, &mut cur_packed, cur_word);
                        cur_word = cur_word.saturating_add(1);
                        used_bits = 0;
                    }
                }
                None => {
                    let w = words(s);
                    if w == 0 {
                        locs.push(FieldLoc::Words(cur_word));
                    } else {
                        if used_bits > 0 {
                            flush_packed(&mut groups, &mut cur_packed, cur_word);
                            cur_word = cur_word.saturating_add(1);
                            used_bits = 0;
                        }
                        locs.push(FieldLoc::Words(cur_word));
                        groups.push(FieldGroup::Word { index, offset: cur_word, words: w });
                        cur_word = cur_word.saturating_add(w);
                    }
                }
            }
        }
        flush_packed(&mut groups, &mut cur_packed, cur_word);
        let total = cur_word.saturating_add(usize::from(used_bits > 0));
        FieldLayout {
            locs: locs.into_boxed_slice(),
            words: total,
            bit_words: bit_words.into_boxed_slice(),
            groups: groups.into_boxed_slice(),
        }
    }

    /// Occupied word-aligned groups in physical word order, skipping
    /// zero-storage children and yielding each packed word once.
    #[inline]
    pub fn word_groups(&self) -> &[FieldGroup] {
        &self.groups
    }

    /// Field layout of a `Record`, `Tuple` or `Fcn` shape.
    pub fn of_shape(s: &Shape) -> Option<Self> {
        match s {
            Shape::Record(fs) => Some(Self::of_shapes(fs.iter().map(|(_, f)| f))),
            Shape::Tuple(es) => Some(Self::of_shapes(es.iter())),
            Shape::Fcn { dom, range } => Some(Self::of_shapes(std::iter::repeat_n(range.as_ref(), dom.len()))),
            _ => None,
        }
    }
}

/// Slot layout of a homogeneous array (`Fcn`, `Map`, `Seq`, or indexed
/// homogeneous `Tuple` / `Record`).
///
/// Note: for `SlotLayout::Bits(b)`, element `i` sits at the exact same
/// `(word, shift)` as field `i` of `FieldLayout::of_shapes(repeat_n(elem, n))`
/// (`word = i / (64 / b)`, `shift = 64 - ((i % (64 / b)) + 1) * b`).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum SlotLayout {
    /// Word-aligned elements of `words` `u64`s each (`0` for `Never`).
    Words(usize),
    /// Sub-word elements of `bits` (`1..=63`) bits, packed MSB-first with
    /// `64 / bits` elements per `u64` word.
    Bits(u8),
}

impl SlotLayout {
    pub fn of(elem: &Shape) -> Self {
        match scalar_bits(elem) {
            Some(0) => SlotLayout::Words(0),
            Some(b) => SlotLayout::Bits(b),
            None => SlotLayout::Words(words(elem)),
        }
    }

    #[inline]
    pub const fn per_word(bits: u8) -> usize {
        64 / (bits as usize)
    }

    /// Total `u64` words required for `len` element slots.
    #[inline]
    pub const fn array_words(self, len: usize) -> usize {
        match self {
            SlotLayout::Words(w) => len.saturating_mul(w),
            SlotLayout::Bits(b) => {
                if len == 0 {
                    0
                } else {
                    len.div_ceil(Self::per_word(b))
                }
            }
        }
    }

    /// `(word_offset, bit_shift)` of 0-based element `i` for `Bits(bits)`.
    #[inline]
    pub const fn bit_pos(bits: u8, i: usize) -> (usize, u8) {
        let pw = Self::per_word(bits);
        let word = i / pw;
        let slot = i % pw;
        let shift = 64 - ((slot as u8 + 1) * bits);
        (word, shift)
    }

    /// Location of 0-based element `i` starting from `base_word`.
    #[inline]
    pub const fn loc(self, base_word: usize, i: usize) -> FieldLoc {
        match self {
            SlotLayout::Words(w) => FieldLoc::Words(base_word.saturating_add(i.saturating_mul(w))),
            SlotLayout::Bits(b) => {
                let (w, shift) = Self::bit_pos(b, i);
                FieldLoc::Bits(BitPos::new(base_word.saturating_add(w), shift, b))
            }
        }
    }

    #[inline]
    pub fn extract(bits: u8, words: &[u64], i: usize) -> u64 {
        let (w, shift) = Self::bit_pos(bits, i);
        extract_bits(words[w], shift, bits)
    }

    #[inline]
    pub fn insert(bits: u8, words: &mut [u64], i: usize, val: u64) {
        let (w, shift) = Self::bit_pos(bits, i);
        words[w] = insert_bits(words[w], shift, bits, val);
    }

    #[inline]
    pub fn set_zeroed(bits: u8, words: &mut [u64], i: usize, val: u64) {
        let (w, shift) = Self::bit_pos(bits, i);
        words[w] |= (val & bit_mask(bits)) << shift;
    }

    /// Bitmask of bits occupied in word `w` (`0..array_words(active_len)`) when
    /// `0..active_len` elements are active.
    #[inline]
    pub fn word_active_mask(bits: u8, active_len: usize, w: usize) -> u64 {
        let pw = Self::per_word(bits);
        let start = w * pw;
        if start >= active_len {
            return 0;
        }
        let count = (active_len - start).min(pw);
        let total_bits = count * (bits as usize);
        if total_bits == 64 {
            u64::MAX
        } else {
            ((1u64 << total_bits) - 1) << (64 - total_bits)
        }
    }
}
