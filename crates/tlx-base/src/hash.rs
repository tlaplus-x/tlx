//! In-memory hashing, stable finalizers, and insertion-ordered interning.

use std::borrow::Borrow;
use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasher, BuildHasherDefault, Hash, Hasher};

pub const INTEGER_MULTIPLIER: u64 = 0x9e37_79b9_7f4a_7c15;

/// The general-purpose in-memory hasher: `rustc-hash` 2 (deterministic, unseeded,
/// well distributed in the low bits that hashbrown uses). Its finishing rotation
/// fills bucket-index bits 26 and up from the key's low bits: pack a `u64` key
/// with its varying part in the low half (see `tlx-live`'s `sparse_key`).
/// Nothing persisted (fingerprints, checkpoints, cache keys) may depend on it;
/// those use `fmix64` and friends below.
pub use rustc_hash::FxHasher;
pub type FxBuildHasher = rustc_hash::FxBuildHasher;
pub type FxMap<K, V> = HashMap<K, V, FxBuildHasher>;
pub type FxSet<K> = HashSet<K, FxBuildHasher>;

/// One multiplication per integer key (addresses, symbols); measured fastest
/// for those, but poor on slices and strings, so only for single-word keys.
#[derive(Default)]
pub struct IntegerHasher(u64);

impl Hasher for IntegerHasher {
    #[inline]
    fn write(&mut self, bytes: &[u8]) {
        for chunk in bytes.chunks(8) {
            let mut word = [0u8; 8];
            word[..chunk.len()].copy_from_slice(chunk);
            self.write_u64(u64::from_le_bytes(word));
        }
    }
    #[inline]
    fn write_u64(&mut self, word: u64) {
        self.0 = (self.0.rotate_left(5) ^ word).wrapping_mul(INTEGER_MULTIPLIER);
    }
    #[inline]
    fn write_usize(&mut self, word: usize) {
        self.write_u64(word as u64);
    }
    #[inline]
    fn write_u32(&mut self, word: u32) {
        self.write_u64(word as u64);
    }
    #[inline]
    fn write_u8(&mut self, word: u8) {
        self.write_u64(word as u64);
    }
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }
}

pub type IntegerBuildHasher = BuildHasherDefault<IntegerHasher>;

#[derive(Default)]
pub struct IdHasher(u64);

impl Hasher for IdHasher {
    fn write(&mut self, _: &[u8]) {
        unreachable!("only u64 keys")
    }
    #[inline]
    fn write_u64(&mut self, word: u64) {
        self.0 = word;
    }
    #[inline]
    fn finish(&self) -> u64 {
        self.0
    }
}

pub type IdMap<V> = HashMap<u64, V, BuildHasherDefault<IdHasher>>;

#[inline]
pub fn mix64(value: u64) -> u64 {
    let value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    let value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

#[inline]
pub fn fmix64(value: u64) -> u64 {
    let value = (value ^ (value >> 33)).wrapping_mul(0xff51_afd7_ed55_8ccd);
    let value = (value ^ (value >> 33)).wrapping_mul(0xc4ce_b9fe_1a85_ec53);
    value ^ (value >> 33)
}

/// A two-lane folded-multiply word stream over 64-bit words: `a` and `b` fold
/// each word in with two different multiplicities (and `b` with the word
/// rotated), `n` counts the words, and `finish` folds both lanes and `n`
/// through `fmix64`. Deterministic across platforms and toolchains, like
/// `StableHasher`; the value fingerprints and the framing checksums are
/// persisted, so its algorithm must never change.
///
/// The fold multiplicities are the standard SplitMix64/xxHash mix constants
/// (`FOLD_K1` is the golden-ratio increment that `INTEGER_MULTIPLIER` also
/// names).
#[derive(Clone)]
pub struct FoldHasher {
    a: u64,
    b: u64,
    n: u64,
}

impl FoldHasher {
    pub fn new() -> FoldHasher {
        FoldHasher { a: 0x243f_6a88_85a3_08d3, b: 0x1319_8a2e_0370_7344, n: 0 }
    }

    /// Fold the next word of the stream in.
    #[inline]
    pub fn word(&mut self, word: u64) {
        self.a = fold_mul(self.a ^ word, FOLD_K1);
        self.b = fold_mul(self.b ^ word.rotate_left(32), FOLD_K2);
        self.n = self.n.wrapping_add(1);
    }

    /// Finalize the stream. Feeding no word gives `finish()` of one word `0`.
    pub fn finish(&self) -> u64 {
        fmix64(fold_mul(self.a ^ FOLD_K3, self.b ^ FOLD_K4) ^ self.n)
    }
}

impl Default for FoldHasher {
    fn default() -> Self {
        Self::new()
    }
}

/// Fold two 64-bit values into one (`a * b`, both halves of the 128-bit
/// product xored): the mix step of `FoldHasher`.
#[inline]
fn fold_mul(a: u64, b: u64) -> u64 {
    let r = (a as u128).wrapping_mul(b as u128);
    (r as u64) ^ ((r >> 64) as u64)
}

const FOLD_K1: u64 = 0x9e37_79b9_7f4a_7c15;
const FOLD_K2: u64 = 0xc2b2_ae3d_27d4_eb4f;
const FOLD_K3: u64 = 0x1656_67b1_9e37_79f9;
const FOLD_K4: u64 = 0x85eb_ca77_c2b2_ae63;

/// Deterministic 64-bit hash of a byte string: its length, then the bytes in
/// little-endian 64-bit words (a final short word is zero-padded) through
/// `FoldHasher`. Used for interned text and for the framing checksums; both
/// are persisted, so the result of a given input must never change.
pub fn hash_bytes(bytes: &[u8]) -> u64 {
    let mut fp = FoldHasher::new();
    fp.word(bytes.len() as u64);
    let mut chunks = bytes.chunks_exact(8);
    for c in &mut chunks {
        fp.word(u64::from_le_bytes(c.try_into().unwrap()));
    }
    let rem = chunks.remainder();
    if !rem.is_empty() {
        let mut buf = [0u8; 8];
        buf[..rem.len()].copy_from_slice(rem);
        fp.word(u64::from_le_bytes(buf));
    }
    fp.finish()
}

/// A hasher whose results never change (across platforms, toolchains,
/// dependency versions): for hashes that are persisted or written into
/// generated code (cache keys), unlike `FxHasher` and std's
/// `DefaultHasher`. Integers are fed little-endian; the bytes are taken in
/// words of 8, each mixed in by `fmix64` (not fast; for keys, not tables).
#[derive(Clone)]
pub struct StableHasher {
    state: u64,
    /// Bytes not yet mixed in (the low `tail_len` bytes, little-endian).
    tail: u64,
    tail_len: u32,
    len: u64,
}

impl StableHasher {
    pub fn new() -> StableHasher {
        StableHasher::with_seed(0)
    }

    fn with_seed(seed: u64) -> StableHasher {
        StableHasher { state: fmix64(seed ^ INTEGER_MULTIPLIER), tail: 0, tail_len: 0, len: 0 }
    }

    #[inline]
    fn word(&mut self, word: u64) {
        self.state = fmix64(self.state.rotate_left(23) ^ word);
    }
}

impl Default for StableHasher {
    fn default() -> StableHasher {
        StableHasher::new()
    }
}

impl Hasher for StableHasher {
    fn write(&mut self, bytes: &[u8]) {
        self.len = self.len.wrapping_add(bytes.len() as u64);
        for &b in bytes {
            self.tail |= (b as u64) << (8 * self.tail_len);
            self.tail_len += 1;
            if self.tail_len == 8 {
                let word = self.tail;
                self.word(word);
                (self.tail, self.tail_len) = (0, 0);
            }
        }
    }
    fn write_u8(&mut self, x: u8) {
        self.write(&[x]);
    }
    fn write_u16(&mut self, x: u16) {
        self.write(&x.to_le_bytes());
    }
    fn write_u32(&mut self, x: u32) {
        self.write(&x.to_le_bytes());
    }
    fn write_u64(&mut self, x: u64) {
        self.write(&x.to_le_bytes());
    }
    fn write_u128(&mut self, x: u128) {
        self.write(&x.to_le_bytes());
    }
    fn write_usize(&mut self, x: usize) {
        self.write_u64(x as u64);
    }
    fn write_i8(&mut self, x: i8) {
        self.write_u8(x as u8);
    }
    fn write_i16(&mut self, x: i16) {
        self.write_u16(x as u16);
    }
    fn write_i32(&mut self, x: i32) {
        self.write_u32(x as u32);
    }
    fn write_i64(&mut self, x: i64) {
        self.write_u64(x as u64);
    }
    fn write_i128(&mut self, x: i128) {
        self.write_u128(x as u128);
    }
    fn write_isize(&mut self, x: isize) {
        self.write_u64(x as i64 as u64);
    }
    fn finish(&self) -> u64 {
        let mut h = self.clone();
        if h.tail_len > 0 {
            let word = h.tail;
            h.word(word);
        }
        fmix64(h.state ^ h.len)
    }
}

pub struct Interner<K, V = K, S = FxBuildHasher> {
    ids: HashMap<K, u32, S>,
    values: Vec<V>,
}

impl<K, V, S: Default> Default for Interner<K, V, S> {
    fn default() -> Self {
        Self { ids: HashMap::with_hasher(S::default()), values: Vec::new() }
    }
}

impl<K: Eq + Hash, V, S: BuildHasher> Interner<K, V, S> {
    #[inline]
    pub fn intern_with<Q: Eq + Hash + ?Sized>(&mut self, key: &Q, make: impl FnOnce() -> (K, V)) -> u32
    where
        K: Borrow<Q>,
    {
        if let Some(&id) = self.ids.get(key) {
            return id;
        }
        let (key, value) = make();
        self.insert(key, value)
    }

    #[inline]
    fn insert(&mut self, key: K, value: V) -> u32 {
        let id = self.values.len() as u32;
        self.values.push(value);
        self.ids.insert(key, id);
        id
    }
}

impl<K: Eq + Hash + Clone, S: BuildHasher> Interner<K, K, S> {
    #[inline]
    pub fn intern(&mut self, value: K) -> u32 {
        if let Some(&id) = self.ids.get(&value) {
            return id;
        }
        self.insert(value.clone(), value)
    }
}

impl<K, V, S> Interner<K, V, S> {
    pub fn into_values(self) -> Vec<V> {
        self.values
    }
    pub fn capacity(&self) -> usize {
        self.values.capacity()
    }
    pub fn map_capacity(&self) -> usize {
        self.ids.capacity()
    }
}

impl<K, V, S> std::ops::Deref for Interner<K, V, S> {
    type Target = [V];
    fn deref(&self) -> &[V] {
        &self.values
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn integer_and_identity_keys_keep_their_hashes() {
        for value in [0, 1, 127, u32::MAX as u64, u64::MAX] {
            let mut address = IntegerHasher::default();
            address.write_usize(value as usize);
            assert_eq!(address.finish(), (value as usize as u64).wrapping_mul(INTEGER_MULTIPLIER));
            let mut symbol = IntegerHasher::default();
            symbol.write_u32(value as u32);
            assert_eq!(symbol.finish(), (value as u32 as u64).wrapping_mul(INTEGER_MULTIPLIER));
            let mut identity = IdHasher::default();
            identity.write_u64(value);
            assert_eq!(identity.finish(), value);
        }
    }

    #[test]
    fn finalizer_vectors() {
        assert_eq!(mix64(0), 0);
        assert_eq!(mix64(1), 0x5692161d100b05e5);
        assert_eq!(mix64(u64::MAX), 0xb4d055fcf2cbbd7b);
        assert_eq!(fmix64(0), 0);
        assert_eq!(fmix64(1), 0xb456bcfc34c2cb2c);
        assert_eq!(fmix64(u64::MAX), 0x64b5720b4b825f21);
    }

    #[test]
    fn fold_hash_byte_vectors() {
        // Fixed fixtures: `hash_bytes` feeds interned text and the framing
        // checksums, both persisted, so a changed value must fail here.
        assert_eq!(hash_bytes(b""), 0x0c0d_7c8f_d5fd_d2f9);
        assert_eq!(hash_bytes(b"hello, frame"), 0xab17_6d96_c362_3862);
        assert_eq!(hash_bytes(b"123456789"), 0xed81_353e_de5e_a192);
        // The length is part of the stream, and a short tail word is padded.
        assert_ne!(hash_bytes(b"12345678"), hash_bytes(b"12345678\0"));
    }

    #[test]
    fn stable_hasher_vectors() {
        let hash = |bytes: &[u8]| {
            let mut h = StableHasher::new();
            h.write(bytes);
            h.finish()
        };
        // (Persisted: these values must never change.)
        assert_eq!(hash(b""), 0x6393_d51c_06c6_18dc);
        assert_eq!(hash(b"abc"), 0x6626_6ffc_a8e2_ba34);
        assert_eq!(hash(b"0123456789abcdef!"), 0xcf28_448d_3155_dacb);
        // Integers are their little-endian bytes, however they are split.
        let mut a = StableHasher::new();
        a.write_u32(0x0403_0201);
        a.write_u64(0x0c0b_0a09_0807_0605);
        a.write_isize(-1);
        let mut b = StableHasher::new();
        b.write(&[1, 2, 3, 4, 5, 6]);
        b.write(&[7, 8, 9, 10, 11, 12]);
        b.write(&[0xff; 8]);
        assert_eq!(a.finish(), b.finish());
        assert_ne!(hash(b"ab"), hash(b"ab\0"));
        assert_ne!(StableHasher::with_seed(1).finish(), StableHasher::new().finish());
    }

    #[test]
    fn intern_ids_follow_insertion_not_hash_order() {
        let mut values = Interner::<String>::default();
        assert_eq!(values.intern("second".into()), 0);
        assert_eq!(values.intern("first".into()), 1);
        assert_eq!(values.intern("second".into()), 0);
        assert_eq!(&*values, &["second", "first"]);
        let mut patterns = Interner::<Box<[u64]>, usize>::default();
        assert_eq!(patterns.intern_with(&[7u64][..], || (vec![7].into(), 9)), 0);
        assert_eq!(patterns.intern_with(&[7u64][..], || panic!("must not allocate on a hit")), 0);
        assert_eq!(patterns.into_values(), vec![9]);
    }
}

mod fpmap;
pub use fpmap::FpMap;
