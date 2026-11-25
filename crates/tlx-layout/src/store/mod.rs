//! The run-owned value store of the compiled tier's `Ref` slots
//! (docs/value-store.md §1): behind `TLX_VALUE_STORE`, the slots whose
//! speculated shape has a `Dyn` part (the driver's `enc::driver` turns the
//! store off when `TLX_ESCAPE` replaces its layout).
//!
//! A *handle* (`u64`, the word of a `Ref` slot) is either an immediate
//! scalar (strings and model values by `Sym` id, Booleans, integers of at
//! most 61 bits: the same encodings as `dynval`) or a reference to an
//! immutable node of one `Store`. A node keeps the exact representation of
//! a finite value: its kind and, for functions, how TLC built it (tuple,
//! record, function over an enumerated domain or over an interval; the
//! *witness*, `tlx_value::plan::Witness`), with its children as handles.
//! Thawing a node gives back exactly the value that was frozen.
//!
//! Two identities:
//! - interning is by the exact representation (kind, witness and child
//!   handles): equal handles mean the same representation; equal values
//!   with different witnesses (`<<1, 2>>` and `[i \in {1, 2} |-> i]`) get
//!   different handles;
//! - every node caches a 64-bit *semantic digest* computed from its
//!   children's digests, the same for all values TLC considers equal (the
//!   tuple / record / function aliases of `tlx_value::Value`'s equality),
//!   and independent of handle numbers, allocation order and threads. State
//!   fingerprints use digests instead of handles. A digest is a filter:
//!   equality is decided structurally (thaw and compare).
//!
//! Nodes are published once and never change or move; readers take no lock
//! (a page table of `OnceLock`s). Interning takes a short lock of one of
//! `SHARDS` index shards. A store belongs to one run; its handles carry the
//! store's id, so a handle of another store is rejected by the checked
//! lookups. There is no reclamation yet: the store is bounded by a byte
//! budget, and exceeding it is a run error (`Full`).

#![forbid(unsafe_code)]

mod ops;
mod order;
mod ser;

#[cfg(test)]
mod tests;

pub use self::ops::{witness, Absent, RefOpError};
pub use self::order::{cmp_tlc, eq_tlc};

use std::collections::HashMap;
use std::hash::BuildHasherDefault;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

use tlx_base::hash::{fmix64, IdHasher};
use tlx_value::{FcnDom, Sym, Value};

/// The immediate scalar schema (tags, mask, payload, integer range, encode
/// and checked decode) lives in `crate::scalar`, its one owner; `store`
/// re-exports it so this store, the `dynval` interner and the C/JIT
/// backends that inline the scalar operations all derive from the same
/// constants (ARCH-07). Only the node format below is this store's own.
pub use crate::scalar::{
    as_bool, as_int, bool_handle, immediate, int_handle, is_immediate, str_handle, tag, TAG_BITS, TAG_BOOL, TAG_INT, TAG_MASK,
    TAG_MODEL_VALUE, TAG_STR,
};

/// The tag of a node handle: this store's own composite format, with the
/// store id and the node index above the tag (`STORE_BITS`), separate from
/// the immediate scalar schema (and from `dynval`'s table tag).
pub(crate) const TAG_NODE: u64 = 5;
/// Bits of a node handle holding the store id (above the tag).
const STORE_BITS: u32 = 16;
const INDEX_SHIFT: u32 = TAG_BITS + STORE_BITS;

/// Nodes per page, and pages.
const PAGE_BITS: u32 = 14;
const PAGE: usize = 1 << PAGE_BITS;
const PAGES: usize = 1 << 16;

const SHARD_BITS: u32 = 6;
const SHARDS: usize = 1 << SHARD_BITS;

/// Checked symbol decoding. A cached `Sym` is a publication proof: only
/// `try_from_id` populates it, and published entries live for the process.
/// The full payload is checked before indexing, so wide ids cannot alias.
fn symbol(h: u64) -> Option<Sym> {
    if !matches!(tag(h), TAG_STR | TAG_MODEL_VALUE) {
        return None;
    }
    let id = u32::try_from(h >> TAG_BITS).ok()?;
    SYMBOLS.with(|c| {
        let mut c = c.borrow_mut();
        let slot = id as usize & (c.len() - 1);
        if let Some(s) = c[slot].filter(|s| s.id() == id) {
            return Some(s);
        }
        let s = Sym::try_from_id(id)?;
        c[slot] = Some(s);
        Some(s)
    })
}

thread_local! {
    static SYMBOLS: std::cell::RefCell<[Option<Sym>; 1024]> = const { std::cell::RefCell::new([None; 1024]) };
}

/// The checked scalar value of an arbitrary immediate word (`None`: a
/// node handle, an invalid tag, or an unpublished symbol). The tag and
/// payload checks are the shared schema's (`crate::scalar`); only the
/// symbol publication check (`symbol`) is this store's.
fn immediate_value(h: u64) -> Option<Value> {
    crate::scalar::scalar_value(h, symbol)
}

/// The payload of a node: a finite value's exact representation.
#[derive(Debug, PartialEq, Eq)]
pub enum Body {
    /// An integer outside the immediate range.
    Int(i64),
    /// A set: its elements in TLC's normalized order (sorted, distinct).
    Set(Box<[u64]>),
    /// `lo..hi`, kept as an interval (`Value::Interval`).
    Interval(i64, i64),
    /// A function with domain `1..n` built as a tuple (`Value::Tuple`).
    Tuple(Box<[u64]>),
    /// A record (`Value::Record`): fields sorted by `Sym` order.
    Record(Box<[(Sym, u64)]>),
    /// Any other function (`Value::Fcn`): the keys (sorted in TLC order)
    /// then the values, and how keys are looked up.
    Fcn(Box<[u64]>, FcnDom),
}

impl Body {
    fn kind_tag(&self) -> u64 {
        match self {
            Body::Int(_) => 1,
            Body::Set(_) => 2,
            Body::Interval(..) => 3,
            Body::Tuple(_) => 4,
            Body::Record(_) => 5,
            Body::Fcn(_, FcnDom::Enumerated) => 6,
            Body::Fcn(_, FcnDom::Interval) => 7,
        }
    }

    /// Payload bytes (for the budget).
    fn bytes(&self) -> usize {
        match self {
            Body::Int(_) | Body::Interval(..) => 0,
            Body::Set(es) | Body::Tuple(es) | Body::Fcn(es, _) => es.len() * 8,
            Body::Record(fs) => fs.len() * std::mem::size_of::<(Sym, u64)>(),
        }
    }
}

/// An immutable published node.
#[derive(Debug)]
pub struct Node {
    /// The semantic digest (see the module comment).
    pub digest: u64,
    pub body: Body,
    /// `DOMAIN` of a function node, computed on first use.
    domain: OnceLock<u64>,
    /// The elements of an interval node as handles, for iteration.
    elems: OnceLock<Box<[u64]>>,
}

impl Node {
    /// The (key, value) pairs of a function node by index.
    pub fn fcn_len(&self) -> usize {
        match &self.body {
            Body::Tuple(vs) => vs.len(),
            Body::Record(fs) => fs.len(),
            Body::Fcn(kv, _) => kv.len() / 2,
            _ => 0,
        }
    }
}

/// Why a value could not be stored.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum StoreError {
    /// A raw child word is not a published handle of this store.
    InvalidHandle(u64),
    /// The store's byte budget is exhausted.
    Full,
    /// The value is not a finite value TLC can store in a state (an
    /// infinite or non-enumerable set), with the evaluation error.
    NotFinite(String),
}

/// Indices (into the node table) of the nodes with one exact hash.
enum Ids {
    One(u32),
    Many(Vec<u32>),
}

#[repr(align(128))]
#[derive(Default)]
struct Shard(Mutex<HashMap<u64, Ids, BuildHasherDefault<IdHasher>>>);

/// Statistics of a store.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct StoreStats {
    pub nodes: u64,
    /// Bytes of nodes and their payloads.
    pub node_bytes: u64,
    /// Estimated bytes of the intern index.
    pub index_bytes: u64,
    pub budget: u64,
}

/// A run-owned store of immutable value nodes (see the module comment).
pub struct Store {
    /// Unique in the process (never reused); `id` is its low 16 bits, in
    /// the handles.
    uid: u64,
    id: u64,
    pages: Box<[OnceLock<Box<[OnceLock<Node>]>>]>,
    next: AtomicU64,
    shards: Box<[Shard]>,
    bytes: AtomicUsize,
    index_bytes: AtomicUsize,
    budget: usize,
    full: AtomicBool,
}

static NEXT_UID: AtomicU64 = AtomicU64::new(1);

fn allocate_uid(next: &AtomicU64) -> u64 {
    // Never reuse the store-id bits: old handles can outlive their store.
    next.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |n| (n < 1 << STORE_BITS).then_some(n + 1)).expect("value store ids exhausted")
}

impl std::fmt::Debug for Store {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Store#{}", self.uid)
    }
}

impl Store {
    /// A new, empty store holding at most `budget` bytes of nodes.
    ///
    /// # Panics
    /// After 65535 stores have been created in this process: the handle's
    /// store-id field must never wrap and accept another store's handles.
    pub fn new(budget: usize) -> Arc<Store> {
        let uid = allocate_uid(&NEXT_UID);
        Arc::new(Store {
            uid,
            id: uid & ((1 << STORE_BITS) - 1),
            pages: (0..PAGES).map(|_| OnceLock::new()).collect(),
            next: AtomicU64::new(0),
            shards: (0..SHARDS).map(|_| Shard::default()).collect(),
            bytes: AtomicUsize::new(0),
            index_bytes: AtomicUsize::new(0),
            budget,
            full: AtomicBool::new(false),
        })
    }

    /// The process-unique id of this store.
    pub fn uid(&self) -> u64 {
        self.uid
    }

    /// Whether an insertion was refused because the budget was exhausted.
    pub fn is_full(&self) -> bool {
        self.full.load(Ordering::Relaxed)
    }

    pub fn budget(&self) -> usize {
        self.budget
    }

    pub fn stats(&self) -> StoreStats {
        StoreStats {
            nodes: self.next.load(Ordering::Relaxed),
            node_bytes: self.bytes.load(Ordering::Relaxed) as u64,
            index_bytes: self.index_bytes.load(Ordering::Relaxed) as u64,
            budget: self.budget as u64,
        }
    }

    fn handle_of(&self, index: u64) -> u64 {
        (index + 1) << INDEX_SHIFT | self.id << TAG_BITS | TAG_NODE
    }

    /// The node of a handle of this store (None: an immediate, a handle of
    /// another store, or no such node).
    #[inline]
    pub fn node(&self, h: u64) -> Option<&Node> {
        if tag(h) != TAG_NODE || (h >> TAG_BITS) & ((1 << STORE_BITS) - 1) != self.id {
            return None;
        }
        let i = (h >> INDEX_SHIFT).checked_sub(1)? as usize;
        self.pages.get(i >> PAGE_BITS)?.get()?.get(i & (PAGE - 1))?.get()
    }

    /// The node of a handle this store produced (panics otherwise: a
    /// compiler defect).
    #[inline]
    pub(crate) fn get(&self, h: u64) -> &Node {
        self.node(h).unwrap_or_else(|| panic!("value store {}: invalid handle {h:#x}", self.uid))
    }

    /// Whether `h` is a valid handle of this store (an immediate with a
    /// published symbol, or a node of this store).
    pub fn is_valid(&self, h: u64) -> bool {
        match tag(h) {
            TAG_NODE => self.node(h).is_some(),
            _ => immediate_value(h).is_some(),
        }
    }

    /// The semantic digest of a handle.
    #[inline]
    pub fn digest(&self, h: u64) -> u64 {
        self.assert_valid(h);
        if is_immediate(h) {
            return scalar_digest(h);
        }
        self.get(h).digest
    }

    fn assert_valid(&self, h: u64) {
        assert!(self.is_valid(h), "value store {}: invalid handle {h:#x}", self.uid);
    }

    /// Store a finite value (lazy values are normalized first, as states
    /// store them).
    pub fn freeze(&self, v: &Value) -> Result<u64, StoreError> {
        if let Some(h) = immediate(v) {
            return Ok(h);
        }
        let body = match v {
            Value::Int(i) => Body::Int(*i),
            Value::Set(es) => Body::Set(es.iter().map(|e| self.freeze(e)).collect::<Result<_, _>>()?),
            Value::Interval(lo, hi) => Body::Interval(*lo, *hi),
            Value::Tuple(es) => Body::Tuple(es.iter().map(|e| self.freeze(e)).collect::<Result<_, _>>()?),
            Value::Record(fs) => Body::Record(fs.iter().map(|(k, e)| Ok((*k, self.freeze(e)?))).collect::<Result<_, StoreError>>()?),
            Value::Fcn(ps, dom) => {
                let mut kv = Vec::with_capacity(ps.len() * 2);
                for (k, _) in ps.iter() {
                    kv.push(self.freeze(k)?);
                }
                for (_, x) in ps.iter() {
                    kv.push(self.freeze(x)?);
                }
                Body::Fcn(kv.into(), *dom)
            }
            Value::LazySet(_) | Value::LazyFcn(_) => {
                let n = v.normalize().map_err(|e| StoreError::NotFinite(e.to_string()))?;
                if !n.is_normal() {
                    return Err(StoreError::NotFinite(format!("{v}")));
                }
                return self.freeze(&n);
            }
            Value::Bool(_) | Value::Str(_) | Value::ModelValue(_) => unreachable!("immediate"),
        };
        self.intern(body)
    }

    /// The value of a slot word: `thaw`, except that word 0 (an unassigned
    /// slot of a state being built, never a handle) is `FALSE`, as zero
    /// words decode as some value of every fixed encoding: nothing reads
    /// an unassigned slot.
    ///
    /// Slot values have a cache of their own (`ROOTS`): the thawing of
    /// their children does not evict them, so states that share a slot's
    /// value share one `Value` as with the `Dyn` interner (consumers such
    /// as the symmetry reduction's caches key on the value's identity).
    pub fn thaw_slot(&self, h: u64) -> Value {
        if h == 0 {
            return Value::Bool(false);
        }
        if is_immediate(h) {
            return immediate_value(h).expect("invalid immediate handle");
        }
        self.assert_valid(h);
        let slot = (fmix64(h ^ self.uid.rotate_left(29)) as usize) & (ROOT_SLOTS - 1);
        let hit = ROOTS.with(|c| match &c.borrow()[slot] {
            Some((u, k, v)) if *u == self.uid && *k == h => Some(v.clone()),
            _ => None,
        });
        if let Some(v) = hit {
            return v;
        }
        let v = thaw_cached(self, h);
        ROOTS.with(|c| c.borrow_mut()[slot] = Some((self.uid, h, v.clone())));
        v
    }

    /// The value of a handle of this store: exactly the value frozen.
    pub fn thaw(&self, h: u64) -> Value {
        if is_immediate(h) {
            return immediate_value(h).expect("invalid immediate handle");
        }
        self.assert_valid(h);
        thaw_cached(self, h)
    }

    fn thaw_node(&self, h: u64) -> Value {
        match &self.get(h).body {
            Body::Int(i) => Value::Int(*i),
            Body::Set(es) => Value::Set(es.iter().map(|e| self.thaw(*e)).collect()),
            Body::Interval(lo, hi) => Value::Interval(*lo, *hi),
            Body::Tuple(es) => Value::Tuple(es.iter().map(|e| self.thaw(*e)).collect()),
            Body::Record(fs) => Value::Record(fs.iter().map(|(k, e)| (*k, self.thaw(*e))).collect()),
            Body::Fcn(kv, dom) => {
                let n = kv.len() / 2;
                Value::Fcn((0..n).map(|i| (self.thaw(kv[i]), self.thaw(kv[n + i]))).collect(), *dom)
            }
        }
    }

    /// The value of an arbitrary word (None: not a valid handle of this
    /// store). For words from outside the compiled code.
    pub fn try_thaw(&self, h: u64) -> Option<Value> {
        match tag(h) {
            TAG_NODE => self.node(h).map(|_| self.thaw(h)),
            _ => immediate_value(h),
        }
    }

    /// Intern a node body (its children are handles of this store).
    pub(crate) fn intern(&self, body: Body) -> Result<u64, StoreError> {
        // Publication is the trust boundary for recursive readers. No
        // public constructor may hide an unchecked word inside a node.
        let check = |h: &u64| if self.is_valid(*h) { Ok(()) } else { Err(StoreError::InvalidHandle(*h)) };
        match &body {
            Body::Set(es) | Body::Tuple(es) | Body::Fcn(es, _) => es.iter().try_for_each(check)?,
            Body::Record(fs) => fs.iter().map(|(_, h)| h).try_for_each(check)?,
            Body::Int(_) | Body::Interval(..) => {}
        }
        let exact = exact_hash(&body);
        let shard = &self.shards[(exact >> (64 - SHARD_BITS)) as usize];
        if let Some(h) = self.find(shard, exact, &body) {
            return Ok(h);
        }
        // (Outside the lock: the digest reads only published children.)
        let digest = self.body_digest(&body);
        let mut index = shard.0.lock().unwrap_or_else(|e| e.into_inner());
        let candidates = |index: &HashMap<u64, Ids, _>| -> Option<u64> {
            let ids: &[u32] = match index.get(&exact)? {
                Ids::One(i) => std::slice::from_ref(i),
                Ids::Many(is) => is,
            };
            ids.iter().map(|&i| self.handle_of(i as u64)).find(|&h| self.get(h).body == body)
        };
        if let Some(h) = candidates(&index) {
            return Ok(h);
        }
        let size = std::mem::size_of::<OnceLock<Node>>() + body.bytes();
        if self.bytes.load(Ordering::Relaxed) + size > self.budget {
            self.full.store(true, Ordering::Relaxed);
            return Err(StoreError::Full);
        }
        let i = self.next.fetch_add(1, Ordering::Relaxed);
        let (p, s) = ((i as usize) >> PAGE_BITS, (i as usize) & (PAGE - 1));
        let Some(slot) = self.pages.get(p) else {
            self.full.store(true, Ordering::Relaxed);
            return Err(StoreError::Full);
        };
        let page = slot.get_or_init(|| (0..PAGE).map(|_| OnceLock::new()).collect());
        let node = Node { digest, body, domain: OnceLock::new(), elems: OnceLock::new() };
        assert!(page[s].set(node).is_ok(), "value store: node slot {i} written twice");
        let i32 = u32::try_from(i).expect("value store index");
        match index.get_mut(&exact) {
            None => {
                index.insert(exact, Ids::One(i32));
                self.index_bytes.fetch_add(24, Ordering::Relaxed);
            }
            Some(Ids::Many(is)) => is.push(i32),
            Some(ids @ Ids::One(_)) => {
                let Ids::One(j) = *ids else { unreachable!() };
                *ids = Ids::Many(vec![j, i32]);
            }
        }
        self.bytes.fetch_add(size, Ordering::Relaxed);
        Ok(self.handle_of(i))
    }

    fn find(&self, shard: &Shard, exact: u64, body: &Body) -> Option<u64> {
        let index = shard.0.lock().unwrap_or_else(|e| e.into_inner());
        let ids: &[u32] = match index.get(&exact)? {
            Ids::One(i) => std::slice::from_ref(i),
            Ids::Many(is) => is,
        };
        ids.iter().map(|&i| self.handle_of(i as u64)).find(|&h| self.get(h).body == *body)
    }

    /// The semantic digest of a body (see `digest_of_value` for the
    /// algebra; both must agree).
    fn body_digest(&self, body: &Body) -> u64 {
        let mut d = Digest::new();
        match body {
            Body::Int(i) => return int_digest(*i),
            Body::Set(es) => {
                d.word(D_SET);
                d.word(es.len() as u64);
                es.iter().for_each(|e| d.word(self.digest(*e)));
            }
            Body::Interval(lo, hi) => {
                let n = if hi < lo { 0 } else { (hi - lo + 1) as u64 };
                d.word(D_SET);
                d.word(n);
                for i in 0..n as i64 {
                    d.word(int_digest(lo + i));
                }
            }
            Body::Tuple(es) => {
                d.word(D_TUPLE);
                d.word(es.len() as u64);
                es.iter().for_each(|e| d.word(self.digest(*e)));
            }
            Body::Record(fs) => {
                d.word(D_RECORD);
                d.word(fs.len() as u64);
                for (k, e) in fs.iter() {
                    d.word(k.text_hash());
                    d.word(self.digest(*e));
                }
            }
            Body::Fcn(kv, _) => {
                let n = kv.len() / 2;
                let (keys, vals) = kv.split_at(n);
                match fcn_alias(keys) {
                    Alias::Tuple => {
                        d.word(D_TUPLE);
                        d.word(n as u64);
                        vals.iter().for_each(|e| d.word(self.digest(*e)));
                    }
                    Alias::Record => {
                        d.word(D_RECORD);
                        d.word(n as u64);
                        for (k, e) in keys.iter().zip(vals) {
                            let s = symbol(*k).expect("invalid string key");
                            d.word(s.text_hash());
                            d.word(self.digest(*e));
                        }
                    }
                    Alias::Fcn => {
                        d.word(D_FCN);
                        d.word(n as u64);
                        for (k, e) in keys.iter().zip(vals) {
                            d.word(self.digest(*k));
                            d.word(self.digest(*e));
                        }
                    }
                }
            }
        }
        d.finish()
    }

    /// Test-only seam (`store/tests.rs`): whether two handles denote equal
    /// values (`Value`'s equality: the aliases are equal). Digests decide
    /// unequal values; equal digests are checked structurally. Production
    /// code compares thawed values directly, so this is not exported.
    #[cfg(test)]
    pub fn same_value(&self, a: u64, b: u64) -> bool {
        self.assert_valid(a);
        self.assert_valid(b);
        a == b || (self.digest(a) == self.digest(b) && self.thaw(a) == self.thaw(b))
    }

    /// `DOMAIN` of a function node, cached on the node.
    pub(crate) fn cached_domain(&self, f: u64, make: impl FnOnce() -> Result<u64, StoreError>) -> Result<u64, StoreError> {
        let node = self.get(f);
        if let Some(d) = node.domain.get() {
            return Ok(*d);
        }
        let d = make()?;
        Ok(*node.domain.get_or_init(|| d))
    }

    /// The elements of a set handle as handles, in normalized order (an
    /// interval's are materialized once). None: not a set node, or a non-empty
    /// interval whose endpoints do not fit immediate integer handles.
    pub fn set_elems(&self, s: u64) -> Option<&[u64]> {
        let node = self.node(s)?;
        match &node.body {
            Body::Set(es) => Some(es),
            Body::Interval(lo, hi) => {
                if hi < lo {
                    return Some(&[]);
                }
                if int_handle(*lo).is_none() || int_handle(*hi).is_none() {
                    return None;
                }
                Some(node.elems.get_or_init(|| (*lo..=*hi).map(|i| int_handle(i).expect("interval of immediate integers")).collect()))
            }
            _ => None,
        }
    }
}

/// The value semantics of a stored function's keys: equal to a tuple (keys
/// `1..n`, also the empty function), to a record (string keys), or neither
/// (`tlx_value::FcnKind`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Alias {
    Tuple,
    Record,
    Fcn,
}

/// `FcnKind::of` on the sorted keys of a stored function.
pub(crate) fn fcn_alias(keys: &[u64]) -> Alias {
    match (keys.first(), keys.last()) {
        (None, _) => Alias::Tuple,
        (Some(f), Some(l)) if as_int(*f) == Some(1) && as_int(*l) == Some(keys.len() as i64) => Alias::Tuple,
        (Some(f), _) if tag(*f) == TAG_STR => Alias::Record,
        _ => Alias::Fcn,
    }
}

// ---- semantic digests ----

const D_BOOL: u64 = 0x9c3a_5f1e_29d4_b701;
const D_INT: u64 = 0x2f6b_92c4_e85a_3d17;
const D_STR: u64 = 0x6d29_e7a1_43bc_f80b;
const D_MV: u64 = 0xb476_1d3e_9f02_c5b9;
const D_SET: u64 = 0x4e98_c06b_7d51_a24f;
const D_TUPLE: u64 = 0xe1c5_4a87_0e3f_96b3;
const D_RECORD: u64 = 0x7a0f_b39d_c218_e475;
const D_FCN: u64 = 0x025e_7c80_b46a_1d99;

/// A two-lane folded-multiply stream hash (like `tlx_value::fingerprint`).
struct Digest {
    a: u64,
    b: u64,
    n: u64,
}

const K1: u64 = 0x9e37_79b9_7f4a_7c15;
const K2: u64 = 0xc2b2_ae3d_27d4_eb4f;

#[inline(always)]
fn fold_mul(a: u64, b: u64) -> u64 {
    let r = (a as u128).wrapping_mul(b as u128);
    (r as u64) ^ ((r >> 64) as u64)
}

impl Digest {
    fn new() -> Digest {
        Digest { a: 0x243f_6a88_85a3_08d3, b: 0x1319_8a2e_0370_7344, n: 0 }
    }
    #[inline(always)]
    fn word(&mut self, w: u64) {
        self.a = fold_mul(self.a ^ w, K1);
        self.b = fold_mul(self.b ^ w.rotate_left(32), K2);
        self.n = self.n.wrapping_add(1);
    }
    fn finish(&self) -> u64 {
        fmix64(fold_mul(self.a ^ 0x1656_67b1_9e37_79f9, self.b ^ 0x85eb_ca77_c2b2_ae63) ^ self.n)
    }
}

fn int_digest(i: i64) -> u64 {
    let mut d = Digest::new();
    d.word(D_INT);
    d.word(i as u64);
    d.finish()
}

/// The digest of an immediate handle.
fn scalar_digest(h: u64) -> u64 {
    let mut d = Digest::new();
    match tag(h) {
        TAG_INT => return int_digest(as_int(h).expect("immediate integer handle")),
        TAG_BOOL => {
            d.word(D_BOOL);
            d.word(h >> TAG_BITS);
        }
        TAG_STR | TAG_MODEL_VALUE => {
            let s = symbol(h).expect("invalid symbol handle");
            d.word(if tag(h) == TAG_STR { D_STR } else { D_MV });
            d.word(s.text_hash());
        }
        _ => unreachable!("not an immediate handle"),
    }
    d.finish()
}

/// The hash of a body's exact representation (its kind, witness and child
/// handles).
fn exact_hash(body: &Body) -> u64 {
    let mut d = Digest::new();
    d.word(body.kind_tag());
    match body {
        Body::Int(i) => d.word(*i as u64),
        Body::Interval(lo, hi) => {
            d.word(*lo as u64);
            d.word(*hi as u64);
        }
        Body::Set(es) | Body::Tuple(es) | Body::Fcn(es, _) => {
            d.word(es.len() as u64);
            es.iter().for_each(|e| d.word(*e));
        }
        Body::Record(fs) => {
            d.word(fs.len() as u64);
            for (k, e) in fs.iter() {
                d.word(k.id() as u64);
                d.word(*e);
            }
        }
    }
    let h = d.finish();
    #[cfg(test)]
    let h = tests::tiny_hash(h);
    h
}

// ---- thawing with a per-thread cache ----

const THAW_SLOTS: usize = 1024;
const ROOT_SLOTS: usize = 2048;

thread_local! {
    static THAWED: std::cell::RefCell<Vec<Option<(u64, u64, Value)>>> = std::cell::RefCell::new(vec![None; THAW_SLOTS]);
    /// Thawed slot values (`Store::thaw_slot`), direct-mapped like `THAWED`.
    static ROOTS: std::cell::RefCell<Vec<Option<(u64, u64, Value)>>> = std::cell::RefCell::new(vec![None; ROOT_SLOTS]);
}

/// `thaw_node`, with a direct-mapped per-thread cache by (store, handle):
/// nodes never change, so a cached value stays valid.
fn thaw_cached(store: &Store, h: u64) -> Value {
    let slot = (fmix64(h ^ store.uid.rotate_left(17)) as usize) & (THAW_SLOTS - 1);
    let hit = THAWED.with(|c| match &c.borrow()[slot] {
        Some((u, k, v)) if *u == store.uid && *k == h => Some(v.clone()),
        _ => None,
    });
    if let Some(v) = hit {
        return v;
    }
    let v = store.thaw_node(h);
    THAWED.with(|c| c.borrow_mut()[slot] = Some((store.uid, h, v.clone())));
    v
}

/// The semantic digest of a value outside any store: `v` is frozen into a
/// throwaway unbounded store and that store's digest is returned, so the
/// result equals `Store::digest(s.freeze(v)?)` for any store `s`. The
/// compiled tier's escape path fingerprints a VIEW value that does not fit
/// the compiled codec with this; the store tests use it as an independent
/// digest oracle.
pub fn digest_of_value(v: &Value) -> Result<u64, StoreError> {
    let s = Store::new(usize::MAX);
    let h = s.freeze(v)?;
    Ok(s.digest(h))
}

/// A shared store handle carried by `Shape::Ref`: one store per run.
/// Shapes compare and hash it by the store's id, and print it as `Ref`
/// (the generated code does not depend on the store).
#[derive(Clone)]
pub struct StoreRef(pub Arc<Store>);

impl StoreRef {
    pub fn new(budget: usize) -> StoreRef {
        StoreRef(Store::new(budget))
    }
}

impl std::ops::Deref for StoreRef {
    type Target = Store;
    fn deref(&self) -> &Store {
        &self.0
    }
}

impl PartialEq for StoreRef {
    fn eq(&self, other: &StoreRef) -> bool {
        self.0.uid == other.0.uid
    }
}

impl Eq for StoreRef {}

impl std::hash::Hash for StoreRef {
    fn hash<H: std::hash::Hasher>(&self, h: &mut H) {
        self.0.uid.hash(h)
    }
}

impl std::fmt::Debug for StoreRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str("Store")
    }
}
