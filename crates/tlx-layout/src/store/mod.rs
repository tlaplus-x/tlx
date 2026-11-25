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
//! Nodes are published once and never change or move while live; node indices
//! are monotonic and never reused. Readers and interners hold a shared
//! recursive read pin (`StorePin`, a `parking_lot::RwLock` read guard over
//! the two-level radix page table); interning additionally takes a short
//! lock of one of `SHARDS` index shards. At a safepoint (no active pins),
//! `Store::collect_with` takes the exclusive table lock, marks all nodes
//! reachable from live roots, sweeps unreachable nodes, index entries, and
//! empty pages/directories, and advances `gc_gen` so per-thread caches drop
//! stale entries without cross-thread synchronization.

#![forbid(unsafe_code)]

mod ops;
mod order;
mod ser;

#[cfg(test)]
mod tests;

pub use self::ops::{witness, Absent, RefOpError};
pub use self::order::{cmp_tlc, cmp_tlc_pin, eq_tlc, eq_tlc_pin};

use std::cell::Cell;
use std::collections::HashMap;
use std::hash::BuildHasherDefault;
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

use tlx_base::hash::{fmix64, IdHasher};
use tlx_base::sync::{RwLock, RwLockReadGuard};
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

/// Two-level radix page table for monotonic node indices:
/// `PAGE = 256` nodes/page (~20 KiB per active dense page),
/// `DIR = 4096` pages per L2 directory (32 KiB inline `dir0` covers the first
/// 1,048,576 nodes in one indirection), `ROOT = 16384` L1 directories
/// (`2^34` = 17.18 billion monotonic indices, fitting within 45 handle bits).
/// Sealed pages with at most `PAGE / 2` survivors compact to `Page::Sparse`
/// during sweep/restore, and sealed overflow directories with at most
/// `DIR / 8` live pages compact to `Dir::Sparse`, keeping retained storage
/// proportional to live survivors and accurately accounted against `budget`.
const PAGE_BITS: u32 = 8;
const PAGE: usize = 1 << PAGE_BITS;
const DIR_BITS: u32 = 12;
const DIR: usize = 1 << DIR_BITS;
const ROOT_BITS: u32 = 14;
const ROOT: usize = 1 << ROOT_BITS;
pub(crate) const MAX_NODES: u64 = (ROOT as u64) * (DIR as u64) * (PAGE as u64);

/// Maximum live nodes in a sealed page before keeping it as `Page::Dense`.
const SPARSE_PAGE_MAX: usize = PAGE / 2;
/// Maximum live pages in a sealed overflow directory before keeping `Dir::Dense`.
const SPARSE_DIR_MAX: usize = DIR / 8;

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
    /// Set on the calling thread whenever `Store::intern` returns
    /// `Err(StoreError::Full)`, so compiled/native/VIEW/symmetry callers can
    /// distinguish a recoverable store budget hit from a layout miss or
    /// evaluation error.
    static STORE_FULL_HIT: Cell<bool> = const { Cell::new(false) };
}

/// Clear this thread's recorded store-full flag before an operation.
#[inline]
pub fn clear_full_hit() {
    STORE_FULL_HIT.with(|f| f.set(false));
}

/// Consume and return whether this thread hit `StoreError::Full` since the
/// last clear.
#[inline]
pub fn take_full_hit() -> bool {
    STORE_FULL_HIT.with(|f| f.replace(false))
}

/// Inspect whether this thread hit `StoreError::Full` since the last clear.
#[inline]
pub fn peek_full_hit() -> bool {
    STORE_FULL_HIT.with(|f| f.get())
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
    /// `DOMAIN` of a function node, computed on first use (cleared on GC).
    domain: OnceLock<u64>,
    /// The elements of an interval node as handles, for iteration (cleared on GC).
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
    One(u64),
    Many(Vec<u64>),
}

#[repr(align(128))]
#[derive(Default)]
struct Shard(Mutex<HashMap<u64, Ids, BuildHasherDefault<IdHasher>>>);

/// One page of up to `PAGE` node slots: active/dense pages use direct O(1)
/// indexing, while sealed sparse pages compact to sorted `(slot, Node)` pairs
/// so sparse survivors never retain empty 20 KiB pages outside the budget.
pub(crate) enum Page {
    Dense(Box<[OnceLock<Node>]>),
    Sparse(Box<[(u16, Node)]>),
}

impl Page {
    fn new_dense() -> Box<Page> {
        Box::new(Page::Dense((0..PAGE).map(|_| OnceLock::new()).collect()))
    }

    #[inline]
    fn get(&self, s: usize) -> Option<&Node> {
        match self {
            Page::Dense(slots) => slots.get(s)?.get(),
            Page::Sparse(entries) => {
                let key = s as u16;
                entries.binary_search_by_key(&key, |&(k, _)| k).ok().map(|i| &entries[i].1)
            }
        }
    }

    pub(crate) fn for_each_live(&self, mut f: impl FnMut(usize, &Node)) {
        match self {
            Page::Dense(slots) => {
                for (s, slot) in slots.iter().enumerate() {
                    if let Some(node) = slot.get() {
                        f(s, node);
                    }
                }
            }
            Page::Sparse(entries) => {
                for &(s, ref node) in entries.iter() {
                    f(s as usize, node);
                }
            }
        }
    }

    pub(crate) fn live_count(&self) -> usize {
        match self {
            Page::Dense(slots) => slots.iter().filter(|s| s.get().is_some()).count(),
            Page::Sparse(entries) => entries.len(),
        }
    }

    /// Unified backing-storage charge (excluding child payloads):
    /// - `Page::Dense`: charges every slot in `0..used_slots` (`PAGE` for a
    ///   sealed page, `next & (PAGE - 1)` for the active tail page), matching
    ///   what monotonic admission reserved across holes.
    /// - `Page::Sparse`: charges the `Page` header plus compacted entries.
    fn backing_bytes(&self, used_slots: usize) -> usize {
        match self {
            Page::Dense(_) => used_slots * std::mem::size_of::<OnceLock<Node>>(),
            Page::Sparse(entries) => std::mem::size_of::<Page>() + entries.len() * std::mem::size_of::<(u16, Node)>(),
        }
    }
}

/// One overflow L2 directory (`d >= 1`): dense while active or well-populated,
/// compacted to sorted `(page_offset, Box<Page>)` pairs when sealed and sparse.
enum Dir {
    Dense(Box<[OnceLock<Box<Page>>]>),
    Sparse(Box<[(u16, Box<Page>)]>),
}

impl Dir {
    fn new_dense() -> Box<Dir> {
        Box::new(Dir::Dense((0..DIR).map(|_| OnceLock::new()).collect()))
    }

    #[inline]
    fn get_page(&self, p: usize) -> Option<&Page> {
        match self {
            Dir::Dense(slots) => slots.get(p)?.get().map(|b| &**b),
            Dir::Sparse(entries) => {
                let key = p as u16;
                entries.binary_search_by_key(&key, |&(k, _)| k).ok().map(|i| &*entries[i].1)
            }
        }
    }

    fn for_each_page(&self, mut f: impl FnMut(usize, &Page)) {
        match self {
            Dir::Dense(slots) => {
                for (p, slot) in slots.iter().enumerate() {
                    if let Some(page) = slot.get() {
                        f(p, page);
                    }
                }
            }
            Dir::Sparse(entries) => {
                for &(p, ref page) in entries.iter() {
                    f(p as usize, page);
                }
            }
        }
    }

    fn backing_bytes(&self) -> usize {
        match self {
            Dir::Dense(slots) => slots.len() * std::mem::size_of::<OnceLock<Box<Page>>>(),
            Dir::Sparse(entries) => std::mem::size_of::<Dir>() + entries.len() * std::mem::size_of::<(u16, Box<Page>)>(),
        }
    }
}

type RootDir = Box<[OnceLock<Box<Page>>]>;
type OverflowDirs = Box<[OnceLock<Box<Dir>>]>;

/// Two-level radix page table protected by `Store::table`, with directory 0
/// (`dir0`, 32 KiB covering the first 1,048,576 nodes) stored inline for
/// single-indirection lookups on the common path and overflow directories
/// allocated lazily.
struct Pages {
    dir0: RootDir,
    dirs: OnceLock<OverflowDirs>,
}

impl Pages {
    fn new() -> Pages {
        Pages { dir0: (0..DIR).map(|_| OnceLock::new()).collect(), dirs: OnceLock::new() }
    }

    #[inline]
    fn get_index(&self, i: u64) -> Option<&Node> {
        let page_idx = i >> PAGE_BITS;
        let s = (i as usize) & (PAGE - 1);
        if page_idx < DIR as u64 {
            return self.dir0[page_idx as usize].get()?.get(s);
        }
        let d = (page_idx >> DIR_BITS) as usize;
        let p = (page_idx as usize) & (DIR - 1);
        self.dirs.get()?.get(d - 1)?.get()?.get_page(p)?.get(s)
    }

    fn has_overflow_dir(&self, d: usize) -> bool {
        self.dirs.get().and_then(|ds| ds.get(d - 1)).is_some_and(|s| s.get().is_some())
    }

    fn init_overflow_dir(&self, d: usize) -> bool {
        let dirs = self.dirs.get_or_init(|| (1..ROOT).map(|_| OnceLock::new()).collect());
        let Some(slot) = dirs.get(d - 1) else { return false };
        slot.set(Dir::new_dense()).is_ok()
    }

    fn get_or_init_page(&self, i: u64) -> Option<&[OnceLock<Node>]> {
        let page_idx = i >> PAGE_BITS;
        let page = if page_idx < DIR as u64 {
            self.dir0[page_idx as usize].get_or_init(Page::new_dense)
        } else {
            let d = (page_idx >> DIR_BITS) as usize;
            let p = (page_idx as usize) & (DIR - 1);
            let dirs = self.dirs.get_or_init(|| (1..ROOT).map(|_| OnceLock::new()).collect());
            let dir_slot = dirs.get(d - 1)?;
            let dir = dir_slot.get_or_init(Dir::new_dense);
            let Dir::Dense(slots) = &**dir else {
                unreachable!("value store: writing into sealed sparse directory {d}");
            };
            slots[p].get_or_init(Page::new_dense)
        };
        let Page::Dense(slots) = &**page else {
            unreachable!("value store: writing into sealed sparse page {page_idx}");
        };
        Some(slots)
    }

    pub(crate) fn for_each_page(&self, mut f: impl FnMut(u64, &Page)) {
        for (p, slot) in self.dir0.iter().enumerate() {
            if let Some(page) = slot.get() {
                f(p as u64, page);
            }
        }
        if let Some(dirs) = self.dirs.get() {
            for (i, dir_slot) in dirs.iter().enumerate() {
                let Some(dir) = dir_slot.get() else { continue };
                let d_base = ((i + 1) as u64) << DIR_BITS;
                dir.for_each_page(|p, page| f(d_base | (p as u64), page));
            }
        }
    }

    /// Finalize one restored page using the unified backing-storage rule:
    /// sealed pages (`page_idx < tail_page`) compact to `Page::Sparse` when
    /// `live <= SPARSE_PAGE_MAX` and otherwise charge `PAGE` dense slots; the
    /// active tail page (`page_idx == tail_page`) charges `next_in_page` dense
    /// slots. Returns the net change in backing bytes (`isize`).
    pub(crate) fn compact_restored_page(&mut self, page_idx: u64, tail_page: u64, next_in_page: usize) -> isize {
        if page_idx > tail_page {
            return 0;
        }
        let slot: Option<&mut OnceLock<Box<Page>>> = if page_idx < DIR as u64 {
            self.dir0.get_mut(page_idx as usize)
        } else {
            let d = (page_idx >> DIR_BITS) as usize;
            let p = (page_idx as usize) & (DIR - 1);
            self.dirs.get_mut().and_then(|ds| ds.get_mut(d - 1)).and_then(|ds| ds.get_mut()).and_then(|dir| match &mut **dir {
                Dir::Dense(slots) => slots.get_mut(p),
                Dir::Sparse(_) => None,
            })
        };
        let Some(page_slot) = slot else { return 0 };
        let Some(page) = page_slot.get_mut() else { return 0 };
        let Page::Dense(slots) = &mut **page else { return 0 };
        let live = slots.iter().filter(|s| s.get().is_some()).count();
        let charged_before = live * std::mem::size_of::<OnceLock<Node>>();
        if live == 0 {
            page_slot.take();
            return -(charged_before as isize);
        }
        if page_idx == tail_page {
            let after = page.backing_bytes(next_in_page);
            return after as isize - charged_before as isize;
        }
        if live <= SPARSE_PAGE_MAX {
            let mut entries = Vec::with_capacity(live);
            for (s, cell) in slots.iter_mut().enumerate() {
                if let Some(node) = cell.take() {
                    entries.push((s as u16, node));
                }
            }
            let sparse = Page::Sparse(entries.into_boxed_slice());
            let after = sparse.backing_bytes(PAGE);
            **page = sparse;
            after as isize - charged_before as isize
        } else {
            let after = page.backing_bytes(PAGE);
            after as isize - charged_before as isize
        }
    }

    /// Compact sealed overflow directories (`d >= 1`, `d < tail_dir`) and
    /// return the total overflow directory backing bytes across all retained
    /// overflow directories.
    pub(crate) fn finalize_restored_dirs(&mut self, tail_dir: usize) -> usize {
        let Some(dirs) = self.dirs.get_mut() else { return 0 };
        let mut dir_bytes = 0usize;
        for (i, dir_slot) in dirs.iter_mut().enumerate() {
            let d = i + 1;
            let Some(dir) = dir_slot.get_mut() else { continue };
            let sealed = d < tail_dir;
            if sealed {
                if let Dir::Dense(slots) = &mut **dir {
                    let live_pages = slots.iter().filter(|s| s.get().is_some()).count();
                    if live_pages == 0 {
                        dir_slot.take();
                        continue;
                    }
                    if live_pages <= SPARSE_DIR_MAX {
                        let mut entries = Vec::with_capacity(live_pages);
                        for (p, cell) in slots.iter_mut().enumerate() {
                            if let Some(page) = cell.take() {
                                entries.push((p as u16, page));
                            }
                        }
                        **dir = Dir::Sparse(entries.into_boxed_slice());
                    }
                }
            }
            dir_bytes += dir.backing_bytes();
        }
        dir_bytes
    }
}

/// Result of one safepoint mark-and-sweep cycle on a `Store`.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct GcStats {
    pub live_nodes: u64,
    pub live_bytes: u64,
    pub reclaimed_nodes: u64,
    pub reclaimed_bytes: u64,
    pub freed_pages: u64,
}

/// Statistics of a store.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct StoreStats {
    /// Currently live nodes.
    pub nodes: u64,
    /// Bytes of live nodes and their payloads.
    pub node_bytes: u64,
    /// Estimated bytes of the intern index.
    pub index_bytes: u64,
    pub budget: u64,
    /// Completed safepoint GC cycles.
    pub gc_cycles: u64,
    /// Cumulative nodes reclaimed across GC cycles.
    pub reclaimed_nodes: u64,
    /// Cumulative node bytes reclaimed across GC cycles.
    pub reclaimed_bytes: u64,
}

/// RAII scope marking that a GC-capable search driver is actively servicing
/// safepoint reclamation for this store. While active, hitting `budget`
/// requests GC and returns `StoreError::Full` without permanently latching
/// `Store::is_full()`.
pub struct StoreGcGuard {
    store: Arc<Store>,
}

impl Drop for StoreGcGuard {
    fn drop(&mut self) {
        self.store.gc_active.fetch_sub(1, Ordering::Release);
    }
}

/// Shared recursive read guard pinning a `Store`'s page table against
/// concurrent safepoint sweeps. Holding one pin across a batch of reads or
/// native operations avoids per-operation locking.
pub struct StorePin<'a> {
    pub(crate) store: &'a Store,
    pages: RwLockReadGuard<'a, Pages>,
    gc_gen: u64,
}

/// A run-owned store of immutable value nodes (see the module comment).
pub struct Store {
    /// Unique in the process (never reused); `id` is its low 16 bits, in
    /// the handles.
    uid: u64,
    id: u64,
    table: RwLock<Pages>,
    next: AtomicU64,
    live_nodes: AtomicU64,
    shards: Box<[Shard]>,
    bytes: AtomicUsize,
    index_bytes: AtomicUsize,
    budget: usize,
    /// Serializes lazy overflow directory (`d >= 1`) budget reservation &
    /// initialization (taken at most once per 1,048,576 nodes).
    dir_init: Mutex<()>,
    soft_limit: AtomicUsize,
    full: AtomicBool,
    gc_active: AtomicUsize,
    gc_requested: AtomicBool,
    gc_gen: AtomicU64,
    gc_cycles: AtomicU64,
    reclaimed_nodes: AtomicU64,
    reclaimed_bytes: AtomicU64,
}

static NEXT_UID: AtomicU64 = AtomicU64::new(1);

fn allocate_uid(next: &AtomicU64) -> u64 {
    // Never reuse the store-id bits: old handles can outlive their store.
    next.fetch_update(Ordering::Relaxed, Ordering::Relaxed, |n| (n < 1 << STORE_BITS).then_some(n + 1)).expect("value store ids exhausted")
}

fn compute_soft_limit(live: usize, budget: usize) -> usize {
    let half = budget / 2;
    let headroom = budget.saturating_sub(live);
    let max_soft = live.saturating_add(headroom.max(2) / 2).min(budget);
    live.saturating_mul(2).max(half).min(max_soft)
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
            table: RwLock::new(Pages::new()),
            next: AtomicU64::new(0),
            live_nodes: AtomicU64::new(0),
            shards: (0..SHARDS).map(|_| Shard::default()).collect(),
            bytes: AtomicUsize::new(0),
            index_bytes: AtomicUsize::new(0),
            budget,
            dir_init: Mutex::new(()),
            soft_limit: AtomicUsize::new(compute_soft_limit(0, budget)),
            full: AtomicBool::new(false),
            gc_active: AtomicUsize::new(0),
            gc_requested: AtomicBool::new(false),
            gc_gen: AtomicU64::new(0),
            gc_cycles: AtomicU64::new(0),
            reclaimed_nodes: AtomicU64::new(0),
            reclaimed_bytes: AtomicU64::new(0),
        })
    }

    /// Pin the page table for reads and interning. Uses recursive read
    /// locking so nested pins on the same thread never deadlock.
    #[inline]
    pub fn pin(&self) -> StorePin<'_> {
        let pages = self.table.read_recursive();
        let gc_gen = self.gc_gen.load(Ordering::Relaxed);
        StorePin { store: self, pages, gc_gen }
    }

    /// Mark that a GC-capable search is actively driving reclamation for
    /// this store until the returned guard drops.
    pub fn enter_gc_scope(self: &Arc<Store>) -> StoreGcGuard {
        self.gc_active.fetch_add(1, Ordering::AcqRel);
        StoreGcGuard { store: Arc::clone(self) }
    }

    /// Whether the store has crossed its soft limit (or hit its budget while
    /// GC-managed) and wants a safepoint collection.
    #[inline]
    pub fn needs_gc(&self) -> bool {
        self.gc_requested.load(Ordering::Acquire)
    }

    /// Monotonically incremented on every completed GC sweep; used to
    /// invalidate per-thread handle caches lazily.
    #[inline]
    pub fn gc_gen(&self) -> u64 {
        self.gc_gen.load(Ordering::Acquire)
    }

    /// Permanently mark this store exhausted after a GC-backed retry still
    /// could not fit the live root set within `budget`.
    pub fn mark_full(&self) {
        self.full.store(true, Ordering::Relaxed);
    }

    /// The process-unique id of this store.
    pub fn uid(&self) -> u64 {
        self.uid
    }

    /// Whether an insertion was permanently refused because the budget was
    /// exhausted.
    pub fn is_full(&self) -> bool {
        self.full.load(Ordering::Relaxed)
    }

    pub fn budget(&self) -> usize {
        self.budget
    }

    pub fn stats(&self) -> StoreStats {
        StoreStats {
            nodes: self.live_nodes.load(Ordering::Relaxed),
            node_bytes: self.bytes.load(Ordering::Relaxed) as u64,
            index_bytes: self.index_bytes.load(Ordering::Relaxed) as u64,
            budget: self.budget as u64,
            gc_cycles: self.gc_cycles.load(Ordering::Relaxed),
            reclaimed_nodes: self.reclaimed_nodes.load(Ordering::Relaxed),
            reclaimed_bytes: self.reclaimed_bytes.load(Ordering::Relaxed),
        }
    }

    pub(crate) fn handle_of(&self, index: u64) -> u64 {
        (index + 1) << INDEX_SHIFT | self.id << TAG_BITS | TAG_NODE
    }

    /// Whether `h` names a currently published live node of this store.
    #[inline]
    pub fn has_node(&self, h: u64) -> bool {
        self.pin().node(h).is_some()
    }

    /// Whether `h` is a valid handle of this store (an immediate with a
    /// published symbol, or a live node of this store).
    #[inline]
    pub fn is_valid(&self, h: u64) -> bool {
        match tag(h) {
            TAG_NODE => self.pin().node(h).is_some(),
            _ => immediate_value(h).is_some(),
        }
    }

    /// The semantic digest of a handle.
    #[inline]
    pub fn digest(&self, h: u64) -> u64 {
        if is_immediate(h) {
            assert!(immediate_value(h).is_some(), "value store {}: invalid handle {h:#x}", self.uid);
            return scalar_digest(h);
        }
        self.pin().digest(h)
    }

    /// Store a finite value (lazy values are normalized first, as states
    /// store them).
    pub fn freeze(&self, v: &Value) -> Result<u64, StoreError> {
        if let Some(h) = immediate(v) {
            return Ok(h);
        }
        self.pin().freeze(v)
    }

    /// The value of a slot word (see `StorePin::thaw_slot`).
    pub fn thaw_slot(&self, h: u64) -> Value {
        if h == 0 {
            return Value::Bool(false);
        }
        if is_immediate(h) {
            return immediate_value(h).expect("invalid immediate handle");
        }
        let gc_gen = self.gc_gen.load(Ordering::Acquire);
        let slot = (fmix64(h ^ self.uid.rotate_left(29)) as usize) & (ROOT_SLOTS - 1);
        let hit = ROOTS.with(|c| match &c.borrow()[slot] {
            Some((u, g, k, v)) if *u == self.uid && *g == gc_gen && *k == h => Some(v.clone()),
            _ => None,
        });
        if let Some(v) = hit {
            return v;
        }
        self.pin().thaw_slot(h)
    }

    /// The value of a handle of this store: exactly the value frozen.
    pub fn thaw(&self, h: u64) -> Value {
        if is_immediate(h) {
            return immediate_value(h).expect("invalid immediate handle");
        }
        let gc_gen = self.gc_gen.load(Ordering::Acquire);
        let slot = (fmix64(h ^ self.uid.rotate_left(17)) as usize) & (THAW_SLOTS - 1);
        let hit = THAWED.with(|c| match &c.borrow()[slot] {
            Some((u, g, k, v)) if *u == self.uid && *g == gc_gen && *k == h => Some(v.clone()),
            _ => None,
        });
        if let Some(v) = hit {
            return v;
        }
        self.pin().thaw(h)
    }

    /// The value of an arbitrary word (None: not a valid handle of this
    /// store). For words from outside the compiled code.
    pub fn try_thaw(&self, h: u64) -> Option<Value> {
        match tag(h) {
            TAG_NODE => self.pin().try_thaw(h),
            _ => immediate_value(h),
        }
    }

    /// Safepoint mark-and-sweep collection of all nodes not transitively
    /// reachable from roots fed to `visit_roots`.
    ///
    /// Must only be called when no thread is actively using the store (or
    /// holds a `StorePin`), such as at an explorer safepoint or between
    /// search phases.
    pub fn collect_with<F>(&self, visit_roots: F) -> GcStats
    where
        F: FnOnce(&mut dyn FnMut(u64)),
    {
        self.try_collect_with::<std::convert::Infallible, _>(|mark| {
            visit_roots(mark);
            Ok(())
        })
        .unwrap()
    }

    /// Fallible safepoint mark-and-sweep collection: if `visit_roots` returns
    /// `Err(e)` (e.g. an I/O error reading a spilled frontier segment), the
    /// collection aborts *before* sweeping so live nodes are never dropped on
    /// an incomplete root scan.
    pub fn try_collect_with<E, F>(&self, visit_roots: F) -> Result<GcStats, E>
    where
        F: FnOnce(&mut dyn FnMut(u64)) -> Result<(), E>,
    {
        let mut pages = self.table.write();
        let mut marks: HashMap<u64, [u64; PAGE / 64], BuildHasherDefault<IdHasher>> = HashMap::default();
        let mut stack: Vec<u64> = Vec::new();
        let store_id = self.id;

        {
            let pages_ref: &Pages = &pages;
            let mut root_cb = |h: u64| mark_handle(pages_ref, &mut marks, &mut stack, store_id, h);
            visit_roots(&mut root_cb)?;
        }

        while let Some(idx) = stack.pop() {
            let Some(node) = pages.get_index(idx) else { continue };
            match &node.body {
                Body::Int(_) | Body::Interval(..) => {}
                Body::Set(es) | Body::Tuple(es) | Body::Fcn(es, _) => {
                    for &c in es.iter() {
                        mark_handle(&pages, &mut marks, &mut stack, store_id, c);
                    }
                }
                Body::Record(fs) => {
                    for &(_, c) in fs.iter() {
                        mark_handle(&pages, &mut marks, &mut stack, store_id, c);
                    }
                }
            }
        }

        let mut live_buckets: usize = 0;
        for shard in self.shards.iter() {
            let mut index = shard.0.lock().unwrap_or_else(|e| e.into_inner());
            index.retain(|_, ids| match ids {
                Ids::One(i) => is_marked(&marks, *i),
                Ids::Many(is) => {
                    is.retain(|i| is_marked(&marks, *i));
                    match is.len() {
                        0 => false,
                        1 => {
                            *ids = Ids::One(is[0]);
                            true
                        }
                        _ => true,
                    }
                }
            });
            if index.capacity() > 64 && index.len() * 4 < index.capacity() {
                index.shrink_to_fit();
            }
            live_buckets += index.len();
        }
        self.index_bytes.store(live_buckets * 24, Ordering::Relaxed);

        let next = self.next.load(Ordering::Acquire);
        let tail_page = next >> PAGE_BITS;
        let next_in_page = (next as usize) & (PAGE - 1);
        let tail_dir = (tail_page >> DIR_BITS) as usize;

        struct SweepAcc {
            tail_page: u64,
            next_in_page: usize,
            slot_overhead: usize,
            live_nodes: u64,
            live_bytes: usize,
            reclaimed_nodes: u64,
            reclaimed_bytes: u64,
            freed_pages: u64,
            dropped_tail_page: bool,
        }

        impl SweepAcc {
            /// Sweep one page in place; returns `false` if the page has zero
            /// survivors and should be dropped. Uses the same backing-storage
            /// rule as admission and restore: dense sealed pages charge `PAGE`
            /// slots, the active dense tail page charges `next_in_page` slots,
            /// and sealed sparse pages compact to `Page::Sparse`.
            fn sweep_page(
                &mut self,
                page: &mut Page,
                page_idx: u64,
                marks: &HashMap<u64, [u64; PAGE / 64], BuildHasherDefault<IdHasher>>,
            ) -> bool {
                let page_marks = marks.get(&page_idx);
                let is_marked_slot = |s: usize| page_marks.is_some_and(|bits| (bits[s >> 6] >> (s & 63)) & 1 != 0);
                let sealed = page_idx < self.tail_page;
                let used_slots = if sealed { PAGE } else { self.next_in_page };
                match page {
                    Page::Dense(slots) => {
                        let mut live_in_page = 0usize;
                        let mut payload_bytes = 0usize;
                        let mut dead_payload_bytes = 0u64;
                        for (s, slot) in slots.iter_mut().enumerate() {
                            let Some(node) = slot.get_mut() else { continue };
                            let pbytes = node.body.bytes();
                            if is_marked_slot(s) {
                                live_in_page += 1;
                                payload_bytes += pbytes;
                                node.domain.take();
                                node.elems.take();
                            } else {
                                self.reclaimed_nodes += 1;
                                dead_payload_bytes += pbytes as u64;
                                slot.take();
                            }
                        }
                        let backing_before = used_slots * self.slot_overhead;
                        if live_in_page == 0 {
                            self.reclaimed_bytes += backing_before as u64 + dead_payload_bytes;
                            if !sealed {
                                self.dropped_tail_page = true;
                            }
                            return false;
                        }
                        self.live_nodes += live_in_page as u64;
                        if sealed && live_in_page <= SPARSE_PAGE_MAX {
                            let mut entries = Vec::with_capacity(live_in_page);
                            for (s, slot) in slots.iter_mut().enumerate() {
                                if let Some(node) = slot.take() {
                                    entries.push((s as u16, node));
                                }
                            }
                            *page = Page::Sparse(entries.into_boxed_slice());
                        }
                        let backing_after = page.backing_bytes(used_slots);
                        self.reclaimed_bytes += backing_before.saturating_sub(backing_after) as u64 + dead_payload_bytes;
                        self.live_bytes += backing_after + payload_bytes;
                        true
                    }
                    Page::Sparse(entries) => {
                        let backing_before = std::mem::size_of::<Page>() + entries.len() * std::mem::size_of::<(u16, Node)>();
                        let mut kept = Vec::new();
                        let mut payload_bytes = 0usize;
                        let mut dead_payload_bytes = 0u64;
                        let old = std::mem::take(entries);
                        for (s, mut node) in old.into_vec() {
                            let pbytes = node.body.bytes();
                            if is_marked_slot(s as usize) {
                                payload_bytes += pbytes;
                                node.domain.take();
                                node.elems.take();
                                kept.push((s, node));
                            } else {
                                self.reclaimed_nodes += 1;
                                dead_payload_bytes += pbytes as u64;
                            }
                        }
                        if kept.is_empty() {
                            self.reclaimed_bytes += backing_before as u64 + dead_payload_bytes;
                            return false;
                        }
                        self.live_nodes += kept.len() as u64;
                        *entries = kept.into_boxed_slice();
                        let backing_after = std::mem::size_of::<Page>() + entries.len() * std::mem::size_of::<(u16, Node)>();
                        self.reclaimed_bytes += backing_before.saturating_sub(backing_after) as u64 + dead_payload_bytes;
                        self.live_bytes += backing_after + payload_bytes;
                        true
                    }
                }
            }
        }

        let mut acc = SweepAcc {
            tail_page,
            next_in_page,
            slot_overhead: std::mem::size_of::<OnceLock<Node>>(),
            live_nodes: 0,
            live_bytes: 0,
            reclaimed_nodes: 0,
            reclaimed_bytes: 0,
            freed_pages: 0,
            dropped_tail_page: false,
        };

        // Sweep inline directory 0.
        for (p, page_slot) in pages.dir0.iter_mut().enumerate() {
            let Some(page) = page_slot.get_mut() else { continue };
            if !acc.sweep_page(page, p as u64, &marks) {
                page_slot.take();
                acc.freed_pages += 1;
            }
        }

        // Sweep overflow directories (`d >= 1`), compacting sealed sparse dirs
        // and charging retained overflow directory backing storage.
        if let Some(dirs) = pages.dirs.get_mut() {
            for (i, dir_slot) in dirs.iter_mut().enumerate() {
                let d = i + 1;
                let Some(dir) = dir_slot.get_mut() else { continue };
                let d_base = (d as u64) << DIR_BITS;
                let sealed_dir = d < tail_dir;
                let dir_alive = match &mut **dir {
                    Dir::Dense(slots) => {
                        let mut live_pages = 0usize;
                        for (p, page_slot) in slots.iter_mut().enumerate() {
                            let Some(page) = page_slot.get_mut() else { continue };
                            if acc.sweep_page(page, d_base | (p as u64), &marks) {
                                live_pages += 1;
                            } else {
                                page_slot.take();
                                acc.freed_pages += 1;
                            }
                        }
                        if live_pages == 0 {
                            false
                        } else {
                            if sealed_dir && live_pages <= SPARSE_DIR_MAX {
                                let mut entries = Vec::with_capacity(live_pages);
                                for (p, page_slot) in slots.iter_mut().enumerate() {
                                    if let Some(page) = page_slot.take() {
                                        entries.push((p as u16, page));
                                    }
                                }
                                **dir = Dir::Sparse(entries.into_boxed_slice());
                            }
                            true
                        }
                    }
                    Dir::Sparse(entries) => {
                        let mut kept = Vec::new();
                        let old = std::mem::take(entries);
                        for (p, mut page) in old.into_vec() {
                            if acc.sweep_page(&mut page, d_base | (p as u64), &marks) {
                                kept.push((p, page));
                            } else {
                                acc.freed_pages += 1;
                            }
                        }
                        if kept.is_empty() {
                            false
                        } else {
                            *entries = kept.into_boxed_slice();
                            true
                        }
                    }
                };
                if !dir_alive {
                    dir_slot.take();
                } else {
                    acc.live_bytes += dir.backing_bytes();
                }
            }
        }

        let SweepAcc { live_nodes, live_bytes, reclaimed_nodes, reclaimed_bytes, freed_pages, dropped_tail_page, .. } = acc;
        if dropped_tail_page && next_in_page != 0 {
            // Advancing `next` past the dropped empty tail page keeps the next
            // allocation aligned at slot 0 of the following page with zero
            // uncharged leading holes.
            let aligned = (tail_page + 1) << PAGE_BITS;
            if aligned <= MAX_NODES {
                self.next.store(aligned, Ordering::Release);
            }
        }
        self.live_nodes.store(live_nodes, Ordering::Relaxed);
        self.bytes.store(live_bytes, Ordering::Relaxed);
        self.soft_limit.store(compute_soft_limit(live_bytes, self.budget), Ordering::Relaxed);
        self.gc_requested.store(false, Ordering::Release);
        self.gc_cycles.fetch_add(1, Ordering::Relaxed);
        self.reclaimed_nodes.fetch_add(reclaimed_nodes, Ordering::Relaxed);
        self.reclaimed_bytes.fetch_add(reclaimed_bytes, Ordering::Relaxed);
        self.gc_gen.fetch_add(1, Ordering::Release);

        Ok(GcStats { live_nodes, live_bytes: live_bytes as u64, reclaimed_nodes, reclaimed_bytes, freed_pages })
    }

    /// Test-only seam (`store/tests.rs`): whether two handles denote equal
    /// values (`Value`'s equality: the aliases are equal). Digests decide
    /// unequal values; equal digests are checked structurally. Production
    /// code compares thawed values directly, so this is not exported.
    #[cfg(test)]
    pub fn same_value(&self, a: u64, b: u64) -> bool {
        let pin = self.pin();
        pin.assert_valid(a);
        pin.assert_valid(b);
        a == b || (pin.digest(a) == pin.digest(b) && pin.thaw(a) == pin.thaw(b))
    }
}

#[inline]
fn is_marked(marks: &HashMap<u64, [u64; PAGE / 64], BuildHasherDefault<IdHasher>>, idx: u64) -> bool {
    let page_idx = idx >> PAGE_BITS;
    let slot = (idx as usize) & (PAGE - 1);
    marks.get(&page_idx).is_some_and(|bits| (bits[slot >> 6] >> (slot & 63)) & 1 != 0)
}

#[inline]
fn mark_handle(
    pages: &Pages,
    marks: &mut HashMap<u64, [u64; PAGE / 64], BuildHasherDefault<IdHasher>>,
    stack: &mut Vec<u64>,
    store_id: u64,
    h: u64,
) {
    if tag(h) != TAG_NODE || ((h >> TAG_BITS) & ((1 << STORE_BITS) - 1)) != store_id {
        return;
    }
    let Some(idx) = (h >> INDEX_SHIFT).checked_sub(1) else { return };
    if pages.get_index(idx).is_none() {
        return;
    }
    let page_idx = idx >> PAGE_BITS;
    let slot = (idx as usize) & (PAGE - 1);
    let word = slot >> 6;
    let bit = 1u64 << (slot & 63);
    let bits = marks.entry(page_idx).or_insert([0u64; PAGE / 64]);
    if bits[word] & bit == 0 {
        bits[word] |= bit;
        stack.push(idx);
    }
}

impl<'a> StorePin<'a> {
    /// The underlying store.
    #[inline]
    pub fn store(&self) -> &'a Store {
        self.store
    }

    /// The node of a handle of this store (None: an immediate, a handle of
    /// another store, or no such live node).
    #[inline]
    pub fn node(&self, h: u64) -> Option<&Node> {
        if tag(h) != TAG_NODE || (h >> TAG_BITS) & ((1 << STORE_BITS) - 1) != self.store.id {
            return None;
        }
        let i = (h >> INDEX_SHIFT).checked_sub(1)?;
        self.pages.get_index(i)
    }

    /// The node of a handle this store produced (panics otherwise: a
    /// compiler defect).
    #[inline]
    pub(crate) fn get(&self, h: u64) -> &Node {
        self.node(h).unwrap_or_else(|| panic!("value store {}: invalid handle {h:#x}", self.store.uid))
    }

    /// Whether `h` is a valid handle of this store (an immediate with a
    /// published symbol, or a live node of this store).
    #[inline]
    pub fn is_valid(&self, h: u64) -> bool {
        match tag(h) {
            TAG_NODE => self.node(h).is_some(),
            _ => immediate_value(h).is_some(),
        }
    }

    fn assert_valid(&self, h: u64) {
        assert!(self.is_valid(h), "value store {}: invalid handle {h:#x}", self.store.uid);
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
        let slot = (fmix64(h ^ self.store.uid.rotate_left(29)) as usize) & (ROOT_SLOTS - 1);
        let hit = ROOTS.with(|c| match &c.borrow()[slot] {
            Some((u, g, k, v)) if *u == self.store.uid && *g == self.gc_gen && *k == h => Some(v.clone()),
            _ => None,
        });
        if let Some(v) = hit {
            return v;
        }
        let v = thaw_cached(self, h);
        ROOTS.with(|c| c.borrow_mut()[slot] = Some((self.store.uid, self.gc_gen, h, v.clone())));
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
        self.intern_impl(body, None)
    }

    /// Publish a validated node body at exact index `idx` (used by sparse
    /// snapshot restoration). Returns an existing handle if an identical
    /// body is already present.
    pub(crate) fn intern_at(&self, idx: u64, body: Body) -> Result<u64, StoreError> {
        self.intern_impl(body, Some(idx))
    }

    fn intern_impl(&self, body: Body, fixed_index: Option<u64>) -> Result<u64, StoreError> {
        // Publication is the trust boundary for recursive readers. No
        // public constructor may hide an unchecked word inside a node.
        let check = |h: &u64| if self.is_valid(*h) { Ok(()) } else { Err(StoreError::InvalidHandle(*h)) };
        match &body {
            Body::Set(es) | Body::Tuple(es) | Body::Fcn(es, _) => es.iter().try_for_each(check)?,
            Body::Record(fs) => fs.iter().map(|(_, h)| h).try_for_each(check)?,
            Body::Int(_) | Body::Interval(..) => {}
        }
        let exact = exact_hash(&body);
        let shard = &self.store.shards[(exact >> (64 - SHARD_BITS)) as usize];
        if fixed_index.is_none() {
            if let Some(h) = self.find(shard, exact, &body) {
                return Ok(h);
            }
        }
        // (Outside the lock: the digest reads only published children.)
        let digest = self.body_digest(&body);
        let mut index = shard.0.lock().unwrap_or_else(|e| e.into_inner());
        let candidates = |index: &HashMap<u64, Ids, _>| -> Option<u64> {
            let ids: &[u64] = match index.get(&exact)? {
                Ids::One(i) => std::slice::from_ref(i),
                Ids::Many(is) => is,
            };
            ids.iter().map(|&i| self.store.handle_of(i)).find(|&h| self.get(h).body == body)
        };
        if let Some(h) = candidates(&index) {
            return Ok(h);
        }
        let size = std::mem::size_of::<OnceLock<Node>>() + body.bytes();
        let prev = self
            .store
            .bytes
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |cur| cur.checked_add(size).filter(|&n| n <= self.store.budget));
        let Ok(prev) = prev else {
            STORE_FULL_HIT.with(|f| f.set(true));
            if self.store.gc_active.load(Ordering::Relaxed) > 0 {
                self.store.gc_requested.store(true, Ordering::Release);
            } else {
                self.store.full.store(true, Ordering::Relaxed);
            }
            return Err(StoreError::Full);
        };
        let i = match fixed_index {
            Some(idx) => idx,
            None => match self.claim_index() {
                Ok(idx) => idx,
                Err(e) => {
                    self.store.bytes.fetch_sub(size, Ordering::Relaxed);
                    STORE_FULL_HIT.with(|f| f.set(true));
                    if self.store.gc_active.load(Ordering::Relaxed) > 0 {
                        self.store.gc_requested.store(true, Ordering::Release);
                    } else {
                        self.store.full.store(true, Ordering::Relaxed);
                    }
                    return Err(e);
                }
            },
        };
        let Some(page) = self.pages.get_or_init_page(i) else {
            self.store.bytes.fetch_sub(size, Ordering::Relaxed);
            STORE_FULL_HIT.with(|f| f.set(true));
            self.store.full.store(true, Ordering::Relaxed);
            return Err(StoreError::Full);
        };
        let s = (i as usize) & (PAGE - 1);
        let node = Node { digest, body, domain: OnceLock::new(), elems: OnceLock::new() };
        assert!(page[s].set(node).is_ok(), "value store: node slot {i} written twice");
        match index.get_mut(&exact) {
            None => {
                index.insert(exact, Ids::One(i));
                self.store.index_bytes.fetch_add(24, Ordering::Relaxed);
            }
            Some(Ids::Many(is)) => is.push(i),
            Some(ids @ Ids::One(_)) => {
                let Ids::One(j) = *ids else { unreachable!() };
                *ids = Ids::Many(vec![j, i]);
            }
        }
        self.store.live_nodes.fetch_add(1, Ordering::Relaxed);
        if fixed_index.is_none() && prev + size > self.store.soft_limit.load(Ordering::Relaxed) {
            self.store.gc_requested.store(true, Ordering::Release);
        }
        Ok(self.store.handle_of(i))
    }

    /// Claim the next monotonic node index, reserving and initializing any new
    /// overflow directory (`d >= 1`) *before* advancing `self.store.next` so a
    /// failed directory reservation never consumes an index or leaves an
    /// uncharged hole under concurrent insertion.
    fn claim_index(&self) -> Result<u64, StoreError> {
        loop {
            let cur = self.store.next.load(Ordering::Relaxed);
            if cur >= MAX_NODES {
                return Err(StoreError::Full);
            }
            let d = ((cur >> PAGE_BITS) >> DIR_BITS) as usize;
            if d == 0 || self.pages.has_overflow_dir(d) {
                if self.store.next.compare_exchange_weak(cur, cur + 1, Ordering::Relaxed, Ordering::Relaxed).is_ok() {
                    return Ok(cur);
                }
                continue;
            }
            if !self.reserve_overflow_dir(d) {
                return Err(StoreError::Full);
            }
        }
    }

    #[cold]
    #[inline(never)]
    fn reserve_overflow_dir(&self, d: usize) -> bool {
        let _guard = self.store.dir_init.lock().unwrap_or_else(|e| e.into_inner());
        if self.pages.has_overflow_dir(d) {
            return true;
        }
        let dir_bytes = DIR * std::mem::size_of::<OnceLock<Box<Page>>>();
        if self
            .store
            .bytes
            .fetch_update(Ordering::Relaxed, Ordering::Relaxed, |cur| cur.checked_add(dir_bytes).filter(|&n| n <= self.store.budget))
            .is_err()
        {
            return false;
        }
        if !self.pages.init_overflow_dir(d) {
            self.store.bytes.fetch_sub(dir_bytes, Ordering::Relaxed);
            return false;
        }
        true
    }

    fn find(&self, shard: &Shard, exact: u64, body: &Body) -> Option<u64> {
        let index = shard.0.lock().unwrap_or_else(|e| e.into_inner());
        let ids: &[u64] = match index.get(&exact)? {
            Ids::One(i) => std::slice::from_ref(i),
            Ids::Many(is) => is,
        };
        ids.iter().map(|&i| self.store.handle_of(i)).find(|&h| self.get(h).body == *body)
    }

    /// The semantic digest of a body (see `digest_of_value` for the
    /// algebra; both must agree).
    fn body_digest(&self, body: &Body) -> u64 {
        match body {
            Body::Int(i) => int_digest(*i),
            Body::Set(es) => {
                let mut d = composite_start(D_SET, es.len());
                es.iter().for_each(|e| d.word(self.digest(*e)));
                d.finish()
            }
            Body::Interval(lo, hi) => {
                let n = if hi < lo { 0 } else { (hi - lo + 1) as usize };
                let mut d = composite_start(D_SET, n);
                for i in 0..n as i64 {
                    d.word(int_digest(lo + i));
                }
                d.finish()
            }
            Body::Tuple(es) => {
                let mut d = composite_start(D_TUPLE, es.len());
                es.iter().for_each(|e| d.word(self.digest(*e)));
                d.finish()
            }
            Body::Record(fs) => {
                let mut d = composite_start(D_RECORD, fs.len());
                for (k, e) in fs.iter() {
                    d.word(k.text_hash());
                    d.word(self.digest(*e));
                }
                d.finish()
            }
            Body::Fcn(kv, _) => {
                let n = kv.len() / 2;
                let (keys, vals) = kv.split_at(n);
                match fcn_alias(keys) {
                    Alias::Tuple => {
                        let mut d = composite_start(D_TUPLE, n);
                        vals.iter().for_each(|e| d.word(self.digest(*e)));
                        d.finish()
                    }
                    Alias::Record => {
                        let mut d = composite_start(D_RECORD, n);
                        for (k, e) in keys.iter().zip(vals) {
                            let s = symbol(*k).expect("invalid string key");
                            d.word(s.text_hash());
                            d.word(self.digest(*e));
                        }
                        d.finish()
                    }
                    Alias::Fcn => {
                        let mut d = composite_start(D_FCN, n);
                        for (k, e) in keys.iter().zip(vals) {
                            d.word(self.digest(*k));
                            d.word(self.digest(*e));
                        }
                        d.finish()
                    }
                }
            }
        }
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

fn bool_digest(b: bool) -> u64 {
    let mut d = Digest::new();
    d.word(D_BOOL);
    d.word(b as u64);
    d.finish()
}

fn symbol_digest(tag: u64, s: &Sym) -> u64 {
    let mut d = Digest::new();
    d.word(tag);
    d.word(s.text_hash());
    d.finish()
}

/// Start a composite digest: its kind tag and child count, followed by the
/// children's digests in order. `body_digest` (stored bodies) and
/// `value_digest` (owned values) share this layout so their results agree.
fn composite_start(tag: u64, n: usize) -> Digest {
    let mut d = Digest::new();
    d.word(tag);
    d.word(n as u64);
    d
}

/// The digest of an immediate handle.
fn scalar_digest(h: u64) -> u64 {
    match tag(h) {
        TAG_INT => int_digest(as_int(h).expect("immediate integer handle")),
        TAG_BOOL => bool_digest(h >> TAG_BITS != 0),
        TAG_STR => symbol_digest(D_STR, &symbol(h).expect("invalid symbol handle")),
        TAG_MODEL_VALUE => symbol_digest(D_MV, &symbol(h).expect("invalid symbol handle")),
        _ => unreachable!("not an immediate handle"),
    }
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
    /// Direct-mapped per-thread cache by `(store uid, gc_gen, handle)`.
    static THAWED: std::cell::RefCell<Vec<Option<(u64, u64, u64, Value)>>> = std::cell::RefCell::new(vec![None; THAW_SLOTS]);
    /// Thawed slot values (`StorePin::thaw_slot`), direct-mapped like `THAWED`.
    static ROOTS: std::cell::RefCell<Vec<Option<(u64, u64, u64, Value)>>> = std::cell::RefCell::new(vec![None; ROOT_SLOTS]);
}

/// `thaw_node`, with a direct-mapped per-thread cache by `(store, gc_gen, handle)`.
fn thaw_cached(pin: &StorePin<'_>, h: u64) -> Value {
    let slot = (fmix64(h ^ pin.store.uid.rotate_left(17)) as usize) & (THAW_SLOTS - 1);
    let hit = THAWED.with(|c| match &c.borrow()[slot] {
        Some((u, g, k, v)) if *u == pin.store.uid && *g == pin.gc_gen && *k == h => Some(v.clone()),
        _ => None,
    });
    if let Some(v) = hit {
        return v;
    }
    let v = pin.thaw_node(h);
    THAWED.with(|c| c.borrow_mut()[slot] = Some((pin.store.uid, pin.gc_gen, h, v.clone())));
    v
}

/// The semantic digest of a value outside any store, computed directly from
/// the owned value: the result equals `Store::digest(s.freeze(v)?)` for any
/// store `s` without creating one. The compiled tier fingerprints VIEW values
/// and permuted `Ref` values that do not fit the store with this; the store
/// tests use it as an independent digest oracle.
pub fn digest_of_value(v: &Value) -> Result<u64, StoreError> {
    value_digest(v)
}

/// The function alias of an owned value's keys (the `Value` counterpart of
/// `fcn_alias` on stored key handles).
fn value_fcn_alias(ps: &[(Value, Value)]) -> Alias {
    match (ps.first(), ps.last()) {
        (None, _) => Alias::Tuple,
        (Some((Value::Int(1), _)), Some((Value::Int(last), _))) if *last == ps.len() as i64 => Alias::Tuple,
        (Some((Value::Str(_), _)), _) => Alias::Record,
        _ => Alias::Fcn,
    }
}

/// `body_digest` over an owned value, with the same tags, child order and
/// aliases (an interval is a set of its integers; an enumerated function with
/// keys `1..n` is a tuple and with string keys a record). Lazy values are
/// normalized first, as `Store::freeze` does.
fn value_digest(v: &Value) -> Result<u64, StoreError> {
    Ok(match v {
        Value::Int(i) => int_digest(*i),
        Value::Bool(b) => bool_digest(*b),
        Value::Str(s) => symbol_digest(D_STR, s),
        Value::ModelValue(s) => symbol_digest(D_MV, s),
        Value::Set(es) => {
            let mut d = composite_start(D_SET, es.len());
            for e in es.iter() {
                d.word(value_digest(e)?);
            }
            d.finish()
        }
        Value::Interval(lo, hi) => {
            let n = if hi < lo { 0 } else { (hi - lo + 1) as usize };
            let mut d = composite_start(D_SET, n);
            for i in 0..n as i64 {
                d.word(int_digest(lo + i));
            }
            d.finish()
        }
        Value::Tuple(es) => {
            let mut d = composite_start(D_TUPLE, es.len());
            for e in es.iter() {
                d.word(value_digest(e)?);
            }
            d.finish()
        }
        Value::Record(fs) => {
            let mut d = composite_start(D_RECORD, fs.len());
            for (k, e) in fs.iter() {
                d.word(k.text_hash());
                d.word(value_digest(e)?);
            }
            d.finish()
        }
        Value::Fcn(ps, _) => {
            let n = ps.len();
            match value_fcn_alias(ps) {
                Alias::Tuple => {
                    let mut d = composite_start(D_TUPLE, n);
                    for (_, x) in ps.iter() {
                        d.word(value_digest(x)?);
                    }
                    d.finish()
                }
                Alias::Record => {
                    let mut d = composite_start(D_RECORD, n);
                    for (k, x) in ps.iter() {
                        let Value::Str(s) = k else { unreachable!("record keys are strings") };
                        d.word(s.text_hash());
                        d.word(value_digest(x)?);
                    }
                    d.finish()
                }
                Alias::Fcn => {
                    let mut d = composite_start(D_FCN, n);
                    for (k, x) in ps.iter() {
                        d.word(value_digest(k)?);
                        d.word(value_digest(x)?);
                    }
                    d.finish()
                }
            }
        }
        Value::LazySet(_) | Value::LazyFcn(_) => {
            let n = v.normalize().map_err(|e| StoreError::NotFinite(e.to_string()))?;
            if !n.is_normal() {
                return Err(StoreError::NotFinite(format!("{v}")));
            }
            value_digest(&n)?
        }
    })
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
