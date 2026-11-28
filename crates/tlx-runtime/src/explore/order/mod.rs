//! The representatives of the fingerprint classes in a search of several
//! workers when the fingerprint identifies a class of states rather than a
//! state (VIEW, SYMMETRY: `Model::coarse_fingerprint`).
//!
//! The first state of a class found in BFS order represents it (as in TLC
//! with one worker): it is checked against the invariants, expanded, and on
//! the traces; another state of the class may enable other actions, so the
//! results depend on that choice. With one worker, the first found is the
//! first in BFS order; in the level-synchronous search, it would depend on
//! the scheduling. Instead every successor of a state of level k whose
//! class is new at level k + 1 (a candidate) gets its place in BFS order,
//! its key `(position of its parent in level k, index of the successor
//! among the parent's)`, and the class keeps the least key offered
//! (`Order::best`, which the seen-set insertion is serialized with). A
//! worker buffers its candidates that had the least key when offered; once
//! all workers have expanded level k, each keeps those whose key is still
//! the least (`WorkerState::resolve`): they are logged, checked against the
//! invariants and queued as one worker would have done.
//!
//! Positions: the states of a level are numbered in BFS order, i.e. by key.
//! Resolving a level records, for every state kept, its parent's position
//! and its rank among the parent's states kept (a `Table` per worker, by
//! trace-log entry: a worker logs the states it keeps one after the
//! other), and per parent the number of states kept (`Order::counts`);
//! their prefix sums, computed before the next level (`Order::advance`),
//! give each parent the position of its first state, hence every state its
//! position (`Positions::pos`).
//!
//! Compact layouts:
//! - Keys `(pos, idx)` pack into a single order-preserving `u64`
//!   (`(pos << 24) | idx` for `pos < (1 << 40) - 1` and `idx < (1 << 24)`),
//!   with `u64::MAX` as an overflow sentinel backed by a cold side table of
//!   exact `(u64, u64)` tuples. Mixed fast/overflow comparisons always unpack
//!   so `(5, 1 << 24) < (6, 0)` holds strictly.
//! - `OrderLocal` stores candidate metadata in SoA vectors (`keys`, `ats`,
//!   `fps`: 20 B/cand) plus a cold overflow map keyed by candidate index.
//! - `ranks`, `Table` entries, and `Counts` use 32-bit storage in the common
//!   case (4 B/cand, 8 B/state, 4 B/parent) with exact 64-bit fallbacks.
//!
//! The candidates, the classes' keys and the tables cost memory and time
//! only in this mode; otherwise the fingerprint is the state and the first
//! inserter is as good as any.
//!
//! The states of the candidates of a level are held until the level is
//! resolved, i.e. a whole level of new states at a time, which is what a
//! model with wide states and wide levels pays for: `CandStore` (`store.rs`)
//! keeps them the way the queue does, XOR-varint encoded (10-100x smaller),
//! and `resolve` visits the candidates in the order they were offered, the
//! order the encoded states can be decoded in. The keys, not that order,
//! give the states of the level their BFS positions and the counts.
//!
//! Most successors are of classes already found (KVSSafetyMedium: 95% of
//! them). One of a class found at an earlier level is not a candidate;
//! telling it from one of a class new at this level should not write shared
//! memory, or every successor moves a cache line between the cores (the
//! shard's lock, at least). So `offer` takes the
//! lock only for a class that may be new at this level: one that is not in
//! the seen set yet, or whose bit is set in `NewClasses`, a filter on the
//! fingerprints of the classes inserted into the seen set at this level.
//!
//! Counting the coverage (`Options::coverage`) uses this mode too, with a
//! fingerprint that is the state: the action credited with a new state is
//! the representative's. The liveness edges are then recorded as by one
//! worker: a state expanded records its steps (`EdgeRec::successor`, `end`,
//! which do not depend on the representatives), and a candidate kept gets
//! the atoms of the tableaux evaluated when it is resolved (`EdgeRec::found`),
//! as one worker does when it finds a new state.

mod positions;
mod store;

use std::sync::atomic::Ordering;
use std::sync::Arc;

use parking_lot::Mutex;
use tlx_base::hash::{FxMap, IdMap as FpMap};
use tlx_base::padded::Padded;

pub use positions::Positions;
use positions::{map_bytes, Charge, Counts, NewClasses, Table, TableEntries};
pub(super) use store::CandStore;
use store::Meta;

use super::coverage::{bump, generated_at};
use super::frontier::Task;
use super::tracelog::NO_PARENT;
use super::worker::{edge_error, WorkerState};
use super::{fp_set_full, invariant_failure, Failure, Outcome, OutdegreeHist, SP_GROW};
use crate::fpset::Full;
use crate::mem::{Gauge, Part};
use crate::model::Model;
use crate::queue::StateCodec;
use crate::stats::{self, T};

/// The place of a candidate in BFS order: the position of its parent in
/// the parent's level, and the index of the successor among the parent's
/// successors (as generated).
type Key = (u64, u64);

/// Low bits reserved for `succ_idx` inside a packed `u64` key `(pos << 24) | idx`.
const IDX_BITS: u32 = 24;
const IDX_LIMIT: u64 = 1u64 << IDX_BITS;
const IDX_MASK: u64 = IDX_LIMIT - 1;
/// Upper bound (exclusive) on inline `parent_pos`; reserving `(1 << 40) - 1`
/// guarantees `OVERFLOW_KEY = u64::MAX` never collides with a valid inline key.
const POS_LIMIT: u64 = (1u64 << (64 - IDX_BITS)) - 1;
/// Packed-key sentinel indicating the exact `(u64, u64)` key lives in a cold
/// overflow side table.
const OVERFLOW_KEY: u64 = u64::MAX;

#[inline]
fn pack_key((pos, idx): Key) -> u64 {
    if pos < POS_LIMIT && idx < IDX_LIMIT {
        (pos << IDX_BITS) | idx
    } else {
        OVERFLOW_KEY
    }
}

#[inline]
fn unpack_fast(packed: u64) -> Key {
    debug_assert_ne!(packed, OVERFLOW_KEY);
    (packed >> IDX_BITS, packed & IDX_MASK)
}

/// Shards of `Order::best` (chosen by bits of the fingerprint the shard's
/// map does not use much: hashbrown takes the low and the top bits).
const SHARDS: usize = 256;

#[inline]
fn shard(fp: u64) -> usize {
    (fp >> 32) as usize % SHARDS
}

/// One shard of `Order::best`: 8 B packed keys in `packed`, plus a cold side
/// table for keys whose `pos >= POS_LIMIT` or `idx >= IDX_LIMIT`.
#[derive(Default)]
struct BestShard {
    packed: FpMap<u64>,
    overflow: Option<Box<FpMap<Key>>>,
}

impl BestShard {
    /// If `fp` is already in this shard, update it when `key` is strictly less
    /// than its current best and return `Some(updated)`; return `None` if `fp`
    /// is not yet present.
    #[inline]
    fn update_if_less(&mut self, fp: u64, key: Key, packed_key: u64) -> Option<bool> {
        let slot = self.packed.get_mut(&fp)?;
        if *slot != OVERFLOW_KEY && packed_key != OVERFLOW_KEY {
            let less = packed_key < *slot;
            if less {
                *slot = packed_key;
            }
            return Some(less);
        }
        Some(self.update_if_less_cold(fp, key, packed_key))
    }

    #[cold]
    #[inline(never)]
    fn update_if_less_cold(&mut self, fp: u64, key: Key, packed_key: u64) -> bool {
        let slot = self.packed.get_mut(&fp).expect("existing best entry");
        let cur = if *slot == OVERFLOW_KEY {
            *self.overflow.as_ref().and_then(|ov| ov.get(&fp)).expect("overflow best entry")
        } else {
            unpack_fast(*slot)
        };
        if key < cur {
            if packed_key == OVERFLOW_KEY {
                *slot = OVERFLOW_KEY;
                self.overflow.get_or_insert_with(Default::default).insert(fp, key);
            } else {
                *slot = packed_key;
                if let Some(ov) = &mut self.overflow {
                    ov.remove(&fp);
                }
            }
            true
        } else {
            false
        }
    }

    /// Insert a newly discovered class `fp` into this shard.
    #[inline]
    fn insert_new(&mut self, fp: u64, key: Key, packed_key: u64) {
        self.packed.insert(fp, packed_key);
        if packed_key == OVERFLOW_KEY {
            self.overflow.get_or_insert_with(Default::default).insert(fp, key);
        }
    }

    #[inline]
    fn get_packed(&self, fp: u64) -> Option<u64> {
        self.packed.get(&fp).copied()
    }

    fn get_key(&self, fp: u64) -> Option<Key> {
        let &packed = self.packed.get(&fp)?;
        if packed == OVERFLOW_KEY {
            self.overflow.as_ref().and_then(|ov| ov.get(&fp).copied())
        } else {
            Some(unpack_fast(packed))
        }
    }

    #[inline]
    fn is_empty_and_unallocated(&self) -> bool {
        self.packed.capacity() == 0 && self.overflow.is_none()
    }

    /// Drop the shard's backing hash table and overflow side table immediately
    /// so `Order::best` does not overlap with `resolve_kept`'s next-level tables.
    fn clear(&mut self) {
        self.packed = FpMap::default();
        self.overflow = None;
    }

    fn bytes(&self) -> usize {
        map_bytes(&self.packed) + self.overflow.as_ref().map_or(0, |ov| std::mem::size_of::<FpMap<Key>>() + map_bytes(ov))
    }
}

/// The shared state of the choice of representatives (see the module).
pub(super) struct Order {
    /// The classes new at the level being expanded: the least key offered.
    best: Box<[Padded<Mutex<BestShard>>]>,
    /// A filter on the classes new at the level being expanded (`None` once
    /// `release_after_expand` drops it before `resolve`).
    new: Mutex<Option<Arc<NewClasses>>>,
    /// The positions of the states of the level being expanded (`None` once
    /// `release_after_expand(true)` drops them on non-resumable runs).
    current: Mutex<Option<Arc<Positions>>>,
    /// Per state of the level being expanded (by position), the number of
    /// its successors kept.
    counts: Mutex<Option<Arc<Counts>>>,
    /// Per worker, its table of the states of the next level.
    next: Mutex<Vec<Option<Arc<Table>>>>,
    /// The memory of the candidates buffered by the workers (bytes, and
    /// the most at a time, for the memory budget and `-stats`), and each
    /// worker's capacity and shared metadata (updated on allocation).
    cand_bytes: Arc<Gauge>,
    best_parts: Box<[Part]>,
    shrink: std::sync::atomic::AtomicBool,
    /// Memory pressure: the workers write their full segments of
    /// candidates to disk (`CandStore`), while over the budget.
    spill: std::sync::atomic::AtomicBool,
    workers: usize,
}

impl Order {
    pub(super) fn new(workers: usize) -> Order {
        let gauge = Arc::new(Gauge::new());
        gauge.add(
            std::mem::size_of::<Order>()
                + SHARDS * (std::mem::size_of::<Padded<Mutex<BestShard>>>() + std::mem::size_of::<Part>())
                + workers * std::mem::size_of::<Option<Arc<Table>>>(),
        );
        Order {
            best: (0..SHARDS).map(|_| Padded(Mutex::new(BestShard::default()))).collect(),
            new: Mutex::new(None),
            current: Mutex::new(None),
            counts: Mutex::new(None),
            next: Mutex::new(vec![None; workers]),
            cand_bytes: gauge,
            best_parts: (0..SHARDS).map(|_| Part::default()).collect(),
            shrink: std::sync::atomic::AtomicBool::new(false),
            spill: std::sync::atomic::AtomicBool::new(false),
            workers,
        }
    }

    /// The memory of the candidates buffered by the workers (bytes, as
    /// published; for the memory budget's registry).
    pub(super) fn gauge(&self) -> &Arc<Gauge> {
        &self.cand_bytes
    }

    pub(super) fn shrink(&self) {
        self.shrink.store(true, Ordering::Relaxed);
    }

    fn shrinking(&self) -> bool {
        self.shrink.load(Ordering::Relaxed)
    }

    /// Have the workers write their full segments of candidates to disk
    /// from now on (`on`), or no more (under the budget again: only what
    /// exceeds it goes to disk, and is read back); whether this changed.
    pub(super) fn spill(&self, on: bool) -> bool {
        self.spill.swap(on, Ordering::Relaxed) != on
    }

    fn spilling(&self) -> bool {
        self.spill.load(Ordering::Relaxed)
    }

    /// Start with the states of the first level at `positions` (before the
    /// workers start).
    pub(super) fn start(&self, positions: Arc<Positions>) {
        positions.account(&self.cand_bytes);
        *self.counts.lock() = Some(Counts::zeros(positions.len, &self.cand_bytes));
        *self.new.lock() = Some(Arc::new(NewClasses::new(positions.len, &self.cand_bytes)));
        *self.current.lock() = Some(positions);
    }

    /// The positions of the states of the level being expanded.
    pub(super) fn current(&self) -> Arc<Positions> {
        self.current.lock().clone().expect("level positions active")
    }

    /// Release expansion-only shared metadata (`NewClasses`, and parent-level
    /// `Positions` when `release_current` is true because layout-miss resume
    /// archiving is inactive) once every worker has finished expanding the
    /// level.
    pub(super) fn release_after_expand(&self, release_current: bool) {
        *self.new.lock() = None;
        if release_current {
            *self.current.lock() = None;
        }
    }

    /// Release every `Order::best` shard's backing table and zero its gauge
    /// charge once all workers have finished `filter_candidates`, before
    /// `resolve_kept` allocates next-level tables. Idempotent.
    pub(super) fn clear_best(&self) {
        for (i, b) in self.best.iter().enumerate() {
            let mut b = b.lock();
            if b.is_empty_and_unallocated() {
                continue;
            }
            b.clear();
            self.best_parts[i].set(&self.cand_bytes, 0);
        }
    }

    /// The packed least key offered for class `fp` at this level.
    #[inline]
    fn best_packed(&self, fp: u64) -> Option<u64> {
        self.best[shard(fp)].lock().get_packed(fp)
    }

    /// The unpacked least key offered for class `fp` at this level (once every
    /// worker has expanded the level: the representative's).
    fn best_of(&self, fp: u64) -> Option<Key> {
        self.best[shard(fp)].lock().get_key(fp)
    }

    /// Make the next level (resolved by every worker) the current one:
    /// called by a single worker, the others waiting.
    pub(super) fn advance(&self) {
        // Drop old `current` (if kept for layout-miss resume) and old `counts`
        // before allocating next-level `first`, `Counts`, and `NewClasses`.
        *self.current.lock() = None;
        let mut counts = self.counts.lock();
        let (first, len) = counts.take().map_or_else(|| (Box::from([]), 0), |c| c.prefix_sums());
        let tables = std::mem::replace(&mut *self.next.lock(), vec![None; self.workers]);
        let positions = Arc::new(Positions::from_parts(tables, first, len));
        positions.account(&self.cand_bytes);
        *self.current.lock() = Some(positions);
        *counts = Some(Counts::zeros(len, &self.cand_bytes));
        *self.new.lock() = Some(Arc::new(NewClasses::new(len, &self.cand_bytes)));
        self.clear_best();
    }
}

/// While a level is resolved, the next level's segments are offered to the
/// disk every this many states queued (as `worker::TICK` while expanding).
const RESOLVE_TICK: usize = 1024;

/// Structure-of-arrays buffer of one worker's candidate metadata for a level:
/// 20 bytes per candidate (`keys` 8 B + `ats` 4 B + `fps` 8 B), plus a cold
/// side table of exact `(u64, u64)` keys for candidates whose packed key is
/// `OVERFLOW_KEY`.
#[derive(Default)]
struct CandBuf {
    /// Packed BFS keys `(pos << 24) | idx`, or `OVERFLOW_KEY`.
    keys: Vec<u64>,
    /// Indices returned by `CandStore::push`.
    ats: Vec<u32>,
    /// Class fingerprints.
    fps: Vec<u64>,
    /// Exact keys for candidate indices whose `keys[i] == OVERFLOW_KEY`.
    overflow: Option<Box<FxMap<usize, Key>>>,
}

impl CandBuf {
    #[inline]
    fn len(&self) -> usize {
        self.keys.len()
    }

    #[inline]
    fn push(&mut self, key: Key, at: u32, fp: u64) {
        let packed = pack_key(key);
        if packed == OVERFLOW_KEY {
            self.overflow.get_or_insert_with(Default::default).insert(self.keys.len(), key);
        }
        self.keys.push(packed);
        self.ats.push(at);
        self.fps.push(fp);
    }

    #[inline]
    fn has_overflow(&self) -> bool {
        self.overflow.as_ref().is_some_and(|ov| !ov.is_empty())
    }

    #[inline]
    fn key_at(&self, i: usize) -> Key {
        let packed = self.keys[i];
        if packed == OVERFLOW_KEY {
            self.overflow.as_ref().expect("overflow candidate key")[&i]
        } else {
            unpack_fast(packed)
        }
    }

    #[inline]
    fn pos_at(&self, i: usize) -> u64 {
        let packed = self.keys[i];
        if packed == OVERFLOW_KEY {
            self.overflow.as_ref().expect("overflow candidate key")[&i].0
        } else {
            packed >> IDX_BITS
        }
    }

    #[inline]
    fn at(&self, i: usize) -> u32 {
        self.ats[i]
    }

    #[inline]
    fn fp(&self, i: usize) -> u64 {
        self.fps[i]
    }

    /// Keep only candidates whose key still matches `order.best`, compacting
    /// the parallel vectors and remapping any surviving overflow indices.
    fn retain_best(&mut self, order: &Order) {
        let len = self.keys.len();
        let mut kept_overflow = Vec::new();
        let mut write = 0usize;
        for read in 0..len {
            let packed = self.keys[read];
            let fp = self.fps[read];
            let keep = if packed != OVERFLOW_KEY {
                order.best_packed(fp) == Some(packed)
            } else {
                let key = self.overflow.as_ref().expect("overflow candidate key")[&read];
                if order.best_of(fp) == Some(key) {
                    kept_overflow.push((write, key));
                    true
                } else {
                    false
                }
            };
            if keep {
                if write != read {
                    self.keys[write] = packed;
                    self.ats[write] = self.ats[read];
                    self.fps[write] = fp;
                }
                write += 1;
            }
        }
        self.keys.truncate(write);
        self.ats.truncate(write);
        self.fps.truncate(write);
        if let Some(ov) = &mut self.overflow {
            ov.clear();
            ov.extend(kept_overflow);
        }
    }

    fn clear(&mut self) {
        self.keys.clear();
        self.ats.clear();
        self.fps.clear();
        if let Some(ov) = &mut self.overflow {
            ov.clear();
        }
    }

    fn shrink_to_fit(&mut self) {
        self.keys.shrink_to_fit();
        self.ats.shrink_to_fit();
        self.fps.shrink_to_fit();
        if self.overflow.as_ref().is_some_and(|ov| ov.is_empty()) {
            self.overflow = None;
        } else if let Some(ov) = &mut self.overflow {
            ov.shrink_to_fit();
        }
    }

    fn bytes(&self) -> usize {
        self.keys.capacity() * std::mem::size_of::<u64>()
            + self.ats.capacity() * std::mem::size_of::<u32>()
            + self.fps.capacity() * std::mem::size_of::<u64>()
            + self.overflow.as_ref().map_or(0, |ov| std::mem::size_of::<FxMap<usize, Key>>() + map_bytes(ov))
    }
}

/// Per-kept-candidate rank among its parent's kept successors: 4 B/cand in the
/// common case (`<= u32::MAX`), widening to 8 B/cand if a single parent keeps
/// more than `u32::MAX` successors.
enum Ranks {
    Narrow(Vec<u32>),
    Wide(Vec<u64>),
}

impl Ranks {
    fn new(len: usize) -> Ranks {
        Ranks::Narrow(vec![0u32; len])
    }

    #[inline]
    fn set(&mut self, index: usize, rank: u64) {
        match self {
            Ranks::Narrow(v) => {
                if let Ok(r) = u32::try_from(rank) {
                    v[index] = r;
                } else {
                    self.widen();
                    let Ranks::Wide(w) = self else { unreachable!() };
                    w[index] = rank;
                }
            }
            Ranks::Wide(v) => v[index] = rank,
        }
    }

    #[cold]
    #[inline(never)]
    fn widen(&mut self) {
        if let Ranks::Narrow(v) = self {
            let wide: Vec<u64> = v.iter().map(|&x| x as u64).collect();
            *self = Ranks::Wide(wide);
        }
    }

    #[inline]
    fn get(&self, index: usize) -> u64 {
        match self {
            Ranks::Narrow(v) => v[index] as u64,
            Ranks::Wide(v) => v[index],
        }
    }

    fn bytes(&self) -> usize {
        match self {
            Ranks::Narrow(v) => v.capacity() * std::mem::size_of::<u32>(),
            Ranks::Wide(v) => v.capacity() * std::mem::size_of::<u64>(),
        }
    }
}

/// Compute per-parent ranks, store per-parent kept counts, update outdegree
/// histograms, and return `(ranks, wide_table)` for `resolve`.
fn rank_and_count_kept(
    cands: &CandBuf,
    counts: &Counts,
    outdegree: &mut OutdegreeHist,
    gauge: &Arc<Gauge>,
    scratch: &Charge,
) -> (Ranks, bool) {
    let n = u32::try_from(cands.len()).expect("candidate count fits in u32");
    let mut by_key: Vec<u32> = (0..n).collect();
    // Unstable sorting is in place (no auxiliary allocation).
    if cands.has_overflow() {
        by_key.sort_unstable_by_key(|&i| cands.key_at(i as usize));
    } else {
        by_key.sort_unstable_by_key(|&i| cands.keys[i as usize]);
    }
    let mut ranks = Ranks::new(cands.len());
    scratch.set(gauge, by_key.capacity() * std::mem::size_of::<u32>() + ranks.bytes());
    let mut k = 0u64;
    let mut prev_pos = 0u64;
    let mut max_pos = 0u64;
    let mut max_rank = 0u64;
    for (j, &i) in by_key.iter().enumerate() {
        let pos = cands.pos_at(i as usize);
        k = if j > 0 && prev_pos == pos { k + 1 } else { 0 };
        prev_pos = pos;
        ranks.set(i as usize, k);
        max_pos = max_pos.max(pos);
        max_rank = max_rank.max(k);
        if by_key.get(j + 1).is_none_or(|&next| cands.pos_at(next as usize) != pos) {
            counts.store(pos as usize, k + 1, gauge);
            outdegree.replace(0, k + 1);
        }
    }
    if matches!(ranks, Ranks::Wide(_)) {
        scratch.set(gauge, by_key.capacity() * std::mem::size_of::<u32>() + ranks.bytes());
    }
    drop(by_key);
    scratch.set(gauge, ranks.bytes());
    (ranks, max_pos > u32::MAX as u64 || max_rank > u32::MAX as u64)
}

/// A worker's part of the choice of representatives.
pub(super) struct OrderLocal<'m, S> {
    /// The positions of the level being expanded (`Some` only while expanding),
    /// and the counts of its states' successors kept (`Some` from `order_level`
    /// until `resolve_kept` consumes them).
    positions: Option<Arc<Positions>>,
    counts: Option<Arc<Counts>>,
    /// The filter on the classes new at the level (`Some` only while expanding).
    new: Option<Arc<NewClasses>>,
    /// The position of the state being expanded.
    pos: u64,
    /// The candidates buffered at this level, in the order they were offered.
    cands: CandBuf,
    /// Their states.
    store: CandStore<'m, S>,
    /// Separate charges for `cands` and `store` so `filter_candidates` can
    /// update `cands` while `store` is deposited in `Shared::gc_roots`.
    cands_charge: Charge,
    store_charge: Charge,
}

impl<'m, S> OrderLocal<'m, S> {
    /// The part of a worker, its candidates' states encoded by `codec` (if
    /// any) in segments of `seg_bytes`.
    pub(super) fn new(codec: Option<&'m dyn StateCodec<S>>, seg_bytes: usize) -> OrderLocal<'m, S> {
        OrderLocal {
            positions: None,
            counts: None,
            new: None,
            pos: 0,
            cands: CandBuf::default(),
            store: CandStore::new(codec, seg_bytes),
            cands_charge: Charge::default(),
            store_charge: Charge::default(),
        }
    }

    fn account(&self, gauge: &Arc<Gauge>) {
        self.cands_charge.set(gauge, self.cands.bytes());
        self.store_charge.set(gauge, self.store.bytes());
    }

    pub(super) fn take_store(&mut self) -> CandStore<'m, S> {
        std::mem::replace(&mut self.store, CandStore::new(None, 0))
    }

    pub(super) fn restore_store(&mut self, store: CandStore<'m, S>) {
        self.store = store;
    }
}

impl<M: Model> WorkerState<'_, '_, M> {
    /// Before expanding a level: latch its positions, counts, and new-class filter.
    pub(super) fn order_level(&mut self) {
        if let (Some(o), Some(order)) = (&mut self.order, &self.shared.order) {
            o.positions = Some(order.current());
            o.counts = Some(order.counts.lock().clone().expect("level counts active"));
            o.new = Some(order.new.lock().clone().expect("level new-classes active"));
            if order.shrinking() {
                o.cands.shrink_to_fit();
                o.store.shrink();
            }
            o.account(&order.cand_bytes);
        }
    }

    /// Right after expanding a level: release this worker's handles to
    /// parent-level `Positions` and `NewClasses` before `resolve`.
    pub(super) fn release_expand_order(&mut self) {
        if let Some(o) = &mut self.order {
            o.positions = None;
            o.new = None;
        }
    }

    /// Under memory pressure (`Order::spill`, every `TICK` states): write
    /// the full segments of the candidates to disk and publish their
    /// memory. An IO error stops the search.
    pub(super) fn spill_candidates(&mut self) {
        let (Some(o), Some(order)) = (&mut self.order, &self.shared.order) else { return };
        if !order.spilling() {
            return;
        }
        let r = o.store.spill(&self.shared.opts.spill);
        o.store_charge.set(&order.cand_bytes, o.store.bytes());
        if let Err(e) = r {
            self.shared.fail(Outcome::Io(e.0), NO_PARENT);
        }
    }

    /// Before expanding `task`: its position.
    #[inline]
    pub(super) fn order_task(&mut self, task: &Task<M::State>) {
        if let Some(o) = &mut self.order {
            o.pos = o.positions.as_ref().expect("level positions active").pos(task.log);
        }
    }

    /// Offer successor `t` (fingerprint `fp`, generated by `action`, index
    /// `idx` among the successors of `task`, satisfying the constraints) as
    /// the representative of its class, inserting the class into the seen
    /// set if new. Buffers it if it is the least key of a class new at this
    /// level so far.
    pub(super) fn offer<const STATS: bool>(
        &mut self,
        task: &Task<M::State>,
        t: M::State,
        fp: u64,
        action: u32,
        idx: u64,
    ) -> Result<(), Failure> {
        let shared = self.shared;
        let order = shared.order.as_ref().expect("ordered search");
        let o = self.order.as_mut().expect("ordered search");
        let key = (o.pos, idx);
        let packed_key = pack_key(key);
        let seen = &shared.seen;
        let new = o.new.as_ref().expect("level new-classes active");
        // A class found at an earlier level, told without writing shared
        // memory (see `NewClasses`; the disk tier is asked by `insert` only).
        if !seen.spilling() && seen.contains(fp) && !new.may_hold(fp) {
            return Ok(());
        }
        let high = || shared.control().request(SP_GROW);
        let mut parked = false;
        let s = shard(fp);
        let keep = loop {
            // (The class is inserted into the seen set and into `best`
            // atomically: a class in the seen set and not in `best` is of
            // an earlier level.)
            let mut best = order.best[s].lock();
            if let Some(less) = best.update_if_less(fp, key, packed_key) {
                if less && packed_key == OVERFLOW_KEY {
                    order.best_parts[s].set(&order.cand_bytes, best.bytes());
                }
                break less;
            }
            new.mark(fp);
            match if STATS { stats::fp_insert(seen, self.me, fp, high) } else { seen.insert_by(self.me, fp, &mut 0, high) } {
                Ok(true) => {
                    let capacity = best.packed.capacity();
                    best.insert_new(fp, key, packed_key);
                    if best.packed.capacity() != capacity || packed_key == OVERFLOW_KEY {
                        order.best_parts[s].set(&order.cand_bytes, best.bytes());
                    }
                    break true;
                }
                Ok(false) => break false,
                Err(Full) => {
                    // At its hard limit: grow the set at a safepoint (not
                    // holding the shard) and insert again (see
                    // `insert_when_full`).
                    drop(best);
                    if !seen.can_make_room() || (parked && shared.control().stopped()) {
                        return Err(fp_set_full(seen));
                    }
                    shared.control().request(SP_GROW);
                    shared.mid_task_parked.fetch_add(1, Ordering::AcqRel);
                    shared.safepoint.park(|req, crew| shared.serve_safepoint(req, crew));
                    shared.mid_task_parked.fetch_sub(1, Ordering::AcqRel);
                    parked = true;
                }
            }
        };
        if keep {
            let before_store = o.store.bytes();
            let before_cands = o.cands.bytes();
            let at = o.store.push(t, fp, Meta { parent: task.log, depth: task.depth + 1, action });
            o.cands.push(key, at, fp);
            let after_store = o.store.bytes();
            if after_store != before_store {
                o.store_charge.set(&order.cand_bytes, after_store);
            }
            let after_cands = o.cands.bytes();
            if after_cands != before_cands {
                o.cands_charge.set(&order.cand_bytes, after_cands);
            }
        }
        Ok(())
    }

    /// Phase 1 of representative resolution (after every worker has expanded the
    /// level): retain only candidates whose key still matches `Order::best`.
    /// This is the sole read of `Order::best`, so `Order::clear_best()` can
    /// release all shards before `resolve_kept()` allocates next-level tables.
    pub(super) fn filter_candidates(&mut self) {
        let (Some(o), Some(order)) = (&mut self.order, &self.shared.order) else { return };
        o.cands.retain_best(order);
        if order.shrinking() {
            let before = o.cands.bytes();
            o.cands.shrink_to_fit();
            stats::add_count("representative buffer bytes reclaimed", before.saturating_sub(o.cands.bytes()) as u64);
        }
        o.cands_charge.set(&order.cand_bytes, o.cands.bytes());
    }

    /// Phase 2 of representative resolution (after `Order::clear_best()` has
    /// released `Order::best`): rank the kept candidates in BFS order, log,
    /// count (outdegrees, depth, coverage), check and queue them, and install
    /// this worker's next-level position `Table`. A failure stops the search.
    pub(super) fn resolve_kept(&mut self) {
        let shared = self.shared;
        let (Some(o), Some(order)) = (&mut self.order, &shared.order) else { return };
        o.account(&order.cand_bytes);
        // (Both are put back below, their buffers kept for the next level.)
        let mut cands = std::mem::take(&mut o.cands);
        let counts = o.counts.take().expect("level counts active");
        let mut store = std::mem::replace(&mut o.store, CandStore::new(None, 0));
        // The successors kept per parent: their ranks, counts, and the
        // outdegrees of the parents (counted as 0 when expanded). The
        // candidates are visited by key (as by one worker); their states,
        // which are visited in the order they were offered below, do not
        // take part.
        let scratch = Charge::default();
        let (ranks, wide_table) = rank_and_count_kept(&cands, &counts, &mut self.outdegree, &order.cand_bytes, &scratch);
        drop(counts);
        let model = shared.model;
        let start = self.shard.log.len();
        let mut entries = TableEntries::with_capacity(cands.len(), wide_table);
        let table_charge = Charge::default();
        table_charge.set(&order.cand_bytes, entries.bytes());
        for i in 0..cands.len() {
            if shared.store_gc.is_some() {
                if shared.store_gc.is_some_and(|gc| gc.needs_gc()) {
                    shared.control().request(super::SP_STORE_GC);
                }
                if shared.control().get() != 0 {
                    self.order.as_mut().unwrap().restore_store(store);
                    let go = self.proceed();
                    store = self.order.as_mut().unwrap().take_store();
                    if !go {
                        break;
                    }
                }
            } else if shared.control().stopped() {
                break;
            }
            let at = cands.at(i);
            let fp = cands.fp(i);
            let pos = cands.pos_at(i);
            let (state, Meta { parent, depth, action }) = match store.get(at, fp, &shared.opts.spill) {
                Ok(x) => x,
                Err(e) => {
                    shared.fail(Outcome::Io(e.0), NO_PARENT);
                    break;
                }
            };
            let r = self.append_log(parent, fp);
            entries.push(pos, ranks.get(i));
            bump(&self.slot.cov, generated_at(action) + 1);
            // The atoms of the tableaux on a new state (recording the
            // liveness edges: the fingerprint is the state then, see
            // `explore`), as one worker evaluates them when it finds it.
            if self.shard.edges.is_some() {
                let first = self.shard.edges.as_mut().map_or(Ok(()), |e| e.found(&state));
                let edge_res = match first {
                    Err(e) if e.is_store_full() => {
                        self.order.as_mut().unwrap().restore_store(store);
                        let r = self.retry_edge(&[&state], e, |edges| edges.found(&state));
                        store = self.order.as_mut().unwrap().take_store();
                        r
                    }
                    other => other,
                };
                if let Err((outcome, at)) = edge_error(model, edge_res, parent) {
                    shared.fail(outcome, at);
                    break;
                }
            }
            // Counted before the checks: TLC reports the depth of a
            // violating state.
            if depth > self.max_depth {
                self.max_depth = depth;
                self.slot.max_depth.store(depth as u64, Ordering::Relaxed);
            }
            // (The observer is not told the parent: only its log entry is kept.)
            if let Some(o) = shared.observer {
                o.on_new_state(&state, fp, depth, None);
            }
            let span = stats::span();
            // (`TLCExt!Trace` on the state: its parent's path and the state.)
            let f = if let Some(gc) = shared.store_gc {
                let mut store_opt = Some(store);
                let mut stopped = false;
                let res = shared.with_path_of(parent, || {
                    super::invariant_failure_gc(model, &state, r, &mut |force_drop| {
                        self.order.as_mut().unwrap().restore_store(store_opt.take().unwrap());
                        self.park_for_store_gc(&[&state], force_drop);
                        store_opt = Some(self.order.as_mut().unwrap().take_store());
                        stopped = shared.control().stopped();
                        !stopped
                    })
                });
                store = store_opt.unwrap();
                if matches!(&res, Some((Outcome::Error(e), _)) if e.is_store_full()) && !stopped {
                    gc.mark_full();
                }
                res
            } else {
                shared.with_path_of(parent, || invariant_failure(model, &state, r))
            };
            span.end(T::Invariants);
            if let Some((outcome, at)) = f {
                shared.fail(outcome, at);
                break;
            }
            if shared.paths.is_some() {
                let path = shared.paths.as_ref().and_then(|p| p.lock().get(parent));
                shared.note_path(r, depth, &state, Some(action), path);
            }
            self.local.push_new(Task { state, log: r, depth });
            if (i + 1) % RESOLVE_TICK == 0 {
                // (No states are expanded meanwhile, so no `tick`: the next
                // level queued here, a whole level at once, goes to disk as
                // it is queued while the queue spills.)
                self.local.spill();
            }
        }
        drop(ranks);
        drop(scratch);
        store.clear();
        cands.clear();
        if order.shrinking() {
            let before = store.bytes() + cands.bytes();
            store.shrink();
            cands.shrink_to_fit();
            stats::add_count("representative buffer bytes reclaimed", before.saturating_sub(store.bytes() + cands.bytes()) as u64);
        }
        if let Some(o) = &mut self.order {
            o.cands = cands;
            o.store = store;
            o.account(&order.cand_bytes);
        }
        let table = Arc::new(Table::new(start, entries, table_charge));
        table.account(&order.cand_bytes);
        order.next.lock()[self.me] = Some(table);
    }
}

#[cfg(test)]
mod tests;
