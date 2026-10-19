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
//! The candidates, the classes' keys and the tables cost memory and time
//! only in this mode; otherwise the fingerprint is the state and the first
//! inserter is as good as any.
//!
//! The states of the candidates of a level are held until the level is
//! resolved, i.e. a whole level of new states at a time, which is what a
//! model with wide states and wide levels pays for: `CandStore` keeps them
//! the way the queue does, XOR-varint encoded (10-100x smaller), and
//! `resolve` visits the candidates in the order they were offered, the
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

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use tlx_base::hash::IdMap as FpMap;

use parking_lot::Mutex;
use tlx_base::padded::Padded;

use super::coverage::{bump, generated_at};
use super::frontier::Task;
use super::tracelog::{split_log_ref, LogRef, NO_PARENT};
use super::worker::{edge_error, WorkerState};
use super::{fp_set_full, invariant_failure, Failure, Outcome, SP_GROW};
use crate::fpset::Full;
use crate::io::{BlockRef, BlockStore, IoError, Pending, Prefetch, Spill};
use crate::mem::{Gauge, Part};
use crate::model::Model;
use crate::queue::codec::{self, XorPrev};
use crate::queue::StateCodec;
use crate::stats::{self, T};
use tlx_base::bytes::{get_uvar_trusted, put_uvar};

/// Charge allocations until their last owner releases them, including old
/// position tables still read by workers after a level changes.
#[derive(Default)]
struct Charge(Mutex<Option<(Arc<Gauge>, Part)>>);

impl Charge {
    fn set(&self, gauge: &Arc<Gauge>, bytes: usize) {
        let mut charge = self.0.lock();
        if charge.as_ref().is_some_and(|(g, _)| !Arc::ptr_eq(g, gauge)) {
            let (g, part) = charge.take().expect("old search account");
            part.set(&g, 0);
        }
        let (g, part) = charge.get_or_insert_with(|| (gauge.clone(), Part::default()));
        part.set(g, bytes);
    }
}

impl Drop for Charge {
    fn drop(&mut self) {
        if let Some((g, part)) = self.0.get_mut() {
            part.set(g, 0);
        }
    }
}

struct Counts {
    values: Box<[AtomicU64]>,
    _charge: Charge,
}

impl std::ops::Deref for Counts {
    type Target = [AtomicU64];
    fn deref(&self) -> &Self::Target {
        &self.values
    }
}

/// The classes inserted into the seen set while expanding a level, as a
/// filter on their fingerprints: a clear bit tells that a class in the seen
/// set was found at an earlier level, so a successor of it is no candidate
/// (see the module). A class's bit is set before it is inserted into the
/// seen set (whose insertion releases, and whose lookup acquires), so a
/// worker that finds the class there sees its bit; bits are only set during
/// a level. A set bit may also be another class's (the slow path then
/// decides).
struct NewClasses {
    words: Box<[AtomicU64]>,
    _charge: Charge,
}

impl NewClasses {
    /// A filter for the classes new at the level after one of `states`
    /// states: about 16 bits per state (a level has rarely more new
    /// classes than twice the previous one's states), within 2^12..2^28
    /// bits.
    fn new(states: u64, gauge: &Arc<Gauge>) -> NewClasses {
        let words = (states.saturating_mul(16) / 64).clamp(1 << 6, 1 << 22).next_power_of_two() as usize;
        // (Zeroed memory from the allocator: pages are cleared when touched.)
        let zeros: Box<[u64]> = vec![0u64; words].into_boxed_slice();
        const _: () = assert!(std::mem::size_of::<AtomicU64>() == 8 && std::mem::align_of::<AtomicU64>() == std::mem::align_of::<u64>());
        // SAFETY: AtomicU64 has the size and alignment of u64 (checked above)
        // and the same in-memory representation; the box is uniquely owned.
        let words: Box<[AtomicU64]> = unsafe { Box::from_raw(Box::into_raw(zeros) as *mut [AtomicU64]) };
        let charge = Charge::default();
        charge.set(gauge, std::mem::size_of::<NewClasses>() + words.len() * 8);
        NewClasses { words, _charge: charge }
    }

    #[inline]
    fn at(&self, fp: u64) -> (&AtomicU64, u64) {
        (&self.words[(fp >> 6) as usize & (self.words.len() - 1)], 1 << (fp & 63))
    }

    /// Before inserting class `fp` into the seen set.
    #[inline]
    fn mark(&self, fp: u64) {
        let (w, bit) = self.at(fp);
        if w.load(Ordering::Relaxed) & bit == 0 {
            w.fetch_or(bit, Ordering::Relaxed);
        }
    }

    /// Whether class `fp`, found in the seen set, may have been inserted at
    /// this level.
    #[inline]
    fn may_hold(&self, fp: u64) -> bool {
        let (w, bit) = self.at(fp);
        w.load(Ordering::Relaxed) & bit != 0
    }
}

/// The place of a candidate in BFS order: the position of its parent in
/// the parent's level, and the index of the successor among the parent's
/// successors (as generated).
type Key = (u64, u64);

/// Shards of `Order::best` (chosen by bits of the fingerprint the shard's
/// map does not use much: hashbrown takes the low and the top bits).
const SHARDS: usize = 256;

#[inline]
fn shard(fp: u64) -> usize {
    (fp >> 32) as usize % SHARDS
}

/// The states of a level logged by one worker: for the trace-log entries
/// from `start` on, the position of the parent and the rank among the
/// parent's states of the level (entries that are not states of the level
/// are not looked up).
pub(super) struct Table {
    start: usize,
    entries: Vec<(u64, u64)>,
    charge: Charge,
}

/// The positions of the states of a level in BFS order.
pub struct Positions {
    /// Per worker log, its states of the level.
    tables: Vec<Option<Arc<Table>>>,
    /// Per state of the previous level (by position), the position of its
    /// first state in this level.
    first: Box<[u64]>,
    /// The number of states of the level.
    len: u64,
    charge: Charge,
}

impl Positions {
    /// The positions of the states logged at `refs`, in this order (initial
    /// states).
    pub(super) fn of_seq(refs: &[LogRef]) -> Positions {
        Self::of(refs.len(), refs.iter().enumerate().map(|(j, &r)| (r, j as u64)))
    }

    /// The positions of the states of a level as `(trace-log entry,
    /// position)`, each position below `places.len()` once (the first level
    /// of a resumed search).
    pub(super) fn of_places(places: &[(LogRef, u64)]) -> Positions {
        Self::of(places.len(), places.iter().copied())
    }

    /// The positions of the `len` states `places` gives, twice over.
    fn of(len: usize, places: impl Iterator<Item = (LogRef, u64)> + Clone) -> Positions {
        let mut tables: Vec<Option<Table>> = Vec::new();
        let mut span: Vec<(usize, usize)> = Vec::new();
        for (r, _) in places.clone() {
            let (w, i) = split_log_ref(r);
            if span.len() <= w {
                span.resize(w + 1, (usize::MAX, 0));
            }
            span[w] = (span[w].0.min(i), span[w].1.max(i + 1));
        }
        for &(lo, hi) in &span {
            tables.push((lo < hi).then(|| Table { start: lo, entries: vec![(0, 0); hi - lo], charge: Charge::default() }));
        }
        for (r, j) in places {
            let (w, i) = split_log_ref(r);
            let t = tables[w].as_mut().expect("a table");
            t.entries[i - t.start] = (0, j);
        }
        Positions {
            tables: tables.into_iter().map(|t| t.map(Arc::new)).collect(),
            first: Box::new([0]),
            len: len as u64,
            charge: Charge::default(),
        }
    }

    fn account(&self, gauge: &Arc<Gauge>) {
        self.charge.set(
            gauge,
            std::mem::size_of::<Self>()
                + 2 * std::mem::size_of::<usize>()
                + self.tables.capacity() * std::mem::size_of::<Option<Arc<Table>>>()
                + self.first.len() * 8,
        );
        for table in self.tables.iter().flatten() {
            table.account(gauge);
        }
    }

    /// The position of the state of the level logged at `log`.
    #[inline]
    pub(super) fn pos(&self, log: LogRef) -> u64 {
        let (w, i) = split_log_ref(log);
        let t = self.tables.get(w).and_then(|t| t.as_deref()).expect("a state of the level");
        let (p, j) = t.entries[i - t.start];
        self.first[p as usize] + j
    }
}

impl Table {
    fn account(&self, gauge: &Arc<Gauge>) {
        self.charge.set(gauge, std::mem::size_of::<Self>() + 2 * std::mem::size_of::<usize>() + self.entries.capacity() * 16);
    }
}

/// The shared state of the choice of representatives (see the module).
pub(super) struct Order {
    /// The classes new at the level being expanded: the least key offered.
    best: Box<[Padded<Mutex<FpMap<Key>>>]>,
    /// A filter on the classes new at the level being expanded.
    new: Mutex<Arc<NewClasses>>,
    /// The positions of the states of the level being expanded.
    current: Mutex<Arc<Positions>>,
    /// Per state of the level being expanded (by position), the number of
    /// its successors kept.
    counts: Mutex<Arc<Counts>>,
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
                + SHARDS * (std::mem::size_of::<Padded<Mutex<FpMap<Key>>>>() + std::mem::size_of::<Part>())
                + workers * std::mem::size_of::<Option<Arc<Table>>>(),
        );
        Order {
            best: (0..SHARDS).map(|_| Padded(Mutex::new(FpMap::default()))).collect(),
            new: Mutex::new(Arc::new(NewClasses::new(0, &gauge))),
            current: Mutex::new(Arc::new(Positions { tables: Vec::new(), first: Box::new([]), len: 0, charge: Charge::default() })),
            counts: Mutex::new(zeros(0, &gauge)),
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
        *self.counts.lock() = zeros(positions.len, &self.cand_bytes);
        *self.new.lock() = Arc::new(NewClasses::new(positions.len, &self.cand_bytes));
        *self.current.lock() = positions;
    }

    /// The positions of the states of the level being expanded.
    pub(super) fn current(&self) -> Arc<Positions> {
        self.current.lock().clone()
    }

    /// The least key offered for class `fp` at this level (once every
    /// worker has expanded the level: the representative's).
    fn best_of(&self, fp: u64) -> Option<Key> {
        self.best[shard(fp)].lock().get(&fp).copied()
    }

    /// Make the next level (resolved by every worker) the current one:
    /// called by a single worker, the others waiting.
    pub(super) fn advance(&self) {
        let mut counts = self.counts.lock();
        let mut first = Vec::with_capacity(counts.len());
        let mut len = 0;
        for c in counts.iter() {
            first.push(len);
            len += c.load(Ordering::Relaxed);
        }
        let tables = std::mem::replace(&mut *self.next.lock(), vec![None; self.workers]);
        let positions = Arc::new(Positions { tables, first: first.into(), len, charge: Charge::default() });
        positions.account(&self.cand_bytes);
        *self.current.lock() = positions;
        *counts = zeros(len, &self.cand_bytes);
        *self.new.lock() = Arc::new(NewClasses::new(len, &self.cand_bytes));
        for (i, b) in self.best.iter().enumerate() {
            let mut b = b.lock();
            b.clear();
            if self.shrinking() {
                b.shrink_to_fit();
            }
            self.best_parts[i].set(&self.cand_bytes, best_bytes(&b));
        }
    }
}

fn zeros(n: u64, gauge: &Arc<Gauge>) -> Arc<Counts> {
    let values: Box<[AtomicU64]> = (0..n).map(|_| AtomicU64::new(0)).collect();
    let charge = Charge::default();
    charge.set(gauge, std::mem::size_of::<Counts>() + 2 * std::mem::size_of::<usize>() + values.len() * 8);
    Arc::new(Counts { values, _charge: charge })
}

/// std's Swiss table: power-of-two buckets, one control byte per bucket,
/// and a control group. Include empty reserved buckets, not just entries.
fn best_bytes(map: &FpMap<Key>) -> usize {
    if map.capacity() == 0 {
        return 0;
    }
    let buckets = (map.capacity() + 1).next_power_of_two();
    buckets * (std::mem::size_of::<(u64, Key)>() + 1) + 16
}

/// While a level is resolved, the next level's segments are offered to the
/// disk every this many states queued (as `worker::TICK` while expanding).
const RESOLVE_TICK: usize = 1024;

/// A candidate representative (see the module): its place in BFS order and
/// where its state is (`CandStore`).
///
/// What only the candidates kept need (the parent's trace-log entry, the
/// action, the depth) is stored with the state (`CandStore`), which may be
/// on disk: 24 bytes per candidate stay in memory, for a whole level.
struct Cand {
    /// Its key: the position of its parent, and its index among the
    /// parent's successors (`Key`).
    pos: u64,
    idx: u32,
    /// Its state: the index `CandStore::push` returned.
    at: u32,
    fp: u64,
}

impl Cand {
    fn key(&self) -> Key {
        (self.pos, self.idx as u64)
    }
}

/// What a candidate kept needs besides its state (stored with the state).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
struct Meta {
    /// The parent's trace-log entry.
    parent: LogRef,
    depth: u32,
    /// The action that generated it.
    action: u32,
}

/// The states of the candidates one worker buffered, in the order they were
/// offered (see the module).
///
/// Every candidate's state is needed until the level is resolved (only then
/// is the representative of its class known), so a whole level of states is
/// held at a time. For a model with wide states and wide levels that is the
/// search's memory: MultiPaxos_MC buffers 335 words for each of more than
/// ten million candidates at its widest level, tens of GiB against the
/// 2 GiB the whole single-worker search needs, which the machine pays for
/// in page faults, memory traffic and cache misses (docs/scale.md). The
/// states of a level are alike, so with a state codec (the compiled tier)
/// each is stored XOR-varint encoded against the previous one, as the
/// queue's blocks are: the same candidates cost a few percent of that. A
/// model whose states are not words (the interpreter) keeps them, as
/// before.
///
/// Encoded, the records are appended to segments (`seg_bytes`, whole
/// records each, as the queue's); under memory pressure (`Order::spill`)
/// the full ones go to disk, and `resolve` reads them back in order, the
/// next one read ahead. Even encoded, a wide level is too much for a small
/// budget: MultiPaxos_MC's candidates took 1.5 GiB with 8 or 16 workers,
/// whatever the budget, and a run in a control group of 1.7 GiB (budget
/// 857 MiB) was killed.
///
/// A state stored encoded is decoded after the ones before it, so `resolve`
/// visits the candidates in the order they were offered. Which state of a
/// class represents it, the counts, the BFS positions (from the keys) and
/// the outdegrees do not depend on that order; which of several violations
/// of the level is reported first does (docs/compat.md, tier 3).
enum CandStore<'m, S> {
    /// The states as words, XOR-varint encoded against the previous one.
    Words(Box<Words<'m, S>>),
    /// The states themselves.
    Objects(Vec<Option<(S, Meta)>>),
}

/// A full segment of encoded candidates.
enum CandSeg {
    Mem(Vec<u8>),
    /// Handed to the writer thread.
    Pending(Arc<Pending>),
    Disk(BlockRef),
}

struct Words<'m, S> {
    codec: &'m dyn StateCodec<S>,
    /// The full segments, in order, and the one appended to (records are
    /// only appended).
    segs: Vec<CandSeg>,
    cur: Vec<u8>,
    seg_bytes: usize,
    /// The store of the segments spilled (created with the first one).
    store: Option<Arc<BlockStore>>,
    /// The state `codec.encode` writes before it is encoded.
    scratch: Vec<u64>,
    /// The last state pushed (the record the next one is relative to).
    enc: XorPrev,
    /// The last state decoded; the segment being decoded (`rd`, the
    /// `next` one in `segs`) and where in it the next record starts; the
    /// read ahead of a spilled segment.
    dec: XorPrev,
    rd: Vec<u8>,
    next: usize,
    pos: usize,
    ahead: Option<(usize, Arc<Prefetch>)>,
    /// How many records were pushed, and how many of them have been
    /// decoded (in order).
    pushed: usize,
    decoded: usize,
}

impl<S> Words<'_, S> {
    /// Make the next segment the one decoded (`rd`), reading it back if it
    /// was spilled (and reading the one after it ahead).
    fn load_next(&mut self, spill: &Spill) -> Result<(), IoError> {
        let k = self.next;
        self.next += 1;
        self.pos = 0;
        let Some(seg) = self.segs.get_mut(k) else {
            // (The last records: the segment appended to.)
            self.rd = std::mem::take(&mut self.cur);
            return Ok(());
        };
        let bytes = match std::mem::replace(seg, CandSeg::Mem(Vec::new())) {
            CandSeg::Mem(v) => v,
            CandSeg::Pending(p) => match p.settle::<Vec<u8>>() {
                Ok(r) => self.read_back(k, r)?,
                // (The write failed, recorded in the spill directory: the
                // data came back.)
                Err((v, _)) => v,
            },
            CandSeg::Disk(r) => self.read_back(k, r)?,
        };
        if let (Some(CandSeg::Disk(r)), Some(store)) = (self.segs.get(k + 1), &self.store) {
            self.ahead = Some((k + 1, spill.prefetch(store, r)));
        }
        self.rd = bytes;
        Ok(())
    }

    /// The bytes of spilled segment `k` (at `r`), deleted from the disk
    /// (an IO error is recorded in the spill directory by the store).
    fn read_back(&mut self, k: usize, r: BlockRef) -> Result<Vec<u8>, IoError> {
        let store = self.store.as_ref().expect("a store of the spilled candidates");
        let bytes = match self.ahead.take() {
            Some((at, p)) if at == k => p.wait(),
            _ => store.read(&r),
        };
        store.delete(r);
        bytes
    }
}

impl<'m, S> CandStore<'m, S> {
    /// The store of a worker, with `codec` if the model's states are words,
    /// in segments of `seg_bytes`.
    fn new(codec: Option<&'m dyn StateCodec<S>>, seg_bytes: usize) -> CandStore<'m, S> {
        match codec {
            Some(codec) => CandStore::Words(Box::new(Words {
                codec,
                segs: Vec::new(),
                cur: Vec::new(),
                seg_bytes: seg_bytes.max(1),
                store: None,
                scratch: vec![0; codec.words()],
                enc: XorPrev::new(codec.words()),
                dec: XorPrev::new(codec.words()),
                rd: Vec::new(),
                next: 0,
                pos: 0,
                ahead: None,
                pushed: 0,
                decoded: 0,
            })),
            None => CandStore::Objects(Vec::new()),
        }
    }

    /// Buffer the state of `s` (`fp` its fingerprint) and `meta`: where it
    /// is (a `Cand::at`). The state is encoded, not kept: a record is the
    /// action and depth (varints) and the XOR record of the state, whose
    /// log reference is the parent's.
    fn push(&mut self, s: S, fp: u64, meta: Meta) -> u32 {
        match self {
            CandStore::Words(w) => {
                w.codec.encode(&s, &mut w.scratch);
                // (A segment holds whole records, within its capacity.)
                let most = codec::xor_max_size(w.scratch.len()) + 2 * 10;
                if w.cur.len() + most > w.cur.capacity() {
                    if !w.cur.is_empty() {
                        let full = std::mem::take(&mut w.cur);
                        w.segs.push(CandSeg::Mem(full));
                    }
                    w.cur.reserve_exact(w.seg_bytes.max(most));
                }
                put_uvar(&mut w.cur, meta.action as u64);
                put_uvar(&mut w.cur, meta.depth as u64);
                codec::put_xor(&mut w.cur, &mut w.enc, meta.parent, fp, &w.scratch);
                let at = w.pushed;
                w.pushed += 1;
                at as u32
            }
            CandStore::Objects(v) => {
                v.push(Some((s, meta)));
                (v.len() - 1) as u32
            }
        }
    }

    /// The state at `at` (a `Cand::at`), which must not be before the last
    /// one passed: the records before it are decoded (the states of a level
    /// are stored encoded, see the type). An IO error reading a spilled
    /// segment back stops the search.
    fn get(&mut self, at: u32, fp: u64, spill: &Spill) -> Result<(S, Meta), IoError> {
        match self {
            CandStore::Words(w) => {
                debug_assert!(at as usize >= w.decoded && (at as usize) < w.pushed, "candidates decoded in order");
                let (mut action, mut depth) = (0, 0);
                while w.decoded <= at as usize {
                    while w.pos >= w.rd.len() {
                        w.load_next(spill)?;
                    }
                    action = get_uvar_trusted(&w.rd, &mut w.pos) as u32;
                    depth = get_uvar_trusted(&w.rd, &mut w.pos) as u32;
                    codec::get_xor(&w.rd, &mut w.pos, &mut w.dec);
                    w.decoded += 1;
                }
                let meta = Meta { parent: w.dec.log, depth, action };
                // SAFETY: the records were written only by this codec's
                // encode in push, kept in memory or read back from disk with
                // their checksums verified; the XOR codec preserves the words.
                Ok((unsafe { w.codec.decode_trusted(&w.dec.words, depth, fp) }, meta))
            }
            CandStore::Objects(v) => Ok(v[at as usize].take().expect("the state of a candidate")),
        }
    }

    /// Hand the full segments in memory to the disk, and release those
    /// written (memory pressure: `Order::spill`).
    fn spill(&mut self, spill: &Spill) -> Result<(), IoError> {
        let CandStore::Words(w) = self else { return Ok(()) };
        let mut err = None;
        for seg in &mut w.segs {
            match seg {
                CandSeg::Mem(v) if !v.is_empty() => {
                    let store = match &w.store {
                        Some(s) => s,
                        None => w.store.insert(spill.store("cands")?),
                    };
                    let p = spill.write_async(store, Box::new(std::mem::take(v)));
                    *seg = CandSeg::Pending(p);
                }
                CandSeg::Pending(p) => match p.try_settle::<Vec<u8>>() {
                    Some(Ok(r)) => *seg = CandSeg::Disk(r),
                    Some(Err((v, e))) => {
                        *seg = CandSeg::Mem(v);
                        err.get_or_insert(e);
                    }
                    None => {}
                },
                _ => {}
            }
        }
        err.map_or(Ok(()), Err)
    }

    /// Forget the states of the level resolved (the buffers are reused;
    /// spilled segments are deleted).
    fn clear(&mut self) {
        match self {
            CandStore::Words(w) => {
                w.ahead = None;
                for seg in w.segs.drain(..) {
                    let r = match seg {
                        CandSeg::Mem(_) => continue,
                        CandSeg::Pending(p) => match p.settle::<Vec<u8>>() {
                            Ok(r) => r,
                            Err(_) => continue,
                        },
                        CandSeg::Disk(r) => r,
                    };
                    w.store.as_ref().expect("a store of the spilled candidates").delete(r);
                }
                // (The buffer appended to stays: the segment last decoded, or
                // the one appended to if none was full.)
                if w.cur.capacity() == 0 {
                    w.cur = std::mem::take(&mut w.rd);
                }
                w.cur.clear();
                w.rd = Vec::new();
                w.enc.reset();
                w.dec.reset();
                w.pushed = 0;
                w.decoded = 0;
                w.next = 0;
                w.pos = 0;
            }
            CandStore::Objects(v) => v.clear(),
        }
    }

    fn shrink(&mut self) {
        match self {
            CandStore::Words(w) => {
                w.cur.shrink_to_fit();
                w.rd.shrink_to_fit();
            }
            CandStore::Objects(v) => v.shrink_to_fit(),
        }
    }

    /// The memory of the store (bytes, for the memory budget): segments in
    /// memory, also while being written.
    fn bytes(&self) -> usize {
        match self {
            CandStore::Words(w) => {
                let segs: usize = w
                    .segs
                    .iter()
                    .map(|s| match s {
                        CandSeg::Mem(v) => v.capacity(),
                        CandSeg::Pending(_) => w.seg_bytes,
                        CandSeg::Disk(_) => 0,
                    })
                    .sum();
                std::mem::size_of::<Words<'_, S>>()
                    + segs
                    + w.cur.capacity()
                    + w.rd.capacity()
                    + w.ahead.as_ref().map_or(0, |_| w.seg_bytes)
                    + w.segs.capacity() * std::mem::size_of::<CandSeg>()
                    + 8 * (w.scratch.capacity() + w.enc.words.capacity() + w.dec.words.capacity())
            }
            CandStore::Objects(v) => v.capacity() * std::mem::size_of::<Option<(S, Meta)>>(),
        }
    }
}

/// A worker's part of the choice of representatives.
pub(super) struct OrderLocal<'m, S> {
    /// The positions of the level being expanded and the counts of its
    /// states' successors kept (see `Order`).
    positions: Arc<Positions>,
    counts: Arc<Counts>,
    /// The filter on the classes new at the level (see `Order::new`).
    new: Arc<NewClasses>,
    /// The position of the state being expanded.
    pos: u64,
    /// The candidates buffered at this level, in the order they were offered.
    cands: Vec<Cand>,
    /// Their states.
    store: CandStore<'m, S>,
    charge: Charge,
}

impl<'m, S> OrderLocal<'m, S> {
    /// The part of a worker, its candidates' states encoded by `codec` (if
    /// any) in segments of `seg_bytes`.
    pub(super) fn new(order: &Order, codec: Option<&'m dyn StateCodec<S>>, seg_bytes: usize) -> OrderLocal<'m, S> {
        OrderLocal {
            positions: order.current(),
            counts: order.counts.lock().clone(),
            new: order.new.lock().clone(),
            pos: 0,
            cands: Vec::new(),
            store: CandStore::new(codec, seg_bytes),
            charge: Charge::default(),
        }
    }
}

impl<M: Model> WorkerState<'_, '_, M> {
    /// Before expanding a level: its positions.
    pub(super) fn order_level(&mut self) {
        if let (Some(o), Some(order)) = (&mut self.order, &self.shared.order) {
            o.positions = order.current();
            o.counts = order.counts.lock().clone();
            o.new = order.new.lock().clone();
            if order.shrinking() {
                o.cands.shrink_to_fit();
                o.store.shrink();
            }
            o.charge.set(&order.cand_bytes, cand_bytes(o));
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
        o.charge.set(&order.cand_bytes, cand_bytes(o));
        if let Err(e) = r {
            self.shared.fail(Outcome::Io(e.0), NO_PARENT);
        }
    }

    /// Before expanding `task`: its position.
    #[inline]
    pub(super) fn order_task(&mut self, task: &Task<M::State>) {
        if let Some(o) = &mut self.order {
            o.pos = o.positions.pos(task.log);
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
        let seen = &shared.seen;
        // A class found at an earlier level, told without writing shared
        // memory (see `NewClasses`; the disk tier is asked by `insert` only).
        if !seen.spilling() && seen.contains(fp) && !o.new.may_hold(fp) {
            return Ok(());
        }
        let high = || shared.control().request(SP_GROW);
        let mut parked = false;
        let keep = loop {
            // (The class is inserted into the seen set and into `best`
            // atomically: a class in the seen set and not in `best` is of
            // an earlier level.)
            let mut best = order.best[shard(fp)].lock();
            if let Some(b) = best.get_mut(&fp) {
                let less = key < *b;
                if less {
                    *b = key;
                }
                break less;
            }
            o.new.mark(fp);
            match if STATS { stats::fp_insert(seen, self.me, fp, high) } else { seen.insert_by(self.me, fp, &mut 0, high) } {
                Ok(true) => {
                    let capacity = best.capacity();
                    best.insert(fp, key);
                    if best.capacity() != capacity {
                        order.best_parts[shard(fp)].set(&order.cand_bytes, best_bytes(&best));
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
                    shared.safepoint.park(|req, crew| shared.serve_safepoint(req, crew));
                    parked = true;
                }
            }
        };
        if keep {
            let before = cand_bytes(o);
            let at = o.store.push(t, fp, Meta { parent: task.log, depth: task.depth + 1, action });
            o.cands.push(Cand { pos: key.0, idx: idx as u32, at, fp });
            let bytes = cand_bytes(o);
            if bytes != before {
                o.charge.set(&order.cand_bytes, bytes);
            }
        }
        Ok(())
    }

    /// After every worker has expanded the level: keep the candidates that
    /// represent their classes, in BFS order: log, count (outdegrees,
    /// depth, coverage), check and queue them. A failure stops the search.
    pub(super) fn resolve(&mut self) {
        let shared = self.shared;
        let (Some(o), Some(order)) = (&mut self.order, &shared.order) else { return };
        o.charge.set(&order.cand_bytes, cand_bytes(o));
        // (Both are put back below, their buffers kept for the next level.)
        let mut cands = std::mem::take(&mut o.cands);
        let counts = o.counts.clone();
        let mut store = std::mem::replace(&mut o.store, CandStore::new(None, 0));
        cands.retain(|c| order.best_of(c.fp) == Some(c.key()));
        // The successors kept per parent: their ranks, counts, and the
        // outdegrees of the parents (counted as 0 when expanded). The
        // candidates are visited by key (as by one worker); their states,
        // which are visited in the order they were offered below, do not
        // take part.
        let mut by_key: Vec<u32> = (0..cands.len() as u32).collect();
        by_key.sort_unstable_by_key(|&i| cands[i as usize].key());
        let mut ranks = vec![0u64; cands.len()];
        // Unstable sorting is in place (no auxiliary allocation).
        let scratch = Charge::default();
        scratch.set(&order.cand_bytes, by_key.capacity() * 4 + ranks.capacity() * 8);
        let mut k = 0;
        for (j, &i) in by_key.iter().enumerate() {
            let c = &cands[i as usize];
            k = if j > 0 && cands[by_key[j - 1] as usize].pos == c.pos { k + 1 } else { 0 };
            ranks[i as usize] = k;
            if by_key.get(j + 1).is_none_or(|&n| cands[n as usize].pos != c.pos) {
                counts[c.pos as usize].store(k + 1, Ordering::Relaxed);
                self.outdegree.replace(0, k + 1);
            }
        }
        let model = shared.model;
        let start = self.shard.log.len();
        let mut entries = Vec::with_capacity(cands.len());
        let table_charge = Charge::default();
        table_charge.set(&order.cand_bytes, entries.capacity() * 16);
        for (i, c) in cands.iter().enumerate() {
            if shared.control().stopped() {
                break;
            }
            let (state, Meta { parent, depth, action }) = match store.get(c.at, c.fp, &shared.opts.spill) {
                Ok(x) => x,
                Err(e) => {
                    shared.fail(Outcome::Io(e.0), NO_PARENT);
                    break;
                }
            };
            let r = self.append_log(parent, c.fp);
            entries.push((c.pos, ranks[i]));
            bump(&self.slot.cov, generated_at(action) + 1);
            // The atoms of the tableaux on a new state (recording the
            // liveness edges: the fingerprint is the state then, see
            // `explore`), as one worker evaluates them when it finds it.
            if let Some(e) = &mut self.shard.edges {
                if let Err((outcome, at)) = edge_error(model, e.found(&state), parent) {
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
                o.on_new_state(&state, c.fp, depth, None);
            }
            let span = stats::span();
            // (`TLCExt!Trace` on the state: its parent's path and the state.)
            let f = shared.with_path_of(parent, || invariant_failure(model, &state, r));
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
        store.clear();
        cands.clear();
        if order.shrinking() {
            let before = store.bytes() + cands.capacity() * std::mem::size_of::<Cand>();
            store.shrink();
            cands.shrink_to_fit();
            stats::add_count(
                "representative buffer bytes reclaimed",
                (before - store.bytes() - cands.capacity() * std::mem::size_of::<Cand>()) as u64,
            );
        }
        if let Some(o) = &mut self.order {
            o.cands = cands;
            o.store = store;
            o.charge.set(&order.cand_bytes, cand_bytes(o));
        }
        let table = Arc::new(Table { start, entries, charge: table_charge });
        table.account(&order.cand_bytes);
        order.next.lock()[self.me] = Some(table);
    }
}

/// The memory of a worker's candidates (bytes, for the memory budget).
fn cand_bytes<S>(o: &OrderLocal<'_, S>) -> usize {
    o.cands.capacity() * std::mem::size_of::<Cand>() + o.store.bytes()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bfs_metadata_stays_accounted_while_workers_hold_old_positions() {
        let order = Order::new(2);
        let baseline = order.gauge().bytes();
        order.start(Arc::new(Positions::of_seq(&[0, 1, 2])));
        let before = order.gauge().bytes();
        assert!(before >= baseline + 3 * 16 + 3 * 8, "positions and counts must be registered");
        let old = order.current();
        order.advance();
        let held = order.gauge().bytes();
        drop(old);
        assert!(order.gauge().bytes() < held, "old positions stay charged until their last reader leaves");
    }

    #[test]
    fn recovered_positions_follow_their_entries_not_the_order_read() {
        use super::super::tracelog::log_ref;
        // A level read from a checkpoint in worker order, its BFS positions
        // recorded: the same positions as the level queued in BFS order.
        let read = [(log_ref(1, 5), 2), (log_ref(0, 7), 0), (log_ref(1, 4), 3), (log_ref(0, 9), 1)];
        let placed = Positions::of_places(&read);
        let mut bfs = read;
        bfs.sort_by_key(|&(_, p)| p);
        let refs: Vec<LogRef> = bfs.iter().map(|&(r, _)| r).collect();
        let sorted = Positions::of_seq(&refs);
        for (r, p) in read {
            assert_eq!((placed.pos(r), sorted.pos(r)), (p, p));
        }
        assert_eq!(placed.len, 4);
    }

    #[test]
    fn resumed_positions_move_to_the_new_search_registry() {
        let positions = Arc::new(Positions::of_seq(&[0, 1, 2]));
        let old = Order::new(2);
        old.start(positions.clone());
        let expected = old.gauge().bytes();
        let new = Order::new(2);
        new.start(positions);
        assert_eq!(new.gauge().bytes(), expected);
    }

    #[test]
    fn cleared_candidates_keep_capacity_charged_until_pressure_reclaims_it() {
        let order = Order::new(2);
        let codec = Words3;
        let mut local = OrderLocal::new(&order, Some(&codec), 1 << 20);
        let baseline = order.gauge().bytes();
        for i in 0..5000 {
            let at = local.store.push(vec![i, i * 2, i * 3], i, Meta { parent: 0, depth: 1, action: 0 });
            local.cands.push(Cand { pos: i, idx: 0, at, fp: i });
        }
        local.charge.set(order.gauge(), cand_bytes(&local));
        let full = order.gauge().bytes();
        local.cands.clear();
        local.store.clear();
        local.charge.set(order.gauge(), cand_bytes(&local));
        assert_eq!(order.gauge().bytes(), full);
        local.cands.shrink_to_fit();
        local.store.shrink();
        local.charge.set(order.gauge(), cand_bytes(&local));
        assert!(order.gauge().bytes() < baseline + 1024);
        drop(local);
        assert_eq!(order.gauge().bytes(), baseline);
    }

    /// A class's bit is set by `mark` and stays set; another class's bit is
    /// clear unless it shares the word and bit; the filter is sized from
    /// the level's states within its bounds.
    #[test]
    fn new_classes_filter() {
        let gauge = Arc::new(Gauge::new());
        let f = NewClasses::new(1000, &gauge);
        assert_eq!(f.words.len(), 256);
        let (a, b) = (0x1234_5678_9abc_def0u64, 0x0fed_cba9_8765_4321u64);
        assert!(!f.may_hold(a) && !f.may_hold(b));
        f.mark(a);
        f.mark(a);
        assert!(f.may_hold(a) && !f.may_hold(b));
        assert_eq!(NewClasses::new(0, &gauge).words.len(), 1 << 6);
        assert_eq!(NewClasses::new(u64::MAX, &gauge).words.len(), 1 << 22);
        assert!(gauge.bytes() >= 256 * 8);
        drop(f);
    }

    /// States that are their own words.
    struct Words3;

    impl StateCodec<Vec<u64>> for Words3 {
        fn words(&self) -> usize {
            3
        }
        fn encode(&self, s: &Vec<u64>, out: &mut [u64]) -> u64 {
            out.copy_from_slice(s);
            0
        }
        fn decode(&self, w: &[u64], _depth: u32, _fp: u64) -> Vec<u64> {
            w.to_vec()
        }
    }

    /// The states come back as pushed, skipping some, and again after
    /// `clear`: in memory, and with segments of a few records written to
    /// disk while being pushed (and read back ahead).
    #[test]
    fn encoded_candidates_roundtrip() {
        let codec = Words3;
        // (Parents that go up and down, actions and depths of any size.)
        let meta =
            |x: u64| Meta { parent: x.wrapping_mul(0x9E37_79B9_7F4A_7C15) >> (x % 40), depth: (x % 1000) as u32, action: (x * 7) as u32 };
        let scratch = tlx_testkit::TempDir::new("cands");
        let dir = scratch.child_path("spill");
        let spill = Spill::new(crate::io::SpillConfig { dir: Some(dir.clone()), ..Default::default() });
        for spilling in [false, true] {
            let mut store = CandStore::new(Some(&codec as &dyn StateCodec<Vec<u64>>), 64);
            for _ in 0..2 {
                let states: Vec<Vec<u64>> = (0..50u64).map(|i| vec![i / 7, i * i, if i % 3 == 0 { 0 } else { u64::MAX - i }]).collect();
                let at: Vec<u32> = states
                    .iter()
                    .map(|s| {
                        let at = store.push(s.clone(), 0, meta(s[1]));
                        if spilling {
                            store.spill(&spill).unwrap();
                        }
                        at
                    })
                    .collect();
                assert_eq!(at, (0..50).collect::<Vec<u32>>());
                if spilling {
                    let CandStore::Words(w) = &store else { unreachable!() };
                    assert!(w.segs.len() > 5, "segments of a few records");
                    // (Some written, some still pending or in memory.)
                    store.spill(&spill).unwrap();
                }
                for i in (0..50).step_by(3).chain([49]) {
                    assert_eq!(store.get(i as u32, 0, &spill).unwrap(), (states[i].clone(), meta(states[i][1])));
                }
                store.clear();
            }
            assert_eq!(spill.counters().used, 0, "spilled segments deleted");
        }
        assert!(spill.counters().written > 0);
    }
}
