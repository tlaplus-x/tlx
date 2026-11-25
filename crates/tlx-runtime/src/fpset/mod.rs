//! Lock-free set of 64-bit state fingerprints (docs/scale.md §4.1).
//!
//! An open-addressing table with linear probing; 0 marks an empty slot
//! (fingerprint 0 is remapped to 1). Below `2^21` home slots, each slot is an
//! `AtomicU64` (`8 B/slot`); from `2^21` slots (`12.8 MiB`) on, slots use
//! lossless low-bit `fastrange` quotienting in 64-byte cache lines (`6.4 B/slot`,
//! 10 slots/line), storing only the probe displacement and low fingerprint bits
//! while recovering the high bits from the home bucket (`table`).
//!
//! Placement by the high bits: the home slot of `fp` in a table of `n`
//! slots is `fp * n >> 64` ("fastrange"), monotonic in the fingerprint, so
//! the table is sorted up to the order within probe clusters, `n` need not
//! be a power of two, and a range of high bits is a range of slots. Probes
//! never wrap around: `OVERFLOW` slots follow the `n` home slots, and a
//! probe that runs off their end finds the table full. Probes test aligned
//! groups of slots with a single branch: at the loads a growing table runs
//! at (0.375 to 0.75), a slot-by-slot loop costs a branch misprediction per
//! lookup that ends a few slots past home.
//!
//! Load limits: an insert that brings the table to its high watermark
//! (`HIGH`, 0.75) asks for a larger table (the caller's `high` callback,
//! which requests a safepoint); inserts are refused (`Full`) at the hard
//! limit (`HARD`, 0.9). The number of entries is counted in per-thread
//! stripes far below the watermarks and exactly near them (`count`). The
//! check is not atomic with the insertion, so with `t` threads inserting at
//! once the load can exceed the hard limit by at most `2 (t - 1)` slots
//! (inserts in progress, and those counted in a stripe while the counting
//! became exact), far below the `OVERFLOW` free slots past the end.
//!
//! Growth (`grow`): a table twice as large (at most `FpConfig::limit`
//! slots) into which every fingerprint is inserted again, in parallel by the
//! workers parked at a safepoint. Because `fastrange` is monotonic, workers
//! sweep page-aligned chunks from low to high slots and release completed
//! old-table pages immediately (`madvise`), keeping physical memory bounded
//! by the new table plus one chunk per active worker instead of `old + new`.
//! Growing needs exclusive access: no other thread may use the set
//! meanwhile, except `len` (live statistics).
//!
//! A table of a fixed size (`-fpmem`) never grows: like TLC, inserts fail
//! once it is full. Otherwise the set starts small (`START_SLOTS`) and grows
//! up to its limit, or less: the search lowers the limit when the memory
//! budget leaves no room for a larger table (`cap`, `grow_to`).
//!
//! The disk tier (`disk`; with `with_disk`): a set that cannot grow
//! any more rotates instead of filling up (`rotate`, at a safepoint): its
//! table becomes a sorted run on disk, stays in memory read-only as the
//! old table, and a new table takes the inserts. An insert that finds an
//! empty slot in the table looks the fingerprint up in the old table and
//! the runs (Bloom filters, then a page read) before it inserts; the answer
//! is exact, so nothing above the set changes. Without a disk tier (`-spill
//! off`, or a table of a fixed size) a full set refuses inserts, as before.

mod bloom;
mod count;
mod disk;
mod overflow;
mod table;

use std::cell::UnsafeCell;
use std::sync::atomic::{AtomicU64, AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::Instant;

use self::count::Count;
use self::disk::{assemble, Disk, PieceWriter, Run, BLOCK_FPS};
use self::table::{Table, COMPACT48_MIN_SLOTS};
use crate::explore::safepoint::Crew;
use crate::io::{BlockStore, IoError, Spill};
use crate::mem::{Gauge, Part};
use tlx_base::padded::Padded;

pub use self::disk::DiskStats;

/// The high watermark: a growable table asks to grow at this load.
const HIGH_NUM: usize = 3;
const HIGH_DEN: usize = 4;
/// The hard limit: inserts are refused at this load.
const HARD_NUM: usize = 9;
const HARD_DEN: usize = 10;

/// Slots after the last home slot, where probes end (they never wrap).
pub const OVERFLOW: usize = 4096;

/// The smallest table.
pub const MIN_SLOTS: usize = 1024;

/// The first table of a growable set (`1M` home slots, `8 MiB`).
pub const START_SLOTS: usize = 1 << 20;

/// The default limit of a growable set (`FpConfig::default`; the CLI uses
/// `-maxmem`): `1G` slots (~6.4 GiB).
const DEFAULT_LIMIT_SLOTS: usize = 1 << 30;

/// The most shards `-fpbits` asks for (as TLC).
pub const MAX_BITS: u32 = 30;

/// The table of a set whose disk tier is used from the start (`-spill
/// always`, testing): its home slots (`FpConfig::disk_slots`).
pub const FORCED_DISK_SLOTS: usize = 1 << 18;

/// The size of a fingerprint set.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FpConfig {
    /// Home slots of the first table.
    pub initial: usize,
    /// The table never grows beyond this many home slots.
    pub limit: usize,
    /// A table of a fixed size (`-fpmem`): `initial == limit`.
    pub fixed: bool,
    /// `-fpbits`: the set is divided into `2^bits` shards by the high bits
    /// of the fingerprints (contiguous ranges of slots; growing splits its
    /// work along them).
    pub bits: u32,
    /// With the disk tier used from the start (`-spill always`), the table
    /// has at most this many home slots (`forced_disk`).
    pub disk_slots: usize,
    /// Optional hard cap on displacement-overflow segment bytes (set by
    /// `fixed_mib` so a fixed `-fpmem` table never exceeds its byte budget).
    overflow_cap: Option<usize>,
}

impl Default for FpConfig {
    fn default() -> FpConfig {
        FpConfig::growing(DEFAULT_LIMIT_SLOTS)
    }
}

impl FpConfig {
    /// A table of `slots` home slots (at least `MIN_SLOTS`) that never grows.
    pub fn fixed(slots: usize) -> FpConfig {
        let slots = slots.max(MIN_SLOTS);
        FpConfig { initial: slots, limit: slots, fixed: true, bits: 0, disk_slots: FORCED_DISK_SLOTS, overflow_cap: None }
    }

    /// A table that never grows, of `mib` MiB (`-fpmem`; the fixed probe
    /// overflow tail comes on top, while any compact displacement-overflow
    /// storage stays strictly within `mib` MiB).
    pub fn fixed_mib(mib: usize) -> FpConfig {
        const FIXED_COMPACT_RESERVE: usize = 1 << 20;
        let home_budget = mib.saturating_mul(1 << 20);
        let compact_slots = Table::home_slots_for_bytes(home_budget.saturating_sub(FIXED_COMPACT_RESERVE));
        if compact_slots >= COMPACT48_MIN_SLOTS {
            let max_total = home_budget.saturating_add(Table::probe_tail_bytes(compact_slots));
            let overflow_cap = max_total.saturating_sub(Table::array_bytes(compact_slots));
            FpConfig {
                initial: compact_slots,
                limit: compact_slots,
                fixed: true,
                bits: 0,
                disk_slots: FORCED_DISK_SLOTS,
                overflow_cap: Some(overflow_cap),
            }
        } else {
            let raw_slots = (home_budget / 8).clamp(MIN_SLOTS, COMPACT48_MIN_SLOTS - 1);
            FpConfig { initial: raw_slots, limit: raw_slots, fixed: true, bits: 0, disk_slots: FORCED_DISK_SLOTS, overflow_cap: Some(0) }
        }
    }

    /// A table that starts with `START_SLOTS` home slots and grows up to
    /// `limit` of them.
    pub fn growing(limit: usize) -> FpConfig {
        let limit = limit.max(MIN_SLOTS);
        FpConfig { initial: START_SLOTS.min(limit), limit, fixed: false, bits: 0, disk_slots: FORCED_DISK_SLOTS, overflow_cap: None }
    }

    /// A growable table whose slot limit fits within `bytes` of memory.
    pub fn growing_within(bytes: usize) -> FpConfig {
        FpConfig::growing(FpSet::max_slots_in(bytes))
    }

    /// A growable table limited to `bytes` of memory (a memory budget) at
    /// most; no effect on a table of a fixed size.
    pub fn within(self, bytes: usize) -> FpConfig {
        if self.fixed {
            return self;
        }
        let limit = self.limit.min(FpSet::max_slots_in(bytes)).max(MIN_SLOTS);
        FpConfig { initial: self.initial.clamp(MIN_SLOTS, limit), limit, ..self }
    }

    /// Start with `slots` home slots (at least `MIN_SLOTS`, at most the
    /// limit); no effect on a table of a fixed size.
    pub fn with_initial(self, slots: usize) -> FpConfig {
        if self.fixed {
            return self;
        }
        FpConfig { initial: slots.clamp(MIN_SLOTS, self.limit), ..self }
    }

    /// `-fpbits`.
    pub fn with_bits(self, bits: u32) -> FpConfig {
        FpConfig { bits: bits.min(MAX_BITS), ..self }
    }

    /// The table holds at most `slots` home slots when the disk tier is
    /// used from the start (`TLX_FP_SPILL_SLOTS`, testing).
    pub fn with_disk_slots(self, slots: usize) -> FpConfig {
        FpConfig { disk_slots: slots.max(MIN_SLOTS), ..self }
    }

    /// The disk tier used from the start (`-spill always`): a growable
    /// table of at most `disk_slots` home slots, so that the set rotates
    /// to disk early. No effect on a table of a fixed size.
    pub fn forced_disk(self) -> FpConfig {
        if self.fixed {
            return self;
        }
        let limit = self.limit.min(self.disk_slots);
        FpConfig { initial: self.initial.min(limit), limit, ..self }
    }

    /// The most memory of the table, in MiB (rounded down, at least 1).
    pub fn limit_mib(&self) -> usize {
        let bytes = if self.fixed {
            Table::home_bytes(self.limit).saturating_add(self.overflow_cap.unwrap_or(0)).saturating_add(64)
        } else {
            Table::array_bytes(self.limit).saturating_add(64)
        };
        (bytes >> 20).max(1)
    }
}

pub struct FpSet {
    /// The current table: replaced only by `grow` (with exclusive access).
    table: Padded<UnsafeCell<Table>>,
    /// The number of entries.
    count: Count,
    /// The most home slots (`FpConfig::limit`, or less after `cap`).
    limit: AtomicUsize,
    shards: usize,
    /// Growth: the number of times, the time spent (ns), and the largest
    /// memory of the tables at once (both tables during a growth).
    grows: AtomicU64,
    grow_ns: AtomicU64,
    peak_bytes: AtomicUsize,
    /// The disk tier, once the set rotated (changed only with exclusive
    /// access, like the table).
    disk: UnsafeCell<Option<Box<Disk>>>,
    /// Where the disk tier goes (`with_disk`); None: the set fills up.
    spill: Option<Spill>,
    /// Rotations: their number (also in `Disk`, here for `epoch`) and time.
    rotations: AtomicU64,
    rotate_ns: AtomicU64,
    /// The memory of the set (`bytes`), for the memory budget: its tables
    /// and runs (published by `account` whenever they change), and a merge
    /// in progress (by the disk tier).
    mem: Arc<Gauge>,
    tables: Part,
    /// The memory of the old table (published by `account`, so other
    /// threads like the budget monitor can read it without racing on
    /// `disk`).
    old_bytes: AtomicUsize,
}

// SAFETY: the table and the disk tier are only replaced or changed by
// `grow`, `rotate` and the other functions whose callers guarantee
// exclusive access; otherwise they are shared read-only (the slots are
// atomics, the runs immutable).
unsafe impl Sync for FpSet {}

/// What the disk tier says about a fingerprint (`FpSet::on_disk`).
enum OnDisk {
    No,
    /// No, and a merge of runs is ready to be installed (ask for a
    /// safepoint).
    NoMergeReady,
    Yes,
    /// An IO error.
    Error,
}

/// The set is full (raise the fingerprint memory, or grow the table).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Full;

#[inline]
fn norm(fp: u64) -> u64 {
    if fp == 0 {
        1
    } else {
        fp
    }
}

impl FpSet {
    /// A set of size `config`.
    pub fn with_config(config: FpConfig) -> FpSet {
        let mem = Arc::new(Gauge::new());
        let ovf_cap = config.overflow_cap.unwrap_or(usize::MAX);
        let t = Table::new(config.initial.max(MIN_SLOTS), 0, mem.clone(), ovf_cap);
        let peak = t.bytes();
        let s = FpSet {
            limit: AtomicUsize::new(config.limit.max(t.n)),
            shards: 1 << config.bits.min(MAX_BITS),
            table: Padded(UnsafeCell::new(t)),
            count: Count::new(),
            grows: AtomicU64::new(0),
            grow_ns: AtomicU64::new(0),
            peak_bytes: AtomicUsize::new(peak),
            disk: UnsafeCell::new(None),
            spill: None,
            rotations: AtomicU64::new(0),
            rotate_ns: AtomicU64::new(0),
            mem,
            tables: Part::default(),
            old_bytes: AtomicUsize::new(0),
        };
        s.account();
        s
    }

    /// The set with a disk tier in `spill`: when it can grow no more, it
    /// rotates to disk (`rotate`) instead of filling up.
    pub fn with_disk(self, spill: Spill) -> FpSet {
        FpSet { spill: Some(spill), ..self }
    }

    /// A set of a fixed size, able to hold about `max_entries` fingerprints.
    pub fn new(max_entries: usize) -> FpSet {
        let slots = max_entries.checked_mul(HARD_DEN).map(|n| n / HARD_NUM).expect("fingerprint set too large");
        FpSet::with_config(FpConfig::fixed(slots))
    }

    #[inline]
    fn table(&self) -> &Table {
        // SAFETY: the table is replaced only with exclusive access (see
        // `grow`), never while this reference lives.
        unsafe { &*self.table.0.get() }
    }

    /// The disk tier, if the set has rotated.
    #[inline]
    fn disk(&self) -> Option<&Disk> {
        // SAFETY: as `table`.
        unsafe { (*self.disk.get()).as_deref() }
    }

    /// The disk tier, for a change.
    ///
    /// # Safety
    /// Exclusive access (as `grow`).
    #[allow(clippy::mut_from_ref)]
    unsafe fn disk_mut(&self) -> Option<&mut Disk> {
        // SAFETY: this function's contract.
        unsafe { (*self.disk.get()).as_deref_mut() }
    }

    /// Insert `fp`; returns `Ok(true)` if it was not present before.
    #[inline]
    pub fn try_insert(&self, fp: u64) -> Result<bool, Full> {
        self.insert(fp, &mut 0, || {})
    }

    /// Insert `fp`, adding to `probes` the slots probed beyond the first.
    /// Calls `high` (once per table) when this insert brings a growable
    /// table to its high watermark: the caller should have it grow soon.
    /// `Full`: the table is at its hard limit (or, very unlikely, the
    /// probe ran off the overflow area); growing it would help if
    /// `growable`.
    #[inline]
    pub fn insert(&self, fp: u64, probes: &mut u64, high: impl FnOnce()) -> Result<bool, Full> {
        self.insert_by(count::this_thread(), fp, probes, high)
    }

    /// `insert` by worker `me` of a search (several threads with the same
    /// `me` are correct, but slower).
    #[inline]
    pub fn insert_by(&self, me: usize, fp: u64, probes: &mut u64, high: impl FnOnce()) -> Result<bool, Full> {
        let fp = norm(fp);
        let t = self.table();
        // (The disk tier is asked once, at the first empty slot.)
        let mut asked = false;
        let mut ask = false;
        let mut flushed = 0;
        let inserted = t.insert_with(fp, probes, || {
            flushed = self.count.flushed();
            if flushed >= t.hard_at {
                return Err(Full);
            }
            if !asked && self.spilling() {
                asked = true;
                match self.on_disk(fp) {
                    OnDisk::No => {}
                    OnDisk::NoMergeReady => ask = true,
                    OnDisk::Yes => return Ok(Some(false)),
                    OnDisk::Error => return Err(Full),
                }
            }
            Ok(None)
        })?;
        if !inserted {
            return Ok(false);
        }
        // (Far below the watermarks, the number of entries is counted in
        // stripes: it cannot reach them.)
        if flushed < t.direct_at {
            self.count.add_striped(me);
            if ask {
                high();
            }
            return Ok(true);
        }
        if !t.drained.load(Ordering::Relaxed) && !t.drained.swap(true, Ordering::Relaxed) {
            self.count.drain();
        }
        let n = self.count.add_direct(1);
        let reached = n >= t.high_at && !t.high_reached.load(Ordering::Relaxed) && !t.high_reached.swap(true, Ordering::Relaxed);
        if ask || reached && (t.n < self.limit() || self.spill.is_some()) {
            high();
        }
        Ok(true)
    }

    /// Whether `fp` (normalized; not in the table) is in the disk tier
    /// (which exists), and whether a merge is ready to be installed.
    #[inline(never)]
    fn on_disk(&self, fp: u64) -> OnDisk {
        let d = self.disk().expect("the disk tier");
        match d.contains(fp) {
            Ok(true) => OnDisk::Yes,
            Ok(false) if d.merge_ready() => OnDisk::NoMergeReady,
            Ok(false) => OnDisk::No,
            // (Recorded in the spill directory.)
            Err(_) => OnDisk::Error,
        }
    }

    /// Insert `fp`, growing the table (or rotating it to disk) as needed,
    /// serially.
    ///
    /// # Safety
    /// No other thread uses the set meanwhile, except `len`.
    pub unsafe fn insert_exclusive(&self, fp: u64) -> Result<bool, Full> {
        let mut grow = false;
        loop {
            match self.insert(fp, &mut 0, || grow = true) {
                Ok(new) => {
                    if grow {
                        // SAFETY: as this function's. (At the limit
                        // without a disk tier it does not grow: the table
                        // fills up to its hard limit.)
                        unsafe { self.make_room() };
                    }
                    return Ok(new);
                }
                // SAFETY: as this function's.
                Err(Full) => {
                    if unsafe { !self.make_room() } {
                        return Err(Full);
                    }
                }
            }
        }
    }

    /// Serially: install a finished merge; if the table is at its high
    /// watermark, grow it, or rotate it to disk (a table of the same size)
    /// once it cannot grow. Whether the table changed.
    ///
    /// # Safety
    /// As `insert_exclusive`.
    unsafe fn make_room(&self) -> bool {
        // SAFETY: as this function's.
        unsafe {
            self.install_merge(false);
            if !self.at_high() {
                return false;
            }
            if self.spilling() || !self.growable() {
                return self.rotatable() && self.rotate(None, 0, self.slots(), true).is_ok();
            }
            self.grow(None)
        }
    }

    /// Whether the table can still grow.
    pub fn growable(&self) -> bool {
        self.table().n < self.limit()
    }

    /// Whether the set can rotate to disk (it has a disk tier, and no IO
    /// error happened).
    pub fn rotatable(&self) -> bool {
        self.spill.as_ref().is_some_and(|s| !s.failed())
    }

    /// Whether the table can grow or rotate (an insert refused at the hard
    /// limit can succeed after a safepoint).
    pub fn can_make_room(&self) -> bool {
        self.growable() || self.rotatable()
    }

    /// Whether the set has rotated to disk (it then rotates whenever its
    /// table is full, and never grows any more).
    #[inline]
    pub fn spilling(&self) -> bool {
        self.disk().is_some()
    }

    /// Whether the table has reached its high watermark.
    pub fn at_high(&self) -> bool {
        self.len() >= self.table().high_at
    }

    /// The first IO error of the disk tier (which stopped a rotation or a
    /// lookup), if any.
    pub fn io_error(&self) -> Option<IoError> {
        self.spill.as_ref().and_then(|s| s.error())
    }

    /// The number of times the set grew or rotated (changes when either
    /// happens).
    pub fn epoch(&self) -> u64 {
        self.grows.load(Ordering::Relaxed) + self.rotations.load(Ordering::Relaxed)
    }

    /// The home slots of the next table (`grow`): twice the current ones,
    /// at most the limit.
    pub fn next_slots(&self) -> usize {
        self.table().n.saturating_mul(2).min(self.limit())
    }

    /// The memory of a table of `slots` home slots.
    pub fn table_bytes(slots: usize) -> usize {
        Table::array_bytes(slots)
    }

    /// The most home slots whose table fits in `bytes` (`0` if even `OVERFLOW`
    /// does not fit).
    pub fn slots_for_bytes(bytes: usize) -> usize {
        Table::slots_for_bytes(bytes)
    }

    /// Slot limit corresponding to a memory budget `bytes` (`FpConfig::within`).
    pub fn max_slots_in(bytes: usize) -> usize {
        if bytes == usize::MAX {
            usize::MAX
        } else if bytes >= Table::array_bytes(COMPACT48_MIN_SLOTS) {
            Table::slots_for_bytes(bytes)
        } else {
            bytes / 8
        }
    }

    /// Old-table bytes retained concurrently with the destination table while
    /// `parts` threads stream and discard its units into a new table (capped
    /// at the old table's size).
    fn grow_retained_bytes(&self, parts: usize) -> usize {
        let old = self.table();
        let unit_slots = old.rehash_unit_slots(self.shards);
        if old.is_mapped() && old.slot_len() > unit_slots {
            old.overflow_bytes().saturating_add(parts.max(1).saturating_mul(old.unit_bytes(unit_slots))).min(old.bytes())
        } else {
            old.bytes()
        }
    }

    /// Peak physical bytes of old + destination tables during a `parts`-thread
    /// growth whose destination owns `new_bytes` (including overflow). Covers
    /// both expanding and tier-shrinking transitions.
    fn grow_tables_peak(&self, new_bytes: usize, parts: usize) -> usize {
        let old_bytes = self.table().bytes();
        let retained = self.grow_retained_bytes(parts);
        old_bytes.max(new_bytes).saturating_add(retained).min(old_bytes.saturating_add(new_bytes))
    }

    /// Peak physical bytes of the set while replacing the current table with
    /// one of `slots` home slots across `parts` threads (including bounded
    /// destination overflow segments and disk tier indexes).
    pub fn grow_peak_bytes(&self, slots: usize, parts: usize) -> usize {
        let new_bytes = Self::table_bytes(slots).saturating_add(self.table().max_grow_overflow_bytes(slots, self.table_len()));
        self.grow_tables_peak(new_bytes, parts).saturating_add(self.disk_bytes())
    }

    /// Most home slots (within `limit`) to which the set can grow inside
    /// `room` bytes across `parts` threads.
    pub fn grow_fit_slots(&self, room: usize, parts: usize) -> usize {
        let overhead = self.grow_retained_bytes(parts).saturating_add(self.disk_bytes());
        let mut fit = Self::slots_for_bytes(room.saturating_sub(overhead)).min(self.limit());
        if fit > self.slots() {
            let ovf = self.table().max_grow_overflow_bytes(fit, self.table_len());
            if ovf > 0 {
                fit = Self::slots_for_bytes(room.saturating_sub(overhead.saturating_add(ovf))).min(self.limit());
            }
        }
        fit
    }

    /// Never grow beyond `slots` home slots (nor beyond the current table).
    pub fn cap(&self, slots: usize) {
        self.limit.fetch_min(slots.max(self.table().n), Ordering::Relaxed);
    }

    /// Replace the table with one twice as large (at most the limit),
    /// inserting the fingerprints again on the workers of `crew` (or on the
    /// calling thread). Returns false (and changes nothing) if the table is
    /// at its limit.
    ///
    /// # Safety
    /// No other thread uses the set meanwhile, except `len` (and the
    /// workers of `crew`, through this function).
    pub unsafe fn grow(&self, crew: Option<&Crew<'_>>) -> bool {
        // SAFETY: as this function's.
        unsafe { self.grow_to(crew, 0, self.next_slots()) }
    }

    /// `grow`, to a table of `slots` home slots (at most the limit); false
    /// (and nothing changes) if that is not larger than the current table.
    /// With fewer than `threads` workers in `crew` (e.g. at a safepoint of a
    /// level expanded by one worker while the others wait at the level
    /// barrier), the fingerprints are inserted again by `threads` threads
    /// of its own instead.
    ///
    /// # Safety
    /// As `grow`.
    pub unsafe fn grow_to(&self, crew: Option<&Crew<'_>>, threads: usize, slots: usize) -> bool {
        let start = Instant::now();
        let old = self.table();
        let slots = slots.min(self.limit());
        if old.n >= slots {
            return false;
        }
        let len = old.slot_len();
        let unit_slots = old.rehash_unit_slots(self.shards);
        let parts = crew.map_or(1, |c| c.size()).max(threads).max(1);
        let new = Table::new(slots, old.base, self.mem.clone(), usize::MAX);
        self.peak_bytes.fetch_max(self.grow_tables_peak(new.array_bytes_now(), parts).saturating_add(self.disk_bytes()), Ordering::Relaxed);
        if old.is_mapped() && len > unit_slots {
            let units = len.div_ceil(unit_slots);
            let next = AtomicUsize::new(0);
            let rehash = |_part: usize| loop {
                let u = next.fetch_add(1, Ordering::Relaxed);
                if u >= units {
                    break;
                }
                let lo = u * unit_slots;
                let hi = ((u + 1) * unit_slots).min(len);
                old.rehash_range(lo, hi, &new);
                // SAFETY: each unit `u` is claimed once, `rehash_range` reads
                // only `lo..hi` (and `old.overflow`, which stays live until
                // `old` drops), and `unit_slots` aligns to `Line` and OS page
                // boundaries.
                unsafe { old.discard_slot_range(lo, hi) };
            };
            run_parts(crew, parts, rehash);
        } else {
            // Contiguous ranges of the old table (the shards of `-fpbits`, or
            // more ranges than workers, for balance), taken in turn by the
            // parts of the broadcast.
            let ranges = self.shards.max(4 * parts).min(len.div_ceil(4096)).max(1);
            let rehash = |part: usize| {
                for r in (part..ranges).step_by(parts) {
                    let (lo, hi) = (len * r / ranges, len * (r + 1) / ranges);
                    old.rehash_range(lo, hi, &new);
                }
            };
            run_parts(crew, parts, rehash);
        }
        let actual_peak = self.grow_tables_peak(new.bytes(), parts).saturating_add(self.disk_bytes());
        self.peak_bytes.fetch_max(actual_peak.max(new.bytes() + self.disk_bytes()), Ordering::Relaxed);
        // SAFETY: exclusive access (this function's contract); `old` is not
        // used any more.
        unsafe {
            *self.table.0.get() = new;
        }
        self.account();
        self.grows.fetch_add(1, Ordering::Relaxed);
        self.grow_ns.fetch_add(start.elapsed().as_nanos() as u64, Ordering::Relaxed);
        true
    }

    /// Rotate to disk: write the table as a sorted run (on the workers of
    /// `crew`, or on `threads` threads of its own, see `grow_to`), then
    /// replace it with an empty table of `slots` home slots; with `keep`,
    /// the table stays in memory read-only (the old table, replacing the
    /// previous one), else it is freed. On an IO error (also recorded in
    /// the spill directory) nothing changes.
    ///
    /// # Safety
    /// As `grow`.
    pub unsafe fn rotate(&self, crew: Option<&Crew<'_>>, threads: usize, slots: usize, keep: bool) -> Result<(), IoError> {
        let start = Instant::now();
        let spill = self.spill.as_ref().expect("a fingerprint set without a disk tier rotates");
        let store = match self.disk() {
            Some(d) => d.store.clone(),
            None => {
                let d = Disk::new(spill.store_cached("fpset")?, self.mem.clone());
                let store = d.store.clone();
                // SAFETY: exclusive access (this function's contract).
                unsafe { *self.disk.get() = Some(Box::new(d)) };
                store
            }
        };
        let t = self.table();
        let run = write_run(t, &store, crew, threads, self.table_len())?;
        // (The previous old table goes before the new table comes.)
        // SAFETY: exclusive access.
        unsafe { self.drop_old() };
        self.peak_bytes.fetch_max(t.bytes() + self.disk_bytes() + run.bytes(), Ordering::Relaxed);
        // SAFETY: exclusive access; `t` is not used any more.
        let table = unsafe {
            std::mem::replace(&mut *self.table.0.get(), Table::new(slots.max(MIN_SLOTS), self.len(), self.mem.clone(), usize::MAX))
        };
        // SAFETY: exclusive access.
        unsafe { self.disk_mut() }.expect("the disk tier").add(run, keep.then_some(table));
        self.account();
        self.peak_bytes.fetch_max(self.bytes(), Ordering::Relaxed);
        self.rotations.fetch_add(1, Ordering::Relaxed);
        self.rotate_ns.fetch_add(start.elapsed().as_nanos() as u64, Ordering::Relaxed);
        Ok(())
    }

    /// Install a finished background merge of runs (with `wait`: wait for
    /// one in progress).
    ///
    /// # Safety
    /// As `grow`.
    pub unsafe fn install_merge(&self, wait: bool) {
        // SAFETY: this function's contract.
        if let Some(d) = unsafe { self.disk_mut() } {
            d.install_merge(wait);
            self.account();
        }
    }

    /// Drop the old table (its run stays on disk): memory for a search
    /// under pressure.
    ///
    /// # Safety
    /// As `grow`.
    pub unsafe fn drop_old(&self) {
        // SAFETY: this function's contract.
        if let Some(d) = unsafe { self.disk_mut() } {
            d.drop_old();
            self.account();
        }
    }

    /// Publish the memory of the table arrays and runs (after they changed,
    /// with exclusive access). Displacement-overflow segments charge `self.mem`
    /// directly as they are allocated and dropped, so they are excluded here.
    fn account(&self) {
        let old = self.disk().map_or(0, Disk::old_bytes);
        self.old_bytes.store(old, Ordering::Relaxed);
        let old_array = self.disk().map_or(0, Disk::old_array_bytes);
        self.tables.set(&self.mem, self.table().array_bytes_now() + old_array + self.disk().map_or(0, Disk::runs_bytes));
    }

    /// The gauge of the set's memory (`bytes`, as published).
    pub fn gauge(&self) -> &Arc<Gauge> {
        &self.mem
    }

    /// The memory of the old table, the Bloom filters and indexes of the
    /// runs, and a merge in progress.
    fn disk_bytes(&self) -> usize {
        self.disk().map_or(0, |d| d.old_bytes() + d.index_bytes())
    }

    /// The memory of the Bloom filters and indexes of the runs (and of a
    /// merge in progress).
    pub fn index_bytes(&self) -> usize {
        self.disk().map_or(0, |d| d.index_bytes())
    }

    /// The memory of the old table (published by `account`; safe to read
    /// concurrently with exclusive-access updates).
    pub fn old_bytes(&self) -> usize {
        self.old_bytes.load(Ordering::Relaxed)
    }

    /// The memory the next rotation adds: the Bloom filter and index of a
    /// run of the table's entries.
    pub fn next_run_bytes(&self) -> usize {
        Run::bytes_for(self.table_len())
    }

    /// The disk tier's numbers, if the set rotated.
    pub fn disk_stats(&self) -> Option<DiskStats> {
        self.disk().map(|d| d.stats())
    }

    /// The number of times the set rotated to disk, and the time it took.
    pub fn rotations(&self) -> (u64, std::time::Duration) {
        (self.rotations.load(Ordering::Relaxed), std::time::Duration::from_nanos(self.rotate_ns.load(Ordering::Relaxed)))
    }

    /// The number of entries of the current table.
    pub fn table_len(&self) -> usize {
        self.len() - self.table().base
    }

    /// The number of home slots of the current table.
    pub fn slots(&self) -> usize {
        self.table().n
    }

    /// The most home slots the table may grow to.
    pub fn limit(&self) -> usize {
        self.limit.load(Ordering::Relaxed)
    }

    /// The number of shards (`-fpbits`).
    pub fn shards(&self) -> usize {
        self.shards
    }

    /// The memory of the set: the current table, and the old table, the
    /// Bloom filters and the indexes of the disk tier.
    pub fn bytes(&self) -> usize {
        self.table().bytes() + self.disk_bytes()
    }

    /// The memory of the current table.
    pub fn table_bytes_now(&self) -> usize {
        self.table().bytes()
    }

    /// The largest memory of the set at once (during a growth, both
    /// tables; with the disk tier, both tables and its indexes; includes live
    /// displacement-overflow segment allocations).
    pub fn peak_bytes(&self) -> usize {
        self.peak_bytes.load(Ordering::Relaxed).max(self.mem.peak())
    }

    /// The number of times the table grew, and the time it took.
    pub fn grows(&self) -> (u64, std::time::Duration) {
        (self.grows.load(Ordering::Relaxed), std::time::Duration::from_nanos(self.grow_ns.load(Ordering::Relaxed)))
    }

    /// Checkpoints: call `f` with the fingerprints of part `part` of
    /// `parts` of the current table (0 as 1), in ascending order (sorting
    /// each probe cluster into a scratch buffer without mutating the table);
    /// stops at the first error. The parts, in order, are the table's
    /// fingerprints in ascending order, and the fingerprints of the set are
    /// those of the table and of the runs (`run_count`, `for_each_in_run`);
    /// several threads may each take parts, as a rotation does.
    ///
    /// # Safety
    /// As `grow`, except that other threads may call this function too
    /// (for other parts).
    pub unsafe fn for_each_in_table_part(
        &self,
        part: usize,
        parts: usize,
        mut f: impl FnMut(u64) -> Result<(), String>,
    ) -> Result<(), String> {
        let t = self.table();
        let len = t.slot_len();
        let (lo, hi) = (len * part / parts, len * (part + 1) / parts);
        t.sorted_clusters(lo, hi, |fp| f(fp).map_err(IoError)).map_err(|e| e.0)
    }

    /// The slots of the current table (sizing `for_each_in_table_part`).
    pub fn table_slots(&self) -> usize {
        self.table().slot_len()
    }

    /// The number of runs on disk.
    pub fn run_count(&self) -> usize {
        self.disk().map_or(0, |d| d.run_count())
    }

    /// The id of run `k`: unique in the process, and the same as long as
    /// the run exists (its fingerprints never change).
    pub fn run_id(&self, k: usize) -> u64 {
        self.disk().expect("a disk tier").run_id(k)
    }

    /// The number of fingerprints of run `k`.
    pub fn run_len(&self, k: usize) -> u64 {
        self.disk().expect("a disk tier").run_len(k)
    }

    /// Call `f` with the fingerprints of run `k` in ascending order; stops
    /// at the first error (of `f`, or reading the run back).
    pub fn for_each_in_run(&self, k: usize, f: impl FnMut(u64) -> Result<(), String>) -> Result<(), String> {
        self.disk().expect("a disk tier").for_each_in_run(k, f)
    }

    /// Recovering: make the table large enough for `n` more entries below
    /// its high watermark (growing it to twice that, within its limit and
    /// `max_slots`), so that inserting them in ascending order (as a
    /// checkpoint has them) does not pile them up in the part of a smaller
    /// table their high bits select. Whether they fit.
    ///
    /// # Safety
    /// As `grow`.
    pub unsafe fn reserve(&self, n: usize, max_slots: usize) -> bool {
        let t = self.table();
        if t.high_at.saturating_sub(self.len()) >= n {
            return true;
        }
        let want = n.saturating_add(self.table_len()).saturating_mul(2).min(max_slots).min(self.limit());
        if Table::high_of(want) < n.saturating_add(self.table_len()) {
            // (It would not fit: the table stays as it is.)
            return false;
        }
        // SAFETY: this function's contract.
        unsafe { self.grow_to(None, 0, want) };
        let t = self.table();
        t.high_at.saturating_sub(self.len()) >= n
    }

    /// Whether the set can take runs (`add_run`): it has a disk tier.
    pub fn takes_runs(&self) -> bool {
        self.rotatable() && self.table_len() == 0
    }

    /// Recovering: add the `n` fingerprints of `chunks` (ascending, not in
    /// the set) as a run on disk (the table must be empty, `takes_runs`).
    ///
    /// # Safety
    /// As `grow`.
    pub unsafe fn add_run(&self, n: usize, chunks: &mut dyn FnMut() -> Result<Option<Vec<u64>>, String>) -> Result<(), String> {
        assert!(self.takes_runs(), "add_run: a set without a disk tier, or with a table not empty");
        let spill = self.spill.as_ref().expect("a disk tier");
        if self.disk().is_none() {
            let d = Disk::new(spill.store_cached("fpset").map_err(|e| e.0)?, self.mem.clone());
            // SAFETY: exclusive access (this function's contract).
            unsafe { *self.disk.get() = Some(Box::new(d)) };
        }
        let store = self.disk().expect("the disk tier").store.clone();
        let bloom = bloom::Bloom::new(n);
        let mut w = PieceWriter::new(&store, &bloom);
        let mut count = 0usize;
        let mut last = None;
        while let Some(c) = chunks()? {
            for fp in c {
                if last.is_some_and(|l| fp <= l) {
                    return Err("fingerprints out of order".into());
                }
                last = Some(fp);
                w.push(fp).map_err(|e| e.0)?;
                count += 1;
            }
        }
        if count != n {
            return Err(format!("{count} fingerprints, {n} expected"));
        }
        let piece = w.finish().map_err(|e| e.0)?;
        let run = assemble(store, vec![piece], bloom);
        self.count.add_direct(count);
        // (The empty table takes the inserts after these entries.)
        let slots = self.table().n;
        // SAFETY: exclusive access; the old table is empty and not used any more.
        unsafe { *self.table.0.get() = Table::new(slots, self.len(), self.mem.clone(), usize::MAX) };
        // SAFETY: exclusive access.
        unsafe { self.disk_mut() }.expect("the disk tier").add_loaded(run);
        self.account();
        self.peak_bytes.fetch_max(self.bytes(), Ordering::Relaxed);
        Ok(())
    }

    /// Whether the set holds `fp` (an IO error of the disk tier counts as
    /// no).
    #[inline]
    pub fn contains(&self, fp: u64) -> bool {
        let fp = norm(fp);
        self.table().contains(fp) || self.disk().is_some_and(|d| d.contains(fp).unwrap_or(false))
    }

    /// The number of entries (exact when no insert is in progress).
    pub fn len(&self) -> usize {
        self.count.get()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Maximum number of entries of the current table before inserts fail.
    pub fn max_entries(&self) -> usize {
        self.table().hard
    }

    /// The number of entries at which the current table asks to grow.
    pub fn high(&self) -> usize {
        self.table().high
    }
}

/// Run `f(part)` for `part` in `0..parts`: on the workers of `crew` if it
/// has as many, else on threads of its own.
fn run_parts(crew: Option<&Crew<'_>>, parts: usize, f: impl Fn(usize) + Sync) {
    match crew {
        Some(c) if parts > 1 && c.size() == parts => c.broadcast(f),
        _ if parts > 1 => {
            let pool = tlx_base::par::Pool { threads: parts, stack: tlx_base::par::Stack::Default };
            pool.for_each_part(|_, part| f(part));
        }
        _ => f(0),
    }
}

/// Write the `entries` fingerprints of table `t` to `store` as a run, on
/// the workers of `crew` or `threads` threads (see `FpSet::rotate`): each
/// takes contiguous ranges of slots, sorts their clusters into a scratch
/// buffer and writes them as pieces of the run, in order. On an error, the
/// blocks written are deleted.
fn write_run(t: &Table, store: &Arc<BlockStore>, crew: Option<&Crew<'_>>, threads: usize, entries: usize) -> Result<Run, IoError> {
    let bloom = bloom::Bloom::new(entries);
    let len = t.slot_len();
    let parts = crew.map_or(1, |c| c.size()).max(threads).max(1);
    // (Ranges of about a block of entries, at least one per part.)
    let ranges = (entries / BLOCK_FPS + 1).max(parts).min(len.div_ceil(4096)).max(1);
    let pieces: Vec<parking_lot::Mutex<Option<Result<disk::Piece, IoError>>>> =
        (0..ranges).map(|_| parking_lot::Mutex::new(None)).collect();
    let write = |part: usize| {
        for r in (part..ranges).step_by(parts) {
            let (lo, hi) = (len * r / ranges, len * (r + 1) / ranges);
            let mut w = PieceWriter::new(store, &bloom);
            let res = t.sorted_clusters(lo, hi, |fp| w.push(fp)).and_then(|()| w.finish());
            *pieces[r].lock() = Some(res);
        }
    };
    run_parts(crew, parts, write);
    let mut out = Vec::with_capacity(ranges);
    let mut err = None;
    for p in pieces {
        match p.into_inner().expect("a piece of the run") {
            Ok(p) => out.push(p),
            Err(e) => {
                err.get_or_insert(e);
            }
        }
    }
    if let Some(e) = err {
        for p in out {
            disk::discard(store, p);
        }
        return Err(e);
    }
    Ok(assemble(store.clone(), out, bloom))
}

#[cfg(test)]
mod tests;
