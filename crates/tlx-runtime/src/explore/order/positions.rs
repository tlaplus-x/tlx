//! Compact BFS level metadata: per-parent successor counts (`Counts`), the
//! per-level new-class bit filter (`NewClasses`), per-worker position tables
//! (`Table`), and level-wide BFS positions (`Positions`).

use std::collections::HashMap;
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};
use std::sync::Arc;

use parking_lot::Mutex;
use tlx_base::hash::FxMap;

use super::super::tracelog::{split_log_ref, LogRef};
use crate::mem::{Gauge, Part};

/// Sentinel value in `Counts::values` indicating the exact `u64` count for
/// that parent lives in `Counts::overflow`.
const COUNT_OVERFLOW: u32 = u32::MAX;

/// std's Swiss table: power-of-two buckets, one control byte per bucket,
/// and a control group. Include empty reserved buckets, not just entries.
pub(super) fn map_bytes<K, V, S>(map: &HashMap<K, V, S>) -> usize {
    if map.capacity() == 0 {
        return 0;
    }
    let buckets = (map.capacity() + 1).next_power_of_two();
    buckets * (std::mem::size_of::<(K, V)>() + 1) + 16
}

/// Charge allocations until their last owner releases them, including old
/// position tables still read by workers after a level changes.
#[derive(Default)]
pub(super) struct Charge(Mutex<Option<(Arc<Gauge>, Part)>>);

impl Charge {
    pub(super) fn set(&self, gauge: &Arc<Gauge>, bytes: usize) {
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

/// Per-parent count of kept successors in the level being resolved: 4 B per
/// parent in the common case (`< u32::MAX`), with a cold `u64` overflow map
/// when a parent keeps `>= u32::MAX` successors.
pub(super) struct Counts {
    values: Box<[AtomicU32]>,
    overflow: Mutex<Option<Box<FxMap<usize, u64>>>>,
    charge: Charge,
}

impl Counts {
    pub(super) fn zeros(n: u64, gauge: &Arc<Gauge>) -> Arc<Counts> {
        let n = usize::try_from(n).expect("level size fits in usize");
        // (Zeroed memory from the allocator: pages are cleared when touched.)
        let zeros: Box<[u32]> = vec![0u32; n].into_boxed_slice();
        const _: () = assert!(
            std::mem::size_of::<AtomicU32>() == std::mem::size_of::<u32>()
                && std::mem::align_of::<AtomicU32>() == std::mem::align_of::<u32>()
        );
        // SAFETY: AtomicU32 has the size and alignment of u32 (checked above)
        // and the same in-memory representation; the box is uniquely owned.
        let values: Box<[AtomicU32]> = unsafe { Box::from_raw(Box::into_raw(zeros) as *mut [AtomicU32]) };
        let counts = Arc::new(Counts { values, overflow: Mutex::new(None), charge: Charge::default() });
        counts.account(gauge);
        counts
    }

    /// Record the number of kept successors for `parent` (called at most once
    /// per parent during a level's `resolve`).
    #[inline]
    pub(super) fn store(&self, parent: usize, count: u64, gauge: &Arc<Gauge>) {
        if count < COUNT_OVERFLOW as u64 {
            self.values[parent].store(count as u32, Ordering::Relaxed);
        } else {
            self.store_overflow(parent, count, gauge);
        }
    }

    #[cold]
    #[inline(never)]
    fn store_overflow(&self, parent: usize, count: u64, gauge: &Arc<Gauge>) {
        {
            let mut ov = self.overflow.lock();
            ov.get_or_insert_with(Default::default).insert(parent, count);
        }
        self.values[parent].store(COUNT_OVERFLOW, Ordering::Relaxed);
        self.account(gauge);
    }

    /// Reconstruct exact `u64` prefix sums `(first, total_len)` after every
    /// worker has finished resolving the level.
    pub(super) fn prefix_sums(&self) -> (Box<[u64]>, u64) {
        let mut first = Vec::with_capacity(self.values.len());
        let ov = self.overflow.lock();
        let mut len = 0u64;
        for (parent, c) in self.values.iter().enumerate() {
            first.push(len);
            let v = c.load(Ordering::Relaxed);
            let count =
                if v == COUNT_OVERFLOW { *ov.as_ref().and_then(|m| m.get(&parent)).expect("overflow parent count") } else { v as u64 };
            len = len.checked_add(count).expect("level state count overflow");
        }
        (first.into_boxed_slice(), len)
    }

    fn account(&self, gauge: &Arc<Gauge>) {
        let ov_bytes = self.overflow.lock().as_ref().map_or(0, |m| std::mem::size_of::<FxMap<usize, u64>>() + map_bytes(m));
        self.charge.set(
            gauge,
            std::mem::size_of::<Counts>()
                + 2 * std::mem::size_of::<usize>()
                + self.values.len() * std::mem::size_of::<AtomicU32>()
                + ov_bytes,
        );
    }

    #[cfg(test)]
    pub(super) fn get(&self, parent: usize) -> u64 {
        let v = self.values[parent].load(Ordering::Relaxed);
        if v == COUNT_OVERFLOW {
            *self.overflow.lock().as_ref().and_then(|m| m.get(&parent)).expect("overflow parent count")
        } else {
            v as u64
        }
    }
}

/// The classes inserted into the seen set while expanding a level, as a
/// filter on their fingerprints: a clear bit tells that a class in the seen
/// set was found at an earlier level, so a successor of it is no candidate
/// (see the parent module). A class's bit is set before it is inserted into
/// the seen set (whose insertion releases, and whose lookup acquires), so a
/// worker that finds the class there sees its bit; bits are only set during
/// a level. A set bit may also be another class's (the slow path then
/// decides).
pub(super) struct NewClasses {
    pub(super) words: Box<[AtomicU64]>,
    _charge: Charge,
}

impl NewClasses {
    /// A filter for the classes new at the level after one of `states`
    /// states: about 16 bits per state (a level has rarely more new
    /// classes than twice the previous one's states), within 2^12..2^28
    /// bits.
    pub(super) fn new(states: u64, gauge: &Arc<Gauge>) -> NewClasses {
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
    pub(super) fn mark(&self, fp: u64) {
        let (w, bit) = self.at(fp);
        if w.load(Ordering::Relaxed) & bit == 0 {
            w.fetch_or(bit, Ordering::Relaxed);
        }
    }

    /// Whether class `fp`, found in the seen set, may have been inserted at
    /// this level.
    #[inline]
    pub(super) fn may_hold(&self, fp: u64) -> bool {
        let (w, bit) = self.at(fp);
        w.load(Ordering::Relaxed) & bit != 0
    }
}

/// Compact per-state `(parent_pos, rank)` entries: 8 B/state in the narrow
/// common case (`<= u32::MAX`), widening to 16 B/state only when parent level
/// width or max rank exceeds `u32::MAX`.
pub(super) enum TableEntries {
    Narrow(Vec<(u32, u32)>),
    Wide(Vec<(u64, u64)>),
}

impl TableEntries {
    pub(super) fn with_capacity(len: usize, wide: bool) -> TableEntries {
        if wide {
            TableEntries::Wide(Vec::with_capacity(len))
        } else {
            TableEntries::Narrow(Vec::with_capacity(len))
        }
    }

    pub(super) fn zeroed(len: usize, wide: bool) -> TableEntries {
        if wide {
            TableEntries::Wide(vec![(0, 0); len])
        } else {
            TableEntries::Narrow(vec![(0, 0); len])
        }
    }

    #[inline]
    pub(super) fn push(&mut self, parent_pos: u64, rank: u64) {
        match self {
            TableEntries::Narrow(v) => {
                if let (Ok(p), Ok(r)) = (u32::try_from(parent_pos), u32::try_from(rank)) {
                    v.push((p, r));
                } else {
                    self.widen();
                    let TableEntries::Wide(w) = self else { unreachable!() };
                    w.push((parent_pos, rank));
                }
            }
            TableEntries::Wide(v) => v.push((parent_pos, rank)),
        }
    }

    #[inline]
    pub(super) fn set(&mut self, index: usize, parent_pos: u64, rank: u64) {
        match self {
            TableEntries::Narrow(v) => {
                if let (Ok(p), Ok(r)) = (u32::try_from(parent_pos), u32::try_from(rank)) {
                    v[index] = (p, r);
                } else {
                    self.widen();
                    let TableEntries::Wide(w) = self else { unreachable!() };
                    w[index] = (parent_pos, rank);
                }
            }
            TableEntries::Wide(v) => v[index] = (parent_pos, rank),
        }
    }

    #[cold]
    #[inline(never)]
    fn widen(&mut self) {
        if let TableEntries::Narrow(v) = self {
            let mut wide = Vec::with_capacity(v.capacity());
            wide.extend(v.iter().map(|&(p, r)| (p as u64, r as u64)));
            *self = TableEntries::Wide(wide);
        }
    }

    #[inline]
    pub(super) fn get(&self, index: usize) -> (u64, u64) {
        match self {
            TableEntries::Narrow(v) => {
                let (p, r) = v[index];
                (p as u64, r as u64)
            }
            TableEntries::Wide(v) => v[index],
        }
    }

    pub(super) fn bytes(&self) -> usize {
        match self {
            TableEntries::Narrow(v) => v.capacity() * std::mem::size_of::<(u32, u32)>(),
            TableEntries::Wide(v) => v.capacity() * std::mem::size_of::<(u64, u64)>(),
        }
    }

    #[cfg(test)]
    pub(super) fn is_wide(&self) -> bool {
        matches!(self, TableEntries::Wide(_))
    }
}

/// The states of a level logged by one worker: for the trace-log entries
/// from `start` on, the position of the parent and the rank among the
/// parent's states of the level (entries that are not states of the level
/// are not looked up).
pub(in crate::explore) struct Table {
    start: usize,
    entries: TableEntries,
    charge: Charge,
}

impl Table {
    pub(super) fn new(start: usize, entries: TableEntries, charge: Charge) -> Table {
        Table { start, entries, charge }
    }

    pub(super) fn account(&self, gauge: &Arc<Gauge>) {
        self.charge.set(gauge, std::mem::size_of::<Self>() + 2 * std::mem::size_of::<usize>() + self.entries.bytes());
    }
}

/// The positions of the states of a level in BFS order.
pub struct Positions {
    /// Per worker log, its states of the level.
    tables: Vec<Option<Arc<Table>>>,
    /// Per state of the previous level (by position), the position of its
    /// first state in this level.
    first: Box<[u64]>,
    /// The number of states of the level.
    pub(super) len: u64,
    charge: Charge,
}

impl Positions {
    pub(super) fn from_parts(tables: Vec<Option<Arc<Table>>>, first: Box<[u64]>, len: u64) -> Positions {
        Positions { tables, first, len, charge: Charge::default() }
    }

    /// The positions of the states logged at `refs`, in this order (initial
    /// states).
    pub(in crate::explore) fn of_seq(refs: &[LogRef]) -> Positions {
        Self::of(refs.len(), refs.iter().enumerate().map(|(j, &r)| (r, j as u64)))
    }

    /// The positions of the states of a level as `(trace-log entry,
    /// position)` (the first level of a resumed search). Each position
    /// below `places.len()` must occur once.
    pub(in crate::explore) fn of_places(places: &[(LogRef, u64)]) -> Result<Positions, &'static str> {
        let mut taken = vec![false; places.len()];
        for &(_, p) in places {
            let slot = usize::try_from(p).ok().and_then(|p| taken.get_mut(p)).ok_or("a position past the level")?;
            if std::mem::replace(slot, true) {
                return Err("a position twice");
            }
        }
        Ok(Self::of(places.len(), places.iter().copied()))
    }

    /// The positions of the `len` states `places` gives (iterated twice:
    /// to size the tables, then to fill them).
    fn of(len: usize, places: impl Iterator<Item = (LogRef, u64)> + Clone) -> Positions {
        let mut tables: Vec<Option<Table>> = Vec::new();
        let mut span: Vec<(usize, usize, u64)> = Vec::new();
        for (r, j) in places.clone() {
            let (w, i) = split_log_ref(r);
            if span.len() <= w {
                span.resize(w + 1, (usize::MAX, 0, 0));
            }
            let (lo, hi, max_j) = span[w];
            span[w] = (lo.min(i), hi.max(i + 1), max_j.max(j));
        }
        for &(lo, hi, max_j) in &span {
            tables.push((lo < hi).then(|| {
                let wide = max_j > u32::MAX as u64;
                Table::new(lo, TableEntries::zeroed(hi - lo, wide), Charge::default())
            }));
        }
        for (r, j) in places {
            let (w, i) = split_log_ref(r);
            let t = tables[w].as_mut().expect("a table");
            t.entries.set(i - t.start, 0, j);
        }
        Positions {
            tables: tables.into_iter().map(|t| t.map(Arc::new)).collect(),
            first: Box::new([0]),
            len: len as u64,
            charge: Charge::default(),
        }
    }

    pub(super) fn account(&self, gauge: &Arc<Gauge>) {
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
    pub(in crate::explore) fn pos(&self, log: LogRef) -> u64 {
        let (w, i) = split_log_ref(log);
        let t = self.tables.get(w).and_then(|t| t.as_deref()).expect("a state of the level");
        let (p, j) = t.entries.get(i - t.start);
        self.first[p as usize] + j
    }
}
