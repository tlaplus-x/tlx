//! The blocks of queued states, and the memory they hold (docs/scale.md §5.1).
//!
//! A *block* is a group of states of the same depth, written by one worker:
//! `Block::Objects` (a vector of `Task`s, no codec or a small queue) or
//! `Block::Encoded` (a range of records of a `Seg`, in one of the `Kind`
//! formats of `codec`). `Mem`, `Charge` and `Segment` account for the bytes
//! they hold, which the queue and the archive share.

use std::sync::Arc;

use parking_lot::Mutex;

use super::codec::{self, XorPrev};
use super::seg::{self, Seg};
use crate::io::IoError;
use crate::mem::{Gauge, Meter};

/// A borrowed state yielded during safepoint root scanning: either an object
/// state or its decoded encoding words.
pub(crate) enum StateRef<'a, S> {
    Obj(&'a S),
    Words(&'a [u64]),
}

/// A queued state: the state, its trace-log entry and its depth.
pub(crate) struct Task<S> {
    pub(crate) state: S,
    pub(crate) log: u64,
    pub(crate) depth: u32,
}

/// The maximum number of states of a block.
pub(crate) const BLOCK: usize = 256;

/// The memory held by a queue's blocks (counted by segments and blocks),
/// and the buffers of full-size segments no longer used.
#[derive(Default)]
pub(crate) struct Mem {
    gauge: Gauge,
    /// Free segment buffers (of capacity `seg_bytes`): reused rather than
    /// freed and allocated again (which costs page faults and `madvise`).
    pool: Mutex<Vec<Vec<u8>>>,
    seg_bytes: usize,
    /// The most free buffers kept in `pool`.
    pool_max: usize,
}

/// The most free segment buffers kept by a queue.
const POOL_MAX: usize = 64;

impl Mem {
    /// The memory of a queue of segments of `seg_bytes` (keeping free
    /// segment buffers if `pool`).
    pub(crate) fn new(seg_bytes: usize, pool: bool) -> Arc<Mem> {
        Arc::new(Mem { seg_bytes, pool_max: if pool { POOL_MAX } else { 0 }, ..Mem::default() })
    }

    fn add(&self, n: usize) {
        self.gauge.add(n);
    }

    fn sub(&self, n: usize) {
        self.gauge.sub(n);
    }

    /// The bytes held now.
    pub(crate) fn bytes(&self) -> usize {
        self.gauge.bytes()
    }

    /// The most bytes held at a time.
    pub(crate) fn peak(&self) -> usize {
        self.gauge.peak()
    }

    /// An empty segment buffer of capacity `seg_bytes`, if one is free.
    pub(super) fn reuse(&self) -> Option<Vec<u8>> {
        let data = self.pool.lock().pop()?;
        self.sub(data.capacity());
        Some(data)
    }

    /// Free idle segment buffers, returning the released capacity.
    pub(crate) fn clear_pool(&self) -> usize {
        let mut pool = self.pool.lock();
        let bytes = pool.iter().map(Vec::capacity).sum();
        pool.clear();
        self.sub(bytes);
        bytes
    }
}

impl Meter for Mem {
    fn gauge(&self) -> &Gauge {
        &self.gauge
    }
}

/// Bytes counted in a `Mem` until dropped.
pub(crate) struct Charge {
    bytes: usize,
    pub(super) mem: Arc<Mem>,
}

impl Charge {
    pub(super) fn new(bytes: usize, mem: &Arc<Mem>) -> Charge {
        mem.add(bytes);
        Charge { bytes, mem: mem.clone() }
    }

    /// Split off `bytes` of this charge.
    fn split(&mut self, bytes: usize) -> Charge {
        let bytes = bytes.min(self.bytes);
        self.bytes -= bytes;
        Charge { bytes, mem: self.mem.clone() }
    }

    /// Transfer the full charged byte count out of `self` into a new `Charge`
    /// without releasing the memory accounting in between.
    pub(super) fn take(&mut self) -> Charge {
        let bytes = std::mem::replace(&mut self.bytes, 0);
        Charge { bytes, mem: self.mem.clone() }
    }

    /// Count these bytes in `mem` from now on.
    pub(super) fn move_to(&mut self, mem: &Arc<Mem>) {
        if !Arc::ptr_eq(&self.mem, mem) {
            self.mem.sub(self.bytes);
            mem.add(self.bytes);
            self.mem = mem.clone();
        }
    }
}

impl Drop for Charge {
    fn drop(&mut self) {
        self.mem.sub(self.bytes);
    }
}

/// A segment in memory: the records of the encoded blocks of one writer.
/// (Its charge moves to the archive with its first block, see
/// `Queue::append`.)
pub(crate) struct Segment {
    pub(super) data: Vec<u8>,
    pub(super) charge: Mutex<Charge>,
}

impl Drop for Segment {
    fn drop(&mut self) {
        let charge = self.charge.get_mut();
        let mem = &charge.mem;
        if self.data.capacity() == mem.seg_bytes {
            let mut pool = mem.pool.lock();
            if pool.len() < mem.pool_max {
                let mut data = std::mem::take(&mut self.data);
                data.clear();
                // Transfer the existing charge to the pool without a
                // transient double count in either bytes or the peak.
                debug_assert_eq!(charge.bytes, data.capacity());
                charge.bytes = 0;
                pool.push(data);
            }
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Kind {
    Raw,
    Xor,
}

/// A block of states of the same depth.
pub(crate) enum Block<S> {
    Objects {
        tasks: Vec<Task<S>>,
        _charge: Charge,
    },
    /// Bytes `start..end` of `seg`: `n` records of `kind`.
    Encoded {
        seg: Arc<Seg>,
        start: u32,
        end: u32,
        n: u32,
        kind: Kind,
        depth: u32,
    },
}

impl<S> Block<S> {
    pub(crate) fn len(&self) -> usize {
        match self {
            Block::Objects { tasks, .. } => tasks.len(),
            Block::Encoded { n, .. } => *n as usize,
        }
    }

    /// The depth of the states of this block (0 if empty).
    pub(crate) fn depth(&self) -> u32 {
        match self {
            Block::Objects { tasks, .. } => tasks.first().map_or(0, |t| t.depth),
            Block::Encoded { depth, .. } => *depth,
        }
    }

    /// Whether the states are encoded.
    pub(crate) fn encoded(&self) -> bool {
        matches!(self, Block::Encoded { .. })
    }

    /// Another handle on the records of an encoded block (sharing its
    /// segment, which stays charged where it is); None for a block of
    /// objects.
    pub(crate) fn share(&self) -> Option<Block<S>> {
        match self {
            Block::Objects { .. } => None,
            Block::Encoded { seg, start, end, n, kind, depth } => {
                Some(Block::Encoded { seg: seg.clone(), start: *start, end: *end, n: *n, kind: *kind, depth: *depth })
            }
        }
    }

    /// The states of a block of objects (none for an encoded block).
    pub(crate) fn into_tasks(self) -> Vec<Task<S>> {
        match self {
            Block::Objects { tasks, .. } => tasks,
            Block::Encoded { .. } => Vec::new(),
        }
    }

    /// Map the states of a block of objects with `f`; an encoded block is
    /// kept as it is.
    pub(crate) fn try_map<T, E>(self, f: impl Fn(S) -> Result<T, E>) -> Result<Block<T>, E> {
        Ok(match self {
            Block::Objects { tasks, _charge } => {
                let tasks =
                    tasks.into_iter().map(|t| Ok(Task { state: f(t.state)?, log: t.log, depth: t.depth })).collect::<Result<_, E>>()?;
                Block::Objects { tasks, _charge }
            }
            Block::Encoded { seg, start, end, n, kind, depth } => Block::Encoded { seg, start, end, n, kind, depth },
        })
    }

    /// Call `f(log, fp, words)` for each record of an encoded block (none
    /// for a block of objects), in order; `prev` is scratch of the
    /// encoding's width. Stops at the first error of `f` (the inner
    /// result); the outer one is an error reading a spilled segment. A
    /// spilled segment is read whole into `cache` (for the next blocks,
    /// which often share it), not back into memory for good.
    pub(crate) fn records<E>(
        &self,
        cache: &mut SegCache,
        prev: &mut XorPrev,
        mut f: impl FnMut(u64, u64, &[u64]) -> Result<(), E>,
    ) -> Result<Result<(), E>, IoError> {
        let Block::Encoded { seg, start, n, kind, .. } = self else { return Ok(Ok(())) };
        if !cache.seg.as_ref().is_some_and(|c| Arc::ptr_eq(c, seg)) {
            cache.bytes = None;
            cache.bytes = Some(seg.bytes()?);
            cache.seg = Some(seg.clone());
        }
        let data = match cache.bytes.as_ref().expect("cached segment") {
            seg::Bytes::Shared(s) => &s.data[..],
            seg::Bytes::Owned(v) => &v[..],
        };
        let mut pos = *start as usize;
        prev.reset();
        for _ in 0..*n {
            let (log, fp) = match kind {
                Kind::Raw => {
                    let size = codec::raw_size(prev.words.len());
                    let r = codec::get_raw(&data[pos..pos + size], &mut prev.words);
                    pos += size;
                    r
                }
                Kind::Xor => {
                    let fp = codec::get_xor(data, &mut pos, prev);
                    (prev.log, fp)
                }
            };
            if let Err(e) = f(log, fp, &prev.words) {
                return Ok(Err(e));
            }
        }
        Ok(Ok(()))
    }

    /// Visit every state in this block (as an object for `Block::Objects`, or
    /// as decoded words for `Block::Encoded`) for safepoint root scanning.
    pub(crate) fn visit_states(
        &self,
        cache: &mut SegCache,
        prev: &mut XorPrev,
        visit: &mut dyn FnMut(StateRef<'_, S>),
    ) -> Result<(), IoError> {
        self.visit_suffix(self.len(), cache, prev, visit)
    }

    /// Visit only the last `left` unread states in this block (for `Reader`
    /// safepoint scanning when consumed records are no longer retained for
    /// whole-block archival). For `Block::Objects`, consumed states were
    /// already popped so all remaining tasks are visited; for `Kind::Raw`
    /// encoded blocks the consumed prefix is skipped directly; for `Kind::Xor`
    /// encoded blocks the consumed prefix is decoded into `prev` scratch
    /// without invoking `visit` so the XOR state is reconstructed for the
    /// unread suffix.
    pub(crate) fn visit_suffix(
        &self,
        left: usize,
        cache: &mut SegCache,
        prev: &mut XorPrev,
        visit: &mut dyn FnMut(StateRef<'_, S>),
    ) -> Result<(), IoError> {
        if left == 0 {
            return Ok(());
        }
        match self {
            Block::Objects { tasks, .. } => {
                for t in tasks {
                    visit(StateRef::Obj(&t.state));
                }
                Ok(())
            }
            Block::Encoded { seg, start, n, kind, .. } => {
                let total = *n as usize;
                let skip = total.saturating_sub(left);
                if !cache.seg.as_ref().is_some_and(|c| Arc::ptr_eq(c, seg)) {
                    cache.bytes = None;
                    cache.bytes = Some(seg.bytes()?);
                    cache.seg = Some(seg.clone());
                }
                let data = match cache.bytes.as_ref().expect("cached segment") {
                    seg::Bytes::Shared(s) => &s.data[..],
                    seg::Bytes::Owned(v) => &v[..],
                };
                match kind {
                    Kind::Raw => {
                        let size = codec::raw_size(prev.words.len());
                        let mut pos = *start as usize + skip * size;
                        for _ in skip..total {
                            let _ = codec::get_raw(&data[pos..pos + size], &mut prev.words);
                            pos += size;
                            visit(StateRef::Words(&prev.words));
                        }
                    }
                    Kind::Xor => {
                        let mut pos = *start as usize;
                        prev.reset();
                        for i in 0..total {
                            let _ = codec::get_xor(data, &mut pos, prev);
                            if i >= skip {
                                visit(StateRef::Words(&prev.words));
                            }
                        }
                    }
                }
                Ok(())
            }
        }
    }

    /// The segment of an encoded block.
    pub(super) fn seg(&self) -> Option<&Arc<Seg>> {
        match self {
            Block::Objects { .. } => None,
            Block::Encoded { seg, .. } => Some(seg),
        }
    }

    /// Whether `split_last` can split this block.
    pub(super) fn splittable(&self) -> bool {
        !matches!(self, Block::Encoded { kind: Kind::Xor, .. })
    }

    /// Split off the last `k` states (0 < k < len, `splittable`): `(the
    /// others, the last k)`.
    pub(super) fn split_last(self, k: usize) -> (Block<S>, Block<S>) {
        debug_assert!(0 < k && k < self.len() && self.splittable());
        match self {
            Block::Objects { mut tasks, _charge: mut charge } => {
                let last = tasks.split_off(tasks.len() - k);
                let part = charge.split(charge.bytes * k / (k + tasks.len()));
                (Block::Objects { tasks, _charge: charge }, Block::Objects { tasks: last, _charge: part })
            }
            Block::Encoded { seg, start, end, n, kind, depth } => {
                let size = (end - start) / n;
                let mid = end - size * k as u32;
                let first = Block::Encoded { seg: seg.clone(), start, end: mid, n: n - k as u32, kind, depth };
                (first, Block::Encoded { seg, start: mid, end, n: k as u32, kind, depth })
            }
        }
    }
}

/// The bytes of the segment `Block::records` read last.
#[derive(Default)]
pub(crate) struct SegCache {
    seg: Option<Arc<Seg>>,
    bytes: Option<seg::Bytes>,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn segment(mem: &Arc<Mem>, data: Vec<u8>) -> Segment {
        Segment { charge: Mutex::new(Charge::new(data.capacity(), mem)), data }
    }

    #[test]
    fn pooled_capacity_is_counted_across_reuse_and_drain() {
        let mem = Mem::new(4096, true);
        for _ in 0..100 {
            let data = mem.reuse().unwrap_or_else(|| Vec::with_capacity(4096));
            assert_eq!(mem.bytes(), 0);
            let seg = segment(&mem, data);
            assert_eq!(mem.bytes(), 4096);
            drop(seg);
            assert_eq!(mem.bytes(), 4096);
            assert_eq!(mem.peak(), 4096);
        }
        // Draining idle buffers must leave a live segment's charge intact.
        let live = segment(&mem, Vec::with_capacity(4096));
        assert_eq!(mem.bytes(), 8192);
        assert_eq!(mem.clear_pool(), 4096);
        assert_eq!(mem.bytes(), 4096);
        assert!(mem.reuse().is_none());
        drop(live);
        assert_eq!(mem.clear_pool(), 4096);
        assert_eq!(mem.bytes(), 0);
        assert_eq!(mem.clear_pool(), 0);
    }

    #[test]
    fn pool_limit_and_ineligible_buffers_release_their_charge() {
        let mem = Mem::new(64, true);
        let segments: Vec<_> = (0..POOL_MAX + 1).map(|_| segment(&mem, Vec::with_capacity(64))).collect();
        drop(segments);
        assert_eq!(mem.bytes(), POOL_MAX * 64);
        drop(segment(&mem, Vec::with_capacity(128)));
        assert_eq!(mem.bytes(), POOL_MAX * 64);
        mem.clear_pool();
        assert_eq!(mem.bytes(), 0);
        let mem = Mem::new(64, false);
        drop(segment(&mem, Vec::with_capacity(64)));
        assert_eq!(mem.bytes(), 0);
        assert!(mem.reuse().is_none());
    }
}
