//! The frontier: the states (tasks) left to expand, in level queues of
//! blocks (`crate::queue`, docs/scale.md §5).
//!
//! Workers claim blocks of the current level and append the new states to
//! their own next-level blocks (`Local`). With one worker the next level
//! follows the current one when it is exhausted (`Local::advance`): exact
//! FIFO order. In the level-synchronous search (several workers) each
//! worker submits its blocks before the barrier, and the barrier leader
//! installs the next level (`Frontier::install`).
//!
//! Near the end of a parallel level (few states left to claim) a worker
//! stages the block it claims (`Staged`) instead of keeping it to itself:
//! the workers that find nothing more to claim then steal its states in
//! batches, so that a descheduled worker does not hold up the level barrier
//! with the block it claimed (docs/scale.md §5.2). A narrow level that one
//! worker expands alone stages nothing (`Local::share`).
//!
//! While the search may be resumed (`super::resume`), every worker also
//! keeps the states it is done with in its part of the archive
//! (docs/scale.md §6): compressed blocks move there whole once read,
//! other states are encoded there one by one (`Local::retire`).
//!
//! Under memory pressure the encoded segments of the queue and of the
//! archive go to disk (docs/scale.md §5.3): a worker offers those it
//! wrote every `TICK` states (`Local::spill`), the budget monitor those of
//! the current level far from the claims (`Frontier::spill_tail`).

use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use parking_lot::Mutex;

use crate::io::{IoError, Spill};
use crate::queue::codec::XorPrev;
use crate::queue::{Block, Config, Mem, Queue, Reader, StateCodec, Writer, BLOCK};

pub(super) use crate::queue::Task;

/// A worker's queued states, published for the live statistics.
#[repr(align(128))]
#[derive(Default)]
struct Held(AtomicU64);

/// A block claimed near the end of a level, which the other workers may
/// steal the states of (`Local::steal`); see `docs/scale.md` §5.2.
struct Staged<S> {
    reader: Reader<S>,
    /// The previous record of an encoded block, kept with it: whichever
    /// worker reads the next state decodes it from here.
    prev: XorPrev,
    /// The block is a compressed one, moved to the archive of the worker
    /// that claimed it, whole, once read: its states are not archived one by
    /// one (see `Local::retire`).
    moving: bool,
}

/// The shared part of the frontier.
pub(super) struct Frontier<'m, S> {
    queue: Queue<'m, S>,
    /// The archive's blocks (only its writers are used).
    archive: Queue<'m, S>,
    /// Per worker: the states left in its claimed block and its next-level
    /// states.
    held: Box<[Held]>,
    /// Per worker, with several workers: the block it claimed near the end
    /// of a level, which the others steal the states of.
    staged: Box<[Mutex<Option<Staged<S>>>]>,
    /// Per worker: the states left in the block it staged, updated under the
    /// slot's lock as they are read (whoever reads them), so that `queued`
    /// counts them without taking the lock.
    staged_left: Box<[AtomicU64]>,
}

/// A worker's part of the frontier.
pub(super) struct Local<'f, 'm, S> {
    fr: &'f Frontier<'m, S>,
    me: usize,
    /// The claimed block being expanded, while this worker keeps it (with
    /// one worker, or with several early in a level: near the end of a
    /// level the block is staged, see `Frontier::staged`).
    reader: Option<Reader<S>>,
    prev: XorPrev,
    /// A state done with, whose storage a decoded state may reuse.
    spare: Option<S>,
    /// States taken from a staged block, to expand next: the block's slot is
    /// locked once per batch (`STAGED_BATCH` states, `STAGED_BATCH_BYTES`
    /// bytes), not per state. (Their own memory is not charged to the
    /// queue's: a batch is bounded, and the block keeps the charge of its
    /// records.)
    batch: Vec<Task<S>>,
    /// The states of the next level.
    writer: Writer<S>,
    /// This worker's part of the archive, while archiving.
    archive: Option<Writer<S>>,
    /// The block of the states being expanded is compressed (and this worker
    /// archives): it moves to the archive whole, so its states are not
    /// archived one by one.
    moving: bool,
    /// The blocks this worker claims are staged for the others to steal
    /// from: a level expanded in parallel (`Local::share`). The blocks of a
    /// narrow level expanded by this worker alone stay private.
    sharing: bool,
    /// An error reading a spilled segment back (the search stops).
    io_error: Option<IoError>,
}

impl<'m, S> Frontier<'m, S> {
    /// The frontier of `n` workers, with states encoded by `codec` if given;
    /// the archive's memory is counted in `archive`. Encoded segments may
    /// go to `spill`.
    pub(super) fn new(n: usize, codec: Option<&'m dyn StateCodec<S>>, cfg: Config, archive: Arc<Mem>, spill: &Spill) -> Frontier<'m, S> {
        let words = codec.map_or(0, |c| c.words());
        let workers = n.max(1);
        Frontier {
            queue: Queue::new(codec, cfg, workers).with_spill(spill, "queue"),
            archive: Queue::archive(codec, words, cfg.seg_bytes, archive).with_spill(spill, "archive"),
            held: (0..workers).map(|_| Held::default()).collect(),
            staged: (0..workers).map(|_| Mutex::new(None)).collect(),
            staged_left: (0..workers).map(|_| AtomicU64::new(0)).collect(),
        }
    }

    /// The part of worker `me` (archiving the states it is done with if
    /// `archiving`).
    pub(super) fn local(&self, me: usize, archiving: bool) -> Local<'_, 'm, S> {
        let archive = archiving.then(|| self.archive.writer());
        Local {
            fr: self,
            me,
            reader: None,
            prev: self.queue.scratch(),
            spare: None,
            batch: Vec::new(),
            writer: self.queue.writer(),
            archive,
            moving: false,
            sharing: self.staged.len() > 1,
            io_error: None,
        }
    }

    /// The number of tasks queued (current level and next one).
    pub(super) fn queued(&self) -> u64 {
        // (The states of a staged block are counted where they are taken
        // from, by whoever takes them.)
        let staged: u64 = self.staged_left.iter().map(|n| n.load(Ordering::Relaxed)).sum();
        let held: u64 = self.held.iter().map(|h| h.0.load(Ordering::Relaxed)).sum();
        self.queue.unclaimed() + staged + held
    }

    /// Level-synchronous search, by the barrier leader: make the blocks
    /// submitted by the workers the current level.
    pub(super) fn install(&self) {
        self.queue.install();
    }

    /// The most memory the queue held (bytes), and whether states were encoded.
    pub(super) fn peak_bytes(&self) -> (usize, bool) {
        (self.queue.mem().peak(), self.queue.encoded())
    }

    /// The archive's memory account.
    pub(super) fn archive_mem(&self) -> &Arc<Mem> {
        self.archive.mem_arc()
    }

    /// The queue's memory account.
    pub(super) fn queue_mem(&self) -> &Arc<Mem> {
        self.queue.mem_arc()
    }

    /// The words of encoded states (0: states are objects).
    pub(super) fn words(&self) -> usize {
        self.archive.words()
    }

    /// Memory pressure (or its end): compress the queue's new blocks.
    pub(super) fn squeeze(&self, on: bool) {
        self.queue.squeeze(on);
    }

    /// Whether the queue's new blocks are compressed for memory pressure.
    pub(super) fn squeezed(&self) -> bool {
        self.queue.squeezed()
    }

    /// The queue's encoded segments go to disk from now on (or no more);
    /// whether they do (only if encoded, and the disk may be used).
    pub(super) fn spill_queue(&self, on: bool) -> bool {
        self.queue.spill_on(on)
    }

    /// Whether the queue's segments go to disk.
    pub(super) fn queue_spilling(&self) -> bool {
        self.queue.spilling()
    }

    /// Segments kept resident ahead of claims per list.
    pub(super) fn queue_window(&self) -> usize {
        self.queue.window()
    }

    /// While the queue spills: offer the segments of the current level far
    /// from the claims to the disk.
    pub(super) fn spill_tail(&self) {
        self.queue.spill_tail();
    }

    /// The archive's segments go to disk from now on; whether they do
    /// (only if its states are encoded, and the disk may be used).
    pub(super) fn spill_archive(&self) -> bool {
        self.archive.spill_on(true)
    }

    /// Whether the archive's segments go to disk.
    pub(super) fn archive_spilling(&self) -> bool {
        self.archive.spilling()
    }

    /// The segments written to disk: of the queue, of the archive.
    pub(super) fn spilled_segments(&self) -> (u64, u64) {
        (self.queue.spilled_segments(), self.archive.spilled_segments())
    }

    /// The lists of the current level (`for_each_queued_in`).
    pub(super) fn queued_lists(&self) -> usize {
        self.queue.list_count()
    }

    /// Call `f` with every block of list `l` of the current level not
    /// claimed yet, in claim order (at a level barrier, see
    /// `Queue::for_each_unclaimed_in`).
    pub(super) fn for_each_queued_in<E>(&self, l: usize, f: impl FnMut(&Block<S>) -> Result<(), E>) -> Result<(), E> {
        self.queue.for_each_unclaimed_in(l, f)
    }

    /// A scratch `XorPrev` sized for this frontier's encoded states.
    pub(super) fn scratch(&self) -> XorPrev {
        self.queue.scratch()
    }

    /// Visit every state held in the shared frontier queue (unclaimed current
    /// level + submitted next level) at a safepoint.
    pub(super) fn visit_queued(
        &self,
        cache: &mut crate::queue::SegCache,
        prev: &mut XorPrev,
        visit: &mut dyn FnMut(crate::queue::StateRef<'_, S>),
    ) -> Result<(), IoError> {
        self.queue.visit_states(cache, prev, visit)
    }

    /// Visit states held in per-worker staged blocks (`Frontier::staged`) at a
    /// safepoint. When `include_archive` is true and the owning worker is still
    /// archiving (`owner_archiving(i)`), a compressed staged block (`st.moving`)
    /// keeps its consumed records rooted until the owner moves the whole block
    /// to its archive; otherwise only the unread suffix is visited so consumed
    /// records can be reclaimed immediately.
    pub(super) fn visit_staged(
        &self,
        include_archive: bool,
        owner_archiving: impl Fn(usize) -> bool,
        cache: &mut crate::queue::SegCache,
        prev: &mut XorPrev,
        visit: &mut dyn FnMut(crate::queue::StateRef<'_, S>),
    ) -> Result<(), IoError> {
        for (i, slot) in self.staged.iter().enumerate() {
            let arch = include_archive && owner_archiving(i);
            if let Some(st) = &*slot.lock() {
                let keep_consumed = arch && st.moving;
                st.reader.visit_states(keep_consumed, cache, prev, visit)?;
            }
        }
        Ok(())
    }

    /// Clear `moving` on every staged block once the search drops its
    /// layout-miss archive at a safepoint, so neither `read_own` nor
    /// subsequent thieves treat staged compressed blocks as archived.
    pub(super) fn clear_staged_archiving(&self) {
        for slot in self.staged.iter() {
            if let Some(st) = &mut *slot.lock() {
                st.moving = false;
            }
        }
    }
}

/// The states left to claim below which a claimed block is staged for
/// stealing: the last two blocks of each worker of a level, where the states
/// a descheduled worker holds would otherwise hold up the level barrier.
/// (Guided self-scheduling takes about `1/(2 * workers)` of the states left,
/// but an XOR block is claimed whole.)
fn staging_below(workers: usize) -> u64 {
    2 * workers as u64 * BLOCK as u64
}

/// The states a worker takes from a staged block at a time, under one lock:
/// sharing a block costs a lock (and a move of the slot's cache line) per
/// batch, and a worker descheduled with a batch left costs at most this many
/// expansions at the barrier. Never more than half of what is left, so that
/// the rest stays stealable.
const STAGED_BATCH: usize = 32;

/// The bytes of decoded states a batch may hold: a batch is not charged to
/// the queue's memory (the block is, for its encoded records), so a wide
/// state is taken alone, decoded into the buffer the worker recycles after
/// each expansion, rather than 32 of them being held per worker.
const STAGED_BATCH_BYTES: usize = 64 << 10;

impl<S> Local<'_, '_, S> {
    #[inline]
    fn publish(&self) {
        // (A staged block's states are counted at its slot, see
        // `Frontier::queued`: publishing takes no lock.)
        let n = self.reader.as_ref().map_or(0, |r| r.left()) + self.batch.len() + self.writer.len();
        self.fr.held[self.me].0.store(n as u64, Ordering::Relaxed);
    }

    /// Stage the blocks this worker claims for the others to steal (`on`):
    /// a level expanded in parallel. A narrow level that this worker expands
    /// alone keeps its blocks private: its peers wait at the barrier, so
    /// staging them would only add locks (and the scan of their slots).
    pub(super) fn share(&mut self, on: bool) {
        debug_assert!(self.batch.is_empty(), "a batch left at the end of a level");
        debug_assert!(on || !self.sharing || self.fr.staged[self.me].lock().is_none(), "a staged block left");
        self.sharing = on && self.fr.staged.len() > 1;
    }

    /// Queue a task of the next level (or of the first one: an initial or
    /// resumed state, before `advance`).
    #[inline]
    pub(super) fn push_new(&mut self, task: Task<S>) {
        self.fr.queue.push(&mut self.writer, task);
        self.publish();
    }

    /// The next task of the current level: from the block this worker
    /// claimed (or stolen from another worker's, near the end of a level),
    /// else from a newly claimed one.
    #[inline]
    pub(super) fn pop(&mut self) -> Option<Task<S>> {
        let t = match self.batch.pop() {
            Some(t) => Some(t),
            None => match self.read_own() {
                Some(t) => Some(t),
                None => match self.claim() {
                    Some(t) => Some(t),
                    None => self.steal(),
                },
            },
        };
        self.publish();
        t
    }

    /// Take up to `STAGED_BATCH` states of the block in `slot` into the
    /// batch, under its lock: one state of them.
    fn take_batch(&mut self, slot: &mut parking_lot::MutexGuard<'_, Option<Staged<S>>>, me: usize) -> Option<Task<S>> {
        debug_assert!(self.batch.is_empty(), "a batch is read before another is taken");
        let st = slot.as_mut()?;
        let left = st.reader.left();
        // (A decoded state takes about its words; an object state is not
        // decoded here, and counts by state only.)
        let state_bytes = (8 * self.fr.queue.words()).max(1);
        let by_bytes = (STAGED_BATCH_BYTES / state_bytes).max(1);
        let k = left.min(STAGED_BATCH).min(left.div_ceil(2)).min(by_bytes);
        for _ in 0..k {
            match self.fr.queue.read(&mut st.reader, &mut st.prev, &mut self.spare) {
                Some(t) => self.batch.push(t),
                None => break,
            }
        }
        self.fr.staged_left[me].store(st.reader.left() as u64, Ordering::Relaxed);
        self.moving = st.moving;
        // (The batch is read from its end.)
        self.batch.reverse();
        self.batch.pop()
    }

    /// The next state of the block this worker claimed, if it has one left;
    /// the block is dropped once read (and moved to the archive whole if it
    /// is compressed).
    fn read_own(&mut self) -> Option<Task<S>> {
        let q = &self.fr.queue;
        if let Some(r) = self.reader.as_mut() {
            if let Some(t) = q.read(r, &mut self.prev, &mut self.spare) {
                return Some(t);
            }
        }
        if let Some(r) = self.reader.take() {
            // (Taken with the last state: an exhausted reader must not
            // outlive its block, or the `moving` of a block read later — a
            // stolen batch, say — would move it to the archive. Whether it
            // is whole is the reader's own business.)
            self.moving = false;
            if let (Some(a), true) = (&mut self.archive, r.compressed()) {
                self.fr.archive.append(a, r.into_block());
            }
            return None;
        }
        if !self.sharing {
            return None;
        }
        let mut slot = self.fr.staged[self.me].lock();
        let st = slot.as_mut()?;
        if st.reader.left() == 0 {
            let st = slot.take().expect("the block claimed last");
            drop(slot);
            self.moving = false;
            if let (Some(a), true) = (&mut self.archive, st.moving) {
                self.fr.archive.append(a, st.reader.into_block());
            }
            return None;
        }
        self.take_batch(&mut slot, self.me)
    }

    /// Claim a block of the current level: one state of it. Near the end of
    /// a level the block is staged where the other workers can steal its
    /// states, so that a descheduled worker does not hold up the level
    /// barrier with them.
    fn claim(&mut self) -> Option<Task<S>> {
        let q = &self.fr.queue;
        if self.sharing && q.unclaimed() <= staging_below(self.fr.staged.len()) {
            let mut slot = self.fr.staged[self.me].lock();
            debug_assert!(slot.is_none(), "the block claimed last is still staged");
            debug_assert!(self.reader.is_none(), "a kept block left before a claim");
            match q.claim(self.me, &mut self.prev) {
                Ok(Some(r)) => {
                    let moving = self.archive.is_some() && r.compressed();
                    self.fr.staged_left[self.me].store(r.left() as u64, Ordering::Relaxed);
                    *slot = Some(Staged { reader: r, prev: q.scratch(), moving });
                }
                Ok(None) => {}
                Err(e) => self.io_error = Some(e),
            }
            drop(slot);
            return self.read_own();
        }
        // (A unit test lets another worker claim the rest of the level here,
        // so that the private claim below finds nothing.)
        #[cfg(test)]
        if let Some(gate) = tests::CLAIM_GATE.take() {
            gate.wait();
            gate.wait();
        }
        match q.claim(self.me, &mut self.prev) {
            Ok(Some(r)) => {
                self.moving = self.archive.is_some() && r.compressed();
                self.reader = Some(r);
                self.read_own()
            }
            Ok(None) => None,
            Err(e) => {
                self.io_error = Some(e);
                None
            }
        }
    }

    /// A state of a block another worker staged near the end of the level,
    /// which this worker would otherwise wait for at the barrier.
    fn steal(&mut self) -> Option<Task<S>> {
        if !self.sharing {
            return None;
        }
        let n = self.fr.staged.len();
        for k in 1..n {
            let i = (self.me + k) % n;
            // (The states left are counted at the slot: an empty one costs a
            // load, not a lock.)
            if self.fr.staged_left[i].load(Ordering::Relaxed) == 0 {
                continue;
            }
            let mut slot = self.fr.staged[i].lock();
            let Some(st) = slot.as_mut() else { continue };
            // (Read: its worker moves it to the archive.)
            if st.reader.left() == 0 {
                continue;
            }
            if let Some(t) = self.take_batch(&mut slot, i) {
                return Some(t);
            }
        }
        None
    }

    /// Done with state `s` (expanded): its storage may be reused.
    #[inline]
    pub(super) fn recycle(&mut self, s: S) {
        if self.fr.queue.encoded() {
            self.spare = Some(s);
        }
    }

    /// Done with `task` (expanded, or left at the end): archive its state
    /// while archiving (unless its block moves to the archive whole).
    #[inline]
    pub(super) fn retire(&mut self, task: Task<S>) {
        match &mut self.archive {
            Some(a) if !self.moving => {
                if self.fr.archive.encoded() {
                    self.fr.archive.push_ref(a, &task);
                    self.recycle(task.state);
                } else {
                    self.fr.archive.push(a, task);
                }
            }
            _ => self.recycle(task.state),
        }
    }

    /// Whether this worker archives the states it is done with.
    pub(super) fn archiving(&self) -> bool {
        self.archive.is_some()
    }

    /// Stop archiving (dropping this worker's part of the archive).
    pub(super) fn stop_archiving(&mut self) {
        self.archive = None;
        self.moving = false;
        if let Some(st) = &mut *self.fr.staged[self.me].lock() {
            st.moving = false;
        }
    }

    /// Temporarily move this worker's frontier containers out for safepoint GC
    /// root enumeration (restored by `restore_gc_parts`).
    pub(super) fn take_gc_parts(&mut self) -> (Option<Reader<S>>, Vec<Task<S>>, Writer<S>, Option<Writer<S>>) {
        self.spare = None;
        let reader = self.reader.take();
        let batch = std::mem::take(&mut self.batch);
        let writer = std::mem::replace(&mut self.writer, self.fr.queue.writer());
        let archive = self.archive.take();
        (reader, batch, writer, archive)
    }

    /// Restore the frontier containers moved out by `take_gc_parts`.
    pub(super) fn restore_gc_parts(
        &mut self,
        reader: Option<Reader<S>>,
        batch: Vec<Task<S>>,
        writer: Writer<S>,
        archive: Option<Writer<S>>,
    ) {
        self.reader = reader;
        self.batch = batch;
        self.writer = writer;
        self.archive = archive;
        if self.archive.is_none() {
            self.moving = false;
        }
    }

    /// Visit every state held directly by this `Local` (reader, batch, writer,
    /// and optionally archive), used for single-threaded init-phase GC.
    pub(super) fn visit_local(
        &self,
        include_archive: bool,
        cache: &mut crate::queue::SegCache,
        prev: &mut XorPrev,
        visit: &mut dyn FnMut(crate::queue::StateRef<'_, S>),
    ) -> Result<(), IoError> {
        if let Some(r) = &self.reader {
            let keep_consumed = include_archive && self.archive.is_some() && r.compressed();
            r.visit_states(keep_consumed, cache, prev, visit)?;
        }
        for t in &self.batch {
            visit(crate::queue::StateRef::Obj(&t.state));
        }
        self.writer.visit_states(cache, prev, visit)?;
        if include_archive {
            if let Some(a) = &self.archive {
                a.visit_states(cache, prev, visit)?;
            }
        }
        Ok(())
    }

    /// Add `blocks` (of states done with) to this worker's part of the archive.
    pub(super) fn archive_blocks(&mut self, blocks: Vec<Block<S>>) {
        if let Some(a) = &mut self.archive {
            for b in blocks {
                self.fr.archive.append(a, b);
            }
        }
    }

    /// Add the encoded state `(log, fp, words)` of depth `depth` (done
    /// with) to this worker's part of the archive (recovering from a
    /// checkpoint).
    pub(super) fn archive_words(&mut self, log: u64, fp: u64, depth: u32, words: &[u64]) {
        if let Some(a) = &mut self.archive {
            self.fr.archive.push_words(a, log, fp, depth, words);
        }
    }

    /// The blocks of this worker's part of the archive so far (None if not
    /// archiving), for a checkpoint.
    pub(super) fn archived(&mut self) -> Option<&[Block<S>]> {
        let a = self.archive.as_mut()?;
        Some(self.fr.archive.blocks(a))
    }

    /// This worker's part of the archive (None if not archiving); its
    /// segments on disk while the archive spills.
    pub(super) fn take_archive(&mut self) -> Option<Vec<Block<S>>> {
        let mut a = self.archive.take()?;
        let blocks = self.fr.archive.take(&mut a);
        if self.fr.archive.spilling() {
            self.fr.archive.spill_blocks(&blocks);
        }
        Some(blocks)
    }

    /// Offer the segments this worker wrote (of the next level, of its part
    /// of the archive) to the disk, while they spill.
    pub(super) fn spill(&mut self) {
        self.fr.queue.spill_writer(&mut self.writer);
        if let Some(a) = &mut self.archive {
            self.fr.archive.spill_writer(a);
        }
    }

    /// The error reading a spilled segment back, if one occurred.
    pub(super) fn take_io_error(&mut self) -> Option<IoError> {
        self.io_error.take()
    }

    /// The number of tasks of the next level.
    #[inline]
    pub(super) fn next_len(&self) -> usize {
        self.writer.len()
    }

    /// Number of sealed blocks finished by this worker's writer.
    #[inline]
    pub(super) fn sealed_blocks(&self) -> usize {
        self.writer.sealed_blocks()
    }

    /// Submit the tasks of the next level (level-synchronous search, before
    /// the barrier; see `Frontier::install`).
    pub(super) fn submit(&mut self) {
        self.fr.queue.submit(self.me, &mut self.writer);
    }

    /// Queue the encoded state `(log, fp, words)` of depth `depth` (of the
    /// first level: recovering from a checkpoint), in a compressed block.
    pub(super) fn push_words(&mut self, log: u64, fp: u64, depth: u32, words: &[u64]) {
        self.fr.queue.push_words(&mut self.writer, log, fp, depth, words);
        self.publish();
    }

    /// Make this worker's next-level tasks the current level (with one
    /// worker, a solo worker, or the initial states). The current level
    /// must be exhausted, and no other worker claiming.
    pub(super) fn advance(&mut self) {
        self.submit();
        self.fr.queue.install();
        self.publish();
    }

    /// At the end of the search: remove the tasks left that this worker
    /// holds or can claim (its claimed block, staged or not, unclaimed
    /// blocks of the current level, its next-level tasks). Returns their
    /// number. While archiving, those of the current level are archived (in
    /// queue order).
    pub(super) fn drain(&mut self) -> usize {
        let q = &self.fr.queue;
        let mut n = 0;
        // (The states taken from a staged block but not expanded: their
        // block archives them if it moves whole, else they are archived one
        // by one below.)
        let batch = std::mem::take(&mut self.batch);
        let moved = self.moving;
        // (A staged block is this worker's too; the others may have taken
        // some of its states.)
        let mut held = self.reader.take().or_else(|| {
            let mut slot = self.fr.staged[self.me].lock();
            self.fr.staged_left[self.me].store(0, Ordering::Relaxed);
            slot.take().map(|st| st.reader)
        });
        // (Compressed blocks move whole below; other states are archived
        // one by one.)
        self.moving = false;
        let mut tasks = Vec::new();
        // (Spilled segments are read back only to archive states one by one.)
        while let Some(mut r) = held.take().or_else(|| q.claim_unloaded(self.me, &mut self.prev)) {
            if let (Some(a), true) = (&mut self.archive, r.compressed()) {
                n += r.left();
                self.fr.archive.append(a, r.into_block());
                continue;
            }
            let left = r.left();
            match q.drain_reader(&mut r, &mut self.prev, self.archive.is_some(), &mut tasks) {
                Ok(k) => n += k,
                Err(e) => {
                    // (The search fails: the archive is not used.)
                    n += left;
                    self.io_error.get_or_insert(e);
                }
            }
            for t in tasks.drain(..) {
                self.retire(t);
            }
        }
        for t in batch {
            n += 1;
            if !moved {
                self.retire(t);
            }
        }
        // (Not read: only counted.)
        n += q.drain_writer(&mut self.writer, &mut self.prev, false, &mut tasks).unwrap_or(0);
        self.publish();
        n
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::queue::BlockKinds;

    /// States of 3 words `(i, i / 2, 7)`.
    struct Words;

    impl StateCodec<Vec<u64>> for Words {
        fn words(&self) -> usize {
            3
        }
        fn encode(&self, s: &Vec<u64>, out: &mut [u64]) -> u64 {
            out.copy_from_slice(s);
            s[0].wrapping_mul(0x9E37_79B9_7F4A_7C15)
        }
        fn decode(&self, w: &[u64], _depth: u32, _fp: u64) -> Vec<u64> {
            w.to_vec()
        }
    }

    /// The logs of the states archived by `l`, in order.
    fn archived(fr: &Frontier<'_, Vec<u64>>, l: &mut Local<'_, '_, Vec<u64>>) -> Vec<u64> {
        let mut logs = Vec::new();
        let mut prev = fr.archive.scratch();
        let mut cache = crate::queue::SegCache::default();
        for b in l.take_archive().unwrap() {
            b.records(&mut cache, &mut prev, |log, _, w| {
                assert_eq!(w, &[log, log / 2, 7]);
                logs.push(log);
                Ok::<_, ()>(())
            })
            .unwrap()
            .unwrap();
        }
        logs
    }

    /// The archive gets every state done with exactly once, in order:
    /// compressed blocks whole (also when only partly expanded), other
    /// states one by one, whatever the mix of blocks of a level.
    #[test]
    fn archive_gets_every_state_once() {
        let cfg = Config { kinds: BlockKinds::Auto, seg_bytes: 4096, compress_above: 1 << 30 };
        // Kinds of the blocks of a level (true: compressed), and the
        // states expanded before the search stops (the others are drained).
        for (kinds, expand) in [
            (vec![true, false], 3),
            (vec![true, false, true], 300),
            (vec![false, true, false], 600),
            (vec![true, true], 256),
            (vec![false], 0),
        ] {
            let fr = Frontier::new(1, Some(&Words as &dyn StateCodec<Vec<u64>>), cfg, Mem::new(4096, false), &Spill::default());
            let mut l = fr.local(0, true);
            let mut i = 0u64;
            for &compressed in &kinds {
                fr.squeeze(compressed);
                for _ in 0..crate::queue::BLOCK {
                    l.push_new(Task { state: vec![i, i / 2, 7], log: i, depth: 1 });
                    i += 1;
                }
            }
            l.advance();
            for _ in 0..expand {
                let t = l.pop().unwrap();
                l.retire(t);
            }
            assert_eq!(l.drain(), i as usize - expand);
            assert_eq!(archived(&fr, &mut l), (0..i).collect::<Vec<_>>(), "{kinds:?} {expand}");
        }
    }

    /// One level of `n` states of depth 1, written by worker 0, current.
    fn level(a: &mut Local<'_, '_, Vec<u64>>, n: u64) {
        for i in 0..n {
            a.push_new(Task { state: vec![i, i / 2, 7], log: i, depth: 1 });
        }
        a.advance();
    }

    /// Near the end of a level the block a worker claims is staged: a worker
    /// that finds nothing more to claim expands the states the first one has
    /// not, one at a time, so that the level ends without it (a descheduled
    /// worker would otherwise hold up the barrier with the rest of its
    /// block).
    #[test]
    fn idle_workers_steal_a_stalled_workers_block() {
        for compressed in [false, true] {
            let cfg = Config { kinds: BlockKinds::Auto, seg_bytes: 4096, compress_above: 1 << 30 };
            let fr = Frontier::new(2, Some(&Words as &dyn StateCodec<Vec<u64>>), cfg, Mem::new(4096, false), &Spill::default());
            fr.squeeze(compressed);
            let mut a = fr.local(0, false);
            let mut b = fr.local(1, false);
            level(&mut a, BLOCK as u64);
            // Worker 0 claims the block (whole if compressed, else its last
            // part), expands one state, and is descheduled.
            let first = a.pop().unwrap().log;
            let staged = fr.staged[0].lock().as_ref().map(|st| st.reader.left());
            assert!(staged.is_some_and(|left| left > 0), "a staged block: {compressed}");
            assert_eq!(fr.queued(), BLOCK as u64 - 1, "the staged states are queued: {compressed}");
            // Worker 1 claims the rest of the level, then steals the states
            // worker 0 has not expanded.
            let mut seen = vec![0u8; BLOCK];
            seen[first as usize] += 1;
            while let Some(t) = b.pop() {
                seen[t.log as usize] += 1;
            }
            // Worker 1 took the states of worker 0's block (the block is
            // read, and dropped by its own worker): the queue counts only the
            // batch worker 0 had taken, not the states a thief consumed.
            assert_eq!(fr.staged[0].lock().as_ref().map(|st| st.reader.left()), Some(0), "compressed={compressed}");
            assert_eq!(fr.queued(), (STAGED_BATCH - 1) as u64, "compressed={compressed}");
            // Worker 0 expands the batch it held, and has nothing left.
            while let Some(t) = a.pop() {
                seen[t.log as usize] += 1;
            }
            assert!(seen.iter().all(|&c| c == 1), "compressed={compressed}");
            assert_eq!(fr.queued(), 0, "compressed={compressed}");
            assert!(fr.staged[0].lock().is_none());
            assert!(a.take_io_error().is_none() && b.take_io_error().is_none());
            fr.queue_mem().clear_pool();
            assert_eq!(fr.queue_mem().bytes(), 0);
        }
    }

    /// A worker that keeps a block early in a level goes on reading it after
    /// the level's end has been reached (the blocks claimed after it are
    /// staged): none of its states is lost. A block of a level expanded alone
    /// is never staged.
    #[test]
    fn a_kept_block_is_read_after_the_end_of_the_level() {
        let cfg = Config { kinds: BlockKinds::Auto, seg_bytes: 4096, compress_above: 1 << 30 };
        let fr = Frontier::new(2, Some(&Words as &dyn StateCodec<Vec<u64>>), cfg, Mem::new(4096, false), &Spill::default());
        let mut a = fr.local(0, false);
        let mut b = fr.local(1, false);
        // (Wide enough that the first claim keeps its block.)
        let n = staging_below(2) + BLOCK as u64;
        level(&mut a, n);
        let mut seen = vec![0u8; n as usize];
        // Worker 0 expands the level alone (as a narrow level is): its blocks
        // are not staged for stealing.
        a.share(false);
        let t = a.pop().unwrap();
        seen[t.log as usize] += 1;
        assert!(fr.staged[0].lock().is_none(), "a block of a level expanded alone is kept");
        while let Some(t) = b.pop() {
            seen[t.log as usize] += 1;
        }
        // Worker 0 goes on with the block it kept.
        while let Some(t) = a.pop() {
            seen[t.log as usize] += 1;
        }
        assert!(seen.iter().all(|&c| c == 1), "{seen:?}");
        assert_eq!(fr.queued(), 0);
    }

    /// States of `n` words, the first their log.
    struct Wide(usize);

    impl StateCodec<Vec<u64>> for Wide {
        fn words(&self) -> usize {
            self.0
        }
        fn encode(&self, s: &Vec<u64>, out: &mut [u64]) -> u64 {
            out.copy_from_slice(s);
            s[0].wrapping_mul(0x9E37_79B9_7F4A_7C15)
        }
        fn decode(&self, w: &[u64], _depth: u32, _fp: u64) -> Vec<u64> {
            w.to_vec()
        }
    }

    thread_local! {
        /// A gate a unit test sets to interleave another worker's claims
        /// with the private claim of the worker that takes it.
        pub(super) static CLAIM_GATE: std::cell::RefCell<Option<Arc<std::sync::Barrier>>> =
            const { std::cell::RefCell::new(None) };
    }

    /// An exhausted kept reader is taken when it is read dry, so it cannot
    /// outlive its block: with the other worker left holding a staged
    /// compressed block, this worker steals a batch (which sets `moving`)
    /// and the stale reader would be moved to the encoded archive — an empty
    /// block that makes a checkpoint skip the worker's archive whole.
    #[test]
    fn interleaved_private_claim_leaves_an_encoded_archive() {
        // (Auto: the first block is of objects, the rest are compressed.)
        let cfg = Config { kinds: BlockKinds::Auto, seg_bytes: 1 << 20, compress_above: 1 << 30 };
        let fr = Frontier::new(2, Some(&Words as &dyn StateCodec<Vec<u64>>), cfg, Mem::new(1 << 20, false), &Spill::default());
        let mut a = fr.local(0, true);
        let mut b = fr.local(1, true);
        for i in 0..6 * BLOCK as u64 {
            fr.squeeze(i >= BLOCK as u64);
            a.push_new(Task { state: vec![i, i / 2, 7], log: i, depth: 1 });
        }
        a.advance();
        for _ in 0..BLOCK {
            let t = a.pop().unwrap();
            a.retire(t);
        }
        assert_eq!(fr.queue.unclaimed(), 5 * BLOCK as u64);
        // (Worker 0 selects the private claim path; worker 1 claims the rest
        // of the level meanwhile, leaving its last compressed block staged.)
        let gate = Arc::new(std::sync::Barrier::new(2));
        CLAIM_GATE.set(Some(gate.clone()));
        std::thread::scope(|scope| {
            scope.spawn(|| {
                gate.wait();
                while fr.queue.unclaimed() > 0 {
                    let t = b.pop().unwrap();
                    b.retire(t);
                }
                assert!(fr.staged_left[1].load(Ordering::Relaxed) > 0, "a staged block is left");
                gate.wait();
            });
            while let Some(t) = a.pop() {
                a.retire(t);
            }
        });
        while let Some(t) = b.pop() {
            b.retire(t);
        }
        let blocks = a.archived().unwrap();
        assert!(blocks.iter().all(|b| b.encoded()), "an exhausted kept block reached the archive");
    }

    /// A batch is bounded by its decoded bytes as well as by its states: a
    /// wide state is taken alone (its batch is empty), so the workers of a
    /// memory-tight search do not each hold 32 decoded wide states.
    #[test]
    fn a_batch_is_bounded_by_decoded_bytes() {
        let words = STAGED_BATCH_BYTES / 8;
        let codec = Wide(words);
        let cfg = Config { kinds: BlockKinds::Xor, seg_bytes: 1 << 20, compress_above: 0 };
        let fr = Frontier::new(2, Some(&codec as &dyn StateCodec<Vec<u64>>), cfg, Mem::new(1 << 20, false), &Spill::default());
        let mut a = fr.local(0, false);
        let mut b = fr.local(1, false);
        for i in 0..BLOCK as u64 {
            let mut state = vec![i; words];
            state[1] = i / 2;
            a.push_new(Task { state, log: i, depth: 1 });
        }
        a.advance();
        // (The wide XOR block is claimed whole and staged.)
        assert!(a.pop().is_some());
        assert!(fr.staged[0].lock().as_ref().is_some_and(|st| st.reader.left() > 0), "a staged block");
        assert_eq!(fr.held[0].0.load(Ordering::Relaxed), 0, "one state of {words} words per batch: no batch is held");
        assert_eq!(fr.queued(), BLOCK as u64 - 1, "every state not yet expanded is still queued");
        // (The other worker can steal the rest: every state is expanded once.)
        let mut n = 1;
        while let Some(t) = b.pop() {
            assert_eq!(t.state.len(), words);
            n += 1;
        }
        while let Some(t) = a.pop() {
            assert_eq!(t.state.len(), words);
            n += 1;
        }
        assert_eq!(n, BLOCK);
        assert_eq!(fr.queued(), 0);
    }

    /// A narrow level expanded by one worker (the others wait at the
    /// barrier) keeps its blocks private: nothing is staged, nothing is
    /// stolen, and every state is still expanded exactly once.
    #[test]
    fn a_level_expanded_alone_stages_nothing() {
        for compressed in [false, true] {
            let cfg = Config { kinds: BlockKinds::Auto, seg_bytes: 4096, compress_above: 1 << 30 };
            let fr = Frontier::new(2, Some(&Words as &dyn StateCodec<Vec<u64>>), cfg, Mem::new(4096, false), &Spill::default());
            fr.squeeze(compressed);
            let mut a = fr.local(0, false);
            let mut b = fr.local(1, false);
            level(&mut a, BLOCK as u64);
            a.share(false);
            let mut seen = vec![0u8; BLOCK];
            let mut n = 0;
            while let Some(t) = a.pop() {
                seen[t.log as usize] += 1;
                n += 1;
                assert!(fr.staged[0].lock().is_none(), "staged in a level expanded alone: {compressed}");
            }
            assert_eq!(n, BLOCK, "compressed={compressed}");
            assert!(seen.iter().all(|&c| c == 1), "compressed={compressed}");
            assert!(b.pop().is_none());
            assert_eq!(fr.queued(), 0, "compressed={compressed}");
        }
    }

    /// Stealing loses and repeats no archived state: a compressed block moves
    /// to the archive of the worker that claimed it whole (also when the
    /// others stole its states), and the states of a block of objects are
    /// archived one by one, by whoever expands them.
    #[test]
    fn stealing_keeps_the_archive_exact() {
        for compressed in [false, true] {
            let cfg = Config { kinds: BlockKinds::Auto, seg_bytes: 4096, compress_above: 1 << 30 };
            let fr = Frontier::new(2, Some(&Words as &dyn StateCodec<Vec<u64>>), cfg, Mem::new(4096, false), &Spill::default());
            fr.squeeze(compressed);
            let mut a = fr.local(0, true);
            let mut b = fr.local(1, true);
            let n = 2 * BLOCK as u64;
            level(&mut a, n);
            // Worker 0 expands a few states, then stalls; worker 1 ends the
            // level (and steals what worker 0 has left).
            for _ in 0..3 {
                let t = a.pop().unwrap();
                a.retire(t);
            }
            while let Some(t) = b.pop() {
                b.retire(t);
            }
            // (The batch worker 0 was taking when the level ended: it
            // expanded three of its `STAGED_BATCH` states.)
            assert_eq!(a.drain(), STAGED_BATCH - 3, "compressed={compressed}");
            assert_eq!(b.drain(), 0, "compressed={compressed}");
            let mut logs = archived(&fr, &mut a);
            logs.extend(archived(&fr, &mut b));
            logs.sort_unstable();
            assert_eq!(logs, (0..n).collect::<Vec<_>>(), "compressed={compressed}");
        }
    }

    /// Safepoint GC root scanning covers staged blocks and stolen per-worker
    /// batches (both object and compressed blocks), keeping consumed records
    /// rooted only while a compressed staged block is still destined for a
    /// retained archive.
    #[test]
    fn staged_and_stolen_batches_are_visited_for_gc() {
        for compressed in [false, true] {
            let cfg = Config { kinds: BlockKinds::Auto, seg_bytes: 4096, compress_above: 1 << 30 };
            let fr = Frontier::new(2, Some(&Words as &dyn StateCodec<Vec<u64>>), cfg, Mem::new(4096, false), &Spill::default());
            fr.squeeze(compressed);
            let mut a = fr.local(0, true);
            let mut b = fr.local(1, true);
            let n = 64u64;
            level(&mut a, n);
            // Worker 0 claims and stages the block, expands 2 states, and holds
            // the rest of its batch. Worker 1 steals a batch and expands 1 state.
            let t0 = a.pop().unwrap();
            a.retire(t0);
            let t1 = a.pop().unwrap();
            a.retire(t1);
            let s0 = b.pop().unwrap();
            b.retire(s0);

            let (ra, ba, wa, aa) = a.take_gc_parts();
            let (rb, bb, wb, ab) = b.take_gc_parts();
            assert!(!ba.is_empty(), "worker 0 batch should be non-empty: compressed={compressed}");
            assert!(!bb.is_empty(), "worker 1 batch should be non-empty: compressed={compressed}");

            let scan = |include_archive: bool, owner_archiving: bool| {
                let mut cache = crate::queue::SegCache::default();
                let mut prev = fr.scratch();
                let mut seen = Vec::new();
                let mut visit = |sr: crate::queue::StateRef<'_, Vec<u64>>| match sr {
                    crate::queue::StateRef::Obj(st) => seen.push(st[0]),
                    crate::queue::StateRef::Words(w) => seen.push(w[0]),
                };
                fr.visit_queued(&mut cache, &mut prev, &mut visit).unwrap();
                fr.visit_staged(include_archive, |i| i == 0 && owner_archiving, &mut cache, &mut prev, &mut visit).unwrap();
                for t in ba.iter().chain(bb.iter()) {
                    visit(crate::queue::StateRef::Obj(&t.state));
                }
                if include_archive {
                    if let Some(arch) = &aa {
                        arch.visit_states(&mut cache, &mut prev, &mut visit).unwrap();
                    }
                    if let Some(arch) = &ab {
                        arch.visit_states(&mut cache, &mut prev, &mut visit).unwrap();
                    }
                }
                seen.sort_unstable();
                seen.dedup();
                seen
            };

            // With archive retained, all 64 states remain reachable.
            assert_eq!(scan(true, true), (0..n).collect::<Vec<_>>(), "retained compressed={compressed}");

            // Once the archive is dropped, only the 61 unexpanded states stay
            // rooted (the 3 retired states are released immediately).
            let without_archive = scan(false, true);
            assert_eq!(without_archive.len(), (n - 3) as usize, "dropped compressed={compressed}");

            // After `clear_staged_archiving`, a compressed staged block drops
            // its consumed prefix even if `include_archive` & `owner_archiving`
            // are true (whereas uncompressed blocks archived retired states in
            // `aa`/`ab` directly).
            fr.clear_staged_archiving();
            let after_clear = scan(true, true);
            let want_after_clear = if compressed { n - 3 } else { n };
            assert_eq!(after_clear.len(), want_after_clear as usize, "cleared compressed={compressed}");

            a.restore_gc_parts(ra, ba, wa, aa);
            b.restore_gc_parts(rb, bb, wb, ab);
            let mut rest = 3u64;
            while a.pop().is_some() {
                rest += 1;
            }
            while b.pop().is_some() {
                rest += 1;
            }
            assert_eq!(rest, n, "restored batches must preserve every state: compressed={compressed}");
        }
    }
}
