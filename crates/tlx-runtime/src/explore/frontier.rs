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

use crate::io::{IoError, Spill};
use crate::queue::codec::XorPrev;
use crate::queue::{Block, Config, Mem, Queue, Reader, StateCodec, Writer};

pub(super) use crate::queue::Task;

/// A worker's queued states, published for the live statistics.
#[repr(align(128))]
#[derive(Default)]
struct Held(AtomicU64);

/// The shared part of the frontier.
pub(super) struct Frontier<'m, S> {
    queue: Queue<'m, S>,
    /// The archive's blocks (only its writers are used).
    archive: Queue<'m, S>,
    /// Per worker: the states left in its claimed block and its next-level
    /// states.
    held: Box<[Held]>,
}

/// A worker's part of the frontier.
pub(super) struct Local<'f, 'm, S> {
    fr: &'f Frontier<'m, S>,
    me: usize,
    /// The claimed block being expanded.
    reader: Option<Reader<S>>,
    prev: XorPrev,
    /// A state done with, whose storage a decoded state may reuse.
    spare: Option<S>,
    /// The states of the next level.
    writer: Writer<S>,
    /// This worker's part of the archive, while archiving.
    archive: Option<Writer<S>>,
    /// The claimed block is compressed: moved to the archive once read
    /// (its states are not archived one by one).
    moving: bool,
    /// An error reading a spilled segment back (the search stops).
    io_error: Option<IoError>,
}

impl<'m, S> Frontier<'m, S> {
    /// The frontier of `n` workers, with states encoded by `codec` if given;
    /// the archive's memory is counted in `archive`. Encoded segments may
    /// go to `spill`.
    pub(super) fn new(n: usize, codec: Option<&'m dyn StateCodec<S>>, cfg: Config, archive: Arc<Mem>, spill: &Spill) -> Frontier<'m, S> {
        let words = codec.map_or(0, |c| c.words());
        Frontier {
            queue: Queue::new(codec, cfg, n).with_spill(spill, "queue"),
            archive: Queue::archive(codec, words, cfg.seg_bytes, archive).with_spill(spill, "archive"),
            held: (0..n).map(|_| Held::default()).collect(),
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
            writer: self.queue.writer(),
            archive,
            moving: false,
            io_error: None,
        }
    }

    /// The number of tasks queued (current level and next one).
    pub(super) fn queued(&self) -> u64 {
        self.queue.unclaimed() + self.held.iter().map(|h| h.0.load(Ordering::Relaxed)).sum::<u64>()
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
}

impl<S> Local<'_, '_, S> {
    #[inline]
    fn publish(&self) {
        let n = self.reader.as_ref().map_or(0, |r| r.left()) + self.writer.len();
        self.fr.held[self.me].0.store(n as u64, Ordering::Relaxed);
    }

    /// Queue a task of the next level (or of the first one: an initial or
    /// resumed state, before `advance`).
    #[inline]
    pub(super) fn push_new(&mut self, task: Task<S>) {
        self.fr.queue.push(&mut self.writer, task);
        self.publish();
    }

    /// The next task of the current level: from the claimed block, else
    /// from a newly claimed one.
    #[inline]
    pub(super) fn pop(&mut self) -> Option<Task<S>> {
        let q = &self.fr.queue;
        loop {
            if let Some(r) = &mut self.reader {
                if let Some(t) = q.read(r, &mut self.prev, &mut self.spare) {
                    self.publish();
                    return Some(t);
                }
            }
            if self.moving {
                self.move_read();
            }
            self.reader = match q.claim(self.me, &mut self.prev) {
                Ok(r) => r,
                Err(e) => {
                    self.io_error = Some(e);
                    None
                }
            };
            match &self.reader {
                Some(r) => self.moving = self.archive.is_some() && r.compressed(),
                None => return None,
            }
        }
    }

    /// Move the compressed block read (all of it) to the archive.
    #[cold]
    fn move_read(&mut self) {
        self.moving = false;
        if let (Some(r), Some(a)) = (self.reader.take(), &mut self.archive) {
            self.fr.archive.append(a, r.into_block());
        }
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
    /// holds or can claim (its claimed block, unclaimed blocks of the
    /// current level, its next-level tasks). Returns their number. While
    /// archiving, those of the current level are archived (in queue order).
    pub(super) fn drain(&mut self) -> usize {
        let q = &self.fr.queue;
        let mut n = 0;
        let mut held = self.reader.take();
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
}
