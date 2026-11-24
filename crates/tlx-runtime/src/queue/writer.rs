//! Writing the next level, one `Writer` per worker (docs/scale.md §5.1).
//!
//! A writer appends the states a worker finds: blocks of objects while the
//! queue is small, encoded blocks in segments beyond `Config::compress_above`
//! (or under memory pressure), as `Config::kinds` says. The segments are
//! handed to the disk by the queue once they are closed (`Queue::spill_writer`).

use std::sync::atomic::Ordering;

use parking_lot::Mutex;

use super::block::{Block, Charge, Kind, Segment, Task};
use super::codec::{self, XorPrev};
use super::seg::Seg;
use super::{BlockKinds, Queue, StateCodec, BLOCK};

/// An encoded block being written: from `start` in the open segment.
struct Open {
    start: usize,
    n: u32,
    kind: Kind,
    depth: u32,
}

/// The blocks a worker writes (the new states of the next level), in
/// order: blocks of objects and encoded blocks (with a codec: see
/// `BlockKinds`).
pub(crate) struct Writer<S> {
    /// Finished blocks.
    pub(super) blocks: Vec<Block<S>>,
    /// The states written (in all blocks).
    len: usize,
    /// The open block of objects.
    tasks: Vec<Task<S>>,
    /// The open segment, its finished blocks and its open block.
    seg: Vec<u8>,
    seg_blocks: Vec<Open>,
    open: Option<Open>,
    /// A segment was filled: start the next ones at full size.
    filled: bool,
    /// `BlockKinds::Auto`: new blocks are compressed (the queue was over
    /// `Config::compress_above`, and has not fallen under half of it since).
    compress: bool,
    /// The previous record of the open XOR block; scratch words.
    prev: XorPrev,
    cur: Vec<u64>,
    /// The blocks before this one were spilled, or offered to be, or kept
    /// (`Queue::spill_writer`); the segments kept in memory.
    pub(super) spilled: usize,
    pub(super) kept: usize,
}

impl<S> Writer<S> {
    pub(super) fn new(words: usize) -> Writer<S> {
        Writer {
            blocks: Vec::new(),
            len: 0,
            tasks: Vec::new(),
            seg: Vec::new(),
            seg_blocks: Vec::new(),
            open: None,
            filled: false,
            compress: false,
            prev: XorPrev::new(words),
            cur: vec![0; words],
            spilled: 0,
            kept: 0,
        }
    }

    /// The states written.
    #[inline]
    pub(crate) fn len(&self) -> usize {
        self.len
    }

    /// Number of sealed blocks (encoded or object) finished by this writer.
    #[inline]
    pub(crate) fn sealed_blocks(&self) -> usize {
        self.blocks.len()
    }

    /// Append `t`.
    #[inline]
    pub(super) fn push(&mut self, q: &Queue<'_, S>, t: Task<S>) {
        self.len += 1;
        match q.codec {
            Some(codec) if self.encode_next(q, t.depth) => self.push_encoded(q, codec, &t),
            _ => self.push_object(q, t),
        }
    }

    /// Append the state of `t` encoded (with a codec: `push` without
    /// taking the state).
    #[inline]
    pub(super) fn push_ref(&mut self, q: &Queue<'_, S>, t: &Task<S>) {
        self.len += 1;
        let codec = q.codec.expect("encoding a state without a codec");
        self.push_encoded(q, codec, t);
    }

    /// Append the record `(log, fp, words)` in an XOR-varint block (a state
    /// already encoded, see `ResumePoint::transcode`).
    pub(super) fn push_words(&mut self, q: &Queue<'_, S>, log: u64, fp: u64, depth: u32, words: &[u64]) {
        self.len += 1;
        let kind = self.begin_record(q, Kind::Xor, depth);
        debug_assert_eq!(kind, Kind::Xor);
        codec::put_xor(&mut self.seg, &mut self.prev, log, fp, words);
    }

    /// Append the finished block `b` (after the states written so far),
    /// counting its memory in this queue's from now on (all of its segment's,
    /// for an encoded block).
    pub(super) fn append(&mut self, q: &Queue<'_, S>, mut b: Block<S>) {
        self.close_objects(q);
        self.close_block();
        self.freeze(q);
        match &mut b {
            Block::Objects { _charge, .. } => _charge.move_to(&q.mem),
            Block::Encoded { seg, .. } => seg.move_to(&q.mem),
        }
        self.len += b.len();
        self.blocks.push(b);
    }

    /// With a codec: whether to encode the next state (of depth `depth`):
    /// as the open block if it has room, else as `Config::kinds` says.
    #[inline]
    fn encode_next(&mut self, q: &Queue<'_, S>, depth: u32) -> bool {
        if let Some(o) = &self.open {
            if (o.n as usize) < BLOCK && o.depth == depth {
                return true;
            }
        } else if let Some(l) = self.tasks.last() {
            if self.tasks.len() < BLOCK && l.depth == depth {
                return false;
            }
        }
        match q.cfg.kinds {
            BlockKinds::Raw | BlockKinds::Xor => true,
            BlockKinds::Objects => false,
            BlockKinds::Auto => {
                let bytes = q.mem.bytes();
                if bytes > q.cfg.compress_above || q.squeeze.load(Ordering::Relaxed) {
                    self.compress = true;
                } else if bytes < q.cfg.compress_above / 2 {
                    self.compress = false;
                }
                self.compress
            }
        }
    }

    fn push_object(&mut self, q: &Queue<'_, S>, t: Task<S>) {
        if self.open.is_some() || !self.seg_blocks.is_empty() {
            // (The encoded blocks come first.)
            self.close_block();
            self.freeze(q);
        }
        if self.tasks.len() == BLOCK || self.tasks.last().is_some_and(|l| l.depth != t.depth) {
            self.close_objects(q);
        }
        if self.tasks.capacity() == 0 {
            self.tasks.reserve_exact(BLOCK);
        }
        self.tasks.push(t);
    }

    pub(super) fn close_objects(&mut self, q: &Queue<'_, S>) {
        if !self.tasks.is_empty() {
            let tasks = std::mem::take(&mut self.tasks);
            // (With a codec, the states' heap data are their words.)
            let heap = q.codec.map_or(0, |c| (8 * c.words()).div_ceil(16) * 16);
            let charge = Charge::new(tasks.capacity() * (std::mem::size_of::<Task<S>>() + heap), &q.mem);
            self.blocks.push(Block::Objects { tasks, _charge: charge });
        }
    }

    fn push_encoded(&mut self, q: &Queue<'_, S>, codec: &dyn StateCodec<S>, t: &Task<S>) {
        let kind = self.begin_record(q, if q.cfg.kinds == BlockKinds::Raw { Kind::Raw } else { Kind::Xor }, t.depth);
        // (A raw record is encoded through `prev.words`, unused by raw
        // blocks; an XOR one through `cur`.)
        match kind {
            Kind::Raw => {
                let fp = codec.encode(&t.state, &mut self.prev.words);
                codec::put_raw(&mut self.seg, t.log, fp, &self.prev.words);
            }
            Kind::Xor => {
                let at = self.seg.len();
                let fp = codec.encode(&t.state, &mut self.cur);
                codec::put_xor(&mut self.seg, &mut self.prev, t.log, fp, &self.cur);
                debug_assert!(self.seg.len() - at <= codec::xor_max_size(self.cur.len()));
            }
        }
    }

    /// Make room for a record of depth `depth` in the open encoded block
    /// (opening one of kind `new` if needed, and a segment): the kind of
    /// the open block.
    fn begin_record(&mut self, q: &Queue<'_, S>, new: Kind, depth: u32) -> Kind {
        // (The objects come first.)
        self.close_objects(q);
        if self.open.as_ref().is_some_and(|o| o.n as usize == BLOCK || o.depth != depth) {
            self.close_block();
        }
        let w = self.prev.words.len();
        let kind = self.open.as_ref().map_or(new, |o| o.kind);
        let max = if kind == Kind::Raw { codec::raw_size(w) } else { codec::xor_max_size(w) };
        if !self.seg.is_empty() && self.seg.len() + max > q.cfg.seg_bytes {
            self.close_block();
            self.filled = true;
            self.freeze(q);
        }
        if self.open.is_none() {
            if self.seg.capacity() == 0 {
                match q.mem.reuse() {
                    Some(buf) => self.seg = buf,
                    None => {
                        let cap = if self.filled { q.cfg.seg_bytes } else { q.cfg.seg_bytes.min(4096) };
                        self.seg.reserve_exact(cap);
                    }
                }
                self.seg.reserve(max);
            }
            if kind == Kind::Xor {
                self.prev.reset();
            }
            self.open = Some(Open { start: self.seg.len(), n: 0, kind, depth });
        }
        self.open.as_mut().unwrap().n += 1;
        kind
    }

    /// Close the open encoded block.
    pub(super) fn close_block(&mut self) {
        if let Some(o) = self.open.take() {
            self.seg_blocks.push(o);
        }
    }

    /// Turn the open segment's blocks into `Block`s.
    pub(super) fn freeze(&mut self, q: &Queue<'_, S>) {
        if self.seg_blocks.is_empty() {
            return;
        }
        let data = std::mem::take(&mut self.seg);
        let ends: Vec<usize> = self.seg_blocks.iter().skip(1).map(|o| o.start).chain([data.len()]).collect();
        let seg = Seg::new(Segment { charge: Mutex::new(Charge::new(data.capacity(), &q.mem)), data });
        for (o, end) in self.seg_blocks.drain(..).zip(ends) {
            self.blocks.push(Block::Encoded {
                seg: seg.clone(),
                start: o.start as u32,
                end: end as u32,
                n: o.n,
                kind: o.kind,
                depth: o.depth,
            });
        }
    }

    /// Take all blocks written (closing the open ones).
    pub(crate) fn take(&mut self, q: &Queue<'_, S>) -> Vec<Block<S>> {
        self.close_objects(q);
        self.close_block();
        self.freeze(q);
        self.len = 0;
        self.spilled = 0;
        self.kept = 0;
        std::mem::take(&mut self.blocks)
    }
}
