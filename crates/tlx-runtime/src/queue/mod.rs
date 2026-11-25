//! Level queues of states (docs/scale.md §5).
//!
//! A level of the breadth-first search is a sequence of *blocks* of at
//! most 256 states, all of the same depth. Each worker appends the new
//! states it finds to the blocks of its own `Writer`; between levels the
//! writers' blocks become the next level (`Queue::install`), one list per
//! worker. A worker takes the states to expand by claiming blocks: from its
//! own list first, then from the others' (`Queue::claim`). With one worker
//! the order is the exact FIFO order.
//!
//! Blocks hold objects (`Task`s), unless the model has a `StateCodec`:
//! then, once the queue holds more than `Config::compress_above` bytes,
//! writers produce XOR-varint compressed blocks (`codec`): byte ranges of
//! 1 MiB *segments* written by one worker, which decode on their own.
//! Fixed-size raw encoded blocks exist too (`BlockKinds::Raw`): they are
//! slower than objects, which need no copy, so they are not used by
//! default.
//!
//! Under memory pressure (or with `-spill always`) the segments go to disk
//! (`seg`): those a worker writes (`Queue::spill_writer`, at
//! `Queue::submit`), and those of the current level far from being claimed
//! (`Queue::spill_tail`). Claiming a block reads its segment back, and
//! starts reading the next few segments of its list ahead (`PREFETCH`).
//! Only where the bytes are changes: the blocks, their order and the
//! claims are the same.
//!
//! The same blocks make the *archive* of a search that may be resumed
//! (docs/scale.md §6): an archive queue (`Queue::archive`) whose writers
//! keep the expanded states (XOR-varint blocks with a codec, objects
//! without); compressed blocks of the queue are moved there whole once
//! expanded (`Queue::append`).
//!
//! This file holds the queue itself: the level's block lists, claiming,
//! spilling and installation, and the queue's parameters (`Config`,
//! `BlockKinds`) and codec contract (`StateCodec`). The child modules hold
//! the blocks and the memory they hold (`block`), their ends (`reader`,
//! `writer`), the record formats (`codec`) and the segments in memory or on
//! disk (`seg`).

mod block;
pub(crate) mod codec;
mod reader;
mod seg;
mod writer;

pub(crate) use self::block::{Block, Charge, Mem, SegCache, Segment, Task, BLOCK};
pub(crate) use self::reader::Reader;
pub(crate) use self::writer::Writer;

use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::{Arc, Weak};

use parking_lot::{Mutex, RwLock};

use self::codec::XorPrev;
use self::seg::{Seg, Spilled};
use crate::io::{BlockStore, IoError, Spill};

/// Optional on a `Model`: states that can be written as words (a compiled
/// model's encoded states), so that queued states take a few bytes each
/// instead of a heap object.
pub trait StateCodec<S>: Sync {
    /// The number of words of every encoding.
    fn words(&self) -> usize;

    /// Write the encoding of `s` to `out` (`words()` long); returns the
    /// fingerprint of `s` (stored with it).
    fn encode(&self, s: &S, out: &mut [u64]) -> u64;

    /// The state of encoding `w`, at depth (level) `depth`, of fingerprint `fp`.
    fn decode(&self, w: &[u64], depth: u32, fp: u64) -> S;

    /// Validate external raw words before they enter a trusted queue/archive.
    /// Codecs whose states contain process-local handles must override this.
    fn validate(&self, _w: &[u64]) -> Result<(), String> {
        Ok(())
    }

    /// Rewrite any process-local handles in encoded state `src` into their
    /// store-independent checkpoint representation before writing to disk.
    /// Returns `src` directly without copying when no rewriting is needed.
    fn checkpoint_words<'a>(&self, src: &'a [u64], _buf: &'a mut Vec<u64>) -> &'a [u64] {
        src
    }

    /// Validate checkpoint words `src` and rewrite any store-independent
    /// checkpoint handles for this run before they enter the trusted queue or
    /// archive. Returns `src` directly without copying when no rewriting is
    /// needed.
    fn recover_words<'a>(&self, src: &'a [u64], _buf: &'a mut Vec<u64>) -> Result<&'a [u64], String> {
        self.validate(src)?;
        Ok(src)
    }

    /// Decode words known to come from this codec's encoder.
    ///
    /// # Safety
    /// `w` must be an unchanged encoding produced by this codec, or external
    /// words successfully checked by `validate`, with required publication
    /// synchronization. Spilled bytes require checksum verification against
    /// the checksum retained when the original encoding was written.
    unsafe fn decode_trusted(&self, w: &[u64], depth: u32, fp: u64) -> S {
        self.decode(w, depth, fp)
    }

    /// Decode trusted words while reusing an old state's storage.
    ///
    /// # Safety
    /// Same valid-encoding and publication contract as `decode_trusted`.
    unsafe fn decode_into_trusted(&self, w: &[u64], depth: u32, fp: u64, old: S) -> S {
        self.decode_into(w, depth, fp, old)
    }

    /// `decode`, reusing the storage of `old` (a state the search is done
    /// with) if possible.
    fn decode_into(&self, w: &[u64], depth: u32, fp: u64, old: S) -> S {
        drop(old);
        self.decode(w, depth, fp)
    }
}

/// Which kinds of blocks writers produce for a model with a codec.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BlockKinds {
    /// Blocks of objects while the queue holds at most
    /// `Config::compress_above` bytes, XOR-varint ones beyond (until it
    /// holds less than half of that).
    Auto,
    /// Raw encoded blocks only.
    Raw,
    /// XOR-varint blocks only.
    Xor,
    /// Blocks of objects only (no encoding).
    Objects,
}

/// Queue parameters (testing knobs: `TLX_SEG_BYTES`,
/// `TLX_QUEUE_COMPRESS_MB`, read by the CLI).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Config {
    /// Segment size in bytes (default 1 MiB).
    pub seg_bytes: usize,
    pub kinds: BlockKinds,
    /// `BlockKinds::Auto`: the queue size (bytes) above which blocks are
    /// compressed (default 64 MiB; the CLI derives it from the memory
    /// budget, see `crate::mem`). Under memory pressure blocks are
    /// compressed whatever the size (`Queue::squeeze`).
    pub compress_above: usize,
}

impl Default for Config {
    fn default() -> Config {
        Config { seg_bytes: 1 << 20, kinds: BlockKinds::Auto, compress_above: 64 << 20 }
    }
}

/// Segments read ahead of the claims, divided among the lists of a level
/// (at least 2 per list): 8 MiB with the default segments.
const PREFETCH: usize = 8;

/// The blocks of a level written by one worker, claimed in order (by that
/// worker first, then by the others).
#[repr(align(128))]
struct List<S> {
    blocks: Vec<Mutex<Option<Block<S>>>>,
    /// The first block not entirely claimed.
    cursor: AtomicUsize,
    /// The segments of the encoded blocks, in order, with the index of
    /// their first block (weak: a segment is freed once its blocks are read).
    segs: Vec<(usize, Weak<Seg>)>,
    /// The segments before this one were read ahead (or claimed).
    fetched: AtomicUsize,
    /// The segments from this one on were offered to the disk
    /// (`Queue::spill_tail`).
    tail: AtomicUsize,
}

impl<S> List<S> {
    fn new(blocks: Vec<Block<S>>) -> List<S> {
        let mut segs: Vec<(usize, Weak<Seg>)> = Vec::new();
        let mut last: Option<&Arc<Seg>> = None;
        for (i, b) in blocks.iter().enumerate() {
            if let Some(s) = b.seg() {
                if !last.is_some_and(|l| Arc::ptr_eq(l, s)) {
                    segs.push((i, Arc::downgrade(s)));
                    last = Some(s);
                }
            }
        }
        let tail = AtomicUsize::new(segs.len());
        List {
            blocks: blocks.into_iter().map(|b| Mutex::new(Some(b))).collect(),
            cursor: AtomicUsize::new(0),
            segs,
            fetched: AtomicUsize::new(0),
            tail,
        }
    }

    /// The blocks not claimed yet (no claim in progress).
    fn take_rest(&mut self) -> Vec<Block<S>> {
        let start = (*self.cursor.get_mut()).min(self.blocks.len());
        self.blocks.drain(start..).filter_map(|b| b.into_inner()).collect()
    }

    /// The index in `segs` of the segment of block `i` (or of the last
    /// segment before it).
    fn seg_of(&self, i: usize) -> usize {
        self.segs.partition_point(|(first, _)| *first <= i).saturating_sub(1)
    }
}

/// The queue of a search: the current level (one list of blocks per
/// worker), and the blocks of the next one submitted by the workers.
pub(crate) struct Queue<'c, S> {
    codec: Option<&'c dyn StateCodec<S>>,
    /// The words of the encodings.
    words: usize,
    cfg: Config,
    mem: Arc<Mem>,
    /// Memory pressure: `BlockKinds::Auto` compresses new blocks whatever
    /// the queue's size.
    squeeze: AtomicBool,
    level: RwLock<Vec<List<S>>>,
    /// States of the current level not claimed yet.
    unclaimed: AtomicU64,
    /// Blocks of the next level, per worker.
    submitted: Mutex<Vec<(usize, Vec<Block<S>>)>>,
    /// The disk layer, if segments may be spilled; the store of the
    /// spilled segments (created with the first one) and its file's name.
    spill: Option<Spill>,
    store: Mutex<Option<Arc<BlockStore>>>,
    name: &'static str,
    /// Segments go to disk (memory pressure, or `-spill always`).
    spilling: AtomicBool,
    /// Some segment was spilled: claims read ahead.
    spilled: AtomicBool,
    /// The segments spilled.
    spills: AtomicU64,
    /// Segments read ahead per list.
    window: usize,
}

impl<'c, S> Queue<'c, S> {
    /// The queue of `workers` workers.
    pub(crate) fn new(codec: Option<&'c dyn StateCodec<S>>, cfg: Config, workers: usize) -> Queue<'c, S> {
        let mem = Mem::new(cfg.seg_bytes, true);
        let words = codec.map_or(0, |c| c.words());
        let lists = (0..workers.max(1)).map(|_| List::new(Vec::new())).collect();
        Queue::with(codec, words, cfg, mem, lists, (PREFETCH / workers.max(1)).max(2))
    }

    /// An archive (docs/scale.md §6) of states of `words` words (encoded
    /// with `codec` if given), its memory counted in `mem`: its writers
    /// write XOR-varint blocks if the states are encoded (`codec` or
    /// `words > 0`), objects otherwise. (Not a queue: only its writers are
    /// used.)
    pub(crate) fn archive(codec: Option<&'c dyn StateCodec<S>>, words: usize, seg_bytes: usize, mem: Arc<Mem>) -> Queue<'c, S> {
        let kinds = if codec.is_some() || words > 0 { BlockKinds::Xor } else { BlockKinds::Objects };
        let cfg = Config { seg_bytes, kinds, compress_above: 0 };
        Queue::with(codec, words, cfg, mem, Vec::new(), 0)
    }

    fn with(
        codec: Option<&'c dyn StateCodec<S>>,
        words: usize,
        cfg: Config,
        mem: Arc<Mem>,
        lists: Vec<List<S>>,
        window: usize,
    ) -> Queue<'c, S> {
        Queue {
            codec,
            words,
            cfg,
            mem,
            squeeze: AtomicBool::new(false),
            level: RwLock::new(lists),
            unclaimed: AtomicU64::new(0),
            submitted: Mutex::new(Vec::new()),
            spill: None,
            store: Mutex::new(None),
            name: "queue",
            spilling: AtomicBool::new(false),
            spilled: AtomicBool::new(false),
            spills: AtomicU64::new(0),
            window,
        }
    }

    /// This queue's encoded segments may go to disk (`spill_on`), in a file
    /// named after `name`.
    pub(crate) fn with_spill(mut self, spill: &Spill, name: &'static str) -> Queue<'c, S> {
        if spill.enabled() {
            self.spill = Some(spill.clone());
        }
        self.name = name;
        self
    }

    /// Whether states are stored encoded.
    pub(crate) fn encoded(&self) -> bool {
        self.codec.is_some()
    }

    /// A writer for this queue.
    pub(crate) fn writer(&self) -> Writer<S> {
        Writer::new(self.words)
    }

    /// A reader's scratch for this queue.
    pub(crate) fn scratch(&self) -> XorPrev {
        XorPrev::new(self.words)
    }

    /// The memory of the blocks.
    pub(crate) fn mem(&self) -> &Mem {
        &self.mem
    }

    /// The memory account of the blocks.
    pub(crate) fn mem_arc(&self) -> &Arc<Mem> {
        &self.mem
    }

    /// The words of the encodings.
    pub(crate) fn words(&self) -> usize {
        self.words
    }

    /// Memory pressure (or its end): compress new blocks whatever the
    /// queue's size (`BlockKinds::Auto`).
    pub(crate) fn squeeze(&self, on: bool) {
        self.squeeze.store(on, Ordering::Relaxed);
    }

    /// Whether new blocks are compressed because of memory pressure.
    pub(crate) fn squeezed(&self) -> bool {
        self.squeeze.load(Ordering::Relaxed)
    }

    /// Write the encoded segments to disk from now on (or no more): those
    /// of the writers (`spill_writer`, `submit`) and those of the current
    /// level far from the claims (`spill_tail`). Only if the queue may
    /// spill (`with_spill`). Whether it spills now.
    pub(crate) fn spill_on(&self, on: bool) -> bool {
        let on = on && self.spill.is_some() && self.words > 0;
        self.spilling.store(on, Ordering::Relaxed);
        on
    }

    /// Whether segments go to disk.
    #[inline]
    pub(crate) fn spilling(&self) -> bool {
        self.spilling.load(Ordering::Relaxed)
    }

    /// The number of segments written to disk so far.
    pub(crate) fn spilled_segments(&self) -> u64 {
        self.spills.load(Ordering::Relaxed)
    }

    /// Segments kept resident ahead of claims per list.
    #[inline]
    pub(crate) fn window(&self) -> usize {
        self.window
    }

    /// The store of the spilled segments (None if it cannot be created: the
    /// error is recorded in the disk layer, which stops the search).
    fn store(&self) -> Option<Arc<BlockStore>> {
        let spill = self.spill.as_ref()?;
        let mut st = self.store.lock();
        if st.is_none() {
            *st = spill.store(self.name).ok();
        }
        st.clone()
    }

    /// Offer segment `s` to the disk (see `Seg::spill`).
    fn spill_seg(&self, s: &Seg) -> Spilled {
        let (Some(spill), Some(store)) = (&self.spill, self.store()) else { return Spilled::Done };
        let r = s.spill(spill, &store);
        if r == Spilled::Now {
            self.spilled.store(true, Ordering::Relaxed);
            self.spills.fetch_add(1, Ordering::Relaxed);
        }
        r
    }

    /// While spilling: offer the segments of the blocks `w` finished since
    /// the last call to the disk, but the first ones of the level (as many
    /// as are read ahead: they are read first). Stops at a segment being
    /// read (an archive's block moved there whole), offered again next time.
    pub(crate) fn spill_writer(&self, w: &mut Writer<S>) {
        if self.spilling() {
            w.spilled = self.spill_from(&w.blocks, w.spilled, &mut w.kept);
        }
    }

    /// Offer the segments of `blocks` from block `start` on to the disk,
    /// keeping the first ones (counted in `kept`) up to the read-ahead
    /// window; the block where it stopped (at a segment being read).
    fn spill_from(&self, blocks: &[Block<S>], start: usize, kept: &mut usize) -> usize {
        let mut last: Option<&Arc<Seg>> = None;
        let mut i = start;
        while let Some(b) = blocks.get(i) {
            if let Some(s) = b.seg() {
                if !last.is_some_and(|l| Arc::ptr_eq(l, s)) {
                    if *kept < self.window {
                        *kept += 1;
                    } else if self.spill_seg(s) == Spilled::Busy {
                        break;
                    }
                    last = Some(s);
                }
            }
            i += 1;
        }
        i
    }

    /// Offer the segments of `blocks` to the disk (all of them, except
    /// those being read).
    pub(crate) fn spill_blocks(&self, blocks: &[Block<S>]) {
        let mut last: Option<&Arc<Seg>> = None;
        for s in blocks.iter().filter_map(|b| b.seg()) {
            if !last.is_some_and(|l| Arc::ptr_eq(l, s)) {
                self.spill_seg(s);
                last = Some(s);
            }
        }
    }

    /// While spilling: offer the segments of the current level beyond the
    /// read-ahead window of the claims to the disk, from the end of each
    /// list. (Those of a list are offered once.)
    pub(crate) fn spill_tail(&self) {
        if !self.spilling() {
            return;
        }
        let lists = self.level.read();
        for list in lists.iter() {
            let keep = list.seg_of(list.cursor.load(Ordering::Relaxed)) + self.window + 1;
            let mut t = list.tail.load(Ordering::Relaxed);
            while t > keep {
                t -= 1;
                if let Some(s) = list.segs[t].1.upgrade() {
                    self.spill_seg(&s);
                }
                list.tail.store(t, Ordering::Relaxed);
            }
        }
    }

    /// Read the segments of `list` after that of block `i` ahead, up to
    /// the window.
    fn prefetch_ahead(&self, list: &List<S>, i: usize) {
        let Some(spill) = &self.spill else { return };
        if list.segs.is_empty() {
            return;
        }
        let k = list.seg_of(i);
        let upto = (k + self.window).min(list.segs.len() - 1);
        let from = list.fetched.fetch_max(upto + 1, Ordering::Relaxed).max(k + 1);
        for (_, s) in list.segs.iter().take(upto + 1).skip(from) {
            if let Some(s) = s.upgrade() {
                s.prefetch(spill);
            }
        }
    }

    /// States of the current level not claimed yet.
    #[inline]
    pub(crate) fn unclaimed(&self) -> u64 {
        self.unclaimed.load(Ordering::Relaxed)
    }

    /// Append `t` to `w`.
    #[inline]
    pub(crate) fn push(&self, w: &mut Writer<S>, t: Task<S>) {
        w.push(self, t);
    }

    /// Append the state of `t` to `w`, encoded (this queue has a codec).
    #[inline]
    pub(crate) fn push_ref(&self, w: &mut Writer<S>, t: &Task<S>) {
        w.push_ref(self, t);
    }

    /// Append the encoded state `(log, fp, words)` of depth `depth` to `w`
    /// (in an XOR-varint block).
    pub(crate) fn push_words(&self, w: &mut Writer<S>, log: u64, fp: u64, depth: u32, words: &[u64]) {
        w.push_words(self, log, fp, depth, words);
    }

    /// Append block `b` (of another queue, or of this one) to `w`, whole.
    pub(crate) fn append(&self, w: &mut Writer<S>, b: Block<S>) {
        w.append(self, b);
    }

    /// The blocks of `w` (closing the open ones).
    pub(crate) fn take(&self, w: &mut Writer<S>) -> Vec<Block<S>> {
        w.take(self)
    }

    /// The blocks of `w` so far, closing the open ones (`w` goes on
    /// writing new blocks after them).
    pub(crate) fn blocks<'w>(&self, w: &'w mut Writer<S>) -> &'w [Block<S>] {
        w.close_objects(self);
        w.close_block();
        w.freeze(self);
        &w.blocks
    }

    /// The lists of the current level (`for_each_unclaimed_in`).
    pub(crate) fn list_count(&self) -> usize {
        self.level.read().len()
    }

    /// Call `f` with every block of list `l` of the current level not
    /// claimed yet, in claim order; stops at the first error. No worker may
    /// claim meanwhile (a checkpoint at a level barrier); several threads
    /// may each take lists.
    pub(crate) fn for_each_unclaimed_in<E>(&self, l: usize, mut f: impl FnMut(&Block<S>) -> Result<(), E>) -> Result<(), E> {
        let lists = self.level.read();
        let Some(list) = lists.get(l) else { return Ok(()) };
        let start = list.cursor.load(Ordering::Acquire);
        for slot in list.blocks.iter().skip(start) {
            if let Some(b) = &*slot.lock() {
                f(b)?;
            }
        }
        Ok(())
    }

    /// Claim states of the current level for worker `me`: a reader of
    /// them. The blocks `me` wrote come first (they are likely in its
    /// caches), then those of the others, each list in order. With several
    /// workers, a claim takes only part of a block when few states are left
    /// (guided self-scheduling: about 1/(2 * workers) of them), so that the
    /// workers finish a level together. A spilled segment is read back (an
    /// error leaves the block unclaimed), and the next ones of its list
    /// are read ahead.
    pub(crate) fn claim(&self, me: usize, prev: &mut XorPrev) -> Result<Option<Reader<S>>, IoError> {
        self.claim_as(me, prev, true)
    }

    /// `claim`, without reading the block's segment (see `Reader::load`).
    pub(crate) fn claim_unloaded(&self, me: usize, prev: &mut XorPrev) -> Option<Reader<S>> {
        self.claim_as(me, prev, false).ok().flatten()
    }

    fn claim_as(&self, me: usize, prev: &mut XorPrev, load: bool) -> Result<Option<Reader<S>>, IoError> {
        let lists = self.level.read();
        let n = lists.len();
        for k in 0..n {
            let list = &lists[(me + k) % n];
            loop {
                let i = list.cursor.load(Ordering::Acquire);
                let Some(slot) = list.blocks.get(i) else { break };
                let mut slot = slot.lock();
                let Some(b) = slot.take() else {
                    // (Emptied by another worker, which moves the cursor.)
                    drop(slot);
                    let _ = list.cursor.compare_exchange(i, i + 1, Ordering::AcqRel, Ordering::Relaxed);
                    continue;
                };
                let data = match (load, b.seg()) {
                    (true, Some(s)) => match s.get() {
                        Ok(d) => Some(d),
                        Err(e) => {
                            *slot = Some(b);
                            return Err(e);
                        }
                    },
                    _ => None,
                };
                let want = if n == 1 { usize::MAX } else { (self.unclaimed() as usize).div_ceil(2 * n).max(1) };
                let b = if b.len() > want && b.splittable() {
                    let (rest, part) = b.split_last(want);
                    *slot = Some(rest);
                    drop(slot);
                    part
                } else {
                    drop(slot);
                    let _ = list.cursor.compare_exchange(i, i + 1, Ordering::AcqRel, Ordering::Relaxed);
                    b
                };
                self.unclaimed.fetch_sub(b.len() as u64, Ordering::Relaxed);
                if self.spilled.load(Ordering::Relaxed) {
                    self.prefetch_ahead(list, i);
                }
                let mut r = Reader::new(b, prev);
                r.data = data;
                return Ok(Some(r));
            }
        }
        Ok(None)
    }

    /// The next state of reader `r` (reusing the storage of `spare`, if
    /// given and possible).
    #[inline]
    pub(crate) fn read(&self, r: &mut Reader<S>, prev: &mut XorPrev, spare: &mut Option<S>) -> Option<Task<S>> {
        r.next(self.codec, prev, spare)
    }

    /// Remove the states left in `r`: their number; appended to `out` if
    /// `take` (reading its segment back if spilled).
    pub(crate) fn drain_reader(&self, r: &mut Reader<S>, prev: &mut XorPrev, take: bool, out: &mut Vec<Task<S>>) -> Result<usize, IoError> {
        let n = r.left();
        if take {
            r.load()?;
            while let Some(t) = r.next(self.codec, prev, &mut None) {
                out.push(t);
            }
        }
        r.left = 0;
        Ok(n)
    }

    /// Remove the states of writer `w`: their number; appended to `out` if `take`.
    pub(crate) fn drain_writer(&self, w: &mut Writer<S>, prev: &mut XorPrev, take: bool, out: &mut Vec<Task<S>>) -> Result<usize, IoError> {
        let mut n = 0;
        for b in w.take(self) {
            n += self.drain_reader(&mut Reader::new(b, prev), prev, take, out)?;
        }
        Ok(n)
    }

    /// Submit the blocks of writer `w` (of worker `worker`) to the next
    /// level (their segments to disk, while spilling).
    pub(crate) fn submit(&self, worker: usize, w: &mut Writer<S>) {
        let (start, mut kept) = (w.spilled, w.kept);
        let blocks = w.take(self);
        if !blocks.is_empty() {
            if self.spilling() {
                self.spill_from(&blocks, start, &mut kept);
            }
            self.submitted.lock().push((worker, blocks));
        }
    }

    /// Make the submitted blocks the current level: each worker's after
    /// the unclaimed blocks of its list of the current one (left when the
    /// search stops). No worker may be claiming meanwhile. Spilled
    /// segments at the start of the lists are read ahead.
    pub(crate) fn install(&self) {
        let mut lists = self.level.write();
        let n = lists.len();
        let mut next: Vec<Vec<Block<S>>> = lists.iter_mut().map(|l| l.take_rest()).collect();
        for (w, b) in std::mem::take(&mut *self.submitted.lock()) {
            next[w % n].extend(b);
        }
        self.unclaimed.store(next.iter().flatten().map(|b| b.len() as u64).sum(), Ordering::Relaxed);
        *lists = next.into_iter().map(List::new).collect();
        // Rotate the backing spill store at each level boundary: installed
        // segments retain their `Arc<BlockStore>` until read and unlink it once
        // the level finishes, bounding sparse length and extent-tree metadata
        // across arbitrarily many overlapping BFS levels.
        *self.store.lock() = None;
        if let (Some(spill), true) = (&self.spill, self.spilled.load(Ordering::Relaxed)) {
            for list in lists.iter() {
                let upto = self.window.min(list.segs.len());
                list.fetched.store(upto, Ordering::Relaxed);
                for (_, s) in &list.segs[..upto] {
                    if let Some(s) = s.upgrade() {
                        s.prefetch(spill);
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests;
