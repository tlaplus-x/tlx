//! The disk tier of the fingerprint set (docs/scale.md §4.2).
//!
//! Once the in-memory table cannot grow within the memory budget, the set
//! rotates instead of filling up: at a safepoint the table is written to
//! disk as a sorted run, kept in memory read-only (`Disk::old`, a copy of
//! the newest run that answers the lookups of recent states without IO),
//! and a new, empty table takes the inserts. Every fingerprint is in the
//! current table or on disk; the old table only spares reads.
//!
//! A run is a sequence of blocks of sorted, distinct fingerprints in the
//! set's block store (`crate::io`), with, in memory, the first fingerprint
//! of every 4 KiB page (a sparse index: 0.02 byte per fingerprint) and a
//! Bloom filter (`bloom`, 1.25 bytes per fingerprint). A lookup that misses
//! both tables asks the Bloom filter of every run and looks at one page of
//! each run whose filter says "maybe". Runs are disjoint: a fingerprint is
//! inserted into the table only if no run holds it.
//!
//! Lookups read a run through a read-only mapping of its part of the file
//! (`Run::map`; the run files are the only spill files read at random, and
//! go through the page cache): a page the system has in memory costs no
//! system call and no copy (with `pread`, PaxosCommit `-spill
//! always` spent 1.1 µs per page with 1 worker, and 8 workers spent 50 s of
//! system time on 8 M pages). A page's checksum is verified the first time a
//! lookup reads it (`Run::verified`), not on every lookup. Without a
//! mapping (the system refused one), lookups read the page with `pread`.
//!
//! Runs are merged in the background (size-tiered: `MERGE_FANIN` runs of a
//! size class into one), so that lookups ask a few filters only; a merged
//! run replaces its inputs at the next safepoint (`Disk::install_merge`),
//! and the inputs' blocks are deleted when the last reader lets them go.

use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::Arc;
use std::thread::JoinHandle;

use tlx_base::par::OneShot;

use super::bloom::Bloom;
use super::Table;
use crate::io::{as_bytes, as_bytes_mut, BlockRef, BlockStore, IoError, Mapping, PAGE};
use crate::mem::Gauge;

/// Fingerprints of a page of a run.
pub(super) const PAGE_FPS: usize = PAGE / 8;

/// Fingerprints of a block of a run (1 MiB).
pub(super) const BLOCK_FPS: usize = 1 << 17;

/// Size-tiered merging: this many runs of one size class (a power of 4 of
/// fingerprints) are merged into one.
const MERGE_FANIN: usize = 4;

/// The in-memory index of a run, per fingerprint (bytes): its page's fence
/// (8 bytes and a 4-byte block number per page of 512).
const INDEX_BYTES_PER_PAGE: usize = 12;

/// A block of a run.
struct RunBlock {
    r: BlockRef,
    /// Its first page among the run's pages, and its fingerprints.
    first_page: u32,
    count: u32,
}

/// A run: sorted, distinct fingerprints on disk (see the module doc).
pub(super) struct Run {
    store: Arc<BlockStore>,
    blocks: Vec<RunBlock>,
    /// Per page, its first fingerprint and its block.
    fences: Vec<u64>,
    page_block: Vec<u32>,
    count: u64,
    /// The largest fingerprint.
    last: u64,
    bloom: Bloom,
    /// The part of the file holding its blocks, mapped (see the module
    /// doc), and per page whether a lookup verified its checksum.
    map: Option<Mapping>,
    verified: Box<[AtomicU64]>,
    /// Unique in the process (a run never changes: checkpoints refer to
    /// runs by it).
    id: u64,
}

/// The id of the next run.
static NEXT_RUN_ID: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);

impl Run {
    /// The number of fingerprints.
    pub(super) fn len(&self) -> u64 {
        self.count
    }

    /// The memory of its Bloom filter and index.
    pub(super) fn bytes(&self) -> usize {
        self.bloom.bytes()
            + self.fences.capacity() * 8
            + self.page_block.capacity() * 4
            + self.blocks.capacity() * std::mem::size_of::<RunBlock>()
            + self.verified.len() * 8
    }

    /// The memory of the Bloom filter and index of a run of `n` fingerprints.
    pub(super) fn bytes_for(n: usize) -> usize {
        Bloom::bytes_for(n) + n.div_ceil(PAGE_FPS) * INDEX_BYTES_PER_PAGE
    }

    /// Whether the run holds `fp` (normalized): its Bloom filter, then one
    /// page looked at (counted in `reads`).
    pub(super) fn contains(&self, fp: u64, reads: &AtomicU64) -> Result<bool, IoError> {
        if fp > self.last || !self.bloom.maybe(fp) {
            return Ok(false);
        }
        let g = self.fences.partition_point(|&f| f <= fp);
        if g == 0 {
            return Ok(false);
        }
        let g = g - 1;
        let b = &self.blocks[self.page_block[g] as usize];
        let i = g - b.first_page as usize;
        let n = (b.count as usize - i * PAGE_FPS).min(PAGE_FPS);
        reads.fetch_add(1, Ordering::Relaxed);
        if let Some(m) = &self.map {
            let bytes = m.bytes(b.r.off + (i * PAGE) as u64, n * 8);
            let (w, bit) = (&self.verified[g / 64], 1u64 << (g % 64));
            if w.load(Ordering::Relaxed) & bit == 0 {
                self.store.verify_page(&b.r, i, bytes)?;
                w.fetch_or(bit, Ordering::Relaxed);
            }
            // SAFETY: `n` fingerprints, 8-byte aligned (`map_run`).
            let page = unsafe { std::slice::from_raw_parts(bytes.as_ptr().cast::<u64>(), n) };
            return Ok(page.binary_search(&fp).is_ok());
        }
        let mut page = [0u64; PAGE_FPS];
        self.store.read_range(&b.r, i * PAGE, as_bytes_mut(&mut page[..n]))?;
        Ok(page[..n].binary_search(&fp).is_ok())
    }

    /// The fingerprints of block `k`.
    fn read_block(&self, k: usize, buf: &mut Vec<u64>) -> Result<(), IoError> {
        let b = &self.blocks[k];
        buf.clear();
        buf.resize(b.count as usize, 0);
        self.store.read_into(&b.r, as_bytes_mut(buf))
    }
}

impl Drop for Run {
    fn drop(&mut self) {
        // (Unmapped before its blocks are deleted.)
        self.map = None;
        for b in self.blocks.drain(..) {
            self.store.delete(b.r);
        }
    }
}

/// A part of a run being written (see `Pieces`): its blocks, and the
/// fences and blocks of its pages (numbered from 0 within the piece).
#[derive(Default)]
pub(super) struct Piece {
    blocks: Vec<RunBlock>,
    fences: Vec<u64>,
    page_block: Vec<u32>,
    count: u64,
    last: u64,
}

/// Writes ascending fingerprints as blocks of a run (into a `Piece`),
/// adding them to the run's Bloom filter.
pub(super) struct PieceWriter<'a> {
    store: &'a BlockStore,
    bloom: &'a Bloom,
    buf: Vec<u64>,
    piece: Piece,
}

impl<'a> PieceWriter<'a> {
    pub(super) fn new(store: &'a BlockStore, bloom: &'a Bloom) -> PieceWriter<'a> {
        PieceWriter { store, bloom, buf: Vec::new(), piece: Piece::default() }
    }

    /// Append `fp` (larger than the ones before).
    #[inline]
    pub(super) fn push(&mut self, fp: u64) -> Result<(), IoError> {
        debug_assert!(self.buf.last().map_or(self.piece.count == 0 || fp > self.piece.last, |&l| fp > l));
        self.bloom.insert(fp);
        if self.buf.capacity() == 0 {
            self.buf.reserve_exact(BLOCK_FPS);
        }
        self.buf.push(fp);
        if self.buf.len() == BLOCK_FPS {
            self.flush()?;
        }
        Ok(())
    }

    fn flush(&mut self) -> Result<(), IoError> {
        if self.buf.is_empty() {
            return Ok(());
        }
        let p = &mut self.piece;
        let r = self.store.append(as_bytes(&self.buf))?;
        let k = p.blocks.len() as u32;
        p.blocks.push(RunBlock { r, first_page: p.fences.len() as u32, count: self.buf.len() as u32 });
        for page in self.buf.chunks(PAGE_FPS) {
            p.fences.push(page[0]);
            p.page_block.push(k);
        }
        p.count += self.buf.len() as u64;
        p.last = *self.buf.last().unwrap();
        self.buf.clear();
        Ok(())
    }

    /// The piece written; on an error, its blocks are deleted.
    pub(super) fn finish(mut self) -> Result<Piece, IoError> {
        match self.flush() {
            Ok(()) => Ok(std::mem::take(&mut self.piece)),
            Err(e) => {
                discard(self.store, std::mem::take(&mut self.piece));
                Err(e)
            }
        }
    }
}

impl Drop for PieceWriter<'_> {
    fn drop(&mut self) {
        // (Not finished: an error, or a panic.)
        discard(self.store, std::mem::take(&mut self.piece));
    }
}

/// Delete the blocks of `p`.
pub(super) fn discard(store: &BlockStore, p: Piece) {
    for b in p.blocks {
        store.delete(b.r);
    }
}

/// The run made of `pieces` (in ascending order of their fingerprints) and
/// the Bloom filter they were added to.
pub(super) fn assemble(store: Arc<BlockStore>, pieces: Vec<Piece>, bloom: Bloom) -> Run {
    let id = NEXT_RUN_ID.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let mut run = Run {
        store,
        blocks: Vec::new(),
        fences: Vec::new(),
        page_block: Vec::new(),
        count: 0,
        last: 0,
        bloom,
        map: None,
        verified: Box::new([]),
        id,
    };
    let pages: usize = pieces.iter().map(|p| p.fences.len()).sum();
    run.fences.reserve_exact(pages);
    run.page_block.reserve_exact(pages);
    run.blocks.reserve_exact(pieces.iter().map(|p| p.blocks.len()).sum());
    for p in pieces {
        if p.count == 0 {
            continue;
        }
        let (page0, block0) = (run.fences.len() as u32, run.blocks.len() as u32);
        run.blocks.extend(p.blocks.into_iter().map(|b| RunBlock { first_page: b.first_page + page0, ..b }));
        run.fences.extend(p.fences);
        run.page_block.extend(p.page_block.into_iter().map(|k| k + block0));
        run.count += p.count;
        run.last = p.last;
    }
    run.map = map_run(&run);
    run.verified = (0..run.fences.len().div_ceil(64)).map(|_| AtomicU64::new(0)).collect();
    run
}

/// A mapping of the part of the file that holds the blocks of `run` (they
/// are written), if the system gives one and its fingerprints are aligned
/// in it.
fn map_run(run: &Run) -> Option<Mapping> {
    let lo = run.blocks.iter().map(|b| b.r.off).min()?;
    let hi = run.blocks.iter().map(|b| b.r.off + b.r.len as u64).max()?;
    if run.blocks.iter().any(|b| b.r.off % 8 != 0) {
        return None;
    }
    let m = run.store.map(lo, hi)?;
    // (The mapping starts at a page boundary of the system, so offsets
    // aligned in the file are aligned in memory.)
    (m.bytes(lo, 0).as_ptr() as usize).is_multiple_of(8).then_some(m)
}

/// A background merge of runs.
struct Merge {
    inputs: Vec<Arc<Run>>,
    out: Arc<MergeOut>,
    handle: Option<JoinHandle<()>>,
}

/// What a merge shares with its thread.
struct MergeOut {
    result: OneShot<Result<Run, IoError>>,
    /// The result is there.
    done: AtomicBool,
    /// Its installation was requested (see `Disk::merge_ready`).
    asked: AtomicBool,
    /// Stop as soon as possible (the set is dropped).
    cancel: AtomicBool,
    /// The memory the merge holds (its Bloom filter, index, buffers),
    /// also counted in the set's gauge from the start of the merge until
    /// it is installed or dropped (`Disk::end_merge`).
    bytes: AtomicUsize,
    mem: Arc<Gauge>,
}

/// The disk tier (see the module doc). Changed only with exclusive access
/// to the set, except its counters and the merge's state.
pub(super) struct Disk {
    pub(super) store: Arc<BlockStore>,
    /// The set's gauge (for the memory of merges).
    mem: Arc<Gauge>,
    /// The table before the current one (read-only), a copy of `newest`.
    old: Option<Table>,
    newest: Option<Arc<Run>>,
    /// The other runs (in no particular order).
    runs: Vec<Arc<Run>>,
    merge: Option<Merge>,
    /// Merges failed (an IO error): no more merging.
    merge_failed: bool,
    /// Pages read by lookups, and lookups that found the fingerprint on
    /// disk; rotations and merges done.
    reads: AtomicU64,
    hits: AtomicU64,
    pub(super) rotations: u64,
    merges: u64,
}

/// The disk tier's numbers (for `-stats`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct DiskStats {
    /// Runs on disk, and the fingerprints they hold.
    pub runs: u64,
    pub on_disk: u64,
    /// The memory of the Bloom filters and indexes.
    pub index_bytes: u64,
    pub rotations: u64,
    pub merges: u64,
    /// Pages read by lookups, and lookups that found the fingerprint.
    pub reads: u64,
    pub hits: u64,
}

impl Disk {
    /// The disk tier in `store`; the memory of its merges counts in `mem`
    /// (the set's gauge; the rest the set counts itself, `FpSet::account`).
    pub(super) fn new(store: Arc<BlockStore>, mem: Arc<Gauge>) -> Disk {
        Disk {
            store,
            mem,
            old: None,
            newest: None,
            runs: Vec::new(),
            merge: None,
            merge_failed: false,
            reads: AtomicU64::new(0),
            hits: AtomicU64::new(0),
            rotations: 0,
            merges: 0,
        }
    }

    /// Whether `fp` (normalized) is in the old table or on disk.
    pub(super) fn contains(&self, fp: u64) -> Result<bool, IoError> {
        if let Some(t) = &self.old {
            if t.contains(fp) {
                return Ok(true);
            }
        }
        // (`newest` is a copy of `old`.)
        for r in &self.runs {
            if r.contains(fp, &self.reads)? {
                self.hits.fetch_add(1, Ordering::Relaxed);
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// The number of runs.
    pub(super) fn run_count(&self) -> usize {
        self.runs.len() + self.newest.is_some() as usize
    }

    /// The id of run `k` (unique in the process; its fingerprints never
    /// change).
    pub(super) fn run_id(&self, k: usize) -> u64 {
        self.runs.iter().chain(&self.newest).nth(k).expect("a run").id
    }

    /// The number of fingerprints of run `k`.
    pub(super) fn run_len(&self, k: usize) -> u64 {
        self.runs.iter().chain(&self.newest).nth(k).expect("a run").count
    }

    /// Call `f` with the fingerprints of run `k` in ascending order (the
    /// old table is a copy of the newest run); stops at the first error.
    pub(super) fn for_each_in_run(&self, k: usize, mut f: impl FnMut(u64) -> Result<(), String>) -> Result<(), String> {
        let r = self.runs.iter().chain(&self.newest).nth(k).expect("a run");
        let mut buf = Vec::new();
        for b in 0..r.blocks.len() {
            r.read_block(b, &mut buf).map_err(|e| e.0)?;
            for &x in &buf {
                f(x)?;
            }
        }
        Ok(())
    }

    /// Add `run`, read from a checkpoint (not a rotation of the table).
    pub(super) fn add_loaded(&mut self, run: Run) {
        self.runs.push(Arc::new(run));
        self.maybe_merge();
    }

    /// Add `run`, written from the current table; `table` (the current
    /// table, replaced) stays in memory as the old table if given. The
    /// previous old table goes.
    pub(super) fn add(&mut self, run: Run, table: Option<Table>) {
        self.drop_old();
        let run = Arc::new(run);
        match table {
            Some(t) => {
                self.old = Some(t);
                self.newest = Some(run);
            }
            None => self.runs.push(run),
        }
        self.rotations += 1;
        self.maybe_merge();
    }

    /// Drop the old table (its run stays).
    pub(super) fn drop_old(&mut self) {
        self.old = None;
        if let Some(r) = self.newest.take() {
            self.runs.push(r);
        }
    }

    /// The memory of the old table (slot array and overflow segments).
    pub(super) fn old_bytes(&self) -> usize {
        self.old.as_ref().map_or(0, Table::bytes)
    }

    /// The slot-array bytes of the old table (excluding overflow segments,
    /// which charge `mem` directly).
    pub(super) fn old_array_bytes(&self) -> usize {
        self.old.as_ref().map_or(0, Table::array_bytes_now)
    }

    /// The memory of the Bloom filters and indexes (and of a merge in
    /// progress).
    pub(super) fn index_bytes(&self) -> usize {
        self.runs_bytes() + self.merge.as_ref().map_or(0, |m| m.out.bytes.load(Ordering::Relaxed))
    }

    /// The memory of the Bloom filters and indexes of the runs.
    pub(super) fn runs_bytes(&self) -> usize {
        self.runs.iter().chain(&self.newest).map(|r| r.bytes()).sum::<usize>()
    }

    /// A merge's thread has ended (joined): its memory goes from the gauge.
    fn end_merge(&self, m: &Merge) {
        self.mem.sub(m.out.bytes.load(Ordering::Relaxed));
    }

    pub(super) fn stats(&self) -> DiskStats {
        let runs = self.runs.iter().chain(&self.newest);
        DiskStats {
            runs: runs.clone().count() as u64,
            on_disk: runs.map(|r| r.len()).sum(),
            index_bytes: self.index_bytes() as u64,
            rotations: self.rotations,
            merges: self.merges,
            reads: self.reads.load(Ordering::Relaxed),
            hits: self.hits.load(Ordering::Relaxed),
        }
    }

    /// Whether a merge has finished and was not asked to be installed yet
    /// (then it is asked now: true once per merge).
    #[inline]
    pub(super) fn merge_ready(&self) -> bool {
        self.merge.as_ref().is_some_and(|m| m.out.done.load(Ordering::Acquire) && !m.out.asked.swap(true, Ordering::Relaxed))
    }

    /// Install a finished merge (with `wait`: wait for one in progress):
    /// its run replaces its inputs. Then start the next merge if one is due.
    pub(super) fn install_merge(&mut self, wait: bool) {
        loop {
            let Some(m) = &self.merge else { return };
            if !wait && !m.out.done.load(Ordering::Acquire) {
                return;
            }
            let mut m = self.merge.take().unwrap();
            if let Some(h) = m.handle.take() {
                let _ = h.join();
            }
            self.end_merge(&m);
            match m.out.result.try_take() {
                Some(Ok(run)) => {
                    self.runs.retain(|r| !m.inputs.iter().any(|i| Arc::ptr_eq(i, r)));
                    self.runs.push(Arc::new(run));
                    self.merges += 1;
                }
                // (The error is recorded: the search stops.)
                _ => self.merge_failed = true,
            }
            // (The inputs' blocks are deleted as their last reference goes.)
            drop(m);
            self.maybe_merge();
        }
    }

    /// Start merging the runs of the smallest size class that has
    /// `MERGE_FANIN` of them, if no merge is in progress.
    fn maybe_merge(&mut self) {
        if self.merge.is_some() || self.merge_failed {
            return;
        }
        let class = |r: &Run| (63 - r.len().max(1).leading_zeros()) / 2;
        let mut classes: Vec<u32> = self.runs.iter().map(|r| class(r)).collect();
        classes.sort_unstable();
        let Some(c) = classes.chunk_by(|a, b| a == b).find(|g| g.len() >= MERGE_FANIN).map(|g| g[0]) else { return };
        let inputs: Vec<Arc<Run>> = self.runs.iter().filter(|r| class(r) == c).cloned().collect();
        let out = Arc::new(MergeOut {
            result: OneShot::new(),
            done: AtomicBool::new(false),
            asked: AtomicBool::new(false),
            cancel: AtomicBool::new(false),
            bytes: AtomicUsize::new(0),
            mem: self.mem.clone(),
        });
        let (ins, o, store) = (inputs.clone(), out.clone(), self.store.clone());
        let handle = tlx_base::stack::spawn(std::thread::Builder::new().name("tlx-fpset-merge".into()), move || {
            let r = merge(store, &ins, &o);
            drop(ins);
            if let Some(result) = r.transpose() {
                o.result.set(result);
            }
            o.done.store(true, Ordering::Release);
        })
        .expect("failed to spawn the fingerprint-set merge thread");
        self.merge = Some(Merge { inputs, out, handle: Some(handle) });
    }
}

impl Drop for Disk {
    fn drop(&mut self) {
        if let Some(mut m) = self.merge.take() {
            m.out.cancel.store(true, Ordering::Relaxed);
            if let Some(h) = m.handle.take() {
                let _ = h.join();
            }
            self.end_merge(&m);
        }
    }
}

/// Merge `inputs` into one run (None if cancelled).
fn merge(store: Arc<BlockStore>, inputs: &[Arc<Run>], out: &MergeOut) -> Result<Option<Run>, IoError> {
    let total: u64 = inputs.iter().map(|r| r.len()).sum();
    let bloom = Bloom::new(total as usize);
    let bytes = Run::bytes_for(total as usize) + (inputs.len() + 1) * BLOCK_FPS * 8;
    out.bytes.store(bytes, Ordering::Relaxed);
    out.mem.add(bytes);
    struct Cursor<'r> {
        run: &'r Run,
        block: usize,
        buf: Vec<u64>,
        pos: usize,
    }
    impl Cursor<'_> {
        /// The current fingerprint, reading the next block when needed.
        fn head(&mut self) -> Result<Option<u64>, IoError> {
            while self.pos == self.buf.len() {
                if self.block == self.run.blocks.len() {
                    return Ok(None);
                }
                self.run.read_block(self.block, &mut self.buf)?;
                self.block += 1;
                self.pos = 0;
            }
            Ok(Some(self.buf[self.pos]))
        }
    }
    let mut cursors: Vec<Cursor<'_>> = inputs.iter().map(|r| Cursor { run: r, block: 0, buf: Vec::new(), pos: 0 }).collect();
    let mut w = PieceWriter::new(&store, &bloom);
    let mut since_check = 0;
    loop {
        // (A few inputs: the least head by a linear scan.)
        let mut min: Option<(u64, usize)> = None;
        for (k, c) in cursors.iter_mut().enumerate() {
            if let Some(f) = c.head()? {
                if min.is_none_or(|(m, _)| f < m) {
                    min = Some((f, k));
                }
            }
        }
        let Some((f, _)) = min else { break };
        for c in cursors.iter_mut() {
            // (Runs are disjoint; equal heads are skipped all the same.)
            if c.pos < c.buf.len() && c.buf[c.pos] == f {
                c.pos += 1;
            }
        }
        w.push(f)?;
        since_check += 1;
        if since_check == BLOCK_FPS {
            since_check = 0;
            if out.cancel.load(Ordering::Relaxed) {
                return Ok(None);
            }
        }
    }
    let piece = w.finish()?;
    Ok(Some(assemble(store, vec![piece], bloom)))
}
