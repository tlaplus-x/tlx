//! Bounded-memory external merge-sort for single-worker recovery of a
//! positioned checkpoint queue (docs/scale.md §9.3).
//!
//! A checkpoint written by several workers under VIEW, SYMMETRY or `-coverage`
//! records each queued state's BFS position (`0..queued`). With one worker,
//! expansion order is exact BFS order, so the queued level must be reordered
//! by position before entering `seed`.
//!
//! States are buffered compactly in memory — encoded words as delta-XOR
//! varints relative to the run's first state, serialized states as raw
//! `Persist` payloads (with oversized payloads stored out-of-line as external
//! `BlockRef`s once spilling is active) — with a 16-byte `(pos, off)` index
//! sorted in place. All buffer memory is charged to `Component::Frontier`.
//!
//! When the buffer reaches its share of `MemBudget` (or under `-spill always`),
//! the sorted run is written in page-aligned sequential XOR-varint or raw
//! chunks to its own temporary `BlockStore` (`recover-run-<n>.spill`) in the
//! spill directory. Each run's block list and page checksums are stored on disk
//! as a small page-aligned multi-level index tree inside that run's
//! `BlockStore`, leaving only a single root `BlockRef` (`O(1)` RAM) per run in
//! memory. As blocks are consumed during a merge, their page-aligned extents
//! are punched (`BlockStore::delete_reclaimable`), and each consumed run's
//! `BlockStore` is dropped and unlinked immediately at EOF so allocated disk
//! space stays strictly within `-maxdisk`. Oversized serialized payloads live
//! in a separate page-aligned `recover-ext-<n>.spill` store so they transfer
//! zero-copy across intermediate merges and reclaim whole pages when emitted.
//! Size-tiered compaction keeps the number of live runs (and open files)
//! logarithmic without quadratic rewrites, and merge batch selection sizes each
//! pass by the runs' actual maximum block sizes so oversized records never
//! multiply memory across merge inputs.

use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::ops::Range;
use std::sync::Arc;

use tlx_base::bytes::{get_uvar_trusted, put_uvar, unzigzag, zigzag};

use crate::io::{BlockRef, BlockStore, Spill, SpillMode, PAGE};
use crate::mem::{Gauge, Part};
use crate::queue::codec::{self, XorPrev};

/// Maximum fan-in per compaction or merge pass. Keeps live per-run spill files
/// bounded well below conservative file-descriptor limits (`O(MAX_MERGE_WAY *
/// tiers)`) while maintaining logarithmic pass count.
const MAX_MERGE_WAY: usize = 16;

/// Tag byte for `SortFormat::Bytes` records: payload stored inline.
const TAG_INLINE: u8 = 0;
/// Tag byte for `SortFormat::Bytes` records: payload stored in an external
/// `BlockRef` inside the sorter's page-aligned external `BlockStore`
/// (zero-copy across intermediate merges; loaded one record at a time during
/// final emission).
const TAG_EXTERNAL: u8 = 1;

/// Round a target chunk/index size to a whole positive multiple of `PAGE`.
fn align_chunk(bytes: usize) -> usize {
    (bytes.max(PAGE) / PAGE) * PAGE
}

/// Zero-pad `buf` to a positive whole multiple of `PAGE` so every block written
/// to a per-run store starts at a `PAGE`-aligned offset and spans whole pages.
fn pad_to_page(buf: &mut Vec<u8>) {
    let padded = buf.len().max(1).next_multiple_of(PAGE);
    buf.resize(padded, 0);
}

/// Encoded byte length of an unsigned varint (`put_uvar`).
#[inline]
fn uvar_len(mut v: u64) -> usize {
    let mut n = 1;
    while v >= 0x80 {
        v >>= 7;
        n += 1;
    }
    n
}

/// Exact encoded byte length of one `Words` run record (`pos_delta` +
/// `codec::put_xor` relative to `prev`).
fn xor_record_len(prev: &XorPrev, pos_delta: u64, log: u64, words: &[u64]) -> usize {
    let mut len = uvar_len(pos_delta) + uvar_len(zigzag(log.wrapping_sub(prev.log) as i64)) + 8 + words.len().div_ceil(8);
    for (&w, &p) in words.iter().zip(&prev.words) {
        if w != p {
            len += uvar_len(w ^ p);
        }
    }
    len
}

/// Persist an oversized `Bytes` payload into the page-aligned external store
/// prefixed with its exact byte length (`[u64 len][payload][zero pad]`).
fn write_external(store: &BlockStore, payload: &[u8]) -> Result<BlockRef, String> {
    store.append_paged(&(payload.len() as u64).to_le_bytes(), payload).map_err(|e| e.0)
}

/// Read an external `Bytes` payload written by `write_external`, returning the
/// backing buffer and exact payload byte length (`&buf[8..8 + len]`).
fn read_external(store: &BlockStore, bref: &BlockRef) -> Result<(Vec<u8>, usize), String> {
    let data = store.read(bref).map_err(|e| e.0)?;
    if data.len() < 8 {
        return Err("corrupt external sort block".into());
    }
    let len = usize::try_from(u64::from_le_bytes(data[..8].try_into().expect("8 bytes")))
        .map_err(|_| "corrupt external sort block".to_string())?;
    if len.checked_add(8).is_none_or(|end| end > data.len()) {
        return Err("corrupt external sort block".into());
    }
    Ok((data, len))
}

/// State representation buffered by [`QueueSorter`].
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SortFormat {
    /// Encoded states of `words` u64 words.
    Words(usize),
    /// Serialized `Persist` state payloads.
    Bytes,
}

impl SortFormat {
    fn num_words(self) -> usize {
        match self {
            SortFormat::Words(w) => w,
            SortFormat::Bytes => 0,
        }
    }

    fn per_run_overhead(self) -> usize {
        self.num_words() * 8 + 1024
    }
}

/// Memory and spilling limits for [`QueueSorter`].
#[derive(Clone, Copy, Debug)]
pub(super) struct SortConfig {
    pub(super) format: SortFormat,
    /// Maximum in-memory run buffer bytes before flushing a sorted run to disk
    /// (`usize::MAX` when spilling is disabled or the budget is unlimited).
    pub(super) run_limit: usize,
    /// Target byte size of each spilled data/index block (`BlockRef`).
    pub(super) chunk_bytes: usize,
    /// Target memory budget for k-way merge read buffers.
    pub(super) merge_budget: usize,
    /// Spill even when the entire level fits in one run (`SpillMode::Always`).
    pub(super) force_spill: bool,
    /// Whether disk spilling is permitted (`mode != SpillMode::Off`).
    pub(super) can_spill: bool,
}

impl SortConfig {
    /// Derive sort limits from the search's memory budget, current headroom,
    /// queue segment size and spill mode.
    pub(super) fn for_budget(format: SortFormat, total: usize, room: usize, seg_bytes: usize, mode: SpillMode) -> SortConfig {
        let seg = seg_bytes.max(4096);
        match mode {
            SpillMode::Off => SortConfig {
                format,
                run_limit: usize::MAX,
                chunk_bytes: seg.clamp(4096, 256 << 10),
                merge_budget: usize::MAX,
                force_spill: false,
                can_spill: false,
            },
            SpillMode::Always => {
                let chunk_bytes = seg.clamp(4096, 64 << 10);
                SortConfig { format, run_limit: seg, chunk_bytes, merge_budget: seg, force_spill: true, can_spill: true }
            }
            SpillMode::Auto if total == usize::MAX => SortConfig {
                format,
                run_limit: usize::MAX,
                chunk_bytes: seg.clamp(4096, 256 << 10),
                merge_budget: usize::MAX,
                force_spill: false,
                can_spill: true,
            },
            SpillMode::Auto => {
                let run_limit = auto_run_limit(total, room, seg);
                let chunk_bytes = (total / 64).clamp(4096, 256 << 10).min(seg);
                SortConfig { format, run_limit, chunk_bytes, merge_budget: run_limit, force_spill: false, can_spill: true }
            }
        }
    }

    /// Payloads larger than this threshold are written as external `BlockRef`s
    /// when spilling, keeping data blocks bounded to `~chunk_bytes`.
    fn external_threshold(self) -> usize {
        (self.chunk_bytes / 2).max(1024)
    }
}

/// Compute the in-memory run cap for `SpillMode::Auto` under a finite budget:
/// half of current headroom, bounded between a small floor (so tight budgets
/// still make progress without tiny 1-state runs) and a quarter of total
/// budget (leaving headroom for `seed` and other components without triggering
/// stage-1 archive relief).
fn auto_run_limit(total: usize, room: usize, seg: usize) -> usize {
    let floor = (total / 8).clamp(4096, 1 << 20).min(seg);
    let ceiling = (total / 4).max(floor);
    (room / 2).clamp(floor, ceiling)
}

/// A sorted record yielded by [`QueueSorter::finish`].
pub(super) enum Record<'a> {
    Words { pos: u64, log: u64, fp: u64, words: &'a [u64] },
    Bytes { pos: u64, log: u64, fp: u64, payload: &'a [u8] },
}

/// Index entry in the current in-memory run buffer (16 bytes).
#[derive(Clone, Copy)]
struct Entry {
    pos: u64,
    off: usize,
}

/// On-disk tree of data blocks rooted at a single `BlockRef` (`O(1)` RAM).
///
/// `height == 0` means `root` is the run's sole data block directly;
/// `height > 0` means `root` is an index block whose serialized child
/// `BlockRef`s are at `height - 1`.
struct BlockTree {
    root: BlockRef,
    height: u8,
    max_block_bytes: usize,
    max_index_bytes: usize,
}

/// Builds a [`BlockTree`] using only `O(height)` index buffers in RAM.
struct BlockTreeWriter {
    store: Arc<BlockStore>,
    index_bytes: usize,
    /// Per index level (`0` holds data `BlockRef`s, `1` holds level-0 index
    /// `BlockRef`s, ...): `[u32 count | encoded BlockRefs...]`.
    levels: Vec<Vec<u8>>,
    counts: Vec<u32>,
    max_block_bytes: usize,
    max_index_bytes: usize,
}

impl BlockTreeWriter {
    fn new(store: Arc<BlockStore>, index_bytes: usize) -> BlockTreeWriter {
        BlockTreeWriter {
            store,
            index_bytes: align_chunk(index_bytes),
            levels: Vec::new(),
            counts: Vec::new(),
            max_block_bytes: 0,
            max_index_bytes: 0,
        }
    }

    fn bytes(&self) -> usize {
        self.levels.iter().map(Vec::capacity).sum::<usize>()
            + self.levels.capacity() * std::mem::size_of::<Vec<u8>>()
            + self.counts.capacity() * std::mem::size_of::<u32>()
    }

    fn push_data_block(&mut self, block: BlockRef) -> Result<(), String> {
        self.max_block_bytes = self.max_block_bytes.max(block.len);
        self.push_at_level(0, block)
    }

    fn push_at_level(&mut self, lvl: usize, child: BlockRef) -> Result<(), String> {
        if self.levels.len() <= lvl {
            self.levels.push(0u32.to_le_bytes().to_vec());
            self.counts.push(0);
        }
        if self.counts[lvl] > 0 && self.levels[lvl].len().saturating_add(child.encoded_len()) > self.index_bytes {
            let idx = self.flush_level(lvl)?;
            self.push_at_level(lvl + 1, idx)?;
        }
        child.encode(&mut self.levels[lvl]);
        self.counts[lvl] += 1;
        Ok(())
    }

    fn flush_level(&mut self, lvl: usize) -> Result<BlockRef, String> {
        let count = self.counts[lvl];
        debug_assert!(count > 0);
        self.levels[lvl][..4].copy_from_slice(&count.to_le_bytes());
        pad_to_page(&mut self.levels[lvl]);
        let b = self.store.append(&self.levels[lvl]).map_err(|e| e.0)?;
        self.max_index_bytes = self.max_index_bytes.max(b.len);
        self.levels[lvl].clear();
        self.levels[lvl].extend_from_slice(&0u32.to_le_bytes());
        self.counts[lvl] = 0;
        Ok(b)
    }

    fn finish(mut self) -> Result<Option<BlockTree>, String> {
        if self.levels.is_empty() {
            return Ok(None);
        }
        let mut lvl = 0usize;
        loop {
            if lvl + 1 == self.levels.len() && self.counts[lvl] == 1 {
                let mut at = 4;
                let root = BlockRef::decode(&self.levels[lvl], &mut at).map_err(|e| e.0)?;
                return Ok(Some(BlockTree {
                    root,
                    height: lvl as u8,
                    max_block_bytes: self.max_block_bytes,
                    max_index_bytes: if lvl == 0 { 0 } else { self.max_index_bytes },
                }));
            }
            if self.counts[lvl] > 0 {
                let idx = self.flush_level(lvl)?;
                self.push_at_level(lvl + 1, idx)?;
            }
            lvl += 1;
        }
    }
}

/// One open index block on the descent stack of [`BlockTreeReader`].
struct IndexFrame {
    block: BlockRef,
    data: Vec<u8>,
    at: usize,
    left: u32,
    /// Logical tree level of this index block (`1` = children are level-0 data
    /// blocks; `2` = children are level-1 index blocks, etc.). Stored
    /// explicitly so popping an exhausted parent never shifts child depth.
    level: u8,
}

impl IndexFrame {
    fn open(store: &BlockStore, block: BlockRef, level: u8) -> Result<IndexFrame, String> {
        debug_assert!(level > 0);
        let data = store.read(&block).map_err(|e| e.0)?;
        if data.len() < 4 {
            return Err("corrupt sort index block".into());
        }
        let left = u32::from_le_bytes(data[..4].try_into().expect("4 bytes"));
        Ok(IndexFrame { block, data, at: 4, left, level })
    }

    fn bytes(&self) -> usize {
        self.block.sums_bytes() + self.data.capacity()
    }
}

/// Streams level-0 data `BlockRef`s out of a [`BlockTree`] using `O(height)`
/// RAM, deleting each index block as soon as its last child is consumed.
struct BlockTreeReader {
    single: Option<BlockRef>,
    frames: Vec<IndexFrame>,
    height: u8,
}

impl BlockTreeReader {
    fn open(store: &BlockStore, tree: BlockTree) -> Result<BlockTreeReader, String> {
        if tree.height == 0 {
            return Ok(BlockTreeReader { single: Some(tree.root), frames: Vec::new(), height: 0 });
        }
        let mut frames = Vec::with_capacity(tree.height as usize);
        frames.push(IndexFrame::open(store, tree.root, tree.height)?);
        Ok(BlockTreeReader { single: None, frames, height: tree.height })
    }

    fn bytes(&self) -> usize {
        self.single.as_ref().map_or(0, BlockRef::sums_bytes)
            + self.frames.iter().map(IndexFrame::bytes).sum::<usize>()
            + self.frames.capacity() * std::mem::size_of::<IndexFrame>()
    }

    fn next_block(&mut self, store: &BlockStore) -> Result<Option<BlockRef>, String> {
        if self.height == 0 {
            return Ok(self.single.take());
        }
        loop {
            while self.frames.last().is_some_and(|f| f.left == 0) {
                let done = self.frames.pop().expect("non-empty");
                store.delete_reclaimable(done.block);
            }
            let Some(top) = self.frames.last_mut() else {
                return Ok(None);
            };
            let child = BlockRef::decode(&top.data, &mut top.at).map_err(|e| e.0)?;
            top.left -= 1;
            let child_level = top.level - 1;
            if top.left == 0 {
                let done = self.frames.pop().expect("non-empty");
                store.delete_reclaimable(done.block);
            }
            if child_level == 0 {
                return Ok(Some(child));
            }
            self.frames.push(IndexFrame::open(store, child, child_level)?);
        }
    }
}

/// A sorted run persisted in its own temporary `BlockStore` (`O(1)` RAM).
struct Run {
    store: Arc<BlockStore>,
    tree: BlockTree,
    count: u64,
    tier: u8,
}

impl Run {
    /// Estimated peak RAM of a [`RunReader`] scanning this run.
    fn reader_bytes(&self, format: SortFormat) -> usize {
        self.tree
            .max_block_bytes
            .saturating_add((self.tree.height as usize).saturating_mul(self.tree.max_index_bytes))
            .saturating_add(format.per_run_overhead())
    }
}

/// Bounded-memory sorter for queued checkpoint states keyed by BFS position.
pub(super) struct QueueSorter<'a> {
    cfg: SortConfig,
    spill: &'a Spill,
    gauge: &'a Gauge,
    charge: Part,
    /// Page-aligned store for oversized externalized `SortFormat::Bytes` payloads.
    ext_store: Option<Arc<BlockStore>>,
    runs: Vec<Run>,
    base: XorPrev,
    has_base: bool,
    buf: Vec<u8>,
    entries: Vec<Entry>,
    scratch: Vec<u64>,
}

impl Drop for QueueSorter<'_> {
    fn drop(&mut self) {
        self.charge.set(self.gauge, 0);
    }
}

impl<'a> QueueSorter<'a> {
    pub(super) fn new(cfg: SortConfig, spill: &'a Spill, gauge: &'a Gauge) -> QueueSorter<'a> {
        let w = cfg.format.num_words();
        let sorter = QueueSorter {
            cfg,
            spill,
            gauge,
            charge: Part::default(),
            ext_store: None,
            runs: Vec::new(),
            base: XorPrev::new(w),
            has_base: false,
            buf: Vec::new(),
            entries: Vec::new(),
            scratch: vec![0; w],
        };
        sorter.update_charge(0);
        sorter
    }

    pub(super) fn format(&self) -> SortFormat {
        self.cfg.format
    }

    pub(super) fn can_spill(&self) -> bool {
        self.cfg.can_spill
    }

    pub(super) fn charged_bytes(&self) -> usize {
        self.charge.get()
    }

    fn ensure_ext_store(&mut self) -> Result<Arc<BlockStore>, String> {
        ensure_ext_store(self.spill, &mut self.ext_store)
    }

    /// Recompute the run cap from the current budget headroom (for
    /// `SpillMode::Auto`), flushing the current run immediately if it now
    /// exceeds the cap.
    pub(super) fn refresh_budget(&mut self, total: usize, room: usize, seg_bytes: usize) -> Result<(), String> {
        if !self.cfg.can_spill || self.cfg.force_spill || total == usize::MAX {
            return Ok(());
        }
        let seg = seg_bytes.max(4096);
        let limit = auto_run_limit(total, room, seg);
        self.cfg.run_limit = limit;
        self.cfg.merge_budget = limit;
        if !self.entries.is_empty() && self.data_bytes() >= self.cfg.run_limit {
            self.flush_run()?;
        }
        Ok(())
    }

    fn append_entry(&mut self, pos: u64, encode: impl FnOnce(&mut Vec<u8>, &XorPrev)) {
        let prev_cap = self.buf.capacity() + self.entries.capacity();
        let off = self.buf.len();
        encode(&mut self.buf, &self.base);
        self.entries.push(Entry { pos, off });
        if self.buf.capacity() + self.entries.capacity() != prev_cap {
            self.update_charge(0);
        }
    }

    /// Buffer an encoded state (`SortFormat::Words`).
    pub(super) fn push_words(&mut self, pos: u64, log: u64, fp: u64, words: &[u64]) -> Result<(), String> {
        debug_assert_eq!(self.cfg.format, SortFormat::Words(words.len()));
        if self.cfg.can_spill && !self.entries.is_empty() && self.data_bytes() >= self.cfg.run_limit {
            self.flush_run()?;
        }
        if !self.has_base {
            self.base.log = log;
            self.base.words.copy_from_slice(words);
            self.has_base = true;
        }
        self.append_entry(pos, |buf, base| put_xor_ref(buf, base, log, fp, words));
        Ok(())
    }

    /// Buffer a serialized `Persist` state (`SortFormat::Bytes`).
    ///
    /// Oversized payloads (larger than `chunk_bytes / 2`) are written directly
    /// to `BlockStore` as external `BlockRef`s whenever spilling is active or
    /// the payload would exceed `run_limit`, so neither the run buffer nor
    /// k-way merge ever accumulates multiple large payloads in RAM.
    pub(super) fn push_bytes(&mut self, pos: u64, log: u64, fp: u64, payload: &[u8]) -> Result<(), String> {
        debug_assert_eq!(self.cfg.format, SortFormat::Bytes);
        let inline_est = 1 + 8 + 10 + 10 + payload.len() + std::mem::size_of::<Entry>();
        let externalize = self.cfg.can_spill
            && payload.len() > self.cfg.external_threshold()
            && (self.cfg.force_spill || !self.runs.is_empty() || self.data_bytes().saturating_add(inline_est) > self.cfg.run_limit);
        if externalize {
            let store = self.ensure_ext_store()?;
            let bref = write_external(&store, payload)?;
            let ext_est = 1 + 8 + 10 + bref.encoded_len() + std::mem::size_of::<Entry>();
            if !self.entries.is_empty() && self.data_bytes().saturating_add(ext_est) > self.cfg.run_limit {
                self.flush_run()?;
            }
            self.append_entry(pos, |buf, _| {
                buf.push(TAG_EXTERNAL);
                buf.extend_from_slice(&fp.to_le_bytes());
                put_uvar(buf, log);
                bref.encode(buf);
            });
            return Ok(());
        }
        if self.cfg.can_spill && !self.entries.is_empty() && self.data_bytes().saturating_add(inline_est) > self.cfg.run_limit {
            self.flush_run()?;
        }
        self.append_entry(pos, |buf, _| {
            buf.push(TAG_INLINE);
            buf.extend_from_slice(&fp.to_le_bytes());
            put_uvar(buf, log);
            put_uvar(buf, payload.len() as u64);
            buf.extend_from_slice(payload);
        });
        Ok(())
    }

    /// Emit all buffered states in ascending `pos` order (with deterministic
    /// tie-breaking by insertion order).
    pub(super) fn finish(mut self, mut emit: impl FnMut(Record<'_>) -> Result<(), String>) -> Result<(), String> {
        if self.entries.is_empty() && self.runs.is_empty() {
            return Ok(());
        }
        // Fast path: everything fits in one in-memory run and disk forcing is off.
        if self.runs.is_empty() && !self.cfg.force_spill {
            self.entries.sort_unstable_by_key(|e| (e.pos, e.off));
            match self.cfg.format {
                SortFormat::Words(_) => {
                    for &e in &self.entries {
                        let mut at = e.off;
                        let (log, fp) = get_xor_ref(&self.buf, &mut at, &self.base, &mut self.scratch);
                        emit(Record::Words { pos: e.pos, log, fp, words: &self.scratch })?;
                    }
                }
                SortFormat::Bytes => {
                    for &e in &self.entries {
                        match get_bytes_rec(&self.buf, e.off)? {
                            (log, fp, BufBytes::Inline(range)) => {
                                emit(Record::Bytes { pos: e.pos, log, fp, payload: &self.buf[range] })?;
                            }
                            (log, fp, BufBytes::External(bref)) => {
                                let store = self.ext_store.as_ref().expect("external payload has a store");
                                let (data, len) = read_external(store, &bref)?;
                                self.update_charge(data.capacity());
                                let res = emit(Record::Bytes { pos: e.pos, log, fp, payload: &data[8..8 + len] });
                                store.delete_reclaimable(bref);
                                drop(data);
                                self.update_charge(0);
                                res?;
                            }
                        }
                    }
                }
            }
            return Ok(());
        }

        // Disk path: flush the trailing run and release all run-building buffers
        // before allocating k-way merge read buffers.
        if !self.entries.is_empty() {
            self.flush_run_inner(false)?;
        }
        self.buf = Vec::new();
        self.entries = Vec::new();
        self.base.words = Vec::new();
        self.scratch = Vec::new();
        self.update_charge(0);

        // Multi-pass reduction while the remaining runs exceed the merge budget
        // (or the `MAX_MERGE_WAY` cap), sizing each batch by the runs' actual
        // block sizes.
        while self.runs.len() > 2 {
            let total_readers: usize = self.runs.iter().map(|r| r.reader_bytes(self.cfg.format)).sum();
            if self.runs.len() <= MAX_MERGE_WAY && total_readers <= self.cfg.merge_budget {
                break;
            }
            self.runs.sort_by_key(|r| r.count);
            let k = pick_batch_len(&self.runs, self.cfg.format, self.cfg.merge_budget, self.writer_reserve());
            let tier = self.runs[..k].iter().map(|r| r.tier).max().unwrap_or(0).saturating_add(1);
            let batch: Vec<Run> = self.runs.drain(..k).collect();
            self.merge_to_run(batch, tier)?;
        }

        let ext_store = self.ext_store.clone();
        let batch = std::mem::take(&mut self.runs);
        merge_runs(self.cfg.format, batch, self.gauge, &self.charge, 0, |rec, extra| match rec {
            MergeRecord::Words { pos, log, fp, words } => emit(Record::Words { pos, log, fp, words }),
            MergeRecord::BytesInline { pos, log, fp, payload } => emit(Record::Bytes { pos, log, fp, payload }),
            MergeRecord::BytesExternal { pos, log, fp, bref } => {
                let store = ext_store.as_ref().expect("external payload has a store");
                let (data, len) = read_external(store, &bref)?;
                self.charge.set(self.gauge, extra + data.capacity());
                let res = emit(Record::Bytes { pos, log, fp, payload: &data[8..8 + len] });
                store.delete_reclaimable(bref);
                drop(data);
                self.charge.set(self.gauge, extra);
                res
            }
        })
    }

    fn writer_reserve(&self) -> usize {
        // Reserve room for one data chunk and two index-level buffers during an
        // intermediate merge pass.
        align_chunk(self.cfg.chunk_bytes).saturating_mul(2)
    }

    fn flush_run(&mut self) -> Result<(), String> {
        self.flush_run_inner(true)
    }

    fn flush_run_inner(&mut self, compact: bool) -> Result<(), String> {
        if self.entries.is_empty() {
            return Ok(());
        }
        let store = self.spill.store("recover-run").map_err(|e| e.0)?;
        self.entries.sort_unstable_by_key(|e| (e.pos, e.off));
        let mut writer =
            RunWriter::new(store, self.spill, &mut self.ext_store, self.cfg.format, self.cfg.chunk_bytes, self.cfg.external_threshold());
        match self.cfg.format {
            SortFormat::Words(_) => {
                for &e in &self.entries {
                    let mut at = e.off;
                    let (log, fp) = get_xor_ref(&self.buf, &mut at, &self.base, &mut self.scratch);
                    writer.push_words(e.pos, log, fp, &self.scratch)?;
                }
            }
            SortFormat::Bytes => {
                for &e in &self.entries {
                    match get_bytes_rec(&self.buf, e.off)? {
                        (log, fp, BufBytes::Inline(range)) => writer.push_bytes_inline(e.pos, log, fp, &self.buf[range])?,
                        (log, fp, BufBytes::External(bref)) => writer.push_bytes_external(e.pos, log, fp, &bref)?,
                    }
                }
            }
        }
        let writer_bytes = writer.bytes();
        let maybe_run = writer.finish(0)?;
        self.update_charge(writer_bytes);
        if let Some(run) = maybe_run {
            self.runs.push(run);
        }
        self.buf.clear();
        self.entries.clear();
        self.has_base = false;
        // Release oversized capacity so a temporary spike never stays pinned.
        if self.buf.capacity() + self.entries.capacity() * std::mem::size_of::<Entry>() > self.cfg.run_limit.saturating_mul(2) {
            self.buf = Vec::new();
            self.entries = Vec::new();
        }
        self.update_charge(0);
        if compact {
            self.compact_tiers()?;
        }
        Ok(())
    }

    /// Size-tiered compaction: whenever a tier accumulates enough runs to fill
    /// a budget-bounded merge pass (`target >= 2`), merge that tier into a
    /// single run at `tier + 1`. Keeps the number of live runs (and open spill
    /// files) `O(log N)` and total bytes rewritten `O(N log N)` (never quadratic).
    fn compact_tiers(&mut self) -> Result<(), String> {
        let mut tier = 0u8;
        loop {
            let indices: Vec<usize> = self.runs.iter().enumerate().filter(|(_, r)| r.tier == tier).map(|(i, _)| i).collect();
            if indices.len() < 2 {
                break;
            }
            let avail = self.cfg.merge_budget.saturating_sub(self.writer_reserve());
            let max_reader = indices.iter().map(|&i| self.runs[i].reader_bytes(self.cfg.format)).max().unwrap_or(1).max(1);
            let target = (avail / max_reader).clamp(2, MAX_MERGE_WAY);
            if indices.len() < target {
                break;
            }
            // Drop run-building buffers before opening merge readers so peak
            // RAM never holds both simultaneously.
            self.buf = Vec::new();
            self.entries = Vec::new();
            let chosen = &indices[..target];
            let mut batch = Vec::with_capacity(chosen.len());
            for &idx in chosen.iter().rev() {
                batch.push(self.runs.swap_remove(idx));
            }
            self.merge_to_run(batch, tier.saturating_add(1))?;
            tier = tier.saturating_add(1);
        }
        Ok(())
    }

    fn merge_to_run(&mut self, batch: Vec<Run>, tier: u8) -> Result<(), String> {
        let store = self.spill.store("recover-run").map_err(|e| e.0)?;
        let base = self.run_buf_bytes() + self.runs_meta_bytes();
        let mut writer =
            RunWriter::new(store, self.spill, &mut self.ext_store, self.cfg.format, self.cfg.chunk_bytes, self.cfg.external_threshold());
        merge_runs(self.cfg.format, batch, self.gauge, &self.charge, base, |rec, extra| {
            match rec {
                MergeRecord::Words { pos, log, fp, words } => writer.push_words(pos, log, fp, words)?,
                MergeRecord::BytesInline { pos, log, fp, payload } => writer.push_bytes_inline(pos, log, fp, payload)?,
                MergeRecord::BytesExternal { pos, log, fp, bref } => writer.push_bytes_external(pos, log, fp, &bref)?,
            }
            self.charge.set(self.gauge, base + extra + writer.bytes());
            Ok(())
        })?;
        if let Some(merged) = writer.finish(tier)? {
            self.runs.push(merged);
        }
        self.update_charge(0);
        Ok(())
    }

    /// Active record bytes buffered in the current run (excluding fixed
    /// `base`/`scratch` word buffers so wide states still pack full runs).
    fn data_bytes(&self) -> usize {
        self.buf.len() + self.entries.len() * std::mem::size_of::<Entry>()
    }

    fn run_buf_bytes(&self) -> usize {
        self.buf.capacity()
            + self.entries.capacity() * std::mem::size_of::<Entry>()
            + (self.base.words.capacity() + self.scratch.capacity()) * 8
    }

    fn runs_meta_bytes(&self) -> usize {
        self.runs.capacity() * std::mem::size_of::<Run>() + self.runs.iter().map(|r| r.tree.root.sums_bytes()).sum::<usize>()
    }

    fn update_charge(&self, extra: usize) {
        self.charge.set(self.gauge, self.run_buf_bytes() + self.runs_meta_bytes() + extra);
    }
}

fn ensure_ext_store(spill: &Spill, slot: &mut Option<Arc<BlockStore>>) -> Result<Arc<BlockStore>, String> {
    match slot {
        Some(s) => Ok(s.clone()),
        None => {
            let s = spill.store("recover-ext").map_err(|e| e.0)?;
            *slot = Some(s.clone());
            Ok(s)
        }
    }
}

/// Select how many leading runs of `runs` (`>= 2`, `<= MAX_MERGE_WAY`) can be
/// merged together within `budget - writer_reserve`, using each run's actual
/// [`Run::reader_bytes`].
fn pick_batch_len(runs: &[Run], format: SortFormat, budget: usize, writer_reserve: usize) -> usize {
    let avail = budget.saturating_sub(writer_reserve);
    let mut used = 0usize;
    let mut k = 0usize;
    for r in runs.iter().take(MAX_MERGE_WAY) {
        let need = r.reader_bytes(format);
        if k >= 2 && used.saturating_add(need) > avail {
            break;
        }
        used = used.saturating_add(need);
        k += 1;
    }
    k.min(runs.len())
}

/// Append a self-contained delta-XOR record relative to `base` (without
/// mutating `base`).
fn put_xor_ref(out: &mut Vec<u8>, base: &XorPrev, log: u64, fp: u64, words: &[u64]) {
    debug_assert_eq!(words.len(), base.words.len());
    put_uvar(out, zigzag(log.wrapping_sub(base.log) as i64));
    out.extend_from_slice(&fp.to_le_bytes());
    let bmap_at = out.len();
    let bmap_len = words.len().div_ceil(8);
    out.resize(bmap_at + bmap_len, 0);
    for (g, (ws, bs)) in words.chunks(8).zip(base.words.chunks(8)).enumerate() {
        let mut bits = 0u8;
        for (i, (w, b)) in ws.iter().zip(bs.iter()).enumerate() {
            bits |= ((w != b) as u8) << i;
        }
        out[bmap_at + g] = bits;
        while bits != 0 {
            let i = bits.trailing_zeros() as usize;
            bits &= bits - 1;
            put_uvar(out, ws[i] ^ bs[i]);
        }
    }
}

/// Decode a delta-XOR record written by `put_xor_ref` into `words`, returning
/// `(log, fp)`.
fn get_xor_ref(b: &[u8], pos: &mut usize, base: &XorPrev, words: &mut [u64]) -> (u64, u64) {
    debug_assert_eq!(words.len(), base.words.len());
    words.copy_from_slice(&base.words);
    let log = base.log.wrapping_add(unzigzag(get_uvar_trusted(b, pos)) as u64);
    let fp = u64::from_le_bytes(b[*pos..*pos + 8].try_into().expect("8 bytes"));
    *pos += 8;
    let bmap = *pos;
    let bmap_len = words.len().div_ceil(8);
    *pos += bmap_len;
    for byte in 0..bmap_len {
        let mut bits = b[bmap + byte];
        while bits != 0 {
            let i = byte * 8 + bits.trailing_zeros() as usize;
            bits &= bits - 1;
            words[i] ^= get_uvar_trusted(b, pos);
        }
    }
    (log, fp)
}

enum BufBytes {
    Inline(Range<usize>),
    External(BlockRef),
}

/// Decode a `SortFormat::Bytes` record at `off` in `b`.
fn get_bytes_rec(b: &[u8], mut at: usize) -> Result<(u64, u64, BufBytes), String> {
    let tag = b[at];
    at += 1;
    let fp = u64::from_le_bytes(b[at..at + 8].try_into().expect("8 bytes"));
    at += 8;
    let log = get_uvar_trusted(b, &mut at);
    match tag {
        TAG_INLINE => {
            let len = get_uvar_trusted(b, &mut at) as usize;
            Ok((log, fp, BufBytes::Inline(at..at + len)))
        }
        TAG_EXTERNAL => {
            let bref = BlockRef::decode(b, &mut at).map_err(|e| e.0)?;
            Ok((log, fp, BufBytes::External(bref)))
        }
        _ => Err("corrupt sort buffer record".into()),
    }
}

/// Writes one sorted run as a [`BlockTree`] of page-aligned self-contained
/// chunks into its own `BlockStore`.
struct RunWriter<'a> {
    store: Arc<BlockStore>,
    spill: &'a Spill,
    ext_store: &'a mut Option<Arc<BlockStore>>,
    format: SortFormat,
    chunk_bytes: usize,
    external_threshold: usize,
    buf: Vec<u8>,
    count: u64,
    prev_pos: u64,
    prev: XorPrev,
    tree: BlockTreeWriter,
    total: u64,
}

impl<'a> RunWriter<'a> {
    fn new(
        store: Arc<BlockStore>,
        spill: &'a Spill,
        ext_store: &'a mut Option<Arc<BlockStore>>,
        format: SortFormat,
        chunk_bytes: usize,
        external_threshold: usize,
    ) -> RunWriter<'a> {
        let chunk_bytes = align_chunk(chunk_bytes);
        let tree = BlockTreeWriter::new(store.clone(), chunk_bytes);
        RunWriter {
            store,
            spill,
            ext_store,
            format,
            chunk_bytes,
            external_threshold,
            buf: Vec::new(),
            count: 0,
            prev_pos: 0,
            prev: XorPrev::new(format.num_words()),
            tree,
            total: 0,
        }
    }

    fn bytes(&self) -> usize {
        self.buf.capacity() + self.prev.words.capacity() * 8 + self.tree.bytes()
    }

    fn begin_block(&mut self) {
        self.buf.clear();
        self.buf.extend_from_slice(&0u64.to_le_bytes());
        self.count = 0;
        self.prev_pos = 0;
        self.prev.reset();
    }

    fn flush_block(&mut self) -> Result<(), String> {
        if self.count == 0 {
            return Ok(());
        }
        self.buf[..8].copy_from_slice(&self.count.to_le_bytes());
        pad_to_page(&mut self.buf);
        let b = self.store.append(&self.buf).map_err(|e| e.0)?;
        self.tree.push_data_block(b)?;
        self.begin_block();
        Ok(())
    }

    fn begin_record(&mut self, pos: u64, est: usize) -> Result<(), String> {
        if self.count > 0 && self.buf.len().saturating_add(est) > self.chunk_bytes {
            self.flush_block()?;
        }
        if self.buf.is_empty() {
            self.begin_block();
        }
        debug_assert!(pos >= self.prev_pos, "run records must be sorted by position");
        put_uvar(&mut self.buf, pos - self.prev_pos);
        self.prev_pos = pos;
        self.count += 1;
        self.total += 1;
        Ok(())
    }

    fn push_words(&mut self, pos: u64, log: u64, fp: u64, words: &[u64]) -> Result<(), String> {
        debug_assert_eq!(self.format, SortFormat::Words(words.len()));
        let est = if self.count > 0 {
            debug_assert!(pos >= self.prev_pos, "run records must be sorted by position");
            xor_record_len(&self.prev, pos - self.prev_pos, log, words)
        } else {
            0
        };
        self.begin_record(pos, est)?;
        codec::put_xor(&mut self.buf, &mut self.prev, log, fp, words);
        Ok(())
    }

    fn push_bytes_inline(&mut self, pos: u64, log: u64, fp: u64, payload: &[u8]) -> Result<(), String> {
        debug_assert_eq!(self.format, SortFormat::Bytes);
        if payload.len() > self.external_threshold {
            let ext = ensure_ext_store(self.spill, self.ext_store)?;
            let bref = write_external(&ext, payload)?;
            return self.push_bytes_external(pos, log, fp, &bref);
        }
        let pos_delta = if self.count > 0 {
            debug_assert!(pos >= self.prev_pos, "run records must be sorted by position");
            pos - self.prev_pos
        } else {
            pos
        };
        let est = uvar_len(pos_delta) + 1 + 8 + uvar_len(log) + uvar_len(payload.len() as u64) + payload.len();
        self.begin_record(pos, est)?;
        self.buf.push(TAG_INLINE);
        self.buf.extend_from_slice(&fp.to_le_bytes());
        put_uvar(&mut self.buf, log);
        put_uvar(&mut self.buf, payload.len() as u64);
        self.buf.extend_from_slice(payload);
        Ok(())
    }

    fn push_bytes_external(&mut self, pos: u64, log: u64, fp: u64, bref: &BlockRef) -> Result<(), String> {
        debug_assert_eq!(self.format, SortFormat::Bytes);
        let pos_delta = if self.count > 0 {
            debug_assert!(pos >= self.prev_pos, "run records must be sorted by position");
            pos - self.prev_pos
        } else {
            pos
        };
        let est = uvar_len(pos_delta) + 1 + 8 + uvar_len(log) + bref.encoded_len();
        self.begin_record(pos, est)?;
        self.buf.push(TAG_EXTERNAL);
        self.buf.extend_from_slice(&fp.to_le_bytes());
        put_uvar(&mut self.buf, log);
        bref.encode(&mut self.buf);
        Ok(())
    }

    fn finish(mut self, tier: u8) -> Result<Option<Run>, String> {
        self.flush_block()?;
        let store = self.store;
        Ok(self.tree.finish()?.map(|tree| Run { store, tree, count: self.total, tier }))
    }
}

enum ReaderPayload {
    Inline(Range<usize>),
    External(Option<BlockRef>),
}

enum MergeRecord<'a> {
    Words { pos: u64, log: u64, fp: u64, words: &'a [u64] },
    BytesInline { pos: u64, log: u64, fp: u64, payload: &'a [u8] },
    BytesExternal { pos: u64, log: u64, fp: u64, bref: BlockRef },
}

/// Streams sorted records from one persisted [`Run`], reclaiming each
/// page-aligned data and index block as soon as it is consumed and unlinking
/// the run's `BlockStore` file on drop.
struct RunReader {
    store: Arc<BlockStore>,
    format: SortFormat,
    tree: BlockTreeReader,
    current_block: Option<BlockRef>,
    chunk: Vec<u8>,
    at: usize,
    left: u64,
    pos: u64,
    log: u64,
    fp: u64,
    prev: XorPrev,
    payload: ReaderPayload,
}

impl RunReader {
    fn open(format: SortFormat, run: Run) -> Result<Option<RunReader>, String> {
        let tree = BlockTreeReader::open(&run.store, run.tree)?;
        let mut r = RunReader {
            store: run.store,
            format,
            tree,
            current_block: None,
            chunk: Vec::new(),
            at: 0,
            left: 0,
            pos: 0,
            log: 0,
            fp: 0,
            prev: XorPrev::new(format.num_words()),
            payload: ReaderPayload::Inline(0..0),
        };
        if r.advance()? {
            Ok(Some(r))
        } else {
            Ok(None)
        }
    }

    fn bytes(&self) -> usize {
        let ext = match &self.payload {
            ReaderPayload::External(Some(b)) => b.sums_bytes(),
            _ => 0,
        };
        self.chunk.capacity()
            + self.prev.words.capacity() * 8
            + self.tree.bytes()
            + self.current_block.as_ref().map_or(0, BlockRef::sums_bytes)
            + ext
    }

    fn take_current(&mut self) -> MergeRecord<'_> {
        match self.format {
            SortFormat::Words(_) => MergeRecord::Words { pos: self.pos, log: self.log, fp: self.fp, words: &self.prev.words },
            SortFormat::Bytes => match &mut self.payload {
                ReaderPayload::Inline(range) => {
                    MergeRecord::BytesInline { pos: self.pos, log: self.log, fp: self.fp, payload: &self.chunk[range.clone()] }
                }
                ReaderPayload::External(slot) => MergeRecord::BytesExternal {
                    pos: self.pos,
                    log: self.log,
                    fp: self.fp,
                    bref: slot.take().expect("external payload taken once"),
                },
            },
        }
    }

    fn advance(&mut self) -> Result<bool, String> {
        while self.left == 0 {
            if let Some(done) = self.current_block.take() {
                self.store.delete_reclaimable(done);
            }
            let Some(next) = self.tree.next_block(&self.store)? else {
                self.chunk = Vec::new();
                self.prev.words = Vec::new();
                self.payload = ReaderPayload::Inline(0..0);
                return Ok(false);
            };
            self.chunk = self.store.read(&next).map_err(|e| e.0)?;
            self.current_block = Some(next);
            if self.chunk.len() < 8 {
                return Err("corrupt sort spill block".into());
            }
            self.left = u64::from_le_bytes(self.chunk[..8].try_into().expect("8 bytes"));
            self.at = 8;
            self.pos = 0;
            self.prev.reset();
        }
        self.left -= 1;
        self.pos += get_uvar_trusted(&self.chunk, &mut self.at);
        match self.format {
            SortFormat::Words(_) => {
                self.fp = codec::get_xor(&self.chunk, &mut self.at, &mut self.prev);
                self.log = self.prev.log;
            }
            SortFormat::Bytes => {
                let tag = self.chunk[self.at];
                self.at += 1;
                self.fp = u64::from_le_bytes(self.chunk[self.at..self.at + 8].try_into().expect("8 bytes"));
                self.at += 8;
                self.log = get_uvar_trusted(&self.chunk, &mut self.at);
                match tag {
                    TAG_INLINE => {
                        let len = get_uvar_trusted(&self.chunk, &mut self.at) as usize;
                        self.payload = ReaderPayload::Inline(self.at..self.at + len);
                        self.at += len;
                    }
                    TAG_EXTERNAL => {
                        let bref = BlockRef::decode(&self.chunk, &mut self.at).map_err(|e| e.0)?;
                        self.payload = ReaderPayload::External(Some(bref));
                    }
                    _ => return Err("corrupt sort spill record".into()),
                }
            }
        }
        Ok(true)
    }
}

/// Min-heap item ordered by ascending `(pos, run)`.
#[derive(Clone, Copy, Eq, PartialEq)]
struct HeapItem {
    pos: u64,
    run: usize,
}

impl Ord for HeapItem {
    fn cmp(&self, other: &Self) -> Ordering {
        other.pos.cmp(&self.pos).then_with(|| other.run.cmp(&self.run))
    }
}

impl PartialOrd for HeapItem {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// K-way merge `batch` of sorted runs, invoking `on_record(record, merge_bytes)`
/// for each record in ascending `pos` order. Exhausted run readers are dropped
/// immediately so their underlying spill files are unlinked without waiting for
/// the rest of the batch.
fn merge_runs(
    format: SortFormat,
    batch: Vec<Run>,
    gauge: &Gauge,
    charge: &Part,
    base_bytes: usize,
    mut on_record: impl FnMut(MergeRecord<'_>, usize) -> Result<(), String>,
) -> Result<(), String> {
    let mut readers: Vec<Option<RunReader>> = Vec::with_capacity(batch.len());
    let mut heap: BinaryHeap<HeapItem> = BinaryHeap::with_capacity(batch.len());
    let mut readers_bytes = 0usize;
    for run in batch {
        if let Some(r) = RunReader::open(format, run)? {
            let idx = readers.len();
            readers_bytes += r.bytes();
            heap.push(HeapItem { pos: r.pos, run: idx });
            readers.push(Some(r));
        }
    }
    let heap_bytes = heap.capacity() * std::mem::size_of::<HeapItem>();
    charge.set(gauge, base_bytes + readers_bytes + heap_bytes);

    while let Some(HeapItem { run, .. }) = heap.pop() {
        let reader = readers[run].as_mut().expect("live reader in heap");
        let before = reader.bytes();
        let extra = readers_bytes + heap_bytes;
        on_record(reader.take_current(), extra)?;
        let more = reader.advance()?;
        let after = if more {
            let pos = reader.pos;
            let bytes = reader.bytes();
            heap.push(HeapItem { pos, run });
            bytes
        } else {
            // Drop the exhausted reader immediately so its run file is unlinked.
            readers[run] = None;
            0
        };
        if after != before {
            readers_bytes = readers_bytes.saturating_sub(before).saturating_add(after);
            charge.set(gauge, base_bytes + readers_bytes + heap_bytes);
        }
    }
    charge.set(gauge, base_bytes);
    Ok(())
}

#[cfg(test)]
mod tests;
