//! A block store: one spill file of blocks (see the module doc of `io`).

use std::collections::BTreeMap;
use std::fs::{File, OpenOptions};
use std::os::unix::fs::FileExt;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;

use parking_lot::Mutex;

use super::{disk_reserve, disk_space, fs_info, Ctx, DirLease, IoError};

/// The unit of checksums: every page of a block has one.
pub const PAGE: usize = 4096;

/// Where a block is: its offset and length in its store, and the checksums
/// of its pages.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BlockRef {
    pub off: u64,
    pub len: usize,
    sums: Box<[u32]>,
}

impl BlockRef {
    /// Heap bytes held by this reference's page checksums.
    pub(crate) fn sums_bytes(&self) -> usize {
        self.sums.len() * std::mem::size_of::<u32>()
    }

    /// Serialized byte length of this block reference (`encode`).
    pub(crate) fn encoded_len(&self) -> usize {
        20 + self.sums.len() * 4
    }

    /// Serialize this block reference (offset, length, page checksums) into `out`.
    pub(crate) fn encode(&self, out: &mut Vec<u8>) {
        out.extend_from_slice(&self.off.to_le_bytes());
        out.extend_from_slice(&(self.len as u64).to_le_bytes());
        out.extend_from_slice(&(self.sums.len() as u32).to_le_bytes());
        for &s in &self.sums {
            out.extend_from_slice(&s.to_le_bytes());
        }
    }

    /// Deserialize a block reference written by `encode` from `b` at `*at`.
    pub(crate) fn decode(b: &[u8], at: &mut usize) -> Result<BlockRef, IoError> {
        let bad = || IoError("corrupt spill block reference".into());
        if at.checked_add(20).is_none_or(|end| end > b.len()) {
            return Err(bad());
        }
        let off = u64::from_le_bytes(b[*at..*at + 8].try_into().expect("8 bytes"));
        let len = usize::try_from(u64::from_le_bytes(b[*at + 8..*at + 16].try_into().expect("8 bytes"))).map_err(|_| bad())?;
        let n = u32::from_le_bytes(b[*at + 16..*at + 20].try_into().expect("4 bytes")) as usize;
        *at += 20;
        if n != len.div_ceil(PAGE) {
            return Err(bad());
        }
        let end = n.checked_mul(4).and_then(|k| at.checked_add(k)).ok_or_else(bad)?;
        if end > b.len() {
            return Err(bad());
        }
        let mut sums = Vec::with_capacity(n);
        for chunk in b[*at..end].chunks_exact(4) {
            sums.push(u32::from_le_bytes(chunk.try_into().expect("4 bytes")));
        }
        *at = end;
        Ok(BlockRef { off, len, sums: sums.into_boxed_slice() })
    }
}

/// Upper bound on coalesced dead byte intervals tracked per store for
/// boundary/tail hole-punch reclamation. Page-aligned stores keep 0 entries
/// and sequential queue draining keeps O(workers) entries.
const MAX_DEAD_INTERVALS: usize = 64;

/// Per-file physical allocation state guarded by a short mutex around offset
/// reservation and dead-range coalescing (never held during disk I/O).
struct AllocState {
    /// The end of the file: blocks are appended at offsets reserved here.
    end: u64,
    /// Allocation-unit-rounded high-water byte offset charged for this file.
    data_charged: u64,
    /// Allocation-unit-rounded data bytes still live (not yet punched).
    live_data: u64,
    /// Worst-case extent-tree metadata bytes for `data_charged` assuming
    /// fragmentation down to `unit` (`extent_meta_bytes(data_charged / unit, unit)`).
    /// Monotonic until the file is truncated back to 0 when empty or unlinked,
    /// covering extent-tree blocks retained by filesystems like ext4 after hole punching.
    worst_meta: u64,
    /// Number of non-empty blocks currently live (including in-flight writes).
    live_blocks: usize,
    /// Number of appends currently executing `write_all_at` on this file.
    in_flight_writes: usize,
    /// Set if an OS write failed partially; prevents `set_len(0)` from
    /// releasing the failed write's physical reservation before unlink.
    has_failed_write: bool,
    /// Set once `punch_hole` fails on this store so dead intervals never
    /// accumulate on filesystems without hole-punch support.
    punch_disabled: bool,
    /// Coalesced dead byte intervals `[lo, hi)` awaiting whole-unit reclamation.
    dead: BTreeMap<u64, u64>,
}

/// Conservative upper bound on filesystem extent-tree metadata bytes for a
/// file with at most `extents` disjoint extents:
/// - `0..=4` extents fit inline in an ext4 inode (`0` extra blocks);
/// - `5..=64` extents need at most 1 extent-tree leaf block (`1 * unit`);
/// - above `64` extents, reserve 1 leaf block per 64 extents plus 2 tree
///   index/root blocks (ext4 fits 340 extents/block, covering ext4/XFS/APFS).
fn extent_meta_bytes(extents: u64, unit: u64) -> u64 {
    if extents <= 4 {
        0
    } else if extents <= 64 {
        unit
    } else {
        (extents.div_ceil(64) + 2) * unit
    }
}

/// Insert `[lo, hi)` into `dead`, coalescing with any adjacent or overlapping
/// dead intervals, and return the resulting merged `(lo, hi)`.
fn coalesce_dead(dead: &mut BTreeMap<u64, u64>, mut lo: u64, mut hi: u64) -> (u64, u64) {
    if let Some((&prev_lo, &prev_hi)) = dead.range(..=lo).next_back() {
        if prev_hi >= lo {
            dead.remove(&prev_lo);
            lo = prev_lo;
            hi = hi.max(prev_hi);
        }
    }
    while let Some((&next_lo, &next_hi)) = dead.range(lo..=hi).next() {
        dead.remove(&next_lo);
        hi = hi.max(next_hi);
    }
    (lo, hi)
}

/// Record a partial-unit dead interval while keeping `dead.len()` strictly
/// bounded. Dropping the oldest partial fragment only forgoes reclaiming that
/// fragment until unlink and stays conservative for `-maxdisk`.
fn insert_dead_bounded(dead: &mut BTreeMap<u64, u64>, lo: u64, hi: u64) {
    if dead.len() >= MAX_DEAD_INTERVALS {
        dead.pop_first();
    }
    dead.insert(lo, hi);
}

/// A file of blocks.
pub struct BlockStore {
    file: File,
    path: PathBuf,
    /// Filesystem allocation unit (at least `PAGE`).
    unit: u64,
    /// Serializes offset + dead-interval / physical allocation bookkeeping.
    alloc: Mutex<AllocState>,
    /// The logical bytes of the blocks not deleted.
    live: AtomicU64,
    /// Conservative physical bytes (`live_data + worst_meta`) charged to
    /// `ctx.phys_used` for this store.
    phys_live: AtomicU64,
    ctx: Arc<Ctx>,
    /// (Keeps the directory while the store exists; gives it back when
    /// the store is the last user.)
    _dir: DirLease,
}

impl BlockStore {
    #[cfg(test)]
    pub(crate) fn dead_intervals_len(&self) -> usize {
        self.alloc.lock().dead.len()
    }

    /// A new file at `path`; with `nocache`, written and read past the page
    /// cache where the system allows (macOS).
    pub(super) fn create(path: PathBuf, dir: DirLease, ctx: Arc<Ctx>, nocache: bool) -> Result<BlockStore, IoError> {
        let file = OpenOptions::new()
            .read(true)
            .write(true)
            .create_new(true)
            .open(&path)
            .map_err(|e| IoError(format!("cannot create the spill file {}: {e}", path.display())))?;
        #[cfg(target_os = "macos")]
        if nocache {
            use std::os::fd::AsRawFd;
            // (Best effort: only a hint to the page cache.)
            // SAFETY: a valid descriptor.
            unsafe { libc::fcntl(file.as_raw_fd(), libc::F_NOCACHE, 1) };
        }
        #[cfg(not(target_os = "macos"))]
        let _ = nocache;
        let unit = fs_info(&path).map_or(PAGE as u64, |(_, _, fr)| fr.max(PAGE as u64));
        Ok(BlockStore {
            file,
            path,
            unit,
            alloc: Mutex::new(AllocState {
                end: 0,
                data_charged: 0,
                live_data: 0,
                worst_meta: 0,
                live_blocks: 0,
                in_flight_writes: 0,
                has_failed_write: false,
                punch_disabled: false,
                dead: BTreeMap::new(),
            }),
            live: AtomicU64::new(0),
            phys_live: AtomicU64::new(0),
            ctx,
            _dir: dir,
        })
    }

    pub fn path(&self) -> &std::path::Path {
        &self.path
    }

    /// The bytes of the blocks not deleted.
    pub fn bytes(&self) -> u64 {
        self.live.load(Ordering::Relaxed)
    }

    fn maxdisk_err(&self, max: u64) -> IoError {
        IoError(format!(
            "the spill files would take more than -maxdisk {} (in {}); give tlx more disk (-maxdisk) or memory (-maxmem)",
            size(max),
            self.dir_display()
        ))
    }

    /// Check `fail_after` and filesystem free space (`disk_space`), adding
    /// `len` to `ctx.written` and `ctx.used`. Returns `used_after`.
    fn reserve_logical_and_space(&self, len: u64, need_space: u64) -> Result<u64, IoError> {
        let ctx = &*self.ctx;
        let cfg = &ctx.cfg;
        let written = ctx.written.fetch_add(len, Ordering::Relaxed) + len;
        if cfg.fail_after.is_some_and(|n| written > n) {
            return Err(IoError(format!(
                "cannot write the spill file {}: injected write error (SpillConfig::fail_after)",
                self.path.display()
            )));
        }
        let used = ctx.used.fetch_add(len, Ordering::Relaxed) + len;
        if let Some((avail, total)) = disk_space(&self.path) {
            let keep = disk_reserve(total);
            if avail < need_space + keep {
                ctx.used.fetch_sub(len, Ordering::Relaxed);
                return Err(IoError(format!(
                    "no space left for the spill files in {}: {} free, {} to write, tlx keeps {} free; free some disk space, give another directory (-metadir) or more memory (-maxmem)",
                    self.dir_display(),
                    size(avail),
                    size(need_space),
                    size(keep)
                )));
            }
        }
        Ok(used)
    }

    /// Reserve file offset and conservative physical/logical quota before
    /// issuing any write, rejecting before touching disk if worst-case
    /// allocation-unit data + extent-tree metadata would exceed `-maxdisk`.
    fn reserve_append(&self, len: u64) -> Result<(u64, u64), IoError> {
        let mut st = self.alloc.lock();
        let (new_end, new_data, new_live_data, new_worst_meta, delta_phys) = if len == 0 {
            (st.end, st.data_charged, st.live_data, st.worst_meta, 0)
        } else {
            let new_end = st.end + len;
            let new_data = new_end.next_multiple_of(self.unit);
            let delta_data = new_data.saturating_sub(st.data_charged);
            let new_live_data = st.live_data + delta_data;
            let new_worst_meta = extent_meta_bytes(new_data / self.unit, self.unit);
            let delta_meta = new_worst_meta.saturating_sub(st.worst_meta);
            (new_end, new_data, new_live_data, new_worst_meta, delta_data + delta_meta)
        };
        let ctx = &*self.ctx;
        if delta_phys > 0 {
            let phys_after = ctx.phys_used.fetch_add(delta_phys, Ordering::Relaxed) + delta_phys;
            if let Some(max) = ctx.cfg.maxdisk {
                if phys_after > max {
                    ctx.phys_used.fetch_sub(delta_phys, Ordering::Relaxed);
                    return Err(self.maxdisk_err(max));
                }
            }
        }
        let need_space = delta_phys.max(len);
        let used_after = match self.reserve_logical_and_space(len, need_space) {
            Ok(u) => u,
            Err(e) => {
                if delta_phys > 0 {
                    ctx.phys_used.fetch_sub(delta_phys, Ordering::Relaxed);
                }
                return Err(e);
            }
        };
        let off = st.end;
        st.end = new_end;
        st.data_charged = new_data;
        st.live_data = new_live_data;
        st.worst_meta = new_worst_meta;
        if len > 0 {
            st.live_blocks += 1;
            st.in_flight_writes += 1;
        }
        if delta_phys > 0 {
            self.phys_live.fetch_add(delta_phys, Ordering::Relaxed);
        }
        Ok((off, used_after))
    }

    /// Execute an append of `len` bytes using `write_fn(file, off)`.
    ///
    /// Quota is enforced conservatively before issuing `write_fn` so `-maxdisk`
    /// is never exceeded even transiently; a failed OS write (`write_all_at`
    /// error such as `EFBIG`/`ENOSPC`) retains its physical reservation until
    /// `Drop` unlinks the file.
    fn append_with(&self, len: u64, write_fn: impl FnOnce(&File, u64) -> std::io::Result<()>) -> Result<u64, IoError> {
        let (off, used_after) = self.reserve_append(len)?;
        let res = write_fn(&self.file, off);
        if len > 0 {
            let mut st = self.alloc.lock();
            st.in_flight_writes -= 1;
            if res.is_err() {
                st.live_blocks = st.live_blocks.saturating_sub(1);
                st.has_failed_write = true;
            }
        }
        match res {
            Ok(()) => {
                self.live.fetch_add(len, Ordering::Relaxed);
                self.ctx.peak.fetch_max(used_after, Ordering::Relaxed);
                self.ctx.blocks.fetch_add(1, Ordering::Relaxed);
                Ok(off)
            }
            Err(e) => {
                // Keep the physical reservation in `self.phys_live` /
                // `ctx.phys_used` until unlink because a partial OS write
                // (e.g. EFBIG/ENOSPC) may have allocated blocks on disk.
                self.ctx.used.fetch_sub(len, Ordering::Relaxed);
                Err(IoError(format!("cannot write the spill file {}: {e}", self.path.display())))
            }
        }
    }

    fn dir_display(&self) -> String {
        self.path.parent().map_or_else(String::new, |p| p.display().to_string())
    }

    /// Append a block; where it is. Several threads may append at once.
    pub fn append(&self, data: &[u8]) -> Result<BlockRef, IoError> {
        let len = data.len() as u64;
        match self.append_with(len, |file, off| file.write_all_at(data, off)) {
            Ok(off) => Ok(BlockRef { off, len: data.len(), sums: data.chunks(PAGE).map(checksum).collect() }),
            Err(e) => Err(self.ctx.fail(e)),
        }
    }

    /// Append `header` followed by `body`, zero-padded to a whole multiple of
    /// `PAGE`, without copying `body` on the heap. Only use on a store whose
    /// blocks are all page-sized so offsets stay page-aligned for full
    /// hole-punch reclamation (`delete_reclaimable`).
    pub(crate) fn append_paged(&self, header: &[u8], body: &[u8]) -> Result<BlockRef, IoError> {
        self.append_paged_hook(header, body, || {})
    }

    pub(super) fn append_paged_hook(&self, header: &[u8], body: &[u8], after_header: impl FnOnce()) -> Result<BlockRef, IoError> {
        let raw_len = header.len() + body.len();
        let padded_len = raw_len.max(1).next_multiple_of(PAGE);
        let pad_len = padded_len - raw_len;
        let plen = padded_len as u64;
        let r = self.append_with(plen, |file, off| {
            debug_assert_eq!(off % PAGE as u64, 0, "append_paged requires a page-aligned store");
            if !header.is_empty() {
                file.write_all_at(header, off)?;
                after_header();
            }
            if !body.is_empty() {
                file.write_all_at(body, off + header.len() as u64)?;
            }
            if pad_len > 0 {
                let zeros = [0u8; PAGE];
                file.write_all_at(&zeros[..pad_len], off + raw_len as u64)?;
            }
            Ok(())
        });
        match r {
            Ok(off) => {
                let pages = padded_len / PAGE;
                let mut sums = Vec::with_capacity(pages);
                let mut page = [0u8; PAGE];
                let hlen = header.len();
                for p in 0..pages {
                    let start = p * PAGE;
                    let end = start + PAGE;
                    if start >= hlen && end <= raw_len {
                        sums.push(checksum(&body[start - hlen..end - hlen]));
                    } else {
                        page.fill(0);
                        if start < hlen {
                            let h_end = end.min(hlen);
                            let n = h_end - start;
                            page[..n].copy_from_slice(&header[start..h_end]);
                        }
                        let b_start = start.max(hlen);
                        let b_end = end.min(raw_len);
                        if b_start < b_end {
                            let dst = b_start - start;
                            let src = b_start - hlen;
                            page[dst..dst + (b_end - b_start)].copy_from_slice(&body[src..src + (b_end - b_start)]);
                        }
                        sums.push(checksum(&page));
                    }
                }
                Ok(BlockRef { off, len: padded_len, sums: sums.into_boxed_slice() })
            }
            Err(e) => Err(self.ctx.fail(e)),
        }
    }

    /// Read block `r` whole (checksums verified).
    pub fn read(&self, r: &BlockRef) -> Result<Vec<u8>, IoError> {
        let mut out = vec![0u8; r.len];
        self.read_into(r, &mut out)?;
        Ok(out)
    }

    /// Read block `r` into `out` (of its length; checksums verified).
    pub fn read_into(&self, r: &BlockRef, out: &mut [u8]) -> Result<(), IoError> {
        assert_eq!(out.len(), r.len, "read_into: wrong length");
        self.read_pages(r, 0, out)?;
        for (i, page) in out.chunks(PAGE).enumerate() {
            self.verify(r, i, page)?;
        }
        Ok(())
    }

    /// Read `out.len()` bytes at offset `at` of block `r` (reading and
    /// verifying the pages they are in).
    pub fn read_range(&self, r: &BlockRef, at: usize, out: &mut [u8]) -> Result<(), IoError> {
        if out.is_empty() {
            return Ok(());
        }
        assert!(at + out.len() <= r.len, "read_range: out of the block");
        let first = at / PAGE;
        let last = (at + out.len() - 1) / PAGE;
        let start = first * PAGE;
        let end = ((last + 1) * PAGE).min(r.len);
        if start == at && end == at + out.len() {
            // (Whole pages: read in place.)
            self.read_pages(r, start, out)?;
            for (k, page) in out.chunks(PAGE).enumerate() {
                self.verify(r, first + k, page)?;
            }
            return Ok(());
        }
        let mut buf = vec![0u8; end - start];
        self.read_pages(r, start, &mut buf)?;
        for (k, page) in buf.chunks(PAGE).enumerate() {
            self.verify(r, first + k, page)?;
        }
        out.copy_from_slice(&buf[at - start..at - start + out.len()]);
        Ok(())
    }

    fn read_pages(&self, r: &BlockRef, start: usize, buf: &mut [u8]) -> Result<(), IoError> {
        self.file
            .read_exact_at(buf, r.off + start as u64)
            .map_err(|e| self.ctx.fail(IoError(format!("cannot read the spill file {}: {e}", self.path.display()))))?;
        self.ctx.read.fetch_add(buf.len() as u64, Ordering::Relaxed);
        Ok(())
    }

    /// A read-only mapping of the bytes `lo..hi` of the file (all written:
    /// a range of blocks), if the system gives one. Reading it may stop the
    /// process (SIGBUS) where reading the file would fail.
    pub fn map(&self, lo: u64, hi: u64) -> Option<Mapping> {
        use std::os::fd::AsRawFd;
        if hi <= lo {
            return None;
        }
        // SAFETY: no preconditions.
        let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) }.max(1) as u64;
        let base = lo / page * page;
        let len = usize::try_from(hi - base).ok()?;
        // SAFETY: a valid descriptor; a new mapping (no address given) of
        // bytes the file has.
        let ptr =
            unsafe { libc::mmap(std::ptr::null_mut(), len, libc::PROT_READ, libc::MAP_SHARED, self.file.as_raw_fd(), base as libc::off_t) };
        if ptr == libc::MAP_FAILED {
            return None;
        }
        // Lookups read single pages at random: a page fault that is not
        // in the page cache should read that page, not the system's
        // read-around window (on Linux 128 KiB: 32 times the bytes read,
        // and the pages read around evict others; best effort).
        // SAFETY: advice on the mapping just made.
        unsafe { libc::madvise(ptr, len, libc::MADV_RANDOM) };
        Some(Mapping { ptr: ptr.cast(), len, base })
    }

    /// Verify page `page` of block `r` (read as `data`) against its
    /// checksum.
    pub fn verify_page(&self, r: &BlockRef, page: usize, data: &[u8]) -> Result<(), IoError> {
        self.verify(r, page, data)
    }

    fn verify(&self, r: &BlockRef, page: usize, data: &[u8]) -> Result<(), IoError> {
        if checksum(data) == r.sums[page] {
            return Ok(());
        }
        Err(self.ctx.fail(IoError(format!(
            "the spill file {} is corrupt: checksum mismatch at offset {}",
            self.path.display(),
            r.off + (page * PAGE) as u64
        ))))
    }

    /// Coalesce deleted block `r` with any adjacent dead fragments and punch
    /// every whole allocation unit that is now completely dead (including the
    /// final tail page when no write is in flight, advancing `end` to the page
    /// boundary so subsequent appends remain cleanly aligned). Returns the
    /// number of bytes actually punched (`0` when hole punching is unavailable
    /// or no full unit became dead).
    fn punch_and_credit_phys(&self, r: &BlockRef) -> u64 {
        if r.len == 0 {
            return 0;
        }
        let mut st = self.alloc.lock();
        st.live_blocks = st.live_blocks.saturating_sub(1);
        if self.ctx.cfg.no_punch {
            return 0;
        }
        // When every committed block has been deleted and no write is in flight
        // (nor failed partially), truncate the file to 0 directly. This reclaims
        // all data pages—including any whose partial-page dead intervals were
        // evicted from `dead`—and releases extent-tree metadata blocks.
        if st.live_blocks == 0 && st.in_flight_writes == 0 && !st.has_failed_write && st.end > 0 {
            match self.file.set_len(0) {
                Ok(()) => {
                    let data_sub = st.live_data;
                    let phys_sub = st.live_data + st.worst_meta;
                    st.end = 0;
                    st.data_charged = 0;
                    st.live_data = 0;
                    st.worst_meta = 0;
                    st.dead.clear();
                    drop(st);
                    if phys_sub > 0 {
                        self.phys_live.fetch_sub(phys_sub, Ordering::Relaxed);
                        self.ctx.phys_used.fetch_sub(phys_sub, Ordering::Relaxed);
                    }
                    return data_sub;
                }
                Err(e) => {
                    // Truncation failed: keep the physical reservation and
                    // surface the cleanup I/O error.
                    drop(st);
                    let _ = self.ctx.fail(IoError(format!("cannot truncate the spill file {}: {e}", self.path.display())));
                    return 0;
                }
            }
        }
        if st.punch_disabled {
            return 0;
        }
        let (lo, mut hi) = coalesce_dead(&mut st.dead, r.off, r.off + r.len as u64);
        let punch_start = lo.next_multiple_of(self.unit);
        let at_tail = hi == st.end && st.in_flight_writes == 0;
        let punch_end = if at_tail { st.data_charged } else { hi / self.unit * self.unit };
        if punch_end <= punch_start {
            insert_dead_bounded(&mut st.dead, lo, hi);
            return 0;
        }
        if !punch_hole(&self.file, punch_start, punch_end - punch_start) {
            // Hole punching is unsupported or failing on this store; switch to
            // unlink-only reclamation and drop dead-interval bookkeeping.
            st.punch_disabled = true;
            st.dead.clear();
            return 0;
        }
        if at_tail {
            st.end = st.data_charged;
            hi = st.data_charged;
        }
        if lo < punch_start {
            insert_dead_bounded(&mut st.dead, lo, punch_start);
        }
        if punch_end < hi {
            insert_dead_bounded(&mut st.dead, punch_end, hi);
        }
        let reclaimed = punch_end - punch_start;
        let new_live_data = st.live_data.saturating_sub(reclaimed);
        let data_sub = st.live_data - new_live_data;
        st.live_data = new_live_data;
        drop(st);
        if data_sub > 0 {
            self.phys_live.fetch_sub(data_sub, Ordering::Relaxed);
            self.ctx.phys_used.fetch_sub(data_sub, Ordering::Relaxed);
        }
        reclaimed
    }

    /// Delete block `r`: its space is given back (the whole pages covered by
    /// `r` and any adjacent deleted fragments, where the file system supports it).
    pub fn delete(&self, r: BlockRef) {
        self.live.fetch_sub(r.len as u64, Ordering::Relaxed);
        self.ctx.used.fetch_sub(r.len as u64, Ordering::Relaxed);
        let _ = self.punch_and_credit_phys(&r);
    }

    /// Delete block `r`, crediting logical and `-maxdisk` accounting only for
    /// whole allocation units actually reclaimed via `punch_hole`.
    pub(crate) fn delete_reclaimable(&self, r: BlockRef) {
        let punched = self.punch_and_credit_phys(&r);
        if punched > 0 {
            let sub = punched.min(self.live.load(Ordering::Relaxed));
            self.live.fetch_sub(sub, Ordering::Relaxed);
            self.ctx.used.fetch_sub(sub, Ordering::Relaxed);
        }
    }
}

impl Drop for BlockStore {
    fn drop(&mut self) {
        self.ctx.used.fetch_sub(self.live.load(Ordering::Relaxed), Ordering::Relaxed);
        let phys = self.phys_live.load(Ordering::Relaxed);
        match std::fs::remove_file(&self.path) {
            Ok(()) => {
                self.ctx.phys_used.fetch_sub(phys, Ordering::Relaxed);
            }
            Err(e) if e.kind() == std::io::ErrorKind::NotFound => {
                self.ctx.phys_used.fetch_sub(phys, Ordering::Relaxed);
            }
            Err(e) => {
                // File still occupies disk space: keep its physical reservation
                // and surface the cleanup I/O error.
                let _ = self.ctx.fail(IoError(format!("cannot remove the spill file {}: {e}", self.path.display())));
            }
        }
    }
}

/// A read-only mapping of a part of a block store (`BlockStore::map`).
pub struct Mapping {
    ptr: *const u8,
    len: usize,
    /// The file offset of its first byte.
    base: u64,
}

// SAFETY: read-only memory, unmapped only when dropped.
unsafe impl Send for Mapping {}
// SAFETY: as above.
unsafe impl Sync for Mapping {}

impl Mapping {
    /// The `len` bytes at offset `off` of the file (within the mapping).
    #[inline]
    pub fn bytes(&self, off: u64, len: usize) -> &[u8] {
        let at = (off - self.base) as usize;
        assert!(off >= self.base && at + len <= self.len, "Mapping::bytes: out of the mapping");
        // SAFETY: within the mapping, which lives as long as `self`.
        unsafe { std::slice::from_raw_parts(self.ptr.add(at), len) }
    }
}

impl Drop for Mapping {
    fn drop(&mut self) {
        // SAFETY: the mapping made by `BlockStore::map`; no borrow of it
        // outlives `self`.
        unsafe { libc::munmap(self.ptr as *mut libc::c_void, self.len) };
    }
}

/// `b` bytes for a message: in MiB, or KiB below 1 MiB.
fn size(b: u64) -> String {
    if b >= 1 << 20 {
        format!("{} MiB", b >> 20)
    } else {
        format!("{} KiB", b >> 10)
    }
}

/// Give back the space of `len` bytes at `off` (page aligned), keeping the
/// file's size; returns whether the operating system reported success.
fn punch_hole(file: &File, off: u64, len: u64) -> bool {
    use std::os::fd::AsRawFd;
    #[cfg(target_os = "macos")]
    {
        let arg = libc::fpunchhole_t { fp_flags: 0, reserved: 0, fp_offset: off as libc::off_t, fp_length: len as libc::off_t };
        // SAFETY: a valid descriptor and argument.
        unsafe { libc::fcntl(file.as_raw_fd(), libc::F_PUNCHHOLE, &arg) == 0 }
    }
    #[cfg(target_os = "linux")]
    {
        // SAFETY: a valid descriptor.
        unsafe {
            libc::fallocate(
                file.as_raw_fd(),
                libc::FALLOC_FL_PUNCH_HOLE | libc::FALLOC_FL_KEEP_SIZE,
                off as libc::off_t,
                len as libc::off_t,
            ) == 0
        }
    }
    #[cfg(not(any(target_os = "macos", target_os = "linux")))]
    {
        let _ = (file, off, len);
        false
    }
}

/// The checksum of a page: a multiplicative hash of its words, folded to
/// 32 bits (detects torn, misplaced and corrupted pages; not
/// cryptographic).
pub(crate) fn checksum(data: &[u8]) -> u32 {
    const K: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut h = 0x243F_6A88_85A3_08D3u64 ^ data.len() as u64;
    let mut words = data.chunks_exact(8);
    for w in &mut words {
        h = (h ^ u64::from_le_bytes(w.try_into().unwrap())).wrapping_mul(K).rotate_left(29);
    }
    let rest = words.remainder();
    if !rest.is_empty() {
        let mut w = [0u8; 8];
        w[..rest.len()].copy_from_slice(rest);
        h = (h ^ u64::from_le_bytes(w)).wrapping_mul(K).rotate_left(29);
    }
    h ^= h >> 32;
    h.wrapping_mul(K) as u32 ^ (h >> 17) as u32
}
