//! The disk layer of a search (docs/scale.md §10): a spill directory,
//! block stores in it, background IO threads, checksums and disk-space
//! checks.
//!
//! Nothing touches the disk until a component spills: the directory is
//! created on the first `Spill::store`, and removed when the last store in
//! it is dropped (so a run that never spills creates nothing, and one that
//! did leaves nothing behind when it ends normally). A run ended by
//! SIGINT/SIGTERM removes it too (`cleanup_dir_on_signal`).
//!
//! - `BlockStore`: one file of blocks, appended (`append`, positional
//!   writes at reserved offsets: several threads may append) and read back
//!   by position (`read`, `read_range`); every 4 KiB page of a block has a
//!   checksum, verified when it is read; `delete` gives a block's space
//!   back.
//! - `Spill::write_async`: a block handed to the writer thread (bounded
//!   queue: a producer faster than the disk waits); the block stays
//!   readable in memory until written (`Pending`), and stays in memory if
//!   the write fails.
//! - `Spill::prefetch`: a block read by the reader thread ahead of its use.
//! - `SpillVec`: an append-only sequence of fixed-size blocks whose blocks
//!   can be spilled and are read back transparently (trace logs, liveness
//!   edge logs).
//!
//! `SpillVec`'s blocks and the queue's segments (`queue::Seg`) go through
//! the same states (in memory → handed to the writer → on disk → read
//! back; a failed write keeps the data in memory), and share the step out
//! of the writer (`Pending::settle`). They stay two machines on purpose: a
//! `SpillVec` has one owner, a store per sequence, a partial last block
//! (`unseal`) and borrowed iteration; a segment is shared between threads
//! (a lock per segment), is never spilled while a reader holds it, is read
//! ahead (`Fetch`), moves its memory charge between queues and deletes its
//! own disk copy.
//!
//! Errors: the first IO error (a failed write, a full disk, `-maxdisk`
//! exceeded, a checksum mismatch) is recorded (`Spill::error`); the search
//! stops with it (`Outcome::Io`). Before each append the free space of the
//! file system is checked: tlx keeps the smaller of 1 GiB and 2% of the
//! file system free.
//!
//! Spill files are scratch data: they are not synced (`durable` is for
//! checkpoints). On macOS they are
//! written with `F_NOCACHE`, so that the page cache does not keep what the
//! search just gave back; except the fingerprint set's runs
//! (`Spill::store_cached`), read at random a page at a time.

pub mod durable;
mod spillvec;
mod store;

use std::any::Any;
use std::fs::File;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::mpsc::{sync_channel, SyncSender};
use std::sync::{Arc, OnceLock, Weak};

use parking_lot::Mutex;
use tlx_base::par::OneShot;

/// The spill directories alive in this process, so that a signal-handling
/// thread can remove them when a run is ended by SIGINT/SIGTERM (a normal
/// end removes them when their `Dir` is dropped; see
/// `cleanup_dir_on_signal`). The registry only records what the drop would
/// remove, so the signal path mirrors the normal one exactly.
static ACTIVE_DIRS: Mutex<Vec<ActiveDir>> = Mutex::new(Vec::new());
static NEXT_DIR: AtomicU64 = AtomicU64::new(1);

/// A live spill directory (see `ACTIVE_DIRS`); the fields are the ones the
/// normal drop of a `Dir` uses.
struct ActiveDir {
    /// The registration (`Dir::id`).
    id: u64,
    path: PathBuf,
    /// Created by tlx (removed with its contents; else only its files).
    created: bool,
    /// The default `states` directory it is in (removed if empty).
    parent: Option<PathBuf>,
}

/// Remove this process's spill directory as the normal end of a run does:
/// the directory tlx created (with its contents), or, in one the user gave
/// that already existed, the files tlx created in it (the lock file and the
/// spill files), and the `states` directory it was created in if that is
/// empty. For a signal-handling thread that ends the process right after
/// (no spill directory can be created any more); a no-op if none is alive.
///
/// A directory holding a committed checkpoint (`CHECKPOINT_DIR`) is kept
/// with it, so that the run can be recovered (`-recover`): only the spill
/// files, the lock file and an unfinished checkpoint are removed. Returns
/// the directories kept.
pub fn cleanup_dir_on_signal() -> Vec<PathBuf> {
    // (No checkpoint is committed from now on: the process exits. Bounded
    // as below: a commit only renames directories.)
    if let Some(commit) = durable::COMMIT.try_lock_for(std::time::Duration::from_secs(2)) {
        std::mem::forget(commit);
    }
    // (The lock is kept until the process exits: no spill directory is
    // created after this, see `Dir::create`.)
    // (Bounded: the holder only creates or drops a directory, but the
    // process must end whatever happens.)
    let Some(mut guard) = ACTIVE_DIRS.try_lock_for(std::time::Duration::from_secs(2)) else { return Vec::new() };
    let dirs = std::mem::take(&mut *guard);
    std::mem::forget(guard);
    let mut kept = Vec::new();
    for d in dirs {
        // (Interrupted between the renames of a commit: rolled forward.)
        let ckpt = checkpoint_dirs(&d.path);
        if ckpt.roll_forward() {
            remove_own_files(&d.path);
            ckpt.remove_uncommitted();
            kept.push(d.path);
            continue;
        }
        if d.created {
            // (The search's threads may still be writing into it: a file
            // created during the removal makes it fail; retry.)
            for _ in 0..50 {
                if std::fs::remove_dir_all(&d.path).is_ok() || !d.path.exists() {
                    break;
                }
                std::thread::sleep(std::time::Duration::from_millis(2));
            }
        } else {
            // (A directory the user gave and that already existed: remove
            // the lock file and the spill files, as the normal end does
            // through each `BlockStore`'s drop, never the directory.)
            remove_own_files(&d.path);
        }
        if let Some(p) = &d.parent {
            let _ = std::fs::remove_dir(p);
        }
    }
    kept
}

/// Remove the lock file and the spill files of directory `path`.
fn remove_own_files(path: &Path) {
    let _ = std::fs::remove_file(path.join("LOCK"));
    remove_spill_files(path);
}

/// Remove the spill files of directory `path`.
fn remove_spill_files(path: &Path) {
    if let Ok(rd) = std::fs::read_dir(path) {
        for e in rd.flatten() {
            if e.path().extension().is_some_and(|x| x == "spill") {
                let _ = std::fs::remove_file(e.path());
            }
        }
    }
}

/// The subdirectory of a spill directory (a metadir) that holds the last
/// committed checkpoint (`crate::explore::checkpoint`); it is written as
/// `checkpoint.tmp`, and the previous one is `checkpoint.old` while the
/// next one is committed.
pub const CHECKPOINT_DIR: &str = "checkpoint";

/// The checkpoint directories of metadir `metadir`.
pub fn checkpoint_dirs(metadir: &Path) -> DirCommit {
    DirCommit::new(metadir, CHECKPOINT_DIR)
}

pub use self::durable::DirCommit;
pub use self::spillvec::SpillVec;
pub use self::store::{BlockRef, BlockStore, Mapping, PAGE};

/// When the search may use the disk (`-spill`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum SpillMode {
    /// Only under memory pressure (docs/scale.md §2.3).
    #[default]
    Auto,
    /// Never: the stages of memory pressure that would spill are only
    /// recorded.
    Off,
    /// From the start, everything that can be spilled (testing).
    Always,
}

impl SpillMode {
    pub fn parse(v: &str) -> Option<SpillMode> {
        match v.trim().to_ascii_lowercase().as_str() {
            "auto" => Some(SpillMode::Auto),
            "off" | "no" | "never" => Some(SpillMode::Off),
            "always" => Some(SpillMode::Always),
            _ => None,
        }
    }
}

/// Where and how much a search may spill.
#[derive(Clone, Debug, Default)]
pub struct SpillConfig {
    pub mode: SpillMode,
    /// The directory of the spill files (`-metadir`), used as given
    /// (created if needed). None: a new directory `states/<time>` in
    /// `base` (as TLC's default metadir), or in the system's temporary
    /// directory if there is no `base` or it cannot be created there.
    pub dir: Option<PathBuf>,
    /// The directory of the specification (see `dir`).
    pub base: Option<PathBuf>,
    /// The most bytes the spill files may hold (`-maxdisk`).
    pub maxdisk: Option<u64>,
    /// Testing: writes fail once this many bytes
    /// were written.
    pub fail_after: Option<u64>,
    /// Testing: delay each asynchronous write by this duration.
    pub write_delay: Option<std::time::Duration>,
    /// Testing: disable hole punching in `BlockStore::delete_reclaimable` so
    /// tests can exercise the unlink-on-drop fallback path.
    pub no_punch: bool,
    /// `dir` was made by an earlier run of tlx (`-recover`): at the end it
    /// is removed if nothing else is left in it (and the `states`
    /// directory it is in, if empty), as if this run had made it.
    pub reused: bool,
}

/// An IO error of the disk layer, with its message (the file, the
/// operation and the cause).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IoError(pub String);

impl std::fmt::Display for IoError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}

/// What the stores and the IO threads share: the configuration, the first
/// error and the counters.
pub(crate) struct Ctx {
    pub(crate) cfg: SpillConfig,
    error: Mutex<Option<IoError>>,
    failed: AtomicBool,
    /// Bytes written and read.
    pub(crate) written: AtomicU64,
    pub(crate) read: AtomicU64,
    /// Bytes the spill files hold (logical), and the most they held.
    pub(crate) used: AtomicU64,
    pub(crate) peak: AtomicU64,
    /// Conservative upper bound on physical disk bytes allocated across all
    /// live spill files: allocation-unit-rounded live data plus worst-case
    /// extent-tree metadata (including partial failed writes retained until
    /// unlink). Checked before issuing any write so `-maxdisk` is never
    /// exceeded even transiently.
    pub(crate) phys_used: AtomicU64,
    /// Blocks written.
    pub(crate) blocks: AtomicU64,
}

impl Ctx {
    /// Record `e` (if it is the first error) and return it.
    pub(crate) fn fail(&self, e: IoError) -> IoError {
        let mut first = self.error.lock();
        if first.is_none() {
            *first = Some(e.clone());
        }
        self.failed.store(true, Ordering::Release);
        e
    }
}

/// The spill directory of a run and its IO threads (cheap to clone; see the
/// module doc).
#[derive(Clone)]
pub struct Spill(Arc<Inner>);

struct Inner {
    ctx: Arc<Ctx>,
    /// The directory, while a store in it exists.
    dir: Mutex<Weak<Dir>>,
    /// Numbers the files.
    files: AtomicU64,
    threads: OnceLock<Threads>,
}

/// The IO threads (started with the first asynchronous request).
struct Threads {
    write: SyncSender<WriteRequest>,
    read: SyncSender<ReadRequest>,
}

enum ReadRequest {
    Block(Arc<BlockStore>, BlockRef, Arc<Prefetch>),
    Barrier(SyncSender<()>),
}

enum WriteRequest {
    Block(Arc<BlockStore>, Arc<Pending>),
    Barrier(SyncSender<()>),
}

/// Blocks queued for the writer (each up to a segment, 1 MiB by default):
/// a producer faster than the disk waits.
const WRITE_QUEUE: usize = 16;
const READ_QUEUE: usize = 16;

impl Default for Spill {
    fn default() -> Spill {
        Spill::new(SpillConfig::default())
    }
}

impl std::fmt::Debug for Spill {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("Spill").field(&self.0.ctx.cfg).finish()
    }
}

impl Spill {
    pub fn new(cfg: SpillConfig) -> Spill {
        let ctx = Ctx {
            cfg,
            error: Mutex::new(None),
            failed: AtomicBool::new(false),
            written: AtomicU64::new(0),
            read: AtomicU64::new(0),
            used: AtomicU64::new(0),
            peak: AtomicU64::new(0),
            phys_used: AtomicU64::new(0),
            blocks: AtomicU64::new(0),
        };
        Spill(Arc::new(Inner { ctx: Arc::new(ctx), dir: Mutex::new(Weak::new()), files: AtomicU64::new(0), threads: OnceLock::new() }))
    }

    pub fn mode(&self) -> SpillMode {
        self.0.ctx.cfg.mode
    }

    /// Whether the search may spill.
    pub fn enabled(&self) -> bool {
        self.mode() != SpillMode::Off
    }

    /// The first IO error, if any.
    pub fn error(&self) -> Option<IoError> {
        if !self.failed() {
            return None;
        }
        self.0.ctx.error.lock().clone()
    }

    /// Whether an IO error occurred (cheap).
    #[inline]
    pub fn failed(&self) -> bool {
        self.0.ctx.failed.load(Ordering::Acquire)
    }

    /// Bytes written, read, held at most by the spill files, and the
    /// blocks written so far.
    pub fn counters(&self) -> SpillCounters {
        let c = &self.0.ctx;
        SpillCounters {
            written: c.written.load(Ordering::Relaxed),
            read: c.read.load(Ordering::Relaxed),
            peak: c.peak.load(Ordering::Relaxed),
            used: c.used.load(Ordering::Relaxed),
            blocks: c.blocks.load(Ordering::Relaxed),
        }
    }

    /// The spill directory, if it exists now.
    pub fn dir(&self) -> Option<PathBuf> {
        self.0.dir.lock().upgrade().map(|d| d.path.clone())
    }

    /// A new store (a file named after `name`) in the spill directory,
    /// created if needed.
    pub fn store(&self, name: &str) -> Result<Arc<BlockStore>, IoError> {
        self.new_store(name, true)
    }

    /// The spill directory, created if needed, kept (with its lock) while
    /// the hold lives: for checkpoints, which are not block stores.
    pub fn hold_dir(&self) -> Result<DirHold, IoError> {
        self.dir_arc().map(DirHold)
    }

    fn dir_arc(&self) -> Result<Arc<Dir>, IoError> {
        let mut d = self.0.dir.lock();
        match d.upgrade() {
            Some(dir) => Ok(dir),
            None => {
                let dir = Arc::new(Dir::create(&self.0.ctx.cfg).map_err(|e| self.0.ctx.fail(e))?);
                *d = Arc::downgrade(&dir);
                Ok(dir)
            }
        }
    }

    /// `store`, for a file read at random and often (the fingerprint set's
    /// runs): read through the page cache, also on macOS (where the other
    /// spill files bypass it, see the module doc).
    pub fn store_cached(&self, name: &str) -> Result<Arc<BlockStore>, IoError> {
        self.new_store(name, false)
    }

    fn new_store(&self, name: &str, nocache: bool) -> Result<Arc<BlockStore>, IoError> {
        let dir = self.dir_arc()?;
        let n = self.0.files.fetch_add(1, Ordering::Relaxed);
        let path = dir.path.join(format!("{name}-{n}.spill"));
        BlockStore::create(path, dir, self.0.ctx.clone(), nocache).map(Arc::new).map_err(|e| self.0.ctx.fail(e))
    }

    fn threads(&self) -> &Threads {
        self.0.threads.get_or_init(|| {
            let (wtx, wrx) = sync_channel::<WriteRequest>(WRITE_QUEUE);
            let (rtx, rrx) = sync_channel::<ReadRequest>(READ_QUEUE);
            let write_delay = self.0.ctx.cfg.write_delay;
            // (The threads end when the `Spill` is dropped: its senders
            // close the channels.)
            tlx_base::stack::spawn(std::thread::Builder::new().name("tlx-spill-writer".into()), move || {
                while let Ok(request) = wrx.recv() {
                    match request {
                        WriteRequest::Block(store, p) => {
                            if let Some(delay) = write_delay {
                                std::thread::sleep(delay);
                            }
                            p.write(&store);
                        }
                        WriteRequest::Barrier(done) => {
                            let _ = done.send(());
                        }
                    }
                }
            })
            .expect("failed to spawn the spill writer thread");
            tlx_base::stack::spawn(std::thread::Builder::new().name("tlx-spill-reader".into()), move || {
                while let Ok(request) = rrx.recv() {
                    match request {
                        ReadRequest::Block(store, r, p) => {
                            let res = store.read(&r);
                            p.state.set(res);
                        }
                        ReadRequest::Barrier(done) => {
                            let _ = done.send(());
                        }
                    }
                }
            })
            .expect("failed to spawn the spill reader thread");
            Threads { write: wtx, read: rtx }
        })
    }

    /// Write `data` to `store` on the writer thread (waits while its queue
    /// is full). The data stay readable until written (`Pending::with_data`),
    /// and are kept if the write fails.
    pub fn write_async(&self, store: &Arc<BlockStore>, data: Box<dyn Bytes>) -> Arc<Pending> {
        let p = Arc::new(Pending { state: OneShot::with_state(Some(data)) });
        if self.threads().write.send(WriteRequest::Block(store.clone(), p.clone())).is_err() {
            // (Cannot happen: the writer lives as long as `self`.)
            p.write(store);
        }
        p
    }

    /// Wait until all writes queued before this call have finished and the
    /// writer has released their store references. Does not start IO threads
    /// if no asynchronous requests were made. Errors remain in `error()`.
    pub fn wait_for_writes(&self) {
        let Some(threads) = self.0.threads.get() else { return };
        let (done, wait) = sync_channel(0);
        threads.write.send(WriteRequest::Barrier(done)).expect("spill writer stopped");
        wait.recv().expect("spill writer stopped before its barrier");
    }

    /// Wait until reads queued before this call have finished and the reader
    /// has released their store references. A ready prefetch publishes its
    /// bytes before that request's store is dropped; cleanup checks need this
    /// barrier, not only `Prefetch::wait`. Does not start an idle reader.
    pub fn wait_for_reads(&self) {
        let Some(threads) = self.0.threads.get() else { return };
        let (done, wait) = sync_channel(0);
        threads.read.send(ReadRequest::Barrier(done)).expect("spill reader stopped");
        wait.recv().expect("spill reader stopped before its barrier");
    }

    /// Read block `r` of `store` on the reader thread.
    pub fn prefetch(&self, store: &Arc<BlockStore>, r: &BlockRef) -> Arc<Prefetch> {
        let p = Arc::new(Prefetch { state: OneShot::new() });
        if self.threads().read.send(ReadRequest::Block(store.clone(), r.clone(), p.clone())).is_err() {
            p.state.set(store.read(r));
        }
        p
    }
}

/// The counters of a spill directory.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct SpillCounters {
    pub written: u64,
    pub read: u64,
    /// The most bytes the spill files held, and what they hold now.
    pub peak: u64,
    pub used: u64,
    pub blocks: u64,
}

/// Data a block is written from: a vector of plain values.
pub trait Bytes: Send + Sync + 'static {
    fn bytes(&self) -> &[u8];
    fn into_any(self: Box<Self>) -> Box<dyn Any + Send>;
}

/// Values whose bytes can be written and read back as they are: no padding,
/// no pointers, any bit pattern valid.
///
/// # Safety
/// Implement only for such types.
pub unsafe trait Plain: Copy + Default + Send + Sync + 'static {}

// SAFETY: integers and arrays of them.
unsafe impl Plain for u8 {}
unsafe impl Plain for u32 {}
unsafe impl Plain for u64 {}
unsafe impl Plain for [u64; 2] {}

/// The bytes of `v`.
pub fn as_bytes<T: Plain>(v: &[T]) -> &[u8] {
    // SAFETY: `T: Plain` has no padding; the slice covers `v` exactly.
    unsafe { std::slice::from_raw_parts(v.as_ptr().cast::<u8>(), std::mem::size_of_val(v)) }
}

/// The bytes of `v`, writable.
pub fn as_bytes_mut<T: Plain>(v: &mut [T]) -> &mut [u8] {
    // SAFETY: as `as_bytes`, and every bit pattern is a valid `T`.
    unsafe { std::slice::from_raw_parts_mut(v.as_mut_ptr().cast::<u8>(), std::mem::size_of_val(v)) }
}

impl<T: Plain> Bytes for Vec<T> {
    fn bytes(&self) -> &[u8] {
        as_bytes(self)
    }
    fn into_any(self: Box<Self>) -> Box<dyn Any + Send> {
        self
    }
}

/// A block handed to the writer thread.
pub struct Pending {
    state: OneShot<Result<BlockRef, IoError>, Option<Box<dyn Bytes>>>,
}

impl Pending {
    /// Write the data (on the writer thread). The lock is held meanwhile:
    /// a reader of the data waits for the write.
    fn write(&self, store: &BlockStore) {
        self.state.complete(|data| {
            let result = store.append(data.as_ref().expect("pending block without data").bytes());
            if result.is_ok() {
                *data = None;
            }
            result
        });
    }

    /// The result of the write, if done (without waiting, also not for the
    /// lock).
    pub fn try_done(&self) -> Option<Result<BlockRef, IoError>> {
        self.state.try_get()
    }

    /// Wait for the write; its result.
    pub fn wait(&self) -> Result<BlockRef, IoError> {
        self.state.wait()
    }

    /// Wait for the write: where the block is, or (the write failed) its
    /// data back, as the `D` they were handed over as, with the error.
    /// The step of the spill state machine shared by `SpillVec`'s blocks
    /// and the queue's segments (`Pending` → on disk, or back in memory).
    pub fn settle<D: 'static>(&self) -> Result<BlockRef, (D, IoError)> {
        self.state.wait().map_err(|e| (self.take_back(), e))
    }

    /// `settle`, if the write is done (without waiting).
    pub fn try_settle<D: 'static>(&self) -> Option<Result<BlockRef, (D, IoError)>> {
        Some(self.try_done()?.map_err(|e| (self.take_back(), e)))
    }

    /// The data of a block whose write failed, as the `D` they were handed
    /// over as.
    pub(crate) fn take_back<D: 'static>(&self) -> D {
        let d = self.take_data().expect("failed write without its data");
        *d.into_any().downcast::<D>().expect("block data of another type")
    }

    /// Call `f` with the data if they are still in memory (waits for a
    /// write in progress).
    pub fn with_data<R>(&self, f: impl FnOnce(&[u8]) -> R) -> Option<R> {
        self.state.access(|data| data.as_ref().map(|data| f(data.bytes())))
    }

    /// The data back, after a failed write (or before it started).
    fn take_data(&self) -> Option<Box<dyn Bytes>> {
        self.state.access(Option::take)
    }
}

/// A block being read by the reader thread.
pub struct Prefetch {
    state: OneShot<Result<Vec<u8>, IoError>>,
}

impl Prefetch {
    /// Wait for the block; its bytes.
    pub fn wait(&self) -> Result<Vec<u8>, IoError> {
        self.state.take()
    }

    /// Whether the block was read (or failed).
    pub fn ready(&self) -> bool {
        self.state.ready()
    }
}

/// A hold on the spill directory (`Spill::hold_dir`).
pub struct DirHold(Arc<Dir>);

impl DirHold {
    pub fn path(&self) -> &Path {
        &self.0.path
    }

    /// Keep the directory (what is left in it) when it is released: a
    /// checkpoint to recover from.
    pub fn keep(&self) {
        self.0.keep.store(true, Ordering::SeqCst);
    }
}

/// The spill directory, while a store in it exists. Removed when dropped
/// (if tlx created it; else only the lock file).
pub(crate) struct Dir {
    pub(crate) path: PathBuf,
    /// Created by tlx (removed with its contents when dropped).
    created: bool,
    /// The default `states` directory it is in (removed if empty).
    parent: Option<PathBuf>,
    /// The lock file, locked (`File::try_lock`, an `flock`) while the
    /// directory is used.
    _lock: File,
    /// The registration in `ACTIVE_DIRS` (removed when dropped).
    id: u64,
    /// Made by an earlier run (`SpillConfig::reused`): removed if empty.
    reused: bool,
    /// Kept when dropped (`DirHold::keep`): only the lock file goes.
    keep: AtomicBool,
}

impl Dir {
    fn create(cfg: &SpillConfig) -> Result<Dir, IoError> {
        // (The registry stays locked from creating the directory until it is
        // registered: a signal in between would otherwise leave it behind;
        // the signal path waits for the lock and keeps it until the exit.)
        let mut reg = ACTIVE_DIRS.lock();
        let reg = &mut *reg;
        if let Some(d) = &cfg.dir {
            let created = !d.exists();
            std::fs::create_dir_all(d).map_err(|e| IoError(format!("cannot create the spill directory {}: {e}", d.display())))?;
            // (The metadir of an earlier run goes when empty, with the
            // `states` directory it is in if that is empty too.)
            let reused = cfg.reused && !created;
            let parent =
                if reused { d.parent().filter(|p| p.file_name().is_some_and(|n| n == "states")).map(Path::to_path_buf) } else { None };
            let mut dir = Dir::lock(reg, d.clone(), created, parent)?;
            dir.reused = reused;
            return Ok(dir);
        }
        let stamp = timestamp();
        if let Some(base) = &cfg.base {
            let states = base.join("states");
            if std::fs::create_dir_all(&states).is_ok() {
                if let Some(path) = fresh_dir(&states, &stamp) {
                    return Dir::lock(reg, path, true, Some(states));
                }
            }
        }
        let tmp = std::env::temp_dir().join("tlx-states");
        let _ = std::fs::create_dir_all(&tmp);
        match fresh_dir(&tmp, &format!("{stamp}-{}", std::process::id())) {
            Some(path) => Dir::lock(reg, path, true, None),
            None => Err(IoError(format!("cannot create a spill directory in {} (give one with -metadir)", tmp.display()))),
        }
    }

    fn lock(reg: &mut Vec<ActiveDir>, path: PathBuf, created: bool, parent: Option<PathBuf>) -> Result<Dir, IoError> {
        let lp = path.join("LOCK");
        let f = File::create(&lp).map_err(|e| IoError(format!("cannot create {}: {e}", lp.display())))?;
        // (std's `try_lock` is `flock(LOCK_EX | LOCK_NB)` on Unix.)
        if f.try_lock().is_err() {
            return Err(IoError(format!("the spill directory {} is in use by another process", path.display())));
        }
        if !created {
            // (Spill files of a run that was killed: nobody uses them now.)
            remove_spill_files(&path);
        }
        Ok(Dir {
            id: register(reg, &path, created, parent.as_deref()),
            path,
            created,
            parent,
            _lock: f,
            reused: false,
            keep: AtomicBool::new(false),
        })
    }
}

/// Register a live spill directory for the signal path; returns its id.
fn register(reg: &mut Vec<ActiveDir>, path: &Path, created: bool, parent: Option<&Path>) -> u64 {
    let id = NEXT_DIR.fetch_add(1, Ordering::Relaxed);
    reg.push(ActiveDir { id, path: path.to_path_buf(), created, parent: parent.map(Path::to_path_buf) });
    id
}

impl Drop for Dir {
    fn drop(&mut self) {
        if self.keep.load(Ordering::SeqCst) {
            let _ = std::fs::remove_file(self.path.join("LOCK"));
            ACTIVE_DIRS.lock().retain(|d| d.id != self.id);
            return;
        }
        if self.created {
            let _ = std::fs::remove_dir_all(&self.path);
        } else {
            let _ = std::fs::remove_file(self.path.join("LOCK"));
            if self.reused {
                let _ = std::fs::remove_dir(&self.path);
            }
        }
        if let Some(p) = &self.parent {
            // (Only if empty: another run may use it, or the user keep
            // other things there.)
            let _ = std::fs::remove_dir(p);
        }
        // (After the removal: a signal in between only removes it again.)
        ACTIVE_DIRS.lock().retain(|d| d.id != self.id);
    }
}

/// A new directory `<stamp>` in `parent` (`<stamp>.1`, ... if taken).
fn fresh_dir(parent: &Path, stamp: &str) -> Option<PathBuf> {
    for k in 0..1000 {
        let p = if k == 0 { parent.join(stamp) } else { parent.join(format!("{stamp}.{k}")) };
        match std::fs::create_dir(&p) {
            Ok(()) => return Some(p),
            Err(e) if e.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(_) => return None,
        }
    }
    None
}

/// The local time as TLC names its metadirs: `yy-MM-dd-HH-mm-ss`.
fn timestamp() -> String {
    let t = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_secs()) as libc::time_t;
    // SAFETY: an all-zero `tm` is valid; `localtime_r` only writes the `tm`
    // it is given.
    let tm = unsafe {
        let mut tm: libc::tm = std::mem::zeroed();
        if libc::localtime_r(&t, &mut tm).is_null() {
            return format!("{t}");
        }
        tm
    };
    format!("{:02}-{:02}-{:02}-{:02}-{:02}-{:02}", tm.tm_year % 100, tm.tm_mon + 1, tm.tm_mday, tm.tm_hour, tm.tm_min, tm.tm_sec)
}

/// Create (or truncate) `path` with `bytes`, creating its parent
/// directories first (Java's `getParentFile().mkdirs()` then a
/// `FileWriter`: a failure to create them shows as the write's error).
/// Not synced.
pub fn write_creating_parents(path: &Path, bytes: &[u8]) -> std::io::Result<()> {
    if let Some(dir) = path.parent().filter(|d| !d.as_os_str().is_empty()) {
        let _ = std::fs::create_dir_all(dir);
    }
    std::fs::write(path, bytes)
}

/// Append `bytes` to `path` (created if missing). Not synced.
pub fn append_to(path: &Path, bytes: &[u8]) -> std::io::Result<()> {
    use std::io::Write as _;
    std::fs::OpenOptions::new().create(true).append(true).open(path).and_then(|mut f| f.write_all(bytes))
}

/// The space available to this process on the file system of `path`, the size
/// of that file system, and its fundamental allocation unit (bytes).
pub(crate) fn fs_info(path: &Path) -> Option<(u64, u64, u64)> {
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStrExt;
        let c = std::ffi::CString::new(path.as_os_str().as_bytes()).ok()?;
        // SAFETY: an all-zero `statvfs` is valid; `c` is a valid C string.
        let mut st: libc::statvfs = unsafe { std::mem::zeroed() };
        // SAFETY: `c` is a valid NUL-terminated C string and `&mut st` is a
        // valid `statvfs` the call may write.
        if unsafe { libc::statvfs(c.as_ptr(), &mut st) } != 0 {
            return None;
        }
        #[allow(clippy::unnecessary_cast)]
        let frsize = st.f_frsize as u64;
        // (fsblkcnt_t is u32 on macOS, u64 on Linux.)
        #[allow(clippy::unnecessary_cast)]
        let (avail, blocks) = (st.f_bavail as u64, st.f_blocks as u64);
        Some((avail * frsize, blocks * frsize, frsize))
    }
    #[cfg(not(unix))]
    {
        let _ = path;
        None
    }
}

/// The space available to this process on the file system of `path`, and
/// the size of that file system (bytes).
pub fn disk_space(path: &Path) -> Option<(u64, u64)> {
    fs_info(path).map(|(avail, total, _)| (avail, total))
}

/// The free space tlx leaves on a file system of `total` bytes: the
/// smaller of 1 GiB and 2%.
pub fn disk_reserve(total: u64) -> u64 {
    (total / 50).min(1 << 30)
}

/// Parse a disk size (`-maxdisk`, `TLX_MAXDISK`): MiB, or with a suffix
/// `K`, `M`, `G` or `T` (as `-maxmem`, without fractions; the grammar is
/// shared in `size`), as a positive `u64` byte count.
pub fn parse_size(v: &str) -> Option<u64> {
    let (digits, suffix) = crate::size::digits_and_suffix(v.trim());
    let n: u64 = digits.parse().ok()?;
    n.checked_mul(1u64 << crate::size::shift_of(suffix)?).filter(|&b| b > 0)
}

#[cfg(test)]
mod tests;
