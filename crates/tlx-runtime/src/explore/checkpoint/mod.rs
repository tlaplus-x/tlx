//! Checkpoints and recovery (docs/scale.md §9): TLC's `-checkpoint`
//! and `-recover`.
//!
//! A checkpoint is taken at a level barrier (with one worker: between two
//! levels), when every state of the levels before the current one has
//! been expanded and the current level is queued whole: the seen set, the
//! queued states, the trace logs, the counters and, if used, the BFS
//! positions of the queued states (VIEW / SYMMETRY with several workers),
//! the liveness edge logs and the archive of a compiled-tier search that
//! may resume after a layout miss. A recovered search continues from there
//! as the interrupted one would have: same counts, depth and traces (with
//! one worker, the same order of expansion).
//!
//! Layout: the directory `checkpoint` of the metadir (`-metadir`, by
//! default the spill directory), written as `checkpoint.tmp` and renamed
//! when complete (the previous checkpoint is renamed `checkpoint.old`
//! meanwhile, then removed): there is at most one, and a run killed at any
//! moment leaves a complete one (or none). Every file is framed
//! (`tlx_base::frame`: build id, checksummed chunks, end marker); the
//! data of each file is `fsync`ed as it is written (a failure is reported),
//! and the checkpoint as a whole is handed to the medium, best effort, by a
//! single drive-cache flush of its directory just before the commit rename
//! (`crate::io::durable`: `sync_file`, `sync_dir_full`, `DirCommit`; the
//! directory flush ignores its own errors):
//!
//! | file | contents |
//! |---|---|
//! | `MANIFEST` | identity of the run (spec, cfg, options: the caller's), counters (the `-coverage` counts too), the files and their sizes, the snapshots of the workers and of the main thread (`Checkpointed::worker_snapshot`, `main_snapshot`: TLCSet registers) |
//! | `fpset-run-<k>`, `fpset-<p>` | the fingerprints of each run on disk and of each part of the table, ascending, 8 bytes each (the parts of the table, in order, are ascending too) |
//! | `queue-<l>` | the queued states of list `l` of the level, in claim order: trace-log entry, fingerprint, the state (its codec's words XOR-coded, or `Persist` bytes), BFS position |
//! | `trace-<w>.<n>` | worker `w`'s trace log, 16 bytes per entry |
//! | `edges-<w>`, `edges-<w>-fps.<n>`, `edges-<w>-meta.<n>` | worker `w`'s liveness edge log: header (`EdgeRec::header`), columns |
//! | `archive-<w>.<n>` | worker `w`'s part of the archive (XOR-coded records by depth) |
//! | `model-<name>` | the model's files (`Checkpointed::files`) |
//!
//! What a search only appends to (the trace logs, the archive, the edge
//! logs' columns: streams) is written in segments `<stream>.<n>`, the
//! values appended before checkpoint `n`; a checkpoint hard-links the
//! segments of the previous one (by the same search, or the one it
//! recovered from: the recovered archive, read into worker 0's part, as the
//! first segments of `archive-0`, numbering on from it) and the runs of the
//! seen set it wrote (`fpset-run-<id>`: runs never change), and writes only
//! the rest (incremental checkpoints).
//!
//! Each worker writes its own files, then takes the shared ones (a run, a
//! part of the table, a list of the queue) as jobs until none is left: all
//! in parallel. The last worker to finish writes the manifest and commits.

mod manifest;
mod recover;
mod write;

pub(super) use self::recover::recover_phase;
pub use self::recover::Recovery;

use std::fs::File;
use std::io::BufWriter;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use parking_lot::Mutex;
use tlx_base::frame::FrameWriter;

use self::write::Prev;
use super::OutdegreeHist;
use crate::io::durable::{sync_file, DirCommit};
use crate::io::{checkpoint_dirs, DirHold, Plain, Spill, SpillVec};
use crate::stats;

/// The name of the manifest in a checkpoint directory.
pub const MANIFEST: &str = "MANIFEST";

const fn kind(k: &[u8; 4]) -> u32 {
    u32::from_be_bytes(*k)
}
const K_MANIFEST: u32 = kind(b"CKMF");
const K_FPSET: u32 = kind(b"CKFP");
const K_QUEUE: u32 = kind(b"CKQU");
const K_TRACE: u32 = kind(b"CKTL");
const K_EDGES: u32 = kind(b"CKED");
const K_ARCHIVE: u32 = kind(b"CKAR");
const K_MODEL: u32 = kind(b"CKMO");

/// The exit status of a process ended after a checkpoint by
/// `AfterCommit::Abort` (that of a process killed by SIGABRT).
pub const ABORT_EXIT: i32 = 134;

/// The chunks of the large files hold about this many bytes.
const CHUNK_BYTES: usize = 1 << 20;

/// The table of the seen set is written in parts of at least this many
/// slots (and at most `TABLE_PARTS_PER_WORKER` parts per worker).
const TABLE_PART_SLOTS: usize = 1 << 16;
const TABLE_PARTS_PER_WORKER: usize = 2;

/// What happens after a checkpoint is committed (testing,
/// `TLX_CHECKPOINT_ABORT`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum AfterCommit {
    #[default]
    Continue,
    /// After the n-th checkpoint the process ends at once, as if killed:
    /// `_exit(ABORT_EXIT)` (no cleanup; unlike `abort()`, no core dump or
    /// crash report).
    Abort(u64),
    /// After the n-th checkpoint the search stops, and the checkpoint is
    /// kept (in-process tests of recovery).
    Stop(u64),
}

/// What a checkpoint reports (the caller prints TLC's messages).
#[derive(Debug)]
pub enum Event<'a> {
    /// A checkpoint is being written to the run's metadir.
    Start(&'a Path),
    /// It was committed: its number, how long it took, the bytes written,
    /// and the distinct states it holds.
    Done { number: u64, time: Duration, bytes: u64, states: u64 },
    /// It could not be written (the search goes on; the previous one, if
    /// any, is kept).
    Failed(&'a str),
}

/// When and how a search takes checkpoints.
#[derive(Clone, Default)]
pub struct CheckpointConfig {
    /// The interval (`-checkpoint`, minutes in TLC); None: not by time.
    pub every: Option<Duration>,
    /// Testing (`TLX_CHECKPOINT_STATES`): whenever that many distinct
    /// states were found since the last checkpoint.
    pub every_states: Option<u64>,
    pub after: AfterCommit,
    /// What the run is (the spec, the cfg, the options that change its
    /// results), as (key, value) pairs: stored in the manifest, compared
    /// by the caller when recovering.
    pub identity: Vec<(String, String)>,
    pub report: Option<Arc<dyn Fn(&Event<'_>) + Send + Sync>>,
    /// Checkpoints were asked for (`-checkpoint N`, the testing variables),
    /// not only TLC's default interval.
    pub explicit: bool,
}

impl std::fmt::Debug for CheckpointConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("CheckpointConfig")
            .field("every", &self.every)
            .field("every_states", &self.every_states)
            .field("after", &self.after)
            .finish_non_exhaustive()
    }
}

/// The checkpoints of a run (shared by its searches: a compiled-tier run
/// may search several times).
pub struct Checkpointer {
    cfg: CheckpointConfig,
    /// When the last checkpoint was committed (at first: when the run
    /// started), and the distinct states then.
    last: Mutex<(Instant, u64)>,
    /// Checkpoints committed.
    count: AtomicU64,
    /// The metadir, held from the first checkpoint (or the recovery) on.
    hold: Mutex<Option<DirHold>>,
    /// Keep the last checkpoint when the search ends (`AfterCommit::Stop`).
    keep: AtomicBool,
}

impl std::fmt::Debug for Checkpointer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Checkpointer").field("cfg", &self.cfg).field("count", &self.count).finish_non_exhaustive()
    }
}

impl Checkpointer {
    pub fn new(cfg: CheckpointConfig) -> Arc<Checkpointer> {
        Arc::new(Checkpointer {
            cfg,
            last: Mutex::new((Instant::now(), 0)),
            count: AtomicU64::new(0),
            hold: Mutex::new(None),
            keep: AtomicBool::new(false),
        })
    }

    /// Whether checkpoints were asked for (`CheckpointConfig::explicit`).
    pub fn explicit(&self) -> bool {
        self.cfg.explicit
    }

    /// The checkpoints committed so far.
    pub fn count(&self) -> u64 {
        self.count.load(Ordering::Relaxed)
    }

    /// Whether a search of the run that found `distinct` states by now
    /// would have taken a checkpoint (the compiled tier's pre-run, whose
    /// result replaces the search only if not).
    pub fn would_be_due(&self, distinct: u64) -> bool {
        self.due(distinct)
    }

    /// Whether a checkpoint is due, with `distinct` states found.
    fn due(&self, distinct: u64) -> bool {
        if self.keep.load(Ordering::Relaxed) {
            return false;
        }
        let (t, d) = *self.last.lock();
        // (Fewer states than at the last checkpoint: a new search of the run.)
        let d = if distinct < d { 0 } else { d };
        self.cfg.every.is_some_and(|e| t.elapsed() >= e) || self.cfg.every_states.is_some_and(|n| distinct >= d.saturating_add(n.max(1)))
    }

    fn report(&self, e: &Event<'_>) {
        if let Some(r) = &self.cfg.report {
            r(e);
        }
    }

    /// The metadir (held from now on).
    fn dir(&self, spill: &Spill) -> Result<PathBuf, String> {
        let mut h = self.hold.lock();
        if h.is_none() {
            *h = Some(spill.hold_dir().map_err(|e| e.0)?);
        }
        Ok(h.as_ref().expect("held").path().to_path_buf())
    }

    /// Hold the metadir of a recovered run (its checkpoint is removed at
    /// the end like this run's own).
    pub(super) fn adopt(&self, spill: &Spill) -> Result<(), String> {
        self.dir(spill).map(|_| ())
    }

    /// The search ended (not killed): remove the checkpoint (unless it is
    /// to be kept, with the metadir) and release the metadir.
    pub(super) fn finish(&self) {
        let Some(h) = self.hold.lock().take() else { return };
        if self.keep.load(Ordering::SeqCst) {
            h.keep();
            return;
        }
        checkpoint_dirs(h.path()).remove_all();
    }
}

/// A file of a checkpoint being written. Its size is the file's own size on
/// disk (`close`), the single authority: no running total is kept (the
/// manifest's file table and the reported bytes both come from it).
struct Out {
    name: String,
    path: PathBuf,
    w: FrameWriter<BufWriter<File>>,
}

impl Out {
    fn create(dir: &Path, name: &str, kind: u32) -> Result<Out, String> {
        let path = dir.join(name);
        let f = File::create(&path).map_err(|e| format!("cannot create {}: {e}", path.display()))?;
        let w =
            FrameWriter::new(BufWriter::with_capacity(1 << 20, f), kind).map_err(|e| format!("cannot write {}: {e}", path.display()))?;
        Ok(Out { name: name.to_string(), path, w })
    }

    fn chunk(&mut self, b: &[u8]) -> Result<(), String> {
        self.w.chunk(b).map_err(|e| format!("cannot write {}: {e}", self.path.display()))
    }

    /// Finish the file and hand its data to the device: its name and size.
    ///
    /// The sync is a plain `fsync` (`sync_file`), whose failure is
    /// reported: the checkpoint as a whole is handed to the medium, best
    /// effort, by one drive-cache flush before the commit rename
    /// (`DirCommit::commit`), not by a flush per file.
    fn close(self) -> Result<(String, u64), String> {
        let err = |e: &dyn std::fmt::Display| format!("cannot write {}: {e}", self.path.display());
        let bw = self.w.finish().map_err(|e| err(&e))?;
        let f = bw.into_inner().map_err(|e| err(&e.error().to_string()))?;
        let t0 = Instant::now();
        sync_file(&f).map_err(|e| err(&e))?;
        stats::add_secs("checkpoints: file syncs (all threads)", t0.elapsed());
        let len = f.metadata().map_err(|e| err(&e))?.len();
        Ok((self.name, len))
    }
}

/// Call `f` with the values of `v` in order, in slices of at most `n`
/// (spilled blocks read back); stops at the first error.
pub(super) fn chunked<T: Plain>(
    v: &SpillVec<T>,
    spill: &Spill,
    start: usize,
    n: usize,
    mut f: impl FnMut(&[T]) -> Result<(), String>,
) -> Result<(), String> {
    let mut buf = Vec::with_capacity(n.min(v.len() - start.min(v.len())));
    let mut it = v.iter_from(start, Some(spill));
    for x in &mut it {
        buf.push(x);
        if buf.len() == n {
            f(&buf)?;
            buf.clear();
        }
    }
    if let Some(e) = it.error() {
        return Err(e.0.clone());
    }
    if !buf.is_empty() {
        f(&buf)?;
    }
    Ok(())
}

/// Append `n` values read from `chunks` (as `chunked` wrote them) to `v`.
pub(super) fn read_values<T: Plain>(
    v: &mut SpillVec<T>,
    n: usize,
    chunks: &mut dyn FnMut() -> Result<Option<Vec<u8>>, String>,
) -> Result<(), String> {
    let size = std::mem::size_of::<T>();
    let mut left = n;
    while left > 0 {
        let c = chunks()?.ok_or("fewer values than recorded")?;
        if c.len() % size != 0 || c.len() / size > left {
            return Err("a chunk of the wrong size".into());
        }
        let mut vals = vec![T::default(); c.len() / size];
        crate::io::as_bytes_mut(&mut vals).copy_from_slice(&c);
        left -= vals.len();
        for x in vals {
            v.push(x);
        }
    }
    Ok(())
}

/// The segments of a stream: (file, values), in order.
type Segments = Vec<(String, u64)>;

/// What a worker wrote for a checkpoint.
pub(super) struct Part {
    outdegree: OutdegreeHist,
    snapshot: Vec<u8>,
    /// Its part of the archive is complete (and written).
    archived: bool,
    /// It records liveness edges (and wrote them).
    edges: bool,
    /// The files written (or linked), with their sizes.
    files: Vec<(String, u64)>,
    /// Its streams.
    streams: Vec<(String, Segments)>,
}

/// A shared file of a checkpoint, written by whichever worker takes it.
#[derive(Clone, Copy, Debug)]
enum Job {
    /// Run `k` of the seen set on disk.
    Run(usize),
    /// Part `part` of `parts` of the seen set's table.
    Table { part: usize, parts: usize },
    /// List `l` of the queued level.
    Queue(usize),
}

/// What a job wrote: its file (name, size), the fingerprints or states in
/// it, and (a list of the queue) their depth.
struct JobOut {
    file: (String, u64),
    count: u64,
    level: u32,
}

/// The checkpoints of one search.
pub(super) struct CkptRun {
    pub(super) ck: Arc<Checkpointer>,
    /// The barrier leader decided to take a checkpoint at this barrier:
    /// the workers write their parts.
    pub(super) now: AtomicBool,
    /// The directories of the checkpoint being written, and when it
    /// started.
    tmp: Mutex<Option<(DirCommit, Instant)>>,
    /// The workers' parts (per worker).
    parts: Mutex<Vec<Option<Result<Part, String>>>>,
    /// The last checkpoint committed by this search, or the one it
    /// recovered from: what the next one links.
    prev: Mutex<Option<Arc<Prev>>>,
    /// The number of the checkpoint this search recovered from (0: none):
    /// its checkpoints count on from it, so that the segments they write
    /// are never named as the recovered ones they link.
    base: AtomicU64,
    /// The shared files to write (set when a checkpoint starts), the next
    /// one to take, and what each wrote.
    jobs: Mutex<Vec<Job>>,
    next_job: AtomicUsize,
    jobs_done: Mutex<Vec<Option<Result<JobOut, String>>>>,
    /// `Model::extra_generated` when the search started.
    pub(super) extra_at_start: u64,
}

impl CkptRun {
    pub(super) fn new(ck: Arc<Checkpointer>, workers: usize, extra_at_start: u64) -> CkptRun {
        CkptRun {
            ck,
            now: AtomicBool::new(false),
            tmp: Mutex::new(None),
            parts: Mutex::new((0..workers).map(|_| None).collect()),
            prev: Mutex::new(None),
            base: AtomicU64::new(0),
            jobs: Mutex::new(Vec::new()),
            next_job: AtomicUsize::new(0),
            jobs_done: Mutex::new(Vec::new()),
            extra_at_start,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `Out::close` reports the file's own size on disk, the single
    /// authority (a running total of the payloads would miss the frame's
    /// own bytes).
    #[test]
    fn the_size_of_a_written_file_is_its_size_on_disk() {
        let dir = tlx_testkit::TempDir::new("checkpoint-out-size");
        let mut out = Out::create(dir.path(), "a-data-file", K_MODEL).expect("create");
        out.chunk(b"first").expect("chunk");
        out.chunk(&[7u8; 5000]).expect("chunk");
        let (name, len) = out.close().expect("close");
        let on_disk = std::fs::metadata(dir.path().join(&name)).expect("metadata").len();
        assert_eq!(len, on_disk);
    }
}
