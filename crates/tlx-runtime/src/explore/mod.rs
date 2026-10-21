//! Parallel breadth-first state exploration (design.md §7.3).
//!
//! With one worker the order is exact BFS; with several the search is
//! level-synchronous (`levels`), narrow levels being expanded by a single
//! worker.
//!
//! States are not retained after expansion. For error traces every distinct
//! state appends `(parent, fingerprint)` to its worker's trace log
//! (`tracelog`); a trace is rebuilt by re-executing the model along the
//! fingerprint chain (as TLC does).
//!
//! Modules: `worker` (expanding a state: the per-successor hot path),
//! `frontier` (the level queues of tasks, `crate::queue`), `levels`
//! (level-synchronous search, barrier, solo narrow levels), `order`
//! (representatives in BFS order under VIEW / SYMMETRY), `tracelog`,
//! `resume` (the archive and `ResumePoint`), `safepoint` (the control
//! word and pausing all workers), `edges` (the liveness behavior graph
//! recorded while searching), `coverage` (`-coverage` counts per action),
//! `observer` (watching a search: `-dump`, the liveness error search, the
//! compiled tier's faithful pre-run), `run` and `finish` (the phases of
//! one search: preparation, the initial states, the worker scope, the
//! results).
//! The memory budget (`crate::mem`) is enforced here (`Shared::relieve`,
//! `Shared::grow_seen`).

pub mod checkpoint;
mod coverage;
mod edges;
mod finish;
mod frontier;
mod history;
mod levels;
mod observer;
mod order;
mod resume;
mod run;
pub mod safepoint;
mod tracelog;
mod worker;

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};
pub(crate) use tlx_base::par::{join_pool_with as join_all, on_panic as abort_on_panic};

use parking_lot::Mutex;

use self::checkpoint::CkptRun;
use self::frontier::{Frontier, Local, Task};
use self::history::History;
use self::levels::Levels;
use self::order::{Order, Positions};
use self::resume::{Pre, Retention};
use self::safepoint::{Control, Crew, Safepoint};
use self::tracelog::{log_ref, LogRef, TraceLog, NO_PARENT};
use self::worker::Slot;
use crate::cache_mem;
use crate::fpset::{FpConfig, FpSet, Full};
use crate::io::SpillMode;
use crate::live::{self, LiveStats};
use crate::mem::{Component, Gauge, MemBudget, Stage};
use crate::model::{Model, ModelError};

pub use self::checkpoint::{AfterCommit, CheckpointConfig, Checkpointer, Event as CheckpointEvent, Recovery};
pub use self::coverage::{Coverage, CoverageReport};
pub use self::edges::{liveness_memory_error, ActionMasks, AtomBits, LiveGraph, LIVENESS_MEMORY};
pub use self::observer::SearchObserver;
pub use self::resume::{ResumePoint, TranscodeError};

#[derive(Clone, Debug)]
pub struct Options {
    pub workers: usize,
    pub check_deadlock: bool,
    /// The size of the fingerprint set: fixed, or growing up to a limit.
    pub fp: FpConfig,
    /// Periodic progress reports.
    pub progress: Option<Progress>,
    /// Testing: every worker requests a safepoint
    /// (which changes nothing; its executor checks that all workers are
    /// paused) every that many states it expands; 0: never.
    pub safepoint_every: u64,
    /// The parameters of the frontier's queue (testing).
    pub queue: crate::queue::Config,
    /// The memory budget (`-maxmem`, bytes; `usize::MAX`: unlimited), see
    /// `crate::mem`. A growable fingerprint set is limited to it.
    pub maxmem: usize,
    /// The disk layer (`-spill`, `-metadir`, `-maxdisk`): where the trace
    /// logs and liveness edges go under memory pressure (`crate::io`).
    pub spill: crate::io::Spill,
    /// Checkpoints (`-checkpoint`, in the spill directory), if taken.
    pub checkpoint: Option<Arc<Checkpointer>>,
    /// Count the states each action generates and finds (`-coverage`,
    /// `Report::coverage`) ...
    pub coverage: bool,
    /// ... and report them periodically during the search.
    pub coverage_report: Option<CoverageReport>,
}

/// Periodic progress reports during the search (TLC reports after 3
/// seconds, then every minute).
#[derive(Clone)]
pub struct Progress {
    /// Time of the first report after the start of the search.
    pub first: Duration,
    /// Interval between later reports.
    pub every: Duration,
    /// Called (on a monitor thread) with the current statistics.
    pub report: Arc<dyn Fn(&LiveStats) + Send + Sync>,
    /// Called once the initial states are computed and checked without
    /// error, with the numbers of generated and distinct initial states.
    pub init_done: Arc<dyn Fn(u64, u64) + Send + Sync>,
}

impl std::fmt::Debug for Progress {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Progress").field("first", &self.first).field("every", &self.every).finish_non_exhaustive()
    }
}

impl Default for Options {
    fn default() -> Options {
        Options {
            workers: 1,
            check_deadlock: true,
            fp: FpConfig::default(),
            progress: None,
            safepoint_every: 0,
            queue: Default::default(),
            maxmem: usize::MAX,
            spill: Default::default(),
            checkpoint: None,
            coverage: false,
            coverage_report: None,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Stats {
    /// Initial states generated (including duplicates).
    pub init_generated: u64,
    /// Distinct initial states.
    pub init_distinct: u64,
    /// All states generated: initial states plus every successor produced.
    pub generated: u64,
    pub distinct: u64,
    /// Number of BFS levels (initial states are level 1).
    pub depth: u32,
    /// States still queued when exploration stopped.
    pub left: u64,
    /// Outdegree of the state graph: the number of new states found by
    /// expanding a state (TLC's "average outdegree" report).
    pub outdegree: Outdegree,
}

/// Distribution of the number of new states found by expanding a state.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Outdegree {
    pub min: u64,
    pub max: u64,
    /// The mean, rounded.
    pub mean: u64,
    /// The 95th percentile.
    pub p95: u64,
}

/// Histogram of outdegrees, as TLC's (tlc2.util.statistics.
/// FixedSizedBucketStatistics with 32 buckets: larger outdegrees count as 31).
const OUTDEGREE_BUCKETS: usize = 32;

#[derive(Clone)]
struct OutdegreeHist {
    counts: [u64; OUTDEGREE_BUCKETS],
}

impl OutdegreeHist {
    fn new() -> OutdegreeHist {
        OutdegreeHist { counts: [0; OUTDEGREE_BUCKETS] }
    }

    #[inline]
    fn add(&mut self, n: u64) {
        self.counts[(n as usize).min(OUTDEGREE_BUCKETS - 1)] += 1;
    }

    /// Count a state of outdegree `old` as of outdegree `new`.
    fn replace(&mut self, old: u64, new: u64) {
        self.counts[(old as usize).min(OUTDEGREE_BUCKETS - 1)] -= 1;
        self.add(new);
    }

    fn merge(&mut self, o: &OutdegreeHist) {
        for (a, b) in self.counts.iter_mut().zip(&o.counts) {
            *a += b;
        }
    }

    /// TLC's statistics (AbstractBucketStatistics): the mean is rounded,
    /// the percentile is the first outdegree whose cumulated count exceeds
    /// the rank `floor(n * 0.95)`.
    fn summary(&self) -> Outdegree {
        let total: u64 = self.counts.iter().sum();
        if total == 0 {
            return Outdegree::default();
        }
        let present = || self.counts.iter().enumerate().filter(|(_, &c)| c > 0).map(|(k, _)| k as u64);
        let min = present().next().unwrap_or(0);
        let max = present().next_back().unwrap_or(0);
        let sum: u64 = self.counts.iter().enumerate().map(|(k, &c)| k as u64 * c).sum();
        let rank = (total as f64 * 0.95) as u64;
        let mut acc = 0;
        let mut p95 = max;
        for (k, &c) in self.counts.iter().enumerate() {
            acc += c;
            if acc > rank {
                p95 = k as u64;
                break;
            }
        }
        let mean = (sum as f64 / total as f64).round() as u64;
        Outdegree { min, max, mean, p95 }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Outcome {
    Ok,
    InvariantViolated(String),
    /// A state-predicate part of a PROPERTY is false in an initial state.
    InitPropertyViolated(String),
    /// A temporal property is violated by a simulated behavior: the
    /// properties it violates and the counterexample, already rendered.
    TemporalViolated {
        properties: Vec<String>,
        counterexample: String,
    },
    ActionPropertyViolated(String),
    Deadlock,
    /// The fingerprint set is full: the search found more distinct states
    /// than `-fpmem` can hold. A resource limit of the run, not a property
    /// violation or an evaluation error of the specification, so the CLI
    /// reports it as a system error and shows no behavior. `entries` is the
    /// number of states the set holds (the capacity the run was given).
    FpSetFull {
        entries: u64,
    },
    /// The disk layer failed (a write error, a full disk, `-maxdisk`
    /// exceeded, a corrupt spill file): a resource failure of the run, like
    /// `FpSetFull`. The message says what happened.
    Io(String),
    /// A simulation found no initial state that satisfies the state
    /// constraints (TLC's TLC_NO_STATES_SATISFYING_INIT_AND_CONSTRAINT).
    NoInitInConstraint,
    /// An evaluation error (or another error that stops the search).
    Error(ModelError),
}

#[derive(Clone, Debug)]
pub struct TraceStep<S> {
    pub state: S,
    /// Action that produced this state (None for the initial state).
    pub action: Option<u32>,
}

#[derive(Debug)]
pub struct Report<S> {
    pub stats: Stats,
    pub outcome: Outcome,
    /// Trace from an initial state to the offending state (empty if Ok, or if
    /// the error happened while computing initial states).
    pub trace: Vec<TraceStep<S>>,
    /// A genuine prefix was reconstructed, but runtime-dependent generation
    /// prevented rebuilding the whole counterexample (docs/compat.md D-30).
    pub trace_note: Option<String>,
    pub elapsed: Duration,
    /// The failure happened while computing (or checking) the initial
    /// states (TLC then reports no statistics).
    pub in_init: bool,
    /// The behavior graph recorded for liveness checking (`Caps::live_atoms`),
    /// if the search explored the whole state space without error; Err: it
    /// does not fit in the memory budget (the message of the liveness
    /// failure, see `liveness_memory_error`).
    pub live_graph: Option<Result<LiveGraph, String>>,
    /// An atom failed during the search that otherwise ended as `live_graph`
    /// requires (no failure, the whole state space, or the states expanded
    /// before `TLCSet("exit")`): the first error. TLC evaluates the atoms
    /// during its search, so liveness reports it. Not with `live_graph`.
    pub live_error: Option<ModelError>,
    /// The search evaluated the liveness atoms (`Caps::live_atoms`) on every
    /// state it expanded (and their steps) and the atoms of the tableaux on
    /// every state it found (`AtomBits::tableau`), without error: TLC, which
    /// evaluates them during its search, found no error in them either
    /// before the point where the search stopped (if it expanded the initial
    /// states).
    pub live_atoms_ok: bool,
    /// The states each action generated and found (`Options::coverage`).
    pub coverage: Option<Coverage>,
}

/// A full fingerprint set: the message the CLI prints (with the numbers of
/// the run), not a failure of the specification.
pub const FULL: &str = "The fingerprint set is full; rerun with a larger -fpmem.";

/// A fingerprint set that could not grow within the memory budget.
pub const FULL_BUDGET: &str = "The fingerprint set is full: it cannot grow within the memory budget; rerun with a larger -maxmem.";

/// The failure of a full fingerprint set. The state that could not be
/// inserted is not reported: a resource limit is not a counterexample, and
/// its trace (the whole behavior up to it) can be enormous. A set whose
/// disk tier failed (a rotation or a lookup) fails with the IO error.
fn fp_set_full(seen: &FpSet) -> Failure {
    match seen.io_error() {
        Some(e) => (Outcome::Io(e.0), NO_PARENT),
        None => (Outcome::FpSetFull { entries: seen.max_entries() as u64 }, NO_PARENT),
    }
}

/// A failure and the log entry of the state at which it occurred.
type Failure = (Outcome, LogRef);

struct Shared<'m, M: Model> {
    model: &'m M,
    opts: &'m Options,
    /// The observer of the search (`explore_observed`), if any.
    observer: Option<&'m dyn SearchObserver<M::State>>,
    /// The observer's search is not the run's own (`SearchObserver::quiet`).
    quiet: bool,
    /// The observer stopped the search (`SearchObserver::stop`).
    halted: AtomicBool,
    seen: FpSet,
    frontier: Frontier<'m, M::State>,
    /// The control word (stop, safepoint requests) and the safepoints.
    safepoint: Safepoint,
    /// Per-worker counters.
    slots: Box<[Slot]>,
    init_generated: AtomicU64,
    init_distinct: AtomicU64,
    start: Instant,
    failure: Mutex<Option<Failure>>,
    /// The level-synchronous search (several workers).
    levels: Levels,
    /// Choosing the representatives of the fingerprint classes in BFS
    /// order (several workers, `Model::coarse_fingerprint`).
    order: Option<Order>,
    /// Archiving the states done with (see `ResumePoint`).
    retention: Retention,
    /// The memory budget.
    budget: MemBudget,
    /// A resumed (or recovered) search: what the resume point (the
    /// checkpoint) accounts for.
    base_generated: u64,
    base_depth: u32,
    base_outdegree: OutdegreeHist,
    /// `Options::safepoint_every`.
    safepoint_every: u64,
    /// The liveness atoms evaluated to record the behavior graph, if
    /// recording.
    live_atoms: Option<&'m (dyn AtomBits<M::State> + Sync)>,
    /// A resumed search that records the behavior graph: the states of the
    /// levels before its resume point, whose edges are recorded after the
    /// search (docs/scale.md §8.3).
    live_pre: Mutex<Vec<Pre<M::State>>>,
    /// Stages 2 and 3 of memory pressure: workers write the full blocks of
    /// their trace logs (liveness edge logs) to disk.
    spill_logs: AtomicBool,
    spill_edges: AtomicBool,
    /// Taking checkpoints (`Options::checkpoint`), if the model can be.
    ckpt: Option<CkptRun>,
    /// All trace and liveness shards, including those without a current worker.
    history: Mutex<History<'m, M::State>>,
    /// Counting coverage (`Options::coverage`): the counts before the
    /// resume point this search resumed from (flat, see `Slot::cov`).
    cov_base: Vec<u64>,
    /// `TLCExt!Trace` (`Model::uses_trace`): the paths to the states found.
    paths: Option<Mutex<PathTable>>,
}

/// The path (`live::PathNode`) to each state found at the last two depths:
/// the states to expand, and the parents of the states the search finds
/// (whose representatives several workers choose after the level). The
/// paths of the states expanded before are kept by their descendants'.
#[derive(Default)]
pub(super) struct PathTable {
    nodes: tlx_base::hash::FxMap<LogRef, (u32, Arc<live::PathNode>)>,
    depth: u32,
}

impl PathTable {
    pub(super) fn insert(&mut self, at: LogRef, depth: u32, node: Arc<live::PathNode>) {
        if depth > self.depth {
            self.depth = depth;
            self.nodes.retain(|_, (d, _)| *d + 1 >= depth);
        }
        self.nodes.insert(at, (depth, node));
    }

    fn get(&self, at: LogRef) -> Option<Arc<live::PathNode>> {
        self.nodes.get(&at).map(|(_, n)| n.clone())
    }
}

/// Safepoint request: the test safepoint of `Options::safepoint_every`. (Bit 0
/// of the control word is `safepoint::STOP`; the other bits are free for
/// the requests of other components.)
const SP_TEST: u32 = 1 << 31;

/// Safepoint request: grow the fingerprint set (made at its high
/// watermark, or by a worker that found it at its hard limit).
pub(super) const SP_GROW: u32 = 1 << 1;

/// Safepoint request: drop the fingerprint set's old table (its run is on
/// disk), made by the budget once nothing else is left to give back.
const SP_DROP_OLD: u32 = 1 << 2;

/// A fingerprint set growing from at least this many home slots at a
/// safepoint of fewer workers than the search has is rehashed by as many
/// threads as the search has workers (`Shared::grow_seen`).
const GROW_HELPERS_FROM: usize = 1 << 20;

/// The smallest table of a fingerprint set that rotates to disk under
/// memory pressure (512 KiB; less only if its limit is less, as with
/// `-spill always`): smaller tables would rotate too often.
const ROTATE_MIN_SLOTS: usize = 1 << 16;

/// The tables of a fingerprint set that rotates to disk get at least this
/// share of the memory budget (1/4).
const TABLES_SHARE: usize = 4;

/// The number of test safepoints served in this process (for tests).
static TEST_SAFEPOINTS: AtomicU64 = AtomicU64::new(0);

/// The number of safepoints requested with `Options::safepoint_every` that
/// were served so far in this process.
#[doc(hidden)]
pub fn test_safepoints_served() -> u64 {
    TEST_SAFEPOINTS.load(Ordering::SeqCst)
}

impl<M: Model> Shared<'_, M> {
    /// The control word.
    #[inline]
    fn control(&self) -> &Control {
        self.safepoint.control()
    }

    /// A worker panicked: stop the search and release the barrier and the
    /// safepoints.
    fn abort(&self) {
        self.control().stop();
        self.levels.barrier.break_all();
        self.safepoint.break_all();
    }

    /// Whether the observer stops the search here (`SearchObserver::stop`,
    /// after the initial states): it then stops.
    #[cold]
    #[inline(never)]
    fn observer_stops(&self) -> bool {
        let Some(o) = self.observer else {
            return false;
        };
        if !o.stop(false, self.seen.len() as u64) {
            return false;
        }
        self.halted.store(true, Ordering::Relaxed);
        self.control().stop();
        true
    }

    /// Record the first failure and stop all workers.
    fn fail(&self, outcome: Outcome, at: LogRef) {
        let mut f = self.failure.lock();
        if f.is_none() {
            *f = Some((outcome, at));
        }
        self.control().stop();
    }

    /// Serve the safepoint requests `req`: every active worker is parked
    /// (see `safepoint`).
    fn serve_safepoint(&self, req: u32, crew: &Crew<'_>) {
        if req & SP_DROP_OLD != 0 {
            // SAFETY: every active worker is parked, the others hold no
            // reference into the set.
            unsafe { self.seen.drop_old() };
        }
        if req & SP_GROW != 0 {
            self.grow_seen(Some(crew));
        }
        if req & SP_TEST != 0 {
            self.test_safepoint(crew);
        }
    }

    /// Make room in the seen set (at a safepoint: `crew`; or while no
    /// worker runs: None) within the memory budget, once its table reached
    /// its high watermark: grow it twice as large if that fits along with
    /// the current table (both are held while growing), else, after the
    /// earlier stages of memory pressure, stage 5: rotate it to disk
    /// (`rotate_seen`), or without a disk tier grow it as large as fits,
    /// or not at all (the set stops growing and fills up to its hard
    /// limit). A set that rotated rotates from then on. Also installs a
    /// finished merge of the disk tier's runs.
    fn grow_seen(&self, crew: Option<&Crew<'_>>) {
        let seen = &self.seen;
        // SAFETY: every active worker is parked (or none runs), the
        // others hold no reference into the set.
        unsafe { seen.install_merge(false) };
        if !seen.at_high() {
            return;
        }
        // A large table changed at a safepoint with fewer workers than the
        // search's (in a narrow level expanded by one worker, the others
        // wait at the level barrier; or before the workers start): rehashed
        // or written by as many threads.
        let threads =
            if crew.map_or(0, |c| c.size()) < self.slots.len() && seen.slots() >= GROW_HELPERS_FROM { self.slots.len() } else { 0 };
        if seen.spilling() {
            if seen.rotatable() {
                self.rotate_seen(crew, threads);
            }
            return;
        }
        let mut slots = seen.next_slots();
        if self.budget.limited() {
            let old = seen.bytes();
            // The memory left for the tables (the current one included).
            let room = |others: usize| self.budget.total().saturating_sub(others);
            let mut others = self.budget.used(self.accounted()).saturating_sub(old);
            if old + FpSet::table_bytes(slots) > room(others) {
                // Pressure: the earlier stages first.
                if let Some(order) = &self.order {
                    order.shrink();
                }
                if self.relieve_archive() {
                    // (Written out by the workers after the safepoint; a
                    // dropped archive frees nothing that the blocks kept
                    // for the liveness edges of a resumed search share.)
                    if self.frontier.archive_spilling() || self.live_pre.lock().is_empty() {
                        others = others.saturating_sub(self.budget.meters().bytes(Component::Archive));
                    }
                    self.budget.reach(Stage::Archive);
                }
                if old + FpSet::table_bytes(slots) > room(others) && self.start_spilling(true) {
                    // (The workers write their logs out as soon as the
                    // safepoint ends.)
                    others = others.saturating_sub(self.log_bytes());
                }
                if old + FpSet::table_bytes(slots) > room(others) {
                    self.frontier.squeeze(true);
                    self.spill_candidates();
                    self.budget.reach(Stage::Frontier);
                    if self.spill_frontier() {
                        others = others.saturating_sub(self.budget.meters().bytes(Component::Frontier));
                    }
                }
                if old + FpSet::table_bytes(slots) > room(others) {
                    self.budget.reach(Stage::FpSet);
                    if seen.rotatable() {
                        self.rotate_seen(crew, threads);
                        return;
                    }
                    let fit = (room(others).saturating_sub(old) / 8).saturating_sub(crate::fpset::OVERFLOW);
                    let n = seen.slots();
                    slots = if fit >= n + n / 4 { fit } else { n };
                    seen.cap(slots);
                }
            }
        }
        if slots <= seen.slots() && seen.rotatable() {
            // (At its limit, the budget aside: `-spill always`.)
            self.rotate_seen(crew, threads);
            return;
        }
        // SAFETY: every active worker is parked, the others hold no
        // reference into the set; other threads only read its length.
        unsafe { seen.grow_to(crew, threads, slots) };
    }

    /// Stage 5 of memory pressure with the disk tier: rotate the seen set's
    /// table to disk (see `fpset`). The tables (the one that becomes the
    /// old table, and the new one) share the room the budget leaves (at
    /// least `1 / TABLES_SHARE` of the budget, whatever the other
    /// components hold): the new table gets half of it if the old one fits
    /// beside, else what is
    /// left beside the old one if that is at least a quarter of the room,
    /// else (the old table is then dropped) half of it; at least
    /// `ROTATE_MIN_SLOTS` (or the set's limit, if less), at most the limit.
    /// An IO error stops the search.
    fn rotate_seen(&self, crew: Option<&Crew<'_>>, threads: usize) {
        let seen = &self.seen;
        let limit = seen.limit();
        let floor = ROTATE_MIN_SLOTS.min(limit);
        let cur = seen.slots();
        let (slots, keep) = if self.budget.limited() {
            let others = self.budget.used(self.accounted()).saturating_sub(seen.bytes());
            // (The runs' Bloom filters and indexes stay; the next run's
            // come. The other components gave back what they could: the
            // tables get at least a quarter of the budget, else most
            // lookups would go to disk.)
            let total = self.budget.total();
            let room = total.saturating_sub(others + seen.index_bytes() + seen.next_run_bytes()).max(total / TABLES_SHARE);
            let of = |bytes: usize| (bytes / 8).saturating_sub(crate::fpset::OVERFLOW);
            let half = of(room / 2).clamp(floor, limit.max(floor));
            let beside = of(room.saturating_sub(FpSet::table_bytes(cur)));
            if FpSet::table_bytes(cur) + FpSet::table_bytes(half) <= room {
                (half, true)
            } else if beside >= floor.max(half / 2) {
                (beside.min(limit.max(floor)), true)
            } else {
                (half, false)
            }
        } else {
            (cur.clamp(floor, limit.max(floor)), true)
        };
        // SAFETY: every active worker is parked (or none runs), the others
        // hold no reference into the set; other threads only read its length.
        if let Err(e) = unsafe { seen.rotate(crew, threads, slots, keep) } {
            self.fail(Outcome::Io(e.0), NO_PARENT);
        }
    }

    /// Insert `fp` into the seen set while no worker runs (initial states,
    /// resuming), making room in it as a safepoint would (`grow_seen`).
    /// Err: it is full (or its disk tier failed).
    fn insert_exclusive(&self, fp: u64) -> Result<bool, Full> {
        let seen = &self.seen;
        loop {
            let mut high = false;
            match seen.insert(fp, &mut 0, || high = true) {
                Ok(new) => {
                    if high {
                        self.grow_seen(None);
                    }
                    return Ok(new);
                }
                Err(Full) => {
                    let epoch = seen.epoch();
                    if seen.can_make_room() {
                        self.grow_seen(None);
                    }
                    if seen.epoch() == epoch {
                        return Err(Full);
                    }
                }
            }
        }
    }

    /// Stage 1 of memory pressure for the archive: its segments go to disk
    /// (if its states are encoded and the disk may be used), else it is
    /// dropped (every worker drops its part at its next check). Whether
    /// this happened now.
    fn relieve_archive(&self) -> bool {
        let r = &self.retention;
        if !r.on || r.off() || self.frontier.archive_spilling() {
            return false;
        }
        self.frontier.spill_archive() || r.drop_archive()
    }

    /// Register the components' gauges with the budget.
    fn with_meters(mut self) -> Self {
        let b = &mut self.budget;
        b.register(Component::FpSet, self.seen.gauge().clone());
        b.register(Component::Archive, self.frontier.archive_mem().clone());
        b.register(Component::Frontier, self.frontier.queue_mem().clone());
        b.register(Component::Caches, Arc::new(cache_mem::gauge()));
        if let Some(o) = &self.order {
            b.register(Component::Candidates, o.gauge().clone());
        }
        // (The workers publish their parts, see `Slot`.)
        b.register(Component::TraceLogs, Arc::new(Gauge::new()));
        b.register(Component::LiveEdges, Arc::new(Gauge::new()));
        self
    }

    /// The memory the components of the search account for (bytes).
    fn accounted(&self) -> usize {
        self.budget.accounted()
    }

    /// Stage 4 of memory pressure, after compressing: the queue's segments
    /// go to disk (the workers write the next level out, the current one
    /// goes now). Whether they do.
    fn spill_frontier(&self) -> bool {
        let f = &self.frontier;
        if f.queue_spilling() || f.spill_queue(true) {
            f.spill_tail();
            return true;
        }
        false
    }

    /// Stage 4 of memory pressure: the workers write the full segments of
    /// their representatives' candidates (VIEW/SYMMETRY, a whole level of
    /// new states) to disk from now on. Whether this started now.
    fn spill_candidates(&self) -> bool {
        self.opts.spill.enabled() && self.order.as_ref().is_some_and(|o| o.spill(true))
    }

    /// The memory of the workers' trace logs and liveness edges (bytes).
    fn log_bytes(&self) -> usize {
        let m = self.budget.meters();
        m.bytes(Component::TraceLogs) + m.bytes(Component::LiveEdges)
    }

    /// Stages 2 and 3 of memory pressure: the trace logs, then (`both`, or
    /// if they are spilled already) the liveness edges go to disk. Whether
    /// a stage started (false if both had, or the disk may not be used).
    fn start_spilling(&self, both: bool) -> bool {
        if !self.opts.spill.enabled() {
            return false;
        }
        let mut started = false;
        if !self.spill_logs.swap(true, Ordering::Relaxed) {
            self.budget.reach(Stage::TraceLog);
            started = true;
            if !both {
                return true;
            }
        }
        if self.live_atoms.is_some() && !self.spill_edges.swap(true, Ordering::Relaxed) {
            self.budget.reach(Stage::LiveEdges);
            started = true;
        }
        started
    }

    /// Apply the memory budget (at the start of the search, then on the
    /// monitor thread): over budget, the components give memory back in
    /// the order of `crate::mem` (the fingerprint set's stage applies when
    /// it grows).
    fn relieve(&self) {
        let b = &self.budget;
        if !b.limited() {
            return;
        }
        if b.stage() != Stage::None {
            // Under pressure, what the components wrote to disk or dropped
            // is freed to the allocator: have it return that to the OS, so
            // that the resident memory shows it (the budget counts at least
            // the resident memory).
            crate::mem::purge();
        }
        b.sample();
        let mut used = b.used(self.accounted());
        let total = b.total();
        if used > total && b.stage() == Stage::None {
            // Before the first stage: the allocator keeps freed memory for
            // a while (the CLI sets a long purge delay); what it returns
            // may be all the excess.
            crate::mem::purge();
            b.sample();
            used = b.used(self.accounted());
        }
        if used <= total {
            // (Some slack before compressing, and spilling, no more.)
            if used < total / 8 * 7 && self.opts.spill.mode() != SpillMode::Always {
                if self.frontier.squeezed() {
                    self.frontier.squeeze(false);
                    self.frontier.spill_queue(false);
                }
                // (As the queue: candidates already on disk stay there.)
                if let Some(o) = &self.order {
                    o.spill(false);
                }
            }
            return;
        }
        if self.relieve_archive() {
            // (The next period sees what this freed: the workers write the
            // archive out at their next tick, and segments it shares with
            // other blocks, e.g. those kept for the liveness edges of a
            // resumed search, stay.)
            b.reach(Stage::Archive);
            return;
        }
        // The evaluation caches (memo tables) give back half their
        // allowance (with the archive's stage: they are only caches).
        let caches = b.meters().bytes(Component::Caches);
        if caches > 0 && cache_mem::shrink() {
            b.reach(Stage::Archive);
            if used.saturating_sub(caches / 2) <= total {
                return;
            }
        }
        // Stages 2 and 3: the logs to disk, one stage per period of the
        // monitor (so that the next one sees the effect). Without the disk,
        // they are only recorded.
        if self.opts.spill.enabled() {
            if self.start_spilling(false) {
                return;
            }
        } else {
            b.reach(if self.live_atoms.is_some() { Stage::LiveEdges } else { Stage::TraceLog });
        }
        // Stage 4: the queue's new blocks are compressed, and the
        // representatives' candidates (VIEW/SYMMETRY) go to disk; if that is
        // not enough (the next period), the queue's segments go to disk.
        b.reach(Stage::Frontier);
        if self.spill_candidates() {
            return;
        }
        if !self.frontier.squeezed() {
            self.frontier.squeeze(true);
            return;
        }
        if self.spill_frontier() {
            return;
        }
        // Every stage is reached: what is left over budget the components
        // cannot write out (the representatives' candidates of a wide
        // level, say). The fingerprint set's old table is only a cache of
        // its run on disk: it goes, at the next safepoint.
        if self.seen.old_bytes() > 0 {
            self.control().request(SP_DROP_OLD);
        }
        // Near the memory the process can have, the kernel would kill it:
        // stop instead, keeping the last checkpoint to recover with more.
        if let Some(mut why) = over_ceiling(used, total, crate::mem::physical_bytes()) {
            if self.opts.checkpoint.as_ref().is_some_and(|c| c.keep_last()) {
                why.push_str(", recovering the last checkpoint, which is kept");
            }
            self.fail(Outcome::Io(why), NO_PARENT);
        }
    }

    /// The test safepoint: nothing changes the seen set while it lasts.
    fn test_safepoint(&self, crew: &Crew<'_>) {
        let n = self.seen.len();
        crew.broadcast(|_| {
            for _ in 0..64 {
                std::hint::spin_loop();
            }
            assert_eq!(self.seen.len(), n, "a worker inserted a state during a safepoint");
        });
        TEST_SAFEPOINTS.fetch_add(1, Ordering::SeqCst);
    }

    /// States generated so far by the workers (and before the resume point
    /// this search resumed from, if any).
    fn worker_generated(&self) -> u64 {
        self.base_generated + self.slots.iter().map(|s| s.generated.load(Ordering::Relaxed)).sum::<u64>()
    }

    /// The deepest level reached so far.
    fn depth(&self) -> u64 {
        let init = (self.init_generated.load(Ordering::Relaxed) > 0) as u64;
        self.slots.iter().map(|s| s.max_depth.load(Ordering::Relaxed)).max().unwrap_or(0).max(init).max(self.base_depth as u64)
    }
}

impl<M: Model> Shared<'_, M> {
    /// Record the path to new state `s` (log entry `at`, at `depth`), found
    /// by `action` from the state of path `parent` (if the model uses
    /// `TLCExt!Trace`).
    pub(super) fn note_path(&self, at: LogRef, depth: u32, s: &M::State, action: Option<u32>, parent: Option<Arc<live::PathNode>>) {
        if let Some(p) = &self.paths {
            let values = self.model.state_values(s).expect("a model that uses TLCExt!Trace has state values");
            p.lock().insert(at, depth, Arc::new(live::PathNode { values, action, parent }));
        }
    }

    /// The path to the state of log entry `at`, if the model uses
    /// `TLCExt!Trace`.
    fn path_of(&self, at: LogRef) -> Option<live::CurrentPath> {
        self.paths.as_ref().map(|p| p.lock().get(at).map_or(live::CurrentPath::Unavailable, live::CurrentPath::Known))
    }

    /// `f` with the path to the state of log entry `at` as the current
    /// path (`live::with_path`), if the model uses `TLCExt!Trace`.
    fn with_path_of<R>(&self, at: LogRef, f: impl FnOnce() -> R) -> R {
        match self.path_of(at) {
            Some(p) => live::with_path(Some(p), f),
            None => f(),
        }
    }
}

impl<M: Model> live::Source for Shared<'_, M> {
    fn snapshot(&self) -> LiveStats {
        let queued = self.frontier.queued();
        LiveStats {
            generated: self.init_generated.load(Ordering::Relaxed) + self.worker_generated(),
            distinct: self.seen.len() as u64,
            queue: queued,
            // As TLC: 1 while the initial states are computed.
            diameter: self.depth().max(1),
            initial: self.init_distinct.load(Ordering::Relaxed),
            duration_secs: self.start.elapsed().as_secs(),
        }
    }
}

/// The failure, if any, of checking initial state `s` (logged at `at`):
/// invariants, then the state-predicate parts of the properties.
fn init_failure<M: Model>(model: &M, s: &M::State, at: LogRef) -> Option<Failure> {
    let failure = invariant_failure(model, s, at).or_else(|| match model.check_init_property(s) {
        Ok(None) => None,
        Ok(Some(p)) => Some((Outcome::InitPropertyViolated(p), at)),
        Err(e) => Some((Outcome::Error(e), at)),
    });
    match failure {
        Some((Outcome::Error(e), at)) => Some((Outcome::Error(e.on_initial_state(model, s)), at)),
        f => f,
    }
}

/// The failure, if any, of checking the invariants of state `s` (logged at `at`).
fn invariant_failure<M: Model>(model: &M, s: &M::State, at: LogRef) -> Option<Failure> {
    match model.check_invariants(s) {
        Ok(None) => None,
        Ok(Some(i)) => Some((Outcome::InvariantViolated(model.invariant_names()[i].clone()), at)),
        Err(e) => Some((Outcome::Error(e), at)),
    }
}

pub fn explore<M: Model>(model: &M, opts: &Options) -> Report<M::State> {
    explore_resumable(model, opts, None, None).0
}

/// `explore`, watched by `observer` (see `SearchObserver`).
pub fn explore_observed<M: Model>(model: &M, opts: &Options, observer: &dyn SearchObserver<M::State>) -> Report<M::State> {
    search(model, opts, Start::Init, None, Some(observer)).0
}

/// Where a search starts.
#[allow(clippy::large_enum_variant)] // one per search, passed by value once
pub enum Start<'r, S> {
    /// From the initial states.
    Init,
    /// From a resume point (see `explore_resumable`).
    Resume(ResumePoint<S>),
    /// From a checkpoint (`-recover`): as the checkpointed search would
    /// have gone on (counts, depth, traces).
    Recover(&'r Recovery),
}

/// `explore`, optionally resumed from a resume point (`from`; its states are
/// not checked again), and keeping the states it is done with in an archive
/// of at most `retain` bytes (if given) so that a search stopped by an
/// evaluation error can be resumed: the resume point is returned then
/// (unless the archive was dropped because disk was unavailable, or
/// the model generated states outside `successors`, see
/// `Model::extra_generated`).
pub fn explore_resumable<M: Model>(
    model: &M,
    opts: &Options,
    from: Option<ResumePoint<M::State>>,
    retain: Option<usize>,
) -> (Report<M::State>, Option<ResumePoint<M::State>>) {
    explore_from(model, opts, from.map_or(Start::Init, Start::Resume), retain)
}

/// `explore_resumable`, starting from `from`.
pub fn explore_from<M: Model>(
    model: &M,
    opts: &Options,
    from: Start<'_, M::State>,
    retain: Option<usize>,
) -> (Report<M::State>, Option<ResumePoint<M::State>>) {
    search(model, opts, from, retain, None)
}

/// `explore_from`, watched by `observer` if given.
fn search<'m, M: Model>(
    model: &'m M,
    opts: &'m Options,
    from: Start<'_, M::State>,
    retain: Option<usize>,
    observer: Option<&'m dyn SearchObserver<M::State>>,
) -> (Report<M::State>, Option<ResumePoint<M::State>>) {
    let start = Instant::now();
    let mut run = run::prepare(model, opts, &from, retain, observer, start);
    // (Worker 0's queue is the first level; it is created after the
    // search's structures it borrows.)
    let mut seed = run.shared.frontier.local(0, run.archiving);
    let (init_logs, init_err) = match run::init(&run.shared, &mut seed, &mut run.stats, from) {
        Ok(r) => r,
        Err(e) => return (finish::in_init_failed(&run, e), None),
    };
    let in_init = init_err.is_some();
    if let Some((o, at)) = init_err {
        run.shared.fail(o, at);
    } else if let (Some(p), 0) = (&opts.progress, run.shared.base_depth) {
        (p.init_done)(run.stats.init_generated, run.stats.init_distinct);
    }
    // (Before the first state is expanded: an observer may stop the search.)
    if !run.shared.control().stopped() {
        run.shared.observer_stops();
    }

    let outs = run::workers(&run, seed, init_logs);
    finish::finalize(run, outs, in_init)
}

/// The seen set of a search: with a disk tier unless the disk may not be
/// used or the table has a fixed size (`-fpmem`); with `-spill always`,
/// a small table that rotates to disk early (testing).
fn fp_set(opts: &Options) -> FpSet {
    let mut config = opts.fp.within(opts.maxmem);
    if config.fixed || !opts.spill.enabled() {
        return FpSet::with_config(config);
    }
    if opts.spill.mode() == SpillMode::Always {
        config = config.forced_disk();
    }
    FpSet::with_config(config).with_disk(opts.spill.clone())
}

/// What `init_phase` and `resume_phase` produce: the trace logs to continue
/// (per worker; worker 0's only for the initial states) and the first failure.
type InitResult = Result<(Vec<TraceLog>, Option<Failure>), ModelError>;

/// Generate the initial states on this thread: constraints, seen set and
/// invariants. Distinct ones go to `seed` (worker 0's next level: the first
/// level of the search) and get entries in the returned trace log (the
/// start of worker 0's log).
/// Also returns the first failure.
fn init_phase<M: Model>(shared: &Shared<'_, M>, seed: &mut Local<'_, '_, M::State>, stats: &mut Stats) -> InitResult {
    let model = shared.model;
    let observer = shared.observer;
    let mut log = TraceLog::new(shared.opts.queue.seg_bytes);
    let mut err = None;
    // An error of the observer (`SearchObserver::on_init`).
    let mut observed = None;
    // The distinct initial states, in order (choosing representatives in
    // BFS order).
    let mut seq = Vec::new();
    // Whether an observer stopped the search (`SearchObserver::stop`).
    let mut stopped = false;
    let generated = model.init_states_while(&mut |s| {
        if err.is_some() || observed.is_some() {
            // DoInitFunctor keeps enumerating after FingerprintException
            // (catch(Throwable)), unlike EvalException / TLCRuntimeException.
            // Later states count but are neither fingerprinted nor checked.
            if matches!(&err, Some((Outcome::Error(e), _)) if e.kind == crate::ErrorKind::FunctionDomain) {
                stats.init_generated += 1;
                shared.init_generated.store(stats.init_generated, Ordering::Relaxed);
            }
            return true;
        }
        stats.init_generated += 1;
        shared.init_generated.store(stats.init_generated, Ordering::Relaxed);
        let in_model = match model.constraint(&s) {
            Ok(b) => b,
            Err(e) => {
                err = Some((Outcome::Error(e.on_initial_state(model, &s)), NO_PARENT));
                return true;
            }
        };
        let fp = model.fingerprint(&s);
        if !in_model {
            // Not added to the seen set, but invariants are still checked.
            let lr = log_ref(0, log.push(NO_PARENT, fp));
            if let Some(o) = observer {
                o.on_new_state(&s, fp, 1, None);
            }
            err = init_failure(model, &s, lr);
            return true;
        }
        // (The workers have not started yet.)
        match shared.insert_exclusive(fp) {
            Ok(true) => {
                let lr = log_ref(0, log.push(NO_PARENT, fp));
                if shared.order.is_some() {
                    seq.push(lr);
                }
                stats.init_distinct += 1;
                shared.init_distinct.store(stats.init_distinct, Ordering::Relaxed);
                // As TLC, the state is queued before it is checked (this
                // shows in `TLCGet("queue")`).
                let t = s.clone();
                shared.note_path(lr, 1, &s, None, None);
                seed.push_new(Task { state: s, log: lr, depth: 1 });
                if let Some(o) = observer {
                    o.on_new_state(&t, fp, 1, None);
                }
                // TLC's DoInitFunctor calls LiveCheck.addInitState after
                // enqueueing a new state, before checking its invariants.
                if let Some(o) = observer {
                    observed = o.on_init(&t, stats.init_generated - 1).err();
                }
                if observed.is_none() {
                    err = init_failure(model, &t, lr);
                }
                if stats.init_distinct.is_multiple_of(INIT_TICK) && shared.budget.limited() && err.is_none() {
                    err = init_relieve(shared, seed, &mut log);
                }
                if let (Some(o), None) = (observer, &err) {
                    stopped = observed.is_none() && o.stop(true, stats.init_distinct);
                }
            }
            Ok(false) => {}
            Err(_) => err = Some(fp_set_full(&shared.seen)),
        }
        !stopped
    });
    if stopped {
        shared.halted.store(true, Ordering::Relaxed);
        shared.control().stop();
    }
    // TLC stops generating initial states at the first failure (an
    // invariant violated by an initial state): an error the model raises
    // in an initial state it would have generated later is not reached.
    if err.is_none() {
        generated?;
        if let Some(e) = observed {
            return Err(e);
        }
    }
    if let Some(o) = &shared.order {
        o.start(Arc::new(Positions::of_seq(&seq)));
    }
    Ok((vec![log], err))
}

/// Initial states between two applications of the memory budget while
/// they are generated (`init_relieve`).
const INIT_TICK: u64 = 1 << 14;

/// Apply the memory budget while the initial states are generated (on this
/// thread: the budget monitor starts with the workers), so that many
/// initial states are subject to the pressure stages as the states of a
/// level are: the queued ones are compressed and go to disk, and so do the
/// full blocks of their trace log. A failure if a write failed.
fn init_relieve<M: Model>(shared: &Shared<'_, M>, seed: &mut Local<'_, '_, M::State>, log: &mut TraceLog) -> Option<Failure> {
    shared.relieve();
    seed.spill();
    let spill = &shared.opts.spill;
    if shared.spill_logs.load(Ordering::Relaxed) {
        if let Err(e) = log.spill(spill, false) {
            return Some((Outcome::Io(e.0), NO_PARENT));
        }
    }
    spill.error().map(|e| (Outcome::Io(e.0), NO_PARENT))
}

/// Why a search over its budget `total` stops, holding `used` bytes of the
/// `limit` the process can have (its control group's, else the machine's):
/// within a margin of it (1/16, at least 2 GiB: memory grows between the
/// budget's looks every 50 ms), the kernel would kill the process next.
fn over_ceiling(used: usize, total: usize, limit: usize) -> Option<String> {
    const MIB: usize = 1 << 20;
    let margin = (limit / 16).max(2 << 30);
    if used <= total || used < limit.saturating_sub(margin) {
        return None;
    }
    Some(format!(
        "out of memory: the process holds {} MiB, within {} MiB of the {} MiB it can have, past its budget of {} MiB (-maxmem); \
         what it cannot write to disk (the representatives' candidates of a wide level, say) grew past the budget: rerun with more memory",
        used / MIB,
        margin / MIB,
        limit / MIB,
        total / MIB
    ))
}

/// Apply the memory budget every 50 ms (`Shared::relieve`) until `done`.
fn budget_monitor<M: Model>(shared: &Shared<'_, M>, done: &tlx_base::par::Done) {
    tlx_base::par::every(Duration::from_millis(50), done, || shared.relieve());
}

/// Report progress at `p.first`, then every `p.every`, until `done`.
fn progress_monitor<M: Model>(shared: &Shared<'_, M>, p: &Progress, done: &tlx_base::par::Done) {
    let mut next = p.first;
    tlx_base::par::every(Duration::from_millis(50), done, || {
        if shared.start.elapsed() >= next && !done.is_set() {
            (p.report)(&live::Source::snapshot(shared));
            next += p.every.max(Duration::from_millis(100));
        }
    });
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ceilings() {
        const G: usize = 1 << 30;
        // RS_pack_zombie2: 58 GiB held of 58.5, past a 46.8 GiB budget.
        let why = over_ceiling(58 * G, 46 * G, 58 * G + G / 2).expect("stops");
        assert!(why.starts_with("out of memory: the process holds 59392 MiB, within 3744 MiB of the 59904 MiB"), "{why}");
        // Within budget, or with room left before the margin: it goes on.
        assert_eq!(over_ceiling(58 * G, 59 * G, 58 * G + G / 2), None);
        assert_eq!(over_ceiling(54 * G, 46 * G, 58 * G + G / 2), None);
        // A small limit keeps a margin of 2 GiB.
        assert!(over_ceiling(7 * G, 6 * G, 8 * G).is_some());
        assert_eq!(over_ceiling(6 * G - 1, 5 * G, 8 * G), None);
    }

    #[test]
    fn keep_last_without_a_checkpoint() {
        assert!(!Checkpointer::new(CheckpointConfig::default()).keep_last());
    }
}
