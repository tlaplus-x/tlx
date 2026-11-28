//! The phases of a search before and while its workers expand states:
//! preparation, the initial states and the worker scope (`super::search`
//! sequences them with the finalization in `super::finish`).
//!
//! `prepare` reads the options into the search's shared state (`Shared`);
//! `init` computes the initial states, or resumes from a resume point, or
//! adopts and recovers from a checkpoint; `workers` runs the monitors and
//! the workers of the first level in one scope, so that a panicking worker
//! releases the barrier and the safepoints (`Shared::abort`) and the
//! monitors stop before the panic propagates.

use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize};
use std::time::Instant;

use parking_lot::Mutex;

use super::checkpoint::{recover_phase, CkptRun};
use super::frontier::{Frontier, Local};
use super::history::History;
use super::levels::Levels;
use super::order::Order;
use super::resume::{resume_phase, BaseCounters, Retention};
use super::safepoint::Safepoint;
use super::tracelog::TraceLog;
use super::worker::{run_worker, Slot, WorkerOut};
use super::{
    abort_on_panic, budget_monitor, coverage, fp_set, init_phase, join_all, progress_monitor, InitResult, Options, Outcome, ParkedRoots,
    PathTable, SearchObserver, Shared, Start, Stats, NO_PARENT,
};
use crate::cache_mem;
use crate::io::SpillMode;
use crate::live;
use crate::mem::MemBudget;
use crate::model::Model;
use crate::queue::Mem;
use crate::stats;

/// A prepared search: the shared state its workers use, its statistics and
/// the run-scoped values its later phases need (`prepare`; `init` and
/// `workers` add to them and `finish::finalize` consumes them).
pub(super) struct Run<'m, M: Model> {
    pub(super) shared: Shared<'m, M>,
    /// The statistics of the run (empty until the phases fill them).
    pub(super) stats: Stats,
    /// The memory the components accounted for before the first state was
    /// expanded (`stats::levels_snapshot`).
    pub(super) levels0: Vec<u64>,
    /// The archive retains the states the search is done with
    /// (`Retention`): the workers take their parts with it.
    pub(super) archiving: bool,
    /// The search resumes from a resume point (`Start::Resume`): the states
    /// of the levels before it are not evaluated again.
    pub(super) resumed: bool,
    /// `Model::extra_generated` before the search: the states the model
    /// generated outside `successors` during it are the difference.
    pub(super) extra_at_start: u64,
    /// RAII guard marking the model's value store as GC-managed for this run.
    pub(super) _store_gc_guard: Option<Box<dyn std::any::Any + Send + Sync>>,
}

/// The first phase: read `opts` into the search's shared state and the
/// values its later phases need, without touching the model.
pub(super) fn prepare<'m, M: Model>(
    model: &'m M,
    opts: &'m Options,
    from: &Start<'_, M::State>,
    retain: Option<usize>,
    observer: Option<&'m dyn SearchObserver<M::State>>,
    start: Instant,
) -> Run<'m, M> {
    // (A quiet search leaves the run's statistics and caches alone.)
    let quiet = observer.is_some_and(|o| o.quiet());
    if !quiet {
        stats::set_names(model.action_names(), model.invariant_names(), model.action_property_names());
    }
    let levels0 = stats::levels_snapshot();
    if !quiet {
        stats::search_start(match from {
            Start::Resume(c) => Some(c.level()),
            Start::Init | Start::Recover(_) => None,
        });
    }
    let extra_at_start = model.extra_generated();
    let nworkers = opts.workers.max(1);
    let base = match from {
        Start::Init => BaseCounters::none(),
        Start::Resume(c) => c.base.clone(),
        Start::Recover(r) => r.base().clone(),
    };
    let (base_generated, base_depth, base_outdegree) = (base.generated_after_init, base.depth, base.outdegree);
    let counting = opts.coverage;
    // (A resumed search records the edges of the levels before its resume
    // point after the search, expanding their states again.) Counting the
    // coverage with several workers, the representatives are chosen in BFS
    // order (`order`), and the graph is recorded unless the fingerprint
    // identifies a class of states (VIEW, SYMMETRY: liveness does not use
    // it then). (Nor for an observer that evaluates the liveness
    // predicates itself.)
    let live_atoms = if counting && nworkers > 1 && model.coarse_fingerprint() || observer.is_some_and(|o| !o.records_live_graph()) {
        None
    } else {
        model.caps().live_atoms
    };
    let resumed = matches!(from, Start::Resume(_));
    // (Under VIEW or SYMMETRY, not when recording the behavior graph, which
    // liveness does not use then.)
    let order = (nworkers > 1 && (counting || model.coarse_fingerprint() && live_atoms.is_none())).then(|| Order::new(nworkers));
    if let (Some(o), SpillMode::Always) = (&order, opts.spill.mode()) {
        o.spill(true);
    }
    // The coverage counters: per worker, generated and distinct per action.
    let cov_len = if counting { 2 * model.action_names().len() } else { 0 };
    let mut cov_base = vec![0; cov_len];
    if counting {
        coverage::add(&mut cov_base, &base.coverage);
    }
    // The archive's memory: carried over from the resume point.
    let archive_mem = match from {
        Start::Resume(c) => c.mem(),
        _ => Mem::new(opts.queue.seg_bytes, false),
    };
    // (Checkpoints need a way to write the states.)
    let ckpt = opts.checkpoint.clone().filter(|_| model.caps().format.is_some()).map(|c| CkptRun::new(c, nworkers, extra_at_start));
    let store_gc = model.caps().gc;
    let store_gc_guard = store_gc.map(|gc| gc.enter_scope());
    let shared = Shared {
        model,
        opts,
        observer,
        quiet,
        halted: AtomicBool::new(false),
        seen: fp_set(opts),
        frontier: Frontier::new(nworkers, model.caps().codec(), opts.queue, archive_mem, &opts.spill),
        safepoint: Safepoint::new(nworkers),
        slots: (0..nworkers).map(|_| Slot { cov: (0..cov_len).map(|_| AtomicU64::new(0)).collect(), ..Slot::default() }).collect(),
        init_generated: AtomicU64::new(0),
        init_distinct: AtomicU64::new(0),
        start,
        failure: Mutex::new(None),
        levels: Levels::new(nworkers),
        order,
        retention: Retention::new(retain),
        budget: MemBudget::new(opts.maxmem),
        base_generated,
        base_depth,
        base_outdegree,
        safepoint_every: opts.safepoint_every,
        live_atoms,
        periodic: live_atoms.filter(|a| observer.is_none() && a.live_input().is_some()).map(|_| super::periodic::Periodic::new()),
        live_pre: Mutex::new(Vec::new()),
        spill_logs: AtomicBool::new(opts.spill.mode() == SpillMode::Always),
        spill_edges: AtomicBool::new(opts.spill.mode() == SpillMode::Always),
        ckpt,
        history: Mutex::new(History::new()),
        cov_base,
        paths: model.uses_trace().then(|| Mutex::new(PathTable::default())),
        store_gc,
        gc_roots: (0..nworkers).map(|_| Mutex::new(ParkedRoots::default())).collect(),
        mid_task_parked: AtomicUsize::new(0),
        store_gc_epoch: AtomicU64::new(0),
        store_gc_drop_archive: AtomicBool::new(false),
    }
    .with_meters();

    // The evaluation caches' part of the budget, shared by the workers.
    if !quiet {
        cache_mem::set_allowance(if opts.maxmem == usize::MAX { usize::MAX } else { opts.maxmem / cache_mem::BUDGET_FRACTION }, nworkers);
    }
    if opts.spill.mode() == SpillMode::Always {
        // (Testing: the segments of the queue and the archive go to disk
        // from the start.)
        shared.frontier.squeeze(true);
        shared.frontier.spill_queue(true);
        if shared.retention.on {
            shared.frontier.spill_archive();
        }
    }
    // (A budget too small from the start applies its stages at once: one
    // per call, as the monitor does every period.)
    for _ in 0..5 {
        shared.relieve();
    }
    let archiving = shared.retention.on && !shared.retention.off();
    Run { shared, stats: Stats::default(), levels0, archiving, resumed, extra_at_start, _store_gc_guard: store_gc_guard }
}

/// The second phase: the initial states (checked and queued in `seed`), or
/// the states of the resume point, or those of the checkpoint the search
/// recovers from. Err: an error while computing the initial states, which
/// reports the statistics so far and no behavior.
pub(super) fn init<'m, M: Model>(
    shared: &Shared<'m, M>,
    seed: &mut Local<'_, 'm, M::State>,
    stats: &mut Stats,
    from: Start<'_, M::State>,
) -> InitResult {
    match from {
        Start::Resume(c) => resume_phase(shared, seed, stats, c),
        Start::Recover(r) => {
            // (The recovered checkpoint goes when this run ends, as its own;
            // the metadir is locked first: another run may use it.)
            match shared.ckpt.as_ref().map_or(Ok(()), |c| c.ck.adopt(&shared.opts.spill)) {
                Ok(()) => {
                    let r = recover_phase(shared, seed, stats, r);
                    stats::add_secs("recovery from a checkpoint", shared.start.elapsed());
                    r
                }
                Err(e) => Ok((Vec::new(), Some((Outcome::Io(e), NO_PARENT)))),
            }
        }
        Start::Init => {
            let r = live::with_source(shared, || init_phase(shared, seed, stats));
            if !shared.quiet {
                stats::add_secs("initial states", shared.start.elapsed());
            }
            r
        }
    }
}

/// The third phase: the monitors and the workers of the first level in one
/// scope. `seed` is worker 0's queue, filled by `init` with the first
/// level; the other workers take theirs from the frontier.
pub(super) fn workers<'m, M: Model>(
    run: &Run<'m, M>,
    mut seed: Local<'_, 'm, M::State>,
    init_logs: Vec<TraceLog>,
) -> Vec<WorkerOut<'m, M::State>> {
    let shared = &run.shared;
    let archiving = run.archiving;
    let opts = shared.opts;
    let nworkers = shared.slots.len();
    if shared.budget.limited() {
        // Evaluating the initial states may have built large values (e.g. the
        // set an `x \in S` enumerates), freed by now: return their memory
        // before the workers allocate theirs.
        crate::mem::purge();
    }
    // The first level, expanded by all workers.
    seed.advance();
    let monitor_done = tlx_base::par::Done::new();
    // Existing shard IDs remain stable when the worker count changes.
    shared.history.lock().prepare(init_logs, nworkers, shared.live_atoms, opts.queue.seg_bytes);
    let mut seed = Some(seed);
    std::thread::scope(|sc| {
        let monitor_done = &monitor_done;
        if let Some(p) = &opts.progress {
            tlx_base::stack::spawn_default(sc, move || progress_monitor(shared, p, monitor_done));
        }
        if let (Some(c), true) = (&opts.coverage_report, opts.coverage) {
            tlx_base::stack::spawn_default(sc, move || coverage::coverage_monitor(shared, c, monitor_done));
        }
        if shared.budget.limited() {
            tlx_base::stack::spawn_default(sc, move || budget_monitor(shared, monitor_done));
        }
        let handles: Vec<_> = (0..nworkers)
            .map(|id| {
                let local = if id == 0 { seed.take().unwrap() } else { shared.frontier.local(id, archiving) };
                let shard = shared.history.lock().take(id);
                tlx_base::stack::spawn_eval(sc, move || abort_on_panic(|| shared.abort(), || run_worker(shared, id, local, shard)))
            })
            .collect();
        // A panicking worker (e.g. a TLX_PARANOID mismatch) stops the
        // others; the monitor stops before the panic propagates.
        let outs = join_all(handles, || monitor_done.set());
        monitor_done.set();
        outs
    })
}
