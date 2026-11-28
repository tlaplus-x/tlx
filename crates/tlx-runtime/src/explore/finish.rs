//! The finalization of a search (`super::search` runs it after
//! `super::run::workers`): reduce the workers' results into the statistics,
//! take the first failure, rebuild its trace, retain a resume point and
//! build the behavior graph of a complete search (`live_graph_of`).
//!
//! The failure precedence is the one the search relied on: the first
//! failure a worker recorded, else a write that failed after the workers'
//! last check, else a failure of the graph's own building (an atom on a
//! state of the levels before a resume point, or reading its spilled edge
//! logs back).

use std::sync::atomic::Ordering;
use std::time::Instant;

use super::edges::{self, liveness_memory_error, AtomBits, LiveGraph};
use super::history::History;
use super::resume::{record_archived, resume_point, Pre};
use super::run::Run;
use super::tracelog::{rebuild_trace, TraceBuild, TraceLog, NO_PARENT};
use super::worker::WorkerOut;
use super::{Failure, Options, Outcome, OutdegreeHist, Report, ResumePoint, Shared, Stats, TraceStep};
use crate::cache_mem;
use crate::io::IoError;
use crate::live;
use crate::mem::{Component, Registry, Stage};
use crate::model::{Model, ModelError};
use crate::stats;

/// The last phase: the results of a search whose workers have stopped
/// (`outs`). `in_init`: it failed while computing (or checking) the initial
/// states.
pub(super) fn finalize<'m, M: Model>(
    run: Run<'m, M>,
    mut outs: Vec<WorkerOut<'m, M::State>>,
    in_init: bool,
) -> (Report<M::State>, Option<ResumePoint<M::State>>) {
    let Run { shared, mut stats, levels0, resumed, extra_at_start, _store_gc_guard, .. } = run;
    let start = shared.start;
    let model = shared.model;
    let opts = shared.opts;
    let observer = shared.observer;
    let quiet = shared.quiet;
    let counting = opts.coverage;
    let live_atoms = shared.live_atoms;
    let nworkers = shared.slots.len();
    let base_outdegree = shared.base_outdegree.clone();
    let mut outdegree = base_outdegree.clone();
    for o in &outs {
        stats.left += o.left as u64;
        outdegree.merge(&o.outdegree);
    }
    stats.outdegree = outdegree.summary();

    let extra = model.extra_generated() - extra_at_start;
    stats.generated = stats.init_generated + shared.worker_generated() + extra;
    let coverage = counting.then(|| shared.coverage());
    stats.distinct = shared.seen.len() as u64;
    stats.depth = if in_init { u32::from(stats.generated > 0) } else { shared.depth() as u32 };

    let mut failure = shared.failure.lock().take();
    if let (None, Some(e)) = (&failure, opts.spill.error()) {
        // (A write that failed after the workers' last check.)
        failure = Some((Outcome::Io(e.0), NO_PARENT));
    }
    if matches!(failure, Some((Outcome::FpSetFull { .. }, _))) && shared.budget.limited() && !opts.fp.fixed {
        // (Full at the limit the budget sets.)
        shared.budget.reach(Stage::FpSet);
    }
    // The liveness edges: of a complete search, or of one stopped by
    // `TLCSet("exit", TRUE)` (TLC checks the graph of the states it
    // expanded then); the graph is built below, once the search's
    // structures are freed.
    let exited = model.stop_requested();
    for out in &mut outs {
        shared.history.lock().put(std::mem::take(&mut out.shard));
    }
    let history = std::mem::replace(&mut *shared.history.lock(), History::new());
    let (logs, mut edges, all_edges) = history.into_parts();
    // (A quiet search's results only if its observer wants them.)
    let results = !quiet || observer.is_some_and(|o| o.complete_results());
    let graph_wanted = live_atoms.is_some()
        && failure.is_none()
        && !in_init
        && (stats.left == 0 || exited)
        && results
        && !shared.halted.load(Ordering::Relaxed);
    let build_graph = graph_wanted && all_edges && !edges.iter().any(|e| e.failed());
    // (The first worker's error: with several workers, TLC's would be
    // whichever fails first, too.)
    let mut live_error = if graph_wanted { edges.iter_mut().find_map(|e| e.take_error()) } else { None };
    let pre = std::mem::take(&mut *shared.live_pre.lock());
    // (Not after a resume, or a recovery that still owes pre-resume edges:
    // the levels before the resume point were expanded by an earlier search
    // without recording their liveness atoms.)
    let live_atoms_ok = live_atoms.is_some() && !resumed && pre.is_empty() && !in_init && all_edges && edges.iter().all(|e| !e.failed());
    let resumable = matches!(failure, Some((Outcome::Error(ref e), _)) if model.caps().resumes(e))
        && !in_init
        && shared.retention.on
        && !shared.retention.off()
        && extra == 0
        && outs.iter().all(|o| o.archive.is_some());
    let logs_spilled: usize = logs.iter().map(|l| l.spilled_blocks()).sum();
    let meters = shared.budget.meters();
    let frontier_peak = shared.frontier.peak_bytes().0;
    let mem = search_memory(&shared, levels0, &logs, &outs);
    let (outcome, trace, mut trace_note, trace_store_full) = failure_report(model, &shared, &logs, failure, results, resumable);
    let resume = resumable.then(|| keep_resume(&shared, &stats, &base_outdegree, opts, logs, outs));
    report_memory(&shared, meters, mem, resume.is_some(), logs_spilled);
    // The search ended (it was not killed): its checkpoint goes, unless the
    // model stopped on a recoverable resource limit (e.g. value-store budget),
    // trace reconstruction exhausted the store, the search is restarting after
    // a layout miss, or the caller deferred cleanup until post-search liveness
    // checking and replay complete.
    let interrupted = matches!(&outcome, Outcome::Error(e) if model.caps().interrupts(e));
    if let Some(c) = &opts.checkpoint {
        let keep = model.caps().keep_checkpoint() || trace_store_full;
        if keep {
            let kept = c.keep_last();
            if trace_store_full && kept {
                if let Some(note) = &mut trace_note {
                    note.push_str(", recovering the last checkpoint, which is kept");
                }
            }
        }
        if !c.finish_deferred() && (keep || !interrupted) {
            c.finish();
        }
    }
    // The search's structures (fingerprint set, queues, archive, trace
    // logs) are not needed by liveness: freed before it builds its graph.
    drop(shared);
    let (mut outcome, mut live_graph) = (outcome, None);
    if let (Some(atoms), true) = (live_atoms, build_graph) {
        match live_graph_of(model, atoms, edges, pre, nworkers, opts, exited) {
            Ok(g) => live_graph = g,
            Err(LiveStop::Atom(e)) => live_error = Some(e),
            // (Reading spilled edge logs back failed: the run fails, as
            // when the search's own IO fails.)
            Err(LiveStop::Io(e)) => outcome = Outcome::Io(e.0),
        }
    } else {
        drop((edges, pre));
    }
    drop(_store_gc_guard);
    // Pending requests can hold the last spill directory lease even when
    // exploration stops on a violation. Release them before returning.
    opts.spill.wait_for_writes();
    opts.spill.wait_for_reads();
    if matches!(outcome, Outcome::Ok) && live_error.is_none() {
        if let Some(e) = opts.spill.error() {
            outcome = Outcome::Io(e.0);
        }
    }
    (
        Report {
            stats,
            outcome,
            trace,
            trace_note,
            trace_store_full,
            elapsed: start.elapsed(),
            in_init,
            live_graph,
            live_error,
            live_atoms_ok,
            coverage,
            frontier_peak,
        },
        resume,
    )
}

/// The outcome of a search and the counterexample of its first failure, if
/// any: the trace rebuilt along the fingerprint chain (`rebuild_trace`), or
/// none if generation kept it from being rebuilt whole, or the results are
/// not wanted (`results`), with the note that it is incomplete.
fn failure_report<'m, M: Model>(
    model: &'m M,
    shared: &Shared<'m, M>,
    logs: &[TraceLog],
    failure: Option<Failure>,
    results: bool,
    resumable: bool,
) -> (Outcome, Vec<TraceStep<M::State>>, Option<String>, bool) {
    match failure {
        None => (Outcome::Ok, Vec::new(), None, false),
        Some((o, at)) => {
            let no_trace = matches!(&o, Outcome::Error(e) if e.is_store_full() || model.caps().interrupts(e));
            // When the search is not retaining a `ResumePoint`, the frontier and
            // archives are dead; trace reconstruction can sweep leftover search
            // nodes and reclaim transient replay allocations under `store_gc`.
            let replay_gc = (!resumable).then_some(shared.store_gc).flatten();
            let rebuilt = if no_trace || !results {
                Ok(TraceBuild::Unavailable)
            } else if model.coarse_fingerprint() {
                let snapshot = live::Source::snapshot(shared);
                live::with_source(&snapshot, || rebuild_trace(model, logs, at, &o, replay_gc))
            } else {
                rebuild_trace(model, logs, at, &o, replay_gc)
            };
            match rebuilt {
                Ok(TraceBuild::Rebuilt(rebuilt)) => {
                    (o, rebuilt.trace, (!rebuilt.complete).then(|| model.trace_replay_limit().map(str::to_owned)).flatten(), false)
                }
                Ok(TraceBuild::Unavailable) => (o, Vec::new(), None, false),
                Ok(TraceBuild::StoreFull(e)) => (o, Vec::new(), Some(format!("trace cannot be reconstructed: {}", e.message)), true),
                Err(e) => (Outcome::Io(format!("{e} (while rebuilding the trace of: {o:?})")), Vec::new(), None, false),
            }
        }
    }
}

/// The resume point that continues a search stopped by an evaluation error
/// (`resume_point`): the archive, the trace logs, the workers' parts and the
/// positions of the interrupted level.
fn keep_resume<'m, M: Model>(
    shared: &Shared<'m, M>,
    stats: &Stats,
    base_outdegree: &OutdegreeHist,
    opts: &Options,
    logs: Vec<TraceLog>,
    outs: Vec<WorkerOut<'m, M::State>>,
) -> ResumePoint<M::State> {
    let words = shared.frontier.words();
    let positions = shared.order.as_ref().map(|o| o.current());
    resume_point(
        stats,
        shared.base_generated,
        base_outdegree,
        &shared.cov_base,
        logs,
        outs,
        shared.frontier.archive_mem().clone(),
        words,
        opts.queue.seg_bytes,
        positions,
        shared.frontier.archive_spilling().then(|| opts.spill.clone()),
    )
}

/// The memory the search reports (the `-stats` memory block): the peaks of
/// its components and the archive it retained. None if this is not the run's
/// own search, or the statistics are off. Also reports the peak of the
/// representatives' candidates, which the memory block itself does not name.
fn search_memory<'m, M: Model>(
    shared: &Shared<'m, M>,
    levels0: Vec<u64>,
    logs: &[TraceLog],
    outs: &[WorkerOut<'m, M::State>],
) -> Option<stats::SearchMem> {
    let on = stats::on() && !shared.quiet;
    let meters = shared.budget.meters();
    let archive_peak = meters.peak(Component::Archive);
    if let (Some(_), true) = (&shared.order, on) {
        stats::set(
            &format!("{}representative candidates (VIEW/SYMMETRY, peak)", stats::MEMORY),
            stats::Metric::Bytes(meters.peak(Component::Candidates) as u64),
        );
    }
    on.then(|| stats::SearchMem {
        levels0,
        accounted: (shared.accounted(), shared.budget.accounted_peak()),
        queue_peak: shared.frontier.peak_bytes(),
        log_entries: logs.iter().map(|l| l.len()).sum(),
        log_bytes: logs.iter().map(|l| l.bytes()).sum(),
        archived: (!shared.retention.off()).then(|| outs.iter().filter_map(|o| o.archive.as_ref()).flatten().map(|b| b.len()).sum()),
        archive_peak,
        retaining: shared.retention.on,
        budget: shared.budget.limited().then(|| (shared.budget.total(), shared.budget.stage())),
    })
}

/// Report the memory and disk use of the search in the run's statistics
/// (`stats::search_done`): the fingerprint set and its disk tier, the spill
/// layer, and the evaluation caches. Nothing if `mem` is None (the search
/// has no memory report).
fn report_memory<'m, M: Model>(
    shared: &Shared<'m, M>,
    meters: &Registry,
    mem: Option<stats::SearchMem>,
    kept_resume: bool,
    logs_spilled: usize,
) {
    let Some(mem) = mem else {
        return;
    };
    stats::search_done(shared.start.elapsed(), &shared.seen, kept_resume, mem);
    if let Some(d) = shared.seen.disk_stats() {
        let (_, t) = shared.seen.rotations();
        stats::fpset_disk_done(d, t);
    }
    let c = shared.opts.spill.counters();
    if c.blocks > 0 {
        let (queue_segs, archive_segs) = shared.frontier.spilled_segments();
        stats::spill_done(c.written, c.read, c.peak, c.blocks, logs_spilled, queue_segs, archive_segs);
    }
    let peak = meters.peak(Component::Caches);
    if peak > 0 {
        stats::set(&format!("{}memo tables (all threads; peak)", stats::MEMORY), stats::Metric::Bytes(peak as u64));
        if cache_mem::share() != usize::MAX {
            stats::set(
                &format!("{}evaluation caches: allowance per thread (-maxmem / 8 / workers)", stats::MEMORY),
                stats::Metric::Bytes(cache_mem::share() as u64),
            );
        }
    }
}

/// The report of a search that failed while computing (or checking) the
/// initial states: as TLC, the statistics so far (the initial states
/// generated, also one whose VIEW failed, those found and queued) and no
/// behavior.
pub(super) fn in_init_failed<'m, M: Model>(run: &Run<'m, M>, e: ModelError) -> Report<M::State> {
    let shared = &run.shared;
    let mut stats = run.stats.clone();
    stats.generated = stats.init_generated + (shared.model.extra_generated() - run.extra_at_start);
    stats.distinct = shared.seen.len() as u64;
    stats.left = stats.init_distinct;
    stats.depth = u32::from(stats.generated > 0);
    let coverage = shared.opts.coverage.then(|| shared.coverage());
    Report {
        stats,
        outcome: Outcome::Error(e),
        trace: Vec::new(),
        trace_note: None,
        trace_store_full: false,
        elapsed: shared.start.elapsed(),
        in_init: true,
        live_graph: None,
        live_error: None,
        live_atoms_ok: false,
        coverage,
        frontier_peak: shared.frontier.peak_bytes().0,
    }
}

/// The behavior graph of a complete search from the edges its workers
/// recorded (`edges`) and, for a resumed search, those of the states of the
/// levels before its resume point (`pre`, expanded again here); with
/// `exited`, of the states expanded before `TLCSet("exit", TRUE)` (see
/// `edges::build`). None if these cannot be recorded (liveness then
/// explores the state space again), Some(Err) if the graph does not fit in
/// the memory budget (`-maxmem`); an error reading spilled edge logs back,
/// or of an atom on a state of `pre`.
fn live_graph_of<'m, M: Model>(
    model: &'m M,
    atoms: &'m (dyn AtomBits<M::State> + Sync),
    mut edges: Vec<edges::EdgeRec<'m, M::State>>,
    pre: Vec<Pre<M::State>>,
    threads: usize,
    opts: &Options,
    exited: bool,
) -> Result<Option<Result<LiveGraph, String>>, LiveStop> {
    let maxmem = opts.maxmem;
    if !pre.is_empty() {
        let t0 = Instant::now();
        let n = pre.iter().map(|p| p.len()).sum::<usize>();
        match record_archived(model, atoms, pre, threads, opts.queue.seg_bytes) {
            Ok(recs) => edges.extend(recs),
            // (Reading the spilled archive back failed: the run fails.)
            Err(e) => return Err(opts.spill.error().map_or(LiveStop::Atom(e), LiveStop::Io)),
        }
        stats::add_secs("liveness: edges of the levels before the resume point", t0.elapsed());
        stats::add_count("liveness: states expanded again for their edges", n as u64);
    }
    let t0 = Instant::now();
    if stats::on() {
        let bytes = edges.iter().map(|e| e.bytes()).sum::<usize>();
        stats::set(&format!("{}liveness edge logs", stats::MEMORY), stats::Metric::Bytes(bytes as u64));
    }
    if maxmem != usize::MAX {
        // (The records are freed as the graph is built, after its arrays
        // are allocated. Only what the graph adds counts against the
        // budget, with at least a quarter of it: `mem::live_limit`.)
        let (n, e, bytes) = edges::build_bytes(&edges);
        let base = crate::mem::live_base();
        let need = base + bytes;
        if need > crate::mem::live_limit(maxmem, base) {
            let what = format!("its behavior graph ({n} states, {e} edges: {} MiB)", bytes.div_ceil(1 << 20));
            return Ok(Some(Err(liveness_memory_error(&what, need, maxmem))));
        }
    }
    let g = edges::build(edges, &opts.spill, exited).map_err(LiveStop::Io)?;
    stats::add_secs("liveness: edge graph (CSR)", t0.elapsed());
    Ok(g.map(Ok))
}

/// Why `live_graph_of` has no graph to report.
enum LiveStop {
    /// Reading spilled records back failed.
    Io(IoError),
    /// An atom failed on a state of the levels before the resume point.
    Atom(ModelError),
}
