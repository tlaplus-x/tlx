//! An exploration worker: expands states (tasks) and processes their
//! successors (constraints, seen set, invariants, action properties).

use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Instant;

use super::coverage::{self, bump, generated_at};
use super::frontier::{Local, Task};
use super::history::Shard;
use super::levels::run_levels;
use super::order::OrderLocal;
use super::safepoint::STOP;
use super::tracelog::{log_ref, LogRef, NO_PARENT};
use super::{fp_set_full, invariant_failure, Failure, Outcome, OutdegreeHist, Shared, SP_GROW};
use crate::fpset::Full;
use crate::io::{IoError, SpillMode};
use crate::live;
use crate::mem::{Component, Part};
use crate::model::{Model, ModelError};
use crate::queue::Block;
use crate::stats::{self, T};

/// Counters a worker publishes for the live statistics: written by their
/// worker only (plain relaxed stores), summed on read.
#[repr(align(128))]
#[derive(Default)]
pub(super) struct Slot {
    pub(super) generated: AtomicU64,
    pub(super) max_depth: AtomicU64,
    /// The memory of the worker's trace log and liveness edges (bytes;
    /// its parts of the budget's gauges, updated every `TICK` states
    /// expanded).
    pub(super) log_bytes: Part,
    pub(super) edge_bytes: Part,
    /// Counting coverage (`Options::coverage`): per action, the successors
    /// it generated and the new states it found (`coverage::generated_at`);
    /// empty otherwise.
    pub(super) cov: Box<[AtomicU64]>,
}

/// A worker updates its memory counters and checks the archive every this
/// many states it expands.
const TICK: u64 = 1024;

/// The state of one exploration worker.
pub(super) struct WorkerState<'s, 'm, M: Model> {
    pub(super) shared: &'s Shared<'m, M>,
    pub(super) me: usize,
    pub(super) local: Local<'s, 'm, M::State>,
    /// The history shard currently leased by this worker.
    pub(super) shard: Shard<'m, M::State>,
    /// This worker's published counters, and its own copies of them.
    pub(super) slot: &'s Slot,
    pub(super) generated: u64,
    pub(super) max_depth: u32,
    /// New states found by the current expansion.
    new_states: u64,
    pub(super) outdegree: OutdegreeHist,
    /// The depth of the tasks being expanded, and `generated` and
    /// `outdegree` before the first of them (while archiving).
    pub(super) level: u32,
    pub(super) level_start: (u64, OutdegreeHist),
    /// The coverage counts before the first task of `level` (while
    /// archiving and counting).
    level_cov: Vec<u64>,
    /// The worker takes part in safepoints (see `safepoint`).
    active: bool,
    /// `Options::safepoint_every` (testing).
    safepoint_every: u64,
    /// The tasks expanded so far.
    expanded: u64,
    /// Choosing the representatives in BFS order (see `order`), if the
    /// search does.
    pub(super) order: Option<OrderLocal<'m, M::State>>,
    /// The invariant keys (`Model::invariant_key`) of states outside the
    /// constraints already checked without a violation: a direct-mapped
    /// cache (0 = empty; allocated on first use).
    checked_outside: Vec<u64>,
    /// The path to the state being expanded (`TLCExt!Trace`), if known.
    pub(super) path: Option<std::sync::Arc<live::PathNode>>,
}

/// Slots of a worker's cache of checked states outside the constraints.
const CHECKED_OUTSIDE_SLOTS: usize = 1 << 18;

/// What a worker leaves when the search ends.
pub(super) struct WorkerOut<'m, S> {
    pub(super) shard: Shard<'m, S>,
    /// Its part of the archive, if still archiving.
    pub(super) archive: Option<Vec<Block<S>>>,
    pub(super) outdegree: OutdegreeHist,
    /// Tasks left in its queues.
    pub(super) left: usize,
    pub(super) generated: u64,
    pub(super) level: u32,
    pub(super) level_start: (u64, OutdegreeHist),
    /// The worker's coverage counts, and those before the first task of
    /// `level` (if counting).
    pub(super) cov: Vec<u64>,
    pub(super) level_cov: Vec<u64>,
}

impl<'m, M: Model> WorkerState<'_, 'm, M> {
    /// Called between tasks: whether to go on (false once the search
    /// stops). Parks at a safepoint if one is requested.
    #[inline]
    pub(super) fn proceed(&self) -> bool {
        self.shared.control().get() == 0 || self.proceed_slow()
    }

    #[cold]
    #[inline(never)]
    fn proceed_slow(&self) -> bool {
        let shared = self.shared;
        loop {
            let c = shared.control().get();
            if c == 0 {
                return true;
            }
            if c & STOP != 0 {
                return false;
            }
            shared.safepoint.park(|req, crew| shared.serve_safepoint(req, crew));
        }
    }

    /// Stop taking part in safepoints (before waiting at a level barrier,
    /// or at the end).
    pub(super) fn leave_safepoints(&mut self) {
        if self.active {
            self.active = false;
            let shared = self.shared;
            shared.safepoint.leave(|req, crew| shared.serve_safepoint(req, crew));
        }
    }

    /// Take part in safepoints again: the barrier leader has joined on our
    /// behalf (`Safepoint::join_all`).
    pub(super) fn joined_safepoints(&mut self) {
        debug_assert!(!self.active, "joined while active");
        self.active = true;
    }

    pub(super) fn append_log(&mut self, parent: LogRef, fp: u64) -> LogRef {
        log_ref(self.shard.id, self.shard.log.push(parent, fp))
    }

    /// Expand `task`, recording a failure.
    pub(super) fn run(&mut self, task: &Task<M::State>) {
        self.new_states = 0;
        if self.local.archiving() && task.depth != self.level {
            self.level = task.depth;
            self.level_start = (self.generated, self.outdegree.clone());
            if !self.slot.cov.is_empty() {
                self.level_cov = coverage::load(&self.slot.cov);
            }
            self.shared.model.caps().mark();
        }
        match self.shared.path_of(task.log) {
            None => self.expand_any(task),
            Some(p) => {
                self.path = match &p {
                    live::CurrentPath::Known(n) => Some(n.clone()),
                    live::CurrentPath::Unavailable => None,
                };
                live::with_path(Some(p), || self.expand_any(task));
                self.path = None;
            }
        }
        self.outdegree.add(self.new_states);
        self.expanded += 1;
        if self.expanded.is_multiple_of(TICK) {
            self.tick();
        }
        if self.safepoint_every != 0 && self.expanded.is_multiple_of(self.safepoint_every) {
            self.shared.control().request(super::SP_TEST);
        }
    }

    /// Every `TICK` states: spill the full blocks of the trace log and the
    /// liveness edges if asked to (stages 2 and 3 of memory pressure),
    /// publish their memory, check the archive.
    #[cold]
    #[inline(never)]
    fn tick(&mut self) {
        self.local.spill();
        self.spill_logs(false);
        self.spill_candidates();
        let m = self.shared.budget.meters();
        self.slot.log_bytes.set(m.gauge(Component::TraceLogs), self.shard.log.bytes());
        if let Some(e) = &self.shard.edges {
            self.slot.edge_bytes.set(m.gauge(Component::LiveEdges), e.bytes());
        }
        self.check_archive();
    }

    /// Write the full blocks of the logs to disk if asked to (with `end`:
    /// at the end of the worker, waiting for the writes; in `-spill
    /// always` mode, every block). An IO error stops the search.
    fn spill_logs(&mut self, end: bool) {
        let shared = self.shared;
        let spill = &shared.opts.spill;
        let all = end && spill.mode() == SpillMode::Always;
        let mut r: Result<(), IoError> = Ok(());
        if shared.spill_logs.load(Ordering::Relaxed) {
            r = self.shard.log.spill(spill, all);
            if end {
                r = r.and(self.shard.log.settle());
            }
        }
        if let (Some(e), true, true) = (&mut self.shard.edges, r.is_ok(), shared.spill_edges.load(Ordering::Relaxed)) {
            r = e.spill(spill, all);
            if end {
                r = r.and(e.settle());
            }
        }
        if let Err(e) = r {
            shared.fail(Outcome::Io(e.0), NO_PARENT);
        } else if spill.failed() {
            // (Another worker's write.)
            shared.fail(Outcome::Io(spill.error().map_or_else(String::new, |e| e.0)), NO_PARENT);
        }
    }

    /// `run`'s expansion with the observer's hooks (out of the way of the
    /// unobserved search): without statistics in a quiet search; then the
    /// observer may stop the search (`SearchObserver::stop`).
    #[cold]
    #[inline(never)]
    fn expand_observed(&mut self, task: &Task<M::State>) {
        let quiet = self.shared.quiet;
        let unit = if quiet { stats::Span::Off } else { stats::begin_unit(task.depth) };
        if let Err((o, at)) = self.expand_as::<true>(task, stats::on() && !quiet) {
            self.shared.fail(o, at);
        }
        stats::end_unit(unit);
        if !self.shared.control().stopped() {
            self.shared.observer_stops();
        }
    }

    /// Expand `task` (with the observer's hooks if the search is observed),
    /// recording a failure.
    fn expand_any(&mut self, task: &Task<M::State>) {
        // (Instantiated without the observer's hooks unless the search is
        // observed.)
        if self.shared.observer.is_some() {
            self.expand_observed(task);
        } else {
            let unit = stats::begin_unit(task.depth);
            if let Err((o, at)) = self.expand_as::<false>(task, stats::on()) {
                self.shared.fail(o, at);
            }
            stats::end_unit(unit);
        }
    }

    /// `expand`, with the observer's hooks if `OBS`, with the statistics
    /// hooks if `stats_on`.
    #[inline(always)]
    fn expand_as<const OBS: bool>(&mut self, task: &Task<M::State>, stats_on: bool) -> Result<(), Failure> {
        // (Instantiated without the statistics hooks unless they are on,
        // without choosing representatives unless the search does, and
        // without counting the coverage unless it is on.)
        match (stats_on, self.order.is_some(), !self.slot.cov.is_empty()) {
            (false, false, false) => self.expand::<false, false, false, OBS>(task),
            (false, true, false) => self.expand::<false, true, false, OBS>(task),
            (true, false, false) => self.expand::<true, false, false, OBS>(task),
            (true, true, false) => self.expand::<true, true, false, OBS>(task),
            (false, false, true) => self.expand::<false, false, true, OBS>(task),
            (false, true, true) => self.expand::<false, true, true, OBS>(task),
            (true, false, true) => self.expand::<true, false, true, OBS>(task),
            (true, true, true) => self.expand::<true, true, true, OBS>(task),
        }
    }

    /// Generate and process the successors of `task`.
    /// `STATS`: with the statistics hooks; `ORDERED`: choosing the
    /// representatives in BFS order (see `order`); `COV`: counting the
    /// coverage (see `coverage`); `OBS`: calling the observer's hooks
    /// (see `observer`).
    fn expand<const STATS: bool, const ORDERED: bool, const COV: bool, const OBS: bool>(
        &mut self,
        task: &Task<M::State>,
    ) -> Result<(), Failure> {
        let model = self.shared.model;
        if ORDERED {
            self.order_task(task);
        }
        let mut count = 0u64;
        let mut failure = None;
        if let Some(e) = &mut self.shard.edges {
            e.begin();
        }
        let res = if OBS {
            self.observed_successors::<STATS, ORDERED, COV>(task, &mut count, &mut failure)
        } else {
            model.successors(&task.state, &mut |t, a| self.successor::<STATS, ORDERED, COV, false>(task, t, a, &mut count, &mut failure, 0))
        };
        if let Some(f) = failure {
            return Err(f);
        }
        res.map_err(|e| (Outcome::Error(e.in_next_state()), task.log))?;
        // (The observer stopped the search in the middle of the successors:
        // the state's liveness edges are not complete.)
        if OBS && self.shared.halted.load(Ordering::Relaxed) {
            return Ok(());
        }
        // Deadlock: no successor at all was generated (TLC counts stuttering,
        // already-seen and constraint-violating successors).
        if count == 0 && self.shared.opts.check_deadlock {
            return Err((Outcome::Deadlock, task.log));
        }
        if let Some(e) = &mut self.shard.edges {
            let r = e.end(&task.state, model.fingerprint(&task.state), (task.depth == 1).then_some(task.log));
            edge_error(model, r, task.log)?;
        }
        Ok(())
    }

    /// Process successor `t` of `task` by action `a` as it is generated
    /// (counting it in `count`): false to stop the generation, at a
    /// `failure`. (`from`: the fingerprint of `task`'s state if `OBS`.)
    #[inline(always)]
    fn successor<const STATS: bool, const ORDERED: bool, const COV: bool, const OBS: bool>(
        &mut self,
        task: &Task<M::State>,
        t: M::State,
        a: u32,
        count: &mut u64,
        failure: &mut Option<Failure>,
        from: u64,
    ) -> bool {
        if OBS {
            if let Some(o) = self.shared.observer {
                o.on_edge(from, self.shared.model.fingerprint(&t), a);
            }
        }
        *count += 1;
        if STATS {
            stats::successor(a);
        }
        if COV {
            bump(&self.slot.cov, generated_at(a));
        }
        // Published at once: `TLCGet("generated")` counts the
        // successor being checked.
        self.generated += 1;
        self.slot.generated.store(self.generated, Ordering::Relaxed);
        let span = if STATS { stats::span() } else { stats::Span::Off };
        let r = self.add_successor::<STATS, ORDERED, COV, OBS>(task, t, a, *count, from);
        span.end(T::Successor);
        match r {
            // (The observer may stop the search after each successor.)
            Ok(()) if OBS => !self.shared.observer_stops(),
            Ok(()) => true,
            Err(f) => {
                *failure = Some(f);
                false
            }
        }
    }

    /// The successors of `task` generated and processed (`successor`) in an
    /// observed search: as they are generated, or, for an observer that
    /// buffers them, after `on_expanded` saw them all. The error of the
    /// observer, else of the generation.
    #[inline(never)]
    fn observed_successors<const STATS: bool, const ORDERED: bool, const COV: bool>(
        &mut self,
        task: &Task<M::State>,
        count: &mut u64,
        failure: &mut Option<Failure>,
    ) -> Result<(), ModelError> {
        let model = self.shared.model;
        let o = self.shared.observer.expect("an observed search");
        let from = model.fingerprint(&task.state);
        if !o.buffers() {
            return model
                .successors(&task.state, &mut |t, a| self.successor::<STATS, ORDERED, COV, true>(task, t, a, count, failure, from));
        }
        let mut all = Vec::new();
        let res = model.successors(&task.state, &mut |t, a| {
            all.push((t, a));
            true
        });
        let observed = o.on_expanded(&task.state, &all, res.is_ok());
        for (t, a) in all {
            if !self.successor::<STATS, ORDERED, COV, true>(task, t, a, count, failure, from) {
                break;
            }
        }
        observed.and(res)
    }

    /// Insert `fp` into the seen set, found at its hard limit: grow it (or
    /// rotate it to disk) at a safepoint (parking here, in the middle of a
    /// task: the worker holds no reference into the set) and insert again,
    /// until the set can do neither (the capacity error, or an IO error).
    #[cold]
    #[inline(never)]
    fn insert_when_full(&self, fp: u64) -> Result<bool, Failure> {
        let shared = self.shared;
        let seen = &shared.seen;
        loop {
            if !seen.can_make_room() {
                return Err(fp_set_full(seen));
            }
            shared.control().request(SP_GROW);
            shared.safepoint.park(|req, crew| shared.serve_safepoint(req, crew));
            match seen.insert(fp, &mut 0, || shared.control().request(SP_GROW)) {
                Ok(b) => return Ok(b),
                // (A broken safepoint serves nothing: the search stops.)
                Err(Full) if shared.control().stopped() => return Err(fp_set_full(seen)),
                Err(Full) => {}
            }
        }
    }

    /// Process successor `t` of `task` (the `idx`th, by action `action`) as
    /// soon as it is generated (TLC Worker.addElement): constraints, seen
    /// set, invariants, then action properties. (`from`: the fingerprint of
    /// `task`'s state if `OBS`.)
    #[inline]
    fn add_successor<const STATS: bool, const ORDERED: bool, const COV: bool, const OBS: bool>(
        &mut self,
        task: &Task<M::State>,
        t: M::State,
        action: u32,
        idx: u64,
        from: u64,
    ) -> Result<(), Failure> {
        let model = self.shared.model;
        let s = &task.state;
        let span = if STATS { stats::span() } else { stats::Span::Off };
        // (TLC's trace of an error in a constraint or an action property
        // ends with the successor.)
        let in_model = crate::model::admits(model, s, &t);
        span.end(T::Constraint);
        let in_model = match in_model {
            Ok(b) => b,
            Err(e) => return Err((Outcome::Error(e), self.append_log(task.log, model.fingerprint(&t)))),
        };
        let fp = model.fingerprint(&t);
        if let Some(e) = &mut self.shard.edges {
            edge_error(model, e.successor(s, &t, fp, action, in_model), task.log)?;
        }
        // States outside the model are not added to the seen set, but are
        // checked against the invariants every time they are generated.
        // (At the high watermark, the set asks to grow at a safepoint.)
        // (Choosing the representatives in BFS order, a state of a new
        // class is only a candidate until the level is resolved.)
        let seen = &self.shared.seen;
        let high = || self.shared.control().request(SP_GROW);
        let ordered = ORDERED && in_model;
        let new = !in_model
            || !ordered
                && match if STATS { stats::fp_insert(seen, self.me, fp, high) } else { seen.insert_by(self.me, fp, &mut 0, high) } {
                    Ok(b) => b,
                    Err(Full) => self.insert_when_full(fp)?,
                };
        let mut lr = None;
        let depth = task.depth + 1;
        // A state outside the model whose invariants were checked already.
        let key =
            if !in_model && (!OBS || self.shared.observer.is_none()) { model.invariant_key(&t, fp).filter(|&k| k != 0) } else { None };
        let checked = key.is_some_and(|k| self.checked_outside.get(k as usize & (CHECKED_OUTSIDE_SLOTS - 1)) == Some(&k));
        let new = new && !checked;
        if new {
            let r = self.append_log(task.log, fp);
            lr = Some(r);
            if let (true, Some(o)) = (OBS, self.shared.observer) {
                o.on_new_state(&t, fp, depth, Some(from));
            }
            if in_model {
                self.new_states += 1;
                if COV {
                    bump(&self.slot.cov, generated_at(action) + 1);
                }
                if let Some(e) = &mut self.shard.edges {
                    edge_error(model, e.found(&t), task.log)?;
                }
                // Counted before the checks: TLC reports the depth of a
                // violating state.
                if depth > self.max_depth {
                    self.max_depth = depth;
                    self.slot.max_depth.store(depth as u64, Ordering::Relaxed);
                }
            }
            let span = if STATS { stats::span() } else { stats::Span::Off };
            let f = invariant_failure(model, &t, r);
            span.end(T::Invariants);
            if let Some(f) = f {
                return Err(f);
            }
            if let Some(k) = key {
                if self.checked_outside.is_empty() {
                    self.checked_outside = vec![0; CHECKED_OUTSIDE_SLOTS];
                }
                self.checked_outside[k as usize & (CHECKED_OUTSIDE_SLOTS - 1)] = k;
            }
        }
        // Action properties are checked on every transition (TLC: implied actions).
        let span = if STATS { stats::span() } else { stats::Span::Off };
        let transition = model.check_transition(s, &t);
        span.end(T::Transition);
        match transition {
            Ok(None) => {}
            Ok(Some(i)) => {
                let r = lr.unwrap_or_else(|| self.append_log(task.log, fp));
                return Err((Outcome::ActionPropertyViolated(model.action_property_names()[i].clone()), r));
            }
            Err(e) => return Err((Outcome::Error(e), lr.unwrap_or_else(|| self.append_log(task.log, fp)))),
        }
        if ordered {
            self.offer::<STATS>(task, t, fp, action, idx)?;
        } else if let (true, Some(log)) = (in_model, lr) {
            self.shared.note_path(log, depth, &t, Some(action), self.path.clone());
            self.local.push_new(Task { state: t, log, depth });
        }
        Ok(())
    }
}

/// After recording liveness edges: an atom error that interrupts the
/// search (a layout miss while the search can restart, see
/// `Effects::interrupts`) stops it at `at`, so that it restarts and records
/// its edges in the widened layout; other errors only stop the recording
/// (`Report::live_error` carries the first one to liveness).
#[inline]
pub(super) fn edge_error<M: Model>(model: &M, r: Result<(), ModelError>, at: LogRef) -> Result<(), Failure> {
    match r {
        Err(e) if model.caps().interrupts(&e) => Err((Outcome::Error(e), at)),
        _ => Ok(()),
    }
}

/// Run worker `me`, with its leased history shard.
pub(super) fn run_worker<'s, 'm, M: Model>(
    shared: &'s Shared<'m, M>,
    me: usize,
    local: Local<'s, 'm, M::State>,
    shard: Shard<'m, M::State>,
) -> WorkerOut<'m, M::State> {
    live::set_current_worker(Some(me));
    live::with_source(shared, || run_worker_in(shared, me, local, shard))
}

/// `run_worker`, with the live statistics installed.
fn run_worker_in<'s, 'm, M: Model>(
    shared: &'s Shared<'m, M>,
    me: usize,
    local: Local<'s, 'm, M::State>,
    shard: Shard<'m, M::State>,
) -> WorkerOut<'m, M::State> {
    let born = Instant::now();
    let mut shard = shard;
    if let Err(e) = shard.log.unseal() {
        shared.fail(Outcome::Io(e.0), NO_PARENT);
    }
    let mut w = WorkerState {
        shared,
        me,
        local,
        shard,
        slot: &shared.slots[me],
        generated: 0,
        max_depth: 0,
        new_states: 0,
        outdegree: OutdegreeHist::new(),
        level: 0,
        level_start: (0, OutdegreeHist::new()),
        level_cov: Vec::new(),
        active: true,
        safepoint_every: shared.safepoint_every,
        expanded: 0,
        order: shared.order.as_ref().map(|o| OrderLocal::new(o, shared.model.caps().codec(), shared.opts.queue.seg_bytes)),
        checked_outside: Vec::new(),
        path: None,
    };
    if shared.slots.len() > 1 {
        run_levels(&mut w);
    } else {
        // Exact BFS: level after level, each in FIFO order.
        loop {
            w.expand_level(false);
            if shared.control().stopped() || w.local.next_len() == 0 {
                break;
            }
            w.local.advance();
            if shared.checkpoint_due() {
                w.publish_history();
                w.checkpoint_part();
                shared.commit_checkpoint();
                w.lease_history();
            }
        }
    }
    w.leave_safepoints();
    w.spill_logs(true);
    let left = w.retain_left();
    let archive = w.local.take_archive();
    if shared.retention.on {
        shared.model.caps().worker_end();
    }
    w.slot.log_bytes.set(shared.budget.meters().gauge(Component::TraceLogs), w.shard.log.bytes());
    if shared.quiet {
        // (Only what the evaluation counted, as on the thread that called
        // the search.)
        stats::flush();
    } else {
        stats::worker_done(born.elapsed());
    }
    let cov = coverage::load(&w.slot.cov);
    WorkerOut {
        shard: w.shard,
        archive,
        outdegree: w.outdegree,
        left,
        generated: w.generated,
        level: w.level,
        level_start: w.level_start,
        cov,
        level_cov: w.level_cov,
    }
}
