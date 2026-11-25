//! Shape speculation: static hints, the bounded interpreter pre-run that
//! observes the shapes of variables and candidate definitions, and the
//! choice of definitions worth materializing.

use std::collections::{HashSet, VecDeque};
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use std::sync::Mutex;
use std::time::{Duration, Instant};

use tlx_base::time::process_cpu;
use tlx_eval::env::Env;
use tlx_eval::model::State;
use tlx_eval::strings::{makes_strings, StringMakers};
use tlx_eval::{FpMode, InterpModel};
use tlx_layout::decisions::Slot;
use tlx_layout::infer::{bound_covers, refine, set_elem_bound, Hints, Observer};
use tlx_layout::Shape;
use tlx_runtime::io::SpillMode;
use tlx_runtime::{explore_observed, ErrorContext, Model, ModelError, Options, Outcome, Report, SearchObserver};
use tlx_sema::hir::{self, DefId};
use tlx_value::Value;

mod static_hints;
pub use static_hints::{hints, materialize_candidates};
pub(super) use static_hints::{view_def, view_tuple};

/// Bounds of the pre-run.
#[derive(Clone, Copy, Debug)]
pub struct PrerunBudget {
    /// Distinct states.
    pub states: usize,
    /// Wall time: the interpreter can be slow, and shapes not seen within
    /// the budget cost a restart later rather than a wrong result.
    pub time: Duration,
    /// For a simulation (behaviors of at most this many steps; 0 for a
    /// search): most of the time goes to random behaviors after a short
    /// BFS, so that the shapes of deep states are seen too.
    pub walk_depth: u32,
    /// Stop the BFS once the layout has settled (0: never): when the
    /// states observed since the last one that did not fit the layout
    /// chosen so far are at least this many, and at least twice as many as
    /// the states observed before it.
    pub settle: usize,
    /// Threads of the BFS (the search's workers): more than one only for a
    /// search that creates no strings and evaluates no volatile builtins
    /// (see `search_makes_strings`, `search_is_volatile`).
    pub workers: usize,
}

/// What the pre-run found.
pub struct Prerun {
    /// The shape of each variable.
    pub shapes: Vec<Shape>,
    /// The shape of each candidate definition (`None` if it failed to
    /// evaluate in some state or its shape is not worth materializing).
    pub defs: Vec<Option<Shape>>,
    /// Distinct states seen.
    pub states: usize,
    /// The BFS stopped because the layout settled (see `PrerunBudget`).
    pub settled: bool,
    /// The report of the faithful pre-run when it is the search's: it
    /// explored the whole state space (or stopped where the search stops)
    /// with the search's options (see `reuse_ok`). The run needs no other
    /// search then.
    pub report: Option<Report<State>>,
    /// Alternative shapes of variables (index, shape), refined with the
    /// bounds of type invariants (see `type_bounds`): better only if the
    /// layout gets smaller once records are unified (the caller decides).
    pub bounded: Vec<(usize, Shape)>,
}

/// The layout shapes of the variables and the materialized definitions
/// that the driver chooses from a pre-run result.
pub type Layouts<'a> = dyn Fn(Prerun) -> (Vec<Shape>, Vec<(DefId, Shape)>) + Sync + 'a;

/// Shapes speculated from a bounded interpreter pre-run (BFS within
/// `budget`). `search`: the options of the search the pre-run precedes, if
/// its report may replace that search's (see `Prerun::report`).
pub fn prerun_shapes(
    base: &InterpModel,
    budget: PrerunBudget,
    hints: &Hints,
    defs: &[DefId],
    layout: &Layouts,
    search: Option<&Options>,
) -> Result<Result<Prerun, ModelError>, String> {
    // The pre-run is not the search: Print/PrintT must not print (the
    // search prints those lines, as TLC does), files it writes (CSVWrite)
    // are restored.
    let printing = base.ip.print_suppressed();
    base.ip.set_suppress_print(true);
    base.ip.effects_active(true);
    let r = prerun_shapes_inner(base, budget, hints, defs, layout, search);
    // (Undone as a run started over; the results of the programs it ran
    // are kept for the search.)
    let restored = base.ip.effects_finish_prerun();
    base.ip.set_suppress_print(printing);
    restored?;
    Ok(r)
}

fn prerun_shapes_inner(
    base: &InterpModel,
    budget: PrerunBudget,
    hints: &Hints,
    defs: &[DefId],
    layout: &Layouts,
    search: Option<&Options>,
) -> Result<Prerun, ModelError> {
    let start = Instant::now();
    let strings = model_strings(base);
    let mut faithful = search_makes_strings(base, &strings);
    // Whether the pre-run evaluates the constraints (not when that may
    // create strings: see below).
    let mut constrain = true;
    if faithful && budget.walk_depth > 0 {
        // A simulation creates its strings in the order of its random
        // behaviors, which a pre-run cannot follow. When only the checks of
        // states (constraints, invariants, action properties) may create
        // them, the pre-run generates states without checking them: its
        // states are then a superset of the simulation's.
        if generation_makes_strings(base, &strings) {
            return Err(ModelError::from("the simulation may create strings"));
        }
        faithful = false;
        constrain = !constraints_make_strings(base, &strings);
    }
    // Shapes only need the states themselves, not SYMMETRY reduction (in
    // the interpreter it costs a fingerprint per permutation), unless the
    // pre-run is faithful: then it expands the states the search expands,
    // which are fewer under SYMMETRY. A VIEW is kept: without it the state
    // space can be much larger or unbounded. (With SYMMETRY too, the plain
    // fingerprints drop the VIEW as well.)
    let plain;
    let base = if !faithful && base.has_symmetry() {
        plain = base.with_fp_mode(FpMode::Plain);
        &plain
    } else {
        base
    };
    let bfs_time = if budget.walk_depth > 0 { budget.time / 4 } else { budget.time };
    let (max_states, deadline) = (budget.states, start + bfs_time);
    let chooser = Chooser {
        defs,
        hints,
        layout,
        bounds: type_bounds(base),
        settle: budget.settle,
        start_cpu: process_cpu(),
        observed: AtomicUsize::new(0),
        last_miss: AtomicUsize::new(0),
        last_miss_at: AtomicU64::new(0),
    };
    let within = |n: usize| n < max_states && Instant::now() < deadline && !chooser.settled();
    let mut obs = Observed { watch: Watch::new(base, defs), chosen: None };
    if faithful {
        let reuse = search.filter(|o| reuse_ok(base, o));
        let live = live_makes_strings(base, &strings);
        return faithful_prerun(base, &chooser, obs, max_states, &within, hints, reuse, live);
    }
    let mut seen = HashSet::new();
    let mut queue = VecDeque::new();
    let mut inits = Vec::new();
    base.init_states_until(&mut |s| {
        if seen.insert(s.fp) {
            obs.state(&chooser, &s.vals);
            if budget.walk_depth > 0 {
                inits.push(s.clone());
            }
            queue.push_back(s);
        }
        // All initial states (up to the state budget) regardless of time:
        // the search starts with them.
        seen.len() < max_states
    })?;
    // Like the search: every generated state is encoded (so observed), but
    // only states satisfying the CONSTRAINTs are expanded, and transitions
    // violating an ACTION_CONSTRAINT are dropped (their targets observed).
    // (One thread when volatile builtins run, or for the random walks
    // after it: the walks follow the sequential pre-run.)
    let mut threads = budget.workers.min(std::thread::available_parallelism().map_or(1, |n| n.get()));
    if budget.walk_depth > 0 || search_is_volatile(base) {
        threads = 1;
    }
    let (states, rest, errored) = generation_bfs(base, threads, constrain, &chooser, &mut obs, (seen, queue.into()), &within)?;
    if !errored && budget.walk_depth > 0 {
        random_walks(base, &inits, budget.walk_depth, start + budget.time, constrain, &mut |v| obs.state(&chooser, v));
    }
    let settled = !errored && chooser.settled() && rest;
    Ok(result(&obs.watch, hints, &chooser.bounds, states, settled))
}

/// The faithful pre-run (see `search_makes_strings`): the search itself
/// (`explore`, quiet, on one worker), watched by `Faithful`, which observes
/// the states it checks and stops it where the budget ends (`within` of the
/// number of distinct states; for the initial states only `max_states`: the
/// search starts with all of them). Its states are then a prefix of the
/// search's, and so are the strings it creates.
///
/// `reuse`: the options of the search, when the pre-run can be that search
/// (see `reuse_ok`). If it then ends before its budget (the state space is
/// explored, or a failure stops it), its report is the search's
/// (`Prerun::report`): the interpreter's, the semantics oracle of the
/// compiled tier, of the same search.
#[allow(clippy::too_many_arguments)]
fn faithful_prerun<'a>(
    base: &InterpModel,
    chooser: &Chooser<'a>,
    obs: Observed<'a>,
    max_states: usize,
    within: &(dyn Fn(usize) -> bool + Sync),
    hints: &Hints,
    reuse: Option<&Options>,
    live: bool,
) -> Result<Prerun, ModelError> {
    // (Its report needs the behavior graph if the search records one.)
    let reuse = reuse.filter(|_| live || !base.records_live_edges());
    let watcher =
        Faithful { chooser, obs: Mutex::new(obs), max_states, within, live, reuse: reuse.is_some(), stopped: AtomicBool::new(false) };
    // (Not stopping at a deadlock unless the pre-run may be the search:
    // the states after it, which the search does not reach, cannot change
    // the order of the strings it creates; their shapes are observed, as
    // they were before the pre-run became the search.)
    let opts = match reuse {
        Some(o) => Options { workers: 1, check_deadlock: o.check_deadlock, fp: o.fp, ..Options::default() },
        None => Options { workers: 1, check_deadlock: false, ..Options::default() },
    };
    let r = explore_observed(base, &opts, &watcher);
    if let Some(o) = reuse {
        // (Not if the search would have taken a checkpoint by then.)
        if !watcher.stopped.load(Ordering::Relaxed) && o.checkpoint.as_ref().is_none_or(|c| !c.would_be_due(r.stats.distinct)) {
            let obs = watcher.obs.into_inner().unwrap();
            let states = r.stats.distinct as usize;
            return Ok(Prerun { report: Some(r), ..result(&obs.watch, hints, &chooser.bounds, states, false) });
        }
    }
    if let Some(e) = generation_error(&r) {
        if r.stats.distinct == 0 {
            return Err(e);
        }
        let obs = watcher.obs.into_inner().unwrap();
        return Ok(result(&obs.watch, hints, &chooser.bounds, r.stats.distinct as usize, false));
    }
    let obs = watcher.obs.into_inner().unwrap();
    // Settled: the layout settled and the search stopped with states left
    // beyond the next one it would have expanded (as the sequential BFS
    // the pre-run was, which took that one from its queue before it
    // stopped).
    let settled = chooser.settled() && r.stats.left >= 2;
    Ok(result(&obs.watch, hints, &chooser.bounds, r.stats.distinct as usize, settled))
}

/// Watches the faithful pre-run (`faithful_prerun`).
struct Faithful<'a, 'c> {
    chooser: &'c Chooser<'a>,
    obs: Mutex<Observed<'a>>,
    max_states: usize,
    within: &'c (dyn Fn(usize) -> bool + Sync),
    /// Whether the search evaluates the liveness atoms (see
    /// `records_live_graph`).
    live: bool,
    /// The pre-run may be the search (see `faithful_prerun`).
    reuse: bool,
    /// The budget stopped the search.
    stopped: AtomicBool,
}

impl SearchObserver<State> for Faithful<'_, '_> {
    fn quiet(&self) -> bool {
        true
    }

    /// The behavior graph is never built from the pre-run, so its liveness
    /// atoms are not evaluated (in the interpreter they can cost more than
    /// the rest of the pre-run), unless they may create strings:
    /// then they are evaluated as in the search, to create those in its
    /// order.
    fn records_live_graph(&self) -> bool {
        self.live
    }

    /// The trace of a failure and the behavior graph, if the report can be
    /// the search's.
    fn complete_results(&self) -> bool {
        self.reuse && !self.stopped.load(Ordering::Relaxed)
    }

    /// The states the search checks: those it finds, and those outside the
    /// model (CONSTRAINT, ACTION_CONSTRAINT) every time they are generated
    /// (all are encoded by the compiled search).
    fn on_new_state(&self, s: &State, _fp: u64, _depth: u32, _parent: Option<u64>) {
        self.obs.lock().unwrap().state(self.chooser, &s.vals);
    }

    fn stop(&self, init: bool, distinct: u64) -> bool {
        let n = distinct as usize;
        let stop = if init { n >= self.max_states } else { !(self.within)(n) };
        if stop {
            self.stopped.store(true, Ordering::Relaxed);
        }
        stop
    }
}

/// The error of a search stopped by an error generating its states
/// (evaluating Init or Next, or a state they produced): a pre-run that
/// cannot generate the states fails (as the generating one does). Errors
/// of the checks only stop it, as they stop the search.
fn generation_error(r: &Report<State>) -> Option<ModelError> {
    match &r.outcome {
        Outcome::Error(e) if r.in_init => (!matches!(e.context, ErrorContext::InitialState(_))).then(|| e.clone()),
        Outcome::Error(e) => matches!(e.context, ErrorContext::NextState | ErrorContext::IncompleteState { .. }).then(|| e.clone()),
        Outcome::FpSetFull { .. } | Outcome::Io(_) => Some(ModelError::new(format!("{:?}", r.outcome))),
        _ => None,
    }
}

/// A layout chosen from observed states: the shapes of the variables, and
/// of the definitions that would be materialized (by index in the
/// candidates).
type Chosen = (Vec<Shape>, Vec<(usize, Shape)>);

/// What the pre-run observes: the shapes of the variables and of the
/// candidate definitions.
struct Watch<'a> {
    vars: Observer,
    probe: DefProbe<'a>,
}

impl<'a> Watch<'a> {
    fn new(base: &'a InterpModel, defs: &'a [DefId]) -> Watch<'a> {
        Watch { vars: Observer::new(base.ip.prog.vars.len()), probe: DefProbe::new(base, defs) }
    }

    /// Observe a state: whether it changed a shape (open-ended atom
    /// universes become `Dyn`, see `Observer::observe_with`).
    fn observe(&mut self, vals: &[Value], hints: &Hints) -> bool {
        let mut changed = self.vars.observe_with(vals, hints);
        if !self.probe.defs.is_empty() {
            changed |= self.probe.observe(vals, hints);
        }
        changed
    }

    /// Whether the state observed last (values `vals`) fits layout `c`.
    fn fits(&self, c: &Chosen, vals: &[Value]) -> bool {
        let p = &self.probe;
        c.0.iter().zip(vals).all(|(s, v)| s.contains(v)) && c.1.iter().all(|(i, s)| p.failed[*i] || s.contains(&p.last[*i]))
    }

    /// An empty watch of the same definitions (minus those that failed).
    fn fresh(&self) -> Watch<'a> {
        let mut w = Watch::new(self.probe.base, self.probe.defs);
        w.probe.failed.clone_from(&self.probe.failed);
        w
    }

    /// Add what `other` observed.
    fn merge(&mut self, other: Watch) {
        join_into(&mut self.vars, &other.vars);
        let (p, q) = (&mut self.probe, other.probe);
        join_into(&mut p.obs, &q.obs);
        p.failed.iter_mut().zip(&q.failed).for_each(|(a, b)| *a |= *b);
        p.view_parts = match (p.view_parts.take(), q.view_parts) {
            (Some((i, mut a)), Some((_, b))) => {
                join_into(&mut a, &b);
                Some((i, a))
            }
            _ => None,
        };
    }
}

fn join_into(a: &mut Observer, b: &Observer) {
    for (x, y) in a.shapes.iter_mut().zip(&b.shapes) {
        *x = x.join(y);
    }
}

/// Chooses layouts from observations and decides when the layout has
/// settled (see `PrerunBudget::settle`).
struct Chooser<'a> {
    defs: &'a [DefId],
    hints: &'a Hints,
    layout: &'a Layouts<'a>,
    bounds: Vec<(usize, Shape)>,
    settle: usize,
    /// Process CPU time when the pre-run started (see
    /// `tlx_base::time::process_cpu`).
    start_cpu: Duration,
    /// States observed.
    observed: AtomicUsize,
    /// States observed until the last one that did not fit the layout
    /// chosen from those before it.
    last_miss: AtomicUsize,
    /// When that state was observed (CPU nanoseconds since `start_cpu`).
    last_miss_at: AtomicU64,
}

/// A layout that has fit for at least `SETTLE_TIME` of CPU time and at least
/// twice as long as it took to find it, over at least a quarter of the
/// `settle` states, has settled too (where the interpreter is slow, a fixed
/// number of states costs a large part of a short run).
///
/// CPU time, not wall time: a machine under load stretches the wall clock
/// without the pre-run doing more work, and the rule then settles on fewer
/// states than on an idle machine (a loaded EWD998PCal settled after 1565
/// states instead of 4938 and needed 3 layout restarts instead of 1). The
/// process's CPU time advances with the interpreter work itself, whatever
/// the load, and with several pre-run threads it still measures that work
/// (states observed scale with it).
const SETTLE_TIME: Duration = Duration::from_millis(50);

/// The settle rule: whether the pre-run that observed `n` states (the last
/// one that did not fit the layout chosen from those before it was number
/// `last`, observed `found` into the pre-run), `now` into it, may stop.
/// Times are CPU times (see `SETTLE_TIME`). A pure function so that a test
/// can scale them, as a loaded machine does to wall times.
fn settle_rule(settle: usize, n: usize, last: usize, found: Duration, now: Duration) -> bool {
    if settle == 0 || n < last + settle / 4 {
        return false;
    }
    if n >= (3 * last).max(last + settle) {
        return true;
    }
    now.saturating_sub(found) >= SETTLE_TIME.max(2 * found)
}

impl Chooser<'_> {
    /// Process CPU time since the pre-run started.
    fn cpu(&self) -> Duration {
        process_cpu().saturating_sub(self.start_cpu)
    }

    /// The layout the driver would choose from what `w` observed.
    fn choose(&self, w: &Watch) -> Chosen {
        let (vs, ds) = (self.layout)(result(w, self.hints, &self.bounds, 0, false));
        let ds = ds.into_iter().filter_map(|(d, s)| Some((self.defs.iter().position(|x| *x == d)?, s))).collect();
        (vs, ds)
    }

    fn settled(&self) -> bool {
        let (n, last) = (self.observed.load(Ordering::Relaxed), self.last_miss.load(Ordering::Relaxed));
        let found = Duration::from_nanos(self.last_miss_at.load(Ordering::Relaxed));
        settle_rule(self.settle, n, last, found, self.cpu())
    }

    /// Count a state observed by `w` (values `vals`): whether it did not fit
    /// `chosen`, the layout chosen so far (without `settle`: whether it
    /// changed a shape).
    fn count(&self, w: &mut Watch, chosen: Option<&Chosen>, vals: &[Value]) -> bool {
        let changed = w.observe(vals, self.hints);
        let n = self.observed.fetch_add(1, Ordering::Relaxed) + 1;
        // (A state that changed no shape fits.)
        if !changed || self.settle == 0 {
            return changed;
        }
        let fits = chosen.is_some_and(|c| w.fits(c, vals));
        if !fits {
            self.last_miss.fetch_max(n, Ordering::Relaxed);
            self.last_miss_at.fetch_max(self.cpu().as_nanos().min(u64::MAX as u128) as u64, Ordering::Relaxed);
        }
        !fits
    }
}

/// The observations of a sequential pre-run, and the layout chosen from
/// them.
struct Observed<'a> {
    watch: Watch<'a>,
    chosen: Option<Chosen>,
}

impl Observed<'_> {
    /// Observe a state: whether it changed a shape (with `settle`: whether
    /// it did not fit the layout chosen so far, which is then chosen anew).
    fn state(&mut self, chooser: &Chooser, vals: &[Value]) -> bool {
        let miss = chooser.count(&mut self.watch, self.chosen.as_ref(), vals);
        if miss && chooser.settle > 0 {
            self.chosen = Some(chooser.choose(&self.watch));
        }
        miss
    }
}

/// Whether the search evaluates volatile builtins (`Builtin::is_volatile`:
/// random choices, TLCGet/TLCSet registers, printing, files, IOExec): their
/// effects and registers are per thread, so the pre-run then stays on one
/// thread.
fn search_is_volatile(base: &InterpModel) -> bool {
    let mut roots: Vec<hir::Expr> = vec![base.init_expr().clone()];
    roots.extend(base.actions().iter().map(|a| a.expr.clone()));
    for es in [base.constraint_exprs(), base.action_constraint_exprs(), base.invariant_exprs(), base.action_property_exprs()] {
        roots.extend(es.iter().cloned());
    }
    roots.extend(base.view_expr().cloned());
    volatile(base, roots)
}

/// Whether checking the invariants may evaluate volatile builtins (then
/// every check counts, see `Model::invariant_key`).
pub(super) fn invariants_volatile(base: &InterpModel) -> bool {
    volatile(base, base.invariant_exprs().to_vec())
}

/// The liveness atoms: the predicates the search evaluates on the states
/// and steps of the behavior graph it records.
fn live_atoms(base: &InterpModel) -> impl Iterator<Item = &hir::Expr> {
    live_atoms_in(base).map(|(e, _)| e)
}

/// The liveness atoms, with their environments.
fn live_atoms_in(base: &InterpModel) -> impl Iterator<Item = (&hir::Expr, &Env)> {
    use tlx_eval::model::liveness::StateAtom;
    let live = &base.live;
    let state = live.state_atoms.iter().map(|a| match a {
        StateAtom::Pred(a) | StateAtom::EnabledVia(_, a) => (&a.expr, &a.env),
    });
    state.chain(live.action_atoms.iter().map(|a| (&a.expr, &a.env)))
}

/// The expressions the search evaluates on states and steps (all but the
/// initial predicate and the liveness atoms), with their environments.
fn search_exprs(base: &InterpModel) -> impl Iterator<Item = (&hir::Expr, &Env)> {
    static EMPTY: std::sync::OnceLock<Env> = std::sync::OnceLock::new();
    let empty = EMPTY.get_or_init(Env::default);
    let checks = base
        .constraint_exprs()
        .iter()
        .chain(base.action_constraint_exprs())
        .chain(base.invariant_exprs())
        .chain(base.action_property_exprs())
        .chain(base.view_expr());
    base.actions().iter().map(|a| (&a.expr, &a.env)).chain(checks.map(move |e| (e, empty)))
}

/// Whether evaluating `roots` may evaluate volatile builtins (see
/// `search_is_volatile`).
fn volatile(base: &InterpModel, mut stack: Vec<hir::Expr>) -> bool {
    use tlx_sema::hir::{DefKind, ExprKind as H, OpRef};
    let ip = &base.ip;
    let mut seen = HashSet::new();
    while let Some(e) = stack.pop() {
        let def = match &*e.kind {
            H::Builtin { op, .. } | H::Apply { op: OpRef::Builtin(op), .. } | H::OpArg(OpRef::Builtin(op)) if op.is_volatile() => {
                return true
            }
            H::Apply { op: OpRef::Def(d), .. } | H::OpArg(OpRef::Def(d)) => Some(*d),
            H::Apply { op: OpRef::Const(c), .. } | H::OpArg(OpRef::Const(c)) => match ip.const_op_ref(*c) {
                Some(OpRef::Def(d)) => Some(d),
                Some(OpRef::Builtin(op)) if op.is_volatile() => return true,
                _ => None,
            },
            _ => None,
        };
        if let Some(d) = def.map(|d| ip.redirect_def(d)).filter(|d| seen.insert(*d)) {
            let def = &ip.prog.defs[d.idx()];
            if def.builtin.is_some_and(|b| b.is_volatile()) {
                return true;
            }
            match &def.kind {
                DefKind::Op(b) => stack.push(b.clone()),
                DefKind::Fn { body, bounds } => {
                    stack.push(body.clone());
                    stack.extend(bounds.iter().map(|b| b.set.clone()));
                }
                DefKind::Pending => return true,
            }
        }
        tlx_sema::visit::children(&e, &mut |c| stack.push(c.clone()));
    }
    false
}

/// The BFS of a pre-run (not faithful, see `search_makes_strings`) on
/// `threads` threads, a level at a time, from `frontier` (with the
/// fingerprints `seen`), within `within` (of the number of distinct
/// states). `constrain`: whether to evaluate the constraints.
///
/// With several threads each thread observes into a watch of its own,
/// merged into `obs` after each level, when the layout is chosen anew if a
/// state did not fit. With one thread (also for volatile builtins, whose
/// effects are per thread: the caller's) the states are observed into `obs`
/// itself, in the order of a sequential queue, and the layout is chosen
/// anew at each state that did not fit: the observations that decide when
/// it settles are those of a sequential pre-run.
///
/// The distinct states seen, whether states were left unexpanded, and whether
/// generation stopped on a runtime error (after observing at least one state).
fn generation_bfs<'a>(
    base: &InterpModel,
    threads: usize,
    constrain: bool,
    chooser: &Chooser,
    obs: &mut Observed<'a>,
    (seen, mut frontier): (HashSet<u64>, Vec<State>),
    within: &(dyn Fn(usize) -> bool + Sync),
) -> Result<(usize, bool, bool), ModelError> {
    const SHARDS: usize = 64;
    let eager = threads <= 1;
    let mut shards: Vec<Mutex<HashSet<u64>>> = (0..SHARDS).map(|_| Mutex::new(HashSet::new())).collect();
    // The states only reached by transitions violating an
    // ACTION_CONSTRAINT (and not seen otherwise so far).
    let cut: Vec<Mutex<HashSet<u64>>> = (0..SHARDS).map(|_| Mutex::new(HashSet::new())).collect();
    let count = AtomicUsize::new(seen.len());
    for fp in seen {
        shards[fp as usize % SHARDS].get_mut().unwrap().insert(fp);
    }
    let err: Mutex<Option<ModelError>> = Mutex::new(None);
    let stop = AtomicBool::new(false);
    // (One thread: `within` is checked at each state, as the queue of a
    // sequential BFS is, not before each level.)
    while !frontier.is_empty() && (eager || within(count.load(Ordering::Relaxed))) {
        let next_index = AtomicUsize::new(0);
        let chosen = obs.chosen.clone();
        // Expand the frontier from the next unclaimed state on, observing
        // into `o`: the new states found, whether one did not fit the
        // layout, whether it stopped before the frontier was done.
        let expand = |abort: &tlx_base::par::Abort, o: &mut Observed<'a>| -> (Vec<State>, bool, bool) {
            let (mut out, mut miss, mut halted) = (Vec::new(), false, false);
            let mut see = |o: &mut Observed<'a>, vals: &[Value]| {
                if eager {
                    miss |= o.state(chooser, vals);
                } else {
                    miss |= chooser.count(&mut o.watch, o.chosen.as_ref(), vals);
                }
            };
            loop {
                let i = next_index.fetch_add(1, Ordering::Relaxed);
                if i >= frontier.len() {
                    break;
                }
                // (After `TLCSet("exit", TRUE)` the search expands no more states.)
                if stop.load(Ordering::Relaxed) || abort.requested() || base.stop_requested() || !within(count.load(Ordering::Relaxed)) {
                    halted = true;
                    break;
                }
                let s = &frontier[i];
                let r = (|| -> Result<(), ModelError> {
                    if constrain && base.has_constraints() && !base.constraint(s)? {
                        return Ok(());
                    }
                    let mut e = None;
                    base.successors(s, &mut |t, _| {
                        if constrain && base.has_action_constraints() {
                            match base.action_constraint(s, &t) {
                                Ok(true) => {}
                                Ok(false) => {
                                    // (Encoded by the search all the same:
                                    // observed once, not expanded.)
                                    let k = t.fp as usize % SHARDS;
                                    if !shards[k].lock().unwrap().contains(&t.fp) && cut[k].lock().unwrap().insert(t.fp) {
                                        see(o, &t.vals);
                                    }
                                    return within(count.load(Ordering::Relaxed));
                                }
                                Err(x) => {
                                    e = Some(x);
                                    return false;
                                }
                            }
                        }
                        if shards[t.fp as usize % SHARDS].lock().unwrap().insert(t.fp) {
                            count.fetch_add(1, Ordering::Relaxed);
                            see(o, &t.vals);
                            out.push(t);
                        }
                        within(count.load(Ordering::Relaxed))
                    })?;
                    e.map_or(Ok(()), Err)
                })();
                if let Err(e) = r {
                    err.lock().unwrap().get_or_insert(e);
                    stop.store(true, Ordering::Relaxed);
                    break;
                }
            }
            (out, miss, halted)
        };
        let n = threads.min(frontier.len().div_ceil(16));
        let results: Vec<(Vec<State>, Option<Watch<'a>>, bool, bool)> = if eager {
            let (out, miss, halted) = expand(&tlx_base::par::Abort::new(), obs);
            vec![(out, None, miss, halted)]
        } else if n <= 1 {
            let mut o = Observed { watch: obs.watch.fresh(), chosen };
            let (out, miss, halted) = expand(&tlx_base::par::Abort::new(), &mut o);
            vec![(out, Some(o.watch), miss, halted)]
        } else {
            let pool = tlx_base::par::Pool { threads: n, stack: tlx_base::par::Stack::Eval };
            pool.map_owned((0..n).map(|_| Observed { watch: obs.watch.fresh(), chosen: chosen.clone() }).collect(), |abort, mut o| {
                let (out, miss, halted) = expand(abort, &mut o);
                Ok::<_, std::convert::Infallible>((out, Some(o.watch), miss, halted))
            })
            .unwrap()
        };
        let unexpanded = next_index.load(Ordering::Relaxed) < frontier.len();
        let mut next = Vec::new();
        let mut miss = false;
        let mut halted = false;
        for (out, w, m, h) in results {
            next.extend(out);
            if let Some(w) = w {
                obs.watch.merge(w);
            }
            miss |= m;
            halted |= h;
        }
        if let Some(e) = err.lock().unwrap().take() {
            let n = count.load(Ordering::Relaxed);
            if n == 0 {
                return Err(e);
            }
            return Ok((n, false, true));
        }
        if miss && !eager && chooser.settle > 0 {
            obs.chosen = Some(chooser.choose(&obs.watch));
        }
        // (A sequential queue also holds the states found before it stopped.)
        if unexpanded || (eager && halted && !next.is_empty()) {
            return Ok((count.load(Ordering::Relaxed), true, false));
        }
        frontier = next;
    }
    Ok((count.load(Ordering::Relaxed), !frontier.is_empty(), false))
}

/// The pre-run's result from what `w` observed in `states` distinct states
/// (`bounds`: see `type_bounds`).
fn result(w: &Watch, hints: &Hints, bounds: &[(usize, Shape)], states: usize, settled: bool) -> Prerun {
    let vars = &w.vars;
    let shapes = vars.finalize(hints);
    let mut refined = shapes.clone();
    for (var, b) in bounds {
        // (A bound not covering what the pre-run saw is not a bound: the
        // invariant is violated, or the bound is mistaken.)
        if bound_covers(b, &vars.shapes[*var]) {
            let r = refine(&refined[*var], b);
            if bound_covers(&r, &vars.shapes[*var]) {
                refined[*var] = r;
            }
        }
    }
    let bounded = refined.into_iter().enumerate().filter(|(i, r)| *r != shapes[*i]).collect();
    Prerun { shapes, defs: w.probe.finalize(hints), states, settled, report: None, bounded }
}

/// Bounds on state variables from the type invariants: conjuncts `x \in S`
/// and `x \subseteq S` of an INVARIANT (also through 0-ary definitions),
/// with `S` a constant set (see `set_elem_bound`). Every state checked
/// satisfies them, or the search stops with a violation: so they can size
/// the layout exactly where the pre-run only saw part of the values (e.g.
/// all messages of a protocol, `msgs \in SUBSET Message`).
fn type_bounds(base: &InterpModel) -> Vec<(usize, Shape)> {
    let mut out = Vec::new();
    for e in base.invariant_exprs() {
        collect_bounds(base, e, 0, &mut out);
    }
    out
}

fn collect_bounds(base: &InterpModel, e: &hir::Expr, depth: usize, out: &mut Vec<(usize, Shape)>) {
    use tlx_sema::builtins::Builtin as B;
    use tlx_sema::hir::{DefKind, ExprKind as H, OpRef};
    if depth > 16 {
        return;
    }
    let ip = &base.ip;
    match &*e.kind {
        H::And(es) => es.iter().for_each(|x| collect_bounds(base, x, depth + 1, out)),
        H::Apply { op: OpRef::Def(d), args } if args.is_empty() => {
            let d = ip.redirect_def(*d);
            let def = &ip.prog.defs[d.idx()];
            if let (None, DefKind::Op(body)) = (def.builtin, &def.kind) {
                if !ip.is_const_def(d) {
                    collect_bounds(base, body, depth + 1, out);
                }
            }
        }
        H::Builtin { op: op @ (B::In | B::SubsetEq), args } if args.len() == 2 => {
            let H::Var(v) = &*args[0].kind else { return };
            if !const_set_expr(base, &args[1], 0) {
                return;
            }
            let Ok(set) = ip.eval(&args[1], &tlx_eval::env::Env::default(), &tlx_eval::eval::Ctx::NONE) else { return };
            let elem = set_elem_bound(&set);
            let b = match op {
                B::In => elem,
                _ if elem == Shape::Dyn => elem,
                _ => {
                    let max_card = tlx_value::ops::cardinality(&set).ok().and_then(|n| usize::try_from(n).ok()).unwrap_or(usize::MAX);
                    Shape::Set { elem: Box::new(elem), max_card }
                }
            };
            if b != Shape::Dyn {
                out.push((v.idx(), b));
            }
        }
        _ => {}
    }
}

/// Whether `e` is a constant expression that is safe and cheap to evaluate
/// before the search: literals, constants, constant definitions (evaluated
/// once anyway) and set constructors over them, without nondeterministic or
/// side-effecting builtins. (Lazy sets such as `SUBSET S` and `[S -> T]` are
/// not enumerated by evaluating them.)
fn const_set_expr(base: &InterpModel, e: &hir::Expr, depth: usize) -> bool {
    use tlx_sema::hir::{ExprKind as H, OpRef};
    let ip = &base.ip;
    if depth > 32 {
        return false;
    }
    let all = |es: &mut dyn Iterator<Item = &hir::Expr>| -> bool {
        for x in es {
            if !const_set_expr(base, x, depth + 1) {
                return false;
            }
        }
        true
    };
    match &*e.kind {
        H::Num(_) | H::Str(_) | H::Bool(_) => true,
        H::Const(c) => match ip.const_op_ref(*c) {
            Some(OpRef::Def(d)) => ip.is_const_def(ip.redirect_def(d)),
            Some(_) => false,
            None => true,
        },
        H::Apply { op: OpRef::Def(d), args } => args.is_empty() && ip.is_const_def(ip.redirect_def(*d)),
        H::Builtin { op, args } | H::Apply { op: OpRef::Builtin(op), args } => {
            !op.is_volatile() && !makes_strings(*op) && all(&mut args.iter())
        }
        H::SetEnum(es) | H::Tuple(es) => all(&mut es.iter()),
        H::Record(fs) | H::RecordSet(fs) => all(&mut fs.iter().map(|f| &f.1)),
        H::FnSet { domain, range } => all(&mut [domain, range].into_iter()),
        _ => false,
    }
}

/// Random behaviors of at most `depth` steps from `inits`, as a simulation
/// generates them, until `deadline`, each successor observed; they stop
/// early once `observe` has reported no change for a while (half the CPU
/// time spent, at least 50ms of it, see `Chooser`); `constrain`: they end
/// at a state violating a CONSTRAINT and skip transitions violating an
/// ACTION_CONSTRAINT, as the simulation does. An evaluation error ends the
/// walks (the simulation reports it).
fn random_walks(
    base: &InterpModel,
    inits: &[State],
    depth: u32,
    deadline: Instant,
    constrain: bool,
    observe: &mut dyn FnMut(&[Value]) -> bool,
) {
    let start = process_cpu();
    let mut last_change = start;
    let mut rng = tlx_base::rng::SplitMix64::new(0x2545_f491_4f6c_dd1d);
    let mut below = |n: usize| rng.below(n);
    while !inits.is_empty() && Instant::now() < deadline {
        let mut s = inits[below(inits.len())].clone();
        for _ in 0..depth {
            if constrain && base.has_constraints() && !matches!(base.constraint(&s), Ok(true)) {
                break;
            }
            let mut next = Vec::new();
            let r = base.successors(&s, &mut |t, _| {
                if observe(&t.vals) {
                    last_change = process_cpu();
                }
                if !constrain || !base.has_action_constraints() || matches!(base.action_constraint(&s, &t), Ok(true)) {
                    next.push(t);
                }
                true
            });
            if r.is_err() || next.is_empty() || Instant::now() >= deadline {
                break;
            }
            s = next.swap_remove(below(next.len()));
        }
        let now = process_cpu();
        if base.stop_requested() || now.saturating_sub(last_change) > now.saturating_sub(start).div_f64(2.0).max(Duration::from_millis(50))
        {
            return;
        }
    }
}

/// Which expressions of the model may create strings, knowing the values
/// its variables can take (`StringMakers::for_states`: `Tail`, `SubSeq`
/// and `\o` on sequences do not count).
fn model_strings(base: &InterpModel) -> StringMakers<'_> {
    let actions: Vec<(&hir::Expr, &Env)> = search_exprs(base).chain(live_atoms_in(base)).collect();
    StringMakers::for_states(&base.ip, base.init_expr(), &actions)
}

/// Whether the search may create strings: in the initial predicate, the
/// actions, the constraints, the invariants, the action properties or the
/// VIEW. Strings are ordered by creation, as in TLC, so the
/// pre-run must then create them in the search's order: it is the search
/// (`faithful_prerun`) stopped at its budget, so that its states are a
/// prefix of the search's and their strings are created in the same order.
/// (Otherwise it only generates the states.) The liveness atoms alone do
/// not make the pre-run faithful: a pre-run that creates no strings cannot
/// create them out of order.
fn search_makes_strings(base: &InterpModel, strings: &StringMakers) -> bool {
    strings.expr(base.init_expr()) || search_exprs(base).any(|(e, env)| strings.expr_in(e, env))
}

/// Whether evaluating the liveness atoms (on the states and steps of the
/// behavior graph) may create strings.
fn live_makes_strings(base: &InterpModel, strings: &StringMakers) -> bool {
    live_atoms_in(base).any(|(e, env)| strings.expr_in(e, env))
}

/// Whether the report of a faithful pre-run that ends before its budget is
/// the report of the search with options `opts`: a search on one
/// worker, without -coverage, nor the disk from the start (`-spill always`,
/// testing), nor a fingerprint set of a fixed size (the pre-run gets the
/// search's growing one: it fills up as the search's), in which nothing
/// volatile is evaluated (output, registers, files, programs, random
/// choices: the pre-run's are undone, see `prerun_shapes`), the liveness
/// atoms included. (Checkpoints: see `faithful_prerun`; the behavior graph:
/// `Faithful::complete_results`.)
fn reuse_ok(base: &InterpModel, opts: &Options) -> bool {
    opts.workers == 1
        && !opts.coverage
        && opts.spill.mode() != SpillMode::Always
        && !opts.fp.fixed
        && !search_is_volatile(base)
        && !volatile(base, live_atoms(base).cloned().collect())
}

/// Whether generating the states may create strings: in the initial
/// predicate, the actions or the VIEW (which fingerprints use).
fn generation_makes_strings(base: &InterpModel, strings: &StringMakers) -> bool {
    strings.expr(base.init_expr())
        || base.actions().iter().any(|a| strings.expr_in(&a.expr, &a.env))
        || base.view_expr().is_some_and(|e| strings.expr(e))
}

/// Whether evaluating the CONSTRAINTs or ACTION_CONSTRAINTs may create
/// strings.
fn constraints_make_strings(base: &InterpModel, strings: &StringMakers) -> bool {
    base.constraint_exprs().iter().chain(base.action_constraint_exprs()).any(|e| strings.expr(e))
}

/// The states in which a candidate definition with scalar values is
/// evaluated before it is dropped (see `DefProbe::observe`).
const PROBE_SCALAR_STATES: u32 = 50;

/// Observes the values of candidate definitions in pre-run states.
struct DefProbe<'a> {
    base: &'a InterpModel,
    defs: &'a [DefId],
    obs: Observer,
    /// Dropped: failed to evaluate, lazy, too expensive, or scalar.
    failed: Vec<bool>,
    time: Vec<Duration>,
    count: Vec<u32>,
    /// The VIEW definition when its body is a tuple literal: (index in
    /// `defs`, observer of the components). Its components are observed
    /// separately, so that its shape is a tuple of their shapes (not
    /// homogenized like an array: they are usually unrelated variables).
    view_parts: Option<(usize, Observer)>,
    /// Index of the VIEW definition in `defs`: it is evaluated in every
    /// state anyway, so it is kept even if expensive, and normalized.
    view_at: Option<usize>,
    /// The values of the definitions in the state observed last (`false`
    /// for those that failed).
    last: Vec<Value>,
}

impl<'a> DefProbe<'a> {
    fn new(base: &'a InterpModel, defs: &'a [DefId]) -> DefProbe<'a> {
        let n = defs.len();
        let view_at = view_def(base).and_then(|d| defs.iter().position(|x| *x == d));
        let view_parts = view_at.and_then(|i| Some((i, Observer::for_slots(vec![Slot::Def(defs[i].0); view_tuple(base, defs[i])?.len()]))));
        DefProbe {
            base,
            defs,
            obs: Observer::for_slots(defs.iter().map(|d| Slot::Def(d.0)).collect()),
            failed: vec![false; n],
            time: vec![Duration::ZERO; n],
            count: vec![0; n],
            view_parts,
            view_at,
            last: Vec::new(),
        }
    }

    /// Observe a state; true if that changed some shape.
    fn observe(&mut self, vals: &[Value], hints: &Hints) -> bool {
        let mut dv = Vec::with_capacity(self.defs.len());
        for (i, d) in self.defs.iter().enumerate() {
            // A definition with scalar values (typically a predicate: an
            // invariant, a conjunct of one) is not materialized (see
            // `finalize`): after a few states it is no longer evaluated
            // (probing an invariant in every state can cost as much
            // as the rest of the pre-run).
            if !self.failed[i] && self.count[i] >= PROBE_SCALAR_STATES && self.view_at != Some(i) && self.obs.shapes[i].is_scalar() {
                self.failed[i] = true;
            }
            if !self.failed[i] {
                match self.eval(i, *d, vals) {
                    Some(v) => {
                        if let Some((j, parts)) = &mut self.view_parts {
                            if *j == i {
                                match &v {
                                    Value::Tuple(es) if es.len() == parts.shapes.len() => {
                                        parts.observe(es);
                                    }
                                    _ => self.view_parts = None,
                                }
                            }
                        }
                        dv.push(v);
                        continue;
                    }
                    None => self.failed[i] = true,
                }
            }
            dv.push(Value::Bool(false));
        }
        let changed = self.obs.observe_with(&dv, hints);
        self.last = dv;
        changed
    }

    /// The value of definition `d` (number `i`) in state `vals`, if it is
    /// cheap and eager. Expensive definitions are not worth materializing
    /// (and would make the pre-run slow): at most 200µs per evaluation on
    /// average (after 50 evaluations), 100ms for any single one.
    fn eval(&mut self, i: usize, d: DefId, vals: &[Value]) -> Option<Value> {
        let t0 = Instant::now();
        let mut r = self.base.ip.eval_def_in_state(d, vals);
        if self.view_at == Some(i) {
            r = r.and_then(|v| Ok(v.normalize()?));
        }
        let dt = t0.elapsed();
        self.time[i] += dt;
        self.count[i] += 1;
        // (The VIEW is evaluated in every state anyway.)
        let cheap = self.view_at == Some(i)
            || dt < Duration::from_millis(100) && (self.count[i] < 50 || self.time[i] / self.count[i] < Duration::from_micros(200));
        r.ok().filter(|v| cheap && eager(v))
    }

    /// Shapes of the definitions worth materializing: containers without
    /// dynamic parts that never failed.
    fn finalize(&self, hints: &Hints) -> Vec<Option<Shape>> {
        let mut shapes = self.obs.finalize(hints);
        // A tuple VIEW whose dynamic parts are all state variables is kept:
        // those components are encoded like the variables (`View::compile`),
        // as handles of values the states hold anyway.
        let mut view_dyn_ok = false;
        if let Some((i, parts)) = &self.view_parts {
            let parts = parts.finalize(hints);
            view_dyn_ok = view_tuple(self.base, self.defs[*i]).is_some_and(|es| {
                es.len() == parts.len() && es.iter().zip(&parts).all(|(e, s)| !has_dyn(s) || matches!(&*e.kind, hir::ExprKind::Var(_)))
            });
            shapes[*i] = Shape::Tuple(parts.into());
        }
        let view_at = self.view_at;
        shapes
            .into_iter()
            .zip(&self.failed)
            .enumerate()
            .map(|(i, (s, &failed))| {
                let container = matches!(
                    s,
                    Shape::Set { .. }
                        | Shape::Fcn { .. }
                        | Shape::Map { .. }
                        | Shape::Record(_)
                        | Shape::Tuple(_)
                        | Shape::Seq { .. }
                        | Shape::Union(_)
                );
                // (A scalar VIEW is kept: its encoding is what the
                // fingerprints are computed from.)
                let scalar_view = view_at == Some(i) && s.is_scalar();
                let dyn_ok = view_at == Some(i) && view_dyn_ok;
                (!failed && (container || scalar_view) && (!has_dyn(&s) || dyn_ok)).then_some(s)
            })
            .collect()
    }
}

/// No lazy parts (a lazy set's shape could only be found by enumerating it).
fn eager(v: &Value) -> bool {
    match v {
        Value::LazySet(_) | Value::LazyFcn(_) => false,
        Value::Set(es) | Value::Tuple(es) => es.iter().all(eager),
        Value::Record(fs) => fs.iter().all(|(_, x)| eager(x)),
        Value::Fcn(ps, _) => ps.iter().all(|(k, x)| eager(k) && eager(x)),
        _ => true,
    }
}

pub(super) fn has_dyn(s: &Shape) -> bool {
    match s {
        Shape::Dyn | Shape::Never => true,
        Shape::Set { elem, .. } | Shape::Seq { elem, .. } => has_dyn(elem),
        Shape::Fcn { range, .. } | Shape::Map { range, .. } => has_dyn(range),
        Shape::Record(fs) => fs.iter().any(|(_, f)| has_dyn(f)),
        Shape::Tuple(ps) | Shape::Union(ps) => ps.iter().any(has_dyn),
        _ => false,
    }
}
#[cfg(test)]
mod tests;
