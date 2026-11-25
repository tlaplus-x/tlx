//! Performance statistics (`-stats`): where the time and the work of a run
//! went.
//!
//! Everything here is off unless `enable` was called; every hook first
//! checks `on()` (one relaxed load of a static), so the cost of the hooks
//! in a normal run is a predictable branch.
//!
//! When on:
//! - **phases** (front end, pre-run, lowering, C builds, search, liveness,
//!   ...) are recorded by the threads that run them in a small global
//!   registry (`set`, `add_secs`, `add_count`): rare events only;
//! - **hot counters** (states expanded, successors per action, fingerprint
//!   set probes, encodings, ...) are per-thread (`thread_local`), flushed
//!   into the global totals when a worker ends (`worker_done`) or before
//!   the report (`flush`). Periodic completed-unit snapshots let another thread
//!   report a partial run without accessing active workers' thread-local state;
//! - **times** inside the search are sampled: one *unit* of work (a state
//!   expanded, a simulation step) in `SAMPLE_EVERY` is timed in detail
//!   (`Span`s around actions, invariants, fingerprints, ...), and the
//!   totals are extrapolated from the sampled units. Spans nest; each
//!   records its exclusive time (its time minus that of the spans inside
//!   it), so the categories add up to the time of the units.
//! - worker utilization (busy, idle, waiting at the level barrier) is
//!   timed for every wait (they are rare).

use std::cell::RefCell;
use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use std::sync::{Arc, Mutex, OnceLock};
use std::time::{Duration, Instant};

mod report;

pub use self::report::{json, text};

static ON: AtomicBool = AtomicBool::new(false);
static START: OnceLock<Instant> = OnceLock::new();
/// One unit in this many is timed (default 8).
static SAMPLE_EVERY: AtomicU32 = AtomicU32::new(8);

/// Whether statistics are collected. With the `no-stats` feature (only for
/// measuring the cost of the hooks) never: the hooks compile away.
#[inline(always)]
pub fn on() -> bool {
    !cfg!(feature = "no-stats") && ON.load(Ordering::Relaxed)
}

/// Pause statistics collection around a bounded probe outside the search, so
/// the probe's evaluations do not change a `-stats` report. Returns whether
/// they were on, for [`resume`].
pub fn suspend() -> bool {
    let was_on = on();
    ON.store(false, Ordering::Relaxed);
    was_on
}

/// Resume collection paused by [`suspend`].
pub fn resume(was_on: bool) {
    if was_on {
        ON.store(true, Ordering::Relaxed);
    }
}

/// Collect statistics from now on, timing one unit of work in
/// `sample_every` (call at the start of the process: the time origin of
/// `since_start`).
pub fn enable(sample_every: u32) {
    START.get_or_init(Instant::now);
    SAMPLE_EVERY.store(sample_every.max(1), Ordering::Relaxed);
    ON.store(true, Ordering::Relaxed);
}

/// Time since `enable`.
pub fn since_start() -> Duration {
    START.get().map_or(Duration::ZERO, |t| t.elapsed())
}

// ----------------------------------------------------------------------
// phases: a registry of named metrics (rare events)

/// A recorded metric.
#[derive(Clone, Debug, PartialEq)]
pub enum Metric {
    Secs(f64),
    Count(u64),
    /// A size in bytes.
    Bytes(u64),
    Text(String),
}

/// Metrics whose key starts with this are reported in the memory section.
pub const MEMORY: &str = "memory: ";

static PHASES: Mutex<Vec<(String, Metric)>> = Mutex::new(Vec::new());

fn with_phase(key: &str, f: impl FnOnce(Option<&mut Metric>) -> Option<Metric>) {
    let mut p = PHASES.lock().unwrap_or_else(|e| e.into_inner());
    match p.iter_mut().find(|(k, _)| k == key) {
        Some((_, m)) => {
            if let Some(n) = f(Some(m)) {
                *m = n;
            }
        }
        None => {
            if let Some(n) = f(None) {
                p.push((key.to_string(), n));
            }
        }
    }
}

/// Set metric `key` (if on).
pub fn set(key: &str, m: Metric) {
    if on() {
        with_phase(key, |_| Some(m));
    }
}

/// Add `d` to the time `key` (if on).
pub fn add_secs(key: &str, d: Duration) {
    if on() {
        with_phase(key, |m| match m {
            Some(Metric::Secs(s)) => Some(Metric::Secs(*s + d.as_secs_f64())),
            _ => Some(Metric::Secs(d.as_secs_f64())),
        });
    }
}

/// Add `n` to the count `key` (if on).
pub fn add_count(key: &str, n: u64) {
    if on() {
        with_phase(key, |m| match m {
            Some(Metric::Count(c)) => Some(Metric::Count(*c + n)),
            _ => Some(Metric::Count(n)),
        });
    }
}

/// Raise the count `key` to `n` if it is lower (if on).
pub fn max_count(key: &str, n: u64) {
    if on() {
        with_phase(key, |m| match m {
            Some(Metric::Count(c)) if *c >= n => None,
            _ => Some(Metric::Count(n)),
        });
    }
}

/// The recorded metrics, in order of first record.
pub fn phases() -> Vec<(String, Metric)> {
    PHASES.lock().unwrap_or_else(|e| e.into_inner()).clone()
}

fn phase(key: &str) -> Option<Metric> {
    PHASES.lock().unwrap_or_else(|e| e.into_inner()).iter().find(|(k, _)| k == key).map(|(_, m)| m.clone())
}

// ----------------------------------------------------------------------
// hot counters and sampled times (per thread)

/// Counters.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(usize)]
pub enum C {
    /// Units of work: states expanded, simulation steps.
    Units,
    /// Units timed in detail.
    Sampled,
    /// Successors generated.
    Generated,
    /// Fingerprint set: insertions tried, new fingerprints, extra slots
    /// probed (collisions in the table).
    FpInserts,
    FpNew,
    FpProbes,
    /// Encoded states produced by the interpreter and encoded (compiled tier).
    Encodes,
    /// Encoded states decoded to values (for the interpreter, rendering, ...).
    Decodes,
    /// Fingerprints computed (compiled tier: of encodings).
    Fingerprints,
    /// Simulation: behaviors generated.
    Traces,
    /// Interpreter: bodies of 0-ary state-level definitions evaluated
    /// (memo misses included) in a current-state and in a next-state
    /// (primed) context.
    DefEvals,
    DefEvalsPrimed,
}
const NC: usize = C::DefEvalsPrimed as usize + 1;
const C_NAMES: [&str; NC] = [
    "units",
    "sampled_units",
    "generated",
    "fp_inserts",
    "fp_new",
    "fp_probes",
    "encodes",
    "decodes",
    "fingerprints",
    "traces",
    "def_evals",
    "def_evals_primed",
];

/// Sampled timers (exclusive times of the categories of work).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(usize)]
pub enum T {
    /// A unit's own work (queues, trace log, bookkeeping).
    Unit,
    /// Processing a successor (explorer bookkeeping).
    Successor,
    /// CONSTRAINT and ACTION_CONSTRAINT.
    Constraint,
    /// Inserting into the fingerprint set.
    FpSet,
    /// Invariant checks (dispatch; the invariants themselves are tallied
    /// per invariant).
    Invariants,
    /// Action properties (`[][A]_v`) on transitions.
    Transition,
    /// Computing fingerprints.
    Fingerprint,
    /// Encoding values into the state layout.
    Encode,
    /// Decoding encoded states into values.
    Decode,
}
const NT: usize = T::Decode as usize + 1;
const T_NAMES: [&str; NT] = ["unit", "successor", "constraint", "fpset", "invariants", "transition", "fingerprint", "encode", "decode"];
const T_LABELS: [&str; NT] = [
    "explorer, per state",
    "explorer, per successor",
    "constraints",
    "fingerprint set",
    "invariants (dispatch)",
    "action properties (dispatch)",
    "fingerprinting",
    "encoding values",
    "decoding states",
];

/// How an action or a predicate was evaluated.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(usize)]
pub enum Path {
    /// Generated C.
    Native,
    /// Lowered IR, in the IR executor.
    Ir,
    /// The interpreter (not compiled).
    Interp,
    /// The interpreter after compiled code failed or gave up.
    Fallback,
    /// Generated C calling host regions (mixed mode).
    Mixed,
}
const NP: usize = 5;
const P_NAMES: [&str; NP] = ["native", "ir", "interp", "fallback", "mixed"];

/// Calls and sampled time of an action or predicate, by path.
#[derive(Clone, Copy, Debug, Default)]
struct Tally {
    /// Native evaluations that entered no host region, including mixed short circuits.
    fully_native: u64,
    calls: [u64; NP],
    sampled: [u64; NP],
    ns: [u64; NP],
    /// Successors produced (actions).
    succs: u64,
    /// Host region evaluations of its mixed calls, and how many failed.
    regions: u64,
    region_errors: u64,
}

impl Tally {
    fn merge(&mut self, o: &Tally) {
        for p in 0..NP {
            self.calls[p] += o.calls[p];
            self.sampled[p] += o.sampled[p];
            self.ns[p] += o.ns[p];
        }
        self.fully_native += o.fully_native;
        self.succs += o.succs;
        self.regions += o.regions;
        self.region_errors += o.region_errors;
    }
}

/// Utilization of one worker thread.
#[derive(Clone, Copy, Debug, Default)]
struct WorkerTimes {
    life_ns: u64,
    idle_ns: u64,
    barrier_ns: u64,
    units: u64,
}

/// What a thread collected.
#[derive(Clone, Debug)]
struct Local {
    c: [u64; NC],
    t: [u64; NT],
    actions: Vec<Tally>,
    invariants: Vec<Tally>,
    aprops: Vec<Tally>,
    /// Units expanded per depth.
    levels: Vec<u64>,
    idle_ns: u64,
    barrier_ns: u64,
    /// Whether the current unit is timed.
    sampling: bool,
    /// Units until the next timed one.
    countdown: u32,
    /// Exclusive time of the spans ended so far (see `Span`).
    nested: u64,
    /// Host watermarks by evaluation kind. Nested successor predicates must
    /// not make an enclosing native action appear to have entered the host.
    region_evals: [u64; 3],
    /// Inside a search unit (only then are actions and predicates tallied,
    /// so that e.g. the liveness graph build does not count).
    in_unit: bool,
}

impl Local {
    const fn new() -> Local {
        Local {
            c: [0; NC],
            t: [0; NT],
            actions: Vec::new(),
            invariants: Vec::new(),
            aprops: Vec::new(),
            levels: Vec::new(),
            idle_ns: 0,
            barrier_ns: 0,
            sampling: false,
            countdown: 0,
            nested: 0,
            region_evals: [0; 3],
            in_unit: false,
        }
    }

    fn merge(&mut self, o: &Local) {
        for i in 0..NC {
            self.c[i] += o.c[i];
        }
        for i in 0..NT {
            self.t[i] += o.t[i];
        }
        for (dst, src) in [(&mut self.actions, &o.actions), (&mut self.invariants, &o.invariants), (&mut self.aprops, &o.aprops)] {
            if dst.len() < src.len() {
                dst.resize(src.len(), Tally::default());
            }
            for (d, s) in dst.iter_mut().zip(src) {
                d.merge(s);
            }
        }
        if self.levels.len() < o.levels.len() {
            self.levels.resize(o.levels.len(), 0);
        }
        for (d, s) in self.levels.iter_mut().zip(&o.levels) {
            *d += s;
        }
        self.idle_ns += o.idle_ns;
        self.barrier_ns += o.barrier_ns;
    }
}

thread_local! {
    static LOCAL: RefCell<Local> = const { RefCell::new(Local::new()) };
    static PUBLISHED: RefCell<Option<Instant>> = const { RefCell::new(None) };
}

struct Global {
    total: Local,
    workers: Vec<WorkerTimes>,
    live: Vec<(std::thread::ThreadId, Local)>,
    action_names: Vec<String>,
    invariant_names: Vec<String>,
    aprop_names: Vec<String>,
}

static GLOBAL: Mutex<Global> = Mutex::new(Global {
    total: Local::new(),
    workers: Vec::new(),
    live: Vec::new(),
    action_names: Vec::new(),
    invariant_names: Vec::new(),
    aprop_names: Vec::new(),
});

fn global() -> std::sync::MutexGuard<'static, Global> {
    GLOBAL.lock().unwrap_or_else(|e| e.into_inner())
}

#[inline]
fn local<R>(f: impl FnOnce(&mut Local) -> R) -> R {
    LOCAL.with(|l| f(&mut l.borrow_mut()))
}

// The hooks below are called on hot paths: when off they are a load and a
// branch; everything else is out of line (`#[inline(never)]`), so that the
// hooks do not bloat the functions they are in.

/// Add `n` to counter `c` (if on).
#[inline(always)]
pub fn count(c: C, n: u64) {
    if on() {
        count_on(c, n);
    }
}

#[inline(never)]
fn count_on(c: C, n: u64) {
    local(|l| l.c[c as usize] += n);
}

/// A successor generated by action `a` (if on).
#[inline(always)]
pub fn successor(a: u32) {
    if on() {
        successor_on(a);
    }
}

#[inline(never)]
fn successor_on(a: u32) {
    local(|l| {
        l.c[C::Generated as usize] += 1;
        let a = a as usize;
        if l.actions.len() <= a {
            l.actions.resize(a + 1, Tally::default());
        }
        l.actions[a].succs += 1;
    });
}

/// Whether this thread is evaluating a measured search unit.
#[inline]
pub fn in_search_unit() -> bool {
    on() && local(|l| l.in_unit)
}

/// What a function evaluated by tally `kind` (`Span`'s 0: action, 1:
/// invariant, 2: action property) and index `i` did in host regions:
/// `evals` evaluations, `errors` of them failed (if on).
#[inline(always)]
pub fn regions(kind: usize, i: usize, evals: u64, errors: u64) {
    if on() && evals > 0 {
        regions_on(kind, i, evals, errors);
    }
}

#[inline(never)]
fn regions_on(kind: usize, i: usize, evals: u64, errors: u64) {
    local(|l| {
        if !l.in_unit {
            return;
        }
        let t = tally(
            match kind {
                0 => &mut l.actions,
                1 => &mut l.invariants,
                _ => &mut l.aprops,
            },
            i,
        );
        t.regions += evals;
        l.region_evals[kind.min(2)] += evals;
        t.region_errors += errors;
    });
}

/// The names of the actions, invariants and action properties of the
/// model being checked (for the report).
pub fn set_names(actions: &[String], invariants: &[String], aprops: &[String]) {
    if on() {
        let mut g = global();
        g.action_names = actions.to_vec();
        g.invariant_names = invariants.to_vec();
        g.aprop_names = aprops.to_vec();
    }
}

/// A timed section of a sampled unit (see the module documentation).
#[must_use]
pub enum Span {
    Off,
    /// On, but the current unit is not timed: only counts.
    Unsampled {
        regions0: [u64; 3],
    },
    Sampled {
        t0: Instant,
        nested0: u64,
        regions0: [u64; 3],
    },
}

/// Start a span (end it with one of `Span`'s methods).
#[inline(always)]
pub fn span() -> Span {
    if !on() {
        return Span::Off;
    }
    span_on()
}

#[inline(never)]
fn span_on() -> Span {
    local(|l| {
        if l.sampling {
            Span::Sampled { t0: Instant::now(), nested0: l.nested, regions0: l.region_evals }
        } else {
            Span::Unsampled { regions0: l.region_evals }
        }
    })
}

/// Exclusive time of a span ending now, recorded as nested time.
#[inline]
fn exclusive(l: &mut Local, t0: Instant, nested0: u64) -> u64 {
    let elapsed = t0.elapsed().as_nanos() as u64;
    let excl = elapsed.saturating_sub(l.nested - nested0);
    l.nested += excl;
    excl
}

fn tally(v: &mut Vec<Tally>, i: usize) -> &mut Tally {
    if v.len() <= i {
        v.resize(i + 1, Tally::default());
    }
    &mut v[i]
}

impl Span {
    /// End as timer `t`.
    #[inline(always)]
    pub fn end(self, t: T) {
        if let Span::Sampled { .. } = self {
            self.end_sampled(t);
        }
    }

    #[inline(never)]
    fn end_sampled(self, t: T) {
        if let Span::Sampled { t0, nested0, .. } = self {
            local(|l| {
                let x = exclusive(l, t0, nested0);
                l.t[t as usize] += x;
            });
        }
    }

    /// End as a run of action `i` by `path`.
    #[inline(always)]
    pub fn action(self, i: usize, path: Path) {
        if !matches!(self, Span::Off) {
            self.pred(i, path, 0)
        }
    }

    /// End as a check of invariant `i` by `path`.
    #[inline(always)]
    pub fn invariant(self, i: usize, path: Path) {
        if !matches!(self, Span::Off) {
            self.pred(i, path, 1)
        }
    }

    /// End as a check of action property `i` by `path`.
    #[inline(always)]
    pub fn aprop(self, i: usize, path: Path) {
        if !matches!(self, Span::Off) {
            self.pred(i, path, 2)
        }
    }

    /// End as a run of `kind` (0: action, 1: invariant, 2: action property).
    #[inline(never)]
    fn pred(self, i: usize, path: Path, kind: usize) {
        let (t0, nested0, regions0) = match self {
            Span::Off => return,
            Span::Unsampled { regions0 } => (None, 0, regions0),
            Span::Sampled { t0, nested0, regions0 } => (Some(t0), nested0, regions0),
        };
        local(|l| {
            if !l.in_unit {
                return;
            }
            let x = t0.map(|t0| exclusive(l, t0, nested0));
            let fully_native = matches!(path, Path::Native | Path::Mixed) && regions0[kind] == l.region_evals[kind];
            let v = match kind {
                0 => &mut l.actions,
                1 => &mut l.invariants,
                _ => &mut l.aprops,
            };
            let t = tally(v, i);
            t.calls[path as usize] += 1;
            t.fully_native += u64::from(fully_native);
            if let Some(x) = x {
                t.sampled[path as usize] += 1;
                t.ns[path as usize] += x;
            }
        })
    }
}

/// Start a unit of work at `depth` (a state expanded, a simulation step);
/// end it with `end_unit`.
#[inline(always)]
pub fn begin_unit(depth: u32) -> Span {
    if !on() {
        return Span::Off;
    }
    begin_unit_on(depth)
}

#[inline(never)]
fn begin_unit_on(depth: u32) -> Span {
    local(|l| {
        l.c[C::Units as usize] += 1;
        l.in_unit = true;
        let d = depth as usize;
        if l.levels.len() <= d {
            l.levels.resize(d + 1, 0);
        }
        l.levels[d] += 1;
        if l.countdown == 0 {
            l.countdown = SAMPLE_EVERY.load(Ordering::Relaxed) - 1;
            l.sampling = true;
            l.c[C::Sampled as usize] += 1;
            Span::Sampled { t0: Instant::now(), nested0: l.nested, regions0: l.region_evals }
        } else {
            l.countdown -= 1;
            Span::Unsampled { regions0: l.region_evals }
        }
    })
}

/// End a unit started by `begin_unit`.
#[inline(always)]
pub fn end_unit(s: Span) {
    if !matches!(s, Span::Off) {
        end_unit_on(s);
    }
}

#[inline(never)]
fn end_unit_on(s: Span) {
    s.end(T::Unit);
    local(|l| {
        l.sampling = false;
        l.in_unit = false;
        // Check the clock only occasionally; publish complete units, never
        // reset sampling or nested-span bookkeeping during an active search.
        if l.c[C::Units as usize] % 256 == 1 {
            PUBLISHED.with(|last| {
                let mut last = last.borrow_mut();
                if last.is_none_or(|t| t.elapsed() >= Duration::from_millis(250)) {
                    let id = std::thread::current().id();
                    let mut g = global();
                    match g.live.iter_mut().find(|(thread, _)| *thread == id) {
                        Some((_, snapshot)) => *snapshot = l.clone(),
                        None => g.live.push((id, l.clone())),
                    }
                    *last = Some(Instant::now());
                }
            });
        }
    });
}

/// Time a wait of a worker: at the level barrier (`barrier`) or for work.
pub struct Wait(Option<(Instant, bool)>);

#[inline]
pub fn wait(barrier: bool) -> Wait {
    Wait(on().then(|| (Instant::now(), barrier)))
}

impl Drop for Wait {
    fn drop(&mut self) {
        if let Some((t0, barrier)) = self.0 {
            let ns = t0.elapsed().as_nanos() as u64;
            local(|l| if barrier { l.barrier_ns += ns } else { l.idle_ns += ns });
        }
    }
}

/// Take this thread's counters (leaving them empty).
fn take_local() -> Local {
    local(|l| std::mem::replace(l, Local::new()))
}

/// A worker thread that ran for `life` ends: its counters go to the totals.
pub fn worker_done(life: Duration) {
    if !on() {
        return;
    }
    let l = take_local();
    let mut g = global();
    g.live.retain(|(id, _)| *id != std::thread::current().id());
    g.workers.push(WorkerTimes {
        life_ns: life.as_nanos() as u64,
        idle_ns: l.idle_ns,
        barrier_ns: l.barrier_ns,
        units: l.c[C::Units as usize],
    });
    g.total.merge(&l);
}

/// Move this thread's counters to the totals (e.g. the main thread's).
pub fn flush() {
    if on() {
        let l = take_local();
        let mut g = global();
        g.live.retain(|(id, _)| *id != std::thread::current().id());
        g.total.merge(&l);
    }
}

/// Insert `fp` into `set` (by worker `me`, `FpSet::insert_by`), counting
/// (and timing, in a timed unit) the insertion and its probes.
#[inline(always)]
pub fn fp_insert(set: &crate::fpset::FpSet, me: usize, fp: u64, high: impl FnOnce()) -> Result<bool, crate::fpset::Full> {
    if !on() {
        return set.insert_by(me, fp, &mut 0, high);
    }
    fp_insert_on(set, me, fp, high)
}

#[inline(never)]
fn fp_insert_on(set: &crate::fpset::FpSet, me: usize, fp: u64, high: impl FnOnce()) -> Result<bool, crate::fpset::Full> {
    let sp = span();
    let mut probes = 0;
    let r = set.insert_by(me, fp, &mut probes, high);
    sp.end(T::FpSet);
    local(|l| {
        l.c[C::FpInserts as usize] += 1;
        l.c[C::FpNew as usize] += matches!(r, Ok(true)) as u64;
        l.c[C::FpProbes as usize] += probes;
    });
    r
}

/// Memory of a search, as the explorer knows it at its end (sizes of the
/// in-memory structures; see `search_done`).
pub struct SearchMem {
    /// The units per depth before the search (`levels_snapshot`).
    pub levels0: Vec<u64>,
    /// Current and highest sampled sum of registered memory gauges.
    pub accounted: (usize, usize),
    /// The most memory the frontier's blocks held, and whether states were
    /// encoded (else the bytes do not count the states' heap data).
    pub queue_peak: (usize, bool),
    /// Trace log: entries and allocated bytes.
    pub log_entries: usize,
    pub log_bytes: usize,
    /// The archive (for resuming after a layout miss): the states it
    /// holds at the end (None if it was dropped), the most bytes it held.
    pub archived: Option<usize>,
    pub archive_peak: usize,
    pub retaining: bool,
    /// The memory budget (bytes) and the highest pressure stage reached,
    /// if limited.
    pub budget: Option<(usize, crate::mem::Stage)>,
}

/// The units per depth at the start of the latest search run, and the
/// units of earlier runs expanded again by later ones (`search_start`).
static RUNS: Mutex<Option<(Vec<u64>, u64)>> = Mutex::new(None);

/// A search run of the run's own (not a quiet pre-run search) starts: from
/// the initial states (`resume_level` None), or resuming a stopped run at
/// the depth `resume_level`. The units of earlier runs this one does again
/// are counted as repeated expansions: from the initial states all of
/// them, resuming those of the stopped run at that depth or deeper.
pub fn search_start(resume_level: Option<u32>) {
    if !on() {
        return;
    }
    let now = levels_snapshot();
    let total: u64 = now.iter().sum();
    let mut runs = RUNS.lock().unwrap_or_else(|e| e.into_inner());
    let repeated = match runs.as_mut() {
        None => 0,
        Some((prev, repeated)) => {
            *repeated = match resume_level {
                None => total,
                Some(l) => *repeated + (l as usize..now.len()).map(|d| now[d] - prev.get(d).copied().unwrap_or(0)).sum::<u64>(),
            };
            *repeated
        }
    };
    *runs = Some((now, repeated));
    if repeated > 0 {
        set("states expanded again (layout restarts, resumes)", Metric::Count(repeated));
    }
}

/// The units per depth recorded so far (all threads flushed).
pub fn levels_snapshot() -> Vec<u64> {
    if !on() {
        return Vec::new();
    }
    global().total.levels.clone()
}

/// The page size assumed for the fingerprint set's touched-memory estimate.
const PAGE: f64 = if cfg!(all(target_os = "macos", target_arch = "aarch64")) { 16384.0 } else { 4096.0 };

/// A search (`explore`) ended after `d`, with fingerprint set `seen`;
/// records its time, the fingerprint set's use and the memory of its
/// structures (`mem`).
pub fn search_done(d: Duration, seen: &crate::fpset::FpSet, resumable: bool, mem: SearchMem) {
    if !on() {
        return;
    }
    add_secs("search", d);
    add_count("search runs", 1);
    if resumable {
        add_count("search runs stopped resumable", 1);
    }
    let (n, slots) = (seen.table_len() as f64, seen.slots() as f64);
    set("fpset slots", Metric::Count(slots as u64));
    set("fpset entries", Metric::Count(seen.len() as u64));
    set("fpset load", Metric::Text(format!("{:.2}%", 100.0 * n / slots.max(1.0))));
    let limit = seen.limit() as u64;
    set("fpset limit (slots)", if limit > slots as u64 { Metric::Count(limit) } else { Metric::Text("fixed (-fpmem)".into()) });
    if seen.shards() > 1 {
        set("fpset shards (-fpbits)", Metric::Count(seen.shards() as u64));
    }
    let (grows, grow_time) = seen.grows();
    if grows > 0 {
        add_count("fpset grows", grows);
        add_secs("fpset growing", grow_time);
    }
    // Memory. A table is zeroed lazily by the OS; fingerprints are
    // uniform, so the pages touched by n entries are about
    // pages * (1 - exp(-n / pages)) (all of them after a growth, which
    // fills the new table to at least 3/8).
    let reserved = seen.table_bytes_now() as f64;
    let pages = (reserved / PAGE).max(1.0);
    let touched = pages * (1.0 - (-n / pages).exp()) * PAGE;
    let max = |key: &str, b: u64| {
        let key = format!("{MEMORY}{key}");
        with_phase(&key, |m| match m {
            Some(Metric::Bytes(x)) if *x >= b => None,
            _ => Some(Metric::Bytes(b)),
        })
    };
    max("fingerprint set table", reserved as u64);
    max("fingerprint set touched (est.)", touched as u64);
    if grows > 0 {
        max("fingerprint set peak (growing: both tables)", seen.peak_bytes() as u64);
    }
    set(&format!("{MEMORY}accounted at search end"), Metric::Bytes(mem.accounted.0 as u64));
    max("accounted peak (sampled)", mem.accounted.1 as u64);
    max("trace log", mem.log_bytes as u64);
    if let Some((total, stage)) = mem.budget {
        set(BUDGET, Metric::Bytes(total as u64));
        with_phase(&format!("{MEMORY}budget pressure stage"), |m| match m {
            Some(Metric::Text(t)) if t.as_str() >= stage.describe() => None,
            _ => Some(Metric::Text(stage.describe().into())),
        });
    }
    set(&format!("{MEMORY}trace log entries"), Metric::Count(mem.log_entries as u64));
    // The frontier: at most two adjacent levels are queued at a time.
    let levels = levels_snapshot();
    let width = |d: usize| levels.get(d).copied().unwrap_or(0).saturating_sub(mem.levels0.get(d).copied().unwrap_or(0));
    let peak = (0..levels.len()).map(|d| width(d) + width(d + 1)).max().unwrap_or(0);
    set(&format!("{MEMORY}frontier peak tasks (est.)"), Metric::Count(peak));
    let (queue_peak, encoded) = mem.queue_peak;
    max(if encoded { "frontier peak (blocks)" } else { "frontier peak, without state values" }, queue_peak as u64);
    if mem.retaining {
        max("archive peak (for resuming)", mem.archive_peak as u64);
        match mem.archived {
            Some(k) => set(&format!("{MEMORY}archived states (for resuming)"), Metric::Count(k as u64)),
            None => set(
                &format!("{MEMORY}archived states (for resuming)"),
                Metric::Text("dropped (disk unavailable; archive allowance or memory budget exceeded)".into()),
            ),
        }
    }
}

/// The disk layer (`crate::io`) after a search: the bytes its spill files
/// were written and read so far (all searches of the run), the most they
/// held, the blocks written, and the trace-log blocks on disk at the end
/// of this search.
pub fn spill_done(written: u64, read: u64, peak: u64, blocks: u64, log_blocks: usize, queue_segs: u64, archive_segs: u64) {
    if !on() {
        return;
    }
    set("disk: spilled bytes written", Metric::Bytes(written));
    set("disk: spilled bytes read back", Metric::Bytes(read));
    set("disk: spill files peak", Metric::Bytes(peak));
    set("disk: spilled blocks", Metric::Count(blocks));
    set("disk: trace-log blocks on disk", Metric::Count(log_blocks as u64));
    if queue_segs > 0 {
        set("disk: queue segments spilled", Metric::Count(queue_segs));
    }
    if archive_segs > 0 {
        set("disk: archive segments spilled", Metric::Count(archive_segs));
    }
}

/// The disk tier of the fingerprint set after a search: its runs,
/// rotations (and their time `t`), merges and lookups that read a page.
pub fn fpset_disk_done(d: crate::fpset::DiskStats, t: Duration) {
    if !on() {
        return;
    }
    add_count("fpset rotations to disk", d.rotations);
    add_secs("fpset rotating to disk", t);
    add_count("fpset run merges", d.merges);
    set("disk: fpset runs (at the end)", Metric::Count(d.runs));
    set("disk: fpset fingerprints on disk (at the end)", Metric::Count(d.on_disk));
    add_count("fpset disk lookups (pages read)", d.reads);
    add_count("fpset disk lookups found", d.hits);
    let key = format!("{MEMORY}fingerprint set Bloom filters and indexes");
    with_phase(&key, |m| match m {
        Some(Metric::Bytes(x)) if *x >= d.index_bytes => None,
        _ => Some(Metric::Bytes(d.index_bytes)),
    });
}

/// The memory budget (`-maxmem`): the other memory metrics are shown with
/// their share of it.
const BUDGET: &str = "memory: budget (-maxmem)";

static SECTIONS: Mutex<Vec<(String, String)>> = Mutex::new(Vec::new());

/// Set report section `title` to `text` (lines ending in newlines; if
/// on). Sections are printed at the end of the report, in order of first
/// setting.
pub fn set_section(title: &str, text: String) {
    if !on() {
        return;
    }
    let mut s = SECTIONS.lock().unwrap_or_else(|e| e.into_inner());
    match s.iter_mut().find(|(t, _)| t == title) {
        Some((_, x)) => *x = text,
        None => s.push((title.to_string(), text)),
    }
}

#[derive(Clone)]
enum JsonField {
    Frozen(String),
    Live(Arc<dyn Fn() -> String + Send + Sync>),
}

impl JsonField {
    fn render(&self) -> String {
        match self {
            Self::Frozen(raw) => raw.clone(),
            Self::Live(source) => source(),
        }
    }
}

static JSON: Mutex<Vec<(String, JsonField)>> = Mutex::new(Vec::new());

fn json_field(key: &str, value: JsonField) {
    if !on() {
        return;
    }
    let mut j = JSON.lock().unwrap_or_else(|e| e.into_inner());
    match j.iter_mut().find(|(k, _)| k == key) {
        Some((_, x)) => *x = value,
        None => j.push((key.to_string(), value)),
    }
}

/// Set field `key` of the JSON report to `raw` (JSON text; if on).
pub fn set_json(key: &str, raw: String) {
    json_field(key, JsonField::Frozen(raw));
}

/// Register an owned, thread-safe source once, outside measured evaluation.
/// Sources run only for JSON reporting or retirement, outside registry locks.
/// They must not recurse into the report; capture counters, not a model owner.
pub fn set_json_source(key: &str, source: Arc<dyn Fn() -> String + Send + Sync>) {
    json_field(key, JsonField::Live(source));
}

/// Preserve a retiring source's final observation and release its live counters.
pub fn freeze_json(key: &str) {
    if !on() {
        return;
    }
    let source = {
        let j = JSON.lock().unwrap_or_else(|e| e.into_inner());
        match j.iter().find(|(k, _)| k == key) {
            Some((_, JsonField::Live(source))) => source.clone(),
            _ => return,
        }
    };
    let raw = source();
    let mut j = JSON.lock().unwrap_or_else(|e| e.into_inner());
    if let Some((_, value)) = j.iter_mut().find(|(k, _)| k == key) {
        if matches!(value, JsonField::Live(current) if Arc::ptr_eq(current, &source)) {
            *value = JsonField::Frozen(raw);
        }
    }
}

/// The fields registered, in order of first setting. Callbacks run without
/// holding registry locks, so a slow report cannot stall counter publication.
pub(crate) fn json_fields() -> Vec<(String, String)> {
    let fields = JSON.lock().unwrap_or_else(|e| e.into_inner()).clone();
    fields.into_iter().map(|(key, value)| (key, value.render())).collect()
}

/// The text of report section `title`, if set.
pub fn section(title: &str) -> Option<String> {
    SECTIONS.lock().unwrap_or_else(|e| e.into_inner()).iter().find(|(t, _)| t == title).map(|(_, x)| x.clone())
}

fn sections() -> Vec<(String, String)> {
    SECTIONS.lock().unwrap_or_else(|e| e.into_inner()).clone()
}

/// The value of metric `key`, if recorded.
pub fn metric(key: &str) -> Option<Metric> {
    phase(key)
}

/// Encode diagnostic text as a JSON string literal.
pub fn json_string(s: &str) -> String {
    report::js(s)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn json_sources_are_lazy_and_freeze_at_retirement() {
        use std::sync::atomic::AtomicUsize;
        enable(1);
        let owner = std::thread::current().id();
        let reads = Arc::new(AtomicUsize::new(0));
        let value = Arc::new(AtomicUsize::new(17));
        let (source_reads, source_value) = (reads.clone(), value.clone());
        set_json_source(
            "test live source",
            Arc::new(move || {
                if std::thread::current().id() == owner {
                    source_reads.fetch_add(1, Ordering::Relaxed);
                }
                source_value.load(Ordering::Relaxed).to_string()
            }),
        );
        text();
        assert_eq!(reads.load(Ordering::Relaxed), 0, "text must not render JSON sources");
        assert!(json().contains("\"test live source\":17"));
        assert_eq!(reads.load(Ordering::Relaxed), 1);
        value.store(23, Ordering::Relaxed);
        assert!(json().contains("\"test live source\":23"));
        freeze_json("test live source");
        let frozen_reads = reads.load(Ordering::Relaxed);
        value.store(99, Ordering::Relaxed);
        assert!(json().contains("\"test live source\":23"));
        assert_eq!(reads.load(Ordering::Relaxed), frozen_reads);
    }

    #[test]
    fn live_snapshot_is_replaced_by_final_worker_totals() {
        enable(1);
        std::thread::spawn(|| {
            let unit = begin_unit(1);
            successor(0);
            end_unit(unit);
            let id = std::thread::current().id();
            {
                let g = global();
                let (_, live) = g.live.iter().find(|(thread, _)| *thread == id).expect("published worker");
                assert_eq!(live.c[C::Units as usize], 1);
                assert_eq!(live.c[C::Generated as usize], 1);
            }
            worker_done(Duration::from_millis(1));
            assert!(!global().live.iter().any(|(thread, _)| *thread == id));
        })
        .join()
        .unwrap();
    }

    #[test]
    fn spans_are_exclusive() {
        enable(1);
        let u = begin_unit(1);
        // Measure the outer span ourselves: this is the wall time the
        // outer exclusive time plus the inner time must account for.
        let t0 = Instant::now();
        let outer = span();
        let inner = span();
        std::thread::sleep(Duration::from_millis(2));
        inner.action(0, Path::Native);
        std::thread::sleep(Duration::from_millis(1));
        outer.end(T::Successor);
        let total_ns = t0.elapsed().as_nanos() as u64;
        end_unit(u);
        let l = local(|l| l.clone());
        let inner_ns = l.actions[0].ns[Path::Native as usize];
        let outer_ns = l.t[T::Successor as usize];
        // Slack for scheduling noise on a loaded machine; it does not
        // assume any ordering between the two sleeps.
        let slack_ns = 500_000;
        // The inner span covers at least its own sleep.
        assert!(inner_ns >= 2_000_000);
        // The outer exclusive time covers at least the outer-only sleep.
        assert!(outer_ns >= 1_000_000);
        // The two spans together cannot exceed the measured wall time.
        assert!(outer_ns + inner_ns <= total_ns + slack_ns);
        // And the outer exclusive time leaves room for the whole inner span.
        assert!(outer_ns <= total_ns.saturating_sub(inner_ns) + slack_ns);
        assert_eq!(l.actions[0].calls[Path::Native as usize], 1);
        // A statically mixed function can short-circuit before its host site.
        let u = begin_unit(1);
        span().action(1, Path::Mixed);
        let host = span();
        regions(0, 1, 3, 0);
        host.action(1, Path::Mixed);
        // A failed native attempt followed by IR is not fully native.
        span().action(1, Path::Fallback);
        end_unit(u);
        let l = local(|l| l.clone());
        assert_eq!(l.actions[0].fully_native, 1);
        assert_eq!(l.actions[1].fully_native, 1);
        assert_eq!(l.actions[1].calls.iter().sum::<u64>(), 3);
        let u = begin_unit(1);
        let action = span();
        let invariant = span();
        regions(1, 2, 1, 0);
        invariant.invariant(2, Path::Mixed);
        action.action(2, Path::Native);
        end_unit(u);
        let l = local(|l| l.clone());
        assert_eq!(l.actions[2].fully_native, 1, "nested invariant host work is not action host work");
        assert_eq!(l.invariants[2].fully_native, 0);
        let j = json();
        assert!(j.contains("\"fully_native\":1"));
        assert!(j.starts_with('{') && j.ends_with('}'));
        assert!(text().contains("actions"));
    }
}
