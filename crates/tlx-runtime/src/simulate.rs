//! Random simulation (TLC's `-simulate`): random behaviors from random
//! initial states, up to a depth, checking invariants and action
//! properties on every generated state and step.
//!
//! This follows TLC's `Simulator` and `SimulationWorker`:
//! - All initial states (with duplicates) are checked against the
//!   invariants, each followed by the CONSTRAINT; behaviors start from a
//!   random one of those satisfying the CONSTRAINT.
//! - In each step a random action is tried first, then the others (in a
//!   random order of stride `p`), until one has a successor that satisfies
//!   the CONSTRAINT and the ACTION_CONSTRAINT. Every successor of a tried
//!   action is counted as generated and checked against the invariants and
//!   action properties (in generation order), then against the CONSTRAINT
//!   and, if that holds, the ACTION_CONSTRAINT. The next state is a random
//!   one of the successors that passed both.
//! - A state without such a successor ends the behavior, or is a deadlock
//!   when deadlocks are checked (even if it has successors outside the
//!   constraints).
//! - Each worker generates `traces` behaviors.
//! - Generation (TLC's `-generate`, `Tool.probabilistic`) is the same,
//!   except that the successors of a tried action are computed with random
//!   choices that stop at the first successor satisfying the constraints
//!   (`live::generating`), so an action mostly generates one state.
//! - Finite stuttering steps are not shown in error traces.

use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;
use std::time::{Duration, Instant};

use parking_lot::Mutex;

use crate::explore::{Outcome, Report, Stats, TraceStep};
use crate::live::{set_current_action, set_generating, set_has_states, CurrentAction};
use crate::model::Model;
use crate::stats::T;

#[derive(Clone, Debug)]
pub struct SimOptions {
    pub workers: usize,
    pub check_deadlock: bool,
    /// Number of behaviors to generate by each worker (as TLC's `num`).
    pub traces: u64,
    /// Maximum length of a behavior in steps (TLC's `-depth`).
    pub depth: u32,
    pub seed: u64,
    /// Generation mode (TLC's `-generate`): the successors of an action are
    /// computed with random choices (see `live::generating`).
    pub generate: bool,
}

/// The phase of a simulation a progress report is about.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum SimPhase {
    /// The initial states are computed (not yet checked).
    InitComputed,
    /// The initial states are checked; behaviors start.
    InitDone,
    /// A behavior was generated (or the simulation ended).
    #[default]
    Running,
}

/// Progress of a simulation, reported after every behavior.
#[derive(Clone, Copy, Debug, Default)]
pub struct SimProgress {
    pub phase: SimPhase,
    /// States generated so far (TLC's "states checked"): the initial states
    /// and every successor of the actions tried.
    pub generated: u64,
    /// Behaviors started (TLC counts a behavior when it starts).
    pub traces: u64,
    /// Length of the longest behavior so far (in states).
    pub diameter: u32,
    /// TLC's running mean and M2 of the behavior lengths (Welford's
    /// algorithm in integer arithmetic, packed as `m2 << 32 | mean`).
    pub welford: u64,
    pub elapsed: Duration,
    /// Initial states generated, and those satisfying the CONSTRAINT.
    pub init_generated: u64,
    pub init_distinct: u64,
}

impl SimProgress {
    /// Mean, variance and standard deviation of the lengths of the
    /// behaviors, as TLC reports them.
    pub fn length_stats(&self) -> (u64, i64, i64) {
        let mean = self.welford & 0xFFFF_FFFF;
        let m2 = (self.welford >> 32) as f64;
        let var = m2 / (self.traces as f64 + 1.0);
        (mean, java_round(var), java_round(var.sqrt()))
    }
}

/// Java's `Math.round`.
fn java_round(x: f64) -> i64 {
    (x + 0.5).floor() as i64
}

/// TLC's `SimulationWorkerStatistics.collectPostTrace`: one step of
/// Welford's algorithm, with the mean and M2 in integers.
fn welford_step(acc: u64, len: i64, n: u64) -> u64 {
    let mut mean = (acc & 0xFFFF_FFFF) as u32 as i32;
    let mut m2 = (acc >> 32) as i64;
    let delta = len - mean as i64;
    mean = mean.wrapping_add((delta / n.max(1) as i64) as i32);
    m2 = m2.wrapping_add(delta.wrapping_mul(len - mean as i64));
    ((m2 as u64) << 32) | (mean as u32 as u64)
}

/// Checks one simulated behavior (its states, each with the action that
/// produced it) against the temporal properties; `succs[i]` are all the
/// successors of state `i` (for ENABLED). A violation is returned as the
/// outcome of the simulation.
pub type TraceCheck<'a, S> = dyn Fn(&[TraceStep<S>], &[Vec<(S, u32)>]) -> Option<Outcome> + Sync + 'a;

pub(crate) use tlx_base::rng::SplitMix64 as Rng;

/// Some of TLC's primes (`RandomGenerator.primes`): the stride between the
/// actions tried in a step (larger than any number of actions, so all are
/// tried).
pub(crate) const PRIMES: [usize; 8] = [1277011, 1277021, 1277039, 1277041, 1277063, 1277069, 1277071, 1277083];

struct Shared<'a, M: Model> {
    model: &'a M,
    opts: &'a SimOptions,
    init: Vec<M::State>,
    stop: AtomicBool,
    generated: AtomicU64,
    traces: AtomicU64,
    diameter: AtomicU64,
    welford: AtomicU64,
    failure: Mutex<Option<(Outcome, Vec<TraceStep<M::State>>)>>,
    on_progress: &'a (dyn Fn(SimProgress) + Sync),
    check_trace: Option<&'a TraceCheck<'a, M::State>>,
    start: Instant,
    init_stats: (u64, u64),
}

impl<M: Model> Shared<'_, M> {
    /// Record the first failure and stop all workers.
    fn fail(&self, outcome: Outcome, trace: Vec<TraceStep<M::State>>) {
        let trace = without_stuttering(self.model, trace);
        let mut f = self.failure.lock();
        if f.is_none() {
            *f = Some((outcome, trace));
        }
        self.stop.store(true, Ordering::SeqCst);
    }

    fn stopped(&self) -> bool {
        self.stop.load(Ordering::Relaxed) || self.model.stop_requested()
    }

    fn progress(&self) -> SimProgress {
        SimProgress {
            phase: SimPhase::Running,
            generated: self.generated.load(Ordering::Relaxed),
            traces: self.traces.load(Ordering::Relaxed),
            diameter: self.diameter.load(Ordering::Relaxed) as u32,
            welford: self.welford.load(Ordering::Relaxed),
            elapsed: self.start.elapsed(),
            init_generated: self.init_stats.0,
            init_distinct: self.init_stats.1,
        }
    }
}

/// A trace without its finite stuttering steps (TLC's
/// `SimulationWorker.getTrace`).
fn without_stuttering<M: Model>(m: &M, trace: Vec<TraceStep<M::State>>) -> Vec<TraceStep<M::State>> {
    let mut out: Vec<TraceStep<M::State>> = Vec::with_capacity(trace.len());
    let mut last = String::new();
    for step in trace {
        let shown = m.render(&step.state);
        if !out.is_empty() && shown == last {
            continue;
        }
        last = shown;
        out.push(step);
    }
    out
}

pub fn simulate<'a, M: Model>(
    model: &'a M,
    opts: &'a SimOptions,
    on_progress: &'a (dyn Fn(SimProgress) + Sync),
    check_trace: Option<&'a TraceCheck<'a, M::State>>,
) -> Report<M::State> {
    let start = Instant::now();
    crate::stats::set_names(model.action_names(), model.invariant_names(), model.action_property_names());
    // (No memory budget: the workers share the evaluation caches' own.)
    crate::cache_mem::set_allowance(usize::MAX, opts.workers);
    let mut stats = Stats::default();
    let fail_init = |stats: Stats, outcome: Outcome, trace: Vec<TraceStep<M::State>>| Report {
        stats,
        outcome,
        trace,
        trace_note: None,
        trace_store_full: false,
        elapsed: start.elapsed(),
        in_init: true,
        live_graph: None,
        live_witness: None,
        live_error: None,
        live_atoms_ok: false,
        coverage: None,
        frontier_peak: 0,
    };
    // All initial states (TLC does not drop duplicates here).
    let mut all = Vec::new();
    set_current_action(Some(CurrentAction::Init));
    let extra_at_start = model.extra_generated();
    if let Err(e) = model.init_states(&mut |s| all.push(s)) {
        set_current_action(None);
        if let crate::model::ErrorContext::IncompleteState { .. } = e.context {
            // TLC checks the initial states once they are all computed
            // (the model counts those it did not produce as extra).
            let init_generated = all.len() as u64 + (model.extra_generated() - extra_at_start);
            on_progress(SimProgress { phase: SimPhase::InitComputed, init_generated, elapsed: start.elapsed(), ..Default::default() });
        }
        return fail_init(stats, Outcome::Error(e), Vec::new());
    }
    stats.init_generated = all.len() as u64;
    stats.generated = all.len() as u64;
    on_progress(SimProgress {
        phase: SimPhase::InitComputed,
        init_generated: stats.init_generated,
        elapsed: start.elapsed(),
        ..Default::default()
    });
    // Each is checked against the invariants (TLC does not check the
    // state-predicate parts of properties in simulation), then the
    // CONSTRAINT selects the ones behaviors start from.
    let mut init = Vec::new();
    for s in all {
        match model.check_invariants(&s) {
            Ok(Some(i)) => {
                set_current_action(None);
                let outcome = Outcome::InvariantViolated(model.invariant_names()[i].clone());
                return fail_init(stats, outcome, vec![TraceStep { state: s, action: None }]);
            }
            Ok(None) => {}
            Err(e) => {
                set_current_action(None);
                return fail_init(stats, Outcome::Error(e.on_initial_state(model, &s)), Vec::new());
            }
        }
        match model.constraint(&s) {
            Ok(true) => init.push(s),
            Ok(false) => {}
            Err(e) => {
                set_current_action(None);
                return fail_init(stats, Outcome::Error(e.on_initial_state(model, &s)), Vec::new());
            }
        }
    }
    stats.init_distinct = init.len() as u64;
    if init.is_empty() {
        set_current_action(None);
        return fail_init(stats, Outcome::NoInitInConstraint, Vec::new());
    }
    let sh = Shared {
        model,
        opts,
        init,
        stop: AtomicBool::new(false),
        generated: AtomicU64::new(stats.generated),
        traces: AtomicU64::new(0),
        diameter: AtomicU64::new(0),
        welford: AtomicU64::new(0),
        failure: Mutex::new(None),
        on_progress,
        check_trace,
        start,
        init_stats: (stats.init_generated, stats.init_distinct),
    };
    crate::stats::add_secs("initial states", start.elapsed());
    on_progress(SimProgress { phase: SimPhase::InitDone, ..sh.progress() });
    std::thread::scope(|sc| {
        let handles: Vec<_> = (0..opts.workers.max(1))
            .map(|w| {
                let sh = &sh;
                let rng = Rng(opts.seed ^ (w as u64).wrapping_mul(0xa24baed4963ee407));
                // A panicking worker (e.g. a TLX_PARANOID mismatch) stops the
                // others.
                tlx_base::stack::spawn_eval(sc, move || {
                    crate::explore::abort_on_panic(
                        || sh.stop.store(true, Ordering::SeqCst),
                        || {
                            crate::live::set_current_worker(Some(w));
                            let born = Instant::now();
                            worker(sh, rng);
                            crate::stats::worker_done(born.elapsed());
                        },
                    )
                })
            })
            .collect();
        crate::explore::join_all(handles, || {});
    });
    crate::stats::add_secs("simulation", start.elapsed());
    // The final statistics.
    on_progress(sh.progress());
    stats.generated = sh.generated.load(Ordering::Relaxed);
    stats.depth = sh.diameter.load(Ordering::Relaxed) as u32;
    let (outcome, trace) = sh.failure.into_inner().unwrap_or((Outcome::Ok, Vec::new()));
    set_current_action(None);
    Report {
        stats,
        outcome,
        trace,
        trace_note: None,
        trace_store_full: false,
        elapsed: start.elapsed(),
        in_init: false,
        live_graph: None,
        live_witness: None,
        live_error: None,
        live_atoms_ok: false,
        coverage: None,
        frontier_peak: 0,
    }
}

/// What processing the successors of an action found.
enum Found<S> {
    /// The successors satisfying the constraints.
    Next(Vec<(S, u32)>),
    /// A violation or an evaluation error, and the state it is about (if not
    /// the current one).
    Failure(Outcome, Option<(S, u32)>),
}

/// Generate the successors of `s` under action `a`, counting and checking
/// each as TLC's `SimulationWorker.addElement` does. In generation mode,
/// `gen` is the state of the generator of the random choices.
fn try_action<M: Model>(sh: &Shared<M>, s: &M::State, s_action: CurrentAction, a: u32, gen: &mut u64) -> Found<M::State> {
    let m = sh.model;
    let mut next = Vec::new();
    let mut failure = None;
    let mut generated = 0;
    set_current_action(Some(s_action));
    if sh.opts.generate {
        set_generating(Some(*gen));
    }
    let r = m.action_successors(s, a, &mut |t, a| {
        generated += 1;
        crate::stats::successor(a);
        let span = crate::stats::span();
        set_current_action(Some(CurrentAction::Action(a)));
        let checked = (|| -> Result<Option<Outcome>, crate::model::ModelError> {
            let span = crate::stats::span();
            let inv = m.check_invariants(&t);
            span.end(T::Invariants);
            if let Some(i) = inv? {
                return Ok(Some(Outcome::InvariantViolated(m.invariant_names()[i].clone())));
            }
            let span = crate::stats::span();
            let tr = m.check_transition(s, &t);
            span.end(T::Transition);
            if let Some(i) = tr? {
                return Ok(Some(Outcome::ActionPropertyViolated(m.action_property_names()[i].clone())));
            }
            Ok(None)
        })();
        span.end(T::Successor);
        match checked {
            Ok(None) => {}
            Ok(Some(outcome)) => {
                failure = Some((outcome, Some((t, a))));
                return false;
            }
            Err(e) => {
                failure = Some((Outcome::Error(e), Some((t, a))));
                return false;
            }
        }
        // (The ACTION_CONSTRAINT only if the CONSTRAINT holds.)
        let span = crate::stats::span();
        let in_model = crate::model::admits(m, s, &t);
        span.end(T::Constraint);
        set_current_action(Some(s_action));
        match in_model {
            Ok(true) => {
                next.push((t, a));
                set_has_states(true);
            }
            Ok(false) => {}
            Err(e) => {
                failure = Some((Outcome::Error(e), None));
                return false;
            }
        }
        true
    });
    if sh.opts.generate {
        *gen = set_generating(None).unwrap_or(*gen);
    }
    sh.generated.fetch_add(generated, Ordering::Relaxed);
    if let Some((outcome, t)) = failure {
        return Found::Failure(outcome, t);
    }
    if let Err(e) = r {
        return Found::Failure(Outcome::Error(e.in_next_state()), None);
    }
    Found::Next(next)
}

/// Ends a statistics unit when dropped (the step may end by an early return).
struct UnitEnd(Option<crate::stats::Span>);

impl Drop for UnitEnd {
    fn drop(&mut self) {
        if let Some(u) = self.0.take() {
            crate::stats::end_unit(u);
        }
    }
}

fn worker<M: Model>(sh: &Shared<M>, mut rng: Rng) {
    let m = sh.model;
    let nactions = m.action_names().len();
    // The generator of the random choices within actions (generation mode).
    let mut gen = rng.next_u64();
    for _ in 0..sh.opts.traces {
        if sh.stopped() {
            return;
        }
        let n = sh.traces.fetch_add(1, Ordering::Relaxed) + 1;
        crate::stats::count(crate::stats::C::Traces, 1);
        // (`TLCGet("stats").traces` counts the behavior from its start.)
        (sh.on_progress)(sh.progress());
        let s0 = sh.init[rng.below(sh.init.len())].clone();
        // `TLCExt!Trace`: the behavior so far.
        let node = |s: &M::State, action: Option<u32>, parent: Option<Arc<crate::live::PathNode>>| {
            let values = m.state_values(s).expect("a model that uses TLCExt!Trace has state values");
            Arc::new(crate::live::PathNode { values, action, parent })
        };
        let mut path = m.uses_trace().then(|| node(&s0, None, None));
        let mut trace = vec![TraceStep { state: s0, action: None }];
        // All successors of each state, kept for liveness checking.
        let mut succs: Vec<Vec<(M::State, u32)>> = Vec::new();
        for _ in 0..sh.opts.depth {
            if sh.stopped() {
                return;
            }
            if let Some(p) = &path {
                crate::live::set_path(Some(crate::live::CurrentPath::Known(p.clone())));
            }
            let last = trace.last().unwrap();
            let s = &last.state;
            // `TLCGet("action")`: the action that produced the current
            // state (for a step, its first state).
            let s_action = last.action.map_or(CurrentAction::Init, CurrentAction::Action);
            let mut next = Vec::new();
            let unit = crate::stats::begin_unit(trace.len() as u32);
            let unit_ends = UnitEnd(Some(unit));
            if nactions > 0 {
                // A random action first, then the others.
                let mut index = rng.below(nactions);
                let p = PRIMES[rng.below(PRIMES.len())];
                for _ in 0..nactions {
                    match try_action(sh, s, s_action, index as u32, &mut gen) {
                        Found::Next(v) => next = v,
                        Found::Failure(outcome, t) => {
                            if let Some((t, a)) = t {
                                trace.push(TraceStep { state: t, action: Some(a) });
                            }
                            return sh.fail(outcome, trace);
                        }
                    }
                    if !next.is_empty() {
                        break;
                    }
                    index = (index + p) % nactions;
                }
            }
            if sh.check_trace.is_some() {
                // All successors (not only those of the actions tried), for
                // ENABLED.
                set_current_action(Some(s_action));
                let mut all = Vec::new();
                if let Err(e) = m.successors(s, &mut |t, a| {
                    all.push((t, a));
                    true
                }) {
                    return sh.fail(Outcome::Error(e.in_next_state()), trace);
                }
                succs.push(all);
            }
            drop(unit_ends);
            if next.is_empty() {
                if sh.opts.check_deadlock {
                    return sh.fail(Outcome::Deadlock, trace);
                }
                break;
            }
            let (t, a) = next.swap_remove(rng.below(next.len()));
            path = path.take().map(|p| node(&t, Some(a), Some(p)));
            trace.push(TraceStep { state: t, action: Some(a) });
        }
        if let Some(check) = sh.check_trace {
            if sh.stopped() {
                return;
            }
            if succs.len() < trace.len() {
                // The last state (the behavior was cut at the depth).
                let mut succ = Vec::new();
                if let Err(e) = m.successors(&trace.last().unwrap().state, &mut |t, a| {
                    succ.push((t, a));
                    true
                }) {
                    return sh.fail(Outcome::Error(e.in_next_state()), trace);
                }
                succs.push(succ);
            }
            if let Some(outcome) = check(&trace, &succs) {
                // (The counterexample of a violation is rendered already;
                // after an error, TLC shows the behavior.)
                let trace = if matches!(outcome, Outcome::Error(_)) { trace } else { Vec::new() };
                return sh.fail(outcome, trace);
            }
        }
        let len = trace.len() as u64;
        sh.diameter.fetch_max(len, Ordering::Relaxed);
        let tl = len.min(sh.opts.depth as u64) as i64;
        // A compare_exchange loop rather than `fetch_update`: the latter is
        // deprecated by newer rustc releases, and the result here is unused:
        // the accumulator is updated on every path.
        let mut welford = sh.welford.load(Ordering::Relaxed);
        loop {
            let next = welford_step(welford, tl, n);
            match sh.welford.compare_exchange_weak(welford, next, Ordering::Relaxed, Ordering::Relaxed) {
                Ok(_) => break,
                Err(actual) => welford = actual,
            }
        }
        (sh.on_progress)(sh.progress());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn welford_as_tlc() {
        // Lengths 2, 1, 1 (TLC: mean=2, var(x)=1, sd=1 after 3 traces).
        let mut acc = 0;
        for (i, l) in [2, 1, 1].into_iter().enumerate() {
            acc = welford_step(acc, l, i as u64 + 1);
        }
        let p = SimProgress { welford: acc, traces: 3, ..Default::default() };
        assert_eq!(p.length_stats(), (2, 1, 1));
    }
}
