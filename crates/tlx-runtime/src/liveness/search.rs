//! A second search evaluating the liveness predicates where TLC evaluates
//! them during its search, to find where TLC reports their errors (and the
//! violations it detects during its search).

use std::any::Any;
use std::sync::Mutex;

use tlx_base::hash::IdMap;

use super::concrete::{at_point, violation, Concrete, GcHook, NO_STATE};
use super::expand::{concrete_bits, ConcreteSuccessors};
use super::{LiveInput, LiveResult};
use crate::live::LiveStats;
use crate::{AtomBits, ErrorContext, ExpandedBatch, Model, ModelError, Options, Outcome, Report, SearchObserver};

/// The liveness predicates of a spec evaluated on the states of a search as
/// TLC evaluates them during its search (Worker.doNextCheckLiveness,
/// `LiveCheck.addInitState` / `addNextState`). Their errors are reported in
/// context `ErrorContext::Liveness` (`find_error` sets it).
pub trait SearchAtoms<S>: Sync {
    /// On a new initial state in the model: the tableau's state atoms.
    fn init(&self, s: &S) -> Result<(), ModelError>;
    /// After the search expanded `s`, with its successors in the model
    /// `succ`: the action atoms on the stuttering step and the steps to
    /// `succ`, every state atom (`ENABLED` of fairness directly) on `s`,
    /// the tableau's state atoms on `succ`.
    fn expanded(&self, s: &S, succ: &[S]) -> Result<(), ModelError>;
}

/// An observer of a search of `m` (`crate::SearchObserver`) that evaluates
/// the liveness predicates as TLC does during its search (`atoms`): on each
/// new initial state the tableau predicates; after expanding a state (also
/// when its successors failed to compute), the steps to its successors in
/// the model and the stuttering step, every state predicate on the state and
/// the tableau predicates on its successors. An error stops the search there
/// (context `Liveness`). Used to find where TLC reports an error of these
/// predicates: tlx evaluates them only after the search.
///
/// With `early`, TLC's products are also built during the search (in its
/// order: one worker), to find where TLC reports a violation it detects
/// during the search (`tlx_live::ConcreteChecker::fired`); that stops the
/// search too.
struct LiveErrors<'a, M: Model> {
    m: &'a M,
    atoms: &'a dyn SearchAtoms<M::State>,
    check_deadlock: bool,
    early: Option<Mutex<Early<'a, M>>>,
}

/// TLC's products during the search (see `LiveErrors`).
struct Early<'a, M: Model> {
    cx: Concrete<'a, M>,
    checker: tlx_live::ConcreteChecker<ModelError>,
    /// The state id of each state found and not yet expanded, by fingerprint.
    pending: IdMap<u32>,
    /// The products could not be built (an atom failed; the error is
    /// reported as TLC does, or not at all): nothing more is detected.
    off: bool,
    /// The violation found: the property and its counterexample.
    fired: Option<(usize, tlx_live::CLasso)>,
}

/// The message of the error that stops the search of `LiveErrors` at a
/// violation found during the search (not shown).
const FIRED: &str = "liveness: violation found during the search";

impl<M: Model> Early<'_, M> {
    /// A new initial state in the model, the `k`-th enumerated.
    fn init(&mut self, s: &M::State, k: u32) {
        if self.off {
            return;
        }
        let (m, bits) = (self.cx.m, self.cx.bits);
        let fp = m.fingerprint(s);
        self.cx.find(fp);
        let Ok(b) = bits.tableau_bits(s) else {
            self.off = true;
            return;
        };
        let conc = self.cx.state_id((NO_STATE, k));
        self.pending.insert(fp, conc);
        let node = self.cx.node(fp);
        self.checker.event(&tlx_live::Event::Init { node, conc, bits: tlx_live::Bits::from_words(&b) }, &mut self.cx);
    }

    /// GC-backed `init` routing retries and any on-demand expansion through `park`.
    fn init_gc(&mut self, s: &M::State, k: u32, park: &mut dyn FnMut(&[&M::State], bool) -> bool) {
        if self.off {
            return;
        }
        let (m, bits) = (self.cx.m, self.cx.bits);
        let fp = m.fingerprint(s);
        self.cx.find(fp);
        let mut hook = GcHook::Park(park);
        let Ok(b) = self.cx.retry_with(|| bits.tableau_bits(s), |hook, force_drop| self.cx.collect_with(hook, force_drop, &[s]), &mut hook)
        else {
            self.off = true;
            return;
        };
        let conc = self.cx.state_id((NO_STATE, k));
        self.pending.insert(fp, conc);
        let node = self.cx.node(fp);
        self.cx.init_event_with(&mut self.checker, node, conc, &b, &mut hook);
    }

    /// The search expanded `s` with the transitions already generated in `all`:
    /// whether that completes a violation.
    fn next_all(&mut self, s: &M::State, all: &[(M::State, u32)]) -> bool {
        if self.off {
            return false;
        }
        let (m, bits) = (self.cx.m, self.cx.bits);
        let Some(conc) = self.pending.remove(&m.fingerprint(s)) else {
            self.off = true;
            return false;
        };
        let mut out = Vec::with_capacity(all.len());
        for (t, a) in all {
            let Ok(ok) = crate::admits(m, s, t) else {
                self.off = true;
                return false;
            };
            out.push((t.clone(), *a, m.fingerprint(t), ok));
        }
        let Ok(e) = concrete_bits(m, bits, s, ConcreteSuccessors { all: out }) else {
            self.off = true;
            return false;
        };
        let pending = &mut self.pending;
        self.cx.next_event(&mut self.checker, conc, e, None, &mut |id, _, fp| {
            pending.insert(fp, id);
        });
        self.fired = self.checker.fired();
        self.fired.is_some()
    }

    /// GC-backed `next` reusing the worker's filtered successor batch `batch`
    /// and routing atom retries and on-demand expansion through `park`.
    fn next_batch(&mut self, s: &M::State, batch: &ExpandedBatch<'_, M::State>, park: &mut dyn FnMut(&[&M::State], bool) -> bool) -> bool {
        if self.off {
            return false;
        }
        let m = self.cx.m;
        let Some(conc) = self.pending.remove(&m.fingerprint(s)) else {
            self.off = true;
            return false;
        };
        let mut hook = GcHook::Park(park);
        let Ok(e) = self.cx.concrete_bits_with(s, batch.admitted.to_vec(), batch.rejected_staged, Vec::new(), &[], &mut hook) else {
            self.off = true;
            return false;
        };
        let pending = &mut self.pending;
        self.cx.next_event_with(&mut self.checker, conc, e, None, &mut hook, &mut |id, _, fp| {
            pending.insert(fp, id);
        });
        self.fired = self.checker.fired();
        self.fired.is_some()
    }
}

impl<M: Model> LiveErrors<'_, M> {
    /// The products of `early` after the search expanded `s`: the error
    /// stopping the search if that completes a violation.
    fn check_early(&self, s: &M::State, all: &[(M::State, u32)]) -> Result<(), ModelError> {
        match &self.early {
            Some(e) if e.lock().unwrap().next_all(s, all) => Err(ModelError::new(FIRED).within(ErrorContext::Liveness)),
            _ => Ok(()),
        }
    }

    fn check_early_gc(
        &self,
        s: &M::State,
        batch: &ExpandedBatch<'_, M::State>,
        park: &mut dyn FnMut(&[&M::State], bool) -> bool,
    ) -> Result<(), ModelError> {
        match &self.early {
            Some(e) if e.lock().unwrap().next_batch(s, batch, park) => Err(ModelError::new(FIRED).within(ErrorContext::Liveness)),
            _ => Ok(()),
        }
    }
}

impl<M: Model> SearchObserver<M::State> for LiveErrors<'_, M> {
    // No behavior graph is recorded: it would be a second one and, with
    // several workers, drop the BFS-order representative choice (`explore`).
    fn records_live_graph(&self) -> bool {
        false
    }

    // The successors are processed after the check, so that other workers
    // do not expand them before the search stops at an error (TLC: one
    // worker).
    fn buffers(&self) -> bool {
        true
    }

    fn filters_rejected(&self) -> bool {
        true
    }

    fn wants_rejected_staged(&self) -> bool {
        self.early.as_ref().is_some_and(|e| e.lock().unwrap().cx.bits.has_action_atoms())
    }

    fn stage_rejected(&self, t: &M::State) -> Option<Box<dyn Any + Send + Sync>> {
        self.early.as_ref().and_then(|e| e.lock().unwrap().cx.bits.stage_state(t))
    }

    // TLC checks a new initial state before its invariants.
    fn on_init(&self, s: &M::State, k: u64) -> Result<(), ModelError> {
        self.atoms.init(s).map_err(|e| e.within(ErrorContext::Liveness))?;
        if let Some(e) = &self.early {
            e.lock().unwrap().init(s, k as u32);
        }
        Ok(())
    }

    fn on_init_gc(&self, s: &M::State, k: u64, park: &mut dyn FnMut(&[&M::State], bool) -> bool) -> Result<(), ModelError> {
        self.atoms.init(s).map_err(|e| e.within(ErrorContext::Liveness))?;
        if let Some(e) = &self.early {
            e.lock().unwrap().init_gc(s, k as u32, park);
        }
        Ok(())
    }

    fn on_expanded(&self, s: &M::State, all: &[(M::State, u32)], complete: bool) -> Result<(), ModelError> {
        // (An error counts as a step out of the model: the search reports
        // an error of the constraints itself, processing the successors.)
        let in_model = |t: &M::State| crate::admits(self.m, s, t).unwrap_or(false);
        let succ: Vec<M::State> = all.iter().filter(|(t, _)| in_model(t)).map(|(t, _)| t.clone()).collect();
        let deadlock = complete && all.is_empty() && self.check_deadlock;
        let check = || {
            let live = if deadlock { Ok(()) } else { self.atoms.expanded(s, &succ).map_err(|e| e.within(ErrorContext::Liveness)) };
            if live.is_ok() && complete && !deadlock {
                self.check_early(s, all)
            } else {
                live
            }
        };
        // TLC evaluates these predicates once the successors are queued; the
        // search queues them after this check (`buffers`): its statistics
        // with the successors (one worker, products in TLC's order).
        match self.early.as_ref().and_then(|e| crate::live::current().map(|p| (e, p))) {
            Some((e, p)) => {
                let new = e.lock().unwrap().cx.count_new(succ.iter().map(|t| self.m.fingerprint(t)));
                let p = LiveStats { generated: p.generated + all.len() as u64, distinct: p.distinct + new, queue: p.queue + new, ..p };
                at_point(p, check)
            }
            None => check(),
        }
    }

    fn on_expanded_gc(
        &self,
        s: &M::State,
        batch: &ExpandedBatch<'_, M::State>,
        park: &mut dyn FnMut(&[&M::State], bool) -> bool,
    ) -> Result<(), ModelError> {
        let succ: Vec<M::State> = batch.admitted.iter().map(|(t, ..)| t.clone()).collect();
        let deadlock = batch.complete && batch.total_generated == 0 && self.check_deadlock;
        let mut check = || {
            let live = if deadlock { Ok(()) } else { self.atoms.expanded(s, &succ).map_err(|e| e.within(ErrorContext::Liveness)) };
            if live.is_ok() && batch.complete && !deadlock {
                self.check_early_gc(s, batch, park)
            } else {
                live
            }
        };
        match self.early.as_ref().and_then(|e| crate::live::current().map(|p| (e, p))) {
            Some((_, p)) => {
                // `generated`, `distinct`, and `diameter` are already published
                // as each successor is checked in generation order; add any
                // multi-worker deferred queue pushes to `queue`.
                let p = LiveStats { queue: p.queue + batch.deferred_queued, ..p };
                at_point(p, check)
            }
            None => check(),
        }
    }
}

/// The result of `find_error`: the report of the search stopped by an error
/// of a liveness predicate, or by a violation TLC finds during its search
/// (`fired`).
pub struct Found<'a, M: Model> {
    pub report: Report<M::State>,
    pub fired: Option<Fired<'a, M>>,
}

/// A violation TLC finds during its search (see `find_error`).
pub struct Fired<'a, M: Model> {
    cx: Concrete<'a, M>,
    prop: usize,
    lasso: tlx_live::CLasso,
}

impl<M: Model> Fired<'_, M> {
    /// The violation, its counterexample's states rebuilt by re-executing
    /// the model.
    pub fn result(&self, input: &LiveInput) -> LiveResult<M::State> {
        let _gc_guard = self.cx.m.caps().gc.map(|gc| gc.enter_scope());
        if let Some(gc) = self.cx.m.caps().gc {
            let _ = gc.collect(&mut |_| Ok(()));
        }
        violation(input, self.prop, &self.lasso, &self.cx)
    }
}

/// Search `m` again (with `opts`) evaluating the liveness predicates as
/// TLC does during its search (`atoms`): the report of the first error of
/// one of them, if any (TLC stops there; see `LiveErrors`). With `early`
/// (see `LiveInput::reports_early`), also a violation TLC finds during its
/// search, if it stops there (`Found::fired`). `before_search` runs before
/// each search (a second one, with one worker, finds TLC's counts when
/// several workers stopped at an error).
pub fn find_error<'a, M: Model>(
    m: &'a M,
    input: &LiveInput,
    bits: &'a (dyn AtomBits<M::State> + Sync),
    atoms: &'a dyn SearchAtoms<M::State>,
    opts: &Options,
    early: bool,
    before_search: &dyn Fn(),
) -> Option<Found<'a, M>> {
    let early = early.then(|| {
        let checker = tlx_live::ConcreteChecker::new(&input.formulas(), &input.fairness);
        Mutex::new(Early { cx: Concrete::new(m, bits), checker, pending: IdMap::default(), off: false, fired: None })
    });
    let workers = if early.is_some() { 1 } else { opts.workers };
    let lm = LiveErrors { m, atoms, check_deadlock: opts.check_deadlock, early };
    let is_live_error = |r: &Report<M::State>| matches!(&r.outcome, Outcome::Error(e) if matches!(e.context, ErrorContext::Liveness));
    before_search();
    // (TLC's products depend on the order of its search: one worker.)
    let mut r = crate::explore_observed(m, &Options { progress: None, coverage_report: None, workers, ..opts.clone() }, &lm);
    if is_live_error(&r) && workers > 1 {
        // Where several workers stop is a race: once more with one, for
        // TLC's counts.
        before_search();
        r = crate::explore_observed(m, &Options { progress: None, coverage_report: None, workers: 1, ..opts.clone() }, &lm);
    }
    if !is_live_error(&r) {
        return None;
    }
    let fired = lm.early.and_then(|e| {
        let Early { mut cx, fired, .. } = e.into_inner().unwrap();
        cx.enable_gc();
        fired.map(|(prop, lasso)| Fired { cx, prop, lasso })
    });
    Some(Found { report: r, fired })
}
