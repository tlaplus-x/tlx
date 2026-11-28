//! What a running search exposes to the specification it checks:
//! live statistics (TLC's `TLCGet("stats")`, `"distinct"`, ...) and, in
//! simulation, the action that produced the current state
//! (`TLCGet("action")`).
//!
//! Both are reached through thread-locals installed on the threads of the
//! search (the workers, and the thread computing the initial states), so
//! that the interpreter can read them while it evaluates the model without
//! any plumbing through the `Model` interface. So is the path to the state
//! being expanded (`TLCExt!Trace`), for models that ask for it
//! (`Model::uses_trace`).

use std::cell::{Cell, RefCell};
use std::sync::Arc;

use tlx_value::Value;

/// Statistics of a search in progress (TLC's `TLCGet("stats")`). With
/// several workers they are approximate, as in TLC.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct LiveStats {
    /// States generated so far (initial states included).
    pub generated: u64,
    /// Distinct states found so far.
    pub distinct: u64,
    /// States waiting to be expanded.
    pub queue: u64,
    /// The deepest level reached (initial states are level 1).
    pub diameter: u64,
    /// Distinct initial states.
    pub initial: u64,
    /// Seconds since the search started.
    pub duration_secs: u64,
}

/// A running search that can report its statistics.
pub(crate) trait Source {
    fn snapshot(&self) -> LiveStats;
}

impl Source for LiveStats {
    fn snapshot(&self) -> LiveStats {
        *self
    }
}

/// The action that produced the current state of a simulated behavior.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CurrentAction {
    /// The state is an initial state.
    Init,
    /// The state was produced by this action (an index into `action_names`).
    Action(u32),
}

/// A state on the path from an initial state to the state being expanded
/// (`TLCExt!Trace`): its variable values, the action that produced it (none
/// for an initial state) and its predecessor. Paths share their prefixes.
#[derive(Debug)]
pub struct PathNode {
    pub values: Arc<[Value]>,
    pub action: Option<u32>,
    pub parent: Option<Arc<PathNode>>,
}

impl PathNode {
    /// The states of the path ending here, from the initial state.
    pub fn states(self: &Arc<Self>) -> Vec<Arc<PathNode>> {
        let mut out = Vec::new();
        let mut cur = Some(self.clone());
        while let Some(n) = cur {
            cur = n.parent.clone();
            out.push(n);
        }
        out.reverse();
        out
    }
}

/// What the running search knows of the path to the state it expands.
#[derive(Clone, Debug)]
pub enum CurrentPath {
    /// The path ends with the state being expanded.
    Known(Arc<PathNode>),
    /// The model uses `TLCExt!Trace` but the path is not available (a bug,
    /// or a search resumed without it): evaluating `Trace` fails.
    Unavailable,
}

thread_local! {
    static SOURCE: Cell<Option<*const (dyn Source + 'static)>> = const { Cell::new(None) };
    static PATH: RefCell<Option<CurrentPath>> = const { RefCell::new(None) };
    static ACTION: Cell<Option<CurrentAction>> = const { Cell::new(None) };
    /// In generation mode, while the successors of an action are computed:
    /// the state of the generator of the random choices.
    static GENERATE: Cell<Option<u64>> = const { Cell::new(None) };
    /// Whether the action being tried has produced a successor that
    /// satisfies the constraints (TLC's `INextStateFunctor.hasStates`).
    static HAS_STATES: Cell<bool> = const { Cell::new(false) };
    /// The number of the search or simulation worker running on this thread.
    static WORKER: Cell<Option<usize>> = const { Cell::new(None) };
}

/// The number of the worker (of a search or a simulation) running on this
/// thread, if any. TLC's worker 0 is the one whose TLCGet registers the
/// main thread reads (e.g. in the POSTCONDITION).
pub fn current_worker() -> Option<usize> {
    WORKER.with(|w| w.get())
}

/// This thread is worker `me` of a search or simulation.
pub(crate) fn set_current_worker(me: Option<usize>) {
    WORKER.with(|w| w.set(me));
}

/// Generation mode (TLC's `-generate`, i.e. `Tool.probabilistic`): true
/// while the successors of an action are being computed. The enumerator
/// then makes random choices instead of enumerating every alternative:
/// a disjunction tries its disjuncts, `\E` its bindings and `x' \in S` /
/// `x' \subseteq S` their values in a random order, and stops at the first
/// one after which the action has a successor (see `has_states`).
pub fn generating() -> bool {
    GENERATE.with(|g| g.get().is_some())
}

/// A random number below `n` (> 0) from the generation-mode generator.
pub fn gen_below(n: usize) -> usize {
    GENERATE.with(|g| {
        let mut rng = crate::simulate::Rng(g.get().unwrap_or(0));
        let r = rng.below(n);
        g.set(Some(rng.0));
        r
    })
}

/// A random stride for trying `n` alternatives from a random start (TLC's
/// `RandomGenerator.nextPrime`).
pub fn gen_stride() -> usize {
    crate::simulate::PRIMES[gen_below(crate::simulate::PRIMES.len())]
}

/// Whether the action being tried has produced a successor that satisfies
/// the constraints.
pub fn has_states() -> bool {
    HAS_STATES.with(|h| h.get())
}

/// Start (with the generator state) or stop (`None`) generation mode on
/// this thread; returns the previous generator state.
pub(crate) fn set_generating(state: Option<u64>) -> Option<u64> {
    HAS_STATES.with(|h| h.set(false));
    GENERATE.with(|g| g.replace(state))
}

pub(crate) fn set_has_states(on: bool) {
    HAS_STATES.with(|h| h.set(on));
}

/// The statistics of the search running on this thread, if any.
pub fn current() -> Option<LiveStats> {
    // SAFETY: a pointer in `SOURCE` was installed by `with_source` on this
    // thread, which removes it (also when unwinding) before its borrow of the
    // source ends; so it points to a live `Source`.
    SOURCE.with(|s| s.get().map(|p| unsafe { (*p).snapshot() }))
}

/// The path to the state the search on this thread expands, if the model
/// uses `TLCExt!Trace` (none outside a search, or before the first
/// expansion: then only an initial state is evaluated).
pub fn current_path() -> Option<CurrentPath> {
    PATH.with(|p| p.borrow().clone())
}

/// Run `f` with `path` as `current_path()` on this thread (the previous one
/// is restored afterwards, also on a panic).
pub fn with_path<R>(path: Option<CurrentPath>, f: impl FnOnce() -> R) -> R {
    struct Restore(Option<CurrentPath>);
    impl Drop for Restore {
        fn drop(&mut self) {
            PATH.with(|p| *p.borrow_mut() = self.0.take());
        }
    }
    let _restore = Restore(PATH.with(|p| p.replace(path)));
    f()
}

/// Run `f` with the trace path of the predecessor of the state being shown:
/// `current_path()` ends at the state being rendered, so `f` evaluates
/// `TLCExt!Trace` up to the state before it (the path that state was shown
/// with). Outside a path context, or with an unavailable one, `f` runs
/// unchanged.
pub fn with_predecessor_path<R>(f: impl FnOnce() -> R) -> R {
    let previous = match current_path() {
        // (No parent: the state being rendered is the initial one.)
        Some(CurrentPath::Known(node)) => node.parent.clone().map(CurrentPath::Known),
        _ => return f(),
    };
    with_path(previous, f)
}

/// Set `current_path()` on this thread (for a thread that runs nothing
/// else, such as a simulation worker); returns the previous one.
pub(crate) fn set_path(path: Option<CurrentPath>) -> Option<CurrentPath> {
    PATH.with(|p| p.replace(path))
}

/// The action that produced the current state, in simulation.
pub fn current_action() -> Option<CurrentAction> {
    ACTION.with(|a| a.get())
}

pub(crate) fn set_current_action(a: Option<CurrentAction>) {
    ACTION.with(|c| c.set(a));
}

/// Run `f` with `src` as the source of `current()` on this thread (the
/// previous source, if any, is restored afterwards, also on a panic).
///
/// A scoped function rather than a returned guard: a guard could be leaked
/// (`mem::forget`) or dropped out of order, leaving a dangling pointer in
/// `SOURCE`.
pub(crate) fn with_source<R>(src: &dyn Source, f: impl FnOnce() -> R) -> R {
    /// Restores the previous source when dropped.
    struct Restore(Option<*const (dyn Source + 'static)>);
    impl Drop for Restore {
        fn drop(&mut self) {
            SOURCE.with(|s| s.set(self.0));
        }
    }
    // SAFETY: only the lifetime bound of the trait object is erased (same
    // pointer, same vtable). The erased pointer is dereferenced only by
    // `current()` on this thread while it is in `SOURCE`, i.e. during `f`,
    // while `src` is borrowed.
    let p: *const (dyn Source + 'static) = unsafe { std::mem::transmute(src as *const dyn Source) };
    let _restore = Restore(SOURCE.with(|s| s.replace(Some(p))));
    f()
}

#[cfg(test)]
mod tests {
    use super::*;

    struct Fixed(u64);
    impl Source for Fixed {
        fn snapshot(&self) -> LiveStats {
            LiveStats { distinct: self.0, ..LiveStats::default() }
        }
    }

    #[test]
    fn sources_nest_and_are_removed() {
        assert_eq!(current(), None);
        let (a, b) = (Fixed(1), Fixed(2));
        with_source(&a, || {
            assert_eq!(current().unwrap().distinct, 1);
            with_source(&b, || assert_eq!(current().unwrap().distinct, 2));
            assert_eq!(current().unwrap().distinct, 1);
        });
        assert_eq!(current(), None);
    }

    #[test]
    fn source_is_removed_on_panic() {
        let a = Fixed(1);
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| with_source(&a, || panic!("boom"))));
        assert!(r.is_err());
        assert_eq!(current(), None);
    }
}
