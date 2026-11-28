//! Liveness checking after the search, model-generic (design.md §7.4): on
//! a behavior graph — of the whole state space recorded during the search,
//! of the state space explored again TLC's way (VIEW, SYMMETRY), or of one
//! simulated behavior — let tlx-live decide every temporal property under
//! the fairness of the spec, and name the properties a counterexample
//! violates. What depends on the specification (atoms, formulas, fairness)
//! is in tlx-eval; the CLI renders the counterexamples.

mod concrete;
mod expand;
pub(crate) mod recorded;
pub use recorded::RecordedWitness;
mod search;
mod shape;
mod trace;

pub use expand::{expand_concrete, par_map, ConcreteExpansion, ConcreteStep, STUTTER};
pub use search::{find_error, Fired, Found, SearchAtoms};
pub use shape::Lasso;
pub use trace::check_trace;

use crate::mem::RssGuard;
use crate::{AtomBits, LiveGraph, Model, ModelError};

/// The temporal properties of a spec to check and its fairness (from its
/// `LiveSpec`).
pub struct LiveInput<'a> {
    /// One formula per temporal PROPERTY part, with its property's name, in
    /// the order of the PROPERTIES.
    pub props: &'a [(String, tlx_live::Ltl)],
    /// The formula of each part of `props` alone (evaluated on a
    /// counterexample to name the properties it violates).
    pub alone: &'a [tlx_live::Ltl],
    pub fairness: Vec<tlx_live::Fairness>,
    /// VIEW or SYMMETRY: several states share a fingerprint, and the
    /// properties are checked TLC's way (`tlx_live::check_concrete`).
    pub concrete: bool,
}

impl LiveInput<'_> {
    fn formulas(&self) -> Vec<tlx_live::Ltl> {
        self.props.iter().map(|(_, f)| f.clone()).collect()
    }

    /// The state atoms of the tableaux TLC builds for the properties
    /// (`tlx_live::tableau_state_atoms`), each once.
    pub fn tableau_atoms(&self) -> Vec<u32> {
        let mut tableau = Vec::new();
        for (_, f) in self.props {
            for i in tlx_live::tableau_state_atoms(f, &self.fairness) {
                if !tableau.contains(&i) {
                    tableau.push(i);
                }
            }
        }
        tableau
    }

    /// Whether TLC may report a violation of a property during its search,
    /// before the end (see `find_error`).
    pub fn reports_early(&self) -> bool {
        self.props.iter().any(|(_, f)| tlx_live::reports_early(f, &self.fairness))
    }
}

/// The outcome of liveness checking.
pub enum LiveResult<S> {
    /// Every temporal property holds.
    Holds,
    /// A property is violated.
    Violated(Violation<S>),
    /// Checking failed (an error of the model, or of the checker: a
    /// `ModelError` of kind `General`).
    Error(ModelError),
    /// Checking needs more memory than the budget (`-maxmem`) allows: a
    /// resource limit of the run (see `crate::explore::liveness_memory_error`).
    OutOfMemory(String),
}

/// A violation of the temporal properties.
pub struct Violation<S> {
    /// The names of the properties the counterexample violates (as TLC:
    /// see `shape::violated_names`; with VIEW or SYMMETRY possibly none).
    pub names: Vec<String>,
    /// The part of `LiveInput::props` whose check found it.
    pub prop: usize,
    /// The counterexample as TLC shows it.
    pub lasso: Lasso<S>,
}

/// A liveness failure for lack of memory, from a model error (a memory
/// check stopping a search returns its message as one).
fn error_or_memory<S>(e: ModelError) -> LiveResult<S> {
    if e.message.starts_with(crate::explore::LIVENESS_MEMORY) {
        LiveResult::OutOfMemory(e.message)
    } else {
        LiveResult::Error(e)
    }
}

/// Check the temporal properties `input` on the states of `m`, with the
/// atoms evaluated by `bits`, on the behavior graph `recorded` during the
/// search (design.md §7.4); without one (a search that did not record it:
/// recovered from a checkpoint taken without liveness edges) the check is an
/// error.
///
/// With VIEW or SYMMETRY (`LiveInput::concrete`), where several states share
/// a fingerprint, the properties are checked TLC's way
/// (`tlx_live::check_concrete`): TLC's verdicts then depend on which of
/// these states it evaluates predicates on.
///
/// `expanded`: the number of states the search expanded if it stopped at
/// `TLCSet("exit", TRUE)` (TLC then checks the graph of these states; the
/// concrete checker expands the first ones in BFS order), else
/// `usize::MAX`.
pub fn check<M: Model>(
    m: &M,
    input: &LiveInput,
    bits: &(dyn AtomBits<M::State> + Sync),
    workers: usize,
    expanded: usize,
    recorded: Option<Result<LiveGraph, String>>,
    guard: RssGuard,
) -> LiveResult<M::State> {
    if input.concrete {
        return concrete::check_concrete(m, input, bits, workers, expanded, guard);
    }
    let g =
        match recorded {
            Some(Ok(g)) => g,
            Some(Err(msg)) => return LiveResult::OutOfMemory(msg),
            None => return LiveResult::Error(ModelError::new(
                "cannot check temporal properties: the search recorded no liveness edges (recovered from a checkpoint taken without them)",
            )),
        };
    let t0 = std::time::Instant::now();
    let r = recorded::check_recorded(m, input, g, workers, guard);
    crate::stats::add_secs("liveness: check (recorded graph)", t0.elapsed());
    r
}
