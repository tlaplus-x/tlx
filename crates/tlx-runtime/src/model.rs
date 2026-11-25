//! The interface between a model (interpreted or compiled) and the explorer.

use std::fmt;

use crate::explore::AtomBits;
use crate::queue::StateCodec;

/// Error raised while evaluating the model (TLC "evaluation error").
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModelError {
    pub message: String,
    /// The class of the error, which decides how TLC reports it (message
    /// code, exit status).
    pub kind: ErrorKind,
    /// What was being evaluated when the error occurred.
    pub context: ErrorContext,
}

/// What was being evaluated when an error occurred, as far as it changes
/// how TLC reports the error.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub enum ErrorContext {
    #[default]
    Other,
    /// The successors of a state (TLC reports a general error as an
    /// unexpected exception).
    NextState,
    /// Invariant `name` ("Evaluating invariant ... failed").
    Invariant(String),
    /// Action property `name` ("Evaluating action property ... failed").
    ActionProperty(String),
    /// The checks of an initial state, rendered (constraints, invariants):
    /// "While working on the initial state".
    InitialState(String),
    /// A state some variable has no value in (TLC: "not completely
    /// specified"): an initial state (`action` None) or a successor by
    /// action `action`, rendered with `null` for the missing values.
    IncompleteState { action: Option<u32>, state: String, missing: Vec<String> },
    /// The assumption at this location ("Evaluating assumption ... failed").
    Assumption(String),
    /// The predicates of the temporal properties or of fairness (TLC
    /// evaluates them as states are found: `LiveCheck.addInitState` /
    /// `addNextState`).
    Liveness,
}

/// Classes of evaluation errors that TLC reports differently (with their
/// own message codes, tlc2.output.EC, and exit statuses).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum ErrorKind {
    /// Any other error (TLC: a `RuntimeException`, EC.GENERAL).
    #[default]
    General,
    /// Explicit function application outside its domain (a TLC value
    /// operation wrapped in FingerprintException); reported as General.
    FunctionDomain,
    /// An unsupported construct (TLC: an `UnsupportedOperationException`).
    Unsupported,
    /// `Assert(FALSE, ...)` (TLC_VALUE_ASSERT_FAILED).
    AssertFailed,
    /// Division by zero (TLC_MODULE_DIVISION_BY_ZERO).
    DivisionByZero,
    /// An argument outside an operator's domain (TLC_MODULE_ARGUMENT_ERROR).
    ArgumentError,
    /// An integer result outside TLC's range (TLC_MODULE_OVERFLOW).
    Overflow,
    /// `0^0` (TLC_MODULE_NULL_POWER_NULL).
    NullPowerNull,
    /// `Head` / `Tail` of the empty sequence (TLC_MODULE_APPLY_EMPTY_SEQ).
    ApplyEmptySeq,
    /// An integer literal outside TLC's range (TLC_INTEGER_TOO_BIG).
    IntegerTooBig,
    /// Not an error of the spec: a value did not fit the layout of a
    /// compiled model, which stops the search to widen the layout and
    /// resume (`Effects::interrupts`). Reported, if ever, as a general error.
    LayoutMiss,
}

impl ModelError {
    pub fn new(message: impl Into<String>) -> ModelError {
        ModelError::of_kind(ErrorKind::General, message)
    }

    pub fn of_kind(kind: ErrorKind, message: impl Into<String>) -> ModelError {
        ModelError { message: message.into(), kind, context: ErrorContext::Other }
    }

    /// Whether this is a layout miss of a compiled model (`ErrorKind::LayoutMiss`).
    pub fn is_layout_miss(&self) -> bool {
        self.kind == ErrorKind::LayoutMiss
    }

    /// The error, raised in `context`.
    pub fn within(mut self, context: ErrorContext) -> ModelError {
        self.context = context;
        self
    }

    /// The error, raised while checking initial state `s`.
    pub fn on_initial_state<M: Model + ?Sized>(self, m: &M, s: &M::State) -> ModelError {
        self.within(ErrorContext::InitialState(m.render(s)))
    }

    /// The error, raised while computing successors (unless it already
    /// has a context, e.g. an invariant checked as successors are found).
    pub fn in_next_state(self) -> ModelError {
        match self.context {
            ErrorContext::Other => self.within(ErrorContext::NextState),
            _ => self,
        }
    }
}

impl fmt::Display for ModelError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.message)
    }
}

/// The message (so that an error can be used as its text).
impl std::ops::Deref for ModelError {
    type Target = str;

    fn deref(&self) -> &str {
        &self.message
    }
}

impl From<String> for ModelError {
    fn from(message: String) -> ModelError {
        ModelError::new(message)
    }
}

impl From<&str> for ModelError {
    fn from(message: &str) -> ModelError {
        ModelError::new(message)
    }
}

/// Writing the states of a model without a codec to a checkpoint and
/// reading them back (`StateFormat::Bytes`; the states of a model with a
/// codec are written as their words).
pub trait Persist<S>: Sync {
    /// Append state `s` to `out`.
    fn write_state(&self, s: &S, out: &mut Vec<u8>) -> Result<(), String>;
    /// The state `write_state` wrote as `b`, of depth `depth` and
    /// fingerprint `fp`.
    fn read_state(&self, b: &[u8], depth: u32, fp: u64) -> Result<S, String>;
}

/// How the states of a model are written (`Caps::format`).
pub enum StateFormat<'a, S> {
    /// As compact words (`crate::queue`): queued states are stored so, and
    /// checkpoints write them so.
    Words(&'a dyn StateCodec<S>),
    /// As bytes, in checkpoints only (queued states are kept as objects).
    Bytes(&'a dyn Persist<S>),
}

impl<S> Clone for StateFormat<'_, S> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<S> Copy for StateFormat<'_, S> {}

/// Side effects of evaluation across the searches of a run that are
/// interrupted and resumed (`Caps::effects`; docs/design.md §6.5.3).
pub trait Effects: Sync {
    /// Called on a worker's thread before it expands the first state of a
    /// level while the explorer retains states for a resumed search (a
    /// resumed search expands that level again) ...
    fn mark(&self) {}

    /// ... and when the worker ends.
    fn worker_end(&self) {}

    /// While `on`, the explorer evaluates again states a search expanded
    /// already (the levels before a resume point, expanded for their
    /// liveness edges after the search): output that evaluation would
    /// print again (Print, PrintT) is not printed.
    fn replaying(&self, _on: bool) {}

    /// Whether error `e` interrupts the search to have it resumed by
    /// another model (a compiled model's layout miss): the explorer then
    /// rebuilds no trace (which would evaluate the model again).
    fn interrupts(&self, _e: &ModelError) -> bool {
        false
    }
}

/// Checkpoints (docs/scale.md §9): what a model keeps besides its states
/// (`Caps::checkpoint`).
pub trait Checkpointed: Sync {
    /// The model's own files, as (name, contents) (e.g. the string table,
    /// the compiled tier's layouts), given back by
    /// `checkpoint::Recovery::file`. Called while no worker runs.
    fn files(&self) -> Result<Vec<(String, Vec<u8>)>, String> {
        Ok(Vec::new())
    }

    /// What the evaluation keeps on the current thread, a worker of the
    /// search (its TLCSet registers).
    fn worker_snapshot(&self) -> Result<Vec<u8>, String> {
        Ok(Vec::new())
    }

    /// What the evaluation keeps for the main thread (the TLCSet registers
    /// the workers start from). Called while no worker runs.
    fn main_snapshot(&self) -> Result<Vec<u8>, String> {
        Ok(Vec::new())
    }

    /// Recovering from a checkpoint: the main thread's state is `main`
    /// (`main_snapshot`), worker `i` of the recovered search starts from
    /// `snaps[i]` (`worker_snapshot` of worker `i` of the checkpointed
    /// one, which may have had another number of workers; the others start
    /// from the main thread's).
    fn restore_workers(&self, _main: &[u8], _snaps: &[Vec<u8>]) -> Result<(), String> {
        Ok(())
    }

    /// Whether the model hit a recoverable resource limit (such as value-store
    /// budget exhaustion) and wants the last committed checkpoint preserved
    /// when the search finishes so the user can retry with more resources.
    fn keep_checkpoint(&self) -> bool {
        false
    }
}

/// The optional capabilities of a model (`Model::caps`): None is "not
/// supported". The accessors give the defaults of a model without a
/// capability.
pub struct Caps<'a, S> {
    /// How states are written; None: they are queued as objects and the
    /// model cannot be checkpointed.
    pub format: Option<StateFormat<'a, S>>,
    /// The liveness atoms to evaluate on every expanded state and step
    /// while searching, recording the behavior graph (`Report::live_graph`);
    /// None: nothing is recorded.
    pub live_atoms: Option<&'a (dyn AtomBits<S> + Sync)>,
    /// Side effects across interrupted and resumed searches.
    pub effects: Option<&'a dyn Effects>,
    /// What checkpoints keep besides the states.
    pub checkpoint: Option<&'a dyn Checkpointed>,
}

impl<S> Default for Caps<'_, S> {
    fn default() -> Self {
        Caps { format: None, live_atoms: None, effects: None, checkpoint: None }
    }
}

impl<'a, S> Caps<'a, S> {
    /// The codec of the states, if they are written as words.
    pub fn codec(&self) -> Option<&'a dyn StateCodec<S>> {
        match self.format {
            Some(StateFormat::Words(c)) => Some(c),
            _ => None,
        }
    }

    /// How the states are written as bytes, if they are.
    pub fn persist(&self) -> Option<&'a dyn Persist<S>> {
        match self.format {
            Some(StateFormat::Bytes(p)) => Some(p),
            _ => None,
        }
    }

    /// `Effects::mark`.
    pub fn mark(&self) {
        if let Some(e) = self.effects {
            e.mark();
        }
    }

    /// `Effects::worker_end`.
    pub fn worker_end(&self) {
        if let Some(e) = self.effects {
            e.worker_end();
        }
    }

    /// `Effects::replaying`.
    pub fn replaying(&self, on: bool) {
        if let Some(e) = self.effects {
            e.replaying(on);
        }
    }

    /// `Effects::interrupts`.
    pub fn interrupts(&self, e: &ModelError) -> bool {
        self.effects.is_some_and(|x| x.interrupts(e))
    }

    /// `Checkpointed::files`.
    pub fn checkpoint_files(&self) -> Result<Vec<(String, Vec<u8>)>, String> {
        self.checkpoint.map_or(Ok(Vec::new()), |c| c.files())
    }

    /// `Checkpointed::worker_snapshot`.
    pub fn worker_snapshot(&self) -> Result<Vec<u8>, String> {
        self.checkpoint.map_or(Ok(Vec::new()), |c| c.worker_snapshot())
    }

    /// `Checkpointed::main_snapshot`.
    pub fn main_snapshot(&self) -> Result<Vec<u8>, String> {
        self.checkpoint.map_or(Ok(Vec::new()), |c| c.main_snapshot())
    }

    /// `Checkpointed::restore_workers`.
    pub fn restore_workers(&self, main: &[u8], snaps: &[Vec<u8>]) -> Result<(), String> {
        self.checkpoint.map_or(Ok(()), |c| c.restore_workers(main, snaps))
    }

    /// `Checkpointed::keep_checkpoint`.
    pub fn keep_checkpoint(&self) -> bool {
        self.checkpoint.is_some_and(|c| c.keep_checkpoint())
    }
}

/// A model to be explored by breadth-first search.
///
/// Implementations must be deterministic: `init_states` and `successors` must
/// produce the same states (in any order) every time they are called with the
/// same input, since error traces are reconstructed by re-execution.
///
/// The methods that decide verdicts and counts (the checks, the
/// constraints, `coarse_fingerprint`, `extra_generated`, `stop_requested`)
/// have no default, so that none is left out by accident; a model without
/// any of these checks says so with `model_without_checks!()`. The optional
/// capabilities (state format, liveness atoms, side effects across resumes,
/// checkpoints) are grouped in `caps`, whose default is "none". Behavior
/// added to a search (`-dump`, the liveness error search) is a
/// `crate::explore::SearchObserver`, not a model wrapping another.
pub trait Model: Sync {
    type State: Clone + Send + Sync;

    fn init_states(&self, out: &mut dyn FnMut(Self::State)) -> Result<(), ModelError>;

    /// `init_states` while `out` returns true: after it returned false no
    /// more initial states are passed to it (the search stops there, see
    /// `SearchObserver::stop`). A model whose generation of the initial
    /// states evaluates the spec stops generating them, so that it
    /// evaluates no more than a search that ended there; by default the
    /// rest are generated, and dropped.
    fn init_states_while(&self, out: &mut dyn FnMut(Self::State) -> bool) -> Result<(), ModelError> {
        let mut on = true;
        self.init_states(&mut |s| {
            if on {
                on = out(s);
            }
        })
    }

    /// Generate the successors of `s` (including stuttering ones), passing each
    /// to `out` as soon as it is produced; stop early when `out` returns false.
    /// `action` identifies the disjunct of Next that produced the successor
    /// (index into `action_names`).
    fn successors(&self, s: &Self::State, out: &mut dyn FnMut(Self::State, u32) -> bool) -> Result<(), ModelError>;

    /// The successors of `s` under action `action` only (TLC's simulator
    /// evaluates one action at a time). Returns false when `out` stopped the
    /// enumeration. By default, `successors` filtered by action.
    fn action_successors(&self, s: &Self::State, action: u32, out: &mut dyn FnMut(Self::State, u32) -> bool) -> Result<bool, ModelError> {
        let mut go_on = true;
        self.successors(s, &mut |t, a| {
            if a == action {
                go_on = out(t, a);
            }
            go_on
        })?;
        Ok(go_on)
    }

    /// Whether the model evaluates `TLCExt!Trace`: the search then keeps
    /// the path to each state it has yet to expand (`live::current_path`).
    fn uses_trace(&self) -> bool {
        false
    }

    /// Why a failed coarse-fingerprint replay may be incomplete. Computed
    /// only while reconstructing a counterexample, never on the search path.
    fn trace_replay_limit(&self) -> Option<&'static str> {
        None
    }

    /// The variable values of `s`, for `live::PathNode` when `uses_trace`.
    fn state_values(&self, _s: &Self::State) -> Option<std::sync::Arc<[tlx_value::Value]>> {
        None
    }

    fn fingerprint(&self, s: &Self::State) -> u64;

    /// Whether the fingerprint identifies a class of states rather than a
    /// state (VIEW, SYMMETRY): states of the same fingerprint may differ in
    /// what the actions and invariants read, so the results depend on which
    /// one represents the class (the first found in BFS order, as in TLC).
    /// A search of several workers then chooses the representatives in
    /// that order (docs/design.md §7.3).
    fn coarse_fingerprint(&self) -> bool;

    /// Returns the index (into `invariant_names`) of the first violated invariant.
    fn check_invariants(&self, s: &Self::State) -> Result<Option<usize>, ModelError>;

    /// A key of `s` (whose fingerprint is `fp`) for `check_invariants`, when
    /// that is a pure function of the state (no output, registers, random
    /// choices, ...): states with equal keys get the same result. The
    /// search checks states outside the constraints every time they are
    /// generated (as TLC does); with a key it skips the ones it has
    /// already checked without a violation (the result would be the same).
    /// None: always check.
    fn invariant_key(&self, _s: &Self::State, _fp: u64) -> Option<u64> {
        None
    }

    /// PROPERTY parts that are state predicates (TLC's implied inits),
    /// checked on initial states: the label of the first violated one.
    fn check_init_property(&self, s: &Self::State) -> Result<Option<String>, ModelError>;

    /// State constraint (CONSTRAINT): states violating it are not expanded.
    fn constraint(&self, s: &Self::State) -> Result<bool, ModelError>;

    /// Action constraint (ACTION_CONSTRAINT): transitions violating it are dropped.
    fn action_constraint(&self, s: &Self::State, t: &Self::State) -> Result<bool, ModelError>;

    /// Action properties (`PROPERTY [][A]_v`): checked on every generated
    /// transition. Returns the index (into `action_property_names`) of the
    /// first violated one.
    fn check_transition(&self, s: &Self::State, t: &Self::State) -> Result<Option<usize>, ModelError>;

    fn action_property_names(&self) -> &[String];

    /// States the model generated outside of `successors`' output that TLC
    /// counts as generated (intermediate states of action composition), as
    /// a running total; the explorer reports its increase during the run.
    fn extra_generated(&self) -> u64;

    /// Polled by workers; true stops exploration (e.g. `TLCSet("exit", TRUE)`).
    fn stop_requested(&self) -> bool;

    /// The optional capabilities of the model (see `Caps`).
    fn caps(&self) -> Caps<'_, Self::State> {
        Caps::default()
    }

    fn invariant_names(&self) -> &[String];
    fn action_names(&self) -> &[String];

    /// TLC-style rendering of a state (`/\ x = 1` lines).
    fn render(&self, s: &Self::State) -> String;
}

/// Whether the step `s -> t` of `m` stays in the model: `t` satisfies the
/// CONSTRAINT and the step the ACTION_CONSTRAINT (evaluated only if the
/// CONSTRAINT holds; an error of either is the result). The one definition
/// of a successor "in the model" for the search, the simulation and
/// liveness: each caller decides what an error means (propagated with `?`,
/// or, where the step was checked already, `.unwrap_or(false)`).
#[inline]
pub fn admits<M: Model + ?Sized>(m: &M, s: &M::State, t: &M::State) -> Result<bool, ModelError> {
    Ok(m.constraint(t)? && m.action_constraint(s, t)?)
}

/// The checks of a model that has none (no implied inits, constraints or
/// action properties, no composed states, never stops by itself, exact
/// fingerprints): expands to those `Model` methods, inside an
/// `impl Model for ...` block.
#[macro_export]
macro_rules! model_without_checks {
    () => {
        fn coarse_fingerprint(&self) -> bool {
            false
        }
        $crate::model_without_checks!(but coarse_fingerprint);
    };
    // (For a model with its own `coarse_fingerprint`.)
    (but coarse_fingerprint) => {
        fn check_init_property(&self, _s: &Self::State) -> Result<Option<String>, $crate::ModelError> {
            Ok(None)
        }
        fn constraint(&self, _s: &Self::State) -> Result<bool, $crate::ModelError> {
            Ok(true)
        }
        fn action_constraint(&self, _s: &Self::State, _t: &Self::State) -> Result<bool, $crate::ModelError> {
            Ok(true)
        }
        fn check_transition(&self, _s: &Self::State, _t: &Self::State) -> Result<Option<usize>, $crate::ModelError> {
            Ok(None)
        }
        fn action_property_names(&self) -> &[String] {
            &[]
        }
        fn extra_generated(&self) -> u64 {
            0
        }
        fn stop_requested(&self) -> bool {
            false
        }
    };
}
