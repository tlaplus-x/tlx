//! The evaluation context and the state-level definition caches: which
//! states the variables of an expression are read from (`Ctx`), the memo of
//! 0-ary state-level definitions over one state (`StateMemo`), the
//! per-context view of those memos (`DefCache`) and where a `DefCache` takes
//! a state's memo from when it first needs it (`MemoSource`). The dispatcher
//! (`eval.rs`) re-exports these; `count_def_eval` accounts the evaluations
//! that reach the memo path (`-stats`).

use tlx_sema::hir::DefId;
use tlx_value::Value;

use crate::error::EResult;

/// Which states variables are read from.
#[derive(Clone, Copy)]
pub struct Ctx<'a> {
    /// Current state (unprimed variables in Next).
    pub s0: Option<&'a [Value]>,
    /// Next state (primed variables in Next) or the partial initial state (Init).
    pub s1: Option<&'a [Option<Value>]>,
    /// Inside `e'`: unprimed variables are read from `s1`.
    pub primed: bool,
    /// Evaluating Init: variables are read from `s1`.
    pub init: bool,
    /// BFS level of the current state (`TLCGet("level")`); 0 in constant and Init contexts.
    pub level: u32,
    /// Values of 0-ary state-level definitions for this (complete) context.
    pub cache: Option<&'a DefCache<'a>>,
    /// Evaluating (a part of) the function of an application `f[e]`: like
    /// TLC's `EvalControl.KeepLazy`, function constructors stay lazy
    /// (FcnLambdaValue), so only the applied points are evaluated.
    pub keep_lazy: bool,
}

/// Values of 0-ary, deterministic, state-level definitions in one
/// (complete) state. Such a definition reads only the variables of that
/// state, so its value can be shared by every context over the state:
/// unprimed in a state or action context, or primed in an action context
/// whose next state it is.
#[derive(Default)]
pub struct StateMemo {
    defs: std::cell::RefCell<Vec<(DefId, Value)>>,
    /// Fingerprints of the variable values of the state.
    pub(crate) var_fps: std::cell::OnceCell<Vec<u64>>,
}

impl StateMemo {
    /// The memoized value of `d`, or `eval()` recorded on success.
    pub(super) fn get_or_eval(&self, d: DefId, eval: impl FnOnce() -> EResult<Value>) -> EResult<Value> {
        if let Some((_, v)) = self.defs.borrow().iter().find(|(x, _)| *x == d) {
            return Ok(v.clone());
        }
        let v = eval()?;
        self.defs.borrow_mut().push((d, v.clone()));
        Ok(v)
    }
}

/// Count an evaluation of a state-level definition's body in `cx` (`-stats`).
#[inline(always)]
pub(crate) fn count_def_eval(cx: &Ctx) {
    tlx_runtime::stats::count(if cx.primed { tlx_runtime::stats::C::DefEvalsPrimed } else { tlx_runtime::stats::C::DefEvals }, 1);
}

/// Where a `DefCache` gets the memos of its states on first use (e.g. a
/// per-thread table shared by all the contexts over the same states).
pub trait MemoSource {
    /// The memo of the current (`next`: the complete next) state.
    fn memo(&self, next: bool) -> std::rc::Rc<StateMemo>;
}

/// Per-context memo of 0-ary, deterministic, state-level definitions: their
/// values in the current state and (when it is complete) in the next state.
/// Only valid while the states of the context are fixed.
pub struct DefCache<'a> {
    unprimed: std::cell::OnceCell<std::rc::Rc<StateMemo>>,
    /// None: primed evaluations are not memoized (partial next state).
    primed: Option<std::cell::OnceCell<std::rc::Rc<StateMemo>>>,
    /// Source of the memos not given (None: fresh ones).
    source: Option<Box<dyn MemoSource + 'a>>,
}

impl Default for DefCache<'_> {
    fn default() -> Self {
        DefCache { unprimed: Default::default(), primed: Some(Default::default()), source: None }
    }
}

impl<'a> DefCache<'a> {
    /// A cache for contexts whose next state is partial: only unprimed
    /// evaluations are memoized.
    pub fn unprimed() -> Self {
        DefCache { unprimed: Default::default(), primed: None, source: None }
    }

    /// A cache sharing the memos of the current and (complete) next state.
    pub fn over(unprimed: std::rc::Rc<StateMemo>, primed: Option<std::rc::Rc<StateMemo>>) -> Self {
        DefCache { unprimed: std::cell::OnceCell::from(unprimed), primed: primed.map(std::cell::OnceCell::from), source: None }
    }

    /// A cache taking the memos of the current and (if `primed`: the
    /// complete) next state from `source` when first needed: contexts
    /// that evaluate no state-level definition do not look them up.
    pub fn from_source(source: Box<dyn MemoSource + 'a>, primed: bool) -> Self {
        DefCache { unprimed: Default::default(), primed: primed.then(Default::default), source: Some(source) }
    }

    fn get(&self, next: bool) -> Option<&StateMemo> {
        let cell = if next { self.primed.as_ref()? } else { &self.unprimed };
        Some(cell.get_or_init(|| self.source.as_ref().map_or_else(Default::default, |s| s.memo(next))))
    }

    /// The memo of the current state.
    pub(crate) fn current(&self) -> std::rc::Rc<StateMemo> {
        self.get(false);
        self.unprimed.get().expect("made above").clone()
    }

    /// Whether the value of definition `d` in the current (`primed`: next)
    /// state is known.
    pub fn knows(&self, d: DefId, primed: bool) -> bool {
        self.get(primed).is_some_and(|m| m.defs.borrow().iter().any(|(x, _)| *x == d))
    }

    /// Record `v` as the value of definition `d` in the current (`primed`:
    /// next) state, computed elsewhere (e.g. by compiled code), unless
    /// already known. `d` must be a redirected, state-cacheable definition;
    /// a primed value turns on the memo of primed evaluations, so the next
    /// state must be complete and fixed while the cache is in use.
    pub fn seed(&mut self, d: DefId, primed: bool, v: Value) {
        if primed && self.primed.is_none() {
            // (Not the source's: it need not know the next state.)
            self.primed = Some(std::cell::OnceCell::from(std::rc::Rc::default()));
        }
        let memo = self.get(primed).expect("primed memo turned on above");
        let mut defs = memo.defs.borrow_mut();
        if !defs.iter().any(|(x, _)| *x == d) {
            defs.push((d, v));
        }
    }

    /// The memo for evaluations in `cx`, if they may be memoized: never in
    /// Init (the state is partial), primed ones only when the next state is
    /// complete.
    pub(super) fn memo(&self, cx: &Ctx) -> Option<&StateMemo> {
        if cx.init {
            return None;
        }
        self.get(cx.primed)
    }
}

impl<'a> Ctx<'a> {
    /// Constant-level context (no state).
    pub const NONE: Ctx<'static> = Ctx { s0: None, s1: None, primed: false, init: false, level: 0, cache: None, keep_lazy: false };

    pub fn state(s0: &'a [Value], level: u32) -> Ctx<'a> {
        Ctx { s0: Some(s0), s1: None, primed: false, init: false, level, cache: None, keep_lazy: false }
    }

    pub fn action(s0: &'a [Value], s1: &'a [Option<Value>], level: u32) -> Ctx<'a> {
        Ctx { s0: Some(s0), s1: Some(s1), primed: false, init: false, level, cache: None, keep_lazy: false }
    }

    /// Context for enumerating Init over the partial state `s1`.
    pub fn init(s1: &'a [Option<Value>]) -> Ctx<'a> {
        Ctx { s0: None, s1: Some(s1), primed: false, init: true, level: 0, cache: None, keep_lazy: false }
    }

    /// The same context inside `e'`: unprimed variables are read from `s1`.
    pub(crate) fn primed(&self) -> Ctx<'a> {
        Ctx { primed: true, ..*self }
    }

    /// Memoize 0-ary state-level definitions in `c` (the context's states
    /// must be complete and fixed while `c` is in use).
    pub fn with_cache(self, c: &'a DefCache<'a>) -> Ctx<'a> {
        Ctx { cache: Some(c), ..self }
    }

    /// The same context with TLC's KeepLazy flag set or cleared.
    pub(crate) fn lazy(&self, keep_lazy: bool) -> Ctx<'a> {
        Ctx { keep_lazy, ..*self }
    }
}
