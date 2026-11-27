//! `EncModel`: the runtime `Model` over encoded states.
//!
//! Every action, invariant and action property runs natively if possible,
//! else as lowered IR (actions and Init), else in the interpreter. Native
//! and IR runs are speculative: on any failure the interpreter re-runs the
//! same (state, action) pair or predicate and has the last word.
//!
//! Mixed-mode native code calls back into the host for its regions
//! (`HostRegions`), with a per-worker `MixedCx` (`MIXED`).
//!
//! `tier` selects and dispatches the native, mixed and adaptive execution
//! tiers; `exec` runs `Init`, actions and predicates through the compiled,
//! IR and interpreted paths; `runtime_adapter` implements the
//! `tlx_runtime::Model` interface. This root keeps the model's state,
//! construction and layout-miss bookkeeping, plus the shared thread-local
//! emission and fallback scopes.

use std::cell::{Cell, RefCell};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock};

use tlx_eval::model::liveness::StateAtom;
use tlx_eval::model::State as VState;
use tlx_eval::{FpMode, InterpModel};
use tlx_layout::{Layout, Shape};
use tlx_native::mixed::MixedCx;
use tlx_runtime::stats;
use tlx_runtime::{ErrorKind, Model, ModelError};
use tlx_sema::hir::DefId;
use tlx_value::Value;

mod checks;
mod codec;
#[cfg(test)]
mod escape_tests;
mod exec;
mod fingerprint;
mod liveness;
mod runtime_adapter;
mod symmetry;
mod tier;
mod view;
mod view_shape;

use super::mixed::FastRegions;
use super::native::{self, NativeHandle};
use crate::exec::fast;
use crate::exec::memo::MemoScope;
use crate::ir::{ActionFn, PredFn, Stmt};
use crate::lower::Lowerer;
use crate::settings::{Inject, Settings};
use crate::types::Typing;
use fingerprint::Fingerprint;
pub(super) use fingerprint::SemFp;
use symmetry::{compile_symmetry, symmetry_order};
use view::View;

/// Lowered Init (None if it is interpreted) and actions (None for each
/// interpreted one), with a note on each that could not be lowered.
/// Actions whose shape dependencies did not change are imported from `reuse`.
fn lower_init_and_actions(
    lw: &mut Lowerer,
    base: &InterpModel,
    mut reuse: Option<&mut super::cache::ReuseSession<'_>>,
    notes: &mut Vec<String>,
) -> (Option<ActionFn>, Vec<Option<ActionFn>>, u64) {
    let init = lw.lower_init(base.init_expr()).map_err(|e| notes.push(format!("Init interpreted: {}", e.0))).ok();
    let mut reused = 0u64;
    let actions = base
        .actions()
        .iter()
        .enumerate()
        .map(|(i, a)| {
            if let Some(f) = reuse.as_deref_mut().and_then(|r| r.reuse_action(i, lw)) {
                reused += 1;
                return Some(f);
            }
            lw.lower_action(a).map_err(|e| notes.push(format!("action {} interpreted: {}", a.name, e.0))).ok()
        })
        .collect();
    (init, actions, reused)
}

/// Error message of a run stopped by a layout miss.
pub(super) const MISS_MSG: &str = "layout miss";

/// An encoded state.
#[derive(Clone, Debug)]
pub struct EState {
    pub(crate) words: Box<[u64]>,
    #[cfg(debug_assertions)]
    pub(crate) model: u64,
    pub level: u32,
    pub fp: u64,
}

impl EState {
    /// The immutable encoded state words.
    pub fn words(&self) -> &[u64] {
        &self.words
    }

    /// Construct a state from trusted encoder or generated-code output.
    ///
    /// # Safety
    /// `words` must be valid for the model's layout; active Dyn handles must
    /// satisfy `tlx_layout::dynval::lookup_unchecked`'s publication contract.
    pub unsafe fn from_words(model: &EncModel, words: Box<[u64]>, level: u32, fp: u64) -> Self {
        #[cfg(not(debug_assertions))]
        let _ = model;
        Self {
            words,
            level,
            fp,
            #[cfg(debug_assertions)]
            model: model.id,
        }
    }
}

/// A value that did not fit the speculated layout.
pub(super) enum Miss {
    /// Of state variable `.0`.
    Var(usize, Value),
    /// Of the materialized definition `def_shapes[.0]`.
    Def(usize, Value),
}

/// A compiled predicate to evaluate (`EncModel::predicate`): entry `idx`
/// of `invariants` on the state `s` (`t` None), or of `aprops` on the step
/// `s -> t`, at level `level`.
#[derive(Clone, Copy)]
struct PredAt<'a> {
    idx: usize,
    s: &'a EState,
    t: Option<&'a EState>,
    level: u32,
    /// An invariant: its native verdict is a target of
    /// TLX_INJECT_MISMATCH=inv.
    inject: bool,
}

/// The checkpoint files of the compiled tier: the driver's shapes, the
/// `Dyn` interner, and (with `TLX_VALUE_STORE`) the value store.
pub(super) const SPECULATION_FILE: &str = "shapes";
pub(super) const DYN_FILE: &str = "dyn";
pub(super) const STORE_FILE: &str = "store";

pub struct EncModel {
    pub base: Arc<InterpModel>,
    pub(super) escape: Option<super::escape::Escape>,
    pub layout: Arc<Layout>,
    pub(super) typing: Typing,
    pub(super) actions: Vec<Option<ActionFn>>,
    pub(super) invariants: Vec<PredFn>,
    pub(super) aprops: Vec<PredFn>,
    /// Liveness atoms compiled after the invariants and action properties:
    /// per state atom its index in `invariants` (None for `EnabledVia`),
    /// and the index in `aprops` of the first action atom.
    live_state: Vec<Option<usize>>,
    live_action: usize,
    /// CONSTRAINTs compiled after the invariants (index of the first), and
    /// ACTION_CONSTRAINTs after the action properties.
    constraint_at: usize,
    action_constraint_at: usize,
    /// Generated native code (None if disabled, nothing is native or the
    /// C build failed); built in the background, so it may not be loaded
    /// yet.
    native: Option<NativeHandle>,
    /// Actions worth running in the IR executor when not native: without
    /// interpreter-fallback nodes (those re-enter the interpreter per node,
    /// without its caches, and can be slower than interpreting the action).
    /// Composition uses the compiled executor even with host nodes, so its
    /// state transitions and continuations retain their compiled operations.
    exec_ok: Vec<bool>,
    /// Per action: a compiled run may print (Print/PrintT in a native
    /// region, `RegionOracle::mixes_next`): its output is held back until
    /// the run succeeds, as a failed run is redone by the interpreter.
    prints: Vec<bool>,
    /// Init may run in the IR executor when not native: it evaluates no
    /// side-effecting builtin (a failed run is redone by the interpreter,
    /// which would repeat the effects).
    init_exec_ok: bool,
    /// Per entry of `invariants`: evaluated in the IR executor before the
    /// interpreter when not native (see `pred_exec_ok`).
    pred_exec_ok: Vec<bool>,
    /// As `pred_exec_ok`, for the entries of `aprops` (only with the
    /// closure-compiled executor, `fast`).
    aprop_exec_ok: Vec<bool>,
    /// Memo scope of the IR executor runs over this model's IR (on when
    /// mixed mode memoizes its regions).
    memo: MemoScope,
    /// Mixed functions run natively or by their fallback, whichever is
    /// faster (`adapt`; `TLX_MIXED_ADAPT`, not with `TLX_MIXED_FORCE`).
    adapt: bool,
    /// Closure-compiled IR; uncovered functions run in the interpreter.
    fast: fast::Compiled,
    /// The mixed-mode regions of the native library compiled for `fast`
    /// (on first use; `FastRegions`).
    fast_regions: Vec<OnceLock<Option<fast::ExprProg>>>,
    /// How states are fingerprinted (decided once, in `new`).
    fp: Fingerprint,
    /// With value store slots: where their handles are, for semantic
    /// fingerprints (see `SemFp`).
    pub(super) sem: Option<SemFp>,
    /// Cross-check compiled results against the interpreter (TLX_PARANOID).
    paranoid: bool,
    /// Testing: the compiled result to corrupt (TLX_INJECT_MISMATCH), and
    /// the eligible results seen so far.
    inject: Option<Inject>,
    inject_seen: AtomicU64,
    /// First layout miss: (variable, value).
    miss: Mutex<Option<(usize, Value)>>,
    /// Materialized definitions and their shapes.
    def_shapes: Vec<(DefId, Shape)>,
    /// First materialized-definition miss: (index in `def_shapes`, value).
    def_miss: Mutex<Option<(usize, Value)>>,
    /// The invariants are a pure function of the state (see
    /// `Model::invariant_key`).
    pure_invariants: bool,
    /// Action runs that fell back to the interpreter (striped: incremented
    /// by every worker, read once at the end).
    pub bailouts: tlx_base::counter::Striped,
    pub notes: Vec<String>,
    /// Distinct id (key of the per-worker decoded-state cache).
    id: u64,
    /// A layout miss restarts the run (with another model). Cleared when
    /// the search is over: in the phases after it (liveness, `-dump`), a
    /// value that does not fit a materialized definition's shape is
    /// evaluated by the interpreter instead.
    pub(super) restartable: bool,
    /// Checkpoints: the driver's state (the shapes and their misses, the
    /// attempt, store mode), which a recovered run starts from (`Checkpointed::files`).
    pub(super) speculation: Vec<u8>,
    /// Checkpoints: the run's value store when `TLX_VALUE_STORE` is active
    /// (present even while all current slots are fixed, so `model-store`
    /// matches the store mode recorded in `speculation`).
    pub(super) checkpoint_store: Option<tlx_layout::store::StoreRef>,
    /// Compile-time constant value-store handles baked into IR/native/JIT code
    /// (`ConstWords`, `ConstElems`, `Const` of `Ref`-bearing shapes); kept
    /// rooted in every safepoint GC cycle.
    pub(super) pinned_handles: Box<[u64]>,
}

impl EncModel {
    pub fn new(base: Arc<InterpModel>, layout: Arc<Layout>, def_shapes: Vec<(DefId, Shape)>, settings: &Settings) -> EncModel {
        Self::new_with_cache(base, layout, def_shapes, settings, None)
    }

    pub(super) fn new_with_cache(
        base: Arc<InterpModel>,
        layout: Arc<Layout>,
        def_shapes: Vec<(DefId, Shape)>,
        settings: &Settings,
        mut cache: Option<&mut super::cache::CompileCache>,
    ) -> EncModel {
        let lowering_start = std::time::Instant::now();
        let ip = base.ip.clone();
        let mut lw = Lowerer::with_typing(&ip, Typing::with_defs(layout.clone(), &def_shapes));
        let mut notes = Vec::new();
        let live = &base.live;
        let total_invariants = base.invariant_exprs().len()
            + base.constraint_exprs().len()
            + live.state_atoms.iter().filter(|a| matches!(a, StateAtom::Pred(_))).count();
        let total_aprops = base.action_property_exprs().len() + base.action_constraint_exprs().len() + live.action_atoms.len();
        let mut reuse = cache
            .as_deref()
            .and_then(|c| c.begin(&mut lw, &layout.vars, &def_shapes, base.actions().len(), total_invariants, total_aprops));
        let (init, actions, reused_actions) = lower_init_and_actions(&mut lw, &base, reuse.as_mut(), &mut notes);
        let mut reused_preds = 0u64;
        let mut invariants: Vec<PredFn> = Vec::with_capacity(total_invariants);
        for (e, n) in base.invariant_exprs().iter().zip(base.invariant_names()) {
            let idx = invariants.len();
            if let Some(p) = reuse.as_mut().and_then(|r| r.reuse_invariant(idx, &mut lw)) {
                reused_preds += 1;
                invariants.push(p);
            } else {
                invariants.push(lw.lower_pred(n, e));
            }
        }
        let mut aprops: Vec<PredFn> = Vec::with_capacity(total_aprops);
        for (e, n) in base.action_property_exprs().iter().zip(base.action_property_names()) {
            let idx = aprops.len();
            if let Some(p) = reuse.as_mut().and_then(|r| r.reuse_aprop(idx, &mut lw)) {
                reused_preds += 1;
                aprops.push(p);
            } else {
                aprops.push(lw.lower_trans_pred(n, e));
            }
        }
        let constraint_at = invariants.len();
        for (k, e) in base.constraint_exprs().iter().enumerate() {
            let idx = invariants.len();
            if let Some(p) = reuse.as_mut().and_then(|r| r.reuse_invariant(idx, &mut lw)) {
                reused_preds += 1;
                invariants.push(p);
            } else {
                invariants.push(lw.lower_pred(&format!("constraint_{k}"), e));
            }
        }
        let action_constraint_at = aprops.len();
        for (k, e) in base.action_constraint_exprs().iter().enumerate() {
            let idx = aprops.len();
            if let Some(p) = reuse.as_mut().and_then(|r| r.reuse_aprop(idx, &mut lw)) {
                reused_preds += 1;
                aprops.push(p);
            } else {
                aprops.push(lw.lower_trans_pred(&format!("action_constraint_{k}"), e));
            }
        }
        let live_state = live
            .state_atoms
            .iter()
            .enumerate()
            .map(|(k, a)| match a {
                StateAtom::Pred(a) => {
                    let idx = invariants.len();
                    if let Some(p) = reuse.as_mut().and_then(|r| r.reuse_invariant(idx, &mut lw)) {
                        reused_preds += 1;
                        invariants.push(p);
                    } else {
                        invariants.push(lw.lower_pred_in(&format!("live_state_{k}"), &a.expr, &a.env, false));
                    }
                    Some(invariants.len() - 1)
                }
                StateAtom::EnabledVia(..) => None,
            })
            .collect();
        let live_action = aprops.len();
        for (k, a) in live.action_atoms.iter().enumerate() {
            let idx = aprops.len();
            if let Some(p) = reuse.as_mut().and_then(|r| r.reuse_aprop(idx, &mut lw)) {
                reused_preds += 1;
                aprops.push(p);
            } else {
                aprops.push(lw.lower_pred_in(&format!("live_action_{k}"), &a.expr, &a.env, true));
            }
        }
        drop(reuse);
        if reused_actions > 0 {
            stats::add_count("actions reused from IR cache", reused_actions);
        }
        if reused_preds > 0 {
            stats::add_count("predicates reused from IR cache", reused_preds);
        }
        let mut exec_ok: Vec<bool> = actions
            .iter()
            .map(|a| {
                a.as_ref().is_some_and(|f| {
                    (f.body.has_composition() && !lw.stmt_volatile_beyond_output(&f.body))
                        || crate::ir::Coverage::of_stmt(&f.body).interp == 0
                })
            })
            .collect();
        let prints: Vec<bool> = actions.iter().map(|a| a.as_ref().is_some_and(|f| lw.stmt_volatile(&f.body))).collect();
        if let Some(name) = tlx_base::diag::ir_dump() {
            super::diag::dump_ir(&name, tlx_base::diag::ir_dump_raw(), &actions, invariants.iter().chain(&aprops), &lw.typing.funcs);
        }
        let mut init_exec_ok = init.as_ref().is_some_and(|f| !lw.stmt_volatile(&f.body));
        let pred_ok = |p: &PredFn| {
            let body = Stmt::Guard { cond: p.body.clone(), then: Box::new(Stmt::Stop) };
            pred_exec_ok(&body, &lw)
        };
        let mut pred_exec_ok: Vec<bool> = invariants.iter().map(&pred_ok).collect();
        let mut aprop_exec_ok: Vec<bool> = aprops.iter().map(pred_ok).collect();
        tlx_runtime::stats::add_secs("IR lowering", lowering_start.elapsed());
        let verified = crate::verify::enforce(crate::verify::Program::new(&lw.typing, init.as_ref(), &actions, &invariants, &aprops));
        let fast = match &verified {
            Ok(p) => fast::Compiled::from_verified(p, &mut notes),
            Err(e) => {
                notes.push(format!("IR verification failed; interpreting model: {e}"));
                fast::Compiled::empty(actions.len(), invariants.len(), aprops.len())
            }
        };
        init_exec_ok &= fast.init.is_some();
        for (index, eligible) in exec_ok.iter_mut().enumerate() {
            *eligible &= fast.actions[index].is_some();
        }
        for (index, eligible) in pred_exec_ok.iter_mut().enumerate() {
            *eligible &= fast.preds[index].is_some();
        }
        for (index, eligible) in aprop_exec_ok.iter_mut().enumerate() {
            *eligible &= fast.aprops[index].is_some();
        }
        let native = if settings.no_native {
            None
        } else if let Ok(verified) = &verified {
            let mixed = settings.mixed.then_some(crate::native_plan::Mixed { oracle: &lw, force: settings.mixed_force, loops: true });
            #[cfg(feature = "jit")]
            let jit_cache = cache.as_deref_mut().map(|c| &mut c.jit);
            #[cfg(feature = "jit")]
            {
                native::build(verified, &base, settings, mixed, jit_cache, &mut notes)
            }
            #[cfg(not(feature = "jit"))]
            {
                native::build(verified, &base, settings, mixed, &mut notes)
            }
        } else {
            None
        };
        if verified.is_ok() {
            if let Some(c) = cache {
                c.update(&base, &lw, &def_shapes, &actions, &invariants, &aprops);
            }
        }
        let irreversible_actions =
            settings.escape.then(|| actions.iter().map(|a| a.as_ref().is_some_and(|f| lw.stmt_volatile_beyond_output(&f.body))).collect());
        let typing = lw.into_typing();
        let symmetry = compile_symmetry(&base, &layout, &mut notes);
        let view = View::compile(&base, &layout, &def_shapes, settings, &mut notes);
        let fast_regions = match native.as_deref().and_then(|n| n.regions.as_ref()) {
            Some(t) => FastRegions::compile(t, &typing, &fast.prog),
            _ => Vec::new(),
        };
        let has_symmetry = base.has_symmetry();
        let fp = match (symmetry, view) {
            (_, Some(view)) if base.has_projected_symmetry() => Fingerprint::View(view),
            // VIEW with SYMMETRY: TLC takes the VIEW of the orbit's least
            // state in TLC's value order (`base.var_order`), found directly on
            // encoded words with fallback to by-value selection when needed.
            (Some(engine), Some(view)) => Fingerprint::SymView { engine, order: base.var_order(layout.vars.len()).to_vec(), view },
            (Some(engine), None) if !base.has_view() => Fingerprint::Symmetry { engine, order: symmetry_order(&layout) },
            (None, Some(view)) if !has_symmetry => Fingerprint::View(view),
            _ if base.has_view_or_symmetry() => Fingerprint::Values,
            _ => Fingerprint::Words,
        };
        let sem = SemFp::of(
            &layout,
            match &fp {
                Fingerprint::View(v) | Fingerprint::SymView { view: v, .. } => v.typing.layout.vars.last(),
                _ => None,
            },
        );
        let pure_invariants = !base.invariant_names().is_empty() && !super::speculate::invariants_volatile(&base);
        match fp {
            Fingerprint::Symmetry { .. } => notes.push("symmetry: permuting encodings".into()),
            Fingerprint::SymView { .. } => notes.push("symmetry: least state on encodings, VIEW of its permuted encoding".into()),
            _ => {}
        }
        // Fingerprints computed here (on encodings): the interpreter need
        // not reduce the states it produces.
        let base = if matches!(fp, Fingerprint::Symmetry { .. } | Fingerprint::View(_) | Fingerprint::SymView { .. }) {
            Arc::new(base.with_fp_mode(FpMode::Plain))
        } else {
            base
        };
        let escape =
            settings.escape.then(|| super::escape::Escape::new(layout.clone(), base.clone(), settings, irreversible_actions.unwrap()));
        let id = MODEL_IDS.fetch_add(1, Ordering::Relaxed);
        if stats::on() {
            if let Some(t) = native.as_deref().and_then(|n| n.regions.as_ref()) {
                stats::set_json_source(&format!("native_regions_{id}"), Arc::new(t.json_source(&typing)));
            }
        }
        let pinned_handles = if sem.as_ref().and_then(|s| s.store.as_ref()).is_some() {
            collect_pinned_handles(
                &typing,
                init.as_ref(),
                &actions,
                &invariants,
                &aprops,
                match &fp {
                    Fingerprint::View(v) | Fingerprint::SymView { view: v, .. } => Some(v),
                    _ => None,
                },
                native.as_deref().and_then(|n| n.regions.as_ref()),
            )
        } else {
            Box::new([])
        };
        EncModel {
            escape,
            fp,
            sem,
            base,
            layout,
            typing,
            actions,
            invariants,
            aprops,
            live_state,
            live_action,
            constraint_at,
            action_constraint_at,
            exec_ok,
            prints,
            init_exec_ok,
            pred_exec_ok,
            aprop_exec_ok,
            // (One scope for the IR executor and the regions: a thread's
            // table is reset when it switches scopes.)
            memo: MemoScope::with(settings.mixed, "compiled"),
            adapt: settings.mixed && settings.mixed_adapt && settings.mixed_force == 0,
            fast,
            fast_regions,
            native,
            paranoid: settings.paranoid,
            inject: settings.inject,
            inject_seen: AtomicU64::new(0),
            miss: Mutex::new(None),
            def_shapes,
            def_miss: Mutex::new(None),
            pure_invariants,
            bailouts: tlx_base::counter::Striped::new(),
            notes,
            id,
            restartable: false,
            speculation: Vec::new(),
            checkpoint_store: None,
            pinned_handles,
        }
    }

    pub(super) fn lowered_actions(&self) -> usize {
        self.actions.iter().filter(|a| a.is_some()).count()
    }

    /// This model follows a layout-miss restart of the run (the driver): its
    /// layout had no cached C library (see `Native::at_exit_build`).
    pub(super) fn note_restart(&self) {
        if let Some(n) = self.native.as_deref() {
            n.set_restarted();
        }
    }

    #[inline]
    fn escaped(&self, s: &EState) -> bool {
        self.escape.is_some() && s.words.len() > self.layout.words
    }

    /// Execute a published version transactionally: no successor is emitted
    /// until this one action has completed without a layout miss.
    fn escape_action(&self, s: &EState, i: usize, out: &mut dyn FnMut(EState, u32) -> bool) -> Option<Result<bool, ModelError>> {
        let escape = self.escape.as_ref()?;
        let version = escape.version()?;
        let vals = self.cached_values(&s.words, true);
        let input = match version.encode(&VState::new(vals.clone(), s.level, 0)) {
            Ok(s) => s,
            Err(_) => {
                escape.observe(&vals);
                return None;
            }
        };
        let mut buf = Vec::new();
        let mark = tlx_eval::Interp::hold_begin();
        let r = version.action_successors(&input, i as u32, &mut |t, act| {
            buf.push((version.values(&t), t.level, act));
            true
        });
        let lines = tlx_eval::Interp::hold_end(mark);
        if r.is_err() {
            return None;
        }
        let mut encoded = Vec::with_capacity(buf.len());
        for (vals, level, act) in buf {
            match self.encode(&VState::new(vals.clone(), level, 0)) {
                Ok(t) => encoded.push((t, act)),
                Err(e) => return Some(Err(e)),
            }
        }
        self.base.ip.release_output(lines);
        for (t, act) in encoded {
            if !out(t, act) {
                return Some(Ok(false));
            }
        }
        Some(Ok(true))
    }

    /// The first layout miss of the last run, if any (a variable miss takes
    /// precedence over a definition miss); clears both.
    pub(super) fn take_miss(&self) -> Option<Miss> {
        let def = self.def_miss.lock().unwrap().take();
        let var = self.miss.lock().unwrap().take();
        var.map(|(i, v)| Miss::Var(i, v)).or(def.map(|(i, v)| Miss::Def(i, v)))
    }

    /// Record the first layout miss (later ones are ignored).
    fn record_miss(slot: &Mutex<Option<(usize, Value)>>, i: usize, v: Value) -> ModelError {
        let mut slot = slot.lock().unwrap();
        if slot.is_none() {
            *slot = Some((i, v));
        }
        ModelError::of_kind(ErrorKind::LayoutMiss, MISS_MSG)
    }
}

thread_local! {
    /// The mixed-mode state of this worker's native calls, the id of the
    /// `EncModel` whose layout its decoded-state cache is for, and the value
    /// store GC generation it was populated under.
    static MIXED: RefCell<(u64, u64, MixedCx)> = RefCell::new((0, 0, MixedCx::new()));
    /// Un-emitted compiled/encoded states currently being streamed to `out` on
    /// this worker thread, kept here so mid-action GC safepoints mark their
    /// `Shape::Ref` handles.
    static PENDING_EMIT: RefCell<Vec<PendingEmit>> = const { RefCell::new(Vec::new()) };
    /// Thread-local flag set on persistent `StoreFull` retries so compiled
    /// predicates and VIEW expressions skip store-allocating native/IR paths
    /// and evaluate through the interpreter instead.
    static TRANSIENT_FALLBACK: Cell<bool> = const { Cell::new(false) };
}

struct TransientFallbackScope(bool);

impl TransientFallbackScope {
    fn enter() -> Self {
        let prev = TRANSIENT_FALLBACK.with(|f| f.replace(true));
        TransientFallbackScope(prev)
    }
}

impl Drop for TransientFallbackScope {
    fn drop(&mut self) {
        TRANSIENT_FALLBACK.with(|f| f.set(self.0));
    }
}

struct PendingEmit {
    model_id: u64,
    words: Vec<Box<[u64]>>,
}

struct EmitGuard;

impl EmitGuard {
    fn push_words(model_id: u64, words: Vec<Box<[u64]>>) -> EmitGuard {
        PENDING_EMIT.with(|p| p.borrow_mut().push(PendingEmit { model_id, words }));
        EmitGuard
    }

    fn push_word(&self, w: Box<[u64]>) {
        PENDING_EMIT.with(|p| {
            if let Some(entry) = p.borrow_mut().last_mut() {
                entry.words.push(w);
            }
        });
    }

    fn pop_word(&self) -> Option<Box<[u64]>> {
        PENDING_EMIT.with(|p| p.borrow_mut().last_mut().and_then(|e| e.words.pop()))
    }

    fn take_words(self) -> Vec<Box<[u64]>> {
        let words = PENDING_EMIT.with(|p| p.borrow_mut().last_mut().map(|e| std::mem::take(&mut e.words)).unwrap_or_default());
        drop(self);
        words
    }
}

impl Drop for EmitGuard {
    fn drop(&mut self) {
        PENDING_EMIT.with(|p| {
            p.borrow_mut().pop();
        });
    }
}

impl EncModel {
    pub(super) fn set_transient_fallback(on: bool) {
        TRANSIENT_FALLBACK.with(|f| f.set(on));
    }

    #[inline]
    pub(super) fn transient_fallback() -> bool {
        TRANSIENT_FALLBACK.with(Cell::get)
    }

    /// Append all `Shape::Ref` handles from un-emitted states currently held
    /// in `PENDING_EMIT` for this model on the calling thread into `out`.
    pub(super) fn take_pending_emit_roots(&self, out: &mut Vec<u64>) {
        let Some(sem) = &self.sem else { return };
        if sem.state.is_empty() {
            return;
        }
        PENDING_EMIT.with(|p| {
            for entry in p.borrow().iter() {
                if entry.model_id != self.id {
                    continue;
                }
                for w in &entry.words {
                    for &off in &sem.state {
                        if let Some(&h) = w.get(off) {
                            out.push(h);
                        }
                    }
                }
            }
        });
    }
}

/// Walk all lowered IR (Init, actions, invariants, action properties, helper
/// functions, VIEW, and mixed-mode regions) and collect every value-store
/// handle baked into constant encodings (`ConstWords`, `ConstElems`, and
/// `Const` of `Ref`-bearing shapes) so GC never sweeps handles embedded in
/// compiled/JIT/C code.
fn collect_pinned_handles(
    typing: &Typing,
    init: Option<&ActionFn>,
    actions: &[Option<ActionFn>],
    invariants: &[PredFn],
    aprops: &[PredFn],
    view: Option<&View>,
    regions: Option<&super::mixed::RegionTable>,
) -> Box<[u64]> {
    let mut handles = Vec::new();
    let mut offs = Vec::new();
    let mut enc_buf = Vec::new();

    fn walk_expr(e: &crate::ir::Expr, typing: &Typing, offs: &mut Vec<usize>, enc_buf: &mut Vec<u64>, out: &mut Vec<u64>) {
        match &*e.kind {
            crate::ir::ExprKind::ConstWords(w) => {
                if let crate::ir::Ty::Enc(sid) = e.ty {
                    offs.clear();
                    if tlx_layout::layout::ref_offsets(typing.shape(sid), 0, offs).is_some() {
                        for &o in offs.iter() {
                            if let Some(&h) = w.get(o) {
                                out.push(h);
                            }
                        }
                    }
                }
            }
            crate::ir::ExprKind::ConstElems { elem, words, count } => {
                offs.clear();
                if tlx_layout::layout::ref_offsets(typing.shape(*elem), 0, offs).is_some() && !offs.is_empty() {
                    let ew = typing.words(*elem) as usize;
                    for k in 0..(*count as usize) {
                        let base = k * ew;
                        for &o in offs.iter() {
                            if let Some(&h) = words.get(base + o) {
                                out.push(h);
                            }
                        }
                    }
                }
            }
            crate::ir::ExprKind::Const(v) => {
                if let crate::ir::Ty::Enc(sid) = e.ty {
                    let shape = typing.shape(sid);
                    if tlx_layout::layout::has_ref(shape) {
                        offs.clear();
                        if tlx_layout::layout::ref_offsets(shape, 0, offs).is_some() && !offs.is_empty() {
                            enc_buf.resize(typing.words(sid) as usize, 0);
                            if let Ok(n) = v.normalize() {
                                if typing.node(sid).encode(&n, enc_buf).is_ok() {
                                    for &o in offs.iter() {
                                        if let Some(&h) = enc_buf.get(o) {
                                            out.push(h);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        e.for_each_child(&mut |c| walk_expr(c, typing, offs, enc_buf, out));
    }

    fn walk_stmt(s: &Stmt, ty: &Typing, offs: &mut Vec<usize>, enc_buf: &mut Vec<u64>, handles: &mut Vec<u64>) {
        s.for_each_expr_deep(&mut |e| walk_expr(e, ty, offs, enc_buf, handles));
    }

    if let Some(i) = init {
        walk_stmt(&i.body, typing, &mut offs, &mut enc_buf, &mut handles);
    }
    for a in actions.iter().flatten() {
        walk_stmt(&a.body, typing, &mut offs, &mut enc_buf, &mut handles);
    }
    for p in invariants.iter().chain(aprops) {
        walk_expr(&p.body, typing, &mut offs, &mut enc_buf, &mut handles);
    }
    for f in &typing.funcs {
        walk_expr(&f.body, typing, &mut offs, &mut enc_buf, &mut handles);
    }
    if let Some(v) = view {
        walk_stmt(&v.action.body, &v.typing, &mut offs, &mut enc_buf, &mut handles);
        for f in &v.typing.funcs {
            walk_expr(&f.body, &v.typing, &mut offs, &mut enc_buf, &mut handles);
        }
    }
    if let Some(table) = regions {
        for r in &table.regions {
            walk_expr(&r.expr, typing, &mut offs, &mut enc_buf, &mut handles);
        }
    }
    handles.sort_unstable();
    handles.dedup();
    handles.into_boxed_slice()
}

/// Source of the ids of `EncModel`s (0: none).
static MODEL_IDS: AtomicU64 = AtomicU64::new(1);

/// TLX_BAILOUT_DEBUG=n: report the first n IR executor errors.
fn bailout_debug(what: &str, e: &tlx_eval::EvalError) {
    static LEFT: std::sync::OnceLock<std::sync::atomic::AtomicI64> = std::sync::OnceLock::new();
    let left = LEFT.get_or_init(|| {
        std::sync::atomic::AtomicI64::new(tlx_base::knobs::Env::process().num("TLX_BAILOUT_DEBUG").map_or(0, |n| n as i64))
    });
    if left.fetch_sub(1, Ordering::Relaxed) > 0 {
        tlx_base::diag::emit(tlx_base::diag::Topic::Bailout, format_args!("{what}: {}", e.message));
    }
}

impl Drop for EncModel {
    fn drop(&mut self) {
        stats::freeze_json(&format!("native_regions_{}", self.id));
        // A model the driver discards for a widening restart
        // (`restartable`) never searches again: its layout is replaced, so
        // the C library being built for it could never be loaded, and the
        // compilation must not keep running beside the search (one large
        // translation unit per attempt).
        if self.restartable {
            if let Some(n) = self.native.as_deref() {
                n.cancel_builds();
            }
            return;
        }
        // The run ended and nothing restarts (`restartable`; a model dropped
        // for a widening restart keeps it set): start the C build if this run
        // was too short for the delayed one (see `Native::at_exit_build`).
        if let Some(n) = self.native.as_deref() {
            n.at_exit_build();
        }
    }
}

/// Whether a predicate (its body guarding `Stop`) is evaluated in the IR
/// executor before the interpreter when it is not native: one without
/// side-effecting or nondeterministic builtins, and no interpreter
/// fallbacks (it is then cheaper than the interpreter).
fn pred_exec_ok(body: &Stmt, lw: &Lowerer) -> bool {
    crate::coverage::Coverage::of_stmt(body).interp == 0 && !lw.stmt_volatile(body)
}

fn live_bits(n: usize, mut f: impl FnMut(usize) -> Result<bool, ModelError>) -> Result<Vec<u64>, ModelError> {
    let mut out = vec![0u64; n.div_ceil(64)];
    for i in 0..n {
        if f(i)? {
            out[i / 64] |= 1 << (i % 64);
        }
    }
    Ok(out)
}

#[cfg(test)]
mod census_tests {
    use super::*;
    use tlx_runtime::stats::Path;

    #[test]
    fn census_counts_constraints_and_live_atoms_as_predicate_evaluations() {
        let base = tlx_testkit::spec::load(
            "---- MODULE CensusPredicates ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = (x + 1) % 3\nC == x < 3\nAC == x' < 3\nP == []<>(x = 1)\nAP == []<>(<<x' = 2>>_x)\n====\n",
            "INIT Init\nNEXT Next\nCONSTRAINT C\nACTION_CONSTRAINT AC\nPROPERTY P AP\n",
        );
        let settings = crate::settings::Settings::from_lookup(|key| (key == "TLX_NO_NATIVE").then(|| "1".into())).unwrap();
        let m = EncModel::new(
            Arc::new(base),
            Arc::new(tlx_layout::Layout::new(vec![tlx_layout::Shape::Int { lo: 0, hi: 2 }])),
            vec![],
            &settings,
        );
        let s = m.encode(&VState::new(vec![Value::Int(0)].into(), 1, 0)).unwrap();
        let t = m.encode(&VState::new(vec![Value::Int(1)].into(), 2, 0)).unwrap();
        stats::enable(1);
        let unit = stats::begin_unit(1);
        assert!(m.constraints_hold(&s).unwrap());
        assert!(m.action_constraints_hold(&s, &t).unwrap());
        assert!(!m.live_state.is_empty());
        m.live_state_bits(&s, &[]).unwrap();
        m.live_action_bits(&s, &t, None).unwrap();
        let mut buf = Vec::new();
        assert!(matches!(m.compiled_successors(&s, 0, false, &mut buf), Some(Path::Ir)));
        stats::end_unit(unit);
        m.report_native_regions();
        let json = stats::json();
        for name in ["constraint_0", "action_constraint_0", "live_state_0", "live_action_0"] {
            let marker = format!("\"name\":\"{name}\"");
            let row = json.split(&marker).nth(1).expect("named predicate tally").split("\"name\"").next().unwrap();
            assert!(row.contains("\"ir\":1"), "{name}: {row}");
        }
    }
}
