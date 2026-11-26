//! `EncModel`: the runtime `Model` over encoded states.
//!
//! Every action, invariant and action property runs natively if possible,
//! else as lowered IR (actions and Init), else in the interpreter. Native
//! and IR runs are speculative: on any failure the interpreter re-runs the
//! same (state, action) pair or predicate and has the last word.
//!
//! Mixed-mode native code calls back into the host for its regions
//! (`HostRegions`), with a per-worker `MixedCx` (`MIXED`).

use std::cell::{Cell, RefCell};
use std::ffi::c_int;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Arc, Mutex, OnceLock};
use std::time::Instant;

use tlx_eval::model::liveness::StateAtom;
use tlx_eval::model::State as VState;
use tlx_eval::{FpMode, InterpModel};
use tlx_layout::{Layout, Shape};
use tlx_native::mixed::MixedCx;
use tlx_native::native::{Mixed, NativeLib, OK};
use tlx_runtime::stats::{self, Path};
use tlx_runtime::{ErrorKind, GcEvent, Model, ModelError, StoreGcRetry};
use tlx_sema::hir::DefId;
use tlx_value::Value;

mod checks;
mod codec;
#[cfg(test)]
mod escape_tests;
mod fingerprint;
mod liveness;
mod symmetry;
mod view;
mod view_shape;

use super::adapt::{self, Choice, ACTION, STATE_PRED, TRANS_PRED};
use super::mixed::{FastRegions, HostRegions};
use super::native::{self, Native, NativeHandle};
use crate::cgen::UNSUPPORTED;
use crate::exec::fast;
use crate::exec::memo::MemoScope;
use crate::ir::{ActionFn, PredFn, Stmt};
use crate::lower::Lowerer;
use crate::paranoid::mismatch;
use crate::settings::{Inject, InjectKind, Settings};
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

    // ------------------------------------------------------------------
    // testing: deliberate mismatches

    /// Whether the current eligible result (of an injection of one of
    /// `kinds`) is the one to corrupt.
    fn inject_now(&self, kinds: &[InjectKind]) -> Option<InjectKind> {
        let j = self.inject.filter(|j| kinds.contains(&j.kind))?;
        (self.inject_seen.fetch_add(1, Ordering::Relaxed) == j.after).then_some(j.kind)
    }

    /// Corrupt the compiled successors `buf` of `s` (if it is their turn).
    #[cold]
    fn inject_successors(&self, s: &EState, buf: &mut Vec<Box<[u64]>>) {
        if buf.is_empty() {
            return;
        }
        match self.inject_now(&[InjectKind::Drop, InjectKind::Dup, InjectKind::Stale]) {
            Some(InjectKind::Drop) => {
                buf.pop();
            }
            Some(InjectKind::Dup) => buf.push(buf[buf.len() - 1].clone()),
            Some(InjectKind::Stale) => *buf.last_mut().unwrap() = s.words.clone(),
            _ => {}
        }
    }

    // ------------------------------------------------------------------
    // native functions

    fn native_lib(&self, has: impl FnOnce(&Native) -> bool) -> Option<&NativeLib> {
        self.native.as_deref().filter(|n| has(n)).and_then(|n| n.lib())
    }

    /// Run `f` with the mixed-mode side of a call of the native library at
    /// level `level`: this worker's `MixedCx` and the library's regions.
    /// `func`: the function called (`adapt` kind and index), whose region
    /// evaluations the statistics count.
    fn mixed<R>(&self, level: u32, func: Option<(usize, usize)>, f: impl FnOnce(Mixed<'_>) -> R) -> R {
        let table = self.native.as_deref().and_then(|n| n.regions.as_ref()).expect("a library with regions");
        let fast = Some(FastRegions { prog: &self.fast.prog, progs: &self.fast_regions });
        let regions = HostRegions { ip: &self.base.ip, typing: &self.typing, table, memo: self.memo.exec_id(), fast };
        let gc_gen = self.store_gc_gen();
        MIXED.with(|m| match m.try_borrow_mut() {
            Ok(mut m) => {
                let (id, gen, cx) = &mut *m;
                // The decoded-state cache holds states of this model's layout
                // (and pre-GC handles become stale after a value-store sweep).
                if *id != self.id || *gen != gc_gen {
                    *id = self.id;
                    *gen = gc_gen;
                    cx.cache.clear();
                }
                let r = f(Mixed { cx: &mut *cx, regions: &regions, level });
                if stats::on() {
                    let (evals, errors) = table.drain_counts();
                    if let Some((kind, i)) = func {
                        stats::regions(kind, i, evals, errors);
                    }
                }
                r
            }
            // (Not expected: a native call within a native call.)
            Err(_) => f(Mixed { cx: &mut MixedCx::new(), regions: &regions, level }),
        })
    }

    /// `NativeLib::init_into`, with the library's regions if it has some.
    fn lib_init(&self, lib: &NativeLib, buf: &mut Vec<Box<[u64]>>) -> c_int {
        if lib.n_regions() == 0 {
            return lib.init_into(buf);
        }
        self.mixed(0, None, |m| lib.init_mixed(m, buf))
    }

    /// `NativeLib::next_into` on `s`, with the library's regions if any.
    /// (Inlined: see `compiled_successors`.)
    #[inline(always)]
    fn lib_next(&self, lib: &NativeLib, s: &EState, i: usize, buf: &mut Vec<Box<[u64]>>) -> c_int {
        if lib.n_regions() == 0 {
            return lib.next_into(&s.words, i as u32, buf);
        }
        self.mixed(s.level, Some((ACTION, i)), |m| lib.next_mixed(m, &s.words, i as u32, buf))
    }

    /// `NativeLib::invariant_raw` (also constraints and liveness state
    /// atoms) on `s` at level `level`, with the library's regions if any.
    fn lib_inv(&self, lib: &NativeLib, s: &EState, i: usize, level: u32) -> c_int {
        if lib.n_regions() == 0 {
            return lib.invariant_raw(&s.words, i as u32);
        }
        self.mixed(level, Some((STATE_PRED, i)), |m| lib.invariant_mixed(m, &s.words, i as u32))
    }

    /// `NativeLib::action_property_raw` (also action constraints and
    /// liveness action atoms) on `s -> t` at level `level`, with the
    /// library's regions if any.
    fn lib_aprop(&self, lib: &NativeLib, s: &EState, t: &EState, i: usize, level: u32) -> c_int {
        if lib.n_regions() == 0 {
            return lib.action_property_raw(&s.words, &t.words, i as u32);
        }
        self.mixed(level, Some((TRANS_PRED, i)), |m| lib.action_property_mixed(m, &s.words, &t.words, i as u32))
    }

    /// Whether function `i` of `kind` (`adapt::ACTION`, ...) is native and
    /// calls host regions.
    fn is_mixed(&self, kind: usize, i: usize) -> bool {
        self.native.as_deref().is_some_and(|n| {
            let v = match kind {
                ACTION => &n.has.mixed_actions,
                STATE_PRED => &n.has.mixed_invariants,
                _ => &n.has.mixed_action_properties,
            };
            v.get(i).copied().unwrap_or(false)
        })
    }

    /// How to run function `i` of `kind` now: natively (if it is), or, for
    /// a mixed function whose fallback is faster (`adapt`), by its
    /// fallback.
    #[inline]
    fn choose(&self, kind: usize, i: usize) -> Choice {
        if self.adapt && self.is_mixed(kind, i) {
            if let Some(lib) = self.lib_id() {
                let warm = if self.memo.exec_id() != 0 { adapt::WARM } else { 0 };
                let choice = adapt::choose(self.id, lib, kind, i, warm);
                self.report_adaptive(kind, i);
                return choice;
            }
        }
        Choice { native: true, timed: false }
    }

    /// Catch accidental cross-model state use in debug builds. Release keeps
    /// the state/codec representation unchanged (see docs/unsafe-audit.md).
    #[inline]
    fn check_state_model(&self, s: &EState) {
        #[cfg(debug_assertions)]
        assert_eq!(s.model, self.id, "EState belongs to another EncModel");
        #[cfg(not(debug_assertions))]
        let _ = s;
    }

    /// The identity of the native library in use (it changes when the C
    /// library replaces the JIT one).
    fn lib_id(&self) -> Option<usize> {
        self.native.as_deref().and_then(|n| n.lib_slot())
    }

    /// A timed call (`Choice::timed`) of function `i` of `kind` started at
    /// `t0`, of which `excluded` nanoseconds were spent outside it.
    fn record(&self, kind: usize, i: usize, c: Choice, t0: Instant, excluded: u64) {
        let ns = (t0.elapsed().as_nanos() as u64).saturating_sub(excluded);
        adapt::record(self.id, self.lib_id().unwrap_or(0), kind, i, c.native, ns);
        self.report_adaptive(kind, i);
    }

    fn report_adaptive(&self, kind: usize, i: usize) {
        if stats::on() {
            let name = match kind {
                ACTION => self.base.action_names()[i].as_str(),
                STATE_PRED => self.invariants[i].name.as_ref(),
                _ => self.aprops[i].name.as_ref(),
            };
            adapt::report(self.id, kind, i, name);
        }
    }

    /// The statistics path of a native call of function `i` of `kind`.
    fn native_path(&self, kind: usize, i: usize) -> Path {
        if self.is_mixed(kind, i) {
            Path::Mixed
        } else {
            Path::Native
        }
    }

    /// Name predicates at native indices, including constraints and escaped
    /// layouts. Each layout's registered region source is frozen on retirement.
    pub(super) fn report_native_regions(&self) {
        // Search starts install the public property names. Extend them after
        // the run to name constraint tallies at their native predicate indices.
        stats::set_names(
            self.base.action_names(),
            &self.invariants.iter().map(|p| p.name.to_string()).collect::<Vec<_>>(),
            &self.aprops.iter().map(|p| p.name.to_string()).collect::<Vec<_>>(),
        );
        if !stats::on() {
            return;
        }
        if let Some(e) = &self.escape {
            for m in e.models() {
                m.report_native_regions();
            }
        }
    }

    /// `-stats`: the memo tables' hit rates and the host regions that took
    /// the most time, as report sections.
    pub(super) fn report_stats(&self) {
        self.memo.report_stats();
        if let Some(e) = &self.escape {
            e.report();
            let vars: Vec<&str> = self.base.ip.prog.vars.iter().map(|v| &*v.name).collect();
            for (i, version) in e.models().iter().enumerate() {
                if let Some(t) = version.native.as_deref().and_then(|n| n.regions.as_ref()) {
                    stats::set_section(
                        &format!("escape version {i} mixed-mode regions by time (all workers; memo hits included)"),
                        t.report(&vars),
                    );
                    stats::set_section(
                        &format!("escape version {i} mixed-mode region evaluations by state variable read"),
                        t.report_by_var(&vars),
                    );
                }
            }
        }
        if let Some(t) = self.native.as_deref().and_then(|n| n.regions.as_ref()).filter(|_| stats::on()) {
            let vars: Vec<&str> = self.base.ip.prog.vars.iter().map(|v| &*v.name).collect();
            let text = t.report(&vars);
            if !text.is_empty() {
                stats::set_section("mixed-mode regions by time (all workers; memo hits included)", text);
                stats::set_section("mixed-mode region evaluations by state variable read", t.report_by_var(&vars));
            }
        }
        if let Some(t) = self.native.as_deref().and_then(|n| n.refops()).filter(|_| stats::on()) {
            let text = t.report();
            if !text.is_empty() {
                stats::set_section("value store operations called by native code", text);
            }
        }
    }

    /// Native build events since the last call, and whether a build is
    /// still running.
    pub(super) fn native_events(&self) -> (Vec<String>, bool) {
        self.native.as_ref().map_or((Vec::new(), false), |n| n.take_events())
    }

    /// Interpret a native predicate's return code: Some(whether it holds),
    /// or None to evaluate it with the interpreter instead (unsupported, or
    /// a runtime error, which the interpreter reports exactly).
    fn native_verdict(&self, rc: c_int, states: &[&EState]) -> Result<Option<bool>, ModelError> {
        match rc {
            1 => Ok(Some(true)),
            0 => Ok(Some(false)),
            UNSUPPORTED => Ok(None),
            _ => {
                // (After the search a miss widens nothing: the interpreter
                // decides, see `restartable`.)
                if self.restartable && self.escape.is_none() && !self.def_shapes.is_empty() {
                    self.check_def_fit(states)?;
                }
                Ok(None)
            }
        }
    }

    /// After a native predicate error: if a materialized definition's value
    /// does not fit its shape, record the miss (the run restarts widened).
    fn check_def_fit(&self, states: &[&EState]) -> Result<(), ModelError> {
        for s in states {
            // SAFETY: the matching encoder/program produced these words.
            // Active Dyn handles were published before this call.
            let vals = unsafe { self.layout.decode_state_unchecked(&s.words) };
            for (i, (d, shape)) in self.def_shapes.iter().enumerate() {
                if let Ok(v) = self.base.ip.eval_def_in_state(*d, &vals) {
                    if !shape.contains(&v) {
                        return Err(Self::record_miss(&self.def_miss, i, v));
                    }
                }
            }
        }
        Ok(())
    }

    // ------------------------------------------------------------------
    // Init and actions

    /// Run Init natively or as IR into `buf`. False if it is not compiled
    /// or failed (then `buf` is meaningless).
    fn compiled_init(&self, buf: &mut Vec<Box<[u64]>>) -> bool {
        if let Some(lib) = self.native_lib(|n| n.has.init) {
            return self.lib_init(lib, buf) == OK;
        }
        if !self.init_exec_ok {
            return false;
        }
        let Some((prog, action)) = self.fast.init.as_ref().map(|action| (&self.fast.prog, action)) else { return false };
        // A large Init run as IR while the native library is being built:
        // switch to native Init as soon as it is ready.
        let pending = self.native.as_ref().is_some_and(|n| n.has.init);
        let mut switch = false;
        let mut emit = |w: &[u64]| {
            buf.push(w.into());
            if pending && buf.len().is_multiple_of(1024) && self.native_lib(|n| n.has.init).is_some() {
                switch = true;
                return Ok(false);
            }
            Ok(true)
        };
        let ok = fast::run_init_words(&fast::Run::words(&self.base.ip, &self.typing, prog, 0), action, &mut emit).is_ok();
        if switch {
            buf.clear();
            return self.compiled_init(buf);
        }
        ok
    }

    /// Interpreted Init (exact semantics, including error reporting).
    fn interpreted_init(&self, out: &mut dyn FnMut(EState)) -> Result<(), ModelError> {
        let mut err = None;
        self.base.init_states(&mut |v| {
            if err.is_none() {
                match self.encode(&v) {
                    Ok(e) => out(e),
                    Err(e) => err = Some(e),
                }
            }
        })?;
        err.map_or(Ok(()), Err)
    }

    /// Interpreted Init with in-place value-store GC retry per initial state so
    /// interpreter side effects run once and generation stops immediately if
    /// `sink` returns false.
    fn interpreted_init_gc(&self, sink: &mut dyn FnMut(GcEvent<EState>) -> bool) -> Result<(), ModelError> {
        let has_store = self.value_store().is_some();
        let mut err = None;
        self.base.init_states_while(&mut |v| match self.encode_gc(&v, has_store, sink) {
            Ok(Some(e)) => sink(GcEvent::Emit(e, 0)),
            Ok(None) => false,
            Err(e) => {
                err = Some(e);
                false
            }
        })?;
        err.map_or(Ok(()), Err)
    }

    /// `compiled_successors` of an action that may print: its output is held
    /// back in the returned vector instead of released immediately, so a
    /// `StoreFull` retry or interpreter fallback discards it cleanly and
    /// committed output is released exactly once.
    #[inline(never)]
    fn compiled_successors_printing_hold(
        &self,
        s: &EState,
        i: usize,
        native: bool,
        buf: &mut Vec<Box<[u64]>>,
    ) -> (Option<Path>, Vec<String>) {
        let mark = tlx_eval::Interp::hold_begin();
        let ok = self.compiled_successors(s, i, native, buf);
        let lines = tlx_eval::Interp::hold_end(mark);
        if ok.is_some() {
            if self.paranoid {
                self.cross_check_output(s, i, &lines);
            }
            (ok, lines)
        } else {
            (None, Vec::new())
        }
    }

    /// Paranoid: the lines a compiled run of action `i` on `s` printed
    /// (`printed`) are the interpreter's (as multisets).
    fn cross_check_output(&self, s: &EState, i: usize, printed: &[String]) {
        let vs = self.decode_current(s);
        let (_, mut want) =
            tlx_eval::Interp::hold_output(|| self.base.ip.without_effects(|| self.base.successor_values_of(&vs, i, &mut |_| {})));
        let mut got = printed.to_vec();
        want.sort();
        got.sort();
        if want != got {
            let what = format!("action {} on state\n{}", self.base.action_names()[i], self.base.render(&vs));
            mismatch(format_args!("{what}\nthe interpreter prints {want:?} but compiled code printed {got:?}"));
        }
    }

    /// Run action `i` on `s` natively (if `native`) or as IR into `buf`.
    /// The actual path on success, None if it is not compiled or failed.
    /// (Inlined into `run_action`: called once per action and state, a call
    /// costs about 3% of a search with cheap actions.)
    #[inline(always)]
    fn compiled_successors(&self, s: &EState, i: usize, native: bool, buf: &mut Vec<Box<[u64]>>) -> Option<Path> {
        if self.escaped(s) {
            return None;
        }
        if let Some(lib) = self.native_lib(|n| native && n.has.actions[i]) {
            return (self.lib_next(lib, s, i, buf) == OK).then(|| self.native_path(ACTION, i));
        }
        let Some(f) = &self.actions[i] else { return None };
        if !self.exec_ok[i] {
            return None;
        }
        let decode = |w: &[u64]| self.cached_values(w, true);
        if let Some((prog, a)) = self.fast.actions[i].as_ref().map(|a| (&self.fast.prog, a)) {
            let mut emit = |w: &[u64]| {
                buf.push(w.into());
                Ok(true)
            };
            let run = fast::Run::words(&self.base.ip, &self.typing, prog, s.level).with_decoder(&decode).with_memo(self.memo.exec_id());
            // SAFETY: the matching encoder/program produced these words.
            // Active Dyn handles were published before this call.
            let r = unsafe { fast::run_action_words(&run, a, &s.words, &mut emit) };
            if let Err(e) = &r {
                bailout_debug(&format!("action {}", f.name), e);
            }
            return r.is_ok().then_some(Path::Ir);
        }
        None
    }

    /// The verdict of state predicate `idx` (of `invariants`) on `s` at
    /// level `level` from the IR executor (`pred_exec_ok`); None if it does
    /// not run there or fails (the interpreter then evaluates it).
    fn ir_predicate(&self, s: &EState, idx: usize, level: u32) -> Option<bool> {
        if self.escaped(s) {
            return None;
        }
        if !self.pred_exec_ok[idx] {
            return None;
        }
        let p = &self.invariants[idx];
        let decode = |w: &[u64]| self.cached_values(w, false);
        if let Some((prog, fp)) = self.fast.preds[idx].as_ref().map(|q| (&self.fast.prog, q)) {
            let run = fast::Run::words(&self.base.ip, &self.typing, prog, level).with_decoder(&decode).with_memo(self.memo.exec_id());
            // SAFETY: the matching encoder/program produced these words.
            // Active Dyn handles were published before this call.
            return match unsafe { fast::eval_pred_words(&run, fp, &s.words) } {
                Ok(b) => Some(b),
                Err(e) => {
                    bailout_debug(&format!("predicate {}", p.name), &e);
                    None
                }
            };
        }
        None
    }

    // ------------------------------------------------------------------
    // predicates: one ladder (`predicate`) for the invariants, CONSTRAINTs,
    // ACTION_CONSTRAINTs, action properties and liveness atoms

    /// Evaluate compiled predicate `p`: natively (unless the adaptive
    /// tiering runs the fallback, see `choose`), else by `steps` (a
    /// liveness action atom decided by a change of its subscript; `|| None`
    /// elsewhere), else in the IR executor (`ir_predicate`,
    /// `ir_trans_predicate`), else by `interp`, the interpreter, which has
    /// the last word (also on a native error: see `native_verdict`). With
    /// TLX_PARANOID every verdict not from `interp` is checked against it;
    /// `what(note)` describes the predicate and its states in a mismatch
    /// (`note`: how `steps` decided, else empty). Also the path taken (for
    /// the statistics).
    #[inline]
    fn predicate(
        &self,
        p: PredAt<'_>,
        steps: impl FnOnce() -> Option<bool>,
        interp: impl Fn() -> Result<bool, ModelError>,
        what: impl Fn(&str) -> String,
    ) -> Result<(bool, Path), ModelError> {
        let kind = if p.t.is_some() { TRANS_PRED } else { STATE_PRED };
        let c = self.choose(kind, p.idx);
        let t0 = c.timed.then(Instant::now);
        let r = self.predicate_untimed(p, kind, c.native, steps, &interp, &what);
        if let Some(t0) = t0 {
            self.record(kind, p.idx, c, t0, 0);
        }
        r
    }

    /// GC-aware `predicate`: runs the fast path once, and only on `StoreFull`
    /// enters the cold per-predicate retry loop via `collect(force_drop_archive)`
    /// (falling back to the interpreter on retry 3) without replaying earlier
    /// predicates in the same check list.
    #[inline]
    fn predicate_gc(
        &self,
        p: PredAt<'_>,
        steps: impl Fn() -> Option<bool>,
        interp: impl Fn() -> Result<bool, ModelError>,
        what: impl Fn(&str) -> String,
        collect: &mut dyn FnMut(bool) -> bool,
    ) -> Result<(bool, Path), ModelError> {
        match self.predicate(p, &steps, &interp, &what) {
            Err(e) if e.is_store_full() => self.retry_predicate_gc(p, &steps, &interp, &what, collect, e),
            other => other,
        }
    }

    #[cold]
    #[inline(never)]
    fn retry_predicate_gc(
        &self,
        p: PredAt<'_>,
        steps: &impl Fn() -> Option<bool>,
        interp: &impl Fn() -> Result<bool, ModelError>,
        what: &impl Fn(&str) -> String,
        collect: &mut dyn FnMut(bool) -> bool,
        first_err: ModelError,
    ) -> Result<(bool, Path), ModelError> {
        let mut last = first_err;
        for stage in StoreGcRetry::STAGES {
            if !collect(stage.force_drop_archive) {
                return Err(last);
            }
            let _fb = stage.transient_fallback.then(TransientFallbackScope::enter);
            match self.predicate(p, steps, interp, what) {
                Err(e) if e.is_store_full() => last = e,
                other => return other,
            }
        }
        Err(last)
    }

    /// `predicate` without the adaptive tiering's timing (natively only if
    /// `native`).
    #[inline]
    fn predicate_untimed(
        &self,
        p: PredAt<'_>,
        kind: usize,
        native: bool,
        steps: impl FnOnce() -> Option<bool>,
        interp: &impl Fn() -> Result<bool, ModelError>,
        what: &impl Fn(&str) -> String,
    ) -> Result<(bool, Path), ModelError> {
        let checked = |b: bool, note: &str| {
            if self.paranoid {
                self.check_verdict(b, interp(), || what(note));
            }
            b
        };
        let has_store = self.value_store().is_some();
        let skip_compiled = has_store && Self::transient_fallback();
        let mut path = Path::Interp;
        if !skip_compiled {
            let native = native && !self.escaped(p.s) && !p.t.is_some_and(|t| self.escaped(t));
            let has = |n: &Native| native && if p.t.is_some() { n.has.action_properties[p.idx] } else { n.has.invariants[p.idx] };
            if let Some(lib) = self.native_lib(has) {
                if has_store {
                    tlx_layout::store::clear_full_hit();
                }
                let mut rc = match p.t {
                    None => self.lib_inv(lib, p.s, p.idx, p.level),
                    Some(t) => self.lib_aprop(lib, p.s, t, p.idx, p.level),
                };
                if p.inject && self.inject.is_some() && (rc == 0 || rc == 1) && self.inject_now(&[InjectKind::Inv]).is_some() {
                    rc = 1 - rc;
                }
                let verdict = match p.t {
                    None => self.native_verdict(rc, &[p.s])?,
                    Some(t) => self.native_verdict(rc, &[p.s, t])?,
                };
                match verdict {
                    Some(b) => return Ok((checked(b, ""), self.native_path(kind, p.idx))),
                    None => {
                        if has_store && tlx_layout::store::take_full_hit() {
                            return Err(self.store_full_error());
                        }
                        path = Path::Fallback;
                    }
                }
            }
        } else {
            path = Path::Fallback;
        }
        if let Some(b) = steps() {
            return Ok((checked(b, " (as a change of its subscript)"), Path::Interp));
        }
        if !skip_compiled {
            if has_store {
                tlx_layout::store::clear_full_hit();
            }
            let ir = match p.t {
                None => self.ir_predicate(p.s, p.idx, p.level),
                Some(t) => self.ir_trans_predicate(p.s, t, p.idx, p.level),
            };
            if let Some(b) = ir {
                return Ok((checked(b, ""), Path::Ir));
            }
            if has_store && tlx_layout::store::take_full_hit() {
                return Err(self.store_full_error());
            }
        }
        Ok((interp()?, path))
    }

    /// The verdict of transition predicate `idx` (of `aprops`) on the step
    /// `s` -> `t` at level `level` from the closure-compiled executor
    /// (`aprop_exec_ok`); None if it does not run there or fails.
    fn ir_trans_predicate(&self, s: &EState, t: &EState, idx: usize, level: u32) -> Option<bool> {
        if self.escaped(s) || self.escaped(t) {
            return None;
        }
        if !self.aprop_exec_ok[idx] {
            return None;
        }
        let (prog, fp) = self.fast.aprops[idx].as_ref().map(|q| (&self.fast.prog, q))?;
        let decode = |w: &[u64]| self.cached_values(w, true);
        let run = fast::Run::words(&self.base.ip, &self.typing, prog, level).with_decoder(&decode).with_memo(self.memo.exec_id());
        // SAFETY: the matching encoder/program produced these words.
        // Active Dyn handles were published before this call.
        match unsafe { fast::eval_trans_words(&run, fp, &s.words, &t.words) } {
            Ok(b) => Some(b),
            Err(e) => {
                bailout_debug(&format!("action property {}", self.aprops[idx].name), &e);
                None
            }
        }
    }

    /// How `compiled_successors` runs action `i` (None: not compiled).
    fn compiled_path(&self, i: usize, native: bool) -> Option<Path> {
        if self.native_lib(|n| native && n.has.actions[i]).is_some() {
            Some(self.native_path(ACTION, i))
        } else {
            (self.actions[i].is_some() && self.exec_ok[i]).then_some(Path::Ir)
        }
    }

    /// Successors of `s` by action `i` to `out`: compiled (natively if
    /// `native`) into a buffer, or on any error, by the interpreter for
    /// this pair. False if exploration is to stop; also the path taken
    /// (for the statistics).
    fn run_action(&self, s: &EState, i: usize, native: bool, out: &mut dyn FnMut(EState, u32) -> bool) -> (Result<bool, ModelError>, Path) {
        let mut buf = Vec::new();
        tlx_eval::Interp::begin_random_scope();
        if let Some(e) = &self.escape {
            // Output is held transactionally by compiled_successors_printing_hold.
            // Other effects only have a whole-search journal, not an action
            // transaction, so they must run in the interpreter exactly once.
            if e.irreversible_actions[i] {
                return (self.interpreted_successors(s, i, out), Path::Interp);
            }
            if self.escaped(s) {
                e.guards.add(1);
                if let Some(r) = self.escape_action(s, i, out) {
                    return (r, Path::Fallback);
                }
                e.deopts.add(1);
                return (self.interpreted_successors(s, i, out), Path::Fallback);
            }
        }
        let has_store = self.value_store().is_some();
        if has_store {
            tlx_layout::store::clear_full_hit();
        }
        let (ok, pending_lines) = if self.prints[i] {
            self.compiled_successors_printing_hold(s, i, native, &mut buf)
        } else {
            (self.compiled_successors(s, i, native, &mut buf), Vec::new())
        };
        if let Some(path) = ok {
            if self.inject.is_some() {
                // Test hook: a miss where nothing restarts.
                if !self.restartable && self.inject_now(&[InjectKind::Miss]).is_some() {
                    return (Err(ModelError::of_kind(ErrorKind::LayoutMiss, MISS_MSG)), Path::Native);
                }
                self.inject_successors(s, &mut buf);
            }
            if self.paranoid {
                if let Err(e) = self.cross_check(s, i, &buf) {
                    return (Err(e), path);
                }
            }
            if !pending_lines.is_empty() {
                self.base.ip.release_output(pending_lines);
            }
            let r = self.emit_compiled(buf, s, i, out);
            (r, path)
        } else {
            let compiled = self.compiled_path(i, native).is_some();
            if has_store && tlx_layout::store::take_full_hit() {
                let path = self.compiled_path(i, native).unwrap_or(Path::Ir);
                return (Err(self.store_full_error()), path);
            }
            if let Some(e) = self.escape.as_ref().filter(|_| compiled) {
                e.guards.add(1);
                e.deopts.add(1);
                if let Some(r) = self.escape_action(s, i, out) {
                    return (r, Path::Fallback);
                }
            }
            // (Not counting runs the adaptive tiering gave the interpreter.)
            if self.actions[i].is_some() && (native || compiled) {
                self.bailouts.add(1);
            }
            let path = if compiled { Path::Fallback } else { Path::Interp };
            (self.interpreted_successors(s, i, out), path)
        }
    }

    /// GC-aware `run_action`: retries compiled action generation across
    /// `GcEvent::Collect` (dropping the archive on retry 2 and falling back to
    /// the interpreter on retry 3 so transient compiled intermediates cannot
    /// starve a small store), releases captured `PrintT` output once the
    /// compiled batch is committed, and finishes/delivers states strictly one
    /// at a time in order so first-failure order is preserved across retries.
    fn run_action_gc(
        &self,
        s: &EState,
        i: usize,
        native: bool,
        sink: &mut dyn FnMut(GcEvent<EState>) -> bool,
    ) -> (Result<bool, ModelError>, Path) {
        tlx_eval::Interp::begin_random_scope();
        if let Some(e) = &self.escape {
            if e.irreversible_actions[i] {
                return (self.interpreted_successors_gc(s, i, sink), Path::Interp);
            }
            if self.escaped(s) {
                e.guards.add(1);
                if let Some(r) = self.escape_action(s, i, &mut |t, a| sink(GcEvent::Emit(t, a))) {
                    return (r, Path::Fallback);
                }
                e.deopts.add(1);
                return (self.interpreted_successors_gc(s, i, sink), Path::Fallback);
            }
        }
        let has_store = self.value_store().is_some();
        let mut buf = Vec::new();
        let mut tries = 0usize;
        let (ok, pending_lines) = loop {
            buf.clear();
            if has_store {
                tlx_layout::store::clear_full_hit();
            }
            let (ok, lines) = if self.prints[i] {
                self.compiled_successors_printing_hold(s, i, native, &mut buf)
            } else {
                (self.compiled_successors(s, i, native, &mut buf), Vec::new())
            };
            if ok.is_some() {
                break (ok, lines);
            }
            if has_store && tlx_layout::store::take_full_hit() {
                if let Some(stage) = StoreGcRetry::COMPILED_STAGES.get(tries) {
                    tries += 1;
                    if !sink(GcEvent::Collect { force_drop_archive: stage.force_drop_archive }) {
                        return (Ok(false), self.compiled_path(i, native).unwrap_or(Path::Ir));
                    }
                    continue;
                }
                // Even archive-free GC could not hold this compiled action's
                // transient intermediates: sweep the aborted attempt and fall
                // back to the interpreter (which evaluates intermediates as
                // `Value` without interning discarded temporaries).
                if !sink(GcEvent::Collect { force_drop_archive: true }) {
                    return (Ok(false), Path::Fallback);
                }
                let compiled = self.compiled_path(i, native).is_some();
                if self.actions[i].is_some() && (native || compiled) {
                    self.bailouts.add(1);
                }
                return (self.interpreted_successors_gc(s, i, sink), Path::Fallback);
            }
            break (None, Vec::new());
        };
        if let Some(path) = ok {
            if self.inject.is_some() {
                if !self.restartable && self.inject_now(&[InjectKind::Miss]).is_some() {
                    return (Err(ModelError::of_kind(ErrorKind::LayoutMiss, MISS_MSG)), Path::Native);
                }
                self.inject_successors(s, &mut buf);
            }
            if self.paranoid {
                if let Err(e) = self.cross_check_gc(s, i, &mut buf, sink) {
                    return (Err(e), path);
                }
            }
            let r = self.emit_compiled_gc(buf, s.level + 1, i as u32, pending_lines, sink);
            (r, path)
        } else {
            let compiled = self.compiled_path(i, native).is_some();
            if let Some(e) = self.escape.as_ref().filter(|_| compiled) {
                e.guards.add(1);
                e.deopts.add(1);
                if let Some(r) = self.escape_action(s, i, &mut |t, a| sink(GcEvent::Emit(t, a))) {
                    return (r, Path::Fallback);
                }
            }
            if self.actions[i].is_some() && (native || compiled) {
                self.bailouts.add(1);
            }
            let path = if compiled { Path::Fallback } else { Path::Interp };
            (self.interpreted_successors_gc(s, i, sink), path)
        }
    }

    /// Paranoid cross-check for compiled successors while keeping `buf` rooted
    /// across any `StoreFull` GC retry triggered by `check_store_slots`.
    fn cross_check_gc(
        &self,
        s: &EState,
        i: usize,
        buf: &mut Vec<Box<[u64]>>,
        sink: &mut dyn FnMut(GcEvent<EState>) -> bool,
    ) -> Result<(), ModelError> {
        let mut last = match self.cross_check(s, i, buf) {
            Ok(()) => return Ok(()),
            Err(e) if e.is_store_full() => e,
            Err(e) => return Err(e),
        };
        for stage in StoreGcRetry::STAGES {
            let held = std::mem::take(buf);
            let guard = EmitGuard::push_words(self.id, held);
            let ok = sink(GcEvent::Collect { force_drop_archive: stage.force_drop_archive });
            *buf = guard.take_words();
            if !ok {
                return Err(last);
            }
            match self.cross_check(s, i, buf) {
                Ok(()) => return Ok(()),
                Err(e) if e.is_store_full() => last = e,
                Err(e) => return Err(e),
            }
        }
        Err(last)
    }

    /// Paranoid cross-check for compiled Init while keeping `buf` rooted
    /// across any `StoreFull` GC retry triggered by `check_store_slots`.
    fn cross_check_init_gc(&self, buf: &mut Vec<Box<[u64]>>, sink: &mut dyn FnMut(GcEvent<EState>) -> bool) -> Result<(), ModelError> {
        let mut last = match self.cross_check_init(buf) {
            Ok(()) => return Ok(()),
            Err(e) if e.is_store_full() => e,
            Err(e) => return Err(e),
        };
        for stage in StoreGcRetry::STAGES {
            let held = std::mem::take(buf);
            let guard = EmitGuard::push_words(self.id, held);
            let ok = sink(GcEvent::Collect { force_drop_archive: stage.force_drop_archive });
            *buf = guard.take_words();
            if !ok {
                return Err(last);
            }
            match self.cross_check_init(buf) {
                Ok(()) => return Ok(()),
                Err(e) if e.is_store_full() => last = e,
                Err(e) => return Err(e),
            }
        }
        Err(last)
    }

    /// Hand the compiled successors of `s` by action `i` to `out` strictly in
    /// order; false if exploration is to stop.
    fn emit_compiled(
        &self,
        mut buf: Vec<Box<[u64]>>,
        s: &EState,
        i: usize,
        out: &mut dyn FnMut(EState, u32) -> bool,
    ) -> Result<bool, ModelError> {
        if buf.is_empty() {
            return Ok(true);
        }
        if self.value_store().is_none() || buf.len() == 1 {
            for w in buf {
                let t = self.finish(w, s.level + 1)?;
                if !out(t, i as u32) {
                    return Ok(false);
                }
            }
            return Ok(true);
        }
        // Keep un-emitted words rooted in `PENDING_EMIT` while streaming one
        // state at a time in order so `out` sees the first failure before later
        // states' VIEW/SYMMETRY fingerprints are evaluated.
        buf.reverse();
        let guard = EmitGuard::push_words(self.id, buf);
        while let Some(w) = guard.pop_word() {
            let t = self.finish(w, s.level + 1)?;
            if !out(t, i as u32) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// GC-aware ordered emission of compiled successors: finishes and delivers
    /// states one at a time in order, retrying `finish` (VIEW/SYMMETRY) in
    /// place across `GcEvent::Collect` without re-running the action. Releases
    /// captured `PrintT` output once the first state's fingerprinting succeeds
    /// (or immediately if the batch is empty).
    fn emit_compiled_gc(
        &self,
        mut buf: Vec<Box<[u64]>>,
        level: u32,
        action: u32,
        pending_lines: Vec<String>,
        sink: &mut dyn FnMut(GcEvent<EState>) -> bool,
    ) -> Result<bool, ModelError> {
        if buf.is_empty() {
            if !pending_lines.is_empty() {
                self.base.ip.release_output(pending_lines);
            }
            return Ok(true);
        }
        // Fast path for the common 1-successor action: zero `PENDING_EMIT`
        // touches unless `finish_or_return` actually hits `StoreFull`.
        if buf.len() == 1 {
            let w = buf.pop().unwrap();
            match self.finish_or_return(w, level) {
                Ok(t) => {
                    if !pending_lines.is_empty() {
                        self.base.ip.release_output(pending_lines);
                    }
                    return Ok(sink(GcEvent::Emit(t, action)));
                }
                Err((w, e)) if e.is_store_full() => {
                    return self.emit_compiled_gc_slow(vec![w], level, action, pending_lines, sink, Some(e));
                }
                Err((_, e)) => {
                    if !pending_lines.is_empty() {
                        self.base.ip.release_output(pending_lines);
                    }
                    return Err(e);
                }
            }
        }
        buf.reverse();
        self.emit_compiled_gc_slow(buf, level, action, pending_lines, sink, None)
    }

    #[cold]
    #[inline(never)]
    fn emit_compiled_gc_slow(
        &self,
        buf_rev: Vec<Box<[u64]>>,
        level: u32,
        action: u32,
        mut pending_lines: Vec<String>,
        sink: &mut dyn FnMut(GcEvent<EState>) -> bool,
        mut first_full: Option<ModelError>,
    ) -> Result<bool, ModelError> {
        let guard = EmitGuard::push_words(self.id, buf_rev);
        while let Some(w) = guard.pop_word() {
            let initial = match first_full.take() {
                Some(e) => Err((w, e)),
                None => self.finish_or_return(w, level),
            };
            let t = match initial {
                Ok(t) => t,
                Err((mut w_cur, mut last)) if last.is_store_full() => {
                    let mut finished = None;
                    for stage in StoreGcRetry::STAGES {
                        guard.push_word(w_cur);
                        if !sink(GcEvent::Collect { force_drop_archive: stage.force_drop_archive }) {
                            return Ok(false);
                        }
                        w_cur = guard.pop_word().expect("re-pushed emit word");
                        let _fb = stage.transient_fallback.then(TransientFallbackScope::enter);
                        match self.finish_or_return(w_cur, level) {
                            Ok(t) => {
                                finished = Some(t);
                                break;
                            }
                            Err((w_next, e2)) if e2.is_store_full() => {
                                w_cur = w_next;
                                last = e2;
                            }
                            Err((_, e2)) => {
                                if !pending_lines.is_empty() {
                                    self.base.ip.release_output(pending_lines);
                                }
                                return Err(e2);
                            }
                        }
                    }
                    match finished {
                        Some(t) => t,
                        None => return Err(last),
                    }
                }
                Err((_, e)) => {
                    if !pending_lines.is_empty() {
                        self.base.ip.release_output(pending_lines);
                    }
                    return Err(e);
                }
            };
            if !pending_lines.is_empty() {
                self.base.ip.release_output(std::mem::take(&mut pending_lines));
            }
            if !sink(GcEvent::Emit(t, action)) {
                return Ok(false);
            }
        }
        Ok(true)
    }

    /// Encode one interpreter state `v`, retrying in place across
    /// `GcEvent::Collect` if `StoreFull` occurs without re-running the
    /// interpreter action. Returns `Ok(None)` if the search stopped during GC.
    fn encode_gc(&self, v: &VState, has_store: bool, sink: &mut dyn FnMut(GcEvent<EState>) -> bool) -> Result<Option<EState>, ModelError> {
        let mut last = match self.encode(v) {
            Ok(e) => return Ok(Some(e)),
            Err(e) if has_store && e.is_store_full() => e,
            Err(e) => return Err(e),
        };
        for stage in StoreGcRetry::STAGES {
            if !sink(GcEvent::Collect { force_drop_archive: stage.force_drop_archive }) {
                return Ok(None);
            }
            let _fb = stage.transient_fallback.then(TransientFallbackScope::enter);
            match self.encode(v) {
                Ok(e) => return Ok(Some(e)),
                Err(e) if e.is_store_full() => last = e,
                Err(e) => return Err(e),
            }
        }
        Err(last)
    }

    /// Successors of `s` by action `i` from the interpreter; false if
    /// exploration is to stop.
    fn interpreted_successors(&self, s: &EState, i: usize, out: &mut dyn FnMut(EState, u32) -> bool) -> Result<bool, ModelError> {
        let mut go_on = true;
        let mut err = None;
        self.base.successors_of(&self.decode_current(s), i, &mut |t, act| match self.encode(&t) {
            Ok(e) => {
                if self.escaped(&e) {
                    if let Some(escape) = &self.escape {
                        escape.observe(&t.vals);
                    }
                }
                let go = out(e, act);
                go_on &= go;
                go
            }
            Err(e) => {
                err = Some(e);
                go_on = false;
                false
            }
        })?;
        match err {
            Some(e) => Err(e),
            None => Ok(go_on),
        }
    }

    /// GC-aware interpreted successors: runs `base.successors_of` once and
    /// encodes/delivers each successor strictly in order with in-place GC
    /// retries, keeping interpreter effects (`Print`, `TLCSet`, files) exact
    /// and preserving first-failure order.
    fn interpreted_successors_gc(&self, s: &EState, i: usize, sink: &mut dyn FnMut(GcEvent<EState>) -> bool) -> Result<bool, ModelError> {
        let has_store = self.value_store().is_some();
        let mut go_on = true;
        let mut err = None;
        self.base.successors_of(&self.decode_current(s), i, &mut |t, act| match self.encode_gc(&t, has_store, sink) {
            Ok(Some(e)) => {
                if self.escaped(&e) {
                    if let Some(escape) = &self.escape {
                        escape.observe(&t.vals);
                    }
                }
                let go = sink(GcEvent::Emit(e, act));
                go_on &= go;
                go
            }
            Ok(None) => {
                go_on = false;
                false
            }
            Err(e) => {
                err = Some(e);
                go_on = false;
                false
            }
        })?;
        match err {
            Some(e) => Err(e),
            None => Ok(go_on),
        }
    }
}

impl Model for EncModel {
    type State = EState;

    fn uses_trace(&self) -> bool {
        self.base.uses_trace()
    }

    fn trace_replay_limit(&self) -> Option<&'static str> {
        self.base.trace_replay_limit()
    }

    fn state_values(&self, s: &EState) -> Option<Arc<[Value]>> {
        Some(self.values(s))
    }

    fn init_states(&self, out: &mut dyn FnMut(EState)) -> Result<(), ModelError> {
        let mut buf = Vec::new();
        let has_store = self.value_store().is_some();
        // (Random choices restart for each evaluation, as in the interpreter.)
        tlx_eval::Interp::begin_random_scope();
        if has_store {
            tlx_layout::store::clear_full_hit();
        }
        // (With -coverage, the interpreter counts what Init rejects.)
        if self.base.coverage || !self.compiled_init(&mut buf) {
            if !self.base.coverage && has_store && tlx_layout::store::take_full_hit() {
                return Err(self.store_full_error());
            }
            return self.interpreted_init(out);
        }
        if self.inject.is_some() && self.inject_now(&[InjectKind::Init]).is_some() {
            buf.pop();
        }
        if self.paranoid {
            self.cross_check_init(&buf)?;
        }
        if has_store {
            buf.reverse();
            let guard = EmitGuard::push_words(self.id, buf);
            while let Some(w) = guard.pop_word() {
                out(self.finish(w, 1)?);
            }
        } else {
            for w in buf {
                out(self.finish(w, 1)?);
            }
        }
        Ok(())
    }

    fn init_states_gc(&self, sink: &mut dyn FnMut(GcEvent<EState>) -> bool) -> Result<(), ModelError> {
        let has_store = self.value_store().is_some();
        tlx_eval::Interp::begin_random_scope();
        if self.base.coverage {
            return self.interpreted_init_gc(sink);
        }
        let mut buf = Vec::new();
        let mut tries = 0usize;
        let ok = loop {
            buf.clear();
            if has_store {
                tlx_layout::store::clear_full_hit();
            }
            if self.compiled_init(&mut buf) {
                break true;
            }
            if has_store && tlx_layout::store::take_full_hit() {
                if let Some(stage) = StoreGcRetry::COMPILED_STAGES.get(tries) {
                    tries += 1;
                    if !sink(GcEvent::Collect { force_drop_archive: stage.force_drop_archive }) {
                        return Ok(());
                    }
                    continue;
                }
                if !sink(GcEvent::Collect { force_drop_archive: true }) {
                    return Ok(());
                }
                return self.interpreted_init_gc(sink);
            }
            break false;
        };
        if !ok {
            return self.interpreted_init_gc(sink);
        }
        if self.inject.is_some() && self.inject_now(&[InjectKind::Init]).is_some() {
            buf.pop();
        }
        if self.paranoid {
            self.cross_check_init_gc(&mut buf, sink)?;
        }
        let _ = self.emit_compiled_gc(buf, 1, 0, Vec::new(), sink)?;
        Ok(())
    }

    fn successors(&self, s: &EState, out: &mut dyn FnMut(EState, u32) -> bool) -> Result<(), ModelError> {
        self.check_state_model(s);
        if self.base.symmetry_check_due() {
            self.base.check_symmetry_claim(&self.decode_current(s));
        }
        for i in 0..self.actions.len() {
            if !self.action_successors(s, i as u32, out)? {
                break;
            }
        }
        Ok(())
    }

    fn action_successors(&self, s: &EState, action: u32, out: &mut dyn FnMut(EState, u32) -> bool) -> Result<bool, ModelError> {
        self.check_state_model(s);
        if action == 0 && self.base.symmetry_check_due() {
            self.base.check_symmetry_claim(&self.decode_current(s));
        }
        let i = action as usize;
        // Generation mode (`-generate`): the random choices within actions
        // are the interpreter's (compiled actions enumerate every successor).
        let span = stats::span();
        if tlx_runtime::live::generating() {
            let r = self.interpreted_successors(s, i, out);
            span.action(i, Path::Interp);
            return r;
        }
        let c = self.choose(ACTION, i);
        if !c.timed {
            let (r, path) = self.run_action(s, i, c.native, out);
            span.action(i, path);
            return r;
        }
        // A timed call (adaptive tiering): without the time spent in `out`.
        let t0 = Instant::now();
        let mut excluded = 0u64;
        let mut timed_out = |t: EState, a: u32| {
            let t1 = Instant::now();
            let go = out(t, a);
            excluded += t1.elapsed().as_nanos() as u64;
            go
        };
        let (r, path) = self.run_action(s, i, c.native, &mut timed_out);
        self.record(ACTION, i, c, t0, excluded);
        span.action(i, path);
        r
    }

    fn action_successors_gc(&self, s: &EState, action: u32, sink: &mut dyn FnMut(GcEvent<EState>) -> bool) -> Result<bool, ModelError> {
        self.check_state_model(s);
        if action == 0 && self.base.symmetry_check_due() {
            self.base.check_symmetry_claim(&self.decode_current(s));
        }
        let i = action as usize;
        let span = stats::span();
        if tlx_runtime::live::generating() {
            let r = self.interpreted_successors_gc(s, i, sink);
            span.action(i, Path::Interp);
            return r;
        }
        let c = self.choose(ACTION, i);
        if !c.timed {
            let (r, path) = self.run_action_gc(s, i, c.native, sink);
            span.action(i, path);
            return r;
        }
        let t0 = Instant::now();
        let mut excluded = 0u64;
        let mut timed_sink = |ev: GcEvent<EState>| {
            let t1 = Instant::now();
            let go = sink(ev);
            excluded += t1.elapsed().as_nanos() as u64;
            go
        };
        let (r, path) = self.run_action_gc(s, i, c.native, &mut timed_sink);
        self.record(ACTION, i, c, t0, excluded);
        span.action(i, path);
        r
    }

    fn fingerprint(&self, s: &EState) -> u64 {
        self.check_state_model(s);
        s.fp
    }
    fn coarse_fingerprint(&self) -> bool {
        self.base.has_view_or_symmetry()
    }

    fn check_invariants(&self, s: &EState) -> Result<Option<usize>, ModelError> {
        self.check_state_model(s);
        // (Called on every state or step: nothing to do is cheap.)
        if self.base.invariant_names().is_empty() {
            return Ok(None);
        }
        self.invariants_violated(s)
    }

    fn check_invariants_gc(&self, s: &EState, collect: &mut dyn FnMut(bool) -> bool) -> Result<Option<usize>, ModelError> {
        self.check_state_model(s);
        if self.base.invariant_names().is_empty() {
            return Ok(None);
        }
        self.invariants_violated_gc(s, collect)
    }

    fn invariant_key(&self, _s: &EState, fp: u64) -> Option<u64> {
        // (A class fingerprint does not identify the state; hashing the
        // words costs about as much as the native invariants save.)
        (self.pure_invariants && matches!(self.fp, Fingerprint::Words)).then_some(fp)
    }

    fn constraint(&self, s: &EState) -> Result<bool, ModelError> {
        self.check_state_model(s);
        // (Called on every state or step: nothing to do is cheap.)
        let holds = self.base.constraint_exprs().is_empty() || self.constraints_hold(s)?;
        // `_POSSIBLE` predicates, by the interpreter until witnessed.
        if holds && self.base.possible_pending(false) {
            self.base.witness(&self.decode(s), None)?;
        }
        Ok(holds)
    }

    fn constraint_gc(&self, s: &EState, collect: &mut dyn FnMut(bool) -> bool) -> Result<bool, ModelError> {
        self.check_state_model(s);
        let holds = self.base.constraint_exprs().is_empty() || self.constraints_hold_gc(s, collect)?;
        if holds && self.base.possible_pending(false) {
            self.base.witness(&self.decode(s), None)?;
        }
        Ok(holds)
    }

    fn action_constraint(&self, s: &EState, t: &EState) -> Result<bool, ModelError> {
        self.check_state_model(s);
        self.check_state_model(t);
        // (Called on every state or step: nothing to do is cheap.)
        let holds = self.base.action_constraint_exprs().is_empty() || self.action_constraints_hold(s, t)?;
        if holds && self.base.possible_pending(true) {
            self.base.witness(&self.decode_current(s), Some(&self.decode(t)))?;
        }
        Ok(holds)
    }

    fn action_constraint_gc(&self, s: &EState, t: &EState, collect: &mut dyn FnMut(bool) -> bool) -> Result<bool, ModelError> {
        self.check_state_model(s);
        self.check_state_model(t);
        let holds = self.base.action_constraint_exprs().is_empty() || self.action_constraints_hold_gc(s, t, collect)?;
        if holds && self.base.possible_pending(true) {
            self.base.witness(&self.decode_current(s), Some(&self.decode(t)))?;
        }
        Ok(holds)
    }

    fn check_transition(&self, s: &EState, t: &EState) -> Result<Option<usize>, ModelError> {
        self.check_state_model(s);
        self.check_state_model(t);
        // (Called on every state or step: nothing to do is cheap.)
        if self.base.action_property_names().is_empty() {
            return Ok(None);
        }
        self.action_property_violated(s, t)
    }

    fn check_transition_gc(&self, s: &EState, t: &EState, collect: &mut dyn FnMut(bool) -> bool) -> Result<Option<usize>, ModelError> {
        self.check_state_model(s);
        self.check_state_model(t);
        if self.base.action_property_names().is_empty() {
            return Ok(None);
        }
        self.action_property_violated_gc(s, t, collect)
    }

    fn action_property_names(&self) -> &[String] {
        self.base.action_property_names()
    }
    fn extra_generated(&self) -> u64 {
        self.base.ip.composed_states.load(std::sync::atomic::Ordering::Relaxed)
    }

    fn stop_requested(&self) -> bool {
        self.base.stop_requested()
    }
    /// States are queued and written as their words (`StateCodec`).
    fn caps(&self) -> tlx_runtime::Caps<'_, EState> {
        tlx_runtime::Caps {
            format: Some(tlx_runtime::StateFormat::Words(self)),
            live_atoms: self.base.records_live_edges().then_some(self as _),
            effects: Some(self),
            checkpoint: Some(self),
            gc: self.value_store().map(|_| self as &dyn tlx_runtime::StoreGc<EState>),
        }
    }
    fn invariant_names(&self) -> &[String] {
        self.base.invariant_names()
    }

    fn action_names(&self) -> &[String] {
        self.base.action_names()
    }
    fn check_init_property(&self, s: &EState) -> Result<Option<String>, ModelError> {
        self.check_state_model(s);
        if !self.base.has_init_properties() {
            return Ok(None);
        }
        self.base.check_init_properties(&self.decode(s))
    }

    fn render(&self, s: &EState) -> String {
        self.check_state_model(s);
        self.base.render(&self.decode(s))
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
