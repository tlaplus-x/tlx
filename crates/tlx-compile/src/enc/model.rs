//! `EncModel`: the runtime `Model` over encoded states.
//!
//! Every action, invariant and action property runs natively if possible,
//! else as lowered IR (actions and Init), else in the interpreter. Native
//! and IR runs are speculative: on any failure the interpreter re-runs the
//! same (state, action) pair or predicate and has the last word.
//!
//! Mixed-mode native code calls back into the host for its regions
//! (`HostRegions`), with a per-worker `MixedCx` (`MIXED`).

use std::cell::RefCell;
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
use tlx_runtime::{ErrorKind, Model, ModelError};
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
fn lower_init_and_actions(lw: &mut Lowerer, base: &InterpModel, notes: &mut Vec<String>) -> (Option<ActionFn>, Vec<Option<ActionFn>>) {
    let init = lw.lower_init(base.init_expr()).map_err(|e| notes.push(format!("Init interpreted: {}", e.0))).ok();
    let actions = base
        .actions()
        .iter()
        .map(|a| lw.lower_action(a).map_err(|e| notes.push(format!("action {} interpreted: {}", a.name, e.0))).ok())
        .collect();
    (init, actions)
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
}

impl EncModel {
    pub fn new(base: Arc<InterpModel>, layout: Arc<Layout>, def_shapes: Vec<(DefId, Shape)>, settings: &Settings) -> EncModel {
        let lowering_start = std::time::Instant::now();
        let ip = base.ip.clone();
        let mut lw = Lowerer::with_typing(&ip, Typing::with_defs(layout.clone(), &def_shapes));
        let mut notes = Vec::new();
        let (init, actions) = lower_init_and_actions(&mut lw, &base, &mut notes);
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
        let mut invariants: Vec<PredFn> =
            base.invariant_exprs().iter().zip(base.invariant_names()).map(|(e, n)| lw.lower_pred(n, e)).collect();
        let mut aprops: Vec<PredFn> =
            base.action_property_exprs().iter().zip(base.action_property_names()).map(|(e, n)| lw.lower_trans_pred(n, e)).collect();
        let constraint_at = invariants.len();
        for (k, e) in base.constraint_exprs().iter().enumerate() {
            invariants.push(lw.lower_pred(&format!("constraint_{k}"), e));
        }
        let action_constraint_at = aprops.len();
        for (k, e) in base.action_constraint_exprs().iter().enumerate() {
            aprops.push(lw.lower_trans_pred(&format!("action_constraint_{k}"), e));
        }
        let live = &base.live;
        let live_state = live
            .state_atoms
            .iter()
            .enumerate()
            .map(|(k, a)| match a {
                StateAtom::Pred(a) => {
                    invariants.push(lw.lower_pred_in(&format!("live_state_{k}"), &a.expr, &a.env, false));
                    Some(invariants.len() - 1)
                }
                StateAtom::EnabledVia(..) => None,
            })
            .collect();
        let live_action = aprops.len();
        for (k, a) in live.action_atoms.iter().enumerate() {
            aprops.push(lw.lower_pred_in(&format!("live_action_{k}"), &a.expr, &a.env, true));
        }
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
            native::build(verified, &base, settings, mixed, &mut notes)
        } else {
            None
        };
        let irreversible_actions =
            settings.escape.then(|| actions.iter().map(|a| a.as_ref().is_some_and(|f| lw.stmt_volatile_beyond_output(&f.body))).collect());
        let typing = lw.into_typing();
        let symmetry = compile_symmetry(&base, &layout, &mut notes);
        let view = View::compile(&base, &layout, &def_shapes, settings, &mut notes);
        let fast_regions = match native.as_deref().and_then(|n| n.regions.as_ref()) {
            Some(t) => FastRegions::compile(t, &typing, &fast.prog),
            _ => Vec::new(),
        };
        let has_symmetry = !base.symmetry_maps().is_empty();
        let fp = match (symmetry, view) {
            (_, Some(view)) if base.has_projected_symmetry() => Fingerprint::View(view),
            // VIEW with SYMMETRY: TLC takes the VIEW of the orbit's least
            // state in its value order, which encodings do not preserve:
            // that state is chosen by value, then its encoding permuted.
            (Some(group), Some(view)) => Fingerprint::SymView { group, view },
            (Some(group), None) if !base.has_view() => Fingerprint::Symmetry { group, order: symmetry_order(&layout) },
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
            Fingerprint::SymView { .. } => notes.push("symmetry: least state by value, VIEW of its permuted encoding".into()),
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
        MIXED.with(|m| match m.try_borrow_mut() {
            Ok(mut m) => {
                let (id, cx) = &mut *m;
                // The decoded-state cache holds states of this model's layout.
                if *id != self.id {
                    *id = self.id;
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

    /// `compiled_successors` of an action that may print: its output is
    /// held back while it runs and printed if the run succeeds, else
    /// dropped (the interpreter redoes the run, printing again).
    /// TLX_PARANOID compares the lines with the interpreter's. (Out of
    /// line: `run_action`'s path for the other actions stays as short.)
    #[inline(never)]
    fn compiled_successors_printing(&self, s: &EState, i: usize, native: bool, buf: &mut Vec<Box<[u64]>>) -> Option<Path> {
        let mark = tlx_eval::Interp::hold_begin();
        let ok = self.compiled_successors(s, i, native, buf);
        let lines = tlx_eval::Interp::hold_end(mark);
        if ok.is_some() {
            if self.paranoid {
                self.cross_check_output(s, i, &lines);
            }
            self.base.ip.release_output(lines);
        }
        ok
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
        let mut path = Path::Interp;
        let native = native && !self.escaped(p.s) && !p.t.is_some_and(|t| self.escaped(t));
        let has = |n: &Native| native && if p.t.is_some() { n.has.action_properties[p.idx] } else { n.has.invariants[p.idx] };
        if let Some(lib) = self.native_lib(has) {
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
                None => path = Path::Fallback,
            }
        }
        if let Some(b) = steps() {
            return Ok((checked(b, " (as a change of its subscript)"), Path::Interp));
        }
        let ir = match p.t {
            None => self.ir_predicate(p.s, p.idx, p.level),
            Some(t) => self.ir_trans_predicate(p.s, t, p.idx, p.level),
        };
        if let Some(b) = ir {
            return Ok((checked(b, ""), Path::Ir));
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
            // Output is held transactionally by compiled_successors_printing.
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
        let ok = if self.prints[i] {
            self.compiled_successors_printing(s, i, native, &mut buf)
        } else {
            self.compiled_successors(s, i, native, &mut buf)
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
                self.cross_check(s, i, &buf);
            }
            let r = self.emit_compiled(buf, s, i, out);
            (r, path)
        } else {
            let compiled = self.compiled_path(i, native).is_some();
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

    /// Hand the compiled successors of `s` by action `i` to `out`; false
    /// if exploration is to stop.
    fn emit_compiled(
        &self,
        buf: Vec<Box<[u64]>>,
        s: &EState,
        i: usize,
        out: &mut dyn FnMut(EState, u32) -> bool,
    ) -> Result<bool, ModelError> {
        for w in buf {
            let t = self.finish(w, s.level + 1)?;
            if !out(t, i as u32) {
                return Ok(false);
            }
        }
        Ok(true)
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
        // (Random choices restart for each evaluation, as in the interpreter.)
        tlx_eval::Interp::begin_random_scope();
        // (With -coverage, the interpreter counts what Init rejects.)
        if self.base.coverage || !self.compiled_init(&mut buf) {
            return self.interpreted_init(out);
        }
        if self.inject.is_some() && self.inject_now(&[InjectKind::Init]).is_some() {
            buf.pop();
        }
        if self.paranoid {
            self.cross_check_init(&buf);
        }
        for w in buf {
            out(self.finish(w, 1)?);
        }
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

    fn check_transition(&self, s: &EState, t: &EState) -> Result<Option<usize>, ModelError> {
        self.check_state_model(s);
        self.check_state_model(t);
        // (Called on every state or step: nothing to do is cheap.)
        if self.base.action_property_names().is_empty() {
            return Ok(None);
        }
        self.action_property_violated(s, t)
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
    /// The mixed-mode state of this worker's native calls, and the id of
    /// the `EncModel` whose layout its decoded-state cache is for.
    static MIXED: RefCell<(u64, MixedCx)> = RefCell::new((0, MixedCx::new()));
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
