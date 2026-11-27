//! The compiled-tier driver: speculate a layout, explore, and on a layout
//! miss widen the offending shape and restart.

use std::sync::Arc;
use std::time::{Duration, Instant};
use tlx_layout::decisions::{in_slot, note_for, summary, Slot};
use tlx_layout::permute::AtomOrbits;
use tlx_layout::store::StoreRef;

use tlx_eval::model::State;
use tlx_eval::InterpModel;
use tlx_layout::infer::{grown_ints, map_value_ints, unify_records, widen_repeated, Hints};
use tlx_layout::{Layout, Shape};
use tlx_runtime::stats::{self, Metric};
use tlx_runtime::{explore_from, Options, Outcome, Recovery, Report, ResumePoint, Start};
use tlx_sema::hir::DefId;

use super::diag;
use super::model::{EState, EncModel, Miss, DYN_FILE, SPECULATION_FILE, STORE_FILE};
use super::speculate::{has_dyn, hints, materialize_candidates, prerun_shapes, Prerun, PrerunBudget};
use crate::settings::Settings;
use tlx_base::diag::{emit, Topic};

/// A progress line of the compiled tier (`compile: ...`).
fn log(text: impl std::fmt::Display) {
    emit(Topic::Compile, text);
}

/// Run a full check with the compiled tier, widening the layout and
/// restarting on layout misses (at most `max_restarts` times; a miss after
/// that continues in the fallback layout, see `Speculation::fallback`).
///
/// A restart continues the search where it stopped when possible: while a
/// miss can still happen the explorer keeps the visited states in its
/// compressed archive (within `TLX_RETAIN_MB` and the memory budget), and
/// after a miss they are re-encoded in the widened layout and the search
/// resumes at the start of the level it was expanding, continuing its trace
/// logs (see `tlx_runtime::ResumePoint`).
///
/// The search is always compiled (its pre-run is never the search, see
/// `check_from`).
pub fn check(base: Arc<InterpModel>, opts: &Options, max_restarts: usize) -> Result<(EncModel, Report<EState>), String> {
    match run_check(base, opts, max_restarts, None, false)? {
        Checked::Compiled(m, r) => Ok((m, r)),
        Checked::Interpreted(_) => unreachable!("the pre-run is not the search"),
    }
}

/// The result of a run of the compiled tier.
#[allow(clippy::large_enum_variant)] // one value per run, never stored in bulk; boxing only adds an indirection
pub enum Checked {
    /// The compiled search's model and report.
    Compiled(EncModel, Report<EState>),
    /// The report of the interpreter's pre-run, which explored the whole
    /// state space (or stopped where the search stops) with the search's
    /// options: it is the search's (`TLX_PRERUN_REUSE`, see
    /// `Prerun::report`), and no model was compiled.
    Interpreted(Report<State>),
}

/// `check`, recovering from checkpoint `recover` if given: the shapes and
/// the `Dyn` interner of the checkpointed run are restored (no pre-run), so
/// that states are encoded as there. Err: the checkpoint cannot be used
/// (its compiled-tier files are missing or do not fit). Unless
/// `TLX_PRERUN_REUSE=0` or `TLX_PARANOID`, the pre-run may be the search
/// (`Checked::Interpreted`).
pub fn check_from(base: Arc<InterpModel>, opts: &Options, max_restarts: usize, recover: Option<&Recovery>) -> Result<Checked, String> {
    let settings = Settings::global();
    run_check(base, opts, max_restarts, recover, settings.prerun_reuse && !settings.paranoid)
}

/// `check_from`; `reuse`: the pre-run may be the search.
fn run_check(
    base: Arc<InterpModel>,
    opts: &Options,
    max_restarts: usize,
    mut recover: Option<&Recovery>,
    reuse: bool,
) -> Result<Checked, String> {
    let raw_settings = Settings::global();
    // `TLX_ESCAPE` replaces the layouts value-store slots would sit in, so
    // the store stays off whenever `TLX_ESCAPE` is enabled (the pair is not
    // refused on fresh runs; recovering a store checkpoint under `TLX_ESCAPE`
    // is refused by `recovered_speculation`).
    let escape_set = raw_settings.escape;
    let store_mode = if raw_settings.value_store && !escape_set {
        if raw_settings.value_store_all {
            StoreMode::All
        } else {
            StoreMode::Dyn
        }
    } else {
        StoreMode::Off
    };
    if raw_settings.value_store && escape_set {
        log("value store (TLX_VALUE_STORE) disabled: the escape slots replace its layout");
    }
    let checkpoint_escape = raw_settings.escape && (recover.is_some() || opts.checkpoint.as_ref().is_some_and(|c| c.explicit()));
    let settings_override = checkpoint_escape.then(|| {
        log("escape slots disabled: explicit checkpoints require the original codec");
        Settings { escape: false, ..raw_settings.clone() }
    });
    let settings = settings_override.as_ref().unwrap_or(raw_settings);
    let max_restarts = settings.max_restarts.unwrap_or(max_restarts);
    // (The pre-run's evaluations may set TLCGet registers.)
    let registers = base.ip.save_registers();
    let (mut spec, first) = match recover {
        Some(r) => {
            let (spec, attempt) =
                recovered_speculation(&base, store_mode, escape_set, settings.value_store_bytes(opts.maxmem), |name| r.file(name))?;
            log(format_args!("recovering with the shapes of attempt {attempt} (no pre-run)"));
            (spec, attempt)
        }
        None => match Speculation::new(&base, settings, 0, opts.workers, reuse.then_some(opts)) {
            Ok(mut spec) => {
                if store_mode != StoreMode::Off {
                    spec.store = Some(StoreRef::new(settings.value_store_bytes(opts.maxmem)));
                    spec.store_all = store_mode == StoreMode::All;
                }
                (spec, 0)
            }
            Err(SpeculationError::Effects(e)) => return Err(e),
            Err(SpeculationError::Search(r)) => {
                let r = *r;
                stats::add_count("pre-run reused as the search", 1);
                base.ip.effects_finish();
                // (As the search reports its initial states.)
                if let (Some(p), false) = (&opts.progress, r.in_init) {
                    (p.init_done)(r.stats.init_generated, r.stats.init_distinct);
                }
                return Ok(Checked::Interpreted(r));
            }
        },
    };
    let escape_opts = (settings.escape && opts.checkpoint.is_some()).then(|| Options { checkpoint: None, ..opts.clone() });
    let opts = escape_opts.as_ref().unwrap_or(opts);
    // Ensure a checkpoint held across layout-miss restarts is always finalized
    // if `run_check` exits before a terminal `explore_from` runs (unless the
    // caller deferred cleanup until post-search liveness/replay completes).
    struct FinishCheckpoint<'a>(Option<&'a tlx_runtime::Checkpointer>);
    impl Drop for FinishCheckpoint<'_> {
        fn drop(&mut self) {
            if let Some(c) = self.0 {
                if !c.finish_deferred() {
                    c.finish();
                }
            }
        }
    }
    let _finish_ckpt = FinishCheckpoint(opts.checkpoint.as_deref());
    // The search to resume, and the layout of its states.
    let mut resume: Option<(ResumePoint<EState>, Arc<Layout>)> = None;
    // The search time that resuming saves.
    let mut searched = Duration::ZERO;
    let mut repeated = 0;
    let mut archive_lost = false;
    for attempt in first.. {
        let mut m = spec.model(&base, settings, attempt);
        m.restartable = !spec.fallback;
        if attempt > first {
            m.note_restart();
        }
        m.speculation = spec.encode(attempt);
        m.checkpoint_store = spec.store.clone();
        if tlx_base::diag::enabled(Topic::Coverage) {
            if let Some((_, old)) = &resume {
                for (i, (a, b)) in old.vars.iter().zip(&m.layout.vars).enumerate().filter(|(_, (a, b))| a != b) {
                    log(format_args!("widened {}: {a:?} -> {b:?}", base.ip.prog.vars[i].name));
                }
            }
        }
        let from = resume.take().and_then(|(c, old)| migrate(&m, c, &old, opts.workers, searched));
        if from.is_none() {
            searched = Duration::ZERO;
            if attempt > first {
                // Reclaim dead nodes from the previous attempt or an abandoned
                // archive migration so the restart from scratch gets the full
                // value-store budget.
                if m.value_store().is_some() {
                    let _ = tlx_runtime::StoreGc::collect(&m, &mut |_| Ok(()));
                }
                stats::add_count("states repeated from scratch", repeated);
                stats::add_count("restarts from scratch", 1);
                if archive_lost {
                    let message = format!("resume archive dropped: restarting from scratch, {repeated} states repeated");
                    log(&message);
                    stats::set("resume archive dropped", Metric::Text(message));
                    stats::add_count("restarts after archive dropped", 1);
                }
            }
        }
        // Archive the states while another restart is possible. When every
        // layout slot provably accepts the values Init, Next and the
        // materialized definitions can produce, no miss can happen and the
        // archive is pure overhead (scale.md §6).
        let limit = settings.retain_bytes(opts.maxmem);
        let archive_would_be_on = !spec.fallback && !settings.escape && limit > 0;
        // Liveness runs keep the archive: after a resume the levels before
        // the resume point are expanded again *from the archive* to record
        // their edges (scale.md §8.3), and a checkpoint taken before that
        // replay carries them there. The closure proof covers layout misses,
        // not that second consumer; eliding here could lose edges.
        let liveness = !base.live.is_empty();
        if liveness && archive_would_be_on {
            stats::set("archive retention", Metric::Text("kept: a liveness run replays archived levels for their edges".into()));
        }
        let closed = if archive_would_be_on && !liveness {
            if spec.closed.is_none() && !spec.closure_refuted {
                let (_, layout_defs) = spec.layout_shapes();
                let proof = super::closure::layout_is_closed(&base, &m.layout.vars, &layout_defs);
                match &proof {
                    Ok(()) => {
                        log("archive retention elided: every compiled layout slot is provably closed");
                        stats::set(&format!("{}archive memory limit (elided: closed layout)", stats::MEMORY), Metric::Bytes(0));
                        stats::set("archive retention", Metric::Text("elided: every slot is closed against layout misses".into()));
                        if tlx_layout::decisions::on() {
                            for (i, _) in m.layout.vars.iter().enumerate() {
                                note_for(Slot::Var(i as u32), "archive elided: the slot is provably closed".into());
                            }
                            for (d, _) in &layout_defs {
                                note_for(Slot::Def(d.0), "archive elided: the slot is provably closed".into());
                            }
                        }
                    }
                    Err(why) => stats::set("archive retention", Metric::Text(format!("kept: {why}"))),
                }
                spec.closed = Some(proof);
            }
            spec.closed.as_ref().is_some_and(|r| r.is_ok()) && !spec.closure_refuted
        } else {
            false
        };
        // `m.restartable` intentionally stays set even when the layout is
        // proven closed: it is also what makes the runtime treat a layout
        // miss as a resumable interruption rather than a fatal evaluation
        // error. A refuted proof can then restart (from scratch) instead of
        // producing a wrong result; the paranoid assertion below turns a
        // refutation into a test failure.
        let retain = (archive_would_be_on && !closed).then_some(limit);
        if retain.is_some() {
            let source = if settings.retain_mb.is_some() { "TLX_RETAIN_MB" } else { "-maxmem / 4" };
            stats::set(&format!("{}archive memory limit ({source})", stats::MEMORY), Metric::Bytes(limit as u64));
        }
        // Side effects (output, files, registers) of the interrupted search:
        // a resumed search repeats the level it was expanding, a search
        // started over everything. The main thread's TLCGet registers: as
        // before the pre-run when starting over (a resumed search keeps
        // those its initial states set); each worker of a resumed search
        // continues with its own.
        match &from {
            Some(c) => base.ip.effects_rollback_level(c.rolled_back())?,
            None if attempt > 0 => base.ip.effects_rollback_run()?,
            None => {}
        }
        if from.is_none() {
            base.ip.restore_registers(&registers);
        }
        base.ip.effects_active(!spec.fallback);
        base.ip.new_workers();
        let start = match (recover.take(), from) {
            (Some(r), _) => Start::Recover(r),
            (None, Some(c)) => Start::Resume(c),
            (None, None) => Start::Init,
        };
        let (r, resume_point) = explore_from(&m, opts, start, retain);
        // Check store exhaustion before classifying a miss as a refuted
        // closed-layout proof: a full value store surfaces through `Miss`,
        // which is a hard budget stop rather than a layout-widening miss.
        spec.check_store(opts.checkpoint.as_deref())?;
        if closed && matches!(&r.outcome, Outcome::Error(e) if e.is_layout_miss()) {
            // A proof bug must never turn into a wrong result: paranoid runs
            // fail loudly, ordinary runs fall back to the archive.
            if settings.paranoid {
                crate::paranoid::mismatch(format_args!("a run proved closed against misses stopped with a layout-miss"));
            }
            log("closed-layout proof refuted by a layout-miss; keeping the archive for the rest of the run");
            stats::set("closed-layout proof refuted", Metric::Text("a layout-miss occurred".into()));
            spec.closure_refuted = true;
        }
        searched += r.elapsed;
        if !spec.after_run(&m, &r, attempt, max_restarts) {
            base.ip.effects_finish();
            // Nothing restarts after the search (see `EncModel::restartable`).
            m.restartable = false;
            return Ok(Checked::Compiled(m, r));
        }
        repeated = r.stats.distinct.saturating_sub(r.stats.left);
        archive_lost = resume_point.is_none() && !r.in_init && retain.is_some();
        resume = resume_point.map(|c| (c, m.layout.clone()));
    }
    unreachable!()
}

/// The speculation of a checkpoint, and its attempt (`file`: the
/// checkpoint's compiled-tier files), with the checkpointed run's `Dyn`
/// interner and (when `TLX_VALUE_STORE` was active) its `Store` restored.
/// The shapes are decoded first: a checkpoint of another speculation version
/// or value-store mode is refused before its tables are loaded.
fn recovered_speculation<'a>(
    base: &InterpModel,
    expected_store: StoreMode,
    escape_set: bool,
    store_budget: usize,
    file: impl Fn(&str) -> Option<&'a [u8]>,
) -> Result<(Speculation, usize), String> {
    let dynv = file(DYN_FILE).ok_or("the checkpoint has no compiled-tier state (it was not taken with -compile)")?;
    let shapes = file(SPECULATION_FILE).ok_or("the checkpoint has no compiled-tier shapes")?;
    let (mut spec, attempt, ck_mode) = Speculation::decode(base, shapes)?;
    if ck_mode != expected_store {
        if escape_set && ck_mode != StoreMode::Off {
            return Err(format!("the checkpoint was taken with {}, cannot recover with TLX_ESCAPE=1", ck_mode.label()));
        }
        return Err(format!("the checkpoint was taken with {}, this run uses {}", ck_mode.label(), expected_store.label()));
    }
    let mut rd = tlx_value::ser::Reader::new(dynv);
    let snap = tlx_layout::ser::read_dyn_table(&mut rd).map_err(|e| format!("corrupt Dyn interner: {e}"))?;
    rd.finish().map_err(|e| format!("corrupt Dyn interner: {e}"))?;
    tlx_layout::dynval::restore(&snap)?;
    match ck_mode {
        StoreMode::Off => {
            if file(STORE_FILE).is_some() {
                return Err("corrupt checkpoint: unexpected value store file for TLX_VALUE_STORE=0".into());
            }
        }
        StoreMode::Dyn | StoreMode::All => {
            let store_bytes = file(STORE_FILE).ok_or("the checkpoint has no value store (missing model-store)")?;
            let mut srd = tlx_value::ser::Reader::new(store_bytes);
            let store = tlx_layout::ser::read_store(&mut srd, store_budget)?;
            spec.store = Some(StoreRef(store));
            spec.store_all = ck_mode == StoreMode::All;
        }
    }
    Ok((spec, attempt))
}

/// Run a simulation `run` (of behaviors of at most `depth` steps) with the
/// compiled tier, widening the layout and starting over on layout misses
/// (at most `max_restarts` times). The interpreter's random numbers start
/// from `seed` when the model is built (constant subexpressions are
/// evaluated then) and again with every restart.
pub fn simulate<S>(
    base: Arc<InterpModel>,
    depth: u32,
    seed: u64,
    max_restarts: usize,
    run: &mut dyn FnMut(&EncModel) -> (Report<EState>, S),
) -> Result<(EncModel, Report<EState>, S), String> {
    let settings = Settings::global();
    let max_restarts = settings.max_restarts.unwrap_or(max_restarts);
    // (The pre-run's evaluations may set TLCGet registers.)
    let registers = base.ip.save_registers();
    let mut spec = match Speculation::new(&base, settings, depth.max(1), 1, None) {
        Ok(spec) => spec,
        Err(SpeculationError::Effects(e)) => return Err(e),
        Err(SpeculationError::Search(_)) => unreachable!("the pre-run is not the simulation"),
    };
    if settings.value_store && !settings.escape {
        spec.store = Some(StoreRef::new(settings.value_store_bytes(usize::MAX)));
        spec.store_all = settings.value_store_all;
    }
    for attempt in 0.. {
        base.ip.set_seed(seed);
        // Starting over: the output and files of the earlier attempt are
        // not repeated, the registers are as before it.
        if attempt > 0 {
            base.ip.effects_rollback_run()?;
        }
        base.ip.effects_active(!spec.fallback);
        base.ip.restore_registers(&registers);
        base.ip.new_workers();
        let mut m = spec.model(&base, settings, attempt);
        m.restartable = !spec.fallback;
        if attempt > 0 {
            m.note_restart();
        }
        let (r, extra) = run(&m);
        spec.check_store(None)?;
        if !spec.after_run(&m, &r, attempt, max_restarts) {
            base.ip.effects_finish();
            // Nothing restarts after the simulation (see `EncModel::restartable`).
            m.restartable = false;
            return Ok((m, r, extra));
        }
    }
    unreachable!()
}

/// A pre-run may complete the search or fail to restore its effects.
/// Restoration errors are fatal; ordinary shape-probing errors may fall back.
enum SpeculationError {
    Search(Box<Report<State>>),
    Effects(String),
}

/// The speculated shapes, widened after each layout miss.
struct Speculation {
    hints: Hints,
    shapes: Vec<Shape>,
    def_shapes: Vec<(DefId, Shape)>,
    /// Layout misses per variable so far.
    misses: Vec<u32>,
    /// Layout misses per materialized definition (as `def_shapes`).
    def_misses: Vec<u32>,
    /// The layout cannot miss: every variable is `Dyn` and no definition
    /// is materialized (values are interned, actions and predicates run
    /// boxed or in the interpreter). Taken when a miss happens after
    /// `max_restarts` restarts, for the rest of the run.
    fallback: bool,
    /// The run's value store (`TLX_VALUE_STORE`): layouts hold the slots
    /// whose shape has `Dyn` parts in it (`Shape::Ref`). The speculation's
    /// own shapes keep `Dyn` (shape inference and checkpoints).
    store: Option<StoreRef>,
    /// `TLX_VALUE_STORE=all` (testing): every slot is a `Ref`.
    store_all: bool,
    /// Cross-attempt cache for unchanged lowered IR and JIT machine code.
    cache: super::cache::CompileCache,
    /// The static closed-layout proof for the current shapes (`None`: not
    /// computed yet, or invalidated by a widening): `Ok` when no slot can
    /// miss, so the archive is elided; `Err` names the construct that kept
    /// it.
    closed: Option<Result<(), String>>,
    /// A proven-closed run missed anyway (a bug in the proof): never elide
    /// again for this run, so the archive is available to resume.
    closure_refuted: bool,
}

/// The version of `Speculation::encode`, and of the compiled tier's
/// checkpoint files with it (4: value store mode and `model-store`).
const SPECULATION_VERSION: u64 = 4;

/// How a run uses the value store (`TLX_VALUE_STORE`), recorded in
/// `model-shapes` so recovery refuses mismatched modes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum StoreMode {
    Off = 0,
    Dyn = 1,
    All = 2,
}

impl StoreMode {
    fn from_byte(b: u8) -> Result<StoreMode, String> {
        match b {
            0 => Ok(StoreMode::Off),
            1 => Ok(StoreMode::Dyn),
            2 => Ok(StoreMode::All),
            _ => Err(format!("corrupt compiled-tier shapes: unknown value store mode {b}")),
        }
    }

    fn label(self) -> &'static str {
        match self {
            StoreMode::Off => "TLX_VALUE_STORE=0",
            StoreMode::Dyn => "TLX_VALUE_STORE=1",
            StoreMode::All => "TLX_VALUE_STORE=all",
        }
    }
}

impl Speculation {
    fn store_mode(&self) -> StoreMode {
        match (&self.store, self.store_all) {
            (None, _) => StoreMode::Off,
            (Some(_), false) => StoreMode::Dyn,
            (Some(_), true) => StoreMode::All,
        }
    }

    /// The state of the speculation at attempt `attempt`, for a checkpoint:
    /// version, attempt, fallback, store mode, the variables' shapes and
    /// misses, the materialized definitions (id, shape) and their misses.
    fn encode(&self, attempt: usize) -> Vec<u8> {
        use tlx_layout::ser::write_shape;
        let mut w = tlx_value::ser::Writer::new();
        w.uvar(SPECULATION_VERSION);
        w.usize(attempt);
        w.u8(self.fallback as u8);
        w.u8(self.store_mode() as u8);
        w.usize(self.shapes.len());
        for (s, &n) in self.shapes.iter().zip(&self.misses) {
            write_shape(&mut w, s);
            w.uvar(n as u64);
        }
        w.usize(self.def_shapes.len());
        for ((d, s), &n) in self.def_shapes.iter().zip(&self.def_misses) {
            w.uvar(d.0 as u64);
            write_shape(&mut w, s);
            w.uvar(n as u64);
        }
        w.into_bytes()
    }

    /// The speculation `encode` wrote, its attempt, and its store mode.
    fn decode(base: &InterpModel, b: &[u8]) -> Result<(Speculation, usize, StoreMode), String> {
        use tlx_layout::ser::read_shape;
        let mut r = tlx_value::ser::Reader::new(b);
        let e = |e: tlx_value::ser::DecodeError| format!("corrupt compiled-tier shapes: {e}");
        let small = |v: u64| u32::try_from(v).map_err(|_| "corrupt compiled-tier shapes: a count out of range".to_string());
        let version = r.uvar().map_err(e)?;
        if version != SPECULATION_VERSION {
            return Err(format!(
                "the checkpoint's compiled-tier shapes are of version {version}, this tlx reads version {SPECULATION_VERSION}"
            ));
        }
        let attempt = r.usize().map_err(e)?;
        let fallback = r.u8().map_err(e)? != 0;
        let store_mode = StoreMode::from_byte(r.u8().map_err(e)?)?;
        let n = r.count(2).map_err(e)?;
        if n != base.ip.prog.vars.len() {
            return Err(format!("the checkpoint has shapes of {n} variables, the spec {}", base.ip.prog.vars.len()));
        }
        let (mut shapes, mut misses) = (Vec::with_capacity(n), Vec::with_capacity(n));
        for _ in 0..n {
            shapes.push(read_shape(&mut r).map_err(e)?);
            misses.push(small(r.uvar().map_err(e)?)?);
        }
        let n = r.count(3).map_err(e)?;
        let (mut def_shapes, mut def_misses) = (Vec::with_capacity(n), Vec::with_capacity(n));
        for _ in 0..n {
            let d = small(r.uvar().map_err(e)?)?;
            if d as usize >= base.ip.prog.defs.len() {
                return Err("corrupt compiled-tier shapes: a definition out of range".into());
            }
            def_shapes.push((DefId(d), read_shape(&mut r).map_err(e)?));
            def_misses.push(small(r.uvar().map_err(e)?)?);
        }
        r.finish().map_err(e)?;
        Ok((
            Speculation {
                hints: hints(base),
                shapes,
                def_shapes,
                misses,
                def_misses,
                fallback,
                store: None,
                store_all: false,
                cache: super::cache::CompileCache::default(),
                closed: None,
                closure_refuted: false,
            },
            attempt,
            store_mode,
        ))
    }

    /// `walk_depth`, `workers`: see `PrerunBudget`; `search`: see
    /// `prerun_shapes` (Err: the pre-run's report is the search's).
    fn new(
        base: &InterpModel,
        settings: &Settings,
        walk_depth: u32,
        workers: usize,
        search: Option<&Options>,
    ) -> Result<Speculation, SpeculationError> {
        let hints = hints(base);
        let (shapes, def_shapes) = speculate(base, &hints, settings, walk_depth, workers, search)?;
        let misses = vec![0; shapes.len()];
        let def_misses = vec![0; def_shapes.len()];
        Ok(Speculation {
            hints,
            shapes,
            def_shapes,
            misses,
            def_misses,
            fallback: false,
            store: None,
            store_all: false,
            cache: super::cache::CompileCache::default(),
            closed: None,
            closure_refuted: false,
        })
    }

    /// The model of attempt `attempt` (in the current shapes).
    fn model(&mut self, base: &Arc<InterpModel>, settings: &Settings, attempt: usize) -> EncModel {
        let (shapes, defs) = self.layout_shapes();
        let layout = Arc::new(Layout::new(shapes));
        let t0 = Instant::now();
        let m = EncModel::new_with_cache(base.clone(), layout, defs, settings, Some(&mut self.cache));
        log(format_args!("lowering and code generation: {:.2}s", t0.elapsed().as_secs_f64()));
        stats::set("state words", Metric::Count(m.layout.words as u64));
        stats::add_secs("model build (lowering, C generation)", t0.elapsed());
        stats::add_count("model builds", 1);
        if attempt == 0 {
            if !self.def_shapes.is_empty() {
                let names: Vec<&str> = self.def_shapes.iter().map(|(d, _)| def_name(base, *d)).collect();
                log(format_args!("materialized definitions: {}", names.join(", ")));
            }
            diag::log_coverage(&m);
        } else if tlx_base::diag::enabled(tlx_base::diag::Topic::Coverage) {
            diag::log_coverage(&m);
        }
        m
    }

    /// After a run of `m` (attempt `attempt`) with report `r`: if it stopped
    /// on a layout miss, widen and return true (restart). After
    /// `max_restarts` restarts, a miss switches to the fallback layout
    /// instead (which cannot miss).
    fn after_run<S>(&mut self, m: &EncModel, r: &Report<S>, attempt: usize, max_restarts: usize) -> bool {
        m.report_native_regions();
        let base = &m.base;
        let (events, pending) = m.native_events();
        events.into_iter().for_each(log);
        if pending {
            log("native build still running at the end of the search");
        }
        // (The fallback layout cannot miss; it is never restarted.)
        let stopped_by_miss = !self.fallback && matches!(&r.outcome, Outcome::Error(e) if e.is_layout_miss());
        let last = attempt + 1 == max_restarts;
        match m.take_miss() {
            Some(miss) if stopped_by_miss && attempt >= max_restarts => {
                let what = match &miss {
                    Miss::Var(var, v) => format!("{} (value {v})", base.ip.prog.vars[*var].name),
                    Miss::Def(i, v) => format!("definition {} (value {v})", def_name(base, self.def_shapes[*i].0)),
                };
                log(format_args!("layout miss on {what} after {max_restarts} restarts; continuing with dynamic values (no fixed layout) for the rest of the run"));
                stats::add_count("restarts (layout miss)", 1);
                stats::add_count("fallbacks to dynamic values", 1);
                for v in 0..self.shapes.len() {
                    note_for(Slot::Var(v as u32), format!("Dyn: fallback layout after a miss on {what} ({max_restarts} restarts)"));
                }
                self.fallback = true;
                self.shapes.iter_mut().for_each(|s| *s = Shape::Dyn);
                self.def_shapes.clear();
                self.def_misses.clear();
                self.closed = None;
                true
            }
            Some(Miss::Var(var, v)) if stopped_by_miss => {
                log(format_args!("layout miss on {} (value {v}); widening and restarting", base.ip.prog.vars[var].name));
                stats::add_count("restarts (layout miss)", 1);
                self.misses[var] += 1;
                let slot = Slot::Var(var as u32);
                if last {
                    // Last attempt: a Dyn slot holds any value.
                    note_for(slot, format!("Dyn: miss {} on the last restart (value {v})", self.misses[var]));
                    self.shapes[var] = Shape::Dyn;
                    self.closed = None;
                    return true;
                }
                let old = self.shapes[var].clone();
                self.shapes[var] = in_slot(slot, || atom_orbits(base).close(&widen_repeated(&old, &v, &self.hints, self.misses[var] - 1)));
                if tlx_layout::decisions::on() {
                    let what = format!("miss {} (value {v}): {} -> {}", self.misses[var], summary(&old), summary(&self.shapes[var]));
                    note_for(slot, what);
                }
                widen_alike(&old, &mut self.shapes, var, &mut self.def_shapes);
                unify(&mut self.shapes, &mut self.def_shapes);
                self.closed = None;
                true
            }
            Some(Miss::Def(i, v)) if stopped_by_miss => {
                log(format_args!(
                    "layout miss on definition {} (value {v}); widening and restarting",
                    def_name(base, self.def_shapes[i].0)
                ));
                stats::add_count("restarts (layout miss)", 1);
                self.def_misses[i] += 1;
                let slot = Slot::Def(self.def_shapes[i].0 .0);
                let w = in_slot(slot, || {
                    atom_orbits(base).close(&widen_repeated(&self.def_shapes[i].1, &v, &self.hints, self.def_misses[i] - 1))
                });
                note_for(slot, format!("miss {} (value {v}): {} -> {}", self.def_misses[i], summary(&self.def_shapes[i].1), summary(&w)));
                if last || has_dyn(&w) {
                    note_for(slot, "not materialized any more (last restart, or Dyn parts)".to_string());
                    // No longer materialized (on the last attempt, or when
                    // the definition's values are open-ended).
                    self.def_shapes.remove(i);
                    self.def_misses.remove(i);
                    self.closed = None;
                    return true;
                }
                self.def_shapes[i].1 = w;
                unify(&mut self.shapes, &mut self.def_shapes);
                self.closed = None;
                true
            }
            _ => {
                let b = m.bailouts.get();
                stats::set("action runs fell back to the interpreter", Metric::Count(b));
                m.report_stats();
                if stats::on() {
                    stats::set_section("layout slots (final layout: shape, words; how it was chosen)", self.slot_report(base));
                    if let Some(s) = &self.store {
                        let st = s.stats();
                        stats::set(&format!("{}value store nodes", stats::MEMORY), Metric::Count(st.nodes));
                        stats::set(&format!("{}value store nodes and payloads", stats::MEMORY), Metric::Bytes(st.node_bytes));
                        stats::set(&format!("{}value store index (est.)", stats::MEMORY), Metric::Bytes(st.index_bytes));
                        stats::set(&format!("{}value store budget", stats::MEMORY), Metric::Bytes(st.budget));
                        if st.gc_cycles > 0 {
                            stats::set(&format!("{}value store GC cycles", stats::MEMORY), Metric::Count(st.gc_cycles));
                            stats::set(&format!("{}value store reclaimed nodes", stats::MEMORY), Metric::Count(st.reclaimed_nodes));
                            stats::set(&format!("{}value store reclaimed bytes", stats::MEMORY), Metric::Bytes(st.reclaimed_bytes));
                        }
                        let calls = |i: usize| crate::exec::refops::CALLS[i].load(std::sync::atomic::Ordering::Relaxed);
                        stats::set("value store operations (closure IR)", Metric::Count(calls(0)));
                        stats::set("value store operations (native ref_op)", Metric::Count(calls(1)));
                    }
                }
                if stats::on() {
                    let (n, bytes) = tlx_layout::dynval::footprint();
                    if n > 0 {
                        stats::set(&format!("{}Dyn interner values", stats::MEMORY), Metric::Count(n as u64));
                        stats::set(&format!("{}Dyn interner tables", stats::MEMORY), Metric::Bytes(bytes as u64));
                        let retained = tlx_layout::dynval::retained_value_bytes();
                        stats::set(&format!("{}Dyn interner value heap (retained)", stats::MEMORY), Metric::Bytes(retained as u64));
                    }
                }
                if b > 0 {
                    log(format_args!("{b} action evaluations fell back to the interpreter"));
                }
                false
            }
        }
    }
}

impl Speculation {
    /// The shapes of the layout and of the materialized definitions: as
    /// speculated, except that with a value store a variable whose shape
    /// has `Dyn` parts is one `Ref` slot, and so are the `Dyn` components
    /// of a tuple VIEW (state variables, see `speculate::DefProbe`).
    fn layout_shapes(&self) -> (Vec<Shape>, Vec<(DefId, Shape)>) {
        let Some(store) = &self.store else { return (self.shapes.clone(), self.def_shapes.clone()) };
        fn contains_dyn(s: &Shape) -> bool {
            let mut found = matches!(s, Shape::Dyn);
            s.for_each_child(|c| found |= contains_dyn(c));
            found
        }
        let all = self.store_all;
        let to_ref = |s: &Shape| if all || contains_dyn(s) { Shape::Ref(store.clone()) } else { s.clone() };
        let shapes = self.shapes.iter().map(to_ref).collect();
        let defs = self
            .def_shapes
            .iter()
            .map(|(d, s)| {
                let s = match s {
                    Shape::Tuple(es) if contains_dyn(s) => Shape::Tuple(es.iter().map(to_ref).collect()),
                    s => to_ref(s),
                };
                (*d, s)
            })
            .collect();
        (shapes, defs)
    }

    /// Err if the value store filled up: after safepoint reclamation could not
    /// fit the live root set within the budget, the store latched full and
    /// values it refused were neither stored nor fingerprinted correctly.
    fn check_store(&self, checkpoint: Option<&tlx_runtime::Checkpointer>) -> Result<(), String> {
        match &self.store {
            Some(s) if s.is_full() => {
                let mut msg = format!(
                    "the value store (TLX_VALUE_STORE) exceeded its budget of {} MiB (-maxmem): raise -maxmem or turn the store off (TLX_VALUE_STORE=0)",
                    s.budget() >> 20
                );
                if checkpoint.is_some_and(|c| c.keep_last()) {
                    msg.push_str(", recovering the last checkpoint, which is kept");
                }
                Err(msg)
            }
            _ => Ok(()),
        }
    }

    /// One line per slot of the final layout (variables, then materialized
    /// definitions): its shape summary and words, then the decisions noted
    /// on it (`tlx_layout::decisions`; "observed" when none).
    fn slot_report(&self, base: &InterpModel) -> String {
        let mut out = String::new();
        let mut slot = |name: &str, s: &Shape, slot: Slot| {
            let words = tlx_layout::layout::words(s);
            out += &format!("  {name:<24} {} ({words} word{})\n", summary(s), if words == 1 { "" } else { "s" });
            let notes = tlx_layout::decisions::notes(slot);
            if notes.is_empty() {
                out += "      observed\n";
            }
            for (what, n) in notes {
                let times = if n > 1 { format!(" ({n} times)") } else { String::new() };
                out += &format!("      {what}{times}\n");
            }
        };
        let (shapes, defs) = self.layout_shapes();
        for (v, s) in shapes.iter().enumerate() {
            slot(&base.ip.prog.vars[v].name, s, Slot::Var(v as u32));
        }
        for (d, s) in &defs {
            slot(&format!("definition {}", def_name(base, *d)), s, Slot::Def(d.0));
        }
        out
    }
}

/// After variable `var` (of shape `old`) was widened: integers elsewhere
/// with a bound that grew (counters, indices, values copied around) tend to
/// outgrow it together: they get the new bound, which saves restarts and
/// keeps the encodings of values moved between them alike.
fn widen_alike(old: &Shape, shapes: &mut [Shape], var: usize, defs: &mut [(DefId, Shape)]) {
    let mut grown = Vec::new();
    grown_ints(old, &shapes[var], &mut grown);
    if grown.is_empty() {
        return;
    }
    let mut f = |lo: i64, hi: i64| {
        let (mut l, mut h) = (lo, hi);
        for &((l0, h0), (l1, h1)) in &grown {
            if h1 > h0 && hi == h0 {
                h = h.max(h1);
            }
            if l1 < l0 && lo == l0 {
                l = l.min(l1);
            }
        }
        ((l, h) != (lo, hi)).then_some((l, h))
    };
    for s in shapes.iter_mut().chain(defs.iter_mut().map(|d| &mut d.1)) {
        *s = map_value_ints(s, &mut f);
    }
}

/// Make records with the same fields alike in the variables and the
/// materialized definitions (see `unify_records`); a definition whose shape
/// would get dynamic parts keeps its shape.
fn unify(shapes: &mut [Shape], defs: &mut [(DefId, Shape)]) {
    let mut all: Vec<Shape> = shapes.iter().chain(defs.iter().map(|d| &d.1)).cloned().collect();
    unify_records(&mut all);
    let (vs, ds) = all.split_at(shapes.len());
    shapes.clone_from_slice(vs);
    for (d, s) in defs.iter_mut().zip(ds) {
        if !has_dyn(s) {
            d.1 = s.clone();
        }
    }
}

/// Re-encode the archived states of resume point `c` (in layout `old`) for
/// model `m`; None (start over) if some state does not fit, or if
/// re-encoding them would take longer than searching them again (about
/// `searched`).
fn migrate(m: &EncModel, c: ResumePoint<EState>, old: &Layout, workers: usize, searched: Duration) -> Option<ResumePoint<EState>> {
    // At most this many threads re-encode (the machine may be shared), and
    // only this many states (about 25 ms on one thread) or more are worth
    // more threads than the search's workers.
    const REENCODE_THREADS: usize = 8;
    const REENCODE_PARALLEL_MIN: usize = 10_000;
    const SAMPLE: usize = 1000;
    let t0 = Instant::now();
    let (n, level) = (c.len(), c.level());
    // Re-encoding stalls the search: on more threads than its workers when
    // it evaluates nothing (a late miss with one worker re-encoded
    // 260k states in 0.6 s). The result does not depend on the threads.
    let workers = if m.migrate_is_pure() && n >= REENCODE_PARALLEL_MIN {
        workers.max(std::thread::available_parallelism().map_or(1, |p| p.get()).min(REENCODE_THREADS))
    } else {
        workers
    };
    debug_assert_eq!(c.words(), old.words);
    // Keep the value store in GC-managed mode during optional archive
    // migration so a budget hit while converting the archive fails migration
    // cleanly without permanently latching `Store::is_full()`; when migration
    // returns `None`, `run_check` reclaims the partial allocations before
    // restarting from scratch.
    let _store_gc_guard = m.value_store().map(|s| s.0.enter_gc_scope());
    // An archived state (`words` in layout `old`, of depth `depth`) in the
    // layout of `m`: its words in `out`, its fingerprint.
    let reencode = |words: &[u64], depth: u32, out: &mut [u64]| -> Result<u64, tlx_runtime::ModelError> {
        let s = m.migrate(
            old,
            &EState {
                words: words.into(),
                level: depth,
                fp: 0,
                #[cfg(debug_assertions)]
                model: 0,
            },
        )?;
        out.copy_from_slice(&s.words);
        Ok(s.fp)
    };
    if n > SAMPLE {
        let k = SAMPLE.min(n);
        let mut out = vec![0u64; m.layout.words];
        let sample_ok = c.sample(k, |w, d| reencode(w, d, &mut out).is_ok());
        let estimate = t0.elapsed().mul_f64(n as f64 / k as f64 / workers.max(1) as f64);
        if !sample_ok || estimate > searched {
            m.take_miss();
            log(format_args!("starting over (re-encoding {n} states: about {:.2}s)", estimate.as_secs_f64()));
            return None;
        }
    }
    match c.transcode(workers, m.layout.words, reencode) {
        Ok(c) => {
            log(format_args!("resuming the search at depth {level}: {n} states re-encoded in {:.2}s", t0.elapsed().as_secs_f64()));
            stats::add_count("resumed searches", 1);
            stats::add_count("states re-encoded", n as u64);
            stats::add_secs("re-encoding", t0.elapsed());
            Some(c)
        }
        Err(_) => {
            // (A miss recorded while re-encoding is found again.)
            m.take_miss();
            log("cannot re-encode the visited states; starting over");
            None
        }
    }
}

/// Initial shapes of the variables and of the materialized definitions,
/// from the pre-run (all `Dyn` and none if it fails); Err: the pre-run's
/// report, which is the search's (see `prerun_shapes`'s `search`).
fn speculate(
    base: &InterpModel,
    hints: &Hints,
    settings: &Settings,
    walk_depth: u32,
    workers: usize,
    search: Option<&Options>,
) -> Result<(Vec<Shape>, Vec<(DefId, Shape)>), SpeculationError> {
    let cands = if settings.no_materialize { Vec::new() } else { materialize_candidates(base) };
    if stats::on() {
        tlx_layout::decisions::enable();
    }
    let t0 = Instant::now();
    let budget =
        PrerunBudget { states: settings.prerun_states, time: settings.prerun_time, walk_depth, settle: settings.prerun_settle, workers };
    let orbits = atom_orbits(base);
    let layout = |p: Prerun| {
        let (shapes, defs, _) = layouts(base, &cands, p, &orbits);
        (shapes, defs)
    };
    let pre = prerun_shapes(base, budget, hints, &cands, &layout, search).map_err(SpeculationError::Effects)?;
    let dt = t0.elapsed();
    stats::add_secs("pre-run", dt);
    if let Ok(p) = &pre {
        stats::add_count("pre-run states", p.states as u64);
    }
    match &pre {
        Ok(p) => {
            let why = if p.report.is_some() {
                " (the search: its result is the run's)"
            } else if p.settled {
                " (layout settled)"
            } else if dt >= budget.time {
                " (time budget)"
            } else {
                ""
            };
            log(format_args!("pre-run: {:.2}s, {} states{why}", dt.as_secs_f64(), p.states))
        }
        Err(_) => log(format_args!("pre-run: {:.2}s", dt.as_secs_f64())),
    }
    match pre {
        Ok(Prerun { report: Some(r), .. }) => Err(SpeculationError::Search(Box::new(r))),
        Ok(p) => {
            let (shapes, defs, notes) = layouts(base, &cands, p, &orbits);
            notes.into_iter().for_each(log);
            Ok((shapes, defs))
        }
        Err(e) => {
            log(format_args!("pre-run failed ({}); using Dyn layout", e.message));
            for v in 0..base.ip.prog.vars.len() {
                note_for(Slot::Var(v as u32), format!("Dyn: the pre-run failed ({})", e.message));
            }
            Ok((vec![Shape::Dyn; base.ip.prog.vars.len()], Vec::new()))
        }
    }
}

fn atom_orbits(base: &InterpModel) -> AtomOrbits {
    match base.symmetry_factors() {
        Some(factors) => AtomOrbits::from_factors(&factors),
        None => AtomOrbits::from_group(base.symmetry_maps()),
    }
}

/// The shapes of the variables and of the materialized definitions (among
/// the candidates `cands`) from pre-run result `p`.
fn layouts(base: &InterpModel, cands: &[DefId], p: Prerun, orbits: &AtomOrbits) -> (Vec<Shape>, Vec<(DefId, Shape)>, Vec<String>) {
    let view = super::speculate::view_def(base);
    let defs = cands
        .iter()
        .zip(p.defs)
        .filter_map(|(&d, observed)| {
            let shape = orbits.close(&observed?);
            (!has_dyn(&shape) || (view == Some(d) && super::speculate::view_allows_dyn(base, d, &shape))).then_some((d, shape))
        })
        .collect();
    let shapes = p.shapes.iter().map(|s| orbits.close(s)).collect();
    let bounded = p.bounded.iter().map(|(v, s)| (*v, orbits.close(s))).collect();
    with_bounds(base, shapes, defs, bounded)
}

/// The unified shapes of the variables and definitions, with those of the
/// shapes refined by type-invariant bounds (`bounded`, in order) that do
/// not make the state larger (and the notes to log about the bounds taken). A bound can make a set of records a bitset
/// over exactly the possible records (much smaller than a sorted array of
/// them), but unifying records with the same fields elsewhere can undo that
/// (and leave a large cardinality bound): such a refinement is not taken.
fn with_bounds(
    base: &InterpModel,
    shapes: Vec<Shape>,
    defs: Vec<(DefId, Shape)>,
    bounded: Vec<(usize, Shape)>,
) -> (Vec<Shape>, Vec<(DefId, Shape)>, Vec<String>) {
    let unified = |shapes: &[Shape]| {
        let (mut s, mut d) = (shapes.to_vec(), defs.clone());
        unify(&mut s, &mut d);
        let words: usize = s.iter().map(tlx_layout::layout::words).sum();
        (s, d, words)
    };
    let mut notes = Vec::new();
    let mut cur = shapes;
    let mut best = unified(&cur);
    for (var, r) in bounded {
        let mut trial = cur.clone();
        trial[var] = r;
        let t = unified(&trial);
        if t.2 <= best.2 && best.0.iter().zip(&t.0).all(|(old, new)| !has_dyn(new) || has_dyn(old)) {
            if t.2 < best.2 {
                notes.push(format!("type invariant bounds {}: {} -> {} state words", base.ip.prog.vars[var].name, best.2, t.2));
            }
            if tlx_layout::decisions::on() && trial[var] != cur[var] {
                let what = format!("type-invariant bound: {} -> {}", summary(&cur[var]), summary(&trial[var]));
                note_for(Slot::Var(var as u32), what);
            }
            cur = trial;
            best = t;
        }
    }
    (best.0, best.1, notes)
}

fn def_name(base: &InterpModel, d: DefId) -> &str {
    &base.ip.prog.defs[d.idx()].name
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn partial_server_orbit_uses_one_compiled_layout() {
        let src = tlx_testkit::module(
            "Orbit",
            r"EXTENDS TLC
CONSTANT Server
VARIABLE msg
Symmetry == Permutations(Server)
Init == \E s \in Server : msg = [dest |-> s, sent |-> FALSE]
Next == \E s \in Server : msg' = [dest |-> s, sent |-> TRUE]",
        );
        let cfg = "CONSTANT Server = {s1, s2, s3, s4}\nSYMMETRY Symmetry\nINIT Init\nNEXT Next\n";
        let base = Arc::new(tlx_testkit::spec::load(&src, cfg));
        let settings = Settings { prerun_states: 1, paranoid: true, ..Settings::global().clone() };
        // Isolate the observations from static constant hints that can already
        // cover all four servers in this small fixture.
        let (shapes, defs) = speculate(&base, &Hints::default(), &settings, 0, 1, None).ok().unwrap();
        let model = EncModel::new(base.clone(), Arc::new(Layout::new(shapes)), defs, &settings);
        assert!(model.notes.iter().any(|n| n == "symmetry: permuting encodings"), "{:?}", model.notes);
        let opts = Options { workers: 1, ..Options::default() };
        let reference = tlx_runtime::explore(&*base, &opts);
        let compiled = tlx_runtime::explore(&model, &opts);
        assert!(matches!(reference.outcome, Outcome::Ok));
        assert!(matches!(compiled.outcome, Outcome::Ok), "{:?}", compiled.outcome);
        assert_eq!(reference.stats.distinct, 2);
        assert_eq!((compiled.stats.generated, compiled.stats.distinct), (reference.stats.generated, reference.stats.distinct));
    }

    #[test]
    fn orbit_closure_rechecks_materialization_and_bounds() {
        use tlx_layout::shape::{map_shape, FcnWitness};
        use tlx_value::{Sym, Value};

        let src = tlx_testkit::module("Orbit", "VARIABLE x\nV == <<x, x = x>>\nInit == x = TRUE\nNext == x' = x");
        let base = tlx_testkit::spec::load(&src, "VIEW V\nINIT Init\nNEXT Next\n");
        let view = super::super::speculate::view_def(&base).unwrap();
        let mut servers = ["s1", "s2", "s3", "s4"].map(Sym::new);
        servers.sort();
        let orbits = AtomOrbits::from_factors(&[&servers]);
        let atoms = Shape::Atom(servers[..3].iter().copied().map(Value::ModelValue).collect());
        let key = Shape::Tuple(vec![atoms, Shape::Int { lo: 1, hi: 1200 }].into());
        let map = map_shape(key, Shape::Bool, FcnWitness::Enumerated);
        assert!(matches!(map, Shape::Map { .. }));
        assert_eq!(orbits.close(&map), Shape::Dyn);
        let candidate = |def| Prerun {
            shapes: vec![Shape::Bool],
            defs: vec![Some(def)],
            states: 1,
            settled: false,
            report: None,
            bounded: vec![(0, map.clone())],
        };
        let tuple = |x, y| Shape::Tuple(vec![x, y].into());
        let (vars, defs, _) = layouts(&base, &[view], candidate(tuple(Shape::Bool, map.clone())), &orbits);
        assert_eq!(vars, vec![Shape::Bool]);
        assert!(defs.is_empty());
        let (_, defs, _) = layouts(&base, &[view], candidate(tuple(map.clone(), Shape::Bool)), &orbits);
        assert_eq!(defs, vec![(view, tuple(Shape::Dyn, Shape::Bool))]);
        let base = tlx_testkit::spec::load(&src, "INIT Init\nNEXT Next\n");
        assert!(layouts(&base, &[view], candidate(map.clone()), &orbits).1.is_empty());
    }

    /// A checkpoint of an older speculation version is refused before its
    /// `Dyn` interner table is loaded; one of this version restores
    /// its table.
    #[test]
    fn checkpoints_of_other_speculation_versions_are_refused_first() {
        let src = tlx_testkit::module("S", "EXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1");
        let m = tlx_testkit::spec::load(&src, "INIT Init\nNEXT Next\n");
        let spec = Speculation {
            hints: hints(&m),
            shapes: vec![Shape::Int { lo: 0, hi: 3 }],
            def_shapes: Vec::new(),
            misses: vec![1],
            def_misses: Vec::new(),
            fallback: false,
            store: None,
            store_all: false,
            cache: crate::enc::cache::CompileCache::default(),
            closed: None,
            closure_refuted: false,
        };
        let shapes = spec.encode(4);
        let recover = |shapes: &[u8], dynv: &[u8], store: Option<&[u8]>, mode: StoreMode, escape: bool| {
            recovered_speculation(&m, mode, escape, usize::MAX, |name| match name {
                SPECULATION_FILE => Some(shapes),
                DYN_FILE => Some(dynv),
                STORE_FILE => store,
                _ => None,
            })
        };
        let table = |snap: &[Vec<tlx_value::Value>]| {
            let mut w = tlx_value::ser::Writer::new();
            tlx_layout::ser::write_dyn_table(&mut w, snap).unwrap();
            w.into_bytes()
        };
        let good_dyn = table(&tlx_layout::dynval::snapshot());
        // A table of no shards does not fit this build: refused when loaded.
        let bad = table(&[]);
        let Err(e) = recover(&shapes, &bad, None, StoreMode::Off, false) else { panic!("an interner table of no shards was restored") };
        assert!(e.contains("shards"), "{e}");
        // The current table (restoring it changes nothing): recovered.
        let (got, attempt) = recover(&shapes, &good_dyn, None, StoreMode::Off, false).unwrap();
        assert_eq!((got.shapes, got.misses, attempt), (spec.shapes.clone(), spec.misses.clone(), 4));
        assert!(got.store.is_none());
        // Stray model-store with StoreMode::Off is refused.
        let Err(e) = recover(&shapes, &good_dyn, Some(&[]), StoreMode::Off, false) else { panic!("stray model-store must be refused") };
        assert!(e.contains("unexpected value store"), "{e}");
        // Mode mismatches are refused before loading tables.
        let Err(e) = recover(&shapes, &bad, None, StoreMode::Dyn, false) else {
            panic!("StoreMode::Off checkpoint must be refused under StoreMode::Dyn")
        };
        assert!(e.contains("TLX_VALUE_STORE=0") && e.contains("TLX_VALUE_STORE=1"), "{e}");
        // StoreMode::Dyn checkpoint: requires matching mode and valid model-store.
        let mut store_spec = spec;
        let orig_store = StoreRef::new(usize::MAX);
        orig_store.freeze(&tlx_value::Value::tuple(vec![tlx_value::Value::Int(7)])).unwrap();
        store_spec.store = Some(orig_store.clone());
        let store_shapes = store_spec.encode(2);
        let mut sw = tlx_value::ser::Writer::new();
        tlx_layout::ser::write_store(&mut sw, &orig_store).unwrap();
        let store_bytes = sw.into_bytes();
        let Err(e) = recover(&store_shapes, &good_dyn, Some(&store_bytes), StoreMode::Off, false) else {
            panic!("StoreMode::Dyn checkpoint must be refused under StoreMode::Off")
        };
        assert!(e.contains("TLX_VALUE_STORE=1") && e.contains("TLX_VALUE_STORE=0"), "{e}");
        let Err(e) = recover(&store_shapes, &good_dyn, Some(&store_bytes), StoreMode::Off, true) else {
            panic!("StoreMode::Dyn checkpoint must be refused under TLX_ESCAPE=1")
        };
        assert!(e.contains("TLX_ESCAPE=1"), "{e}");
        let Err(e) = recover(&store_shapes, &good_dyn, None, StoreMode::Dyn, false) else { panic!("missing model-store must be refused") };
        assert!(e.contains("missing model-store"), "{e}");
        let (got, attempt) = recover(&store_shapes, &good_dyn, Some(&store_bytes), StoreMode::Dyn, false).unwrap();
        assert_eq!(attempt, 2);
        let restored = got.store.expect("restored store");
        assert_ne!(restored.uid(), orig_store.uid(), "restored store must allocate a fresh uid");
        assert_eq!(restored.stats().nodes, orig_store.stats().nodes);
        // Version 1: refused before the table is read.
        let mut old = shapes.clone();
        assert_eq!(old[0], SPECULATION_VERSION as u8);
        old[0] = 1;
        let Err(e) = recover(&old, &bad, None, StoreMode::Off, false) else { panic!("a checkpoint of version 1 was recovered") };
        assert_eq!(e, "the checkpoint's compiled-tier shapes are of version 1, this tlx reads version 4");
    }
}
