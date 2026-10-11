//! Prepare the model, dispatch the search and hand its report to `report::finish`.
//! Automatic-symmetry retries drop the entire first run before starting again.

use std::path::PathBuf;
use std::process::ExitCode;
use std::sync::Arc;
use std::time::Instant;

use tlx_eval::model::WarningKind;
use tlx_eval::InterpModel;
use tlx_runtime::{explore, ErrorContext, Model, Options, Outcome, Report};
use tlx_sema::Program;

use crate::args::{parse_args, Args};
use crate::out::code;
use crate::recovery::{checkpointer, identity_mismatch, print_start, run_identity};
use crate::report::{
    finish, live_branches, Run, EXIT_ASSUMPTION, EXIT_CONFIG_ERROR, EXIT_EVAL_ERROR, EXIT_GENERAL_ERROR, EXIT_LIVENESS_EVAL,
};
use crate::{autosym, coverage, live, load, out, process, recovery, settings, simulation, stats, symcheck};
use crate::{parse_only, print_finished, print_mode, PROGRESS_EVERY, PROGRESS_EVERY_SHORT};

pub(crate) fn check(started: Instant) -> ExitCode {
    let mut restart = false;
    let result = check_once(started, false, &mut restart);
    if !restart {
        return result;
    }
    // The first search and all its state stores have been dropped.
    out::clear_reduced();
    out::info(code::GENERAL, "Automatic symmetry runtime guard failed; restarting without automatic symmetry.");
    check_once(started, true, &mut false)
}

fn check_once(started: Instant, noautosymmetry: bool, restart: &mut bool) -> ExitCode {
    if std::env::args().nth(1).as_deref() == Some("optimize") {
        return crate::optimization::run();
    }
    if std::env::args().nth(1).as_deref() == Some("parse") {
        return parse_only();
    }
    let prepared = match prepare(started, noautosymmetry, restart) {
        Ok(prepared) => prepared,
        Err(code) => return code,
    };
    run(prepared, started, restart)
}

/// A fully configured model. Early diagnostics and non-search commands have
/// already completed; all model capabilities remain on the original model.
struct Prepared {
    args: Args,
    model: InterpModel,
    recovery: Option<tlx_runtime::Recovery>,
    seed: Option<u64>,
    check_deadlock: bool,
}

/// Preserve TLC's setup/error order: restore strings before loading, bind
/// checkpoint identity after symmetry, then validate literals and assumptions.
/// `Err` is an already reported exit, including successful non-search commands.
fn prepare(started: Instant, noautosymmetry: bool, restart: &mut bool) -> Result<Prepared, ExitCode> {
    let mut a = parse_args();
    a.noautosymmetry |= noautosymmetry;
    if let Some(o) = &a.stats {
        stats::enable(o.clone());
    }
    // The environment, read once (TLX_PATH after the -I directories,
    // TLX_CLASSPATH after the built-in modules).
    let ck_env;
    match settings::Env::from_env() {
        Ok(env) => {
            ck_env = (env.checkpoint_secs, env.checkpoint_states, env.checkpoint_abort);
            a.includes.extend(env.path);
            a.classpath.extend(env.classpath);
            a.queue = env.queue;
            a.queue_compress_given = env.queue_compress_given;
            a.maxmem = a.maxmem.or(env.maxmem);
            a.fp_table_min = env.fp_table_min;
            a.fp_spill_slots = env.fp_spill_slots;
            a.spill_cfg.mode = a.spill_mode.or(env.spill).unwrap_or_default();
            a.spill_cfg.dir = a.spill_cfg.dir.take().or(env.metadir);
            a.spill_cfg.maxdisk = a.spill_cfg.maxdisk.or(env.maxdisk);
            // (Before the front end allocates: pages faulted in before keep
            // their size.)
            process::set_huge_pages(env.thp, a.maxmem, a.workers);
            a.resolve_tier();
        }
        Err(e) => {
            eprintln!("tlx: {e}");
            return Err(ExitCode::from(2));
        }
    }
    if a.optimize
        && !a.tlc
        && (a.simulate.is_some()
            || a.checksymmetry
            || a.coverage.is_some()
            || a.recover.is_some()
            || a.checkpoint.is_some_and(|n| n > 0)
            || ck_env.0.is_some()
            || ck_env.1.is_some())
    {
        eprintln!("tlx: -optimize supports exhaustive checking without simulation, symmetry diagnostics, coverage or checkpoints");
        return Err(ExitCode::from(2));
    }
    let ck_interval = a.checkpoint_interval(ck_env.0);
    let recovery = recovery::prepare(&mut a)?;
    // (As TLC's default metadir: next to the specification.)
    a.spill_cfg.base = Some(a.spec.parent().filter(|p| !p.as_os_str().is_empty()).map_or_else(|| PathBuf::from("."), PathBuf::from));
    a.spill = tlx_runtime::io::Spill::new(a.spill_cfg.clone());
    out::set_tool(a.tool);
    out::set_nowarning(a.nowarning);
    out::info(code::TLC_VERSION, &format!("tlx version {}", env!("CARGO_PKG_VERSION")));
    let seed = a.simulate.map(|_| {
        a.seed.unwrap_or_else(|| {
            let t = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap_or_default();
            t.as_nanos() as u64 ^ (std::process::id() as u64) << 32
        })
    });
    if a.checksymmetry {
        out::info(code::GENERAL, "Running bounded symmetry checking with one interpreter worker.");
    } else {
        print_mode(&a, seed);
    }
    // (TLC's plain output does not show these.)
    if out::tool() {
        out::info(code::TLC_SANY_START, "Starting SANY...");
    }
    let model_seed = seed.or(a.seed).unwrap_or(0);
    let mut model = stats::timed("front end (parse, sema, cfg)", || load::load_model(&mut a, model_seed))?;
    if out::tool() {
        out::info(code::TLC_SANY_END, "SANY finished.");
    }
    // (Before the identity of a checkpoint, which records the symmetry.)
    let symmetry = match autosym::run(&mut model, &a, ck_env.0.is_none() && ck_env.1.is_none()) {
        Ok(s) => s,
        Err(code) => {
            print_finished(started);
            return Err(code);
        }
    };
    if model.ip.symmetry_guard_failed() {
        *restart = true;
        return Err(ExitCode::SUCCESS);
    }
    let check_deadlock = model.check_deadlock && !a.no_deadlock;
    let identity = run_identity(&a, &model, check_deadlock, seed.or(a.seed).unwrap_or(0), symmetry.as_ref());
    if let Some(r) = &recovery {
        if let Some(why) = identity_mismatch(r.identity(), &identity) {
            out::error(code::GENERAL, &format!("cannot recover from {}: {why}", a.recover.as_ref().expect("-recover").display()));
            return Err(ExitCode::from(EXIT_GENERAL_ERROR));
        }
    }
    if !a.checksymmetry && a.simulate.is_none() && a.dump.is_none() && model.ip.symmetry_guard_counts().is_none() {
        a.checkpointer = checkpointer(a.checkpoint.is_some(), ck_interval, ck_env, identity, recovery.is_some());
    }
    if !a.checksymmetry {
        model.live.tableau = live::tableau_atoms(&model);
    }
    model.ip.set_run_config(if a.checksymmetry { 1 } else { a.workers }, check_deadlock);
    if let (Some(traces), Some(seed)) = (a.simulate, seed) {
        model.ip.set_simulation(tlx_eval::SimConfig {
            generate: a.generate,
            // (TLC: the number of workers times num, as a Java int.)
            traces: (a.workers as i64).wrapping_mul(traces.min(i64::MAX as u64) as i64) as i32 as i64,
            depth: if a.depth == i32::MAX as u32 { -1 } else { a.depth as i64 },
            seed: seed as i64,
        });
    }
    out::info(code::TLC_STARTING, &format!("Starting... ({})", out::now()));
    if let (Some(note), false) = (&a.tier_note, a.checksymmetry) {
        tlx_base::diag::emit(tlx_base::diag::Topic::Compile, note);
    }
    warn_ignored_flags(&a);
    for w in &model.warnings {
        let c = match w.kind {
            WarningKind::LivenessSymmetry => code::TLC_FEATURE_UNSUPPORTED_LIVENESS_SYMMETRY,
            WarningKind::SubscriptWithoutVariable => code::TLC_SUBSCRIPT_CONTAIN_NO_STATE_VAR,
        };
        out::warning(c, &w.text);
    }
    // TLC rejects integer literals it cannot represent and real number
    // literals while it processes the specification.
    match bad_literal(&model.ip.prog) {
        Some(BadLiteral::Big(n)) => {
            out::error(code::TLC_INTEGER_TOO_BIG, &format!("TLC can't handle a number this big.\n{n}"));
            print_finished(started);
            return Err(ExitCode::from(EXIT_GENERAL_ERROR));
        }
        Some(BadLiteral::Real(d)) => {
            out::error(code::TLC_CANT_HANDLE_REAL_NUMBERS, &format!("TLC can't handle real numbers.\n{d}"));
            print_finished(started);
            return Err(ExitCode::from(EXIT_CONFIG_ERROR));
        }
        None => {}
    }
    // TLC (ModelChecker.modelCheckImpl) refuses temporal properties that
    // are tautologies before it checks the assumptions.
    if !a.checksymmetry && a.simulate.is_none() && !model.live.is_empty() && tlx_live::is_tautology(model.live.props.iter().map(|(_, f)| f))
    {
        out::error(code::TLC_LIVE_FORMULA_TAUTOLOGY, tlx_eval::model::TAUTOLOGY);
        print_finished(started);
        return Err(ExitCode::from(EXIT_LIVENESS_EVAL));
    }
    if let Err(e) = model.check_assumes() {
        if guard_restart(&model.ip, true, restart) {
            return Err(ExitCode::SUCCESS);
        }
        match &e.context {
            ErrorContext::Assumption(at) => {
                let text = format!("Evaluating assumption {at} failed.\n{}", out::nested(out::error_kind(&e), &e.message));
                out::error(code::TLC_ASSUMPTION_EVALUATION_ERROR, &text);
            }
            _ => out::error(code::TLC_ASSUMPTION_FALSE, &e.message),
        }
        print_finished(started);
        return Err(ExitCode::from(EXIT_ASSUMPTION));
    }
    if a.checksymmetry && a.suggest {
        return Err(symcheck::suggest(&model, &a.symmetry, started));
    }
    if a.checksymmetry {
        return Err(symcheck::run(&model, &a.symmetry, started));
    }
    warn_state_level_properties(&model);
    if !model.live.is_empty() {
        let text = format!("Implied-temporal checking--satisfiability problem has {} branches.", live_branches(&model));
        out::info(code::TLC_LIVE_IMPLIED, &text);
    }
    if !model.has_behavior {
        out::info(code::TLC_SUCCESS, "Model checking completed. No error has been found.");
        out::info(code::TLC_STATS, "0 states generated, 0 distinct states found, 0 states left on queue.");
        out::info(code::TLC_SEARCH_DEPTH, "The depth of the complete state graph search is 0.");
        print_finished(started);
        return Err(ExitCode::SUCCESS);
    }
    Ok(Prepared { args: a, model, recovery, seed, check_deadlock })
}

/// Dispatch simulation, init-only or BFS without wrapping the model. Each
/// completed search hands its original tier to `report::finish`.
fn run(prepared: Prepared, started: Instant, restart: &mut bool) -> ExitCode {
    let Prepared { args: a, mut model, recovery, seed, check_deadlock } = prepared;
    if let (Some(traces), Some(seed)) = (a.simulate, seed) {
        return simulation::run(&a, model, traces, seed, check_deadlock, started);
    }
    if model.no_next {
        // TLC (ModelChecker): with no next-state action it computes the
        // initial states and then, unless there are none, fails with
        // EC.TLC_STATES_AND_NO_NEXT_ACTION (exit 75).
        let opts = a.options(1, false);
        out::info(code::TLC_COMPUTING_INIT, "Computing initial states...");
        let r = explore(&model, &opts);
        if guard_restart(&model.ip, matches!(r.outcome, Outcome::Error(_)), restart) {
            return ExitCode::SUCCESS;
        }
        // (Unless the fingerprint set filled up while computing them: the
        // capacity error is the more accurate report, and `finish` gives it.)
        if r.stats.distinct > 0 && !matches!(r.outcome, Outcome::FpSetFull { .. }) {
            out::error(code::TLC_STATES_AND_NO_NEXT_ACTION, "No next state actions defined to generate successor states from.");
            print_finished(started);
            return ExitCode::from(EXIT_EVAL_ERROR);
        }
        let run = Run { workers: 1, actions: Vec::new(), started, sim: None, fp_mem: a.fp_mem(), opts: None, coverage: None };
        return finish(&model, r, &run);
    }
    let mut opts = a.options(a.workers, check_deadlock);
    let coverage = a.coverage.map(|interval| {
        // (Every tier enumerates the initial states with the interpreter,
        // which counts what Init rejects.)
        model.coverage = true;
        let table = Arc::new(coverage::Table::new(&model));
        opts.coverage = true;
        opts.coverage_report =
            Some(coverage::reporter(table.clone(), interval, if a.progress { PROGRESS_EVERY_SHORT } else { PROGRESS_EVERY }));
        table
    });
    // (The searches after the search take no checkpoints.)
    let run = Run {
        workers: opts.workers,
        actions: model.action_names().to_vec(),
        started,
        sim: None,
        fp_mem: a.fp_mem(),
        opts: Some(Options { checkpoint: None, ..opts.clone() }),
        coverage,
    };
    if a.compile {
        print_start(&recovery);
        let base = Arc::new(model);
        let (m, r) = match tlx_compile::enc::check_from(base.clone(), &opts, 16, recovery.as_ref()) {
            Ok(tlx_compile::enc::Checked::Compiled(m, r)) => (m, r),
            Ok(tlx_compile::enc::Checked::Interpreted(r)) => {
                if guard_restart(&base.ip, matches!(r.outcome, Outcome::Error(_)), restart) {
                    return ExitCode::SUCCESS;
                }
                // The pre-run was the search (in the interpreter).
                if a.dump.is_some() {
                    let dump_opts = Options { progress: None, coverage: false, coverage_report: None, checkpoint: None, ..opts.clone() };
                    explore_dumping(&*base, &dump_opts, &a.dump, None);
                }
                return finish(&*base, r, &run);
            }
            Err(e) => {
                if guard_restart(&base.ip, true, restart) {
                    return ExitCode::SUCCESS;
                }
                out::error(
                    code::GENERAL,
                    &match &a.recover {
                        Some(d) => format!("cannot recover from {}: {e}", d.display()),
                        None => e,
                    },
                );
                return ExitCode::from(EXIT_GENERAL_ERROR);
            }
        };
        if guard_restart(&base.ip, matches!(r.outcome, Outcome::Error(_)), restart) {
            return ExitCode::SUCCESS;
        }
        if a.dump.is_some() {
            // The compiled search may restart; dump with a final search
            // (with the interpreter if it misses: it cannot restart).
            let dump_opts = Options { progress: None, coverage: false, coverage_report: None, checkpoint: None, ..opts.clone() };
            let d = explore_dumping(&m, &dump_opts, &a.dump, None);
            if matches!(&d.outcome, Outcome::Error(e) if e.is_layout_miss()) {
                tlx_base::diag::emit(tlx_base::diag::Topic::Compile, "layout miss writing the -dump file; writing it with the interpreter");
                explore_dumping(&*m.base, &dump_opts, &a.dump, None);
            }
        }
        return finish(&m, r, &run);
    }
    print_start(&recovery);
    let r = explore_dumping(&model, &opts, &a.dump, recovery.as_ref());
    if guard_restart(&model.ip, matches!(r.outcome, Outcome::Error(_)), restart) {
        return ExitCode::SUCCESS;
    }
    finish(&model, r, &run)
}

/// Never publish a report from a search whose runtime proof failed.
fn guard_restart(ip: &tlx_eval::Interp, error: bool, restart: &mut bool) -> bool {
    if let Some((calls, candidates)) = ip.symmetry_guard_counts() {
        tlx_runtime::stats::set_section(
            "symmetry guards",
            format!("interpreter: {calls} evaluations, {candidates} candidates; native guards use IR loops\n"),
        );
    }
    *restart = ip.symmetry_guard_failed() || (error && ip.symmetry_guard_counts().is_some());
    *restart
}

/// Explore (from checkpoint `recover` if given), writing the states to the
/// `-dump` file if requested.
fn explore_dumping<M: Model>(
    m: &M,
    opts: &Options,
    dump: &Option<(PathBuf, tlx_runtime::DumpOptions)>,
    recover: Option<&tlx_runtime::Recovery>,
) -> Report<M::State> {
    if let Some(r) = recover {
        return tlx_runtime::explore_from(m, opts, tlx_runtime::Start::Recover(r), None).0;
    }
    let Some((path, o)) = dump else { return explore(m, opts) };
    let o = tlx_runtime::DumpOptions { reduced: out::reduced(), ..*o };
    let dump = match tlx_runtime::DumpObserver::create(m, path, o) {
        Ok(d) => d,
        Err(e) => {
            out::warning(code::GENERAL, &format!("cannot write {}: {e}", path.display()));
            return explore(m, opts);
        }
    };
    let r = tlx_runtime::explore_observed(m, opts, &dump);
    if let Err(e) = dump.finish() {
        out::warning(code::GENERAL, &format!("cannot write {}: {e}", path.display()));
    }
    r
}

/// An integer literal of the specification that does not fit in TLC's
/// 32-bit integers, if any.
enum BadLiteral {
    Big(i128),
    Real(std::sync::Arc<str>),
}

fn bad_literal(prog: &Program) -> Option<BadLiteral> {
    use tlx_sema::hir::{DefKind, Expr, ExprKind};
    fn find(e: &Expr) -> Option<BadLiteral> {
        match &*e.kind {
            ExprKind::Num(n) if *n > i32::MAX as i128 => return Some(BadLiteral::Big(*n)),
            ExprKind::Decimal(d) => return Some(BadLiteral::Real(d.clone())),
            _ => {}
        }
        let mut found = None;
        tlx_sema::visit::children(e, &mut |c| {
            if found.is_none() {
                found = find(c);
            }
        });
        found
    }
    let bodies = prog.defs.iter().flat_map(|d| match &d.kind {
        DefKind::Op(body) => vec![body],
        DefKind::Fn { bounds, body } => bounds.iter().map(|b| &b.set).chain([body]).collect(),
        DefKind::Pending => vec![],
    });
    bodies.chain(&prog.assumes).find_map(find)
}

/// TLC's warning about PROPERTYs that are state predicates (only checked
/// on the initial states).
fn warn_state_level_properties(model: &InterpModel) {
    let parts = model.spec_parts();
    let temporal: Vec<&String> =
        parts.implied_invariants.iter().chain(&parts.implied_actions).chain(&parts.implied_temporals).map(|(n, _)| n).collect();
    for name in &model.ip.cfg.properties {
        // State-level: all its parts are checked on the initial states.
        if parts.implied_inits.iter().any(|(n, _)| n == name) && !temporal.contains(&name) {
            out::warning(
                code::TLC_LIVE_FORMULA_STATE_LEVEL,
                &format!("The formula {name} is a state-level formula, but it was used as a PROPERTY (or PROPERTIES), where a temporal formula is typically expected. State-level formulas used as PROPERTY or PROPERTIES are only checked in the initial state. To verify that the formula {name} holds in all states of every behavior, use INVARIANT {name} instead. Alternatively, applying the \"always\" temporal operator ([]) to the state-level formula {name} changes it into a temporal formula, asserting that {name} holds in all states of every behavior. See https://explain.tlapl.us/invariants-and-properties for additional details."),
            );
        }
    }
}

/// Warn about options that have no effect in the selected mode.
fn warn_ignored_flags(a: &Args) {
    let simulation = a.simulate.is_some();
    if a.dump.is_some() && simulation {
        out::warning(code::GENERAL, "-dump has no effect with -simulate or -generate.");
    }
    if a.coverage.is_some() && simulation {
        out::warning(code::GENERAL, "-coverage has no effect with -simulate or -generate (tlx).");
    }
    if !simulation && a.depth_given {
        out::warning(code::GENERAL, "-depth has no effect without -simulate or -generate.");
    }
}
