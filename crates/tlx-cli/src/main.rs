//! `tlx check Spec.tla [-config Spec.cfg] [-workers N] [-deadlock] [-I dir]...`
//! (`tlx check -h`, `settings::help`, and docs/configuration.md list all
//! options and environment variables).
//!
//! Output mimics TLC's so that scripts/difftest.py can compare the two;
//! with `-tool` the messages are wrapped as TLC's `-tool` does.

use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

use tier::Tier;
use tlx_eval::InterpModel;
use tlx_runtime::{ErrorContext, ErrorKind, LiveStats, Model, ModelError, Options, Outcome, Progress, Report, SimProgress};

use args::*;
use out::code;
use simulation::print_sim_progress;

/// TLC reports progress 3 seconds after the start of the search, then
/// every minute (TLCGlobals.progressInterval).
const PROGRESS_FIRST: Duration = Duration::from_secs(3);
const PROGRESS_EVERY: Duration = Duration::from_secs(60);
/// The interval with `-progress`.
const PROGRESS_EVERY_SHORT: Duration = Duration::from_secs(10);

mod abstraction;
mod args;
mod autosym;
mod check;
mod coverage;
mod dump_trace;
mod live;
mod load;
mod out;
mod process;
mod recovery;
mod report;
mod settings;
mod simulation;
mod stats;
mod symcheck;
mod tier;

/// The message code and text of a configuration `<-` substitution error
/// (TLC's `SpecProcessor.processSpec`).
fn cfg_subst_error(e: &tlx_sema::CfgSubstError) -> (u32, String) {
    use tlx_sema::CfgSubstError::*;
    match e {
        RhsAppearedAfterLhs(rhs) => (
            code::TLC_CONFIG_RHS_ID_APPEARED_AFTER_LHS_ID,
            format!("In the configuration file, the identifier {rhs} appears\non the right-hand side of a <- after already appearing on the\nleft-hand side of a <-."),
        ),
        WrongSubstitution { lhs, rhs } => (
            code::TLC_CONFIG_WRONG_SUBSTITUTION,
            format!("The configuration file substitutes for {lhs} with the undefined identifier {rhs}."),
        ),
        WrongNumberOfArgs { lhs, rhs } => (
            code::TLC_CONFIG_WRONG_SUBSTITUTION_NUMBER_OF_ARGS,
            format!("The configuration file substitutes for {lhs} with {rhs} of different number of arguments."),
        ),
        IdDoesNotAppear(name) => (
            code::TLC_CONFIG_ID_DOES_NOT_APPEAR_IN_SPEC,
            format!("In the configuration file, the identifier {name} does not appear in the specification."),
        ),
        NoModules(m) => (
            code::TLC_NO_MODULES,
            format!("In the configuration file, the module name {m} is not a module in the specification."),
        ),
    }
}

/// The message code and text of a name the configuration refers to that is
/// not a 0-ary operator definition (TLC's `SpecProcessor.processConfig`).
fn cfg_name_error(e: &tlx_sema::CfgNameError) -> (u32, String) {
    use tlx_sema::CfgNameError::*;
    match e {
        NotDefined { what, name } => (
            code::TLC_CONFIG_SPECIFIED_NOT_DEFINED,
            format!("The {what} {name} specified in the configuration file\nis not defined in the specification."),
        ),
        RequiresNoArg { what, name } => {
            (code::TLC_CONFIG_ID_REQUIRES_NO_ARG, format!("The {what} {name} specified in the configuration file requires arguments."))
        }
        IsConstant { what, name } => {
            // TLC tells a constant used as INIT/NEXT (2233) from one used as
            // an invariant or a specification name (2230).
            let c = if matches!(*what, "initial predicate" | "next state action") {
                code::TLC_CONFIG_ID_MUST_NOT_BE_CONSTANT
            } else {
                code::TLC_CONFIG_ID_HAS_VALUE
            };
            (c, format!("The {what} {name} specified in the configuration file is a constant with a value."))
        }
        NotBothSpecAndInit => (
            code::TLC_CONFIG_NOT_BOTH_SPEC_AND_INIT,
            "The configuration file specifies both a SPECIFICATION and an INIT or NEXT.".to_string(),
        ),
    }
}

/// "Finished in 01min 05s at (2024-01-31 13:45:00)".
fn print_finished(started: Instant) {
    out::info(code::TLC_FINISHED, &format!("Finished in {} at ({})", out::duration(started.elapsed()), out::now()));
}

/// The line TLC starts with: the mode of the run and the machine.
fn print_mode(a: &Args, seed: Option<u64>) {
    let cores = std::thread::available_parallelism().map_or(1, |n| n.get());
    let workers = format!("{} worker{}", a.workers, if a.workers == 1 { "" } else { "s" });
    let machine =
        format!("[pid: {}] ({} {}, tlx {})", std::process::id(), std::env::consts::OS, std::env::consts::ARCH, env!("CARGO_PKG_VERSION"));
    match seed {
        Some(seed) => out::info(
            code::TLC_MODE_SIMU,
            &format!("Running Random Simulation with seed {} with {workers} on {cores} cores {machine}.", seed as i64),
        ),
        None => out::info(
            code::TLC_MODE_MC,
            &format!("Running breadth-first search Model-Checking with fp 0 and seed {} with {workers} on {cores} cores with {}MB fingerprint memory {machine}.", a.seed.unwrap_or(0) as i64, a.fp_mib()),
        ),
    }
}

/// The sink of the progress stream of the compiled tier (`tlx_base::diag`):
/// with `-tool`, stdout carries only TLC's framed messages, so it goes to
/// stderr.
fn progress_line(line: &str) {
    if out::tool() {
        eprintln!("{line}");
    } else {
        println!("{line}");
    }
}

/// "Finished computing initial states: ...".
fn print_init_done(generated: u64, distinct: u64) {
    let now = out::now();
    if generated == distinct {
        let s = if distinct == 1 { "" } else { "s" };
        out::info(
            code::TLC_INIT_GENERATED1,
            &format!("Finished computing initial states: {distinct} distinct state{s} generated at {now}."),
        );
    } else {
        out::info(
            code::TLC_INIT_GENERATED2,
            &format!("Finished computing initial states: {generated} states generated, with {distinct} of them distinct at {now}."),
        );
    }
}

/// TLC's progress line; the rates (per minute) are optional.
fn print_progress(depth: u64, generated: u64, distinct: u64, queue: u64, rates: Option<(u64, u64)>) {
    use out::commas;
    let (g, d) = match rates {
        Some((gr, dr)) => (format!(" ({} s/min)", commas(gr)), format!(" ({} ds/min)", commas(dr))),
        None => (String::new(), String::new()),
    };
    out::info(
        code::TLC_PROGRESS_STATS,
        &format!(
            "Progress({depth}) at {}: {} states generated{g}, {} distinct states found{d}, {} states left on queue.",
            out::now(),
            commas(generated),
            commas(distinct),
            commas(queue)
        ),
    );
}

/// Periodic progress reports during the search, as TLC: the rates are the
/// increase since the previous report, per minute.
fn progress_reporter(every: Duration) -> Progress {
    let last = Mutex::new((0u64, 0u64));
    let minutes = every.as_secs_f64() / 60.0;
    let init_printed = AtomicBool::new(false);
    Progress {
        first: PROGRESS_FIRST,
        every,
        report: Arc::new(move |l: &LiveStats| {
            let mut last = last.lock().unwrap();
            let rate = |now: u64, before: u64| (now.saturating_sub(before) as f64 / minutes) as u64;
            let rates = (rate(l.generated, last.0), rate(l.distinct, last.1));
            *last = (l.generated, l.distinct);
            print_progress(l.diameter, l.generated, l.distinct, l.queue, Some(rates));
        }),
        // A compiled search may restart: reported once.
        init_done: Arc::new(move |generated, distinct| {
            if !init_printed.swap(true, Ordering::Relaxed) {
                print_init_done(generated, distinct);
            }
        }),
    }
}

fn main() -> ExitCode {
    tlx_base::stack::install_current().expect("failed to install stack-overflow fallback");
    tlx_base::diag::install_progress(progress_line);
    // Signals, the panic hook and the allocator (mimalloc): the process-wide
    // setup lives in `process`, which `main` runs before any other thread or
    // parse exists.
    process::init();
    let started = Instant::now();
    // Evaluate on a thread with the large stack that deep recursion (and the
    // recursion guard in tlx-eval) needs: the OS gives the main thread a
    // smaller, fixed stack. `check` and the statistics live on that thread.
    tlx_base::stack::run_on_named_stack(tlx_base::stack::EVAL_STACK_SIZE, Some("tlx"), move || {
        let code = check::check(started);
        stats::finish(started);
        code
    })
}

/// Documentation syntax checks need neither module resolution nor a model configuration.
fn parse_only() -> ExitCode {
    let args: Vec<_> = std::env::args_os().skip(2).collect();
    let [path] = args.as_slice() else {
        eprintln!("usage: tlx parse Spec.tla");
        return ExitCode::from(2);
    };
    let source = match std::fs::read_to_string(path) {
        Ok(source) => source,
        Err(error) => {
            eprintln!("{}: {error}", Path::new(path).display());
            return ExitCode::from(2);
        }
    };
    match tlx_front::parse::parse_modules(&source, tlx_front::ast::FileId(0)) {
        Ok(_) => ExitCode::SUCCESS,
        Err(errors) => {
            for error in errors {
                eprintln!("{}:{error}", Path::new(path).display());
            }
            ExitCode::from(1)
        }
    }
}
