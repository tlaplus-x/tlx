//! Seeded interpreter and compiled simulation, progress and temporal checks.

use std::process::ExitCode;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::Instant;

use tlx_eval::InterpModel;
use tlx_runtime::{Model, ModelError, Outcome, Report, SimPhase, SimProgress};

use crate::args::Args;
use crate::out::code;
use crate::report::{finish, Run, Sim, EXIT_GENERAL_ERROR};
use crate::tier::Tier;
use crate::{live, out, PROGRESS_EVERY, PROGRESS_EVERY_SHORT};

/// The simulation progress line: TLC's own format with `-tool`.
pub(crate) fn print_sim_progress(p: &SimProgress) {
    let text = if out::tool() {
        format!(
            "Progress({}) at {}: {} states generated, -1 distinct states found, -1 states left on queue.",
            p.traces,
            out::now(),
            p.generated
        )
    } else {
        let (mean, var, sd) = p.length_stats();
        format!(
            "Progress: {} states checked, {} traces generated (trace length: mean={mean}, var(x)={var}, sd={sd})",
            p.generated, p.traces
        )
    };
    out::info(code::TLC_PROGRESS_SIMU, &text);
}

/// `-simulate`: random behaviors, with the interpreter or (`-compile`) the
/// compiled tier.
pub(crate) fn run(a: &Args, model: InterpModel, traces: u64, seed: u64, check_deadlock: bool, started: Instant) -> ExitCode {
    let opts = tlx_runtime::SimOptions { workers: a.workers, check_deadlock, traces, depth: a.depth, seed, generate: a.generate };
    let init_printed = AtomicBool::new(false);
    if a.compile {
        // A layout miss restarts the simulation (with the same seed).
        let mut run = |m: &tlx_compile::enc::EncModel| run_simulation(a, m, &opts, &init_printed);
        let (m, r, p) = match tlx_compile::enc::simulate(Arc::new(model), a.depth, seed, 16, &mut run) {
            Ok(result) => result,
            Err(e) => {
                out::error(code::GENERAL, &e);
                return ExitCode::from(EXIT_GENERAL_ERROR);
            }
        };
        let run = Run {
            workers: a.workers,
            actions: m.base.action_names().to_vec(),
            started,
            sim: Some(Sim { seed, init_label: m.base.init_label(), progress: p }),
            fp_mem: a.fp_mem(),
            opts: None,
            coverage: None,
            checkpoint: None,
        };
        return finish(&m, r, &run);
    }
    let (r, p) = run_simulation(a, &model, &opts, &init_printed);
    let run = Run {
        workers: a.workers,
        actions: model.action_names().to_vec(),
        started,
        sim: Some(Sim { seed, init_label: model.init_label(), progress: p }),
        fp_mem: a.fp_mem(),
        opts: None,
        coverage: None,
        checkpoint: None,
    };
    finish(&model, r, &run)
}

/// Simulate `m` (a model of `base`), reporting progress (the initial states
/// once: see `init_printed`); returns the report and the last progress.
fn run_simulation<T: Tier>(a: &Args, m: &T, opts: &tlx_runtime::SimOptions, init_printed: &AtomicBool) -> (Report<T::State>, SimProgress) {
    let base = m.base();
    // Progress every minute (TLC's Simulator.ProgressReport).
    let every = if a.progress { PROGRESS_EVERY_SHORT } else { PROGRESS_EVERY };
    let last = Mutex::new((SimProgress::default(), every));
    let progress = |p: tlx_runtime::SimProgress| {
        let (level_mean, level_variance, _) = p.length_stats();
        base.ip.set_final_stats(tlx_eval::RunStats {
            distinct: p.generated,
            generated: p.generated,
            queue: 0,
            diameter: p.diameter as u64,
            duration_secs: p.elapsed.as_secs(),
            initial: 0,
            traces: Some(p.traces),
            level_mean,
            level_variance,
        });
        let mut last = last.lock().unwrap();
        match p.phase {
            SimPhase::InitComputed => {
                if !init_printed.load(Ordering::Relaxed) {
                    out::info(code::TLC_COMPUTING_INIT_PROGRESS, &format!("Computed {} initial states...", p.init_generated));
                }
                return;
            }
            // (TLC's simulator always says "state".)
            SimPhase::InitDone => {
                if init_printed.swap(true, Ordering::Relaxed) {
                    return;
                }
                out::info(
                    code::TLC_INIT_GENERATED1,
                    &format!("Finished computing initial states: {} distinct state generated at {}.", p.init_distinct, out::now()),
                )
            }
            SimPhase::Running => {}
        }
        if p.traces >= last.0.traces {
            last.0 = p;
        }
        if p.elapsed >= last.1 {
            last.1 = p.elapsed + every;
            print_sim_progress(&p);
        }
    };
    // Temporal properties are checked on every behavior.
    let check = |trace: &[tlx_runtime::TraceStep<T::State>], succs: &[Vec<(T::State, u32)>]| {
        let steps: Vec<_> = trace.iter().map(|t| (t.state.clone(), t.action)).collect();
        let view = live::TraceView::new(m, base.init_label());
        // TLC's algorithm (LiveCheck1), also without VIEW or SYMMETRY: its
        // verdicts differ from those on the behavior's graph (e.g. it
        // evaluates the state predicates of a node on the previous state).
        let lv = live::check_trace(m, &steps, succs, &view);
        match lv {
            live::Liveness::Holds => None,
            live::Liveness::Violated(properties, counterexample) => Some(Outcome::TemporalViolated { properties, counterexample }),
            // (By the message only, as TLC reports errors of the liveness
            // checks of a simulation.)
            live::Liveness::Error(ModelError { message, .. }) | live::Liveness::OutOfMemory(message) => {
                Some(Outcome::Error(message.into()))
            }
        }
    };
    let check_trace: Option<&tlx_runtime::simulate::TraceCheck<_>> = (!base.live.is_empty()).then_some(&check);
    let r = tlx_runtime::simulate(m, opts, &progress, check_trace);
    let mut p = last.into_inner().unwrap().0;
    p.generated = r.stats.generated;
    (r, p)
}
