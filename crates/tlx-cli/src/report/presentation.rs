//! TLC-style outcome, trace and statistics presentation, in reporting order.

use super::diagnostic::{error_report, fp_set_full};
use super::*;

pub(super) type SavedTrace = [(Arc<[tlx_value::Value]>, Option<u32>)];

/// Print the result TLC-style and return TLC's exit code.
/// `view` shows the states and labels the steps of a trace.
pub(super) fn report<T: Tier>(
    r: Report<T::State>,
    saved_trace: Option<&SavedTrace>,
    live: Option<(live::Liveness, Duration)>,
    post: Option<(u32, String)>,
    view: &live::TraceView<T::State>,
    run: &Run,
    dump: &dyn Fn(),
) -> ExitCode {
    let (code, success, post_failed) = outcome::<T>(&r, saved_trace, &live, &post, view, run);
    let incomplete = trace::<T>(&r, saved_trace, view);
    // (TLC's -dumpTrace postconditions, before the statistics.)
    dump();
    // (A simulation reports the POSTCONDITION after the statistics.)
    if let (Outcome::Deadlock, Some((c, msg)), None) = (&r.outcome, &post, &run.sim) {
        out::error(*c, msg);
    }
    statistics(&r, &post, run, incomplete, code, success, post_failed)
}

/// Report the outcome before any behavior or final statistics.
/// Keep every outcome explicit: names, messages and exit codes belong together.
fn outcome<T: Tier>(
    r: &Report<T::State>,
    saved_trace: Option<&SavedTrace>,
    live: &Option<(live::Liveness, Duration)>,
    post: &Option<(u32, String)>,
    view: &live::TraceView<T::State>,
    run: &Run,
) -> (u8, bool, bool) {
    let liveness_done = |d: Duration| {
        out::info(
            code::TLC_CHECKING_TEMPORAL_PROPS_END,
            &format!("Finished checking temporal properties in {} at {}", out::duration(d), out::now()),
        );
    };
    let temporal_violation = |properties: &[String], counterexample: &str| {
        out::error(code::TLC_TEMPORAL_PROPERTY_VIOLATED, &live::violation_message(properties));
        print!("{counterexample}");
    };
    let mut success = false;
    let mut post_failed = false;
    let code = match &r.outcome {
        Outcome::Ok => {
            match &live {
                Some((live::Liveness::Violated(name, trace), d)) => {
                    temporal_violation(name, trace);
                    liveness_done(*d);
                    EXIT_LIVENESS
                }
                Some((live::Liveness::Error(e), d)) => {
                    out::error(out::error_code(&e.message), &e.message);
                    liveness_done(*d);
                    EXIT_EVAL_ERROR
                }
                // A resource limit of the run, as a full fingerprint set.
                Some((live::Liveness::OutOfMemory(msg), _)) => {
                    out::error(code::GENERAL, msg);
                    EXIT_GENERAL_ERROR
                }
                _ => {
                    if let Some((_, d)) = &live {
                        liveness_done(*d);
                    }
                    match &post {
                        Some((c, msg)) => {
                            out::error(*c, msg);
                            post_failed = true;
                            EXIT_ASSUMPTION
                        }
                        None if run.sim.is_some() => 0,
                        None => {
                            success = true;
                            // TLC's optimistic estimate of a fingerprint collision.
                            let (n, g) = (r.stats.distinct as f64, r.stats.generated as f64);
                            let p = n * (g - n).max(0.0) / 2f64.powi(64);
                            out::info(
                                code::TLC_SUCCESS,
                                &format!(
                                    "Model checking completed. No error has been found.\n  Estimates of the probability that TLC did not check all reachable states\n  because two distinct states had the same fingerprint:\n  calculated (optimistic):  val = {}",
                                    out::probability(p)
                                ),
                            );
                            0
                        }
                    }
                }
            }
        }
        Outcome::InvariantViolated(name) if r.in_init => {
            let state = match saved_trace {
                Some(saved) => saved.first().map(|(v, _)| view.show_values(0, v, None, None)).unwrap_or_default(),
                None => r.trace.first().map(|t| view.show(0, &t.state, None, None)).unwrap_or_default(),
            };
            out::error(code::TLC_INVARIANT_VIOLATED_INITIAL, &format!("Invariant {name} is violated by the initial state:\n{state}\n"));
            EXIT_INVARIANT
        }
        Outcome::InvariantViolated(name) => {
            out::error(code::TLC_INVARIANT_VIOLATED_BEHAVIOR, &format!("Invariant {name} is violated."));
            EXIT_INVARIANT
        }
        Outcome::TemporalViolated { properties, counterexample } => {
            temporal_violation(properties, counterexample);
            // A violation found during the search (a finite prefix that
            // reaches an accepting sink of the tableau): TLC reports it with
            // the error state of a safety violation
            // (LiveCheck.printErrorTrace: setErrState(..,
            // TLC_INVARIANT_VIOLATED_BEHAVIOR)), so it exits with
            // VIOLATION_SAFETY; a simulation's with VIOLATION_LIVENESS.
            if run.sim.is_some() {
                EXIT_LIVENESS
            } else {
                EXIT_INVARIANT
            }
        }
        Outcome::InitPropertyViolated(label) => {
            // TLC shows just the state (no behavior).
            let state = match saved_trace {
                Some(saved) => saved.first().map(|(v, _)| view.show_values(0, v, None, None)).unwrap_or_default(),
                None => r.trace.first().map(|t| view.show(0, &t.state, None, None)).unwrap_or_default(),
            };
            out::error(code::TLC_PROPERTY_VIOLATED_INITIAL, &format!("Property {label} is violated by the initial state:\n{state}\n"));
            EXIT_LIVENESS
        }
        Outcome::ActionPropertyViolated(name) => {
            out::error(code::TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR, &format!("Action property {name} is violated."));
            EXIT_LIVENESS
        }
        Outcome::Deadlock => {
            out::error(code::TLC_DEADLOCK_REACHED, "Deadlock reached.");
            EXIT_DEADLOCK
        }
        // A full fingerprint set is a resource limit, not a violation of the
        // specification: no behavior (it can have tens of thousands of
        // states), a system-error exit status.
        Outcome::FpSetFull { entries } => {
            out::error(code::GENERAL, &fp_set_full(run.fp_mem, r.stats.distinct, *entries));
            EXIT_GENERAL_ERROR
        }
        // The disk layer failed (writing, a full disk, -maxdisk): a
        // resource failure too.
        Outcome::Io(msg) => {
            out::error(code::GENERAL, &format!("The search stopped: {msg}"));
            EXIT_GENERAL_ERROR
        }
        Outcome::NoInitInConstraint => {
            out::error(
                code::TLC_NO_STATES_SATISFYING_INIT_AND_CONSTRAINT,
                "There is no state satisfying the initial state predicate and the state-constraint(s).",
            );
            EXIT_GENERAL_ERROR
        }
        Outcome::Error(e) => {
            let (c, text, exit) = error_report(e, r.in_init, run);
            out::error(c, &text);
            exit
        }
    };
    (code, success, post_failed)
}

/// Print a behavior, preserving any note that limits its completeness.
/// Return an incomplete successor for the statistics suppression rules.
fn trace<'a, T: Tier>(
    r: &'a Report<T::State>,
    saved_trace: Option<&SavedTrace>,
    view: &live::TraceView<T::State>,
) -> Option<(Option<u32>, &'a String)> {
    let incomplete = match &r.outcome {
        Outcome::Error(ModelError { context: ErrorContext::IncompleteState { action, state, .. }, .. }) => Some((*action, state)),
        _ => None,
    };
    // (No behavior for a failure on an initial state: TLC shows the state.)
    let state_only = r.in_init && matches!(r.outcome, Outcome::InvariantViolated(_) | Outcome::Error(_))
        || matches!(r.outcome, Outcome::InitPropertyViolated(_));
    if let Some(note) = &r.trace_note {
        println!("{note}");
    }
    let trace_len = saved_trace.map_or(r.trace.len(), |s| s.len());
    if trace_len > 0 && !state_only {
        out::error(code::TLC_BEHAVIOR_UP_TO_THIS_POINT, "The behavior up to this point is:");
        let mut text = String::new();
        if let Some(saved) = saved_trace {
            for (i, (vals, action)) in saved.iter().enumerate() {
                let next = saved.get(i + 1).map(|(v, _)| v);
                text += &view.step_values(i, &view.label(*action), vals, next, *action);
            }
        } else {
            for (i, step) in r.trace.iter().enumerate() {
                let next = r.trace.get(i + 1).map(|t| &t.state);
                text += &view.step(i, &view.label(step.action), &step.state, next, step.action);
            }
        }
        // The incomplete successor ends the behavior.
        if let (None, Some((Some(a), state))) = (&r.trace_note, incomplete) {
            text += &out::state(trace_len + 1, &view.label(Some(a)), state);
        }
        print!("{text}");
    }
    incomplete
}

/// Final simulation/search statistics and the finish message. Simulation's
/// POSTCONDITION and initial-state failures have distinct reporting orders.
fn statistics<S>(
    r: &Report<S>,
    post: &Option<(u32, String)>,
    run: &Run,
    incomplete: Option<(Option<u32>, &String)>,
    mut code: u8,
    success: bool,
    post_failed: bool,
) -> ExitCode {
    if let (Some(sim), true) = (&run.sim, r.in_init) {
        // TLC's simulator reports nothing more after a violation by an
        // initial state (or an incomplete one); after an error, the states
        // generated.
        if incomplete.is_none() && matches!(r.outcome, Outcome::Error(_)) {
            if out::tool() {
                print_sim_progress(&sim.progress);
            }
            let stats =
                format!("The number of states generated: {}\nSimulation using seed {} and aril 0", r.stats.generated, sim.seed as i64);
            out::info(code::TLC_STATS_SIMU, &stats);
        }
        print_finished(run.started);
        return ExitCode::from(code);
    }
    if let Some(sim) = &run.sim {
        let stats = format!("The number of states generated: {}\nSimulation using seed {} and aril 0", r.stats.generated, sim.seed as i64);
        let progress = &sim.progress;
        // TLC's order (its progress reporter thread ends the run); no
        // statistics after the POSTCONDITION failed.
        if post_failed {
            print_sim_progress(progress);
        } else if code == 0 {
            if out::tool() {
                print_sim_progress(progress);
            }
            print_sim_progress(progress);
            out::info(code::TLC_STATS_SIMU, &stats);
        } else {
            if out::tool() {
                print_sim_progress(progress);
            }
            out::info(code::TLC_STATS_SIMU, &stats);
            // After a failure, TLC's simulator still checks the
            // POSTCONDITION; the more severe exit status wins.
            if let (false, Some((c, msg))) = (matches!(r.outcome, Outcome::Ok), &post) {
                out::error(*c, msg);
                code = code.max(if *c == code::TLC_POSTCONDITION_FALSE { EXIT_ASSUMPTION } else { EXIT_EVAL_ERROR });
            }
            print_sim_progress(progress);
        }
        print_finished(run.started);
        return ExitCode::from(code);
    }
    // TLC reports no statistics after a violation by an initial state (but
    // does after an error, unless the state is incomplete).
    if !r.in_init || matches!(r.outcome, Outcome::Error(_)) && incomplete.is_none() {
        // (TLC's coverage statistics come before the search's.)
        if let (Some(table), Some(c)) = (&run.coverage, &r.coverage) {
            print!("{}", table.render(c, run.started.elapsed()));
        }
        let st = &r.stats;
        if out::tool() {
            // The final progress report, with the rates over the whole run.
            let minutes = r.elapsed.as_secs_f64().max(1e-3) / 60.0;
            let rates = ((st.generated as f64 / minutes) as u64, (st.distinct as f64 / minutes) as u64);
            print_progress(st.depth.max(u32::from(r.in_init)) as u64, st.generated, st.distinct, st.left, Some(rates));
        }
        out::info(
            code::TLC_STATS,
            &format!(
                "{} states generated, {} distinct states found, {} states left on queue{}.",
                st.generated,
                st.distinct,
                st.left,
                out::reduced_suffix()
            ),
        );
        out::info(code::TLC_SEARCH_DEPTH, &format!("The depth of the complete state graph search is {}.", st.depth));
        // (Also after an invariant failed to evaluate.)
        let invariant_error = matches!(&r.outcome, Outcome::Error(e) if matches!(e.context, ErrorContext::Invariant(_))) && !r.in_init;
        if success || invariant_error {
            let o = &st.outdegree;
            out::info(
                code::TLC_STATE_GRAPH_OUTDEGREE,
                &format!(
                    "The average outdegree of the complete state graph is {} (minimum is {}, the maximum {} and the 95th percentile is {}).",
                    o.mean, o.min, o.max, o.p95
                ),
            );
        }
    }
    print_finished(run.started);
    ExitCode::from(code)
}
