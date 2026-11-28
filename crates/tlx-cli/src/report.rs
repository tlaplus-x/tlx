//! The end of a run: liveness and POSTCONDITION after the search, then
//! the TLC-style report of the outcome, its message codes and TLC's exit
//! status.

use super::*;

mod diagnostic;
mod presentation;

use presentation::report;

/// Exit codes (TLC's `EC.ExitStatus`).
/// VIOLATION_ASSUMPTION: an assumption or the POSTCONDITION is violated.
pub(crate) const EXIT_ASSUMPTION: u8 = 10;
pub(crate) const EXIT_DEADLOCK: u8 = 11;
pub(crate) const EXIT_INVARIANT: u8 = 12;
/// VIOLATION_LIVENESS (also an action property violated by a simulation).
pub(crate) const EXIT_LIVENESS: u8 = 13;
/// VIOLATION_ASSERT.
pub(crate) const EXIT_ASSERT: u8 = 14;
/// FAILURE_SPEC_EVAL.
pub(crate) const EXIT_EVAL_ERROR: u8 = 75;
/// FAILURE_LIVENESS_EVAL (e.g. a temporal property that is a tautology).
pub(crate) const EXIT_LIVENESS_EVAL: u8 = 77;
/// FAILURE_SAFETY_EVAL (an invariant could not be evaluated, or is not a
/// state predicate).
pub(crate) const EXIT_SAFETY_EVAL: u8 = 76;
pub(crate) const EXIT_SETUP_ERROR: u8 = 150;
/// SYSTEM_ERROR_CONFIG (e.g. an action-level PROPERTY).
pub(crate) const EXIT_CONFIG_ERROR: u8 = 151;
/// TLC's exit status for other errors (`EC.ExitStatus.ERROR`).
pub(crate) const EXIT_GENERAL_ERROR: u8 = 255;

/// A run being reported.
pub(crate) struct Run {
    pub(crate) workers: usize,
    /// The names of the actions (TLC's), as in errors.
    pub(crate) actions: Vec<String>,
    pub(crate) started: Instant,
    pub(crate) sim: Option<Sim>,
    /// What limits the fingerprint set (a full one reports it).
    pub(crate) fp_mem: FpMem,
    /// The options of a model-checking search.
    pub(crate) opts: Option<Options>,
    /// `-coverage`: the coverage entries of the model.
    pub(crate) coverage: Option<Arc<coverage::Table>>,
    /// The run's checkpointer, finalized only after post-search liveness and
    /// counterexample replay complete so replay-time store exhaustion can
    /// preserve the last committed checkpoint.
    pub(crate) checkpoint: Option<Arc<tlx_runtime::Checkpointer>>,
}

/// A simulation being reported.
pub(crate) struct Sim {
    pub(crate) seed: u64,
    /// The label of initial states in traces.
    pub(crate) init_label: String,
    /// The last progress of the simulation.
    pub(crate) progress: SimProgress,
}

/// After the search: liveness, POSTCONDITION, then the TLC-style report.
pub(crate) fn finish<T: Tier>(m: &T, r: Report<T::State>, run: &Run) -> ExitCode {
    finish_with_trace(m, r, None, run)
}

/// Like `finish`, preserving a pre-decoded `saved_trace` snapshot taken before
/// any secondary search on `m` (such as `-dump`).
pub(crate) fn finish_with_trace<T: Tier>(
    m: &T,
    mut r: Report<T::State>,
    mut saved_trace: Option<Vec<(Arc<[tlx_value::Value]>, Option<u32>)>>,
    run: &Run,
) -> ExitCode {
    let base = m.base();
    let init = run.sim.as_ref().map_or_else(|| "Initial predicate".to_string(), |sim| sim.init_label.clone());
    let view = live::TraceView::new(m, init);
    explain_incomplete(m, &mut r, saved_trace.as_deref());
    let recorded = match &r.live_graph {
        Some(Ok(g)) => g.bytes(),
        _ => 0,
    };
    // (Liveness, if any, starts here.)
    let checks = run.sim.is_none() && matches!(r.outcome, Outcome::Ok) && !base.live.is_empty();
    let guard =
        tlx_runtime::mem::RssGuard::new(if checks { run.opts.as_ref().map_or(usize::MAX, |o| o.maxmem) } else { usize::MAX }, recorded);
    let periodic = r.live_witness.is_some();
    let mut lv = if run.sim.is_none() { liveness(m, &mut r, run, &view, guard) } else { None };
    // TLC evaluates the liveness predicates during its search: an error in
    // one of them stops it where it occurs, maybe before the end of the
    // search or the failure tlx found. So does a violation of some
    // properties that TLC detects during its search. Search again
    // to find them then.
    if let (Some(opts), false) = (&run.opts, base.live.is_empty()) {
        let early = live::reports_early(base);
        let again = match (&r.outcome, &lv) {
            (Outcome::Ok, Some((live::Liveness::Error(e), _))) => !e.is_store_full(),
            (Outcome::Ok, Some((live::Liveness::Violated(..), _))) => early && !periodic,
            (Outcome::Ok | Outcome::FpSetFull { .. } | Outcome::Io(_), _) => false,
            (Outcome::Error(e), _) if e.is_store_full() => false,
            // A violation: the search found none of these errors where TLC
            // evaluates the predicates before it, if the initial
            // states were expanded (a state at depth 3 was found). (After an
            // evaluation error in the next-state relation TLC still checks
            // the state, and an error there decides its exit status.)
            (Outcome::InvariantViolated(_) | Outcome::ActionPropertyViolated(_) | Outcome::Deadlock, _)
                if !early && r.live_atoms_ok && r.stats.depth >= 3 =>
            {
                false
            }
            _ => true,
        };
        if again && saved_trace.is_none() && !r.trace.is_empty() && m.caps().gc.is_some() {
            // Decode the original trace into owned `Value`s before `find_error`
            // launches a second search on `m`, whose safepoint GC sweeps the
            // value store without rooting `r.trace`.
            saved_trace = Some(r.trace.drain(..).map(|t| (m.values(&t.state), t.action)).collect());
        }
        let found = again.then(|| {
            let t0 = Instant::now();
            let r2 = live::find_error(m, opts, early, &view);
            stats::phase("liveness: search again (TLC's errors during its search)", t0.elapsed());
            r2
        });
        if let Some(r2) = found.flatten() {
            r = Report { elapsed: r.elapsed, ..r2 };
            saved_trace = None;
            lv = None;
        }
    }
    // Finalize the run's checkpoint only after liveness checking and replay have
    // returned, so value-store exhaustion during replay (including a secondary
    // `live::find_error` trace rebuild) preserves the last committed checkpoint
    // while normal completion/violation cleans it up.
    if let Some(c) = &run.checkpoint {
        let keep = m.caps().keep_checkpoint()
            || r.trace_store_full
            || matches!(&lv, Some((live::Liveness::Error(e), _)) if e.is_store_full())
            || matches!(&r.outcome, Outcome::Error(e) if e.is_store_full());
        if keep && c.keep_last() {
            if let Some((live::Liveness::Error(e), _)) = &mut lv {
                if e.is_store_full() && !e.message.contains("recovering the last checkpoint") {
                    e.message.push_str(", recovering the last checkpoint, which is kept");
                }
            }
            if r.trace_store_full {
                if let Some(note) = &mut r.trace_note {
                    if !note.contains("recovering the last checkpoint") {
                        note.push_str(", recovering the last checkpoint, which is kept");
                    }
                }
            }
        }
        c.finish();
    }
    let post = postcondition(base, &r, run.sim.is_some());
    // -dumpTrace: TLC writes the counterexample of a violation (not after
    // an evaluation error, and not when trace reconstruction yielded 0 states).
    let has_trace = saved_trace.as_ref().map_or(!r.trace.is_empty(), |s| !s.is_empty());
    let steps: Option<Vec<_>> = (dump_trace::requested()
        && has_trace
        && matches!(r.outcome, Outcome::InvariantViolated(_) | Outcome::ActionPropertyViolated(_) | Outcome::Deadlock))
    .then(|| match &saved_trace {
        Some(saved) => saved.clone(),
        None => r.trace.iter().map(|t| (m.values(&t.state), t.action)).collect(),
    });
    // (And of a liveness violation, the lasso shown.)
    let lasso = match (&r.outcome, &lv) {
        (Outcome::TemporalViolated { counterexample, .. }, _) | (_, Some((live::Liveness::Violated(_, counterexample), _))) => {
            dump_trace::kept_lasso(counterexample)
        }
        _ => None,
    };
    let dump = || {
        if let Some(steps) = &steps {
            dump_trace::write(base, steps);
        } else if let Some(l) = &lasso {
            dump_trace::write_lasso(base, l);
        }
    };
    report::<T>(r, saved_trace.as_deref(), lv, post, &view, run, &dump)
}

/// An incomplete state reported by a compiled tier (by its message only):
/// found again with the interpreter, which shows the state.
pub(crate) fn explain_incomplete<T: Tier>(m: &T, r: &mut Report<T::State>, saved_trace: Option<&[(Arc<[tlx_value::Value]>, Option<u32>)]>) {
    let base = m.base();
    let Outcome::Error(e) = &r.outcome else { return };
    if matches!(e.context, ErrorContext::IncompleteState { .. })
        || !e.message.contains(" is not completely specified. The following variable(s) are not defined: ")
    {
        return;
    }
    let found = if e.message.starts_with("The initial state ") {
        base.init_states(&mut |_| {}).err()
    } else if let Some((vals, len)) = saved_trace
        .and_then(|s| s.last().map(|(v, _)| (v.clone(), s.len())))
        .or_else(|| r.trace.last().map(|last| (m.values(&last.state), r.trace.len())))
    {
        let vals: Vec<Option<tlx_value::Value>> = vals.iter().cloned().map(Some).collect();
        let Ok(s) = base.make_state(&vals, len as u32, "the last state") else { return };
        (0..base.action_names().len()).find_map(|i| base.successors_of(&s, i, &mut |_, _| true).err())
    } else {
        None
    };
    if let Some(found) = found.filter(|f| matches!(f.context, ErrorContext::IncompleteState { .. })) {
        r.outcome = Outcome::Error(found);
    }
}

/// Record the statistics of the search of `r` for `TLCGet("stats")` (and
/// `"queue"`, ...) evaluated after it: in the POSTCONDITION, and in the
/// properties a liveness counterexample is found to violate (TLC evaluates
/// them when it reports the violation, with the statistics of its search
/// then).
pub(crate) fn record_search_stats<S>(base: &InterpModel, r: &Report<S>) {
    base.ip.set_final_stats(tlx_eval::RunStats {
        distinct: r.stats.distinct,
        generated: r.stats.generated,
        queue: r.stats.left,
        diameter: r.stats.depth as u64,
        duration_secs: r.elapsed.as_secs(),
        initial: r.stats.init_distinct,
        ..Default::default()
    });
}

/// The POSTCONDITION after a search that ran to completion (TLC also
/// checks it after a deadlock, and its simulator after any behavior but
/// a failure of the initial states): the message code and text if it is
/// violated or cannot be evaluated.
pub(crate) fn postcondition<S>(base: &InterpModel, r: &Report<S>, simulation: bool) -> Option<(u32, String)> {
    if !matches!(r.outcome, Outcome::Ok | Outcome::Deadlock) && (!simulation || r.in_init) {
        return None;
    }
    if !simulation {
        // (The statistics of a simulation are already recorded.)
        record_search_stats(base, r);
    }
    match base.check_postcondition() {
        Ok(msg) => msg.map(|m| (code::TLC_POSTCONDITION_FALSE, m)),
        Err(e) => {
            let label = base.postcondition_label().unwrap_or_default();
            let text = format!("Evaluating postcondition {label} failed.\n{}", out::nested(out::error_kind(&e), &e.message));
            Some((code::TLC_POSTCONDITION_EVALUATION_ERROR, text))
        }
    }
}

/// Liveness checking after a search without errors, if the model has
/// temporal properties: the outcome and the time it took.
/// Its time counts in the run's elapsed time (as with TLC).
pub(crate) fn liveness<T: Tier>(
    m: &T,
    r: &mut Report<T::State>,
    run: &Run,
    view: &live::TraceView<T::State>,
    guard: tlx_runtime::mem::RssGuard,
) -> Option<(live::Liveness, Duration)> {
    let base = m.base();
    let (workers, opts) = (run.workers, run.opts.as_ref());
    if !matches!(r.outcome, Outcome::Ok) || base.live.is_empty() {
        return None;
    }
    let st = &r.stats;
    let space = if r.live_witness.is_some() { "partial" } else { "complete" };
    print_progress(st.depth as u64, st.generated, st.distinct, st.left, None);
    // TLC checks each disjunct of the negated properties (its "branches")
    // on its own copy of the state graph.
    let branches = live_branches(base);
    let text = if branches > 1 {
        format!(
            "Checking {branches} branches of temporal properties for the {space} state space with {} total distinct states",
            st.distinct * branches as u64
        )
    } else {
        format!("Checking temporal properties for the {space} state space with {} total distinct states", st.distinct)
    };
    out::info(code::TLC_CHECKING_TEMPORAL_PROPS, &format!("{text} at ({})", out::now()));
    let start = Instant::now();
    record_search_stats(base, r);
    // A search stopped by TLCSet("exit", TRUE): TLC checks the graph of the
    // states it expanded (those left on the queue are not).
    let expanded = if m.stop_requested() { (st.distinct - st.left) as usize } else { usize::MAX };
    // (An atom failed during the search: TLC reports it as it evaluates
    // them there, `live_error`.)
    let mut lv = match r.live_error.take() {
        Some(e) => live::Liveness::Error(e),
        None if r.live_witness.is_some() => {
            live::rendered(base, r.live_witness.take().unwrap().replay(m, &base.liveness_input()), view, false)
        }
        None => live::check(m, workers, expanded, view, r.live_graph.take(), guard),
    };
    if matches!(&lv, live::Liveness::Error(e) if e.is_layout_miss()) {
        // A compiled model cannot widen its layout after the search: the
        // interpreter checks the properties instead (on the graph its own
        // search records; with VIEW or SYMMETRY the check explores).
        tlx_base::diag::emit(
            tlx_base::diag::Topic::Compile,
            "layout miss checking temporal properties; checking them with the interpreter",
        );
        let view = live::TraceView::new(base, "Initial predicate".into());
        lv = match opts {
            Some(opts) if !base.has_view_or_symmetry() => interpreted_liveness(base, opts, workers, expanded, &view, guard),
            _ => live::check(base, workers, expanded, &view, None, guard),
        };
    }
    r.elapsed += start.elapsed();
    Some((lv, start.elapsed()))
}

/// The interpreter's own search of the model, for the behavior graph it
/// records (liveness after a compiled model's layout miss): the graph (or
/// the memory error), or the error of an atom or of the search. The output
/// of the spec stays suppressed (the first search printed it).
fn interpreted_liveness(
    base: &InterpModel,
    opts: &Options,
    workers: usize,
    expanded: usize,
    view: &live::TraceView<tlx_eval::model::State>,
    guard: tlx_runtime::mem::RssGuard,
) -> live::Liveness {
    let printing = !base.ip.print_suppressed();
    base.ip.set_suppress_print(true);
    // (The first search's request to stop would end this one at once.)
    base.ip.undo_exit();
    let r = tlx_runtime::explore(
        base,
        &Options { progress: None, coverage: false, coverage_report: None, checkpoint: None, workers, ..opts.clone() },
    );
    base.ip.set_suppress_print(!printing);
    match (r.live_error, r.live_witness, r.live_graph, r.outcome) {
        (Some(e), _, _, _) | (_, _, _, Outcome::Error(e)) => live::Liveness::Error(e),
        (_, Some(witness), _, Outcome::Ok) => live::rendered(base, witness.replay(base, &base.liveness_input()), view, false),
        (_, _, graph, Outcome::Ok) => live::check(base, workers, expanded, view, graph, guard),
        _ => live::Liveness::Error(tlx_runtime::ModelError::new("internal error: the interpreter's search recorded no liveness graph")),
    }
}

/// The number of disjuncts of the negated temporal properties (TLC's
/// "branches"), each checked on its own.
pub(crate) fn live_branches(base: &InterpModel) -> usize {
    tlx_live::branches(base.live.props.iter().map(|(_, f)| f))
}
