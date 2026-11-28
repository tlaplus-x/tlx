//! Liveness checking (design.md §7.4), as the CLI reports it: the checks
//! themselves are `tlx_runtime::liveness` (on the behavior graph recorded
//! during the search, TLC's way under VIEW or SYMMETRY, or on one simulated
//! behavior); here their counterexamples are rendered as TLC shows them.

use std::sync::Arc;

use tlx_eval::model::liveness::InterpSearchAtoms;
use tlx_eval::InterpModel;
use tlx_runtime::liveness::{LiveResult, STUTTER};
use tlx_runtime::mem::RssGuard;
use tlx_value::Value;

use crate::tier::Tier;

/// The outcome of liveness checking.
pub enum Liveness {
    /// Every temporal property holds.
    Holds,
    /// A property is violated: the names of the properties the
    /// counterexample violates (as TLC: see `violated_names`; with VIEW or
    /// SYMMETRY possibly none) and the rendered counterexample.
    Violated(Vec<String>, String),
    /// Checking failed (an error of the model, or of the checker: a
    /// `ModelError` of kind `General`).
    Error(tlx_runtime::ModelError),
    /// Checking needs more memory than the budget (`-maxmem`) allows: a
    /// resource limit of the run (see `tlx_runtime::explore::liveness_memory_error`).
    OutOfMemory(String),
}

/// TLC's message for the violation of the temporal properties `names`
/// (MP, `EC.TLC_TEMPORAL_PROPERTY_VIOLATED`): "Temporal property P was
/// violated.", "Temporal properties P and Q were violated.", "Temporal
/// properties P, Q, and R were violated." or, naming none, "Temporal
/// properties were violated.".
pub fn violation_message(names: &[String]) -> String {
    match names {
        [] => "Temporal properties were violated.\n".to_string(),
        [p] => format!("Temporal property {p} was violated.\n"),
        [p, q] => format!("Temporal properties {p} and {q} were violated.\n"),
        [ps @ .., last] => format!("Temporal properties {}, and {last} were violated.\n", ps.join(", ")),
    }
}

/// How the states of a counterexample are shown and its steps labeled
/// (a safety trace, a lasso): the state through the ALIAS if there is one,
/// else as the model renders it.
type Text<'a, S> = dyn Fn(usize, &S, Option<&S>) -> String + 'a;
type ValText<'a> = dyn Fn(usize, &Arc<[Value]>, Option<&Arc<[Value]>>) -> String + 'a;

pub struct TraceView<'a, S> {
    text: Box<Text<'a, S>>,
    val_text: Box<ValText<'a>>,
    /// The values of the variables of a state (`-dumpTrace`).
    pub values: Box<dyn Fn(&S) -> Arc<[Value]> + Sync + 'a>,
    /// The label of the initial state.
    init: String,
    action: Box<dyn Fn(u32) -> String + 'a>,
    /// `TLCExt!Trace` in the ALIAS: the states shown so far, as the path to
    /// the state shown (`tlx_runtime::live::current_path`), if the spec
    /// uses it.
    path: Option<std::cell::RefCell<Vec<Arc<tlx_runtime::live::PathNode>>>>,
}

impl<'a, S> TraceView<'a, S> {
    /// The states of `t` shown through the ALIAS, or (without one, or if it
    /// cannot be evaluated) as `t` renders them; `init` labels the initial
    /// state.
    pub fn new<T: Tier<State = S>>(t: &'a T, init: String) -> TraceView<'a, S> {
        let base = t.base();
        let text = move |i: usize, s: &S, next: Option<&S>| {
            let next = next.map(|n| t.values(n));
            base.render_alias(&t.values(s), next.as_deref(), i as u32 + 1).unwrap_or_else(|| t.render(s))
        };
        let val_text = move |i: usize, vals: &Arc<[Value]>, next: Option<&Arc<[Value]>>| {
            base.render_alias(vals, next.map(|n| n.as_ref()), i as u32 + 1)
                .unwrap_or_else(|| tlx_runtime::Model::render(base, &tlx_eval::model::State::new(vals.clone(), i as u32 + 1, 0)))
        };
        TraceView {
            text: Box::new(text),
            val_text: Box::new(val_text),
            values: Box::new(move |s| t.values(s)),
            init,
            action: Box::new(move |a| base.action_label(a as usize)),
            path: base.ip.uses_trace().then(Default::default),
        }
    }

    /// State number `i + 1` of a trace (reached by action `into`), followed
    /// by `next` if any. The states of a trace are shown in order: `Trace`
    /// in the ALIAS is the trace up to the state shown.
    pub fn show(&self, i: usize, s: &S, next: Option<&S>, into: Option<u32>) -> String {
        use tlx_runtime::live::{with_path, CurrentPath, PathNode};
        let Some(path) = &self.path else { return (self.text)(i, s, next) };
        let node = {
            let mut p = path.borrow_mut();
            p.truncate(i);
            let parent = p.last().cloned();
            let node = Arc::new(PathNode { values: (self.values)(s), action: into, parent });
            p.push(node.clone());
            node
        };
        with_path(Some(CurrentPath::Known(node)), || (self.text)(i, s, next))
    }

    /// Like `show`, rendering pre-decoded owned variable values so traces
    /// survive value-store GC during a secondary liveness recheck search.
    pub fn show_values(&self, i: usize, vals: &Arc<[Value]>, next: Option<&Arc<[Value]>>, into: Option<u32>) -> String {
        use tlx_runtime::live::{with_path, CurrentPath, PathNode};
        let Some(path) = &self.path else { return (self.val_text)(i, vals, next) };
        let node = {
            let mut p = path.borrow_mut();
            p.truncate(i);
            let parent = p.last().cloned();
            let node = Arc::new(PathNode { values: vals.clone(), action: into, parent });
            p.push(node.clone());
            node
        };
        with_path(Some(CurrentPath::Known(node)), || (self.val_text)(i, vals, next))
    }

    /// The label of a step: `<Initial predicate>` or `<Action ...>`, by the
    /// action into the state (None for an initial state).
    pub fn label(&self, into: Option<u32>) -> String {
        match into {
            None => format!("<{}>", self.init),
            Some(a) => format!("<{}>", (self.action)(a)),
        }
    }

    /// The printed state `i + 1` of a trace (reached by `into`) under `label`.
    pub fn step(&self, i: usize, label: &str, s: &S, next: Option<&S>, into: Option<u32>) -> String {
        crate::out::state(i + 1, label, &self.show(i, s, next, into))
    }

    /// Like `step`, rendering pre-decoded owned variable values.
    pub fn step_values(&self, i: usize, label: &str, vals: &Arc<[Value]>, next: Option<&Arc<[Value]>>, into: Option<u32>) -> String {
        crate::out::state(i + 1, label, &self.show_values(i, vals, next, into))
    }
}

/// Check the temporal properties of `m`'s base on its states
/// (`tlx_runtime::liveness::check`, which see), rendering a counterexample
/// with `view`.
pub fn check<T: Tier>(
    m: &T,
    workers: usize,
    expanded: usize,
    view: &TraceView<T::State>,
    recorded: Option<Result<tlx_runtime::LiveGraph, String>>,
    guard: RssGuard,
) -> Liveness {
    let base = m.base();
    crate::stats::record_peak_rss("peak RSS before liveness");
    if tlx_runtime::stats::on() {
        let live = &base.live;
        let pred = |f: &&tlx_eval::model::liveness::Fair| {
            matches!(live.state_atoms[f.enabled as usize], tlx_eval::model::liveness::StateAtom::Pred(_))
        };
        let steps = |f: &&tlx_eval::model::liveness::Fair| live.enabled_steps.get(f.enabled as usize).is_some_and(Option::is_some);
        let direct = live.fairness.iter().filter(pred).filter(|f| !steps(f)).count();
        let from_steps = live.fairness.iter().filter(pred).filter(steps).count();
        tlx_runtime::stats::set("liveness: fairness ENABLED evaluated directly", tlx_runtime::stats::Metric::Count(direct as u64));
        // (Where A cannot be enumerated from a state, evaluated directly.)
        tlx_runtime::stats::set("liveness: fairness ENABLED from A's steps", tlx_runtime::stats::Metric::Count(from_steps as u64));
        tlx_runtime::stats::set("liveness: fairness conditions", tlx_runtime::stats::Metric::Count(live.fairness.len() as u64));
    }
    let r = tlx_runtime::liveness::check(m, &base.liveness_input(), m, workers, expanded, recorded, guard);
    rendered(base, r, view, true)
}

/// Check the temporal properties of `m`'s base TLC's way on one simulated
/// behavior (`tlx_runtime::liveness::check_trace`, which see), rendering a
/// counterexample with `view`. States are the same if their values are.
pub fn check_trace<T: Tier>(
    m: &T,
    trace: &[(T::State, Option<u32>)],
    succs: &[Vec<(T::State, u32)>],
    view: &TraceView<T::State>,
) -> Liveness {
    let r = tlx_runtime::liveness::check_trace(m, &m.base().liveness_input(), m, trace, succs, &|a, b| m.values(a) == m.values(b));
    rendered(m.base(), r, view, true)
}

/// The result `r` of checking the properties of `base`, a counterexample
/// rendered with `view`; `warn`: whether a stuttering one is
/// warned about (not for a violation found during the search, as TLC).
pub(crate) fn rendered<S>(base: &InterpModel, r: LiveResult<S>, view: &TraceView<S>, warn: bool) -> Liveness {
    match r {
        LiveResult::Holds => Liveness::Holds,
        LiveResult::Error(e) => Liveness::Error(e),
        LiveResult::OutOfMemory(msg) => Liveness::OutOfMemory(msg),
        LiveResult::Violated(v) => {
            let stuttering = v.lasso.stuttering() && warn;
            violated(base, v.names, &base.live.props[v.prop].1, render(&v.lasso, view), stuttering)
        }
    }
}

/// The violation of the properties `names`, found checking formula `f`,
/// with the rendered counterexample `out` and the lasso it shows
/// (`stuttering`: whether its cycle is, and is warned about). The lasso is
/// kept for `-dumpTrace`.
fn violated(
    base: &InterpModel,
    names: Vec<String>,
    f: &tlx_live::Ltl,
    (mut out, lasso): (String, crate::dump_trace::Lasso),
    stuttering: bool,
) -> Liveness {
    let live = &base.live;
    if stuttering && live.fairness.is_empty() && tlx_live::needs_cycle_conditions(f) {
        if let Some(spec) = base.specification_location() {
            out += &crate::out::format(
                crate::out::code::GENERAL,
                crate::out::Class::Warning,
                &format!(
                    "The stuttering counterexample above may be caused by the absence of a fairness constraint in the behavior specification {spec}. To rule out such counterexamples, conjoin a suitable fairness constraint to {} (compare Chapter 8, page 87ff of Specifying Systems at https://lamport.azurewebsites.net/tla/book.html).",
                    base.ip.cfg.specification.as_deref().unwrap_or_default()
                ),
            );
        }
    }
    crate::dump_trace::keep_lasso(&out, lasso);
    Liveness::Violated(names, out)
}

/// TLC's rendering of the liveness counterexample `l`: the prefix and the
/// cycle, each state labeled by the step into it, closed by "Back to state
/// k: <A>" (or "Stuttering").
fn render<S>(l: &tlx_runtime::liveness::Lasso<S>, view: &TraceView<S>) -> (String, crate::dump_trace::Lasso) {
    use crate::out;
    let mut text =
        out::format(out::code::TLC_COUNTER_EXAMPLE, out::Class::Error, "The following behavior constitutes a counter-example:\n");
    let label = |a: u32| if a == STUTTER { "Stuttering".to_string() } else { view.label(Some(a)) };
    let action = |a: Option<u32>| a.filter(|&a| a != STUTTER);
    let mut states = Vec::with_capacity(l.states.len());
    for (k, (s, into)) in l.states.iter().enumerate() {
        let lab = match into {
            None => view.label(None),
            Some(a) => label(*a),
        };
        let next = &l.states[l.next(k)].0;
        text += &view.step(k, &lab, s, Some(next), action(*into));
        if crate::dump_trace::requested() {
            states.push(((view.values)(s), action(*into)));
        }
    }
    // The step closing the lasso, as TLC's CounterExample has it: to the
    // cycle's first state by the closing action, or (stuttering) a step
    // from the last state to itself, with the action of the step into it.
    let back = if l.stuttering() {
        text += &out::stuttering(l.states.len() + 1);
        l.states.last().and_then(|(_, into)| action(*into))
    } else {
        text += &out::back_to_state(l.cycle + 1, &label(l.close));
        action(Some(l.close))
    };
    (text, crate::dump_trace::Lasso { states, back_to: l.cycle + 1, back })
}

/// The state atoms of the tableaux TLC builds for the temporal properties
/// of `base` (`LiveSpec::tableau`).
pub fn tableau_atoms(base: &InterpModel) -> Vec<u32> {
    base.liveness_input().tableau_atoms()
}

/// Whether TLC may report a violation of a temporal property of `base`
/// during its search, before the end (see `find_error`).
pub fn reports_early(base: &InterpModel) -> bool {
    base.liveness_input().reports_early()
}

/// Search `m` again (with `opts`) evaluating the liveness predicates as
/// TLC does during its search (`tlx_runtime::liveness::find_error`, which
/// see): the report of the first error of one of them, if any. With
/// `early` (see `reports_early`), also the report of a violation TLC finds
/// during its search, if it stops there (outcome `TemporalViolated`, its
/// counterexample rendered with `view`).
pub fn find_error<T: Tier>(
    m: &T,
    opts: &tlx_runtime::Options,
    early: bool,
    view: &TraceView<T::State>,
) -> Option<tlx_runtime::Report<T::State>> {
    let base = m.base();
    let input = base.liveness_input();
    let values = |s: &T::State| m.values(s);
    let level = |s: &T::State| m.level(s);
    let atoms = InterpSearchAtoms { base, values: &values, level: &level };
    // (The search printed already.)
    let printing = !base.ip.print_suppressed();
    base.ip.set_suppress_print(true);
    // (The first search's TLCSet("exit", TRUE) would stop this one at
    // once: each requests it where TLC does.)
    let found = tlx_runtime::liveness::find_error(m, &input, m, &atoms, opts, early, &|| base.ip.undo_exit());
    base.ip.set_suppress_print(!printing);
    let found = found?;
    let Some(fired) = found.fired else { return Some(found.report) };
    // (TLC names the violated properties where its search stopped.)
    crate::report::record_search_stats(base, &found.report);
    let outcome = match rendered(base, fired.result(&input), view, false) {
        Liveness::Violated(properties, counterexample) => tlx_runtime::Outcome::TemporalViolated { properties, counterexample },
        Liveness::Error(e) => tlx_runtime::Outcome::Error(e),
        Liveness::OutOfMemory(message) => tlx_runtime::Outcome::Error(tlx_runtime::ModelError::new(message)),
        Liveness::Holds => unreachable!("a violation"),
    };
    Some(tlx_runtime::Report { outcome, trace: Vec::new(), ..found.report })
}

#[cfg(test)]
mod tests {
    #[test]
    fn violation_message() {
        let m = |names: &[&str]| super::violation_message(&names.iter().map(|n| n.to_string()).collect::<Vec<_>>());
        assert_eq!(m(&[]), "Temporal properties were violated.\n");
        assert_eq!(m(&["P"]), "Temporal property P was violated.\n");
        assert_eq!(m(&["P", "Q"]), "Temporal properties P and Q were violated.\n");
        assert_eq!(m(&["P", "Q", "R"]), "Temporal properties P, Q, and R were violated.\n");
    }
}
