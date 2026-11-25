//! Checking the behavior graph recorded during the search.

use std::borrow::Cow;

use super::shape::{violated, violated_names, Shape};
use super::{LiveInput, LiveResult, STUTTER};
use crate::mem::RssGuard;
use crate::{LiveGraph, Model, ModelError};

struct ReplayStep {
    src: u32,
    edge: u32,
    stutter: bool,
    target_fp: u64,
    state_pat: u32,
    action_pat: u32,
}

/// Check every temporal property of `input` on the behavior graph `g`
/// recorded during the search of `m` (on up to `workers` threads). A counterexample's states are rebuilt
/// by re-executing `m` along its path; an error of `m` there (a layout miss
/// of a compiled model: the interpreter checks again) or a path that does
/// not follow the graph (a bug) is the result.
pub(super) fn check_recorded<M: Model>(m: &M, input: &LiveInput, g: LiveGraph, workers: usize, guard: RssGuard) -> LiveResult<M::State> {
    record_live_graph(&g);
    let LiveGraph { init, fps, off, tgt, edge_pat, state_pat, state_pats, action_pats } = g;
    let bits = |p: Vec<Box<[u64]>>| p.into_iter().map(tlx_live::Bits::from_boxed_words).collect();
    let graph = tlx_live::Csr { init, off, tgt, edge_pat, state_pat, state_pats: bits(state_pats), action_pats: bits(action_pats) };
    let (mut peak, mut err) = ((0, 0, 0), None);
    for (i, (_, f)) in input.props.iter().enumerate() {
        let mut st = tlx_live::CheckStats::default();
        let r = tlx_live::check_lasso_csr_stats(&graph, f, &input.fairness, workers, &mut guard.product(&mut peak, &mut err), &mut st);
        record_product(peak);
        record_check(&st);
        let Ok(r) = r else { return LiveResult::OutOfMemory(err.unwrap_or_default()) };
        if let Err(cx) = r {
            let steps: Vec<ReplayStep> = cx
                .prefix
                .iter()
                .chain(&cx.cycle)
                .map(|&(src, edge)| {
                    let idx = edge as usize;
                    let e = graph.off[src as usize] + idx;
                    let t = graph.tgt[e];
                    ReplayStep {
                        src,
                        edge,
                        stutter: idx + 1 == graph.degree(src),
                        target_fp: fps[t as usize],
                        state_pat: graph.state_pat[src as usize],
                        action_pat: graph.edge_pat.get(e),
                    }
                })
                .collect();
            let first = steps.first().map(|step| fps[step.src as usize]);
            let (state_pats, action_pats) = {
                let mut csr = graph;
                (std::mem::take(&mut csr.state_pats), std::mem::take(&mut csr.action_pats))
            };
            drop(fps);
            let path = match replay(m, first, &steps) {
                Ok(p) => p,
                Err(e) => return LiveResult::Error(e),
            };
            let seq: Vec<(u32, &M::State, u32)> = steps.iter().zip(&path).map(|(step, (st, a))| (step.src, st, *a)).collect();
            let sh = Shape::new(&seq, cx.prefix.len());
            let names =
                violated_names(input, &sh, &mut |k| Ok(Cow::Borrowed(&state_pats[steps[sh.shown[k].pos].state_pat as usize])), &mut |k| {
                    Ok(Cow::Borrowed(&action_pats[steps[sh.shown[k].leave].action_pat as usize]))
                });
            return violated(names, i, &seq, &sh);
        }
    }
    LiveResult::Holds
}

/// Reclaim transient value-store allocations during lasso counterexample
/// replay, keeping the replayed `path`, active `extra` states, and any
/// thread-local emit handles rooted.
fn collect_lasso<S>(gc: &dyn crate::model::StoreGc<S>, path: &[(S, u32)], extra: &[&S]) -> bool {
    let mut tls = Vec::new();
    gc.take_thread_roots(&mut tls);
    gc.collect(&mut |mark| {
        for (s, _) in path {
            gc.mark_state(s, mark);
        }
        for s in extra {
            gc.mark_state(s, mark);
        }
        for &h in &tls {
            mark(h);
        }
        Ok(())
    })
    .is_ok()
}

/// The states along `steps` of the recorded graph of `m`, each with the
/// action of the edge leaving it: re-executed from the initial state, taking
/// at each node the successor in the model the edge stands for (the edges of
/// a state are its successors in the model in generation order, then the
/// stuttering step), as error traces are rebuilt. An error if `m` fails or a
/// state's fingerprint is not the node's (a bug: the graph is of this model).
fn replay<M: Model>(m: &M, first: Option<u64>, steps: &[ReplayStep]) -> Result<Vec<(M::State, u32)>, ModelError> {
    let lost = || ModelError::new("internal error: a counterexample of the recorded liveness graph cannot be replayed");
    let first = first.ok_or_else(lost)?;
    let store_gc = m.caps().gc;
    let _gc_guard = store_gc.map(|gc| gc.enter_scope());
    if let Some(gc) = store_gc {
        // Sweep dead handles left over from the completed search before
        // reconstructing the lasso so replay starts with the full budget.
        let _ = gc.collect(&mut |_| Ok(()));
    }
    let mut found = None;
    if let Some(gc) = store_gc {
        let mut err: Option<ModelError> = None;
        let res = m.init_states_gc(&mut |ev| match ev {
            crate::model::GcEvent::Collect { .. } => collect_lasso(gc, &[], &[]),
            crate::model::GcEvent::Emit(s, _) => {
                if found.is_some() || err.is_some() {
                    return false;
                }
                if m.fingerprint(&s) == first {
                    match m.constraint_gc(&s, &mut |_| collect_lasso(gc, &[], &[&s])) {
                        Ok(true) => {
                            found = Some(s);
                            return false;
                        }
                        Ok(false) => {}
                        Err(e) if e.is_store_full() => {
                            gc.mark_full();
                            err = Some(e);
                            return false;
                        }
                        Err(_) => {}
                    }
                }
                true
            }
        });
        if let Some(e) = err {
            return Err(e);
        }
        res.inspect_err(|e| {
            if e.is_store_full() {
                gc.mark_full();
            }
        })?;
    } else {
        m.init_states(&mut |s| {
            if found.is_none() && m.fingerprint(&s) == first && matches!(m.constraint(&s), Ok(true)) {
                found = Some(s);
            }
        })?;
    }
    let mut cur = found.ok_or_else(lost)?;
    let mut path = Vec::with_capacity(steps.len());
    for step in steps {
        let e = step.edge as usize;
        let (t, a) = if step.stutter {
            (cur.clone(), STUTTER)
        } else if let Some(gc) = store_gc {
            if gc.needs_gc() {
                collect_lasso(gc, &path, &[&cur]);
            }
            let (mut i, mut next, mut err) = (0, None, None);
            for act_idx in 0..m.action_names().len() as u32 {
                let go = m.action_successors_gc(&cur, act_idx, &mut |ev| match ev {
                    crate::model::GcEvent::Collect { .. } => collect_lasso(gc, &path, &[&cur]),
                    crate::model::GcEvent::Emit(t, a) => {
                        if err.is_some() {
                            return false;
                        }
                        match crate::model::admits_gc(m, &cur, &t, &mut |_| collect_lasso(gc, &path, &[&cur, &t])) {
                            Ok(true) => {
                                if i == e {
                                    next = Some((t, a));
                                    return false;
                                }
                                i += 1;
                            }
                            Ok(false) => {}
                            Err(e) if e.is_store_full() => {
                                gc.mark_full();
                                err = Some(e);
                                return false;
                            }
                            Err(_) => {}
                        }
                        true
                    }
                });
                if let Some(e) = err {
                    return Err(e);
                }
                let go = go.inspect_err(|e| {
                    if e.is_store_full() {
                        gc.mark_full();
                    }
                })?;
                if !go {
                    break;
                }
            }
            next.ok_or_else(lost)?
        } else {
            // (An error counts as a step out of the model: the search evaluated
            // these steps without one, so the path is lost then, reported below.)
            let in_model = |s: &M::State, t: &M::State| crate::admits(m, s, t).unwrap_or(false);
            let (mut i, mut next) = (0, None);
            m.successors(&cur, &mut |t, a| {
                if in_model(&cur, &t) {
                    if i == e {
                        next = Some((t, a));
                        return false;
                    }
                    i += 1;
                }
                true
            })?;
            next.ok_or_else(lost)?
        };
        if m.fingerprint(&t) != step.target_fp {
            return Err(lost());
        }
        path.push((std::mem::replace(&mut cur, t), a));
    }
    Ok(path)
}

/// Record what checking one property did (`tlx_live::CheckStats`), for
/// `-stats`: times add up over the properties, sizes are the largest.
fn record_check(st: &tlx_live::CheckStats) {
    use crate::stats;
    if !stats::on() {
        return;
    }
    stats::add_secs("liveness: tableau and product construction (thread-seconds)", std::time::Duration::from_secs_f64(st.build_secs));
    stats::add_secs("liveness: SCC search and counterexample (thread-seconds)", std::time::Duration::from_secs_f64(st.search_secs));
    stats::max_count("liveness: product parts (largest)", st.parts as u64);
    stats::max_count("liveness: tableau states (largest)", st.tableau_states as u64);
    stats::max_count("liveness: tableau waiting states, not built (largest)", st.waiting_states as u64);
}

/// Record the largest product graph (nodes, edges, bytes) for `-stats`.
fn record_product(peak: (usize, usize, usize)) {
    if crate::stats::on() && peak.2 > 0 {
        use crate::stats::{self, Metric};
        stats::set("liveness: product nodes (largest)", Metric::Count(peak.0 as u64));
        stats::set("liveness: product edges (largest)", Metric::Count(peak.1 as u64));
        stats::set(&format!("{}liveness product graph (largest, est.)", stats::MEMORY), Metric::Bytes(peak.2 as u64));
    }
}

/// Record the size of the liveness behavior graph `g` recorded during the
/// search (if on).
fn record_live_graph(g: &LiveGraph) {
    use crate::stats::{self, Metric};
    if !stats::on() {
        return;
    }
    stats::set("liveness: graph states", Metric::Count(g.len() as u64));
    stats::set("liveness: graph edges", Metric::Count(g.tgt.len() as u64));
    stats::set("liveness: state patterns", Metric::Count(g.state_pats.len() as u64));
    stats::set("liveness: action patterns", Metric::Count(g.action_pats.len() as u64));
    stats::set(&format!("{}liveness behavior graph (CSR)", stats::MEMORY), Metric::Bytes(g.bytes() as u64));
}
