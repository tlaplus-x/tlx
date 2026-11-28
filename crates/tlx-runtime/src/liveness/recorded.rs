//! Checking the behavior graph recorded during the search.

use std::borrow::Cow;

use super::shape::{violated, violated_names, Shape};
use super::{LiveInput, LiveResult, STUTTER};
use crate::io::{IoError, Spill, SpillMode, SpillVec};
use crate::mem::RssGuard;
use crate::{LiveGraph, Model, ModelError};

/// The bytes of a block of the spilled fingerprints (1 MiB).
const FPS_BLOCK_BYTES: usize = 1 << 20;

#[derive(Debug)]
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
pub(super) fn check_recorded<M: Model>(
    m: &M,
    input: &LiveInput,
    g: LiveGraph,
    workers: usize,
    guard: RssGuard,
    spill: &Spill,
) -> LiveResult<M::State> {
    match scan(input, g, workers, guard, spill) {
        Ok(Some(witness)) => witness.replay(m, input),
        Ok(None) => LiveResult::Holds,
        Err(msg) => LiveResult::OutOfMemory(msg),
    }
}

/// Evidence owned independently of the graph and the workers' value store.
#[derive(Debug)]
pub struct RecordedWitness {
    first: Option<u64>,
    steps: Vec<ReplayStep>,
    prefix: usize,
    prop: usize,
    state_pats: Vec<tlx_live::Bits>,
    action_pats: Vec<tlx_live::Bits>,
}

impl RecordedWitness {
    pub fn replay<M: Model>(self, m: &M, input: &LiveInput) -> LiveResult<M::State> {
        let Self { first, steps, prefix, prop, state_pats, action_pats } = self;
        let path = match replay(m, first, &steps) {
            Ok(p) => p,
            Err(e) => return LiveResult::Error(e),
        };
        let seq: Vec<(u32, &M::State, u32)> = steps.iter().zip(&path).map(|(step, (st, a))| (step.src, st, *a)).collect();
        let sh = Shape::new(&seq, prefix);
        let names =
            violated_names(input, &sh, &mut |k| Ok(Cow::Borrowed(&state_pats[steps[sh.shown[k].pos].state_pat as usize])), &mut |k| {
                Ok(Cow::Borrowed(&action_pats[steps[sh.shown[k].leave].action_pat as usize]))
            });
        violated(names, prop, &seq, &sh)
    }
}

/// The fingerprints of the behavior graph's nodes (`8 B` each): in memory,
/// or spilled to disk before the product search, which never reads them —
/// only the nodes of a counterexample lasso are read back, on a violation.
enum Fps {
    Mem(Vec<u64>),
    Disk(SpillVec<u64>),
}

impl Fps {
    fn is_disk(&self) -> bool {
        matches!(self, Fps::Disk(_))
    }

    /// The fingerprint of node `i`.
    fn get(&self, i: usize) -> Result<u64, IoError> {
        match self {
            Fps::Mem(v) => Ok(v[i]),
            Fps::Disk(v) => v.get(i),
        }
    }

    /// Move the fingerprints to the spill file, returning the bytes they
    /// held in memory; the values are read back with `get`. Nothing for no
    /// fingerprints, when they are already on disk, or with `-spill off`.
    ///
    /// The blocks are written and freed as they are copied, so that the
    /// spilled copy never adds a whole second vector of fingerprints to the
    /// memory the check is trying to give back.
    fn spill(&mut self, spill: &Spill) -> Result<usize, IoError> {
        if spill.mode() == SpillMode::Off {
            return Ok(0);
        }
        let Self::Mem(fps) = self else { return Ok(0) };
        if fps.is_empty() {
            return Ok(0);
        }
        let freed = fps.capacity() * std::mem::size_of::<u64>();
        let mut disk = SpillVec::new(FPS_BLOCK_BYTES, "liveness-fps");
        let block = disk.block_len();
        for (i, &fp) in fps.iter().enumerate() {
            disk.push(fp);
            if (i + 1) % block == 0 {
                disk.spill(spill, false)?;
                disk.settle()?;
            }
        }
        disk.spill(spill, true)?;
        disk.settle()?;
        // (The vector is freed here; the pages go back before the product.)
        *self = Self::Disk(disk);
        crate::mem::purge();
        Ok(freed)
    }
}

/// The fingerprints of a recorded graph while it is checked: dropped
/// (freeing the blocks of a spilled one and the spill directory they made)
/// before `RecordedWitness::replay` runs, which re-executes the model with
/// the memory the check gave back.
struct FpsLease<'a> {
    fps: Fps,
    spill: &'a Spill,
}

impl FpsLease<'_> {
    /// The fingerprint of node `i`.
    fn get(&self, i: usize) -> Result<u64, String> {
        self.fps.get(i).map_err(disk_error)
    }

    /// Move the fingerprints to the spill file (their bytes in memory).
    fn spill(&mut self) -> Result<usize, String> {
        self.fps.spill(self.spill).map_err(disk_error)
    }
}

impl Drop for FpsLease<'_> {
    fn drop(&mut self) {
        if self.fps.is_disk() || self.spill.failed() {
            // (The IO threads hold the spilled blocks' store: wait for them
            // to release it, so that the directory goes before the replay.)
            self.spill.wait_for_writes();
            self.spill.wait_for_reads();
        }
    }
}

/// The message of a disk-layer failure while checking liveness: the run's
/// other memory errors (`LiveResult::OutOfMemory`, a system error).
fn disk_error(e: IoError) -> String {
    format!("the disk layer failed checking liveness: {e}")
}

pub(crate) fn scan(
    input: &LiveInput,
    g: LiveGraph,
    workers: usize,
    mut guard: RssGuard,
    spill: &Spill,
) -> Result<Option<RecordedWitness>, String> {
    record_live_graph(&g);
    let LiveGraph { init, fps, off, tgt, edge_pat, state_pat, state_pats, action_pats } = g;
    let bits = |p: Vec<Box<[u64]>>| p.into_iter().map(tlx_live::Bits::from_boxed_words).collect();
    let graph = tlx_live::Csr { init, off, tgt, edge_pat, state_pat, state_pats: bits(state_pats), action_pats: bits(action_pats) };
    let mut fps = FpsLease { fps: Fps::Mem(fps), spill };
    if spill.mode() == SpillMode::Always {
        // (The fingerprints are of no use to the product: write them out
        // before it is built.)
        let freed = fps.spill()?;
        guard.release(freed);
    }
    let (mut peak, mut err) = ((0, 0, 0), None);
    for (i, (_, f)) in input.props.iter().enumerate() {
        let mut st = tlx_live::CheckStats::default();
        // An error of a reclamation on demand (a failed write): the check
        // cannot go on, but the message is the disk's, not the budget's.
        let mut spill_err = None;
        let r = {
            let mut reclaim = || match fps.spill() {
                Ok(freed) => freed,
                Err(msg) => {
                    spill_err.get_or_insert(msg);
                    0
                }
            };
            let mut within = guard.product(&mut peak, &mut err, &mut reclaim);
            tlx_live::check_lasso_csr_stats(&graph, f, &input.fairness, workers, &mut within, &mut st)
        };
        record_product(peak);
        record_check(&st);
        if let Some(msg) = spill_err {
            return Err(msg);
        }
        let Ok(r) = r else { return Err(err.unwrap_or_default()) };
        if let Err(cx) = r {
            // (Only now are the fingerprints read, for the nodes of the
            // lasso: the product search did not need them.)
            let mut steps = Vec::with_capacity(cx.prefix.len() + cx.cycle.len());
            for &(src, edge) in cx.prefix.iter().chain(&cx.cycle) {
                let idx = edge as usize;
                let e = graph.off.get(src as usize) + idx;
                let t = graph.tgt[e];
                steps.push(ReplayStep {
                    src,
                    edge,
                    stutter: idx + 1 == graph.degree(src),
                    target_fp: fps.get(t as usize)?,
                    state_pat: graph.state_pat[src as usize],
                    action_pat: graph.edge_pat.get(e),
                });
            }
            let first = match steps.first() {
                Some(step) => Some(fps.get(step.src as usize)?),
                None => None,
            };
            let (state_pats, action_pats) = {
                let mut csr = graph;
                (std::mem::take(&mut csr.state_pats), std::mem::take(&mut csr.action_pats))
            };
            return Ok(Some(RecordedWitness { first, steps, prefix: cx.prefix.len(), prop: i, state_pats, action_pats }));
        }
    }
    Ok(None)
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
