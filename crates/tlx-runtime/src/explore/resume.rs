//! Resumable searches (docs/scale.md §6). While a search may have to be
//! resumed, its workers keep the states they are done with in the archive
//! (compressed blocks, see `frontier`), so that a search stopped by a
//! failure can be rolled back to the start of the level at which it failed
//! (a `ResumePoint`) and resumed, e.g. by the compiled tier after a layout
//! miss with the states re-encoded (`ResumePoint::transcode`). The trace
//! logs are kept: the resumed search continues them, with the fingerprints
//! of the archived states rewritten (re-encoding a state does not change
//! its identity, so the parents of all entries stay valid).
//!
//! Under memory pressure the archive's segments go to disk (stage 1)
//! rather than the archive being dropped: its records are read from there
//! (only the pages of a block at a time) when the search resumes, and the
//! re-encoded archive is written there too.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use super::edges::{AtomBits, EdgeRec};
use super::frontier::{Local, Task};
use super::order::Positions;
use super::tracelog::{split_log_ref, TraceLog, NO_PARENT};
use super::worker::{WorkerOut, WorkerState};
use super::{fp_set_full, InitResult, Outcome, OutdegreeHist, Shared, Stats};
use crate::io::{IoError, Spill};
use crate::mem::Component;
use crate::model::{Model, ModelError};
use crate::queue::codec::XorPrev;
use crate::queue::{Block, Mem, Queue, SegCache};
use tlx_base::par::{Abort, Pool, Stack};

/// A search stopped by a failure, rolled back to the start of the level at
/// which it failed: enough to resume it with another model of the same
/// state space (e.g. with states re-encoded) and get the statistics and
/// traces of an uninterrupted search. Produced by `explore_resumable` when
/// it archives states.
pub struct ResumePoint<S> {
    /// Per worker of the stopped search, its part of the archive: the
    /// distinct states (satisfying the constraints) of depth up to `level`
    /// it expanded or left, in blocks of states of the same depth (in the
    /// order it was done with them: with one worker, BFS order).
    archive: Vec<Vec<Block<S>>>,
    /// The words of the encoded states of the archive (0: objects).
    words: usize,
    /// The archive's memory account and segment size.
    mem: Arc<Mem>,
    seg_bytes: usize,
    /// The trace logs of the stopped search (per worker).
    logs: Vec<TraceLog>,
    /// The depth of the states to expand first (the deepest ones).
    level: u32,
    /// The counters before the expansion of level `level` (its depth is
    /// `level`; the coverage counts if the stopped search counted them).
    pub(super) base: BaseCounters,
    /// Per worker: it expanded states of level `level` (the effects of
    /// which are repeated by a resumed search, see `Effects::mark`).
    rolled_back: Vec<bool>,
    /// The positions of the states of level `level` in BFS order, if the
    /// stopped search chose the representatives in that order (`order`).
    positions: Option<Arc<Positions>>,
    /// The disk layer, if the archive went to disk (so does the re-encoded
    /// archive).
    spill: Option<Spill>,
}

/// What a resumed or recovered search starts from: the counters of the
/// search it continues (`ResumePoint::base`, a checkpoint's manifest).
#[derive(Clone)]
pub(super) struct BaseCounters {
    /// The initial states generated and distinct.
    pub(super) init_generated: u64,
    pub(super) init_distinct: u64,
    /// States generated after the initial ones (by the workers, and the
    /// model's extras): without the initial states.
    pub(super) generated_after_init: u64,
    /// The depth the search starts from.
    pub(super) depth: u32,
    /// Outdegrees of the states expanded.
    pub(super) outdegree: OutdegreeHist,
    /// The coverage counts (flat, see `Slot::cov`; empty if not counted).
    pub(super) coverage: Vec<u64>,
}

impl BaseCounters {
    /// A search from the initial states: nothing before it.
    pub(super) fn none() -> BaseCounters {
        BaseCounters {
            init_generated: 0,
            init_distinct: 0,
            generated_after_init: 0,
            depth: 0,
            outdegree: OutdegreeHist::new(),
            coverage: Vec::new(),
        }
    }

    /// The counters of the initial states, in `stats` and `shared` (before
    /// the workers start).
    pub(super) fn restore_init<M: Model>(&self, shared: &Shared<'_, M>, stats: &mut Stats) {
        stats.init_generated = self.init_generated;
        stats.init_distinct = self.init_distinct;
        shared.init_generated.store(self.init_generated, Ordering::Relaxed);
        shared.init_distinct.store(self.init_distinct, Ordering::Relaxed);
    }
}

/// An error re-encoding the archived states (`ResumePoint::transcode`).
#[derive(Debug)]
pub enum TranscodeError<E> {
    /// From the re-encoding function.
    Encode(E),
    /// Reading the archive's segments back from disk.
    Io(IoError),
}

impl<S> ResumePoint<S> {
    /// The depth at which the resumed search starts expanding.
    pub fn level(&self) -> u32 {
        self.level
    }

    /// Per worker, whether it took part in the interrupted level.
    pub fn rolled_back(&self) -> &[bool] {
        &self.rolled_back
    }

    /// The number of states archived.
    pub fn len(&self) -> usize {
        self.archive.iter().flatten().map(|b| b.len()).sum()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The memory of the archive (bytes).
    pub fn bytes(&self) -> usize {
        self.mem.bytes()
    }

    /// The archive's memory account (the resumed search's archive counts there too).
    pub(super) fn mem(&self) -> Arc<Mem> {
        self.mem.clone()
    }

    /// The words of the encoded states (0: the states are objects).
    pub fn words(&self) -> usize {
        self.words
    }

    /// Call `f(words, depth)` on the first `n` encoded states, in order,
    /// while it returns true; returns false if it returned false.
    pub fn sample(&self, n: usize, mut f: impl FnMut(&[u64], u32) -> bool) -> bool {
        let mut prev = XorPrev::new(self.words);
        let mut cache = SegCache::default();
        let mut left = n;
        for b in self.archive.iter().flatten() {
            if left == 0 {
                break;
            }
            let depth = b.depth();
            let r = b.records(&mut cache, &mut prev, |_, _, w| {
                if left == 0 {
                    return Err(true);
                }
                left -= 1;
                if f(w, depth) {
                    Ok(())
                } else {
                    Err(false)
                }
            });
            // (An archive that cannot be read back cannot be resumed from.)
            if matches!(r, Ok(Err(false)) | Err(_)) {
                return false;
            }
        }
        true
    }

    /// Convert every state held as an object with `f` (on `threads`
    /// threads), keeping the order; the first error, if any. Encoded
    /// states are kept as they are (see `transcode`).
    pub fn try_map<T: Send, E: Send>(self, threads: usize, f: impl Fn(S) -> Result<T, E> + Sync) -> Result<ResumePoint<T>, E>
    where
        S: Send,
    {
        let ResumePoint { archive, words, mem, seg_bytes, logs, level, base, rolled_back, positions, spill } = self;
        let archive = parallel_map(archive, threads, |abort, blocks| {
            let mut out = Vec::with_capacity(blocks.len());
            for b in blocks {
                if abort.requested() {
                    break;
                }
                out.push(b.try_map(&f)?);
            }
            Ok(out)
        })?;
        Ok(ResumePoint { archive, words, mem, seg_bytes, logs, level, base, rolled_back, positions, spill })
    }

    /// Re-encode every encoded state with `f(words, depth, out)`, which
    /// writes the new encoding (`words` words) to `out` and returns the new
    /// fingerprint (on `threads` threads, keeping the order); the first
    /// error, if any (of `f`, or reading the archive back from disk). The
    /// trace logs get the new fingerprints when the search resumes.
    pub fn transcode<E: Send>(
        self,
        threads: usize,
        words: usize,
        f: impl Fn(&[u64], u32, &mut [u64]) -> Result<u64, E> + Sync,
    ) -> Result<ResumePoint<S>, TranscodeError<E>>
    where
        S: Send,
    {
        let ResumePoint { archive, words: old_words, mem, seg_bytes, logs, level, base, rolled_back, positions, spill } = self;
        let f = &f;
        let m = &mem;
        let sp = spill.as_ref();
        let archive = parallel_map(archive, threads, |abort, blocks| {
            let mut q: Queue<'_, S> = Queue::archive(None, words, seg_bytes, m.clone());
            if let Some(sp) = sp {
                // (The re-encoded archive goes to disk as it is written.)
                q = q.with_spill(sp, "archive");
                q.spill_on(true);
            }
            let mut w = q.writer();
            let mut prev = XorPrev::new(old_words);
            let mut cache = SegCache::default();
            let mut out = vec![0u64; words];
            for b in blocks {
                if abort.requested() {
                    break;
                }
                if !b.encoded() {
                    q.append(&mut w, b);
                    continue;
                }
                let depth = b.depth();
                b.records(&mut cache, &mut prev, |log, _, old| {
                    let fp = f(old, depth, &mut out)?;
                    q.push_words(&mut w, log, fp, depth, &out);
                    Ok(())
                })
                .map_err(TranscodeError::Io)?
                .map_err(TranscodeError::Encode)?;
                q.spill_writer(&mut w);
            }
            let blocks = q.take(&mut w);
            if q.spilling() {
                q.spill_blocks(&blocks);
            }
            Ok(blocks)
        })?;
        Ok(ResumePoint { archive, words, mem, seg_bytes, logs, level, base, rolled_back, positions, spill })
    }
}

/// Map the lists of `parts` with `f` on up to `threads` threads (lists
/// split into contiguous runs of blocks), keeping the order. `f` gets the
/// pool's [`Abort`] flag and should stop when another worker has panicked.
fn parallel_map<A: Send, B: Send, E: Send>(
    parts: Vec<Vec<A>>,
    threads: usize,
    f: impl Fn(&Abort, Vec<A>) -> Result<Vec<B>, E> + Sync,
) -> Result<Vec<Vec<B>>, E> {
    let total: usize = parts.iter().map(|p| p.len()).sum();
    let chunk = total.div_ceil(threads.max(1)).max(1);
    // (list index, a run of its items)
    let mut runs: Vec<(usize, Vec<A>)> = Vec::new();
    let n = parts.len();
    for (i, mut p) in parts.into_iter().enumerate() {
        while p.len() > chunk {
            let rest = p.split_off(chunk);
            runs.push((i, p));
            p = rest;
        }
        runs.push((i, p));
    }
    // Old worker parts (including empty ones) can produce more runs than
    // the requested concurrency. Keep the runs independent of the pool size.
    let pool = Pool { threads, stack: Stack::Default };
    let mapped = pool.map_owned(runs, |abort, (index, run)| f(abort, run).map(|values| (index, values)))?;
    let mut out: Vec<Vec<B>> = (0..n).map(|_| Vec::new()).collect();
    for (i, r) in mapped {
        out[i].extend(r);
    }
    Ok(out)
}

/// Whether workers archive the states they are done with (see
/// `ResumePoint`): keep at most `max` bytes in memory, spilling beyond it
/// (or dropping the archive if disk is unavailable).
pub(super) struct Retention {
    pub(super) on: bool,
    pub(super) max: usize,
    /// Set when the archive was dropped.
    off: AtomicBool,
}

impl Retention {
    /// Archiving up to `max` bytes, if given.
    pub(super) fn new(max: Option<usize>) -> Retention {
        Retention { on: max.is_some(), max: max.unwrap_or(0), off: AtomicBool::new(false) }
    }

    /// Whether the archive was dropped.
    pub(super) fn off(&self) -> bool {
        self.off.load(Ordering::Relaxed)
    }

    /// Drop the archive (every worker drops its part at its next check).
    /// Returns true if it was kept until now.
    pub(super) fn drop_archive(&self) -> bool {
        self.on && !self.off.swap(true, Ordering::Relaxed)
    }
}

impl<M: Model> WorkerState<'_, '_, M> {
    /// Done with `task` (expanded, or left in a queue at the end): archive
    /// its state while archiving.
    #[inline]
    pub(super) fn retire(&mut self, task: Task<M::State>) {
        self.local.retire(task);
    }

    /// Stop archiving if the archive is over its limit or was dropped.
    pub(super) fn check_archive(&mut self) {
        if !self.local.archiving() {
            return;
        }
        let shared = self.shared;
        if !shared.frontier.archive_spilling() && shared.budget.meters().bytes(Component::Archive) > shared.retention.max {
            shared.relieve_archive();
        }
        if shared.retention.off() {
            self.local.stop_archiving();
        }
    }

    /// At the end of the search: remove the tasks left (see `Local::drain`;
    /// archived while archiving: with those expanded, they are all the
    /// distinct states found). Returns their number.
    pub(super) fn retain_left(&mut self) -> usize {
        if self.shared.retention.off() {
            self.local.stop_archiving();
        }
        self.local.drain()
    }
}

/// The resume point of a search stopped by a failure while expanding some
/// level: its archive (in `outs`), its trace logs and the statistics before
/// that level.
#[allow(clippy::too_many_arguments)]
pub(super) fn resume_point<S>(
    stats: &Stats,
    base_generated: u64,
    base_outdegree: &OutdegreeHist,
    base_coverage: &[u64],
    logs: Vec<TraceLog>,
    outs: Vec<WorkerOut<S>>,
    mem: Arc<Mem>,
    words: usize,
    seg_bytes: usize,
    positions: Option<Arc<Positions>>,
    spill: Option<Spill>,
) -> ResumePoint<S> {
    // All workers expand the same level (level-synchronous search, or a
    // single worker's BFS order): the deepest level any was expanding.
    let level = outs.iter().map(|o| o.level).max().unwrap_or(0).max(1);
    let rolled_back = outs.iter().map(|o| o.level == level).collect();
    let mut generated = base_generated;
    let mut outdegree = base_outdegree.clone();
    let mut coverage = base_coverage.to_vec();
    for o in &outs {
        let (g, h, c) =
            if o.level == level { (o.level_start.0, &o.level_start.1, &o.level_cov) } else { (o.generated, &o.outdegree, &o.cov) };
        generated += g;
        outdegree.merge(h);
        super::coverage::add(&mut coverage, c);
    }
    // (Without the next level's states, drained at the end with the
    // current level's in a level-synchronous search.)
    let archive = outs.into_iter().map(|o| o.archive.unwrap_or_default().into_iter().filter(|b| b.depth() <= level).collect()).collect();
    let base = BaseCounters {
        init_generated: stats.init_generated,
        init_distinct: stats.init_distinct,
        generated_after_init: generated,
        depth: level,
        outdegree,
        coverage,
    };
    ResumePoint { archive, words, mem, seg_bytes, logs, level, base, rolled_back, positions, spill }
}

/// Resume from `c`: its states are distinct; those of its last level go to
/// `seed` (worker 0's next level: the first level of the search), the
/// others to the archive of worker 0 (while archiving). Returns the trace
/// logs to continue (per worker), with the fingerprints of the archived
/// states rewritten.
pub(super) fn resume_phase<M: Model>(
    shared: &Shared<'_, M>,
    seed: &mut Local<'_, '_, M::State>,
    stats: &mut Stats,
    c: ResumePoint<M::State>,
) -> InitResult {
    let model = shared.model;
    c.base.restore_init(shared, stats);
    let ResumePoint { archive, words, mut logs, level, positions, .. } = c;
    // The states of the first level, in order (choosing representatives in
    // BFS order without the stopped search's positions).
    let mut seq = Vec::new();
    let ordered = shared.order.is_some() && positions.is_none();
    let mut prev = XorPrev::new(words);
    let mut cache = SegCache::default();
    // Recording the behavior graph: the states of the levels before `level`
    // are expanded again after the search, for their edges.
    let recording = shared.live_atoms.is_some();
    let mut pre = Vec::new();
    // Record state `(log, fp)` as seen: a full seen set, or an error
    // reading back a spilled trace log (or archive segment), stops the
    // search.
    let mut io_error: Option<IoError> = None;
    let mut read_error: Option<IoError> = None;
    // `TLCExt!Trace`: the archived states with their trace-log parents (the
    // archive is per worker: a parent may come after its children), linked
    // into paths in BFS order below.
    let paths = shared.paths.is_some();
    let mut found = Vec::new();
    let mut add = |log: u64, fp: u64, depth: u32, state: Option<&M::State>| -> Result<(), ()> {
        // (The workers have not started yet.)
        if shared.insert_exclusive(fp).is_err() {
            return Err(());
        }
        let (w, i) = split_log_ref(log);
        logs[w].set_fp(i, fp).map_err(|e| io_error = Some(e))?;
        if let (true, Some(s)) = (paths, state) {
            let parent = logs[w].get(i).map_err(|e| io_error = Some(e))?.0;
            let values = model.state_values(s).expect("a model that uses TLCExt!Trace has state values");
            found.push((depth, log, parent, values));
        }
        Ok(())
    };
    for b in archive.into_iter().flatten() {
        let depth = b.depth();
        if depth > level {
            continue;
        }
        let full = if b.encoded() {
            let codec = model.caps().codec().expect("encoded states without a codec");
            let r = b.records(&mut cache, &mut prev, |log, fp, w| -> Result<(), ()> {
                let state = (depth == level || paths).then(|| codec.decode(w, depth, fp));
                add(log, fp, depth, state.as_ref())?;
                if let (true, Some(state)) = (depth == level, state) {
                    if ordered {
                        seq.push(log);
                    }
                    seed.push_new(Task { state, log, depth });
                }
                Ok(())
            });
            let r = r.unwrap_or_else(|e| {
                read_error = Some(e);
                Err(())
            });
            if depth < level {
                if recording {
                    pre.extend(b.share().map(Pre::Block));
                }
                seed.archive_blocks(vec![b]);
            }
            r.is_err()
        } else {
            let mut full = false;
            let mut tasks = Vec::new();
            for t in b.into_tasks() {
                if add(t.log, model.fingerprint(&t.state), depth, Some(&t.state)).is_err() {
                    full = true;
                    break;
                }
                if depth == level {
                    if ordered {
                        seq.push(t.log);
                    }
                    seed.push_new(t);
                } else {
                    if recording {
                        tasks.push(Task { state: t.state.clone(), log: t.log, depth });
                    }
                    seed.retire(t);
                }
            }
            if !tasks.is_empty() {
                pre.push(Pre::Tasks(tasks));
            }
            full
        };
        if full {
            let failure = match io_error.or(read_error) {
                Some(e) => (Outcome::Io(e.0), NO_PARENT),
                None => fp_set_full(&shared.seen),
            };
            return Ok((logs, Some(failure)));
        }
    }
    if let Some(p) = &shared.paths {
        found.sort_by_key(|&(depth, ..)| depth);
        let mut p = p.lock();
        let mut nodes: tlx_base::hash::FxMap<u64, Arc<crate::live::PathNode>> = Default::default();
        for (depth, log, parent, values) in found {
            let node = Arc::new(crate::live::PathNode { values, action: None, parent: nodes.get(&parent).cloned() });
            if depth == level {
                p.insert(log, depth, node.clone());
            }
            nodes.insert(log, node);
        }
    }
    *shared.live_pre.lock() = pre;
    if let Some(o) = &shared.order {
        o.start(positions.unwrap_or_else(|| Arc::new(Positions::of_seq(&seq))));
    }
    Ok((logs, None))
}

/// States of the levels before the resume point of a resumed search that
/// records the behavior graph (see `record_archived`): archived blocks
/// (sharing the archive's segments) or states.
pub(super) enum Pre<S> {
    Block(Block<S>),
    Tasks(Vec<Task<S>>),
}

impl<S> Pre<S> {
    pub(super) fn len(&self) -> usize {
        match self {
            Pre::Block(b) => b.len(),
            Pre::Tasks(ts) => ts.len(),
        }
    }

    /// The depth of its states (one level each).
    pub(super) fn depth(&self) -> u32 {
        match self {
            Pre::Block(b) => b.depth(),
            Pre::Tasks(ts) => ts.first().map_or(0, |t| t.depth),
        }
    }
}

/// Record the liveness edges of the states `pre` (of the levels before the
/// resume point of a resumed search, which expanded them in another layout:
/// docs/scale.md §8.3) by expanding them again with `model`, as a worker
/// does but without the seen set and the queues, on up to `threads`
/// threads (a record per thread, in blocks of `block_bytes`). The error if a
/// state cannot be expanded or an atom fails (liveness reports it, or the
/// IO error that is behind it, see `live_graph_of`). When a
/// thread panics, the others stop early and the panic goes on.
pub(super) fn record_archived<'m, M: Model>(
    model: &'m M,
    atoms: &'m (dyn AtomBits<M::State> + Sync),
    pre: Vec<Pre<M::State>>,
    threads: usize,
    block_bytes: usize,
) -> Result<Vec<EdgeRec<'m, M::State>>, ModelError> {
    // Contiguous runs of about the same number of states.
    let total: usize = pre.iter().map(|p| p.len()).sum();
    let per = total.div_ceil(threads.max(1)).max(1);
    let mut runs: Vec<Vec<Pre<M::State>>> = vec![Vec::new()];
    let mut n = 0;
    for p in pre {
        if n >= per {
            runs.push(Vec::new());
            n = 0;
        }
        n += p.len();
        runs.last_mut().expect("a run").push(p);
    }
    // (The search printed what these states print.)
    model.caps().replaying(true);
    let pool = Pool { threads: runs.len(), stack: Stack::Eval };
    let recs =
        pool.map_owned(runs, |abort, run| Ok::<_, std::convert::Infallible>(record_run(model, atoms, run, block_bytes, abort))).unwrap();
    model.caps().replaying(false);
    recs.into_iter().collect()
}

/// `record_archived` of one run of states, on this thread (an error if
/// another thread of the pool panicked).
fn record_run<'m, M: Model>(
    model: &'m M,
    atoms: &'m (dyn AtomBits<M::State> + Sync),
    run: Vec<Pre<M::State>>,
    block_bytes: usize,
    abort: &Abort,
) -> Result<EdgeRec<'m, M::State>, ModelError> {
    let mut rec = EdgeRec::new(atoms, block_bytes);
    let mut prev = XorPrev::new(model.caps().codec().map_or(0, |c| c.words()));
    let mut cache = SegCache::default();
    let aborted = || ModelError::new("aborted: another thread panicked");
    for p in run {
        if abort.requested() {
            return Err(aborted());
        }
        match p {
            Pre::Block(b) => {
                let codec = model.caps().codec().expect("encoded states without a codec");
                let depth = b.depth();
                // (An error reading the archive back fails the run, see
                // `live_graph_of`.)
                b.records(&mut cache, &mut prev, |log, fp, w| record_state(model, &mut rec, &codec.decode(w, depth, fp), fp, depth, log))
                    .map_err(|e| ModelError::new(e.0))??;
            }
            Pre::Tasks(ts) => {
                for t in ts {
                    if abort.requested() {
                        return Err(aborted());
                    }
                    record_state(model, &mut rec, &t.state, model.fingerprint(&t.state), t.depth, t.log)?;
                }
            }
        }
    }
    Ok(rec)
}

/// Record the edges of state `s` (fingerprint `fp`, at `depth`, trace-log
/// entry `log`), generating its successors.
fn record_state<M: Model>(
    model: &M,
    rec: &mut EdgeRec<'_, M::State>,
    s: &M::State,
    fp: u64,
    depth: u32,
    log: u64,
) -> Result<(), ModelError> {
    rec.begin();
    let mut err = None;
    model.successors(s, &mut |t, a| {
        let r = crate::model::admits(model, s, &t).and_then(|in_model| rec.successor(s, &t, model.fingerprint(&t), a, in_model));
        match r {
            Ok(()) => true,
            Err(e) => {
                err = Some(e);
                false
            }
        }
    })?;
    if let Some(e) = err {
        return Err(e);
    }
    rec.end(s, fp, (depth == 1).then_some(log))
}

#[cfg(test)]
mod tests {
    use super::parallel_map;
    use std::collections::HashSet;
    use std::panic::{catch_unwind, AssertUnwindSafe};
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{mpsc, Condvar, Mutex};
    use std::time::Duration;

    fn check_map_cap(parts: Vec<Vec<usize>>, threads: usize) {
        let active = AtomicUsize::new(0);
        let peak = AtomicUsize::new(0);
        let workers = Mutex::new(HashSet::new());
        let released = Mutex::new(false);
        let wake = Condvar::new();
        let (started, starts) = mpsc::channel();
        let expected: Vec<Vec<_>> = parts.iter().map(|part| part.iter().map(|v| v * 2).collect()).collect();
        let mapped = std::thread::scope(|scope| {
            let handle = scope.spawn(|| {
                parallel_map(parts, threads, |_, run| {
                    workers.lock().unwrap().insert(std::thread::current().id());
                    peak.fetch_max(active.fetch_add(1, Ordering::SeqCst) + 1, Ordering::SeqCst);
                    started.send(()).unwrap();
                    let mut ready = released.lock().unwrap();
                    while !*ready {
                        ready = wake.wait(ready).unwrap();
                    }
                    drop(ready);
                    let out = run.into_iter().map(|v| v * 2).collect();
                    active.fetch_sub(1, Ordering::SeqCst);
                    Ok::<_, ()>(out)
                })
            });
            // Hold the first callbacks together to observe peak concurrency.
            // Worker identities also catch over-creation independent of timing.
            let first = starts.recv_timeout(Duration::from_secs(5));
            while starts.recv_timeout(Duration::from_millis(20)).is_ok() {}
            *released.lock().unwrap() = true;
            wake.notify_all();
            let result = handle.join().unwrap().unwrap();
            if !expected.is_empty() {
                first.unwrap();
                assert!(peak.load(Ordering::SeqCst) > 0);
            }
            result
        });
        assert_eq!(mapped, expected);
        assert_eq!(active.load(Ordering::SeqCst), 0);
        assert!(peak.load(Ordering::SeqCst) <= threads.max(1), "peak {} exceeds cap {threads}", peak.load(Ordering::SeqCst));
        assert!(workers.into_inner().unwrap().len() <= threads.max(1));
    }

    #[test]
    fn parallel_map_caps_eight_old_parts() {
        for threads in [0, 1, 3] {
            check_map_cap((0..8).map(|i| vec![i]).collect(), threads);
        }
    }

    #[test]
    fn parallel_map_caps_empty_and_uneven_parts() {
        for threads in [1, 3, 8] {
            check_map_cap(vec![Vec::new(); 8], threads);
            check_map_cap(vec![vec![], (0..31).collect(), vec![], vec![31], vec![], vec![32, 33], vec![], vec![]], threads);
        }
        assert_eq!(parallel_map::<usize, usize, ()>(vec![], 3, |_, _| unreachable!()), Ok(vec![]));
    }

    #[test]
    fn parallel_map_keeps_run_order_and_first_error() {
        for threads in [1, 3, 8] {
            let called = AtomicUsize::new(0);
            let result = parallel_map((0..8).map(|i| vec![i]).collect(), threads, |_, run| {
                called.fetch_add(1, Ordering::SeqCst);
                if run[0] == 1 || run[0] == 7 {
                    Err(run[0])
                } else {
                    Ok(run)
                }
            });
            assert_eq!(result, Err(1));
            assert_eq!(called.load(Ordering::SeqCst), 8, "an error must not skip independent runs");
        }
    }

    #[test]
    fn parallel_map_panic_precedes_errors_and_joins_workers() {
        for threads in [1, 3, 8] {
            let finished = AtomicUsize::new(0);
            let result = catch_unwind(AssertUnwindSafe(|| {
                parallel_map((0..8).map(|i| vec![i]).collect(), threads, |_, run| {
                    if run[0] == 7 {
                        std::panic::panic_any(7usize);
                    }
                    finished.fetch_add(1, Ordering::SeqCst);
                    Err::<Vec<usize>, _>(run[0])
                })
            }));
            assert_eq!(*result.unwrap_err().downcast::<usize>().unwrap(), 7);
            assert_eq!(finished.load(Ordering::SeqCst), 7);
        }
    }

    #[test]
    fn parallel_map_keeps_first_panic_in_run_order() {
        for threads in [1, 3, 8] {
            let result = catch_unwind(AssertUnwindSafe(|| {
                parallel_map((0usize..8).map(|i| vec![i]).collect(), threads, |_, run| {
                    if run[0] == 1 || run[0] == 7 {
                        std::panic::panic_any(run[0]);
                    }
                    Ok::<_, ()>(run)
                })
            }));
            assert_eq!(*result.unwrap_err().downcast::<usize>().unwrap(), 1);
        }
    }
}
