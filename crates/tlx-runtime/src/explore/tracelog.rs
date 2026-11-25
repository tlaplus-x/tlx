//! The trace log (docs/scale.md §7): for every distinct state, the entry of
//! its parent and its fingerprint, in the history shard that recorded it.
//! States are not kept; a trace is rebuilt by re-executing the model along
//! the fingerprint chain (as TLC does).

use super::{Outcome, TraceStep};
use crate::io::{IoError, Spill, SpillVec};
use crate::model::{GcEvent, Model, ModelError, StoreGc};

/// Reference to a trace-log entry: stable shard ID in the high 16 bits, index
/// into that shard's log in the low 48 bits.
pub(super) type LogRef = u64;

/// The parent of an initial state.
pub(super) const NO_PARENT: LogRef = u64::MAX;

pub(super) fn log_ref(shard: usize, idx: usize) -> LogRef {
    ((shard as u64) << 48) | idx as u64
}

/// The (shard, index) a `LogRef` designates.
pub(super) fn split_log_ref(r: LogRef) -> (usize, usize) {
    ((r >> 48) as usize, (r & ((1 << 48) - 1)) as usize)
}

/// One history shard's trace log: `(parent, fingerprint)` for every distinct state
/// it found, in order. Stored in fixed-size blocks (docs/scale.md §7, 1 MiB
/// by default: the queue's segment size): appending never moves entries,
/// and under memory pressure the full blocks are written to disk
/// (`spill`); entries are read back from there when a trace is rebuilt.
pub(super) struct TraceLog {
    entries: SpillVec<[u64; 2]>,
}

impl TraceLog {
    /// A log in blocks of `block_bytes`.
    pub(super) fn new(block_bytes: usize) -> TraceLog {
        TraceLog { entries: SpillVec::new(block_bytes, "trace") }
    }

    #[inline]
    pub(super) fn len(&self) -> usize {
        self.entries.len()
    }

    /// Append an entry; returns its index.
    #[inline]
    pub(super) fn push(&mut self, parent: LogRef, fp: u64) -> usize {
        self.entries.push([parent, fp])
    }

    /// Entry `i`: `(parent, fingerprint)`.
    pub(super) fn get(&self, i: usize) -> Result<(LogRef, u64), IoError> {
        self.entries.get(i).map(|[p, f]| (p, f))
    }

    /// Set the fingerprint of entry `i` (a resumed search: the state
    /// re-encoded, see `ResumePoint`).
    pub(super) fn set_fp(&mut self, i: usize, fp: u64) -> Result<(), IoError> {
        let [p, _] = self.entries.get(i)?;
        self.entries.set(i, [p, fp])
    }

    /// The memory held (bytes).
    pub(super) fn bytes(&self) -> usize {
        self.entries.bytes()
    }

    /// Write the full blocks (with `all`, every block) to disk; see
    /// `SpillVec::spill`.
    pub(super) fn spill(&mut self, spill: &Spill, all: bool) -> Result<(), IoError> {
        self.entries.spill(spill, all)
    }

    /// Wait for the blocks being written.
    pub(super) fn settle(&mut self) -> Result<(), IoError> {
        self.entries.settle()
    }

    /// Before appending to a log spilled whole (`spill` with `all`).
    pub(super) fn unseal(&mut self) -> Result<(), IoError> {
        self.entries.unseal()
    }

    /// The blocks on disk.
    pub(super) fn spilled_blocks(&self) -> usize {
        self.entries.spilled_blocks()
    }

    /// Call `f` with the entries in order, in slices of at most `n`
    /// (spilled blocks are read back); stops at the first error.
    pub(super) fn for_each_chunk(
        &self,
        spill: &Spill,
        start: usize,
        n: usize,
        f: impl FnMut(&[[u64; 2]]) -> Result<(), String>,
    ) -> Result<(), String> {
        super::checkpoint::chunked(&self.entries, spill, start, n, f)
    }
}

impl Default for TraceLog {
    /// (A placeholder, e.g. for `std::mem::take`.)
    fn default() -> TraceLog {
        TraceLog::new(1 << 20)
    }
}

/// Re-execute the model along the fingerprint chain ending at `at`.
pub(super) struct Rebuilt<S> {
    pub trace: Vec<TraceStep<S>>,
    pub complete: bool,
}

/// Outcome of reconstructing a safety counterexample trace.
pub(super) enum TraceBuild<S> {
    /// A full (or best-effort prefix) trace was rebuilt.
    Rebuilt(Rebuilt<S>),
    /// The trace could not be reconstructed for a non-budget reason.
    Unavailable,
    /// Value-store budget exhaustion stopped trace reconstruction.
    StoreFull(ModelError),
}

pub(super) fn rebuild_trace<M: Model>(
    model: &M,
    logs: &[TraceLog],
    at: LogRef,
    outcome: &Outcome,
    store_gc: Option<&dyn StoreGc<M::State>>,
) -> Result<TraceBuild<M::State>, IoError> {
    let mut fps = Vec::new();
    let mut cur = at;
    while cur != NO_PARENT {
        let (w, i) = split_log_ref(cur);
        let (parent, fp) = logs[w].get(i)?;
        fps.push(fp);
        cur = parent;
    }
    fps.reverse();
    let started = std::time::Instant::now();
    if let Some(gc) = store_gc {
        // Sweep dead handles left behind by the completed search before replay
        // begins so trace reconstruction starts with the full store budget.
        let _ = gc.collect(&mut |_| Ok(()));
    }
    let rebuilt = if model.coarse_fingerprint() { replay_classes(model, &fps, outcome, store_gc) } else { replay(model, &fps, store_gc) };
    crate::stats::set("trace reconstruction", crate::stats::Metric::Secs(started.elapsed().as_secs_f64()));
    Ok(rebuilt)
}

/// Reclaim transient value-store allocations during single-threaded trace
/// reconstruction, keeping `trace`, `prefix`, `extra`, and any buffered
/// thread-local emit handles rooted.
fn collect_replay<S>(gc: &dyn StoreGc<S>, trace: &[TraceStep<S>], prefix: &[TraceStep<S>], extra: &[&S]) -> bool {
    let mut tls = Vec::new();
    gc.take_thread_roots(&mut tls);
    gc.collect(&mut |mark| {
        for step in trace {
            gc.mark_state(&step.state, mark);
        }
        for step in prefix {
            gc.mark_state(&step.state, mark);
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

/// Run a GC-aware predicate check during trace replay, reclaiming transient
/// store allocations per predicate when `store_gc` is active.
fn replay_pred<S, T>(
    store_gc: Option<&dyn StoreGc<S>>,
    trace: &[TraceStep<S>],
    prefix: &[TraceStep<S>],
    extra: &[&S],
    f: impl FnOnce(&mut dyn FnMut(bool) -> bool) -> Result<T, ModelError>,
) -> Result<T, ModelError> {
    if let Some(gc) = store_gc {
        f(&mut |_| collect_replay(gc, trace, prefix, extra))
    } else {
        f(&mut |_| false)
    }
}

/// Re-execute a chain whose fingerprints identify concrete states.
fn replay<M: Model>(model: &M, fps: &[u64], store_gc: Option<&dyn StoreGc<M::State>>) -> TraceBuild<M::State> {
    let Some((&first, rest)) = fps.split_first() else {
        return TraceBuild::Unavailable;
    };
    let mut found = None;
    // (An error in a later initial state does not matter: the search
    // stopped at the first failure, see `init_phase`.)
    if let Some(gc) = store_gc {
        let res = model.init_states_gc(&mut |ev| match ev {
            GcEvent::Emit(s, _) => {
                if found.is_none() && model.fingerprint(&s) == first {
                    found = Some(s);
                }
                found.is_none()
            }
            GcEvent::Collect { .. } => {
                let extra: Vec<&M::State> = found.iter().collect();
                collect_replay(gc, &[], &[], &extra)
            }
        });
        if let Err(e) = res {
            if e.is_store_full() {
                return TraceBuild::StoreFull(e);
            }
        }
    } else {
        let _ = model.init_states(&mut |s| {
            if found.is_none() && model.fingerprint(&s) == first {
                found = Some(s);
            }
        });
    }
    let Some(first_state) = found else {
        return TraceBuild::Unavailable;
    };
    let mut trace = vec![TraceStep { state: first_state, action: None }];
    for &fp in rest {
        let mut next = None;
        if let Some(gc) = store_gc {
            if gc.needs_gc() {
                collect_replay(gc, &trace, &[], &[]);
            }
            let prev = &trace.last().unwrap().state;
            for a in 0..model.action_names().len() as u32 {
                let go = match model.action_successors_gc(prev, a, &mut |ev| match ev {
                    GcEvent::Emit(t, act) => {
                        if model.fingerprint(&t) == fp {
                            next = Some((t, act));
                            return false;
                        }
                        true
                    }
                    GcEvent::Collect { .. } => {
                        let extra: Vec<&M::State> = next.as_ref().map(|(s, _)| s).into_iter().collect();
                        collect_replay(gc, &trace, &[], &extra)
                    }
                }) {
                    Ok(go) => go,
                    Err(e) if e.is_store_full() => return TraceBuild::StoreFull(e),
                    Err(_) => return TraceBuild::Unavailable,
                };
                if !go {
                    break;
                }
            }
        } else {
            let prev = &trace.last().unwrap().state;
            if model
                .successors(prev, &mut |t, a| {
                    if model.fingerprint(&t) == fp {
                        next = Some((t, a));
                        return false;
                    }
                    true
                })
                .is_err()
            {
                return TraceBuild::Unavailable;
            }
        }
        let Some((t, a)) = next else {
            return TraceBuild::Unavailable;
        };
        trace.push(TraceStep { state: t, action: Some(a) });
    }
    TraceBuild::Rebuilt(Rebuilt { trace, complete: true })
}

/// VIEW/SYMMETRY logs identify classes. Follow actual successors from an
/// actual initial state, backtracking within each logged class until the
/// reported failure is reproduced. Iterative DFS bounds the depth by the
/// log. Alternatives are re-enumerated, retaining only hashes of previously
/// tried concrete states rather than buffering an entire class of states.
/// All extra work happens after failure; search-time logging is unchanged.
fn replay_classes<M: Model>(model: &M, fps: &[u64], outcome: &Outcome, store_gc: Option<&dyn StoreGc<M::State>>) -> TraceBuild<M::State> {
    use crate::live::{self, CurrentPath, PathNode};
    use std::hash::{Hash, Hasher};
    use std::sync::Arc;

    if fps.is_empty() {
        return TraceBuild::Unavailable;
    }
    let mut tried: Vec<tlx_base::hash::FxSet<u64>> = vec![Default::default()];
    let mut trace: Vec<TraceStep<M::State>> = Vec::with_capacity(fps.len());
    let mut paths: Vec<Arc<PathNode>> = Vec::new();
    let limit = model.trace_replay_limit();
    let mut prefix = Vec::new();
    loop {
        if let Some(gc) = store_gc {
            if gc.needs_gc() {
                collect_replay(gc, &trace, &prefix, &[]);
            }
        }
        let depth = trace.len();
        let terminal = depth + 1 == fps.len();
        let prev = trace.last().map(|s| &s.state);
        let mut next: Option<TraceStep<M::State>> = None;
        let mut pred_full: Option<ModelError> = None;
        let gen_full = {
            let mut consider = |s: M::State, action| {
                if pred_full.is_some() {
                    return false;
                }
                if model.fingerprint(&s) != fps[depth] {
                    return true;
                }
                let step = TraceStep { state: s, action };
                if terminal {
                    match matches_outcome(model, prev, &step, outcome, store_gc, &trace, &prefix) {
                        Ok(true) => {}
                        Ok(false) => return true,
                        Err(e) => {
                            pred_full = Some(e);
                            return false;
                        }
                    }
                } else {
                    let admitted = replay_pred(store_gc, &trace, &prefix, &[&step.state], |c| match prev {
                        None => model.constraint_gc(&step.state, c),
                        Some(p) => crate::model::admits_gc(model, p, &step.state, c),
                    });
                    match admitted {
                        Ok(true) => {}
                        Ok(false) => return true,
                        Err(e) if e.is_store_full() => {
                            pred_full = Some(e);
                            return false;
                        }
                        Err(_) => return true,
                    }
                    // Print-time identity only: enumeration may change order on
                    // every replay. The model's full rendering distinguishes
                    // members of a class without changing search fingerprints.
                    let mut hash = tlx_base::hash::StableHasher::new();
                    model.render(&step.state).hash(&mut hash);
                    if !tried[depth].insert(hash.finish()) {
                        return true;
                    }
                }
                next = Some(step);
                false
            };
            live::with_path(paths.last().cloned().map(CurrentPath::Known), || {
                // A later generation error does not invalidate an earlier
                // successor: the original search may have stopped before it.
                if let Some(gc) = store_gc {
                    if let Some(prev) = prev {
                        for a in 0..model.action_names().len() as u32 {
                            let go = model.action_successors_gc(prev, a, &mut |ev| match ev {
                                GcEvent::Emit(s, act) => consider(s, Some(act)),
                                GcEvent::Collect { .. } => collect_replay(gc, &trace, &prefix, &[]),
                            });
                            match go {
                                Ok(true) => {}
                                Ok(false) => break,
                                Err(e) if e.is_store_full() => return Some(e),
                                Err(_) => break,
                            }
                        }
                    } else if let Err(e) = model.init_states_gc(&mut |ev| match ev {
                        GcEvent::Emit(s, _) => consider(s, None),
                        GcEvent::Collect { .. } => collect_replay(gc, &trace, &prefix, &[]),
                    }) {
                        if e.is_store_full() {
                            return Some(e);
                        }
                    }
                } else if let Some(prev) = prev {
                    let _ = model.successors(prev, &mut |s, a| consider(s, Some(a)));
                } else {
                    let _ = model.init_states_while(&mut |s| consider(s, None));
                }
                None
            })
        };
        if let Some(e) = pred_full.or(gen_full) {
            return TraceBuild::StoreFull(e);
        }
        if let Some(step) = next {
            if model.uses_trace() && !terminal {
                paths.push(Arc::new(PathNode {
                    values: model.state_values(&step.state).expect("a model that uses TLCExt!Trace has state values"),
                    action: step.action,
                    parent: paths.last().cloned(),
                }));
            }
            trace.push(step);
            if terminal {
                return TraceBuild::Rebuilt(Rebuilt { trace, complete: true });
            }
            tried.push(Default::default());
        } else {
            tried.pop();
            if limit.is_some() && trace.len() > prefix.len() {
                prefix = trace.clone();
            }
            if trace.pop().is_none() {
                return match limit {
                    Some(_) => TraceBuild::Rebuilt(Rebuilt { trace: prefix, complete: false }),
                    None => TraceBuild::Unavailable,
                };
            }
            paths.pop();
        }
    }
}

/// Expand `s` during terminal `matches_outcome` verification, reclaiming
/// transient store allocations when `store_gc` is active.
fn replay_expand<M: Model>(
    model: &M,
    s: &M::State,
    store_gc: Option<&dyn StoreGc<M::State>>,
    trace: &[TraceStep<M::State>],
    prefix: &[TraceStep<M::State>],
    mut on_succ: impl FnMut() -> bool,
) -> Result<(), ModelError> {
    if let Some(gc) = store_gc {
        for a in 0..model.action_names().len() as u32 {
            let go = model.action_successors_gc(s, a, &mut |ev| match ev {
                GcEvent::Emit(_, _) => on_succ(),
                GcEvent::Collect { .. } => collect_replay(gc, trace, prefix, &[s]),
            })?;
            if !go {
                break;
            }
        }
        Ok(())
    } else {
        model.successors(s, &mut |_, _| on_succ())
    }
}

/// Check the reported failure under the path to the predecessor, as in the
/// search. A class can contain both a bad action and stuttering, or both
/// failing and non-failing states. Constraints may reject the last state
/// (TLC still checks it), but an evaluation error precedes property checks.
/// Returns `Err(e)` only on value-store budget exhaustion (`e.is_store_full()`).
fn matches_outcome<M: Model>(
    model: &M,
    prev: Option<&M::State>,
    last: &TraceStep<M::State>,
    outcome: &Outcome,
    store_gc: Option<&dyn StoreGc<M::State>>,
    trace: &[TraceStep<M::State>],
    prefix: &[TraceStep<M::State>],
) -> Result<bool, ModelError> {
    use crate::model::ErrorContext;
    let s = &last.state;
    let extra = [s];
    let admitted = replay_pred(store_gc, trace, prefix, &extra, |c| match prev {
        None => model.constraint_gc(s, c),
        Some(p) => crate::model::admits_gc(model, p, s, c),
    });
    if let Err(e) = &admitted {
        if e.is_store_full() {
            return Err(e.clone());
        }
    }
    if let Outcome::Error(expected) = outcome {
        if let ErrorContext::InitialState(rendered) = &expected.context {
            return Ok(model.render(s) == *rendered);
        }
        let check_err = |r: Result<(), ModelError>| match r {
            Err(e) if e.is_store_full() => Err(e),
            Err(e) => Ok(e == *expected),
            Ok(()) => Ok(false),
        };
        if let Err(e) = admitted {
            return Ok(e == *expected);
        }
        if check_err(replay_pred(store_gc, trace, prefix, &extra, |c| model.check_invariants_gc(s, c)).map(|_| ()))? {
            return Ok(true);
        }
        if let Some(p) = prev {
            if check_err(replay_pred(store_gc, trace, prefix, &extra, |c| model.check_transition_gc(p, s, c)).map(|_| ()))? {
                return Ok(true);
            }
        } else if check_err(model.check_init_property(s).map(|_| ()))? {
            return Ok(true);
        }
        if admitted != Ok(true) {
            return Ok(false);
        }
        return with_last_path(model, last, || {
            check_err(replay_expand(model, s, store_gc, trace, prefix, || true).map_err(|e| e.in_next_state()))
        });
    }
    if admitted.is_err() {
        return Ok(false);
    }
    match outcome {
        Outcome::InvariantViolated(name) => match replay_pred(store_gc, trace, prefix, &extra, |c| model.check_invariants_gc(s, c)) {
            Ok(Some(i)) => Ok(model.invariant_names().get(i) == Some(name)),
            Ok(None) => Ok(false),
            Err(e) if e.is_store_full() => Err(e),
            Err(_) => Ok(false),
        },
        Outcome::InitPropertyViolated(name) => match replay_pred(store_gc, trace, prefix, &extra, |c| model.check_invariants_gc(s, c)) {
            Ok(None) => Ok(model.check_init_property(s).ok().flatten().as_ref() == Some(name)),
            Ok(Some(_)) => Ok(false),
            Err(e) if e.is_store_full() => Err(e),
            Err(_) => Ok(false),
        },
        Outcome::ActionPropertyViolated(name) => match prev {
            None => Ok(false),
            Some(p) => match replay_pred(store_gc, trace, prefix, &extra, |c| model.check_transition_gc(p, s, c)) {
                Ok(Some(i)) => Ok(model.action_property_names().get(i) == Some(name)),
                Ok(None) => Ok(false),
                Err(e) if e.is_store_full() => Err(e),
                Err(_) => Ok(false),
            },
        },
        Outcome::Deadlock => {
            if admitted != Ok(true) {
                return Ok(false);
            }
            with_last_path(model, last, || {
                let mut enabled = false;
                match replay_expand(model, s, store_gc, trace, prefix, || {
                    enabled = true;
                    false
                }) {
                    Ok(()) => Ok(!enabled),
                    Err(e) if e.is_store_full() => Err(e),
                    Err(_) => Ok(false),
                }
            })
        }
        _ => Ok(true),
    }
}

/// Expanding the terminal state (deadlock or Next error) needs its whole
/// path, while state/action checks above run under its predecessor's path.
fn with_last_path<M: Model, R>(model: &M, last: &TraceStep<M::State>, f: impl FnOnce() -> R) -> R {
    use crate::live::{self, CurrentPath, PathNode};
    if !model.uses_trace() {
        return f();
    }
    let parent = match live::current_path() {
        Some(CurrentPath::Known(p)) => Some(p),
        _ => None,
    };
    let path = std::sync::Arc::new(PathNode {
        values: model.state_values(&last.state).expect("a model that uses TLCExt!Trace has state values"),
        action: last.action,
        parent,
    });
    live::with_path(Some(CurrentPath::Known(path)), f)
}
