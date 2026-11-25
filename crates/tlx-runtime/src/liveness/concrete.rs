//! TLC's liveness algorithm under VIEW or SYMMETRY: a breadth-first search
//! of concrete states streaming its events into the products of the
//! properties (`tlx_live::ConcreteChecker`).

use std::collections::{HashMap, VecDeque};
use std::sync::Mutex;

use tlx_base::hash::{FpMap, FxMap};

use super::expand::{concrete_bits, concrete_successors};
use super::shape::{step_bits, violated, violated_names, Shape};
use super::{error_or_memory, expand_concrete, par_map, ConcreteExpansion, LiveInput, LiveResult, STUTTER};
use crate::live::LiveStats;
use crate::mem::RssGuard;
use crate::{AtomBits, Model, ModelError};

/// The concrete states of TLC's liveness algorithm under VIEW or SYMMETRY,
/// where graph nodes are fingerprints. States are not kept: each expanded
/// state has an id and is known by how it was reached (an initial state, or
/// a successor of another expanded state), so the states of a
/// counterexample are rebuilt by re-executing the model. Only the states
/// expanded for the current event (and their successors) are at hand, for
/// the products' expansions on demand.
pub(super) struct Concrete<'a, M: Model> {
    pub(super) m: &'a M,
    pub(super) bits: &'a (dyn AtomBits<M::State> + Sync),
    /// The graph node of each fingerprint (numbered in order of insertion),
    /// with `FOUND` set once the search found it.
    nodes: FpMap,
    found: u64,
    /// How each expanded state was reached: `(NO_STATE, i)`, the `i`-th
    /// initial state the model enumerates, or `(from, idx)`, successor
    /// `idx` of state `from` (see `successor`).
    origin: Vec<(u32, u32)>,
    /// The states expanded for the current event, with their successors.
    live: FxMap<u32, (M::State, Vec<M::State>)>,
    /// The expansions on demand of the current event.
    cache: FxMap<(u32, u32), tlx_live::Expansion>,
    steps: u64,
    on_demand: u64,
}

/// `Concrete::origin` of an initial state.
pub(super) const NO_STATE: u32 = u32::MAX;

/// The flag of `Concrete::nodes` marking the fingerprints found by the search.
const FOUND: u32 = 1 << 31;

impl<'a, M: Model> Concrete<'a, M> {
    pub(super) fn new(m: &'a M, bits: &'a (dyn AtomBits<M::State> + Sync)) -> Self {
        Concrete {
            m,
            bits,
            nodes: FpMap::new(),
            found: 0,
            origin: Vec::new(),
            live: FxMap::default(),
            cache: FxMap::default(),
            steps: 0,
            on_demand: 0,
        }
    }

    /// The value of `fp` in `nodes`; a new node (the next number) if it
    /// has none.
    fn entry(&mut self, fp: u64) -> &mut u32 {
        let next = self.nodes.len() as u32;
        self.nodes.get_or_insert_with(fp, || next)
    }

    pub(super) fn node(&mut self, fp: u64) -> u32 {
        *self.entry(fp) & !FOUND
    }

    /// Whether the search has found fingerprint `fp`.
    fn is_found(&self, fp: u64) -> bool {
        self.nodes.get(fp).is_some_and(|id| id & FOUND != 0)
    }

    /// The number of distinct fingerprints among `fps` the search has not
    /// found.
    pub(super) fn count_new(&self, fps: impl Iterator<Item = u64>) -> u64 {
        let mut fresh = tlx_base::hash::IdMap::<()>::default();
        fps.filter(|&fp| !self.is_found(fp) && fresh.insert(fp, ()).is_none()).count() as u64
    }

    /// Whether the search finds fingerprint `fp` for the first time.
    pub(super) fn find(&mut self, fp: u64) -> bool {
        let id = self.entry(fp);
        let new = *id & FOUND == 0;
        *id |= FOUND;
        self.found += u64::from(new);
        new
    }

    /// A new expanded state, reached as `origin`.
    pub(super) fn state_id(&mut self, origin: (u32, u32)) -> u32 {
        self.origin.push(origin);
        self.origin.len() as u32 - 1
    }

    /// The expansion of state `conc` (its stuttering step first, then its
    /// successors in the model: `Succ::idx` is `STUTTER` or the position
    /// among them); the state and its successors are kept for the event.
    fn expansion(&mut self, conc: u32, e: ConcreteExpansion<M::State>) -> tlx_live::Expansion {
        let mut succ = Vec::with_capacity(e.succ.len());
        let mut states = Vec::with_capacity(e.succ.len().saturating_sub(1));
        let mut this = None;
        for (k, c) in e.succ.into_iter().enumerate() {
            let node = self.node(c.fp);
            let idx = if k == 0 { STUTTER } else { k as u32 - 1 };
            succ.push(tlx_live::Succ {
                node,
                idx,
                bits: tlx_live::Bits::from_words(&c.bits),
                step: tlx_live::Bits::from_words(&c.step),
                label: c.action,
            });
            if k == 0 {
                this = Some(c.state);
            } else {
                states.push(c.state);
            }
        }
        self.steps += succ.len() as u64;
        self.live.insert(conc, (this.expect("stuttering step"), states));
        tlx_live::Expansion { conc, bits: tlx_live::Bits::from_words(&e.bits), succ }
    }

    /// The end of an event: its states are no longer needed.
    fn end_event(&mut self) {
        self.live.clear();
        self.cache.clear();
    }

    /// The event of the search expanding state `conc` (expansion `e`), for
    /// the products of `checker`; `found(id, state, fp)` is called (after
    /// the event) for each successor the search finds for the first time,
    /// with its state id. `stats`: the search statistics for the states the
    /// event expands on demand (none: those of the search running).
    pub(super) fn next_event(
        &mut self,
        checker: &mut tlx_live::ConcreteChecker,
        conc: u32,
        e: ConcreteExpansion<M::State>,
        stats: Option<LiveStats>,
        found: &mut dyn FnMut(u32, M::State, u64),
    ) {
        let mut new = Vec::new();
        for (k, c) in e.succ[1..].iter().enumerate() {
            if self.find(c.fp) {
                new.push((k, self.state_id((conc, k as u32)), c.fp));
            }
        }
        let node = self.node(e.succ[0].fp);
        let mut exp = self.expansion(conc, e);
        // TLC's search adds the stuttering step after the successors (but
        // TLC's expansion of other states puts it first).
        exp.succ.rotate_left(1);
        match stats {
            Some(p) => at_point(p, || checker.event(&tlx_live::Event::Next { node, exp }, self)),
            None => checker.event(&tlx_live::Event::Next { node, exp }, self),
        }
        // (The new states are moved out of the event's states, not copied.)
        let (_, succ) = self.live.remove(&conc).expect("the event's state");
        let mut new = new.into_iter().peekable();
        for (k, t) in succ.into_iter().enumerate() {
            if let Some((_, id, fp)) = new.next_if(|&(j, ..)| j == k) {
                found(id, t, fp);
            }
        }
        self.end_event();
    }

    /// Successor `idx` of `s` (as in `expansion`).
    fn successor(&self, s: &M::State, idx: u32) -> Result<M::State, String> {
        if idx == STUTTER {
            return Ok(s.clone());
        }
        let m = self.m;
        let (mut i, mut found, mut err) = (0, None, None);
        m.successors(s, &mut |t, _| {
            match crate::admits(m, s, &t) {
                Ok(true) if i == idx => {
                    found = Some(t);
                    return false;
                }
                Ok(true) => i += 1,
                Ok(false) => {}
                Err(e) => {
                    err = Some(e.message);
                    return false;
                }
            }
            true
        })
        .map_err(|e| e.message)?;
        if let Some(e) = err {
            return Err(e);
        }
        found.ok_or_else(|| format!("liveness: successor {idx} of a state not found rebuilding a counterexample"))
    }

    /// Expanded state `conc`, rebuilt by re-executing the model (with the
    /// states already rebuilt in `memo`).
    fn rebuild(&self, conc: u32, memo: &mut HashMap<u32, M::State>) -> Result<M::State, String> {
        let mut path = Vec::new();
        let mut c = conc;
        let mut s = loop {
            if let Some(s) = memo.get(&c) {
                break s.clone();
            }
            let (from, idx) = self.origin[c as usize];
            if from != NO_STATE {
                path.push(c);
                c = from;
                continue;
            }
            let (mut i, mut found) = (0, None);
            self.m
                .init_states(&mut |s| {
                    if i == idx {
                        found = Some(s);
                    }
                    i += 1;
                })
                .map_err(|e| e.message)?;
            let s = found.ok_or("liveness: initial state not found rebuilding a counterexample")?;
            memo.insert(c, s.clone());
            break s;
        };
        for &c in path.iter().rev() {
            s = self.successor(&s, self.origin[c as usize].1)?;
            memo.insert(c, s.clone());
        }
        Ok(s)
    }

    /// The state at a position of a counterexample.
    fn resolve(&self, c: tlx_live::Conc, memo: &mut HashMap<u32, M::State>) -> Result<M::State, String> {
        match c {
            tlx_live::Conc::State(conc) => self.rebuild(conc, memo),
            tlx_live::Conc::Succ { from, idx } => {
                let s = self.rebuild(from, memo)?;
                self.successor(&s, idx)
            }
        }
    }
}

impl<M: Model> tlx_live::Expand for Concrete<'_, M> {
    fn expand(&mut self, from: u32, idx: u32) -> Result<tlx_live::Expansion, String> {
        if let Some(e) = self.cache.get(&(from, idx)) {
            return Ok(e.clone());
        }
        let t = match self.live.get(&from) {
            Some((s, succ)) => {
                if idx == STUTTER {
                    s.clone()
                } else {
                    succ[idx as usize].clone()
                }
            }
            None => {
                let s = self.rebuild(from, &mut HashMap::new())?;
                self.successor(&s, idx)?
            }
        };
        let e = expand_concrete(self.m, self.bits, &t).map_err(|e| e.message)?;
        self.on_demand += 1;
        let conc = self.state_id((from, idx));
        let e = self.expansion(conc, e);
        self.cache.insert((from, idx), e.clone());
        Ok(e)
    }
}

/// Check the temporal properties TLC's way on the state space of `m`: a
/// breadth-first search like TLC's (the first state found of each
/// fingerprint is expanded) streams its events into the products of all
/// properties. It expands the first `expanded` states only (see `check`).
pub(super) fn check_concrete<M: Model>(
    m: &M,
    input: &LiveInput,
    bits: &(dyn AtomBits<M::State> + Sync),
    workers: usize,
    expanded: usize,
    guard: RssGuard,
) -> LiveResult<M::State> {
    let t0 = std::time::Instant::now();
    let mut checker = tlx_live::ConcreteChecker::new(&input.formulas(), &input.fairness);
    let mut cx = Concrete::new(m, bits);
    if let Err(e) = concrete_search(&mut cx, &mut checker, workers, expanded, guard) {
        record_tlc_liveness(cx.found, cx.steps, cx.on_demand, checker.size(), cx.origin.capacity() * 8);
        return error_or_memory(e);
    }
    crate::stats::add_secs("liveness: behavior graph and products (TLC's algorithm)", t0.elapsed());
    record_tlc_liveness(cx.found, cx.steps, cx.on_demand, checker.size(), cx.origin.capacity() * 8);
    let t0 = std::time::Instant::now();
    let r = match checker.finish() {
        Ok(None) => LiveResult::Holds,
        Ok(Some((i, l))) => violation(input, i, &l, &cx),
        Err(e) => LiveResult::Error(e.into()),
    };
    crate::stats::add_secs("liveness: check (TLC's algorithm)", t0.elapsed());
    r
}

/// `f` with `stats` as the search statistics on this thread: TLC's
/// statistics at a point of its search, for `TLCGet("stats")` (and
/// `"queue"`, ...) in the liveness predicates evaluated then. The previous
/// source, if any, is restored afterwards, also when `f` panics.
pub(super) fn at_point<R>(stats: LiveStats, f: impl FnOnce() -> R) -> R {
    crate::live::with_source(&stats, f)
}

/// The breadth-first search of TLC's liveness algorithm: each part of a BFS
/// level is expanded by `workers` threads, the events follow in order. It
/// stops after `expand` states: those found but not expanded have no event
/// then (TLC's LiveWorker skips such nodes: no behavior goes on from them,
/// not even by stuttering).
///
/// Under VIEW or SYMMETRY this search is TLC's search itself, which
/// evaluates the liveness predicates as it goes (`LiveCheck.addInitState`
/// on each new initial state once it is queued, `addNextState` once all
/// successors of a state are generated and the new ones queued): a
/// predicate that reads the search statistics (`TLCGet("queue")`, as trace
/// validation specs do) sees TLC's values at that point.
fn concrete_search<M: Model>(
    cx: &mut Concrete<M>,
    checker: &mut tlx_live::ConcreteChecker,
    workers: usize,
    mut expand: usize,
    guard: RssGuard,
) -> Result<(), ModelError> {
    let (m, bits) = (cx.m, cx.bits);
    let t0 = std::time::Instant::now();
    let point = |generated: u64, distinct: u64, queue: u64, diameter: u64, initial: u64| LiveStats {
        generated,
        distinct,
        queue,
        diameter,
        initial,
        duration_secs: t0.elapsed().as_secs(),
    };
    let (mut inits, mut err, mut i, mut generated) = (Vec::new(), None, 0u32, 0u64);
    m.init_states(&mut |s| {
        let k = i;
        i += 1;
        generated += 1;
        if err.is_some() {
            return;
        }
        let r = m.constraint(&s).and_then(|ok| {
            Ok(if ok && cx.find(m.fingerprint(&s)) {
                let n = inits.len() as u64 + 1;
                Some(at_point(point(generated, cx.found, n, 1, n), || bits.tableau_bits(&s))?)
            } else {
                None
            })
        });
        match r {
            Ok(Some(b)) => inits.push((k, s, b)),
            Ok(None) => {}
            Err(e) => err = Some(e),
        }
    })?;
    if let Some(e) = err {
        return Err(e);
    }
    let initial = inits.len() as u64;
    let mut level = VecDeque::with_capacity(inits.len());
    for (k, s, b) in inits {
        let conc = cx.state_id((NO_STATE, k));
        let node = cx.node(m.fingerprint(&s));
        checker.event(&tlx_live::Event::Init { node, conc, bits: tlx_live::Bits::from_words(&b) }, cx);
        level.push_back((conc, s));
    }
    // Expanded in parts, to bound the successor states held at a time; a
    // part's states are dropped once expanded, so that a level and the next
    // are not both held whole.
    let part = 1024 * workers.max(1);
    let mut depth = 1u64;
    while !level.is_empty() && expand > 0 {
        let mut next = VecDeque::new();
        while !level.is_empty() && expand > 0 {
            guard
                .check(&|| {
                    let (n, e, _) = checker.size();
                    format!("its behavior graph and products ({} states found, {n} product nodes, {e} product edges so far)", cx.found)
                })
                .map_err(ModelError::new)?;
            let states: Vec<(u32, M::State)> = level.drain(..part.min(level.len()).min(expand)).collect();
            expand -= states.len();
            let succs = par_map(&states, workers, &|(_, s): &(u32, M::State)| concrete_successors(m, s))?;
            // TLC's statistics after the expansion of each state of the part
            // (the new states found by the states before it are not new).
            let mut points = Vec::with_capacity(states.len());
            let mut fresh = tlx_base::hash::IdMap::<()>::default();
            let (mut found, mut queued) = (cx.found, (level.len() + states.len() + next.len()) as u64);
            for su in &succs {
                generated += su.all.len() as u64;
                queued -= 1;
                for &(_, _, fp, ok) in &su.all {
                    if ok && !cx.is_found(fp) && fresh.insert(fp, ()).is_none() {
                        found += 1;
                        queued += 1;
                    }
                }
                let diameter = if fresh.is_empty() { depth } else { depth + 1 };
                points.push(point(generated, found, queued, diameter, initial));
            }
            // (Each successor list is moved into its evaluation.)
            let work: Vec<_> = states.iter().zip(succs.into_iter().map(|su| Mutex::new(Some(su)))).zip(points.iter().copied()).collect();
            let exps = par_map(&work, workers, &|(((_, s), su), p)| {
                let su = su.lock().unwrap().take().expect("each part's successors are evaluated once");
                at_point(*p, || concrete_bits(m, bits, s, su))
            })?;
            for (((conc, s), e), p) in states.into_iter().zip(exps).zip(points) {
                drop(s);
                cx.next_event(checker, conc, e, Some(p), &mut |id, s, _| next.push_back((id, s)));
            }
        }
        level = next;
        depth += 1;
    }
    Ok(())
}

/// The violation of part `prop` of `input` with the counterexample `l` of
/// TLC's algorithm, its states rebuilt by `cx`.
pub(super) fn violation<M: Model>(input: &LiveInput, prop: usize, l: &tlx_live::CLasso, cx: &Concrete<M>) -> LiveResult<M::State> {
    let mut memo = HashMap::new();
    let states: Result<Vec<M::State>, String> = l.prefix.iter().chain(&l.cycle).map(|s| cx.resolve(s.conc, &mut memo)).collect();
    let states = match states {
        Ok(s) => s,
        Err(e) => return LiveResult::Error(e.into()),
    };
    let seq: Vec<(u32, &M::State, u32)> = l.prefix.iter().chain(&l.cycle).zip(&states).map(|(s, st)| (s.node, st, s.label)).collect();
    let sh = Shape::new(&seq, l.prefix.len());
    // As TLC, the atoms are evaluated on the states shown (with SYMMETRY,
    // the cycle may close on a state symmetric to the successor of its last
    // state).
    let names = violated_names(
        input,
        &sh,
        &mut |k| {
            expand_concrete(cx.m, cx.bits, seq[sh.shown[k].pos].1)
                .map(|e| std::borrow::Cow::Owned(tlx_live::Bits::from_words(&e.bits)))
                .map_err(|e| e.message)
        },
        &mut |k| step_bits(cx.bits, seq[sh.shown[k].pos].1, seq[sh.shown[sh.next(k)].pos].1),
    );
    violated(names, prop, &seq, &sh)
}

/// Record the sizes of TLC's liveness algorithm (VIEW or SYMMETRY): graph
/// states and steps, states expanded on demand, product nodes and edges,
/// and the memory of the products and of the expanded states' origins
/// (`origin_bytes`; the states themselves are not kept).
fn record_tlc_liveness(states: u64, steps: u64, on_demand: u64, product: (usize, usize, usize), origin_bytes: usize) {
    use crate::stats::{self, Metric};
    if !stats::on() {
        return;
    }
    stats::set("liveness: graph states", Metric::Count(states));
    stats::set("liveness: graph edges", Metric::Count(steps));
    stats::set("liveness: states expanded on demand", Metric::Count(on_demand));
    stats::set("liveness: product nodes", Metric::Count(product.0 as u64));
    stats::set("liveness: product edges", Metric::Count(product.1 as u64));
    stats::set(&format!("{}liveness products (TLC's algorithm) (est.)", stats::MEMORY), Metric::Bytes(product.2 as u64));
    stats::set(&format!("{}liveness state origins (TLC's algorithm)", stats::MEMORY), Metric::Bytes(origin_bytes as u64));
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn at_point_primes_and_restores_the_statistics() {
        let point = |distinct| LiveStats { distinct, ..LiveStats::default() };
        assert_eq!(crate::live::current(), None);
        at_point(point(7), || {
            assert_eq!(crate::live::current().unwrap().distinct, 7);
            // A nested point shadows the outer one, which comes back after it.
            at_point(point(9), || assert_eq!(crate::live::current().unwrap().distinct, 9));
            assert_eq!(crate::live::current().unwrap().distinct, 7);
        });
        assert_eq!(crate::live::current(), None);
    }

    #[test]
    fn at_point_restores_the_previous_source_on_unwind() {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            at_point(LiveStats { distinct: 7, ..LiveStats::default() }, || panic!("boom"))
        }));
        assert!(r.is_err());
        assert_eq!(crate::live::current(), None);
    }
}
