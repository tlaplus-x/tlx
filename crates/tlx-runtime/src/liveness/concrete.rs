//! TLC's liveness algorithm under VIEW or SYMMETRY: a breadth-first search
//! of concrete states streaming its events into the products of the
//! properties (`tlx_live::ConcreteChecker`).

use std::any::Any;
use std::collections::{HashMap, VecDeque};
use std::sync::Mutex;

use tlx_base::hash::{FpMap, FxMap};

use super::expand::{concrete_bits, concrete_successors, ConcreteStep};
use super::shape::{violated, violated_names, Shape};
use super::{error_or_memory, expand_concrete, par_map, ConcreteExpansion, LiveInput, LiveResult, STUTTER};
use crate::explore::TransientFallbackGuard;
use crate::live::LiveStats;
use crate::mem::RssGuard;
use crate::model::{admits_gc, GcEvent, StoreGc, StoreGcRetry};
use crate::{AtomBits, Model, ModelError};

/// How `Concrete` triggers a value-store collection: either standalone
/// (`check_concrete` / `Fired::result`, where `Concrete` owns the `StoreGc`
/// scope) or through an explorer worker safepoint (`Early` inside
/// `explore_observed`).
pub(super) enum GcHook<'a, S> {
    Standalone,
    Park(&'a mut dyn FnMut(&[&S], bool) -> bool),
}

struct ConcreteSuccessorsGc<S> {
    generated: u64,
    admitted: Vec<(S, u32, u64)>,
    rejected_staged: Vec<Box<dyn Any + Send + Sync>>,
    rejected_states: Vec<S>,
}

struct HookExpand<'a, 'b, 'c, M: Model> {
    cx: &'a mut Concrete<'b, M>,
    hook: &'a mut GcHook<'c, M::State>,
}

impl<M: Model> tlx_live::Expand for HookExpand<'_, '_, '_, M> {
    type Error = ModelError;

    fn expand(&mut self, from: u32, idx: u32) -> Result<tlx_live::Expansion, ModelError> {
        self.cx.expand_with(from, idx, self.hook)
    }
}

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
    /// Active BFS frontier queues when running standalone `check_concrete`
    /// with value-store GC enabled so on-demand `Expand::expand` and
    /// mid-level collections keep queued states rooted.
    frontier: VecDeque<(u32, M::State)>,
    next_frontier: VecDeque<(u32, M::State)>,
    /// Whether `Concrete` owns a standalone `StoreGc` scope and may trigger
    /// collections (`true` in `check_concrete` and `Fired::result`, `false`
    /// while embedded inside `Early` during `explore_observed`).
    gc_enabled: bool,
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
            frontier: VecDeque::new(),
            next_frontier: VecDeque::new(),
            gc_enabled: false,
        }
    }

    /// Enable standalone `StoreGc` collections for this `Concrete` instance
    /// (used by `check_concrete` and `Fired::result` outside `explore_observed`).
    pub(super) fn enable_gc(&mut self) {
        self.gc_enabled = self.m.caps().gc.is_some();
    }

    fn gc(&self) -> Option<&'a dyn StoreGc<M::State>> {
        self.gc_enabled.then(|| self.m.caps().gc).flatten()
    }

    /// Collect unreachable value-store nodes, rooting the active BFS frontiers,
    /// the current event's `live` states, any caller-supplied `mark_extra`
    /// roots, and pending thread-local emit handles.
    fn collect_gc(&self, mark_extra: &mut dyn FnMut(&dyn StoreGc<M::State>, &mut dyn FnMut(u64))) -> bool {
        let Some(gc) = self.gc() else {
            return false;
        };
        let mut tls = Vec::new();
        gc.take_thread_roots(&mut tls);
        gc.collect(&mut |mark| {
            for (_, s) in &self.frontier {
                gc.mark_state(s, mark);
            }
            for (_, s) in &self.next_frontier {
                gc.mark_state(s, mark);
            }
            for (s, succ) in self.live.values() {
                gc.mark_state(s, mark);
                for t in succ {
                    gc.mark_state(t, mark);
                }
            }
            mark_extra(gc, mark);
            for &h in &tls {
                mark(h);
            }
            Ok(())
        })
        .is_ok()
    }

    fn active_gc(&self, hook: &GcHook<'_, M::State>) -> Option<&'a dyn StoreGc<M::State>> {
        match hook {
            GcHook::Standalone => self.gc(),
            GcHook::Park(_) => self.m.caps().gc,
        }
    }

    pub(super) fn collect_with(&self, hook: &mut GcHook<'_, M::State>, force_drop: bool, extra: &[&M::State]) -> bool {
        match hook {
            GcHook::Standalone => self.collect_gc(&mut |gc, mark| {
                for s in extra {
                    gc.mark_state(s, mark);
                }
            }),
            GcHook::Park(park) => {
                let mut roots = Vec::with_capacity(extra.len() + self.live.len() * 2);
                for (s, succ) in self.live.values() {
                    roots.push(s);
                    roots.extend(succ.iter());
                }
                roots.extend_from_slice(extra);
                park(&roots, force_drop)
            }
        }
    }

    /// Retry a value-store-allocating atom evaluation across safepoint GC
    /// cycles (falling back to the interpreter on transient single-evaluation
    /// overflow after 2 retries). `collect` is invoked lazily only when `op`
    /// actually hits `StoreFull`, keeping the hot path O(1) with zero root
    /// enumeration overhead.
    pub(super) fn retry_with<T>(
        &self,
        mut op: impl FnMut() -> Result<T, ModelError>,
        mut collect: impl FnMut(&mut GcHook<'_, M::State>, bool) -> bool,
        hook: &mut GcHook<'_, M::State>,
    ) -> Result<T, ModelError> {
        match op() {
            Err(e) if e.is_store_full() => {
                let Some(gc) = self.active_gc(hook) else {
                    return Err(e);
                };
                let mut last = e;
                for stage in StoreGcRetry::STAGES {
                    if !collect(hook, stage.force_drop_archive) {
                        return Err(last);
                    }
                    let _fb = stage.transient_fallback.then(|| TransientFallbackGuard::enter(gc));
                    match op() {
                        Err(e2) if e2.is_store_full() => last = e2,
                        other => return other,
                    }
                }
                gc.mark_full();
                Err(last)
            }
            other => other,
        }
    }

    /// Retry a value-store-allocating atom evaluation in standalone mode.
    fn retry_gc<T>(
        &self,
        mut op: impl FnMut() -> Result<T, ModelError>,
        mut mark_extra: impl FnMut(&dyn StoreGc<M::State>, &mut dyn FnMut(u64)),
    ) -> Result<T, ModelError> {
        match op() {
            Err(e) if e.is_store_full() => {
                let Some(gc) = self.gc() else {
                    return Err(e);
                };
                let mut last = e;
                for stage in StoreGcRetry::STAGES {
                    if !self.collect_gc(&mut mark_extra) {
                        return Err(last);
                    }
                    let _fb = stage.transient_fallback.then(|| TransientFallbackGuard::enter(gc));
                    match op() {
                        Err(e2) if e2.is_store_full() => last = e2,
                        other => return other,
                    }
                }
                gc.mark_full();
                Err(last)
            }
            other => other,
        }
    }

    fn concrete_successors_with(
        &self,
        s: &M::State,
        extra: &[M::State],
        hook: &mut GcHook<'_, M::State>,
    ) -> Result<ConcreteSuccessorsGc<M::State>, ModelError> {
        let Some(gc) = self.active_gc(hook) else {
            let su = concrete_successors(self.m, s)?;
            let generated = su.all.len() as u64;
            let mut admitted = Vec::new();
            let mut rejected_states = Vec::new();
            let want_rej = self.bits.has_action_atoms();
            for (t, a, fp, ok) in su.all {
                if ok {
                    admitted.push((t, a, fp));
                } else if want_rej {
                    rejected_states.push(t);
                }
            }
            return Ok(ConcreteSuccessorsGc { generated, admitted, rejected_staged: Vec::new(), rejected_states });
        };
        let collect_roots = |hook: &mut GcHook<'_, M::State>,
                             force_drop: bool,
                             cur: Option<&M::State>,
                             admitted: &[(M::State, u32, u64)],
                             rejected_states: &[M::State]|
         -> bool {
            let mut roots = Vec::with_capacity(2 + extra.len() + admitted.len() + rejected_states.len());
            roots.push(s);
            if let Some(t) = cur {
                roots.push(t);
            }
            roots.extend(extra.iter());
            for (x, ..) in admitted {
                roots.push(x);
            }
            roots.extend(rejected_states.iter());
            self.collect_with(hook, force_drop, &roots)
        };
        if gc.needs_gc() {
            collect_roots(hook, false, None, &[], &[]);
        }
        let want_rej = self.bits.has_action_atoms();
        let mut generated = 0u64;
        let mut admitted: Vec<(M::State, u32, u64)> = Vec::new();
        let mut rejected_staged: Vec<Box<dyn Any + Send + Sync>> = Vec::new();
        let mut rejected_states: Vec<M::State> = Vec::new();
        let mut err: Option<ModelError> = None;
        for act_idx in 0..self.m.action_names().len() as u32 {
            let go = self.m.action_successors_gc(s, act_idx, &mut |ev| match ev {
                GcEvent::Collect { force_drop_archive } => collect_roots(hook, force_drop_archive, None, &admitted, &rejected_states),
                GcEvent::Emit(t, a) => {
                    if err.is_some() {
                        return false;
                    }
                    generated += 1;
                    let ok = match admits_gc(self.m, s, &t, &mut |force_drop| {
                        collect_roots(hook, force_drop, Some(&t), &admitted, &rejected_states)
                    }) {
                        Ok(ok) => ok,
                        Err(e) => {
                            err = Some(e);
                            return false;
                        }
                    };
                    if ok {
                        let fp = self.m.fingerprint(&t);
                        admitted.push((t, a, fp));
                    } else {
                        if want_rej {
                            if let Some(tok) = self.bits.stage_state(&t) {
                                rejected_staged.push(tok);
                            } else {
                                rejected_states.push(t);
                            }
                        }
                        if gc.needs_gc() && !collect_roots(hook, false, None, &admitted, &rejected_states) {
                            return false;
                        }
                    }
                    true
                }
            });
            if let Some(e) = err {
                if e.is_store_full() {
                    gc.mark_full();
                }
                return Err(e);
            }
            match go {
                Ok(true) => {}
                Ok(false) => break,
                Err(e) => {
                    if e.is_store_full() {
                        gc.mark_full();
                    }
                    return Err(e);
                }
            }
        }
        Ok(ConcreteSuccessorsGc { generated, admitted, rejected_staged, rejected_states })
    }

    pub(super) fn concrete_bits_with(
        &self,
        s: &M::State,
        admitted: Vec<(M::State, u32, u64)>,
        rejected_staged: &[Box<dyn Any + Send + Sync>],
        rejected_states: Vec<M::State>,
        extra: &[M::State],
        hook: &mut GcHook<'_, M::State>,
    ) -> Result<ConcreteExpansion<M::State>, ModelError> {
        let mut collect_initial = |hook: &mut GcHook<'_, M::State>, force_drop: bool| {
            let mut roots: Vec<&M::State> = Vec::with_capacity(1 + extra.len() + admitted.len() + rejected_states.len());
            roots.push(s);
            roots.extend(extra.iter());
            for (t, ..) in &admitted {
                roots.push(t);
            }
            roots.extend(rejected_states.iter());
            self.collect_with(hook, force_drop, &roots)
        };
        let stutter = self.retry_with(|| self.bits.action(s, s), &mut collect_initial, hook)?;
        let s_tab = self.retry_with(|| self.bits.tableau_bits(s), &mut collect_initial, hook)?;

        let mut cut = Vec::with_capacity(rejected_staged.len() + rejected_states.len());
        let mut steps = Vec::with_capacity(admitted.len() + 1);
        steps.push(ConcreteStep { fp: self.m.fingerprint(s), state: s.clone(), bits: s_tab, step: stutter, action: STUTTER });

        let mut rem_adm = admitted.into_iter();
        while let Some((t, a, fp)) = rem_adm.next() {
            let mut collect_adm = |hook: &mut GcHook<'_, M::State>, force_drop: bool| {
                let mut r = Vec::with_capacity(2 + extra.len() + steps.len() + rem_adm.len() + rejected_states.len());
                r.push(s);
                r.push(&t);
                r.extend(extra.iter());
                for c in &steps {
                    r.push(&c.state);
                }
                for (x, ..) in rem_adm.as_slice() {
                    r.push(x);
                }
                r.extend(rejected_states.iter());
                self.collect_with(hook, force_drop, &r)
            };
            let step = self.retry_with(|| self.bits.action(s, &t), &mut collect_adm, hook)?;
            let tab = self.retry_with(|| self.bits.tableau_bits(&t), &mut collect_adm, hook)?;
            steps.push(ConcreteStep { fp, bits: tab, state: t, step, action: a });
        }

        for tok in rejected_staged {
            cut.push(self.bits.action_staged(s, tok.as_ref())?);
        }
        let mut rem_rej = rejected_states.into_iter();
        while let Some(t) = rem_rej.next() {
            let collect_rej = |hook: &mut GcHook<'_, M::State>, force_drop: bool| {
                let mut r = Vec::with_capacity(2 + extra.len() + steps.len() + rem_rej.len());
                r.push(s);
                r.push(&t);
                r.extend(extra.iter());
                for c in &steps {
                    r.push(&c.state);
                }
                r.extend(rem_rej.as_slice().iter());
                self.collect_with(hook, force_drop, &r)
            };
            cut.push(self.retry_with(|| self.bits.action(s, &t), collect_rej, hook)?);
        }

        let outs: Vec<&[u64]> = steps.iter().map(|c| c.step.as_slice()).chain(cut.iter().map(|b| b.as_slice())).collect();
        let collect_state = |hook: &mut GcHook<'_, M::State>, force_drop: bool| {
            let mut r = Vec::with_capacity(1 + extra.len() + steps.len());
            r.push(s);
            r.extend(extra.iter());
            for c in &steps {
                r.push(&c.state);
            }
            self.collect_with(hook, force_drop, &r)
        };
        let sbits = self.retry_with(|| self.bits.state(s, &outs), collect_state, hook)?;
        Ok(ConcreteExpansion { bits: sbits, succ: steps })
    }

    fn expand_concrete_with(
        &self,
        s: &M::State,
        extra: &[M::State],
        hook: &mut GcHook<'_, M::State>,
    ) -> Result<ConcreteExpansion<M::State>, ModelError> {
        if self.active_gc(hook).is_none() {
            return expand_concrete(self.m, self.bits, s);
        }
        let su = self.concrete_successors_with(s, extra, hook)?;
        self.concrete_bits_with(s, su.admitted, &su.rejected_staged, su.rejected_states, extra, hook)
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

    pub(super) fn init_event_with(
        &mut self,
        checker: &mut tlx_live::ConcreteChecker<ModelError>,
        node: u32,
        conc: u32,
        bits: &[u64],
        hook: &mut GcHook<'_, M::State>,
    ) {
        let mut exp = HookExpand { cx: self, hook };
        checker.event(&tlx_live::Event::Init { node, conc, bits: tlx_live::Bits::from_words(bits) }, &mut exp);
    }

    /// The event of the search expanding state `conc` (expansion `e`), for
    /// the products of `checker`; `found(id, state, fp)` is called (after
    /// the event) for each successor the search finds for the first time,
    /// with its state id. `stats`: the search statistics for the states the
    /// event expands on demand (none: those of the search running).
    pub(super) fn next_event(
        &mut self,
        checker: &mut tlx_live::ConcreteChecker<ModelError>,
        conc: u32,
        e: ConcreteExpansion<M::State>,
        stats: Option<LiveStats>,
        found: &mut dyn FnMut(u32, M::State, u64),
    ) {
        self.next_event_with(checker, conc, e, stats, &mut GcHook::Standalone, found);
    }

    pub(super) fn next_event_with(
        &mut self,
        checker: &mut tlx_live::ConcreteChecker<ModelError>,
        conc: u32,
        e: ConcreteExpansion<M::State>,
        stats: Option<LiveStats>,
        hook: &mut GcHook<'_, M::State>,
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
        {
            let mut expander = HookExpand { cx: self, hook };
            match stats {
                Some(p) => at_point(p, || checker.event(&tlx_live::Event::Next { node, exp }, &mut expander)),
                None => checker.event(&tlx_live::Event::Next { node, exp }, &mut expander),
            }
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
    fn successor(
        &self,
        s: &M::State,
        idx: u32,
        memo: Option<&HashMap<u32, M::State>>,
        extra: &[M::State],
        hook: &mut GcHook<'_, M::State>,
    ) -> Result<M::State, ModelError> {
        if idx == STUTTER {
            return Ok(s.clone());
        }
        let m = self.m;
        let (mut i, mut found, mut err) = (0, None, None);
        if let Some(gc) = self.active_gc(hook) {
            let collect_ctx = |hook: &mut GcHook<'_, M::State>, force_drop: bool, t: Option<&M::State>| -> bool {
                let mut roots = Vec::with_capacity(2 + memo.map_or(0, HashMap::len) + extra.len());
                roots.push(s);
                if let Some(t) = t {
                    roots.push(t);
                }
                if let Some(memo) = memo {
                    roots.extend(memo.values());
                }
                roots.extend(extra.iter());
                self.collect_with(hook, force_drop, &roots)
            };
            if gc.needs_gc() {
                collect_ctx(hook, false, None);
            }
            for act_idx in 0..m.action_names().len() as u32 {
                let go = m
                    .action_successors_gc(s, act_idx, &mut |ev| match ev {
                        GcEvent::Collect { force_drop_archive } => collect_ctx(hook, force_drop_archive, None),
                        GcEvent::Emit(t, _) => {
                            let adm = admits_gc(m, s, &t, &mut |force_drop| collect_ctx(hook, force_drop, Some(&t)));
                            match adm {
                                Ok(true) if i == idx => {
                                    found = Some(t);
                                    return false;
                                }
                                Ok(true) => i += 1,
                                Ok(false) => {}
                                Err(e) => {
                                    if e.is_store_full() {
                                        gc.mark_full();
                                    }
                                    err = Some(e);
                                    return false;
                                }
                            }
                            drop(t);
                            if gc.needs_gc() && !collect_ctx(hook, false, None) {
                                return false;
                            }
                            true
                        }
                    })
                    .inspect_err(|e| {
                        if e.is_store_full() {
                            gc.mark_full();
                        }
                    })?;
                if !go {
                    break;
                }
            }
        } else {
            m.successors(s, &mut |t, _| {
                match crate::admits(m, s, &t) {
                    Ok(true) if i == idx => {
                        found = Some(t);
                        return false;
                    }
                    Ok(true) => i += 1,
                    Ok(false) => {}
                    Err(e) => {
                        err = Some(e);
                        return false;
                    }
                }
                true
            })?;
        }
        if let Some(e) = err {
            return Err(e);
        }
        found.ok_or_else(|| ModelError::new(format!("liveness: successor {idx} of a state not found rebuilding a counterexample")))
    }

    /// Expanded state `conc`, rebuilt by re-executing the model (with the
    /// states already rebuilt in `memo`).
    fn rebuild(
        &self,
        conc: u32,
        memo: &mut HashMap<u32, M::State>,
        extra: &[M::State],
        hook: &mut GcHook<'_, M::State>,
    ) -> Result<M::State, ModelError> {
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
            if let Some(gc) = self.active_gc(hook) {
                let collect_ctx = |hook: &mut GcHook<'_, M::State>, force_drop: bool| -> bool {
                    let mut roots = Vec::with_capacity(memo.len() + extra.len());
                    roots.extend(memo.values());
                    roots.extend(extra.iter());
                    self.collect_with(hook, force_drop, &roots)
                };
                if gc.needs_gc() {
                    collect_ctx(hook, false);
                }
                self.m
                    .init_states_gc(&mut |ev| match ev {
                        GcEvent::Collect { force_drop_archive } => collect_ctx(hook, force_drop_archive),
                        GcEvent::Emit(s, _) => {
                            if i == idx {
                                found = Some(s);
                                return false;
                            }
                            i += 1;
                            drop(s);
                            if gc.needs_gc() && !collect_ctx(hook, false) {
                                return false;
                            }
                            true
                        }
                    })
                    .inspect_err(|e| {
                        if e.is_store_full() {
                            gc.mark_full();
                        }
                    })?;
            } else {
                self.m.init_states(&mut |s| {
                    if i == idx {
                        found = Some(s);
                    }
                    i += 1;
                })?;
            }
            let s = found.ok_or_else(|| ModelError::new("liveness: initial state not found rebuilding a counterexample"))?;
            memo.insert(c, s.clone());
            break s;
        };
        for &c in path.iter().rev() {
            s = self.successor(&s, self.origin[c as usize].1, Some(memo), extra, hook)?;
            memo.insert(c, s.clone());
        }
        Ok(s)
    }

    /// The state at a position of a counterexample.
    fn resolve(
        &self,
        c: tlx_live::Conc,
        memo: &mut HashMap<u32, M::State>,
        extra: &[M::State],
        hook: &mut GcHook<'_, M::State>,
    ) -> Result<M::State, ModelError> {
        match c {
            tlx_live::Conc::State(conc) => self.rebuild(conc, memo, extra, hook),
            tlx_live::Conc::Succ { from, idx } => {
                let s = self.rebuild(from, memo, extra, hook)?;
                self.successor(&s, idx, Some(memo), extra, hook)
            }
        }
    }

    fn expand_with(&mut self, from: u32, idx: u32, hook: &mut GcHook<'_, M::State>) -> Result<tlx_live::Expansion, ModelError> {
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
                let mut memo = HashMap::new();
                let s = self.rebuild(from, &mut memo, &[], hook)?;
                drop(memo);
                self.successor(&s, idx, None, &[], hook)?
            }
        };
        let e = self.expand_concrete_with(&t, &[], hook)?;
        self.on_demand += 1;
        let conc = self.state_id((from, idx));
        let e = self.expansion(conc, e);
        self.cache.insert((from, idx), e.clone());
        Ok(e)
    }
}

impl<M: Model> tlx_live::Expand for Concrete<'_, M> {
    type Error = ModelError;

    fn expand(&mut self, from: u32, idx: u32) -> Result<tlx_live::Expansion, ModelError> {
        self.expand_with(from, idx, &mut GcHook::Standalone)
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
    let _gc_guard = m.caps().gc.map(|gc| gc.enter_scope());
    if let Some(gc) = m.caps().gc {
        // Reclaim dead handles left over from the completed search before
        // running the concrete liveness BFS so it starts with the full budget.
        let _ = gc.collect(&mut |_| Ok(()));
    }
    let mut checker = tlx_live::ConcreteChecker::new(&input.formulas(), &input.fairness);
    let mut cx = Concrete::new(m, bits);
    cx.enable_gc();
    if let Err(e) = concrete_search(&mut cx, &mut checker, workers, expanded, guard) {
        record_tlc_liveness(cx.found, cx.steps, cx.on_demand, checker.size(), cx.origin.capacity() * 8);
        return error_or_memory(e);
    }
    cx.frontier.clear();
    cx.next_frontier.clear();
    crate::stats::add_secs("liveness: behavior graph and products (TLC's algorithm)", t0.elapsed());
    record_tlc_liveness(cx.found, cx.steps, cx.on_demand, checker.size(), cx.origin.capacity() * 8);
    let t0 = std::time::Instant::now();
    let r = match checker.finish() {
        Ok(None) => LiveResult::Holds,
        Ok(Some((i, l))) => violation(input, i, &l, &cx),
        Err(e) => LiveResult::Error(e),
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
    checker: &mut tlx_live::ConcreteChecker<ModelError>,
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
    if let Some(gc) = cx.gc() {
        let res = m.init_states_gc(&mut |ev| match ev {
            GcEvent::Collect { .. } => cx.collect_gc(&mut |gc, mark| {
                for (_, s, _) in &inits {
                    gc.mark_state(s, mark);
                }
            }),
            GcEvent::Emit(s, _) => {
                let k = i;
                i += 1;
                generated += 1;
                if err.is_some() {
                    return false;
                }
                if gc.needs_gc() {
                    cx.collect_gc(&mut |gc, mark| {
                        gc.mark_state(&s, mark);
                        for (_, x, _) in &inits {
                            gc.mark_state(x, mark);
                        }
                    });
                }
                let ok = match m.constraint_gc(&s, &mut |_| {
                    cx.collect_gc(&mut |gc, mark| {
                        gc.mark_state(&s, mark);
                        for (_, x, _) in &inits {
                            gc.mark_state(x, mark);
                        }
                    })
                }) {
                    Ok(ok) => ok,
                    Err(e) => {
                        err = Some(e);
                        return false;
                    }
                };
                if ok && cx.find(m.fingerprint(&s)) {
                    let n = inits.len() as u64 + 1;
                    let p = point(generated, cx.found, n, 1, n);
                    match cx.retry_gc(
                        || at_point(p, || bits.tableau_bits(&s)),
                        |gc, mark| {
                            gc.mark_state(&s, mark);
                            for (_, x, _) in &inits {
                                gc.mark_state(x, mark);
                            }
                        },
                    ) {
                        Ok(b) => inits.push((k, s, b)),
                        Err(e) => {
                            err = Some(e);
                            return false;
                        }
                    }
                }
                true
            }
        });
        if let Some(e) = err {
            if e.is_store_full() {
                gc.mark_full();
            }
            return Err(e);
        }
        if let Err(e) = res {
            if e.is_store_full() {
                gc.mark_full();
            }
            return Err(e);
        }
    } else {
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
    }
    let initial = inits.len() as u64;
    if cx.gc().is_some() {
        let mut events = Vec::with_capacity(inits.len());
        cx.frontier.reserve(inits.len());
        for (k, s, b) in inits {
            let conc = cx.state_id((NO_STATE, k));
            let node = cx.node(m.fingerprint(&s));
            cx.frontier.push_back((conc, s));
            events.push((node, conc, b));
        }
        for (node, conc, b) in events {
            checker.event(&tlx_live::Event::Init { node, conc, bits: tlx_live::Bits::from_words(&b) }, cx);
        }
        let mut depth = 1u64;
        while !cx.frontier.is_empty() && expand > 0 {
            while let Some((conc, s)) = cx.frontier.pop_front() {
                if expand == 0 {
                    cx.frontier.push_front((conc, s));
                    break;
                }
                guard
                    .check(&|| {
                        let (n, e, _) = checker.size();
                        format!("its behavior graph and products ({} states found, {n} product nodes, {e} product edges so far)", cx.found)
                    })
                    .map_err(ModelError::new)?;
                expand -= 1;
                let su = cx.concrete_successors_with(&s, &[], &mut GcHook::Standalone)?;
                generated += su.generated;
                let mut fresh = tlx_base::hash::IdMap::<()>::default();
                let (mut found, mut queued) = (cx.found, (cx.frontier.len() + cx.next_frontier.len()) as u64);
                for &(_, _, fp) in &su.admitted {
                    if !cx.is_found(fp) && fresh.insert(fp, ()).is_none() {
                        found += 1;
                        queued += 1;
                    }
                }
                let diameter = if cx.next_frontier.is_empty() && fresh.is_empty() { depth } else { depth + 1 };
                let p = point(generated, found, queued, diameter, initial);
                let e = at_point(p, || {
                    cx.concrete_bits_with(&s, su.admitted, &su.rejected_staged, su.rejected_states, &[], &mut GcHook::Standalone)
                })?;
                drop(s);
                let mut added = Vec::new();
                cx.next_event(checker, conc, e, Some(p), &mut |id, t, _| added.push((id, t)));
                cx.next_frontier.extend(added);
            }
            std::mem::swap(&mut cx.frontier, &mut cx.next_frontier);
            cx.next_frontier.clear();
            depth += 1;
        }
        return Ok(());
    }
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
    let mut states = Vec::with_capacity(l.prefix.len() + l.cycle.len());
    for s in l.prefix.iter().chain(&l.cycle) {
        match cx.resolve(s.conc, &mut memo, &states, &mut GcHook::Standalone) {
            Ok(st) => states.push(st),
            Err(e) => return LiveResult::Error(e),
        }
    }
    drop(memo);
    let seq: Vec<(u32, &M::State, u32)> = l.prefix.iter().chain(&l.cycle).zip(&states).map(|(s, st)| (s.node, st, s.label)).collect();
    let sh = Shape::new(&seq, l.prefix.len());
    // As TLC, the atoms are evaluated on the states shown (with SYMMETRY,
    // the cycle may close on a state symmetric to the successor of its last
    // state).
    let mut state_full: Option<ModelError> = None;
    let mut step_full: Option<ModelError> = None;
    let names = violated_names(
        input,
        &sh,
        &mut |k| {
            cx.expand_concrete_with(seq[sh.shown[k].pos].1, &states, &mut GcHook::Standalone)
                .map(|e| std::borrow::Cow::Owned(tlx_live::Bits::from_words(&e.bits)))
                .map_err(|e| {
                    let msg = e.message.clone();
                    if e.is_store_full() {
                        state_full = Some(e);
                    }
                    msg
                })
        },
        &mut |k| {
            let a = seq[sh.shown[k].pos].1;
            let b = seq[sh.shown[sh.next(k)].pos].1;
            cx.retry_gc(
                || cx.bits.action(a, b),
                |gc, mark| {
                    for x in &states {
                        gc.mark_state(x, mark);
                    }
                },
            )
            .map(|w| std::borrow::Cow::Owned(tlx_live::Bits::from_words(&w)))
            .map_err(|e| {
                let msg = e.message.clone();
                if e.is_store_full() {
                    step_full = Some(e);
                }
                msg
            })
        },
    );
    if let Some(e) = state_full.or(step_full) {
        return LiveResult::Error(e);
    }
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
