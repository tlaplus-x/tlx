use std::collections::VecDeque;
use std::ops::Range;
use std::sync::Arc;

use super::*;
use crate::search::{find_fair_cycle, lits_hold, PLasso, Prod, NONE};
use crate::tableau::Automaton;
use crate::Bits;

// ---------------------------------------------------------------------------
// The product, built in TLC's order.

/// The bit sets of the products (state-atom bits of states, action-atom
/// bits of steps), interned: products refer to them by number.
pub(super) struct Pats {
    pats: tlx_base::hash::Interner<Box<[u64]>, Bits, std::collections::hash_map::RandomState>,
}

impl Pats {
    pub(super) fn new() -> Pats {
        let mut p = Pats { pats: Default::default() };
        p.id(&Bits::new());
        p
    }

    /// The number of `b` (0 for the empty set).
    fn id(&mut self, b: &Bits) -> u32 {
        let w = b.words();
        self.pats.intern_with(w, || (w.into(), b.clone()))
    }

    pub(super) fn bytes(&self) -> usize {
        self.pats.capacity() * std::mem::size_of::<Bits>()
            + self.pats.map_capacity() * (std::mem::size_of::<(Box<[u64]>, u32)>() + 1)
            + self.pats.iter().map(|b| b.words().len() * 16).sum::<usize>()
    }
}

#[derive(Clone)]
struct TEdge {
    to: u32,
    /// Action-atom bits of the step (`Pats` number).
    step: u32,
    /// The successor index of the step (`Succ::idx`) or, in the product of
    /// a trace, the concrete state it leads to.
    idx: u32,
    label: u32,
}

/// A frame of the (iterative) expansion of a product node.
struct Frame<'e> {
    v: u32,
    exp: Cow<'e, Expansion>,
    sidx: usize,
    k: usize,
    /// The `Pats` number of the bits of step `sidx` (`NONE`: not yet known).
    step: u32,
    /// The edges of `v` so far.
    out: Vec<TEdge>,
}

pub(super) struct TProduct {
    aut: Arc<Automaton>,
    /// With a tableau (`TableauLiveChecker`) or without (`LiveChecker`).
    tableau: bool,
    /// The product of a trace (`build_trace`).
    trace: bool,
    // Per product node: graph node, tableau node, the state-atom bits
    // (`Pats` number) and the concrete state of the state that expanded it
    // (`NONE` if none did), the next product node of the same graph node.
    gnode: Vec<u32>,
    aq: Vec<u32>,
    bits: Vec<u32>,
    xconc: Vec<u32>,
    next: Vec<u32>,
    /// Per graph node: its first and last product nodes (`NONE` if none).
    ends: Vec<[u32; 2]>,
    /// The concrete state of each initial node.
    init: Vec<(u32, u32)>,
    /// Graph nodes expanded by the search (TLC: `isDone`).
    done: Vec<bool>,
    /// Graph nodes written to TLC's disk graph (`LiveChecker` only).
    written: Vec<bool>,
    /// The edges of node `v` are `edges[start[v]..start[v] + len[v]]`,
    /// stored when its expansion ends (a node is expanded once).
    start: Vec<usize>,
    len: Vec<u32>,
    edges: Vec<TEdge>,
    /// The state-atom bits (`Pats` number) of the state each edge leaves, in
    /// the product of a trace (otherwise, those of the node: `bits`).
    esrc: Vec<u32>,
    /// The edges of each node of the product of a trace (to which
    /// `build_trace` adds in any order) with their `esrc`, stored by
    /// `finish`.
    pending: Vec<Vec<(TEdge, u32)>>,
    parent: Vec<(u32, usize)>,
    /// Per tableau node: whether it is an accepting sink of a solution with
    /// an error model without cycle conditions (empty if none is).
    pub(super) sinks: Vec<bool>,
    /// The product node whose expansion found such a sink (TLC's
    /// `errorGraphNode`): see `ConcreteChecker::fired`.
    pub(super) fire: Option<u32>,
}

impl TProduct {
    pub(super) fn new(aut: Arc<Automaton>, tableau: bool) -> TProduct {
        TProduct {
            aut,
            tableau,
            trace: false,
            gnode: Vec::new(),
            aq: Vec::new(),
            bits: Vec::new(),
            xconc: Vec::new(),
            next: Vec::new(),
            ends: Vec::new(),
            init: Vec::new(),
            done: Vec::new(),
            written: Vec::new(),
            start: Vec::new(),
            len: Vec::new(),
            edges: Vec::new(),
            esrc: Vec::new(),
            pending: Vec::new(),
            parent: Vec::new(),
            sinks: Vec::new(),
            fire: None,
        }
    }

    /// Adds the nodes and edges of the next event of the search.
    pub(super) fn event<X: Expand + ?Sized>(&mut self, ev: &Event, ex: &mut X, pats: &mut Pats) -> Result<(), X::Error> {
        let aut = Arc::clone(&self.aut);
        match ev {
            Event::Init { node, conc, bits } => {
                for &q in &aut.init {
                    if lits_hold(&aut.states[q as usize].state_lits, bits) {
                        let (v, fresh) = self.node(*node, q);
                        if fresh {
                            self.init.push((v, *conc));
                        }
                    }
                }
            }
            Event::Next { node, exp } => {
                self.grow(*node);
                self.done[*node as usize] = true;
                if self.tableau {
                    for v in self.nodes_of(*node) {
                        self.expand(v, Cow::Borrowed(exp), ex, pats)?;
                    }
                } else {
                    let v = self.node(*node, 0).0;
                    self.expand(v, Cow::Borrowed(exp), ex, pats)?;
                    self.written[*node as usize] = true;
                }
            }
        }
        Ok(())
    }

    /// The number of product nodes and edges, and an estimate of their
    /// memory in bytes.
    pub(super) fn size(&self) -> (usize, usize, usize) {
        let n = self.gnode.len();
        let e = self.edges.len();
        let b = self.gnode.capacity() * 4 * 5
            + self.start.capacity() * 12
            + self.ends.capacity() * 10
            + self.edges.capacity() * std::mem::size_of::<TEdge>()
            + self.esrc.capacity() * 4;
        (n, e, b)
    }

    fn grow(&mut self, g: u32) {
        let n = g as usize + 1;
        if self.ends.len() < n {
            self.ends.resize(n, [NONE, NONE]);
            self.done.resize(n, false);
            self.written.resize(n, false);
        }
    }

    /// The product nodes of graph node `g`, in creation order.
    fn nodes_of(&self, g: u32) -> Vec<u32> {
        let mut out = Vec::new();
        let mut v = self.ends.get(g as usize).map_or(NONE, |e| e[0]);
        while v != NONE {
            out.push(v);
            v = self.next[v as usize];
        }
        out
    }

    /// The product of one behavior (TLC's simulation mode:
    /// `LiveCheck1.constructBEGraph`).
    pub(super) fn build_trace(&mut self, trace: &[TraceState], pats: &mut Pats) {
        let p = self;
        p.trace = true;
        let (aut, tableau) = (Arc::clone(&p.aut), p.tableau);
        let s0 = &trace[0];
        if !tableau {
            let mut src = p.node(s0.node, 0).0;
            p.bits[src as usize] = pats.id(&s0.bits);
            p.init.push((src, s0.conc));
            p.edge(src, src, &s0.bits, &s0.stutter, s0.conc, STUTTER, pats);
            for (i, s) in trace.iter().enumerate().skip(1) {
                let prev = &trace[i - 1].bits;
                let (dest, fresh) = p.node(s.node, 0);
                if fresh {
                    // (TLC evaluates the new node's state predicates on the
                    // previous state.)
                    p.bits[dest as usize] = pats.id(prev);
                    p.edge(dest, dest, &s.bits, &s.stutter, s.conc, STUTTER, pats);
                    p.edge(src, dest, prev, &s.step, s.conc, s.label, pats);
                } else if !p.pending[src as usize].iter().any(|(e, _)| e.to == dest) {
                    p.edge(src, dest, prev, &s.step, s.conc, s.label, pats);
                }
                src = dest;
            }
            return;
        }
        let mut srcs = Vec::new();
        for &q in &aut.init {
            if lits_hold(&aut.states[q as usize].state_lits, &s0.bits) {
                let v = p.node(s0.node, q).0;
                p.bits[v as usize] = pats.id(&s0.bits);
                p.init.push((v, s0.conc));
                srcs.push(v);
            }
        }
        for &v in &srcs {
            for &q1 in &aut.states[p.aq[v as usize] as usize].succ {
                if let Some(w) = p.find(s0.node, q1) {
                    p.edge(v, w, &s0.bits, &s0.stutter, s0.conc, STUTTER, pats);
                }
            }
        }
        for (i, s) in trace.iter().enumerate().skip(1) {
            let mut dests = Vec::new();
            for &v in &srcs {
                p.trace_step(v, s, &trace[i - 1].bits, &s.step, s.label, &mut dests, pats);
            }
            let mut j = 0;
            while j < dests.len() {
                p.trace_step(dests[j], s, &s.bits, &s.stutter, STUTTER, &mut dests, pats);
                j += 1;
            }
            srcs = dests;
        }
    }

    /// Edges from `v` to the nodes of state `s` (by step `step` from a state
    /// with bits `src`), creating consistent new ones (added to `dests`).
    #[allow(clippy::too_many_arguments)]
    fn trace_step(&mut self, v: u32, s: &TraceState, src: &Bits, step: &Bits, label: u32, dests: &mut Vec<u32>, pats: &mut Pats) {
        let aut = Arc::clone(&self.aut);
        for &q1 in &aut.states[self.aq[v as usize] as usize].succ {
            match self.find(s.node, q1) {
                None => {
                    if lits_hold(&aut.states[q1 as usize].state_lits, &s.bits) {
                        let w = self.node(s.node, q1).0;
                        self.bits[w as usize] = pats.id(&s.bits);
                        self.edge(v, w, src, step, s.conc, label, pats);
                        dests.push(w);
                    }
                }
                Some(w) => {
                    if !self.pending[v as usize].iter().any(|(e, _)| e.to == w) {
                        self.edge(v, w, src, step, s.conc, label, pats);
                    }
                }
            }
        }
    }

    /// An edge of the product of a trace.
    #[allow(clippy::too_many_arguments)]
    fn edge(&mut self, v: u32, w: u32, src: &Bits, step: &Bits, idx: u32, label: u32, pats: &mut Pats) {
        let (src, step) = (pats.id(src), pats.id(step));
        self.pending[v as usize].push((TEdge { to: w, step, idx, label }, src));
    }

    /// The product node `(g, q)`, if any.
    fn find(&self, g: u32, q: u32) -> Option<u32> {
        let mut v = self.ends.get(g as usize).map_or(NONE, |e| e[0]);
        while v != NONE {
            if self.aq[v as usize] == q {
                return Some(v);
            }
            v = self.next[v as usize];
        }
        None
    }

    /// The product node `(g, q)`, created if absent; whether it is new.
    fn node(&mut self, g: u32, q: u32) -> (u32, bool) {
        if let Some(v) = self.find(g, q) {
            return (v, false);
        }
        self.grow(g);
        let id = self.gnode.len() as u32;
        self.gnode.push(g);
        self.aq.push(q);
        self.bits.push(0);
        self.xconc.push(NONE);
        self.next.push(NONE);
        self.start.push(0);
        self.len.push(0);
        if self.trace {
            self.pending.push(Vec::new());
        }
        let e = &mut self.ends[g as usize];
        if e[0] == NONE {
            *e = [id, id];
        } else {
            self.next[e[1] as usize] = id;
            e[1] = id;
        }
        (id, true)
    }

    /// Adds the edges of node `v` for the steps of `exp` (TLC's
    /// `addNextState`), expanding new nodes of done graph nodes at once
    /// from their state.
    fn expand<'e, X: Expand + ?Sized>(&mut self, v: u32, exp: Cow<'e, Expansion>, ex: &mut X, pats: &mut Pats) -> Result<(), X::Error> {
        let aut = Arc::clone(&self.aut);
        self.bits[v as usize] = pats.id(&exp.bits);
        self.xconc[v as usize] = exp.conc;
        let mut stack = vec![Frame { v, exp, sidx: 0, k: 0, step: NONE, out: Vec::new() }];
        'frames: while !stack.is_empty() {
            let on_demand = stack.len() > 1;
            let f = stack.last_mut().expect("frame");
            let a = &aut.states[self.aq[f.v as usize] as usize];
            while f.sidx < f.exp.succ.len() {
                let s = &f.exp.succ[f.sidx];
                let step_ok = lits_hold(&a.action_lits, &s.step);
                while f.k < a.succ.len() {
                    let q2 = a.succ[f.k];
                    f.k += 1;
                    if !step_ok || !lits_hold(&aut.states[q2 as usize].state_lits, &s.bits) {
                        continue;
                    }
                    // (In a node expanded on demand, the stuttering step is
                    // the first: TLC's self-loop. TLC stops expanding the
                    // node there, and its search after the event; the
                    // product here stays complete for callers that go on.)
                    if on_demand && f.sidx == 0 && self.fire.is_none() && self.sinks.get(q2 as usize) == Some(&true) {
                        self.fire = Some(f.v);
                    }
                    let (w, fresh) = self.node(s.node, q2);
                    let add = fresh || (!self.tableau && !self.written[s.node as usize]) || !f.out.iter().any(|e| e.to == w);
                    if add {
                        if f.step == NONE {
                            f.step = pats.id(&s.step);
                        }
                        f.out.push(TEdge { to: w, step: f.step, idx: s.idx, label: s.label });
                    }
                    if fresh && self.tableau && self.done[s.node as usize] {
                        let e2 = ex.expand(f.exp.conc, s.idx)?;
                        self.bits[w as usize] = pats.id(&e2.bits);
                        self.xconc[w as usize] = e2.conc;
                        stack.push(Frame { v: w, exp: Cow::Owned(e2), sidx: 0, k: 0, step: NONE, out: Vec::new() });
                        continue 'frames;
                    }
                }
                f.sidx += 1;
                f.k = 0;
                f.step = NONE;
            }
            let f = stack.pop().expect("frame");
            self.start[f.v as usize] = self.edges.len();
            self.len[f.v as usize] = f.out.len() as u32;
            self.edges.extend(f.out);
        }
        Ok(())
    }

    /// The edges of a trace's product stored, and the BFS tree from the
    /// initial nodes.
    pub(super) fn finish(&mut self) {
        for (v, es) in std::mem::take(&mut self.pending).into_iter().enumerate() {
            self.start[v] = self.edges.len();
            self.len[v] = es.len() as u32;
            for (e, src) in es {
                self.edges.push(e);
                self.esrc.push(src);
            }
        }
        let n = self.gnode.len();
        self.parent = vec![(NONE, 0); n];
        let mut seen = vec![false; n];
        let mut queue = VecDeque::new();
        for &(v, _) in &self.init {
            seen[v as usize] = true;
            queue.push_back(v);
        }
        while let Some(v) = queue.pop_front() {
            for e in self.out(v) {
                let w = self.edges[e].to;
                if !seen[w as usize] {
                    seen[w as usize] = true;
                    self.parent[w as usize] = (v, e);
                    queue.push_back(w);
                }
            }
        }
    }

    #[inline]
    fn out(&self, v: u32) -> Range<usize> {
        let s = self.start[v as usize];
        s..s + self.len[v as usize] as usize
    }

    /// A fair cycle satisfying the error model `pem` and the tableau's
    /// promises, if any.
    pub(super) fn search(&self, pem: &Pem, pats: &Pats) -> Option<CLasso> {
        if self.init.is_empty() {
            return None;
        }
        let empty = &Bits::new();
        let node_cond = self.bits.iter().flat_map(|&b| pem.ae_state.iter().map(move |f| f.eval(&pats.pats[b as usize], empty))).collect();
        let (m, need) = (self.edges.len(), pem.ae_action.len());
        let (mut allowed, mut edge_cond) = (vec![false; m], vec![false; m * need]);
        for v in 0..self.gnode.len() as u32 {
            for e in self.out(v) {
                let src = &pats.pats[if self.trace { self.esrc[e] } else { self.bits[v as usize] } as usize];
                let step = &pats.pats[self.edges[e].step as usize];
                allowed[e] = pem.ea.iter().all(|f| f.eval(src, step));
                for (i, f) in pem.ae_action.iter().enumerate() {
                    edge_cond[e * need + i] = f.eval(src, step);
                }
            }
        }
        let view = View { p: self, pats, allowed, node_cond, edge_cond, need: (pem.ae_state.len(), pem.ae_action.len()) };
        let l = find_fair_cycle(&view, &[], &|v| self.parent[v as usize])?;
        Some(self.lasso(&l))
    }

    /// The counterexample of the violation found at product node `fire`: a
    /// shortest path to it from an initial node, then its state stuttering
    /// forever (TLC: `TableauLiveChecker.printErrorTrace`).
    pub(super) fn fire_lasso(&mut self) -> CLasso {
        let v = self.fire.expect("a violation found during the search");
        self.finish();
        let mut path = Vec::new();
        let mut u = v;
        while self.parent[u as usize].0 != NONE {
            let (p, e) = self.parent[u as usize];
            path.push((p, e));
            u = p;
        }
        path.reverse();
        let mut conc = Conc::State(self.init.iter().find(|&&(w, _)| w == u).map_or(0, |&(_, c)| c));
        let mut prefix = Vec::with_capacity(path.len());
        for (w, e) in path {
            prefix.push(CStep { node: self.gnode[w as usize], conc, label: self.edges[e].label });
            conc = Conc::Succ { from: self.xconc[w as usize], idx: self.edges[e].idx };
        }
        CLasso { prefix, cycle: vec![CStep { node: self.gnode[v as usize], conc, label: STUTTER }] }
    }

    fn lasso(&self, l: &PLasso) -> CLasso {
        // The concrete state at each position: the initial one, then the
        // successor of each step.
        let first = l.prefix.first().or(l.cycle.first()).map(|s| s.0);
        let mut conc = Conc::State(self.init.iter().find(|&&(v, _)| Some(v) == first).map_or(0, |&(_, c)| c));
        let mut step = |&(v, e): &(u32, usize)| {
            let s = CStep { node: self.gnode[v as usize], conc, label: self.edges[e].label };
            let idx = self.edges[e].idx;
            conc = if self.trace { Conc::State(idx) } else { Conc::Succ { from: self.xconc[v as usize], idx } };
            s
        };
        let prefix = l.prefix.iter().map(&mut step).collect();
        let cycle = l.cycle.iter().map(&mut step).collect();
        CLasso { prefix, cycle }
    }
}

/// The product with the conditions of one error model, for the search.
struct View<'p> {
    p: &'p TProduct,
    pats: &'p Pats,
    allowed: Vec<bool>,
    /// `[]<>` conditions per node / edge (`need.0` / `need.1` each).
    node_cond: Vec<bool>,
    edge_cond: Vec<bool>,
    need: (usize, usize),
}

impl Prod for View<'_> {
    fn len(&self) -> usize {
        self.p.gnode.len()
    }

    #[inline]
    fn out(&self, v: u32) -> Range<usize> {
        self.p.out(v)
    }

    #[inline]
    fn tgt(&self, e: usize) -> u32 {
        self.p.edges[e].to
    }

    fn acc(&self, v: u32) -> &[bool] {
        &self.p.aut.states[self.p.aq[v as usize] as usize].acc
    }

    fn num_acc(&self) -> usize {
        self.p.aut.num_acc
    }

    fn node_bits(&self, v: u32) -> &Bits {
        &self.pats.pats[self.p.bits[v as usize] as usize]
    }

    fn edge_bits(&self, _v: u32, e: usize) -> &Bits {
        &self.pats.pats[self.p.edges[e].step as usize]
    }

    fn allowed(&self, e: usize) -> bool {
        self.allowed[e]
    }

    fn need(&self) -> (usize, usize) {
        self.need
    }

    fn node_cond(&self, v: u32, i: usize) -> bool {
        self.node_cond[v as usize * self.need.0 + i]
    }

    fn edge_cond(&self, _v: u32, e: usize, i: usize) -> bool {
        self.edge_cond[e * self.need.1 + i]
    }
}
