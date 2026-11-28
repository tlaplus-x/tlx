//! One disjunct's product: the reachable CSR product of the behavior graph
//! with the automaton of the disjunct's rest, built part by part (see
//! `super::automaton::AutInfo`), and its [`Prod`] implementation.

use std::ops::Range;

use crate::recurrence::Condition;
use crate::tableau::Automaton;
use crate::{Bits, GraphView, Ids, Offsets};

use super::automaton::{AutInfo, GraphBfs, NodeMap, Part};
use super::{Prod, NONE};

/// Memory budget callback for [`Product::build`]: separates mandatory growth
/// checks (returning `false` stops construction) from optional speculative
/// probes (such as `NodeMap` `Sparse -> Dense` promotion, where returning
/// `false` declines the transition without poisoning parallel sibling parts).
pub(super) trait Budget {
    fn check(&mut self, nodes: usize, edges: usize, bytes: usize) -> bool;

    /// Check whether a transient peak of `peak_bytes` fits, reverting any
    /// accounted bytes to `current_bytes` if declined.
    fn try_peak(&mut self, nodes: usize, edges: usize, peak_bytes: usize, current_bytes: usize) -> bool {
        let _ = current_bytes;
        self.check(nodes, edges, peak_bytes)
    }

    /// Record the post-transition footprint once a transient peak drops.
    fn settle(&mut self, _bytes: usize) {}
}

impl Budget for &mut Within<'_> {
    fn check(&mut self, nodes: usize, edges: usize, bytes: usize) -> bool {
        (**self)(nodes, edges, bytes)
    }
}

/// The parent of a product node entered from a waiting state (see
/// `AutInfo`): the step into its graph state from the graph's BFS tree
/// (`GraphBfs::into`).
const FROM_WAITING: u32 = NONE - 1;

/// One disjunct of the negation of a property to check (see
/// `crate::recurrence`): the automaton of its rest and its conditions.
pub(super) struct Check<'a> {
    pub(super) aut: Automaton,
    pub(super) info: AutInfo,
    /// Its recurrence conditions (`Prod::need`: on edges).
    pub(super) recur: &'a [Condition],
    /// Its persistence conditions: the product keeps only the edges whose
    /// position satisfies them.
    pub(super) persist: &'a [Condition],
}

/// The reachable product in CSR form, without the nodes of waiting states
/// and with only the edges inside accepting automaton SCCs (see `AutInfo`)
/// that satisfy the persistence conditions; node ids are in BFS order.
pub(super) struct Product<'a, G: GraphView> {
    g: &'a G,
    aut: &'a Automaton,
    info: &'a AutInfo,
    recurrence: &'a [Condition],
    /// With waiting states.
    bfs: Option<&'a GraphBfs>,
    pub(super) st: Vec<u32>,
    aq: Ids,
    /// BFS tree: `(parent node, index of the graph edge from its state)`;
    /// `NONE` for roots, `FROM_WAITING` for nodes entered from a waiting
    /// state.
    parent: Vec<(u32, u32)>,
    /// Monotone `(start_node, dist)` spans while building with waiting states.
    levels: Vec<(u32, u32)>,
    off: Offsets,
    pub(super) tgt: Vec<u32>,
    /// Index into `edges[st[source]]` of the graph edge behind each product edge.
    pub(super) gedge: Ids,
}

pub(crate) fn lits_hold(lits: &[(u32, bool)], bits: &Bits) -> bool {
    lits.iter().all(|&(a, pos)| bits.get(a) == pos)
}

impl<'a, G: GraphView> Product<'a, G> {
    /// The memory of the product (bytes, estimated from its allocations),
    /// with the larger of `map_bytes` and the post-build SCC search buffers
    /// (`map` is dropped before `fair_cycle` allocates `Search`).
    fn bytes_with_map(&self, map_bytes: usize) -> usize {
        let bfs = self.bfs;
        let nodes = self.st.capacity() * 4 + self.aq.bytes() + self.parent.capacity() * 8 + self.levels.capacity() * 8 + self.off.bytes();
        self.aut.bytes()
            + self.info.bytes()
            + std::mem::size_of_val(self.recurrence)
            + bfs.map_or(0, GraphBfs::bytes)
            + nodes
            + self.tgt.capacity() * 4
            + self.gedge.bytes()
            + map_bytes.max(self.st.len() * SEARCH_NODE_BYTES)
    }

    fn bytes(&self, map: &NodeMap) -> usize {
        self.bytes_with_map(map.bytes())
    }

    /// Node `(s, q)` with BFS tree parent `parent` at distance `dist`,
    /// added unless it exists: its id, or `None` if `budget` stopped growth.
    #[inline]
    fn add<B: Budget + ?Sized>(&mut self, map: &mut NodeMap, s: u32, q: u32, parent: (u32, u32), dist: u32, budget: &mut B) -> Option<u32> {
        let id = self.st.len() as u32;
        let mut promoted = false;
        let (w, fresh) = map.get_or_insert(s, self.info.slot[q as usize], id, |peak_map, cur_map| {
            let ok = budget.try_peak(self.st.len(), self.tgt.len(), self.bytes_with_map(peak_map), self.bytes_with_map(cur_map));
            promoted = ok;
            ok
        });
        if promoted {
            budget.settle(self.bytes(map));
        }
        if fresh {
            self.st.push(s);
            self.aq.push(q);
            self.parent.push(parent);
            if self.bfs.is_some() && self.levels.last().is_none_or(|&(_, d)| d != dist) {
                debug_assert!(self.levels.last().is_none_or(|&(_, d)| dist >= d));
                self.levels.push((id, dist));
            }
            if self.st.len().is_multiple_of(GUARD_EVERY) && !budget.check(self.st.len(), self.tgt.len(), self.bytes(map)) {
                return None;
            }
        }
        Some(w)
    }

    /// Build the reachable product of part `part` (`bfs`: the graph's BFS,
    /// if the part is entered from waiting states); `budget` is called as it
    /// grows (every `GUARD_EVERY` inserted/expanded nodes or edges, on
    /// `NodeMap` promotion, and at the end) with its numbers of nodes and
    /// edges and its memory (`bytes`): None if it stops construction.
    pub(super) fn build<B: Budget + ?Sized>(
        g: &'a G,
        ck: &'a Check<'a>,
        part: &'a Part,
        bfs: Option<&'a GraphBfs>,
        budget: &mut B,
    ) -> Option<Product<'a, G>> {
        let (aut, info, recurrence) = (&ck.aut, &ck.info, ck.recur);
        let slots = part.states.len();
        let map_bytes = NodeMap::initial_bytes(g.num_states(), slots);
        let bfs_bytes = bfs.map_or(0, GraphBfs::bytes);
        if !budget.check(0, 0, aut.bytes() + info.bytes() + std::mem::size_of_val(recurrence) + map_bytes + bfs_bytes) {
            return None;
        }
        let bfs = if part.entries.is_empty() { None } else { bfs };
        let mut map = NodeMap::new(g.num_states(), slots);
        let mut p = Product {
            g,
            aut,
            info,
            recurrence,
            bfs,
            st: Vec::new(),
            aq: Ids::zeros(0, aut.states.len().saturating_sub(1) as u32),
            parent: Vec::new(),
            levels: Vec::new(),
            off: Offsets::from(vec![0]),
            tgt: Vec::new(),
            gedge: Ids::default(),
        };
        let state_ok = |q: u32, s: u32| lits_hold(&aut.states[q as usize].state_lits, g.state_bits(s));
        let mine = |q: u32| part.states.binary_search(&q).is_ok();
        for &s in g.init() {
            for &q in &aut.init {
                if !info.wait[q as usize] && mine(q) && state_ok(q, s) {
                    p.add(&mut map, s, q, (NONE, 0), 0, budget)?;
                }
            }
        }
        // The next graph state entered from waiting states (in
        // `GraphBfs::order`), and the current span in `p.levels`.
        let mut entered = 0;
        let mut lvl = 0;
        let mut v = 0;
        loop {
            let d = if let Some(bfs) = &bfs {
                while p.levels.get(lvl + 1).is_some_and(|&(start, _)| v >= start as usize) {
                    lvl += 1;
                }
                // Enter the nodes of the waiting states' steps at the
                // distance of the next node's successors (with no node left,
                // at the next such distance), keeping the ids in BFS order.
                let upto = if v < p.st.len() {
                    p.levels[lvl].1 + 1
                } else if entered < bfs.order.len() {
                    bfs.entry_dist(bfs.order[entered])
                } else {
                    break;
                };
                while let Some(&t) = bfs.order.get(entered) {
                    let dt = bfs.entry_dist(t);
                    if dt > upto {
                        break;
                    }
                    entered += 1;
                    for &q in &part.entries {
                        if state_ok(q, t) {
                            p.add(&mut map, t, q, (FROM_WAITING, 0), dt, budget)?;
                        }
                    }
                }
                if v == p.st.len() {
                    continue;
                }
                while p.levels.get(lvl + 1).is_some_and(|&(start, _)| v >= start as usize) {
                    lvl += 1;
                }
                p.levels[lvl].1
            } else {
                if v == p.st.len() {
                    break;
                }
                0
            };
            if v % GUARD_EVERY == GUARD_EVERY - 1 && !budget.check(p.st.len(), p.tgt.len(), p.bytes(&map)) {
                return None;
            }
            let (s, q) = (p.st[v], p.aq.get(v));
            let a = &aut.states[q as usize];
            for li in 0..g.degree(s) {
                let (t, bits) = g.edge(s, li);
                if !lits_hold(&a.action_lits, bits) {
                    continue;
                }
                for &q2 in &a.succ {
                    if info.wait[q2 as usize] || !state_ok(q2, t) {
                        continue;
                    }
                    let w = p.add(&mut map, t, q2, (v as u32, li as u32), d + 1, budget)?;
                    if info.keeps(q, q2) && ck.persist.iter().all(|c| c.holds(g.state_bits(s), bits)) {
                        p.tgt.push(w);
                        p.gedge.push(li as u32);
                        if p.tgt.len().is_multiple_of(GUARD_EVERY) && !budget.check(p.st.len(), p.tgt.len(), p.bytes(&map)) {
                            return None;
                        }
                    }
                }
            }
            p.off.push(p.tgt.len());
            v += 1;
        }
        if !budget.check(p.st.len(), p.tgt.len(), p.bytes(&map)) {
            return None;
        }
        p.levels = Vec::new();
        Some(p)
    }

    /// The path in the BFS tree from an initial node to node `v`: per
    /// position, the graph state and the index of the graph edge leaving it.
    pub(super) fn prefix(&self, v: u32) -> Vec<(u32, u32)> {
        let mut path = Vec::new();
        let mut v = v;
        loop {
            match self.parent[v as usize] {
                (NONE, _) => break,
                (FROM_WAITING, _) => {
                    let bfs = self.bfs.expect("entered from a waiting state");
                    let mut s = self.st[v as usize];
                    loop {
                        let (u, li) = bfs.into[s as usize];
                        path.push((u, li));
                        s = u;
                        if bfs.dist[s as usize] == 0 {
                            break;
                        }
                    }
                    break;
                }
                (u, li) => {
                    path.push((self.st[u as usize], li));
                    v = u;
                }
            }
        }
        path.reverse();
        path
    }
}

/// A memory check while a product grows (see `Product::build`): given its
/// nodes, edges and bytes, whether to go on.
pub type Within<'a> = dyn FnMut(usize, usize, usize) -> bool + Send + 'a;

/// `Product::build` calls its memory check every this many inserted/expanded
/// nodes or retained product edges.
const GUARD_EVERY: usize = 1 << 16;

/// The search's arrays per product node (`Search`: region, index, low).
const SEARCH_NODE_BYTES: usize = 12;

impl<G: GraphView> Prod for Product<'_, G> {
    fn len(&self) -> usize {
        self.st.len()
    }

    #[inline]
    fn out(&self, v: u32) -> Range<usize> {
        self.off.range(v as usize)
    }

    #[inline]
    fn tgt(&self, e: usize) -> u32 {
        self.tgt[e]
    }

    #[inline]
    fn live(&self, v: u32) -> bool {
        self.info.live[self.aq.get(v as usize) as usize]
    }

    #[inline]
    fn acc(&self, v: u32) -> &[bool] {
        &self.aut.states[self.aq.get(v as usize) as usize].acc
    }

    fn num_acc(&self) -> usize {
        self.aut.num_acc
    }

    fn need(&self) -> (usize, usize) {
        (0, self.recurrence.len())
    }

    #[inline]
    fn edge_cond(&self, v: u32, e: usize, i: usize) -> bool {
        self.recurrence[i].holds(self.node_bits(v), self.edge_bits(v, e))
    }

    #[inline]
    fn node_bits(&self, v: u32) -> &Bits {
        self.g.state_bits(self.st[v as usize])
    }

    #[inline]
    fn edge_bits(&self, v: u32, e: usize) -> &Bits {
        self.g.edge(self.st[v as usize], self.gedge.get(e) as usize).1
    }
}
