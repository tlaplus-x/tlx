//! What the product needs to know about the automaton (and about the
//! graph): the SCCs of the automaton, its waiting states and the weakly
//! connected parts the product is built and searched part by part, and the
//! BFS of the graph that enters those parts from the waiting states.

use crate::tableau::Automaton;
use crate::GraphView;
use tlx_base::hash::FxMap;

use super::NONE;

/// Dense `(state, automaton state) -> node` maps up to this many entries.
pub(super) const DENSE_LIMIT: usize = 1 << 26;

/// Map from `(graph state, automaton state slot)` to product node ids.
pub(super) enum NodeMap {
    Dense { q: usize, ids: Vec<u32> },
    Sparse(FxMap<u64, u32>),
}

impl NodeMap {
    pub(super) fn new(n: usize, q: usize) -> Self {
        match n.checked_mul(q) {
            Some(len) if len <= DENSE_LIMIT => NodeMap::Dense { q, ids: vec![NONE; len] },
            _ => NodeMap::Sparse(FxMap::default()),
        }
    }

    /// The id of `(s, q)`, inserting `fresh` if absent. Returns `(id, inserted)`.
    #[inline]
    pub(super) fn get_or_insert(&mut self, s: u32, q: u32, fresh: u32) -> (u32, bool) {
        let slot = match self {
            NodeMap::Dense { q: nq, ids } => &mut ids[s as usize * *nq + q as usize],
            NodeMap::Sparse(m) => m.entry(sparse_key(s, q)).or_insert(NONE),
        };
        if *slot == NONE {
            *slot = fresh;
            (fresh, true)
        } else {
            (*slot, false)
        }
    }

    pub(super) fn bytes(&self) -> usize {
        match self {
            NodeMap::Dense { ids, .. } => ids.capacity() * 4,
            // (hashbrown: 12 bytes and a control byte per bucket, at most
            // 7/8 full.)
            NodeMap::Sparse(m) => m.capacity() * 13 * 8 / 7,
        }
    }
}

/// The sparse map's key of `(s, q)`: the state in the low half. FxHasher's
/// finishing rotation fills the bucket index's bits past 26 from the key's
/// low bits, so keyed `(s << 32) | q` all states of one slot share at most
/// 2^26 home buckets, and past that many states the probe sequences grow
/// without bound.
#[inline]
fn sparse_key(s: u32, q: u32) -> u64 {
    (u64::from(q) << 32) | u64::from(s)
}

/// What the product needs to know about the states of the automaton.
///
/// A product node can be on an accepting cycle only if its automaton state
/// is in an accepting SCC of the automaton (one with a cycle and a state in
/// every acceptance set): the cycle projects onto one. The nodes of other
/// states are built for reachability and the BFS tree only, and the
/// product keeps only the edges inside an accepting automaton SCC.
///
/// A *waiting* state is initial, has no literals and a self-loop, and is
/// not in an accepting SCC: the "not yet" branch of a `<>` that the
/// negations of `P ~> Q`, `[]<>P` and `<>[]P` start with. Its product
/// nodes are all reachable states of the graph, along the graph's own
/// steps, so they are not built (they would copy the graph once per such
/// state): the steps out of them enter the other states from the graph's
/// BFS tree (`GraphBfs`).
///
/// Without the waiting states, the automaton falls apart into weakly
/// connected components (one per `~>` of a conjunction, say), whose
/// product nodes no edge connects: each `Part` with an accepting SCC is
/// built and searched on its own, in turn.
pub(super) struct AutInfo {
    /// The automaton SCC of each state.
    scc: Vec<u32>,
    /// Whether the state is in an accepting automaton SCC.
    pub(super) live: Vec<bool>,
    /// Whether the state is a waiting state (its nodes are not built).
    pub(super) wait: Vec<bool>,
    /// The index of each state among the states of its part (`NONE` for
    /// waiting states and states of no part).
    pub(super) slot: Vec<u32>,
    /// The parts with an accepting SCC, by their first state.
    pub(super) parts: Vec<Part>,
}

/// A weakly connected component of the automaton without its waiting
/// states (see `AutInfo`).
pub(super) struct Part {
    /// Its states, ascending.
    pub(super) states: Vec<u32>,
    /// Its states that a waiting state steps to, ascending.
    pub(super) entries: Vec<u32>,
}

impl AutInfo {
    pub(super) fn new(aut: &Automaton) -> AutInfo {
        let n = aut.states.len();
        let scc = automaton_sccs(aut);
        let comps = scc.iter().map(|&c| c as usize + 1).max().unwrap_or(0);
        let acc = aut.num_acc;
        let (mut cyclic, mut cover) = (vec![false; comps], vec![false; comps * acc]);
        for (q, a) in aut.states.iter().enumerate() {
            let c = scc[q] as usize;
            cyclic[c] |= a.succ.iter().any(|&q2| scc[q2 as usize] as usize == c);
            for (i, &x) in a.acc.iter().enumerate() {
                cover[c * acc + i] |= x;
            }
        }
        let live: Vec<bool> = scc.iter().map(|&c| cyclic[c as usize] && cover[c as usize * acc..][..acc].iter().all(|&x| x)).collect();
        let wait: Vec<bool> = (0..n)
            .map(|q| {
                let a = &aut.states[q];
                !live[q]
                    && a.state_lits.is_empty()
                    && a.action_lits.is_empty()
                    && a.succ.contains(&(q as u32))
                    && aut.init.contains(&(q as u32))
            })
            .collect();
        // The weakly connected components without the waiting states
        // (union-find).
        let mut up: Vec<u32> = (0..n as u32).collect();
        fn root(up: &mut [u32], mut q: u32) -> u32 {
            while up[q as usize] != q {
                up[q as usize] = up[up[q as usize] as usize];
                q = up[q as usize];
            }
            q
        }
        for (q, a) in aut.states.iter().enumerate() {
            for &q2 in a.succ.iter().filter(|&&q2| !wait[q] && !wait[q2 as usize]) {
                let (r, r2) = (root(&mut up, q as u32), root(&mut up, q2));
                up[r.max(r2) as usize] = r.min(r2);
            }
        }
        let mut slot = vec![NONE; n];
        let mut parts: Vec<Part> = Vec::new();
        let mut part_of = vec![NONE; n];
        for q in (0..n).filter(|&q| !wait[q]) {
            let r = root(&mut up, q as u32) as usize;
            if part_of[r] == NONE {
                part_of[r] = parts.len() as u32;
                parts.push(Part { states: Vec::new(), entries: Vec::new() });
            }
            let part = &mut parts[part_of[r] as usize];
            slot[q] = part.states.len() as u32;
            part.states.push(q as u32);
        }
        for q in (0..n).filter(|&q| wait[q]) {
            for &q2 in aut.states[q].succ.iter().filter(|&&q2| !wait[q2 as usize]) {
                let part = &mut parts[part_of[root(&mut up, q2) as usize] as usize];
                if !part.entries.contains(&q2) {
                    part.entries.push(q2);
                }
            }
        }
        for part in &mut parts {
            part.entries.sort_unstable();
        }
        // (A part without an accepting SCC has no accepting cycle.)
        parts.retain(|part| part.states.iter().any(|&q| live[q as usize]));
        AutInfo { scc, live, wait, slot, parts }
    }

    pub(super) fn bytes(&self) -> usize {
        self.scc.capacity() * 4
            + self.live.capacity()
            + self.wait.capacity()
            + self.slot.capacity() * 4
            + self.parts.iter().map(|p| (p.states.capacity() + p.entries.capacity()) * 4 + std::mem::size_of::<Part>()).sum::<usize>()
    }

    /// Whether some part is entered from a waiting state.
    pub(super) fn waiting(&self) -> bool {
        self.parts.iter().any(|p| !p.entries.is_empty())
    }

    /// Whether the product keeps its edges from automaton state `q` to `q2`
    /// (see `AutInfo`).
    #[inline]
    pub(super) fn keeps(&self, q: u32, q2: u32) -> bool {
        self.live[q as usize] && self.scc[q as usize] == self.scc[q2 as usize]
    }
}

/// The SCC of each state of the automaton (iterative Tarjan).
fn automaton_sccs(aut: &Automaton) -> Vec<u32> {
    let n = aut.states.len();
    let (mut index, mut low, mut comp) = (vec![NONE; n], vec![0u32; n], vec![NONE; n]);
    let (mut counter, mut comps) = (0u32, 0u32);
    let mut stack: Vec<usize> = Vec::new();
    let mut call: Vec<(usize, usize)> = Vec::new();
    for root in 0..n {
        if index[root] != NONE {
            continue;
        }
        index[root] = counter;
        low[root] = counter;
        counter += 1;
        stack.push(root);
        call.push((root, 0));
        while let Some(&(v, i)) = call.last() {
            if let Some(&w) = aut.states[v].succ.get(i) {
                call.last_mut().expect("frame").1 += 1;
                let w = w as usize;
                if index[w] == NONE {
                    index[w] = counter;
                    low[w] = counter;
                    counter += 1;
                    stack.push(w);
                    call.push((w, 0));
                } else if comp[w] == NONE {
                    low[v] = low[v].min(index[w]);
                }
                continue;
            }
            call.pop();
            if let Some(&(u, _)) = call.last() {
                low[u] = low[u].min(low[v]);
            }
            if low[v] == index[v] {
                loop {
                    let w = stack.pop().expect("tarjan stack");
                    comp[w] = comps;
                    if w == v {
                        break;
                    }
                }
                comps += 1;
            }
        }
    }
    comp
}

/// The graph's BFS from its initial states, for the product nodes of
/// waiting states (see `AutInfo`).
pub(super) struct GraphBfs {
    /// The distance of each state from an initial one (`NONE`: unreachable).
    pub(super) dist: Vec<u32>,
    /// For each state with a step into it from a reachable state, such a
    /// step from a nearest one: `(source, edge index)` (`NONE` if none).
    /// For a state that is not initial, its BFS tree parent.
    pub(super) into: Vec<(u32, u32)>,
    /// The states with a step into them, by the distance of that step's
    /// source (ascending).
    pub(super) order: Vec<u32>,
}

impl GraphBfs {
    pub(super) fn new<G: GraphView>(g: &G) -> GraphBfs {
        let n = g.num_states();
        let (mut dist, mut into) = (vec![NONE; n], vec![(NONE, 0); n]);
        let (mut queue, mut order) = (Vec::with_capacity(n), Vec::with_capacity(n));
        for &s in g.init() {
            if dist[s as usize] == NONE {
                dist[s as usize] = 0;
                queue.push(s);
            }
        }
        let mut k = 0;
        while k < queue.len() {
            let s = queue[k];
            k += 1;
            for li in 0..g.degree(s) {
                let t = g.edge(s, li).0;
                if into[t as usize].0 == NONE {
                    into[t as usize] = (s, li as u32);
                    order.push(t);
                }
                if dist[t as usize] == NONE {
                    dist[t as usize] = dist[s as usize] + 1;
                    queue.push(t);
                }
            }
        }
        GraphBfs { dist, into, order }
    }

    /// The memory of the BFS of a graph of `n` states (bytes; with its
    /// queue while it runs).
    pub(super) fn bytes_for(n: usize) -> usize {
        n * 20
    }

    pub(super) fn bytes(&self) -> usize {
        self.dist.capacity() * 4 + self.into.capacity() * 8 + self.order.capacity() * 4
    }

    /// The distance of the product nodes entered from a waiting state at
    /// graph state `t` (by the step `into[t]`).
    #[inline]
    pub(super) fn entry_dist(&self, t: u32) -> u32 {
        self.dist[self.into[t as usize].0 as usize] + 1
    }
}

#[cfg(test)]
mod tests {
    use super::{sparse_key, NodeMap, DENSE_LIMIT};
    use std::collections::HashSet;
    use std::hash::BuildHasher;
    use tlx_base::hash::FxBuildHasher;

    /// The sparse keys of distinct states spread over a table past 2^26
    /// buckets: 2^20 states of one slot land in about as many 16-bucket
    /// probe groups of a 2^28-bucket table (94%). Keyed `(s << 32) | q`,
    /// they shared 2^26 home buckets (82%), and building the product of a
    /// 176M-state graph took days instead of minutes.
    #[test]
    fn sparse_keys_spread_past_two_to_the_26_buckets() {
        let n = 1u32 << 20;
        let mask = (1u64 << 28) - 1;
        let groups: HashSet<u64> = (0..n).map(|s| (FxBuildHasher::default().hash_one(sparse_key(s, 1)) & mask) >> 4).collect();
        assert!(groups.len() as f64 > 0.9 * f64::from(n), "{} groups", groups.len());
    }

    /// `NodeMap` keys by `(state, slot)`: an existing pair keeps its id and
    /// reports no insertion, a new one gets the next id once, in both the
    /// dense variant and the sparse one chosen past `DENSE_LIMIT` pairs.
    #[test]
    fn node_map_keys_by_state_and_slot() {
        let mut dense = NodeMap::new(4, 3);
        let mut sparse = NodeMap::new(1, DENSE_LIMIT + 1);
        assert!(matches!(dense, NodeMap::Dense { .. }));
        assert!(matches!(sparse, NodeMap::Sparse(_)));
        let pairs = [(0u32, 0u32), (2, 1), (3, 2), (0, 0), (2, 1), (3, 0)];
        for map in [&mut dense, &mut sparse] {
            let mut next = 0u32;
            let mut got = Vec::new();
            for &(s, q) in &pairs {
                let (id, fresh) = map.get_or_insert(s, q, next);
                if fresh {
                    next += 1;
                }
                got.push((id, fresh));
            }
            assert_eq!(got, [(0, true), (1, true), (2, true), (0, false), (1, false), (3, true)]);
            assert!(map.bytes() > 0);
        }
    }
}
