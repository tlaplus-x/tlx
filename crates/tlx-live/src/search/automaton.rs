//! What the product needs to know about the automaton (and about the
//! graph): the SCCs of the automaton, its waiting states and the weakly
//! connected parts the product is built and searched part by part, and the
//! BFS of the graph that enters those parts from the waiting states.

use std::collections::hash_map::Entry;

use crate::tableau::Automaton;
use crate::GraphView;
use tlx_base::hash::FxMap;

use super::NONE;

/// Dense `(state, automaton state) -> node` maps up to this many entries
/// (`256 MiB`).
pub(super) const DENSE_LIMIT: usize = 1 << 26;

/// Up to this many entries (`256 KiB`), [`NodeMap::new`] allocates the dense
/// table eagerly so small graphs pay no hashing overhead. Between this and
/// [`DENSE_LIMIT`], `NodeMap` starts sparse with zero upfront allocation and
/// promotes to dense once the hash table nears half the dense table's size
/// (subject to the memory budget).
pub(super) const EAGER_DENSE_LIMIT: usize = 1 << 16;

/// Estimated bytes of an `FxMap<u64, u32>` with `cap` capacity.
#[inline]
fn sparse_bytes(cap: usize) -> usize {
    // (hashbrown: 12 bytes and a control byte per bucket, at most 7/8 full.)
    cap.saturating_mul(13 * 8) / 7
}

/// Whether the resize about to happen at `cap` would bring `Sparse` to at
/// least half the size of a `Dense` table of `dense_len` entries (`dense_len * 4` B).
///
/// Promoting right before that resize keeps the transient `sparse + dense`
/// peak below `1.5 * dense_bytes` while avoiding the largest hashbrown rehashes
/// on dense parts.
#[inline]
fn should_promote(cap: usize, dense_len: usize) -> bool {
    let dense_bytes = dense_len * 4;
    let next_bytes = if cap == 0 { sparse_bytes(3) } else { sparse_bytes(cap).saturating_mul(2) };
    next_bytes >= dense_bytes / 2
}

/// Map from `(graph state, automaton state slot)` to product node ids.
pub(super) enum NodeMap {
    Dense {
        q: usize,
        ids: Vec<u32>,
    },
    Sparse {
        map: FxMap<u64, u32>,
        /// Number of automaton slots per state (used when promoting to `Dense`).
        q: usize,
        /// Target dense table length `n * q`, or `0` when promotion is disabled
        /// (`n * q > DENSE_LIMIT`, overflow, or previously declined by budget).
        dense_len: usize,
    },
}

impl NodeMap {
    /// Upfront bytes allocated by [`NodeMap::new(n, q)`].
    pub(super) fn initial_bytes(n: usize, q: usize) -> usize {
        match n.checked_mul(q) {
            Some(len) if len <= EAGER_DENSE_LIMIT => len * 4,
            _ => 0,
        }
    }

    pub(super) fn new(n: usize, q: usize) -> Self {
        Self::with_eager_limit(n, q, EAGER_DENSE_LIMIT)
    }

    fn with_eager_limit(n: usize, q: usize, eager_limit: usize) -> Self {
        match n.checked_mul(q) {
            Some(len) if len <= eager_limit.min(DENSE_LIMIT) => NodeMap::Dense { q, ids: vec![NONE; len] },
            Some(len) if len <= DENSE_LIMIT => NodeMap::Sparse { map: FxMap::default(), q, dense_len: len },
            _ => NodeMap::Sparse { map: FxMap::default(), q: 0, dense_len: 0 },
        }
    }

    /// The id of `(s, q)`, inserting `fresh` if absent. Returns `(id, inserted)`.
    ///
    /// When a promotable `Sparse` table is about to resize to at least half of
    /// the equivalent `Dense` table's size, `allow_dense(peak_bytes, cur_bytes)`
    /// is checked before allocating `Dense` (with `peak_bytes = cur_bytes +
    /// dense_bytes`). If it returns `true`, `Sparse` is promoted to `Dense`
    /// and dropped; otherwise promotion is permanently disabled on this map so
    /// it stays `Sparse`.
    #[inline]
    pub(super) fn get_or_insert(&mut self, s: u32, q: u32, fresh: u32, allow_dense: impl FnOnce(usize, usize) -> bool) -> (u32, bool) {
        match self {
            NodeMap::Dense { q: nq, ids } => {
                let slot = &mut ids[s as usize * *nq + q as usize];
                if *slot == NONE {
                    *slot = fresh;
                    (fresh, true)
                } else {
                    (*slot, false)
                }
            }
            NodeMap::Sparse { map, q: nq, dense_len } => {
                let key = sparse_key(s, q);
                if *dense_len > 0 && map.len() >= map.capacity() && should_promote(map.capacity(), *dense_len) {
                    if let Some(&id) = map.get(&key) {
                        return (id, false);
                    }
                    let cur_bytes = sparse_bytes(map.capacity());
                    let dense_bytes = *dense_len * 4;
                    if allow_dense(cur_bytes.saturating_add(dense_bytes), cur_bytes) {
                        let nq = *nq;
                        let mut ids = vec![NONE; *dense_len];
                        for (&k, &id) in map.iter() {
                            let (ms, mq) = unpack_sparse_key(k);
                            ids[ms * nq + mq] = id;
                        }
                        ids[s as usize * nq + q as usize] = fresh;
                        *self = NodeMap::Dense { q: nq, ids };
                        return (fresh, true);
                    }
                    *dense_len = 0;
                    map.insert(key, fresh);
                    return (fresh, true);
                }
                match map.entry(key) {
                    Entry::Occupied(e) => (*e.get(), false),
                    Entry::Vacant(e) => {
                        e.insert(fresh);
                        (fresh, true)
                    }
                }
            }
        }
    }

    pub(super) fn bytes(&self) -> usize {
        match self {
            NodeMap::Dense { ids, .. } => ids.capacity() * 4,
            NodeMap::Sparse { map, .. } => sparse_bytes(map.capacity()),
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

#[inline]
fn unpack_sparse_key(key: u64) -> (usize, usize) {
    ((key as u32) as usize, (key >> 32) as usize)
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
    use super::{sparse_key, NodeMap, DENSE_LIMIT, EAGER_DENSE_LIMIT};
    use std::collections::HashSet;
    use std::hash::BuildHasher;
    use tlx_base::hash::FxBuildHasher;

    /// The sparse keys of distinct states spread over a table past 2^26
    /// buckets: 2^20 states of one slot land in about as many 16-bucket
    /// probe groups of a 2^28-bucket table (94%), and the bucket index's
    /// bits 26 and 27 take every value. Keyed `(s << 32) | q`, those bits
    /// were fixed by the slot (82% of the groups), and the liveness check
    /// of a 176M-state graph ran for more than three hours without ending.
    // A pure `FxHasher` statistics check over 2^20 entries (no `unsafe`); a
    // smaller sample would defeat testing bucket bits 26-27.
    // `node_map_keys_by_state_and_slot` still covers `sparse_key` and
    // `NodeMap::Sparse` under Miri.
    #[test]
    #[cfg_attr(miri, ignore)]
    fn sparse_keys_spread_past_two_to_the_26_buckets() {
        let n = 1u32 << 20;
        let mask = (1u64 << 28) - 1;
        let hash = |s: u32| FxBuildHasher::default().hash_one(sparse_key(s, 1));
        let groups: HashSet<u64> = (0..n).map(|s| (hash(s) & mask) >> 4).collect();
        assert!(groups.len() as f64 > 0.9 * f64::from(n), "{} groups", groups.len());
        let high: HashSet<u64> = (0..n).map(|s| (hash(s) & mask) >> 26).collect();
        assert_eq!(high.len(), 4, "bits 26 and 27 of the bucket index: {high:?}");
    }

    /// `NodeMap` keys by `(state, slot)`: an existing pair keeps its id and
    /// reports no insertion, a new one gets the next id once across eager
    /// dense, promotable sparse, permanent sparse, and overflowed sizes.
    #[test]
    fn node_map_keys_by_state_and_slot() {
        assert_eq!(NodeMap::initial_bytes(4, 3), 48);
        assert_eq!(NodeMap::initial_bytes(EAGER_DENSE_LIMIT, 1), EAGER_DENSE_LIMIT * 4);
        assert_eq!(NodeMap::initial_bytes(EAGER_DENSE_LIMIT + 1, 1), 0);
        assert_eq!(NodeMap::initial_bytes(1, DENSE_LIMIT + 1), 0);
        assert_eq!(NodeMap::initial_bytes(usize::MAX, 2), 0);

        let mut dense = NodeMap::new(4, 3);
        let mut promotable = NodeMap::new(EAGER_DENSE_LIMIT, 2);
        let mut sparse = NodeMap::new(1, DENSE_LIMIT + 1);
        let mut overflow = NodeMap::new(usize::MAX, 2);
        assert!(matches!(dense, NodeMap::Dense { .. }));
        assert!(matches!(promotable, NodeMap::Sparse { dense_len, .. } if dense_len == EAGER_DENSE_LIMIT * 2));
        assert!(matches!(sparse, NodeMap::Sparse { dense_len: 0, .. }));
        assert!(matches!(overflow, NodeMap::Sparse { dense_len: 0, .. }));
        assert_eq!(promotable.bytes(), 0);
        assert_eq!(sparse.bytes(), 0);
        assert_eq!(overflow.bytes(), 0);

        let pairs = [(0u32, 0u32), (2, 1), (3, 2), (0, 0), (2, 1), (3, 0)];
        for map in [&mut dense, &mut promotable, &mut sparse, &mut overflow] {
            let mut next = 0u32;
            let mut got = Vec::new();
            for &(s, q) in &pairs {
                let (id, fresh) = map.get_or_insert(s, q, next, |_, _| panic!("unexpected promotion"));
                if fresh {
                    next += 1;
                }
                got.push((id, fresh));
            }
            assert_eq!(got, [(0, true), (1, true), (2, true), (0, false), (1, false), (3, true)]);
            assert!(map.bytes() > 0);
        }
    }

    /// A promotable `Sparse` map promotes to `Dense` once the next resize
    /// reaches half the dense size, accounting for the transient `sparse +
    /// dense` peak before allocating and preserving every existing id.
    #[test]
    fn node_map_promotes_sparse_to_dense_preserving_ids() {
        let (n, q) = (16usize, 4usize);
        let dense_bytes = n * q * 4;
        let mut map = NodeMap::with_eager_limit(n, q, 0);
        assert!(matches!(map, NodeMap::Sparse { dense_len: 64, .. }));
        assert_eq!(map.bytes(), 0);

        let mut promoted_at = None;
        let mut inserted = Vec::new();
        for id in 0..(n * q) as u32 {
            let s = id / q as u32;
            let slot = id % q as u32;
            let before = map.bytes();
            let (got, fresh) = map.get_or_insert(s, slot, id, |peak, cur| {
                assert_eq!(cur, before);
                assert_eq!(peak, cur + dense_bytes);
                assert!(promoted_at.is_none(), "promotion runs at most once");
                promoted_at = Some(id);
                true
            });
            assert_eq!((got, fresh), (id, true));
            inserted.push((s, slot, id));
            // Re-looking up an existing key right at capacity must not trigger
            // promotion or change its id.
            let (dup, dup_fresh) = map.get_or_insert(s, slot, u32::MAX - 1, |_, _| panic!("duplicate must not promote"));
            assert_eq!((dup, dup_fresh), (id, false));
        }

        let trigger = promoted_at.expect("dense table must promote");
        assert!(trigger > 0 && (trigger as usize) < n * q, "promoted after {trigger} entries");
        assert!(matches!(map, NodeMap::Dense { q: 4, .. }));
        assert!(map.bytes() >= dense_bytes);
        for &(s, slot, id) in &inserted {
            assert_eq!(map.get_or_insert(s, slot, u32::MAX - 1, |_, _| panic!("already dense")), (id, false));
        }
    }

    /// When the budget declines the transient `sparse + dense` peak, `NodeMap`
    /// disables promotion permanently and continues in `Sparse` mode without
    /// losing ids or re-probing the budget on later resizes.
    #[test]
    fn node_map_declined_promotion_stays_sparse() {
        let (n, q) = (16usize, 4usize);
        let dense_bytes = n * q * 4;
        let mut map = NodeMap::with_eager_limit(n, q, 0);
        let mut probes = 0usize;

        for id in 0..(n * q) as u32 {
            let s = id / q as u32;
            let slot = id % q as u32;
            let (got, fresh) = map.get_or_insert(s, slot, id, |peak, cur| {
                probes += 1;
                assert_eq!(peak, cur + dense_bytes);
                false
            });
            assert_eq!((got, fresh), (id, true));
        }

        assert_eq!(probes, 1, "declined promotion must not re-probe on later resizes");
        assert!(matches!(map, NodeMap::Sparse { dense_len: 0, .. }));
        assert!(map.bytes() > 0);
        for id in 0..(n * q) as u32 {
            let (s, slot) = (id / q as u32, id % q as u32);
            assert_eq!(map.get_or_insert(s, slot, u32::MAX - 1, |_, _| panic!("promotion disabled")), (id, false));
        }
    }

    /// Real default thresholds (`EAGER_DENSE_LIMIT < n * q <= DENSE_LIMIT`)
    /// start sparse with zero upfront bytes and promote once density grows.
    #[test]
    #[cfg_attr(miri, ignore)]
    fn node_map_default_thresholds_promote() {
        let (n, q) = (20_000usize, 4usize); // 80_000 > EAGER_DENSE_LIMIT (65_536)
        assert_eq!(NodeMap::initial_bytes(n, q), 0);
        let mut map = NodeMap::new(n, q);
        assert!(matches!(map, NodeMap::Sparse { dense_len: 80_000, .. }));
        assert_eq!(map.bytes(), 0);

        let mut promoted = false;
        for id in 0..10_000u32 {
            let (s, slot) = (id / q as u32, id % q as u32);
            let (got, fresh) = map.get_or_insert(s, slot, id, |peak, cur| {
                assert_eq!(peak, cur + n * q * 4);
                promoted = true;
                true
            });
            assert_eq!((got, fresh), (id, true));
        }
        assert!(promoted);
        assert!(matches!(map, NodeMap::Dense { q: 4, .. }));
        assert!(map.bytes() >= n * q * 4);
        for id in 0..10_000u32 {
            let (s, slot) = (id / q as u32, id % q as u32);
            assert_eq!(map.get_or_insert(s, slot, u32::MAX - 1, |_, _| panic!("already dense")), (id, false));
        }
    }
}
