//! Product of the behavior graph with the tableau automaton, and the search
//! for a reachable fair accepting SCC (generalized Büchi acceptance plus
//! weak/strong fairness as Streett conditions).
//!
//! The search works on any product graph given through [`Prod`]: the
//! product built here from a [`crate::Graph`], or the TLC-style product of
//! `crate::tlc` (graphs with concrete states).
//!
//! The product itself is built in `product`; what it needs to know about
//! the automaton and the graph is prepared in `automaton`. The SCC search
//! over the product and the walk that builds the counterexample cycle live
//! in `accepting` and `walk`; this module keeps the search's schedule (the
//! parts of the products) and its memory budget.

mod accepting;
mod automaton;
mod product;
mod walk;

use std::ops::Range;

use self::accepting::Search;
use self::automaton::{AutInfo, GraphBfs};
use self::product::{Budget, Check, Product};
use crate::tableau::Automaton;
use crate::{Bits, CheckStats, Fairness, GraphView, Lasso, Ltl};

pub(crate) use self::product::{lits_hold, Within};

pub(crate) const NONE: u32 = u32::MAX;
/// Region of nodes that can no longer be part of a fair accepting cycle.
const DEAD: u32 = u32::MAX;

/// A reachable product graph in CSR form, as seen by the search.
pub(crate) trait Prod {
    fn len(&self) -> usize;
    /// The CSR positions of the edges leaving `v`.
    fn out(&self, v: u32) -> Range<usize>;
    /// The target of the edge at CSR position `e`.
    fn tgt(&self, e: usize) -> u32;
    /// Whether `v` may be on an accepting cycle (others are left out of
    /// the search).
    #[inline]
    fn live(&self, _v: u32) -> bool {
        true
    }
    /// Membership of `v` in each acceptance set of the automaton.
    fn acc(&self, v: u32) -> &[bool];
    fn num_acc(&self) -> usize;
    /// State-atom bits at `v` (fairness: ENABLED).
    fn node_bits(&self, v: u32) -> &Bits;
    /// Action-atom bits of the edge at CSR position `e` (leaving `v`).
    fn edge_bits(&self, v: u32, e: usize) -> &Bits;
    /// Whether the edge may be part of a cycle (`<>[]` conditions).
    #[inline]
    fn allowed(&self, _e: usize) -> bool {
        true
    }
    /// The numbers of extra `[]<>` acceptance conditions on nodes and on
    /// edges: for each, some node / edge of a cycle must satisfy it.
    #[inline]
    fn need(&self) -> (usize, usize) {
        (0, 0)
    }
    /// Whether node `v` satisfies node condition `i`.
    #[inline]
    fn node_cond(&self, _v: u32, _i: usize) -> bool {
        false
    }
    /// Whether the edge at CSR position `e` (leaving `v`) satisfies edge
    /// condition `i`.
    #[inline]
    fn edge_cond(&self, _v: u32, _e: usize, _i: usize) -> bool {
        false
    }
}

/// A lasso in the product: `(node, CSR edge leaving it)` per position.
pub(crate) struct PLasso {
    pub prefix: Vec<(u32, usize)>,
    pub cycle: Vec<(u32, usize)>,
}

/// Searches the product `p` for a reachable cycle that is accepting and
/// satisfies all fairness constraints: the node it starts at and the cycle.
fn fair_cycle<P: Prod>(p: &P, fair: &[Fairness]) -> Option<(u32, Vec<(u32, usize)>)> {
    let mut s = Search::new(fair, p, p.len());
    let (scc, r) = s.find()?;
    Some(s.cycle(&scc, r))
}

/// [`fair_cycle`] as a lasso, with the BFS tree `parent` of `p` (`(node,
/// CSR edge into it)`, `NONE` for roots): the prefix is the path to the
/// cycle's start.
pub(crate) fn find_fair_cycle<P: Prod>(p: &P, fair: &[Fairness], parent: &dyn Fn(u32) -> (u32, usize)) -> Option<PLasso> {
    let (v0, cycle) = fair_cycle(p, fair)?;
    let mut prefix = Vec::new();
    let mut v = v0;
    while parent(v).0 != NONE {
        let (u, e) = parent(v);
        prefix.push((u, e));
        v = u;
    }
    prefix.reverse();
    Some(PLasso { prefix, cycle })
}

/// Searches the product of `g` and the automaton of `prop`'s negation for
/// a reachable cycle that is accepting and satisfies all fairness
/// constraints. `within`: see `Product::build`; Err(()) if it stopped the
/// search. `threads`: how many parts of the product (see `AutInfo`) may be
/// built and searched at once; the result is the same (the counterexample
/// of the first part with one). `stats`: what it did.
pub(crate) fn find_fair_accepting<G: GraphView + Sync>(
    g: &G,
    prop: &Ltl,
    fair: &[Fairness],
    threads: usize,
    within: &mut Within<'_>,
    stats: &mut CheckStats,
) -> Result<Option<Lasso>, ()> {
    let t0 = std::time::Instant::now();
    if g.init().is_empty() {
        return Ok(None);
    }
    // Per disjunct of the negation, the automaton of its rest; the units of
    // work are the parts of the products, disjunct by disjunct.
    let disjuncts = crate::recurrence::split_negation(prop);
    let mut checks = Vec::new();
    let mut units = Vec::new();
    for d in &disjuncts {
        let aut = match &d.rest {
            None => Automaton::universal(),
            Some(rest) => Automaton::for_negation_within(&Ltl::Not(Box::new(rest.clone())), within)?,
        };
        if aut.init.is_empty() {
            continue;
        }
        let info = AutInfo::new(&aut);
        stats.tableau_states += aut.states.len();
        stats.waiting_states += info.wait.iter().filter(|&&w| w).count();
        units.extend((0..info.parts.len()).map(|i| (checks.len(), i)));
        checks.push(Check { aut, info, recur: &d.recur, persist: &d.persist });
    }
    stats.parts = units.len();
    let bytes = || checks.iter().map(|c| c.aut.bytes() + c.info.bytes()).sum::<usize>();
    let bfs = if checks.iter().any(|c| c.info.waiting()) {
        if !within(0, 0, bytes() + GraphBfs::bytes_for(g.num_states())) {
            return Err(());
        }
        Some(GraphBfs::new(g))
    } else {
        None
    };
    stats.build_secs = t0.elapsed().as_secs_f64();
    let cx = PartCx { g, checks: &checks, units: &units, bfs: bfs.as_ref(), fair };
    let threads = threads.min(units.len());
    if threads > 1 {
        if let Some(found) = cx.parallel(threads, within, stats) {
            return Ok(found);
        }
        // (Over the memory budget with several parts at once: one at a
        // time.)
        (stats.product_nodes, stats.product_edges) = (0, 0);
    }
    // The parts in turn: the first with a fair accepting cycle.
    for i in 0..units.len() {
        let mut budget = &mut *within;
        let found = cx.part(i, &mut budget, stats).ok_or(())?;
        if found.is_some() {
            return Ok(found);
        }
    }
    Ok(None)
}

/// What building and searching the parts of the products needs (see
/// `find_fair_accepting`): the parts are `units` (a check and one of the
/// parts of its automaton).
struct PartCx<'a, G: GraphView> {
    g: &'a G,
    checks: &'a [Check<'a>],
    units: &'a [(usize, usize)],
    bfs: Option<&'a GraphBfs>,
    fair: &'a [Fairness],
}

impl<G: GraphView + Sync> PartCx<'_, G> {
    /// Build and search part `i`: its counterexample, if any; None if
    /// `budget` stopped it.
    fn part<B: Budget + ?Sized>(&self, i: usize, budget: &mut B, stats: &mut CheckStats) -> Option<Option<Lasso>> {
        let t0 = std::time::Instant::now();
        let (c, k) = self.units[i];
        let ck = &self.checks[c];
        let p = Product::build(self.g, ck, &ck.info.parts[k], self.bfs, budget)?;
        stats.product_nodes += p.st.len();
        stats.product_edges += p.tgt.len();
        stats.build_secs += t0.elapsed().as_secs_f64();
        let t0 = std::time::Instant::now();
        let found = fair_cycle(&p, self.fair).map(|(v0, cycle)| {
            let cycle = cycle.into_iter().map(|(v, e)| (p.st[v as usize], p.gedge.get(e))).collect();
            Lasso { prefix: p.prefix(v0), cycle }
        });
        stats.search_secs += t0.elapsed().as_secs_f64();
        Some(found)
    }

    /// The parts on `threads` threads, each taking the next part: the
    /// counterexample of the first part with one (parts after one with a
    /// counterexample are skipped), or None if `within` stopped one (it is
    /// given the memory of the parts in progress together).
    fn parallel(&self, threads: usize, within: &mut Within<'_>, stats: &mut CheckStats) -> Option<Option<Lasso>> {
        use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
        use std::sync::Mutex;

        struct ParallelBudget<'a, 'b> {
            guard: &'a Mutex<(&'a mut Within<'b>, Vec<usize>)>,
            stopped: &'a AtomicBool,
            slot: usize,
        }

        impl Budget for ParallelBudget<'_, '_> {
            fn check(&mut self, nodes: usize, edges: usize, bytes: usize) -> bool {
                let mut g = self.guard.lock().unwrap_or_else(|e| e.into_inner());
                g.1[self.slot] = bytes;
                let total = g.1.iter().copied().fold(0usize, usize::saturating_add);
                let ok = !self.stopped.load(Ordering::Relaxed) && (g.0)(nodes, edges, total);
                if !ok {
                    self.stopped.store(true, Ordering::Relaxed);
                }
                ok
            }

            fn try_peak(&mut self, nodes: usize, edges: usize, peak_bytes: usize, current_bytes: usize) -> bool {
                let mut g = self.guard.lock().unwrap_or_else(|e| e.into_inner());
                if self.stopped.load(Ordering::Relaxed) {
                    return false;
                }
                g.1[self.slot] = peak_bytes;
                let total = g.1.iter().copied().fold(0usize, usize::saturating_add);
                let ok = (g.0)(nodes, edges, total);
                if !ok {
                    g.1[self.slot] = current_bytes;
                }
                ok
            }

            fn settle(&mut self, bytes: usize) {
                let mut g = self.guard.lock().unwrap_or_else(|e| e.into_inner());
                g.1[self.slot] = bytes;
            }
        }

        let n = self.units.len();
        let (next, first, stopped) = (AtomicUsize::new(0), AtomicUsize::new(usize::MAX), AtomicBool::new(false));
        let guard = Mutex::new((within, vec![0usize; threads]));
        let found: Vec<Mutex<Option<Lasso>>> = (0..n).map(|_| Mutex::new(None)).collect();
        let totals = Mutex::new(CheckStats::default());
        std::thread::scope(|scope| {
            for t in 0..threads {
                let (next, first, stopped, guard, found, totals) = (&next, &first, &stopped, &guard, &found, &totals);
                scope.spawn(move || {
                    let mut mine = CheckStats::default();
                    let mut budget = ParallelBudget { guard, stopped, slot: t };
                    loop {
                        let i = next.fetch_add(1, Ordering::Relaxed);
                        if i >= n || i > first.load(Ordering::Relaxed) || stopped.load(Ordering::Relaxed) {
                            break;
                        }
                        match self.part(i, &mut budget, &mut mine) {
                            None => break,
                            Some(Some(l)) => {
                                *found[i].lock().unwrap_or_else(|e| e.into_inner()) = Some(l);
                                first.fetch_min(i, Ordering::Relaxed);
                            }
                            Some(None) => {}
                        }
                        guard.lock().unwrap_or_else(|e| e.into_inner()).1[t] = 0;
                    }
                    let mut tot = totals.lock().unwrap_or_else(|e| e.into_inner());
                    tot.product_nodes += mine.product_nodes;
                    tot.product_edges += mine.product_edges;
                    tot.build_secs += mine.build_secs;
                    tot.search_secs += mine.search_secs;
                });
            }
        });
        if stopped.load(Ordering::Relaxed) {
            return None;
        }
        let tot = totals.into_inner().unwrap_or_else(|e| e.into_inner());
        stats.product_nodes += tot.product_nodes;
        stats.product_edges += tot.product_edges;
        stats.build_secs += tot.build_secs;
        stats.search_secs += tot.search_secs;
        let first = first.into_inner();
        Some((first < n).then(|| found[first].lock().unwrap_or_else(|e| e.into_inner()).take()).flatten())
    }
}
