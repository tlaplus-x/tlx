//! tlx-live: liveness checking over a pre-computed behavior graph
//! (design.md §7.4).
//!
//! The caller supplies the reachable state graph with all atomic predicates
//! already evaluated (state atoms per state, action atoms per edge) plus a
//! temporal property and fairness constraints. [`check`] decides whether
//! every fair behavior satisfies the property and otherwise returns a lasso
//! counterexample.
//!
//! - `tableau`: ¬property in negation normal form → generalized Büchi
//!   automaton (GPVW-style tableau);
//! - `search`: on-the-fly product with the graph, iterative Tarjan SCCs,
//!   Streett-style refinement for strong fairness and lasso extraction;
//! - `tlc`: TLC's own algorithm, for graphs whose nodes are classes of
//!   states (VIEW, SYMMETRY), where TLC's verdicts depend on it.

mod normal;
mod recurrence;
mod search;
mod tableau;
mod tlc;

pub use normal::{branches, is_tautology, needs_cycle_conditions};
pub use tlc::{
    check_concrete, check_size, check_trace, reports_early, tableau_initial_checks, tableau_state_atoms, CLasso, CStep, Conc,
    ConcreteChecker, Event, Expand, Expansion, Succ, TraceState,
};

/// Temporal formula over pre-evaluated atoms (no `Next` operator: TLA+
/// formulas are stuttering-invariant).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Ltl {
    True,
    False,
    /// State atom `i`: holds at a position if bit i of the state's bits is set.
    State(u32),
    /// Action atom `i`: holds at a position if bit i of the bits of the step
    /// (edge) from this position to the next is set.
    Action(u32),
    Not(Box<Ltl>),
    And(Vec<Ltl>),
    Or(Vec<Ltl>),
    Always(Box<Ltl>),
    Eventually(Box<Ltl>),
}

/// Fairness constraint: WF (`strong = false`) or SF (`strong = true`) of an
/// action. `enabled`: state atom = ENABLED <<A>>_v; `taken`: action atom =
/// <<A>>_v.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Fairness {
    pub strong: bool,
    pub enabled: u32,
    pub taken: u32,
}

/// The behavior graph. States are `0..n`. `edges[s]` lists the successors of
/// `s` with the action-atom bits of that step. Callers include a stuttering
/// self-loop `s -> s` in `edges[s]` for every state.
#[derive(Clone, Debug, Default)]
pub struct Graph {
    pub init: Vec<u32>,
    /// One per state.
    pub state_bits: Vec<Bits>,
    /// One list per state.
    pub edges: Vec<Vec<(u32, Bits)>>,
}

/// The behavior graph in CSR form, with the bits of states and edges
/// interned: the edges of state `s` are at positions `off[s]..off[s + 1]`
/// of `tgt` (targets) and `edge_pat` (index into `action_pats`); the bits of
/// state `s` are `state_pats[state_pat[s]]`. Same conventions as [`Graph`]
/// (a stuttering self-loop in every state's edges).
#[derive(Clone, Debug, Default)]
pub struct Csr {
    pub init: Vec<u32>,
    pub off: Vec<usize>,
    pub tgt: Vec<u32>,
    pub edge_pat: Ids,
    pub state_pat: Vec<u32>,
    pub state_pats: Vec<Bits>,
    pub action_pats: Vec<Bits>,
}

impl Csr {
    /// The number of states.
    pub fn len(&self) -> usize {
        self.state_pat.len()
    }

    pub fn is_empty(&self) -> bool {
        self.state_pat.is_empty()
    }

    /// The number of edges of state `s`.
    pub fn degree(&self, s: u32) -> usize {
        self.off[s as usize + 1] - self.off[s as usize]
    }

    /// Edge `i` of state `s`: its target and action-atom bits.
    #[inline]
    pub fn edge(&self, s: u32, i: usize) -> (u32, &Bits) {
        let e = self.off[s as usize] + i;
        (self.tgt[e], &self.action_pats[self.edge_pat.get(e) as usize])
    }

    /// The state-atom bits of state `s`.
    #[inline]
    pub fn state_bits(&self, s: u32) -> &Bits {
        &self.state_pats[self.state_pat[s as usize] as usize]
    }

    /// The CSR form of `g` (each state's and edge's bits a pattern of their
    /// own).
    pub fn from_graph(g: &Graph) -> Csr {
        let mut c = Csr { init: g.init.clone(), off: vec![0], ..Csr::default() };
        for (s, es) in g.edges.iter().enumerate() {
            c.state_pat.push(c.state_pats.len() as u32);
            c.state_pats.push(g.state_bits[s].clone());
            for (t, b) in es {
                c.tgt.push(*t);
                c.edge_pat.push(c.action_pats.len() as u32);
                c.action_pats.push(b.clone());
            }
            c.off.push(c.tgt.len());
        }
        c
    }
}

/// Small ids (of bit patterns, one per edge of a graph), each stored in the
/// narrowest of `u8`, `u16` and `u32` that holds them all: a behavior graph
/// usually has only a few distinct patterns, and tens of millions of edges.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Ids {
    U8(Vec<u8>),
    U16(Vec<u16>),
    U32(Vec<u32>),
}

impl Default for Ids {
    fn default() -> Ids {
        Ids::U8(Vec::new())
    }
}

impl Ids {
    /// `len` zeros, in the narrowest type that holds ids up to `max`.
    pub fn zeros(len: usize, max: u32) -> Ids {
        if max <= u8::MAX as u32 {
            Ids::U8(vec![0; len])
        } else if max <= u16::MAX as u32 {
            Ids::U16(vec![0; len])
        } else {
            Ids::U32(vec![0; len])
        }
    }

    #[inline]
    pub fn get(&self, i: usize) -> u32 {
        match self {
            Ids::U8(v) => v[i] as u32,
            Ids::U16(v) => v[i] as u32,
            Ids::U32(v) => v[i],
        }
    }

    /// Append `x`, widening the type if needed.
    pub fn push(&mut self, x: u32) {
        match self {
            Ids::U8(v) if x <= u8::MAX as u32 => v.push(x as u8),
            Ids::U16(v) if x <= u16::MAX as u32 => v.push(x as u16),
            Ids::U32(v) => v.push(x),
            Ids::U8(v) if x <= u16::MAX as u32 => *self = Ids::U16(v.iter().map(|&y| y as u16).chain([x as u16]).collect()),
            _ => *self = Ids::U32((0..self.len()).map(|i| self.get(i)).chain([x]).collect()),
        }
    }

    pub fn len(&self) -> usize {
        match self {
            Ids::U8(v) => v.len(),
            Ids::U16(v) => v.len(),
            Ids::U32(v) => v.len(),
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// The memory held (bytes).
    pub fn bytes(&self) -> usize {
        match self {
            Ids::U8(v) => v.capacity(),
            Ids::U16(v) => v.capacity() * 2,
            Ids::U32(v) => v.capacity() * 4,
        }
    }
}

/// Read access to a behavior graph ([`Graph`] or [`Csr`]).
pub(crate) trait GraphView {
    fn init(&self) -> &[u32];
    fn num_states(&self) -> usize;
    fn state_bits(&self, s: u32) -> &Bits;
    fn degree(&self, s: u32) -> usize;
    fn edge(&self, s: u32, i: usize) -> (u32, &Bits);
}

impl GraphView for Graph {
    fn init(&self) -> &[u32] {
        &self.init
    }
    fn num_states(&self) -> usize {
        self.state_bits.len()
    }
    #[inline]
    fn state_bits(&self, s: u32) -> &Bits {
        &self.state_bits[s as usize]
    }
    #[inline]
    fn degree(&self, s: u32) -> usize {
        self.edges[s as usize].len()
    }
    #[inline]
    fn edge(&self, s: u32, i: usize) -> (u32, &Bits) {
        let (t, b) = &self.edges[s as usize][i];
        (*t, b)
    }
}

impl GraphView for Csr {
    fn init(&self) -> &[u32] {
        &self.init
    }
    fn num_states(&self) -> usize {
        self.len()
    }
    #[inline]
    fn state_bits(&self, s: u32) -> &Bits {
        Csr::state_bits(self, s)
    }
    #[inline]
    fn degree(&self, s: u32) -> usize {
        Csr::degree(self, s)
    }
    #[inline]
    fn edge(&self, s: u32, i: usize) -> (u32, &Bits) {
        Csr::edge(self, s, i)
    }
}

/// A compact bitset: up to 64 bits are stored inline, larger sets on the heap.
#[derive(Clone, Debug)]
pub struct Bits(Repr);

#[derive(Clone, Debug)]
enum Repr {
    Inline(u64),
    Heap(Box<[u64]>),
}

impl Default for Bits {
    fn default() -> Self {
        Bits::new()
    }
}

impl Bits {
    /// The empty set.
    pub const fn new() -> Self {
        Bits(Repr::Inline(0))
    }

    /// The set of bits `i` with bit `i` of `w` set.
    pub const fn from_u64(w: u64) -> Self {
        Bits(Repr::Inline(w))
    }

    /// The set of bit `64 * k + j` for each bit j set in word `w[k]`.
    pub fn from_words(w: &[u64]) -> Self {
        match w {
            [] => Bits::new(),
            [x] => Bits::from_u64(*x),
            _ => Bits(Repr::Heap(w.into())),
        }
    }

    /// Like [`Bits::from_words`], reusing an owned multi-word slice without
    /// reallocating.
    pub fn from_boxed_words(w: Box<[u64]>) -> Self {
        match &*w {
            [] => Bits::new(),
            [x] => Bits::from_u64(*x),
            _ => Bits(Repr::Heap(w)),
        }
    }

    /// The set containing exactly `indices`.
    #[cfg(test)]
    fn from_indices(indices: impl IntoIterator<Item = u32>) -> Self {
        let mut b = Bits::new();
        for i in indices {
            b.set(i, true);
        }
        b
    }

    /// The words of the set without trailing zero words (equal sets have
    /// equal words).
    pub(crate) fn words(&self) -> &[u64] {
        let ws: &[u64] = match &self.0 {
            Repr::Inline(w) => std::slice::from_ref(w),
            Repr::Heap(ws) => ws,
        };
        &ws[..ws.iter().rposition(|&w| w != 0).map_or(0, |i| i + 1)]
    }

    /// Whether bit `i` is set.
    #[inline]
    pub fn get(&self, i: u32) -> bool {
        match &self.0 {
            Repr::Inline(w) => i < 64 && (w >> i) & 1 == 1,
            Repr::Heap(ws) => ws.get((i / 64) as usize).is_some_and(|w| (w >> (i % 64)) & 1 == 1),
        }
    }

    /// Sets bit `i` to `v`.
    pub fn set(&mut self, i: u32, v: bool) {
        let word = (i / 64) as usize;
        let mask = 1u64 << (i % 64);
        if word > 0 {
            if let Repr::Inline(w) = self.0 {
                if !v {
                    return;
                }
                let mut ws = vec![0u64; word + 1];
                ws[0] = w;
                self.0 = Repr::Heap(ws.into_boxed_slice());
            }
        }
        match &mut self.0 {
            Repr::Inline(w) => {
                if v {
                    *w |= mask
                } else {
                    *w &= !mask
                }
            }
            Repr::Heap(ws) => {
                if word >= ws.len() {
                    if !v {
                        return;
                    }
                    let mut grown = vec![0u64; word + 1];
                    grown[..ws.len()].copy_from_slice(ws);
                    *ws = grown.into_boxed_slice();
                }
                if v {
                    ws[word] |= mask
                } else {
                    ws[word] &= !mask
                }
            }
        }
    }
}

/// A behavior violating the property: `prefix` from an initial state, then
/// `cycle` repeated forever (the last state of `cycle` steps back to
/// `cycle[0]`; the last prefix state steps to `cycle[0]`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Counterexample {
    pub prefix: Vec<u32>,
    pub cycle: Vec<u32>,
}

/// A counterexample that also names the edge taken at each position:
/// each entry is `(state, i)` where `edges[state][i]` is the step leaving that
/// position (so parallel edges with different action bits are disambiguated).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lasso {
    pub prefix: Vec<(u32, u32)>,
    pub cycle: Vec<(u32, u32)>,
}

impl From<Lasso> for Counterexample {
    fn from(l: Lasso) -> Self {
        Counterexample { prefix: l.prefix.into_iter().map(|(s, _)| s).collect(), cycle: l.cycle.into_iter().map(|(s, _)| s).collect() }
    }
}

/// Like [`check_lasso`], on a graph in CSR form.
pub fn check_lasso_csr(g: &Csr, prop: &Ltl, fairness: &[Fairness]) -> Result<(), Lasso> {
    check_lasso_csr_within(g, prop, fairness, &mut |_, _, _| true).unwrap_or(Ok(()))
}

/// What a check did (for statistics; see [`check_lasso_csr_stats`]).
#[derive(Clone, Copy, Debug, Default)]
pub struct CheckStats {
    /// The states of the tableau automaton (one for a conjunction of
    /// recurrence conditions), and how many of them are waiting states,
    /// whose product nodes are not built.
    pub tableau_states: usize,
    pub waiting_states: usize,
    /// The parts of the product built and searched in turn.
    pub parts: usize,
    /// The product built (all parts): nodes and edges.
    pub product_nodes: usize,
    pub product_edges: usize,
    /// Seconds building the tableau and the product, and searching the
    /// product for a fair accepting cycle (with the counterexample).
    pub build_secs: f64,
    pub search_secs: f64,
}

/// The product graph was too large: the memory check given to
/// [`check_lasso_csr_within`] or [`check_lasso_within`] stopped it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Exhausted;

/// [`check_lasso_csr`] with a memory check: `within(nodes, edges, bytes)`
/// runs during tableau construction (nodes and edges are zero then) and
/// as the reachable product grows. Bytes include the automaton, its
/// construction scratch/caches, and the product and search allocations.
/// When the callback returns false, construction stops.
pub fn check_lasso_csr_within(
    g: &Csr,
    prop: &Ltl,
    fairness: &[Fairness],
    within: &mut (dyn FnMut(usize, usize, usize) -> bool + Send),
) -> Result<Result<(), Lasso>, Exhausted> {
    check_lasso_csr_stats(g, prop, fairness, 1, within, &mut CheckStats::default())
}

/// [`check_lasso_csr_within`] on up to `threads` threads (independent parts
/// of the product at once; the result does not depend on `threads`; the
/// memory check is given their memory together), also telling what the
/// check did (`stats`).
pub fn check_lasso_csr_stats(
    g: &Csr,
    prop: &Ltl,
    fairness: &[Fairness],
    threads: usize,
    within: &mut (dyn FnMut(usize, usize, usize) -> bool + Send),
    stats: &mut CheckStats,
) -> Result<Result<(), Lasso>, Exhausted> {
    assert_eq!(g.off.len(), g.state_pat.len() + 1, "one edge range and one bitset per state");
    match search::find_fair_accepting(g, prop, fairness, threads, within, stats) {
        Ok(Some(l)) => Ok(Err(l)),
        Ok(None) => Ok(Ok(())),
        Err(()) => Err(Exhausted),
    }
}

/// `Ok(())` if every behavior of the graph (infinite path from an initial
/// state) that satisfies all fairness constraints satisfies `prop`.
pub fn check(g: &Graph, prop: &Ltl, fairness: &[Fairness]) -> Result<(), Counterexample> {
    check_lasso(g, prop, fairness).map_err(Counterexample::from)
}

/// Like [`check`], but the counterexample records the edge taken at every step.
pub fn check_lasso(g: &Graph, prop: &Ltl, fairness: &[Fairness]) -> Result<(), Lasso> {
    check_lasso_within(g, prop, fairness, &mut |_, _, _| true).unwrap_or(Ok(()))
}

/// [`check_lasso`] with a memory check, as [`check_lasso_csr_within`].
pub fn check_lasso_within(
    g: &Graph,
    prop: &Ltl,
    fairness: &[Fairness],
    within: &mut (dyn FnMut(usize, usize, usize) -> bool + Send),
) -> Result<Result<(), Lasso>, Exhausted> {
    assert_eq!(g.state_bits.len(), g.edges.len(), "one bitset and one edge list per state");
    match search::find_fair_accepting(g, prop, fairness, 1, within, &mut CheckStats::default()) {
        Ok(Some(l)) => Ok(Err(l)),
        Ok(None) => Ok(Ok(())),
        Err(()) => Err(Exhausted),
    }
}

/// Whether `prop` holds on the lasso whose position `i` has the state-atom
/// bits `states[i]` and whose step leaving position `i` has the action-atom
/// bits `steps[i]`: positions `0..cycle` are the prefix, `cycle..` the cycle
/// (the step leaving the last position goes back to position `cycle`).
///
/// This is TLC's `LiveExprNode.evalOnLasso`, which TLC uses to tell which
/// properties a counterexample violates (`Liveness.findViolatedProperties`).
pub fn eval_lasso<B1: std::borrow::Borrow<Bits>, B2: std::borrow::Borrow<Bits>>(
    prop: &Ltl,
    states: &[B1],
    steps: &[B2],
    cycle: usize,
) -> bool {
    assert!(cycle < states.len() && states.len() == steps.len(), "a lasso with a cycle");
    eval_at(prop, states, steps, cycle, 0)
}

fn eval_at<B1: std::borrow::Borrow<Bits>, B2: std::borrow::Borrow<Bits>>(
    f: &Ltl,
    states: &[B1],
    steps: &[B2],
    cycle: usize,
    pos: usize,
) -> bool {
    // From a position in the prefix, `[]` and `<>` range over the rest of
    // the prefix and the whole cycle; from one in the cycle, over the cycle.
    let from = |pos: usize| if pos < cycle { pos } else { cycle };
    match f {
        Ltl::True => true,
        Ltl::False => false,
        Ltl::State(i) => states[pos].borrow().get(*i),
        Ltl::Action(i) => steps[pos].borrow().get(*i),
        Ltl::Not(x) => !eval_at(x, states, steps, cycle, pos),
        Ltl::And(xs) => xs.iter().all(|x| eval_at(x, states, steps, cycle, pos)),
        Ltl::Or(xs) => xs.iter().any(|x| eval_at(x, states, steps, cycle, pos)),
        Ltl::Always(x) => (from(pos)..states.len()).all(|i| eval_at(x, states, steps, cycle, i)),
        Ltl::Eventually(x) => (from(pos)..states.len()).any(|i| eval_at(x, states, steps, cycle, i)),
    }
}

#[cfg(test)]
mod tests {
    use super::{eval_lasso, Bits, Ltl};

    #[test]
    fn lasso_evaluation() {
        // x = 0, 1, 2, then back to 1: state atom 0 is "x = 0", 1 is
        // "x = 2"; action atom 0 is "x' > x".
        let states = [Bits::from_indices([0]), Bits::new(), Bits::from_indices([1])];
        let steps = [Bits::from_indices([0]), Bits::from_indices([0]), Bits::new()];
        let ev = |f: &Ltl| eval_lasso(f, &states, &steps, 1);
        let s = |i| Box::new(Ltl::State(i));
        assert!(ev(&Ltl::Eventually(s(0))));
        assert!(!ev(&Ltl::Always(Box::new(Ltl::Eventually(s(0))))));
        assert!(ev(&Ltl::Always(Box::new(Ltl::Eventually(s(1))))));
        assert!(!ev(&Ltl::Eventually(Box::new(Ltl::Always(Box::new(Ltl::Action(0)))))));
        assert!(ev(&Ltl::Always(Box::new(Ltl::Eventually(Box::new(Ltl::Not(Box::new(Ltl::Action(0)))))))));
        // A stuttering lasso: the cycle is the last state alone.
        assert!(eval_lasso(&Ltl::Eventually(Box::new(Ltl::Always(s(1)))), &states, &[Bits::new(), Bits::new(), Bits::new()], 2));
    }

    #[test]
    fn bits_inline_and_heap() {
        let mut b = Bits::from_indices([0, 5, 63]);
        assert!(b.get(0) && b.get(5) && b.get(63) && !b.get(1) && !b.get(64) && !b.get(1000));
        b.set(130, true);
        assert!(b.get(0) && b.get(63) && b.get(130) && !b.get(129));
        b.set(5, false);
        b.set(500, false);
        assert!(!b.get(5) && !b.get(500));
        assert!(Bits::from_u64(0b100).get(2));
    }
}
