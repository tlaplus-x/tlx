//! LTL (without Next) to generalized Büchi automaton, GPVW-style.
//!
//! The formula is put in negation normal form and interned. Each automaton
//! state is the result of expanding a set of obligations for the current
//! position into literals that must hold now plus obligations for the next
//! position (`<>p = p \/ X<>p`, `[]p = p /\ X[]p`). One acceptance set per
//! `<>p` subformula: states where `<>p` was not pending or `p` was chosen.

use std::collections::{BTreeSet, HashMap};

use crate::search::Within;
use crate::Ltl;

type Id = u32;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Node {
    True,
    False,
    /// Literal over a state atom (`action = false`) or action atom.
    Lit {
        action: bool,
        atom: u32,
        pos: bool,
    },
    And(Vec<Id>),
    Or(Vec<Id>),
    Always(Id),
    Eventually(Id),
}

#[derive(Default)]
struct Interner {
    nodes: tlx_base::hash::Interner<Node, Node, std::collections::hash_map::RandomState>,
    bytes: usize,
}

impl Interner {
    fn intern(&mut self, n: Node, within: &mut Within<'_>) -> Result<Id, ()> {
        let extra = 4 * std::mem::size_of::<Node>()
            + 64
            + match &n {
                Node::And(xs) | Node::Or(xs) => xs.capacity() * 8,
                _ => 0,
            };
        if !within(0, 0, self.bytes + extra) {
            return Err(());
        }
        let len = self.nodes.len();
        let id = self.nodes.intern(n);
        if self.nodes.len() != len {
            self.bytes += extra;
        }
        Ok(id)
    }

    /// Interns `f` (negated if `neg`) in negation normal form.
    fn nnf(&mut self, f: &Ltl, neg: bool, within: &mut Within<'_>) -> Result<Id, ()> {
        match f {
            Ltl::True | Ltl::False => {
                let t = matches!(f, Ltl::True) != neg;
                self.intern(if t { Node::True } else { Node::False }, within)
            }
            Ltl::State(a) => self.intern(Node::Lit { action: false, atom: *a, pos: !neg }, within),
            Ltl::Action(a) => self.intern(Node::Lit { action: true, atom: *a, pos: !neg }, within),
            Ltl::Not(g) => self.nnf(g, !neg, within),
            Ltl::And(gs) | Ltl::Or(gs) => {
                let conj = matches!(f, Ltl::And(_)) != neg;
                let ids: Vec<Id> = gs.iter().map(|g| self.nnf(g, neg, within)).collect::<Result<_, _>>()?;
                self.junction(conj, ids, within)
            }
            Ltl::Always(g) | Ltl::Eventually(g) => {
                let always = matches!(f, Ltl::Always(_)) != neg;
                let inner = self.nnf(g, neg, within)?;
                match self.nodes[inner as usize] {
                    Node::True | Node::False => Ok(inner),
                    _ if always => self.intern(Node::Always(inner), within),
                    _ => self.intern(Node::Eventually(inner), within),
                }
            }
        }
    }

    /// A flattened, simplified conjunction (`conj`) or disjunction.
    fn junction(&mut self, conj: bool, ids: Vec<Id>, within: &mut Within<'_>) -> Result<Id, ()> {
        let (unit, zero) = if conj { (Node::True, Node::False) } else { (Node::False, Node::True) };
        let mut flat = BTreeSet::new();
        for id in ids {
            match &self.nodes[id as usize] {
                n if *n == unit => {}
                n if *n == zero => return self.intern(zero, within),
                Node::And(cs) if conj => flat.extend(cs.iter().copied()),
                Node::Or(cs) if !conj => flat.extend(cs.iter().copied()),
                _ => {
                    flat.insert(id);
                }
            }
            if !within(0, 0, self.bytes + flat.len() * SET_ENTRY_BYTES) {
                return Err(());
            }
        }
        let cs: Vec<Id> = flat.into_iter().collect();
        match cs.len() {
            0 => self.intern(unit, within),
            1 => Ok(cs[0]),
            _ if conj => self.intern(Node::And(cs), within),
            _ => self.intern(Node::Or(cs), within),
        }
    }
}

/// One automaton state.
#[derive(Debug)]
pub(crate) struct AState {
    /// `(atom, polarity)` literals over state atoms, checked at the current state.
    pub state_lits: Vec<(u32, bool)>,
    /// `(atom, polarity)` literals over action atoms, checked on the edge
    /// leaving the current position.
    pub action_lits: Vec<(u32, bool)>,
    pub succ: Vec<u32>,
    /// Membership in each acceptance set.
    pub acc: Vec<bool>,
}

/// A generalized Büchi automaton over positions of a behavior.
#[derive(Debug)]
pub(crate) struct Automaton {
    pub states: Vec<AState>,
    pub init: Vec<u32>,
    pub num_acc: usize,
}

/// A partially expanded tableau node.
#[derive(Clone, Default)]
struct Partial {
    old: BTreeSet<Id>,
    lits: BTreeSet<(bool, u32, bool)>,
    next: BTreeSet<Id>,
}

type Key = (BTreeSet<(bool, u32, bool)>, BTreeSet<Id>, Vec<bool>);

// BTree nodes reserve multiple entries plus child pointers. Charge a
// conservative per-entry bound, including sparse nodes after clones.
const SET_ENTRY_BYTES: usize = 128;

impl Partial {
    fn bytes(&self) -> usize {
        std::mem::size_of::<Self>() + (self.old.len() + self.lits.len() + self.next.len()) * SET_ENTRY_BYTES
    }
}

struct ExpansionBudget<'a, 'b> {
    within: &'a mut Within<'b>,
    base: usize,
    parts: usize,
    ticks: usize,
    last: usize,
}

impl ExpansionBudget<'_, '_> {
    fn check(&mut self, scratch: usize) -> Result<(), ()> {
        self.ticks += 1;
        let bytes = self.base + self.parts + scratch;
        if self.ticks.is_multiple_of(256) || bytes.abs_diff(self.last) >= 64 * 1024 {
            self.last = bytes;
            if !(self.within)(0, 0, bytes) {
                return Err(());
            }
        }
        Ok(())
    }
}

struct Builder<'a> {
    nodes: &'a [Node],
    /// `(<>p, p)` pairs, one per acceptance set.
    evs: Vec<(Id, Id)>,
    states: Vec<AState>,
    next_of: Vec<BTreeSet<Id>>,
    by_key: HashMap<Key, u32>,
    by_obligations: HashMap<BTreeSet<Id>, Vec<u32>>,
    /// Retained allocations, conservatively allowing vector/hash growth.
    retained: usize,
}

impl Builder<'_> {
    fn expand(
        &self,
        mut todo: Vec<Id>,
        mut p: Partial,
        out: &mut Vec<Partial>,
        parents: usize,
        budget: &mut ExpansionBudget<'_, '_>,
    ) -> Result<(), ()> {
        while let Some(f) = todo.pop() {
            budget.check(parents + p.bytes() + todo.capacity() * 4)?;
            if !p.old.insert(f) {
                continue;
            }
            match &self.nodes[f as usize] {
                Node::True => {}
                Node::False => return Ok(()),
                &Node::Lit { action, atom, pos } => {
                    if p.lits.contains(&(action, atom, !pos)) {
                        return Ok(());
                    }
                    p.lits.insert((action, atom, pos));
                }
                Node::And(cs) => todo.extend(cs.iter().copied()),
                Node::Or(cs) => {
                    for &c in cs {
                        let mut t = todo.clone();
                        t.push(c);
                        self.expand(t, p.clone(), out, parents + p.bytes() + todo.capacity() * 4, budget)?;
                    }
                    return Ok(());
                }
                &Node::Always(g) => {
                    todo.push(g);
                    p.next.insert(f);
                }
                &Node::Eventually(g) => {
                    let mut t = todo.clone();
                    t.push(g);
                    self.expand(t, p.clone(), out, parents + p.bytes() + todo.capacity() * 4, budget)?;
                    p.next.insert(f);
                }
            }
        }
        budget.parts += p.bytes() + std::mem::size_of::<Partial>();
        out.push(p);
        budget.check(parents)?;
        Ok(())
    }

    /// The automaton states for the obligation set `obl`, created on demand.
    fn states_for(&mut self, obl: BTreeSet<Id>, within: &mut Within<'_>) -> Result<Vec<u32>, ()> {
        if let Some(v) = self.by_obligations.get(&obl) {
            if !within(0, 0, self.retained + v.len() * 4 + obl.len() * SET_ENTRY_BYTES) {
                return Err(());
            }
            return Ok(v.clone());
        }
        let mut parts = Vec::new();
        let mut budget = ExpansionBudget { within, base: self.retained + obl.len() * SET_ENTRY_BYTES, parts: 0, ticks: 0, last: 0 };
        self.expand(obl.iter().copied().collect(), Partial::default(), &mut parts, 0, &mut budget)?;
        // Keep the expansion buffer charged while its entries are interned.
        let scratch = budget.parts + parts.capacity() * std::mem::size_of::<Partial>();
        let mut ids = Vec::new();
        for mut p in parts {
            let acc: Vec<bool> = self.evs.iter().map(|&(ev, g)| !p.old.contains(&ev) || p.old.contains(&g)).collect();
            // `Always(h)` in `next` expands `h` at the next position too, so a
            // separate `h` in `next` is redundant (`[]<>g` otherwise forks `2^k`
            // equivalent obligation sets `{[]<>g}` vs `{[]<>g, <>g}`).
            let subsumed: Vec<Id> = p
                .next
                .iter()
                .filter_map(|&id| match self.nodes[id as usize] {
                    Node::Always(h) if p.next.contains(&h) => Some(h),
                    _ => None,
                })
                .collect();
            for h in subsumed {
                p.next.remove(&h);
            }
            let key = (p.lits, p.next, acc);
            let id = match self.by_key.get(&key) {
                Some(&id) => id,
                None => {
                    let id = self.states.len() as u32;
                    let (lits, next, acc) = key.clone();
                    let mut st = AState { state_lits: Vec::new(), action_lits: Vec::new(), succ: Vec::new(), acc };
                    for (action, atom, pos) in lits {
                        if action {
                            st.action_lits.push((atom, pos));
                        } else {
                            st.state_lits.push((atom, pos));
                        }
                    }
                    self.retained += 2 * std::mem::size_of::<AState>()
                        + (key.0.len() + 2 * key.1.len()) * SET_ENTRY_BYTES
                        + 2 * key.2.len()
                        + 2 * (st.state_lits.capacity() + st.action_lits.capacity()) * 8
                        + 2 * std::mem::size_of::<Key>()
                        + 128;
                    self.states.push(st);
                    self.next_of.push(next);
                    self.by_key.insert(key, id);
                    id
                }
            };
            if !within(0, 0, self.retained + scratch + ids.capacity() * 4) {
                return Err(());
            }
            if !ids.contains(&id) {
                ids.push(id);
            }
        }
        self.retained += obl.len() * SET_ENTRY_BYTES + ids.len() * 8 + 128;
        self.by_obligations.insert(obl, ids.clone());
        Ok(ids)
    }
}

impl Automaton {
    /// An automaton accepting exactly the behaviors violating `prop`.
    #[cfg(test)]
    pub(crate) fn for_negation(prop: &Ltl) -> Automaton {
        Self::for_negation_within(prop, &mut |_, _, _| true).unwrap()
    }

    pub(crate) fn universal() -> Self {
        Self { states: vec![AState { state_lits: vec![], action_lits: vec![], succ: vec![0], acc: vec![] }], init: vec![0], num_acc: 0 }
    }

    pub(crate) fn bytes(&self) -> usize {
        self.states.capacity() * std::mem::size_of::<AState>()
            + self.init.capacity() * 4
            + self
                .states
                .iter()
                .map(|s| (s.state_lits.capacity() + s.action_lits.capacity()) * 8 + s.succ.capacity() * 4 + s.acc.capacity())
                .sum::<usize>()
    }

    pub(crate) fn for_negation_within(prop: &Ltl, within: &mut Within<'_>) -> Result<Automaton, ()> {
        // Bound interning storage and its temporary flattened sets before
        // allocating them. No DNF distribution occurs here.
        fn formula_bytes(f: &Ltl) -> usize {
            256usize.saturating_add(match f {
                Ltl::Not(x) | Ltl::Always(x) | Ltl::Eventually(x) => formula_bytes(x),
                Ltl::And(xs) | Ltl::Or(xs) => xs.iter().fold(0usize, |n, x| n.saturating_add(formula_bytes(x))),
                _ => 0,
            })
        }
        let formula_bytes = formula_bytes(prop);
        if !within(0, 0, formula_bytes) {
            return Err(());
        }
        let mut it = Interner { bytes: formula_bytes, ..Interner::default() };
        let root = it.nnf(prop, true, within)?;
        let evs = it
            .nodes
            .iter()
            .enumerate()
            .filter_map(|(i, n)| match *n {
                Node::Eventually(g) => Some((i as Id, g)),
                _ => None,
            })
            .collect();
        let mut b = Builder {
            nodes: &it.nodes,
            evs,
            states: Vec::new(),
            next_of: Vec::new(),
            by_key: HashMap::new(),
            by_obligations: HashMap::new(),
            retained: it.bytes + it.nodes.len() * 8,
        };
        let init = b.states_for(BTreeSet::from([root]), within)?;
        let mut done = 0;
        while done < b.states.len() {
            let succ = b.states_for(b.next_of[done].clone(), within)?;
            b.retained += succ.capacity() * 4;
            b.states[done].succ = succ;
            done += 1;
        }
        if !within(0, 0, b.retained) {
            return Err(());
        }
        Ok(Automaton { states: b.states, init, num_acc: b.evs.len() })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trivial_properties() {
        // ¬True has no runs.
        let a = Automaton::for_negation(&Ltl::True);
        assert!(a.init.is_empty());
        // ¬[]p = <>¬p: one acceptance set.
        let a = Automaton::for_negation(&Ltl::Always(Box::new(Ltl::State(0))));
        assert_eq!(a.num_acc, 1);
        assert!(!a.init.is_empty());
        // ¬(<>[]p0 \/ <>[]p1 \/ <>[]p2) = []<>¬p0 /\ []<>¬p1 /\ []<>¬p2:
        // next-obligation subsumption expands one obligation set (2^3 = 8
        // states, one per acceptance combination, instead of 2 * 2^3 = 16).
        let prop = Ltl::Or((0..3).map(|i| Ltl::Eventually(Box::new(Ltl::Always(Box::new(Ltl::State(i)))))).collect());
        let a = Automaton::for_negation(&prop);
        assert_eq!(a.states.len(), 8);
    }
}
