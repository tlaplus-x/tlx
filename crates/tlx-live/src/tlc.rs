//! TLC-compatible liveness checking for behavior graphs whose nodes are
//! classes of states (fingerprints under VIEW or SYMMETRY) rather than
//! states.
//!
//! When several states share a fingerprint, TLC's verdict depends on which
//! of them it evaluates each predicate on. This module reproduces TLC's
//! algorithm (tlc2.tool.liveness: `Liveness.processLiveness`,
//! `TBPar`/`TBGraph`, `LiveCheck.TableauLiveChecker`/`LiveChecker`,
//! `LiveWorker.checkComponent`):
//!
//! - the negated property is put in disjunctive normal form; in each
//!   disjunct, the conjuncts `[]<>A` / `<>[]A` (A without temporal
//!   operators) become conditions on cycles ("possible error models"), the
//!   rest the tableau formula, translated into a particle tableau;
//! - the product of the behavior graph and the tableau is built in TLC's
//!   order: graph nodes are expanded in BFS order, from the state the
//!   search expanded (the first one found); a tableau node is consistent
//!   with a step if its state predicates hold on the *successor state* of
//!   the step; a product node created for an already expanded graph node is
//!   expanded at once from that successor state (not from the first one
//!   found); only the first edge between two product nodes is kept;
//! - cycle conditions and fairness are evaluated on the state that
//!   expanded a product node and on the steps from it.
//!
//! Without VIEW or SYMMETRY (one state per graph node) this coincides with
//! `crate::check` on the state graph.

use std::borrow::Cow;
use std::sync::Arc;

use crate::tableau::{AState, Automaton};
use crate::{Bits, Fairness, Ltl};

/// A successor of a concrete state.
#[derive(Clone, Debug)]
pub struct Succ {
    /// The graph node (fingerprint class) of the successor.
    pub node: u32,
    /// The caller's index of this successor of the expanded state (what
    /// [`Expand::expand`] and [`Conc::Succ`] refer to it by).
    pub idx: u32,
    /// State-atom bits of the successor state.
    pub bits: Bits,
    /// Action-atom bits of the step.
    pub step: Bits,
    /// The caller's label of the step (e.g. its action).
    pub label: u32,
}

/// A concrete state with its successors (the stuttering step first, as TLC).
#[derive(Clone, Debug, Default)]
pub struct Expansion {
    /// The expanded state (an id of the caller's).
    pub conc: u32,
    /// State-atom bits of the state.
    pub bits: Bits,
    pub succ: Vec<Succ>,
}

/// One call of TLC's `LiveCheck.addInitState` / `addNextState`, in order.
#[derive(Clone, Debug)]
pub enum Event {
    /// An initial state (`bits`: its state-atom bits).
    Init { node: u32, conc: u32, bits: Bits },
    /// The search expanded a state of graph node `node` (which is then done).
    Next { node: u32, exp: Expansion },
}

/// Expansion of concrete states on demand (from the spec, not the graph).
/// The product asks for successors of the states of the event it is
/// processing (and of the states it expanded on demand since), so a caller
/// streaming the events only needs to keep those states.
pub trait Expand {
    type Error;

    /// The expansion of successor `idx` of the expanded state `from`; the
    /// caller gives it an id of its own (`Expansion::conc`).
    fn expand(&mut self, from: u32, idx: u32) -> Result<Expansion, Self::Error>;
}

/// A concrete state of a counterexample, as the caller can rebuild it: one
/// of its states, or a successor of one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Conc {
    State(u32),
    Succ { from: u32, idx: u32 },
}

/// A position of a counterexample.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CStep {
    /// The graph node and the concrete state at this position.
    pub node: u32,
    pub conc: Conc,
    /// The label of the step leaving this position.
    pub label: u32,
}

/// A counterexample: `prefix` then `cycle` forever (the step leaving the
/// last cycle position goes back to the product node of `cycle[0]`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CLasso {
    pub prefix: Vec<CStep>,
    pub cycle: Vec<CStep>,
}

/// Check `prop` under `fairness` TLC's way on the behavior graph given by
/// `events`; `Ok(Err(lasso))` if it is violated.
pub fn check_concrete<X: Expand + ?Sized>(
    events: &[Event],
    ex: &mut X,
    prop: &Ltl,
    fairness: &[Fairness],
) -> Result<Result<(), CLasso>, X::Error> {
    let mut c = ConcreteChecker::new(std::slice::from_ref(prop), fairness);
    for ev in events {
        c.event(ev, ex);
    }
    Ok(match c.finish()? {
        Some((_, l)) => Err(l),
        None => Ok(()),
    })
}

/// TLC's checking of several properties on a behavior graph given event by
/// event (as TLC's search calls `LiveCheck`): the products of every
/// property's tableaux are built while the events stream in, so the caller
/// does not have to keep the states of the graph.
pub struct ConcreteChecker<E = String> {
    /// In order: properties, then the solutions of each.
    slots: Vec<Slot<E>>,
    pats: Pats,
}

struct Slot<E> {
    prop: usize,
    pems: Vec<Pem>,
    p: TProduct,
    /// An expansion failed while building the product.
    err: Option<E>,
}

impl<E> ConcreteChecker<E> {
    pub fn new(props: &[Ltl], fairness: &[Fairness]) -> ConcreteChecker<E> {
        let mut slots = Vec::new();
        for (prop, f) in props.iter().enumerate() {
            for sol in solutions(f, fairness) {
                let (aut, sinks) = automaton(&sol);
                let mut p = TProduct::new(Arc::new(aut), sol.tf.is_some());
                if sol.pems.iter().any(Pem::is_empty) {
                    p.sinks = sinks;
                }
                slots.push(Slot { prop, p, pems: sol.pems, err: None });
            }
        }
        ConcreteChecker { slots, pats: Pats::new() }
    }

    /// The next event of the search.
    pub fn event<X: Expand<Error = E> + ?Sized>(&mut self, ev: &Event, ex: &mut X) {
        for s in &mut self.slots {
            if s.err.is_none() {
                if let Err(e) = s.p.event(ev, ex, &mut self.pats) {
                    s.err = Some(e);
                }
            }
        }
    }

    /// After an event: the violation TLC reports at once, during its search,
    /// if this event completed one (the first property in order, with its
    /// counterexample: a path to a state that may stutter forever).
    ///
    /// TLC (`LiveCheck.TableauLiveChecker.addNextState`) reports a
    /// "safety-like" violation when, expanding a new product node of a state
    /// it has already expanded (the recursion of `addNextState`), the
    /// stuttering step leads to an accepting sink of the tableau (an empty
    /// particle, its only successor itself) and some error model of the
    /// solution has no condition on cycles: whatever follows, the behavior
    /// violates the property. It stops the search there. Product nodes
    /// reaching such a sink otherwise are found by the liveness check after
    /// the search.
    pub fn fired(&mut self) -> Option<(usize, CLasso)> {
        let s = self.slots.iter_mut().find(|s| s.p.fire.is_some())?;
        Some((s.prop, s.p.fire_lasso()))
    }

    /// The number of product nodes and edges built so far, and an estimate
    /// of their memory in bytes.
    pub fn size(&self) -> (usize, usize, usize) {
        let (mut n, mut e, mut b) = (0, 0, self.pats.bytes());
        for s in &self.slots {
            let (n1, e1, b1) = s.p.size();
            n += n1;
            e += e1;
            b += b1;
        }
        (n, e, b)
    }

    /// After the last event: the first property violated (in the order of
    /// `props`) with a counterexample, or the first expansion error, checking
    /// the properties in order as TLC (a violation of an earlier property
    /// wins over an error building the product of a later one).
    pub fn finish(self) -> Result<Option<(usize, CLasso)>, E> {
        let pats = self.pats;
        for mut s in self.slots {
            if let Some(e) = s.err {
                return Err(e);
            }
            s.p.finish();
            for pem in &s.pems {
                if let Some(l) = s.p.search(pem, &pats) {
                    return Ok(Some((s.prop, l)));
                }
            }
        }
        Ok(None)
    }
}

/// A state of a simulated behavior.
#[derive(Clone, Debug)]
pub struct TraceState {
    /// Graph node (fingerprint class) and concrete state.
    pub node: u32,
    pub conc: u32,
    /// State-atom bits of the state.
    pub bits: Bits,
    /// Action-atom bits of its stuttering step and of the step into it
    /// (from the previous state).
    pub stutter: Bits,
    pub step: Bits,
    /// The label of the step into it.
    pub label: u32,
}

/// The label of stuttering steps in counterexamples of [`check_trace`].
pub const STUTTER: u32 = u32::MAX;

/// Check `prop` under `fairness` TLC's way on one simulated behavior (TLC's
/// simulator: `LiveCheck1.checkTrace`); `Some(lasso)` if it is violated.
pub fn check_trace(trace: &[TraceState], prop: &Ltl, fairness: &[Fairness]) -> Option<CLasso> {
    if trace.is_empty() {
        return None;
    }
    for sol in solutions(prop, fairness) {
        let mut pats = Pats::new();
        let mut p = TProduct::new(Arc::new(automaton(&sol).0), sol.tf.is_some());
        p.build_trace(trace, &mut pats);
        p.finish();
        for pem in &sol.pems {
            if let Some(l) = p.search(pem, &pats) {
                return Some(l);
            }
        }
    }
    None
}

/// The automaton of a solution, and which of its states are TLC's accepting
/// sinks (`TBGraphNode.isAccepting`: an empty particle whose only successor
/// is itself; none without a tableau).
fn automaton(sol: &Solution) -> (Automaton, Vec<bool>) {
    match &sol.tf {
        Some(tf) => particle_tableau(tf),
        None => (
            Automaton {
                states: vec![AState { state_lits: Vec::new(), action_lits: Vec::new(), succ: vec![0], acc: Vec::new() }],
                init: vec![0],
                num_acc: 0,
            },
            vec![false],
        ),
    }
}

/// Whether TLC may report a violation of `prop` under `fairness` during its
/// search, before checking liveness (`LiveCheck.TableauLiveChecker`'s
/// "safety-like" violations): some disjunct of the negated property has no
/// condition on cycles and its tableau has an accepting sink. See
/// [`ConcreteChecker::fired`].
pub fn reports_early(prop: &Ltl, fairness: &[Fairness]) -> bool {
    fairness.is_empty() && has_pem_free_accepting_sink(prop)
}

mod formula;
mod product;
mod tableau;

pub use formula::{check_size, tableau_initial_checks, tableau_state_atoms};
use formula::{has_pem_free_accepting_sink, solutions, Pem, Solution};
use product::{Pats, TProduct};
use tableau::particle_tableau;

#[cfg(test)]
mod tests {
    use super::formula::F;
    use super::*;

    fn st(i: u32) -> Ltl {
        Ltl::State(i)
    }

    #[test]
    fn decomposition() {
        // ¬[]<>p = <>[]¬p: one error model, no tableau.
        let s = solutions(&Ltl::Always(Box::new(Ltl::Eventually(Box::new(st(0))))), &[]);
        assert_eq!(s.len(), 1);
        assert!(s[0].tf.is_none());
        assert_eq!(s[0].pems[0].ea.len(), 1);
        // ¬<>p = []¬p: a tableau.
        let s = solutions(&Ltl::Eventually(Box::new(st(0))), &[]);
        assert!(s[0].tf.is_some() && s[0].pems.len() == 1);
        // ¬(<>[]p \/ <>[]q) = []<>¬p /\ []<>¬q.
        let s = solutions(
            &Ltl::Or(vec![
                Ltl::Eventually(Box::new(Ltl::Always(Box::new(st(0))))),
                Ltl::Eventually(Box::new(Ltl::Always(Box::new(st(1))))),
            ]),
            &[],
        );
        assert_eq!(s[0].pems[0].ae_state.len(), 2);
    }

    #[test]
    fn tableau_of_always() {
        // []¬p: one particle {[]¬p, ¬p, ()[]¬p} looping to itself.
        let (a, sinks) = particle_tableau(&F::All(Box::new(F::Lit { action: false, atom: 0, pos: false })));
        assert_eq!(a.states.len(), 1);
        assert_eq!(a.states[0].state_lits, vec![(0, false)]);
        assert_eq!(a.states[0].succ, vec![0]);
        // (Not empty: no accepting sink.)
        assert_eq!(sinks, vec![false]);
    }

    #[test]
    fn early_reports() {
        let al = |f: Ltl| Ltl::Always(Box::new(f));
        let ev = |f: Ltl| Ltl::Eventually(Box::new(f));
        let imp = |a: Ltl, b: Ltl| Ltl::Or(vec![Ltl::Not(Box::new(a)), b]);
        // [](p => []q): its negation <>(p /\ <>~q) is satisfied by a finite
        // prefix.
        let safety = al(imp(st(0), al(st(1))));
        assert!(reports_early(&safety, &[]));
        // Fairness adds cycle conditions to every disjunct.
        assert!(!reports_early(&safety, &[Fairness { strong: false, enabled: 2, taken: 0 }]));
        // <>p, []<>p, p ~> q: violated by infinite behaviors only.
        assert!(!reports_early(&ev(st(0)), &[]));
        assert!(!reports_early(&al(ev(st(0))), &[]));
        assert!(!reports_early(&al(imp(st(0), ev(st(1)))), &[]));
    }

    #[test]
    fn fast_metadata_agrees_with_solutions_on_small_formulas() {
        let base = [Ltl::True, Ltl::False, st(0), st(1), Ltl::Action(0)];
        let mut layer = base.to_vec();
        let mut all = base.to_vec();
        for _ in 0..2 {
            let mut next = Vec::new();
            for a in &layer {
                next.push(Ltl::Not(Box::new(a.clone())));
                next.push(Ltl::Always(Box::new(a.clone())));
                next.push(Ltl::Eventually(Box::new(a.clone())));
            }
            for a in &layer {
                for b in &layer {
                    next.push(Ltl::And(vec![a.clone(), b.clone()]));
                    next.push(Ltl::Or(vec![a.clone(), b.clone()]));
                }
            }
            all.extend(next.iter().cloned());
            layer = next;
        }
        let fair_cases: [&[Fairness]; 3] =
            [&[], &[Fairness { strong: false, enabled: 1, taken: 0 }], &[Fairness { strong: true, enabled: 1, taken: 0 }]];
        for f in &all {
            for fair in fair_cases {
                assert!(check_size(f, fair).is_ok());
                let sols = solutions(f, fair);
                let mut want_atoms = Vec::new();
                let mut want_init = Vec::new();
                for sol in &sols {
                    if let Some(tf) = &sol.tf {
                        fn collect(f: &F, out: &mut Vec<u32>) {
                            match f {
                                F::Bool(_) => {}
                                F::Lit { action, atom, .. } => {
                                    if !*action && !out.contains(atom) {
                                        out.push(*atom);
                                    }
                                }
                                F::And(xs) | F::Or(xs) => xs.iter().for_each(|x| collect(x, out)),
                                F::All(x) | F::Even(x) => collect(x, out),
                            }
                        }
                        collect(tf, &mut want_atoms);
                        want_init.extend(tableau::initial_checks(tf));
                    }
                }
                let got_atoms = tableau_state_atoms(f, fair);
                assert_eq!(got_atoms, want_atoms, "tableau_state_atoms order of {f:?} under {fair:?}");
                assert_eq!(tableau_initial_checks(f, fair), want_init, "tableau_initial_checks of {f:?} under {fair:?}");

                let want_early =
                    sols.iter().any(|sol| sol.tf.is_some() && sol.pems.iter().any(Pem::is_empty) && automaton(sol).1.iter().any(|&b| b));
                assert_eq!(reports_early(f, fair), want_early, "reports_early of {f:?} under {fair:?}");
            }
        }
        // Negated `(<>p0 \/ <>p1) /\ (<>p2 \/ <>p3)` distributes in TLC solution
        // order `[0, 2, 3, 1]`, not syntactic AST order `[0, 1, 2, 3]`.
        let cross = Ltl::Or(vec![
            Ltl::And(vec![Ltl::Always(Box::new(Ltl::Not(Box::new(st(0))))), Ltl::Always(Box::new(Ltl::Not(Box::new(st(1)))))]),
            Ltl::And(vec![Ltl::Always(Box::new(Ltl::Not(Box::new(st(2))))), Ltl::Always(Box::new(Ltl::Not(Box::new(st(3)))))]),
        ]);
        assert_eq!(tableau_state_atoms(&cross, &[]), vec![0, 2, 3, 1]);

        // Deeper mixed PEM + non-PEM `[]<>[]` cases: stripping a PEM sibling
        // from a conjunction (`([]<>[]p0 /\ <>[]p1) \/ <>p2` and
        // `(<>[]p2 /\ []<>[]p0) \/ p1`) must not re-run `[]<>` disjunction
        // merging and push `p0` past `p2` / `p1`.
        let al = |x: Ltl| Ltl::Always(Box::new(x));
        let ev = |x: Ltl| Ltl::Eventually(Box::new(x));
        let nt = |x: Ltl| Ltl::Not(Box::new(x));
        let mixed_cases = [
            // Negation: `([]<>[]~p0 /\ <>[]~p1) \/ <>~p2` -> atoms `[0, 2]`.
            Ltl::And(vec![Ltl::Or(vec![ev(al(ev(st(0)))), al(ev(st(1)))]), al(st(2))]),
            // Negation: `(<>[]~p2 /\ []<>[]~p0) \/ ~p1` -> atoms `[0, 1]`.
            Ltl::And(vec![Ltl::Or(vec![al(ev(st(2))), ev(al(ev(st(0))))]), st(1)]),
            // Negation: `[]<>[]~p0 \/ (p1 /\ <>[]~p2) \/ []<>[]~p3` -> `[1, 0, 3]`.
            Ltl::And(vec![ev(al(ev(st(0)))), Ltl::Or(vec![nt(st(1)), al(ev(st(2)))]), ev(al(ev(st(3))))]),
            // Negation: `([]<>TRUE \/ []<>[]TRUE) /\ p0`. Merged `[]<>(TRUE \/ []TRUE)`
            // stays in the tableau (not re-simplified to `[]<>TRUE`), so no accepting sink.
            Ltl::Or(vec![Ltl::And(vec![ev(al(Ltl::False)), ev(al(ev(Ltl::False)))]), nt(st(0))]),
        ];
        for (idx, mf) in mixed_cases.iter().enumerate() {
            for fair in fair_cases {
                let sols = solutions(mf, fair);
                let mut want_atoms = Vec::new();
                let mut want_init = Vec::new();
                for sol in &sols {
                    if let Some(tf) = &sol.tf {
                        fn collect(f: &F, out: &mut Vec<u32>) {
                            match f {
                                F::Bool(_) => {}
                                F::Lit { action, atom, .. } => {
                                    if !*action && !out.contains(atom) {
                                        out.push(*atom);
                                    }
                                }
                                F::And(xs) | F::Or(xs) => xs.iter().for_each(|x| collect(x, out)),
                                F::All(x) | F::Even(x) => collect(x, out),
                            }
                        }
                        collect(tf, &mut want_atoms);
                        want_init.extend(tableau::initial_checks(tf));
                    }
                }
                assert_eq!(tableau_state_atoms(mf, fair), want_atoms, "mixed case {idx} atoms under {fair:?}");
                assert_eq!(tableau_initial_checks(mf, fair), want_init, "mixed case {idx} init checks under {fair:?}");
                let want_early =
                    sols.iter().any(|sol| sol.tf.is_some() && sol.pems.iter().any(Pem::is_empty) && automaton(sol).1.iter().any(|&b| b));
                assert_eq!(reports_early(mf, fair), want_early, "mixed case {idx} reports_early under {fair:?}");
            }
        }
        assert_eq!(tableau_state_atoms(&mixed_cases[0], &[]), vec![0, 2]);
        assert_eq!(tableau_state_atoms(&mixed_cases[1], &[]), vec![0, 1]);
        assert!(!reports_early(&mixed_cases[3], &[]));
        // Wide flat disjunction (100,000 copies of `[]p0`, negated to one flat
        // conjunction) must not overflow the call stack.
        let wide = Ltl::Or(vec![al(st(0)); 100_000]);
        assert!(check_size(&wide, &[]).is_ok());
        assert_eq!(tableau_state_atoms(&wide, &[]), vec![0]);
        assert_eq!(crate::branches([&wide]), 1);
        // DNF overflow (> i32::MAX disjuncts) is still rejected without allocating.
        let huge_sf: Vec<Fairness> = (0..32).map(|i| Fairness { strong: true, enabled: i, taken: i }).collect();
        assert!(check_size(&Ltl::Eventually(Box::new(st(0))), &huge_sf).is_err());
    }

    #[test]
    fn concrete_checker_preserves_typed_error_in_property_order() {
        #[derive(Debug, PartialEq, Eq)]
        enum ErrKind {
            First,
            Second,
        }
        struct PerSlotErr(usize);
        impl Expand for PerSlotErr {
            type Error = ErrKind;
            fn expand(&mut self, _from: u32, _idx: u32) -> Result<Expansion, ErrKind> {
                self.0 += 1;
                Err(if self.0 == 1 { ErrKind::First } else { ErrKind::Second })
            }
        }
        let p = Ltl::Always(Box::new(Ltl::Or(vec![st(0), Ltl::Always(Box::new(st(0)))])));
        let q = Ltl::Eventually(Box::new(Ltl::Always(Box::new(Ltl::Or(vec![st(1), Ltl::Eventually(Box::new(st(0)))])))));
        let mut checker: ConcreteChecker<ErrKind> = ConcreteChecker::new(&[p, q], &[]);
        let mut ex = PerSlotErr(0);
        let b0 = Bits::from_words(&[1]);
        let b1 = Bits::from_words(&[0]);
        checker.event(&Event::Init { node: 0, conc: 0, bits: b0.clone() }, &mut ex);
        checker.event(
            &Event::Next {
                node: 0,
                exp: Expansion {
                    conc: 0,
                    bits: b0.clone(),
                    succ: vec![
                        Succ { node: 0, idx: 0, bits: b0.clone(), step: Bits::new(), label: 0 },
                        Succ { node: 1, idx: 1, bits: b1.clone(), step: Bits::new(), label: 1 },
                    ],
                },
            },
            &mut ex,
        );
        checker.event(
            &Event::Next {
                node: 1,
                exp: Expansion {
                    conc: 1,
                    bits: b1.clone(),
                    succ: vec![
                        Succ { node: 1, idx: 0, bits: b1.clone(), step: Bits::new(), label: 0 },
                        Succ { node: 0, idx: 1, bits: b0, step: Bits::new(), label: 1 },
                    ],
                },
            },
            &mut ex,
        );
        assert_eq!(ex.0, 2, "both property slots should trigger on-demand expansion");
        assert_eq!(checker.finish(), Err(ErrKind::First));
    }
}
