//! Hand-made liveness scenarios.

mod common;

use common::*;
use tlx_live::{check, check_lasso, Fairness, Graph, Lasso, Ltl};

fn violated(g: &Graph, prop: &Ltl, fair: &[Fairness]) -> Lasso {
    let l = check_lasso(g, prop, fair).expect_err("expected a violation");
    if let Some(err) = lasso_error(g, prop, fair, &l) {
        panic!("invalid counterexample {l:?}: {err}");
    }
    let c = check(g, prop, fair).expect_err("check agrees");
    assert_eq!(c.prefix, l.prefix.iter().map(|x| x.0).collect::<Vec<_>>());
    assert_eq!(c.cycle, l.cycle.iter().map(|x| x.0).collect::<Vec<_>>());
    l
}

fn holds(g: &Graph, prop: &Ltl, fair: &[Fairness]) {
    if let Err(l) = check_lasso(g, prop, fair) {
        panic!("unexpected counterexample {l:?}");
    }
    assert!(brute_force(g, prop, fair, 6).is_none());
}

// State atoms: 0 = p, 1 = ENABLED A. Action atom 0 = A.
// 0 --A--> 1, p holds in 1.
fn eventually_graph() -> Graph {
    graph(&[0], &[0b10, 0b01], &[(0, 1, 0b1)], true)
}

#[test]
fn eventually_violated_by_stuttering() {
    let g = eventually_graph();
    let l = violated(&g, &eventually(st(0)), &[]);
    assert!(l.prefix.is_empty());
    assert_eq!(l.cycle.len(), 1);
    assert_eq!(l.cycle[0].0, 0);
}

#[test]
fn eventually_holds_under_weak_fairness() {
    let g = eventually_graph();
    holds(&g, &eventually(st(0)), &[wf(1, 0)]);
    // Fairness of an unrelated action does not help.
    violated(&g, &eventually(st(0)), &[wf(2, 1)]);
}

#[test]
fn partial_frontier_has_no_fair_stuttering_behavior() {
    // At 0 the progress action is enabled. Its target has not been expanded.
    let g = graph(&[0], &[0b10, 0], &[(0, 0, 0), (0, 1, 1)], false);
    let property = eventually(st(0));
    let fair = [wf(1, 0)];
    assert!(tlx_live::check_lasso_csr(&tlx_live::Csr::from_graph(&g), &property, &fair).is_ok());
    // As soon as the target is expanded and admits stuttering without fairness
    // obligations, the same property has a real lasso.
    let closed = graph(&[0], &[0b10, 0], &[(0, 1, 1)], true);
    violated(&closed, &property, &fair);
}

#[test]
fn trivial_properties() {
    let g = eventually_graph();
    holds(&g, &Ltl::True, &[]);
    violated(&g, &Ltl::False, &[]);
    holds(&g, &always(Ltl::True), &[]);
    violated(&g, &eventually(Ltl::False), &[]);
}

// Two states toggling: 0 --A--> 1 --B--> 0; p in 1. Atoms: state 0 = p,
// 1 = ENABLED A (in 0), 2 = ENABLED B (in 1); action 0 = A, 1 = B.
fn toggle_graph() -> Graph {
    graph(&[0], &[0b010, 0b101], &[(0, 1, 0b01), (1, 0, 0b10)], true)
}

#[test]
fn infinitely_often() {
    let g = toggle_graph();
    let p = always(eventually(st(0)));
    violated(&g, &p, &[]);
    violated(&g, &p, &[wf(2, 1)]);
    holds(&g, &p, &[wf(1, 0)]);
    holds(&g, &p, &[wf(1, 0), wf(2, 1)]);
    // Infinitely often not p needs B to be fair as well.
    let np = always(eventually(not(st(0))));
    violated(&g, &np, &[wf(1, 0)]);
    holds(&g, &np, &[wf(1, 0), wf(2, 1)]);
}

#[test]
fn eventually_always() {
    let g = toggle_graph();
    let p = eventually(always(st(0)));
    let l = violated(&g, &p, &[wf(1, 0), wf(2, 1)]);
    assert!(l.cycle.iter().any(|x| x.0 == 0) && l.cycle.iter().any(|x| x.0 == 1));
    // Without the B edge back, the behavior stays in 1 forever.
    let g2 = graph(&[0], &[0b010, 0b001], &[(0, 1, 0b01)], true);
    holds(&g2, &p, &[wf(1, 0)]);
    violated(&g2, &p, &[]);
}

#[test]
fn leads_to_property() {
    // 0 (p) --A--> 1 --B--> 2 (q); 2 --C--> 0. State atoms: 0 = p, 1 = q,
    // 2 = ENABLED A, 3 = ENABLED B, 4 = ENABLED C. Actions 0 = A, 1 = B, 2 = C.
    let g = graph(&[0], &[0b00101, 0b01000, 0b10010], &[(0, 1, 0b001), (1, 2, 0b010), (2, 0, 0b100)], true);
    let prop = leads_to(st(0), st(1));
    violated(&g, &prop, &[]);
    violated(&g, &prop, &[wf(2, 0)]);
    holds(&g, &prop, &[wf(2, 0), wf(3, 1)]);
    holds(&g, &prop, &[wf(2, 0), wf(3, 1), wf(4, 2)]);
    // q ~> p needs C.
    let back = leads_to(st(1), st(0));
    violated(&g, &back, &[wf(2, 0), wf(3, 1)]);
    holds(&g, &back, &[wf(2, 0), wf(3, 1), wf(4, 2)]);
}

#[test]
fn weak_vs_strong_fairness() {
    // 0 <-B-> 1 toggles; A (only enabled in 0) leads to 2 where q holds.
    // State atoms: 0 = q, 1 = ENABLED A, 2 = ENABLED B. Actions 0 = A, 1 = B.
    let g = graph(&[0], &[0b110, 0b100, 0b001], &[(0, 1, 0b10), (1, 0, 0b10), (0, 2, 0b01)], true);
    let prop = eventually(st(0));
    let l = violated(&g, &prop, &[wf(1, 0), wf(2, 1)]);
    let states: Vec<u32> = l.cycle.iter().map(|x| x.0).collect();
    assert!(states.contains(&0) && states.contains(&1));
    holds(&g, &prop, &[sf(1, 0), wf(2, 1)]);
    // SF alone: staying in 1 forever (A disabled) is fair.
    violated(&g, &prop, &[sf(1, 0)]);
}

#[test]
fn strong_fairness_refinement_nested() {
    // SCC {0,1,2}: 0 -> 1 -> 2 -> 0 via B; SF(A) with A enabled only in 0 and
    // never taken inside; removing 0 leaves {1,2} with no cycle except stuttering.
    // A leads out to 3 where q holds. State atoms: 0 = q, 1 = ENABLED A.
    let g = graph(&[0], &[0b10, 0b00, 0b00, 0b01], &[(0, 1, 0b10), (1, 2, 0b10), (2, 0, 0b10), (0, 3, 0b01)], true);
    let prop = eventually(st(0));
    // With stuttering, staying in 1 forever is still a fair violation.
    let l = violated(&g, &prop, &[sf(1, 0)]);
    assert!(l.cycle.iter().all(|x| x.0 != 0));
    // Without stuttering edges in 1 and 2, the only cycles pass through 0.
    let mut g2 = g.clone();
    g2.edges[1].pop();
    g2.edges[2].pop();
    holds(&g2, &prop, &[sf(1, 0), wf(1, 0)]);
    holds(&g2, &prop, &[sf(1, 0)]);
    violated(&g2, &prop, &[wf(1, 0)]);
}

#[test]
fn action_atoms_in_property() {
    // One state with an A self-loop and a stuttering self-loop.
    // State atom 0 = ENABLED A, action atom 0 = A.
    let g = graph(&[0], &[0b1], &[(0, 0, 0b1)], true);
    let prop = always(eventually(act(0)));
    let l = violated(&g, &prop, &[]);
    assert!(l.cycle.iter().all(|&x| x == (0, 1)));
    holds(&g, &prop, &[wf(0, 0)]);
    // <>[]~A: violated by taking A forever, also mixed cycles.
    let p2 = eventually(always(not(act(0))));
    let l = violated(&g, &p2, &[]);
    assert!(l.cycle.iter().any(|&(_, e)| e == 0));
    // [](A => <>~A) is violated only by A forever.
    let p3 = always(or(vec![not(act(0)), eventually(not(act(0)))]));
    let l = violated(&g, &p3, &[]);
    assert!(l.cycle.iter().all(|&(_, e)| e == 0));
}

#[test]
fn parallel_edges_with_different_bits() {
    // Two edges 0 -> 1 with action bits {0} and {1}; 1 -> 0 with {0}.
    let g = graph(&[0], &[0, 0], &[(0, 1, 0b01), (0, 1, 0b10), (1, 0, 0b01)], false);
    let prop = always(not(act(1)));
    let l = violated(&g, &prop, &[]);
    let used: Vec<_> = l.prefix.iter().chain(&l.cycle).filter(|x| x.0 == 0).collect();
    assert!(used.iter().any(|x| x.1 == 1));
    violated(&g, &always(act(0)), &[]);
    holds(&g, &always(or(vec![act(0), act(1)])), &[]);
    // []<>Action(1) fails: one can always take the {0} edge.
    let l = violated(&g, &always(eventually(act(1))), &[]);
    assert!(l.cycle.iter().all(|x| !(x.0 == 0 && x.1 == 1)));
    // With "enabled" only in 0, SF forces the {1} step but WF does not.
    let mut g2 = g.clone();
    g2.state_bits[0] = tlx_live::Bits::from_u64(1);
    holds(&g2, &always(eventually(act(1))), &[sf(0, 1)]);
    violated(&g2, &always(eventually(act(1))), &[wf(0, 1)]);
}

#[test]
fn multiple_initial_states_and_unreachable() {
    // 2 is unreachable and is the only bad place.
    let g = graph(&[0, 1], &[0b1, 0b1, 0b0], &[(0, 1, 0), (2, 2, 0)], true);
    holds(&g, &always(st(0)), &[]);
    let g2 = graph(&[0, 2], &[0b1, 0b1, 0b0], &[(0, 1, 0)], true);
    let l = violated(&g2, &always(st(0)), &[]);
    assert_eq!(l.prefix.first().map_or(l.cycle[0].0, |x| x.0), 2);
}

#[test]
fn large_atom_indices() {
    let mut g = eventually_graph();
    g.state_bits[1].set(200, true);
    g.edges[0][0].1.set(130, true);
    g.state_bits[0].set(77, true);
    holds(&g, &eventually(st(200)), &[wf(77, 130)]);
    violated(&g, &eventually(st(200)), &[]);
}
