//! Randomized cross-check of `check` against brute-force lasso enumeration.

mod common;

use common::*;
use tlx_live::{check_lasso, Bits, Fairness, Graph, Ltl};

const STATE_ATOMS: u32 = 3;
const ACTION_ATOMS: u32 = 2;

use tlx_testkit::XorShift64Star as Rng;

fn random_graph(r: &mut Rng) -> Graph {
    let n = 1 + r.below(6) as u32;
    let mut g = Graph {
        init: vec![0],
        state_bits: (0..n).map(|_| Bits::from_u64(r.below(1 << STATE_ATOMS))).collect(),
        edges: vec![Vec::new(); n as usize],
    };
    if n > 1 && r.chance(1, 3) {
        g.init.push(1 + r.below(u64::from(n - 1)) as u32);
    }
    for s in 0..n as usize {
        // Stuttering step (usually without action bits).
        let stutter = if r.chance(1, 4) { r.below(1 << ACTION_ATOMS) } else { 0 };
        g.edges[s].push((s as u32, Bits::from_u64(stutter)));
        for _ in 0..r.below(3) {
            let t = r.below(u64::from(n)) as u32;
            g.edges[s].push((t, Bits::from_u64(r.below(1 << ACTION_ATOMS))));
        }
    }
    g
}

fn random_formula(r: &mut Rng, depth: u32) -> Ltl {
    let leaf = depth == 0 || r.chance(1, 4);
    if leaf {
        return match r.below(10) {
            0 => Ltl::True,
            1 => Ltl::False,
            2..=6 => st(r.below(u64::from(STATE_ATOMS)) as u32),
            _ => act(r.below(u64::from(ACTION_ATOMS)) as u32),
        };
    }
    match r.below(8) {
        0 => not(random_formula(r, depth - 1)),
        1 => and(vec![random_formula(r, depth - 1), random_formula(r, depth - 1)]),
        2 => or(vec![random_formula(r, depth - 1), random_formula(r, depth - 1)]),
        3 | 4 => always(random_formula(r, depth - 1)),
        5 | 6 => eventually(random_formula(r, depth - 1)),
        _ => leads_to(random_formula(r, depth - 1), random_formula(r, depth - 1)),
    }
}

fn random_fairness(r: &mut Rng) -> Vec<Fairness> {
    (0..r.below(3))
        .map(|_| Fairness {
            strong: r.chance(1, 2),
            enabled: r.below(u64::from(STATE_ATOMS)) as u32,
            taken: r.below(u64::from(ACTION_ATOMS)) as u32,
        })
        .collect()
}

// Brute-force lasso enumeration is exponential in the bound and takes over
// an hour under Miri even with a handful of cases. `hand.rs` runs the same
// `check_lasso` vs brute-force cross-check exhaustively on small graphs, and
// the two algorithm-agreement tests below still run under Miri.
#[cfg_attr(miri, ignore)]
#[test]
fn agrees_with_brute_force() {
    let mut r = Rng::new(0x9e37_79b9_7f4a_7c15);
    let cases = 5000;
    let (mut violations, mut beyond_bound) = (0, 0);
    for case in 0..cases {
        let g = random_graph(&mut r);
        let prop = random_formula(&mut r, 3);
        let fair = random_fairness(&mut r);
        let got = check_lasso(&g, &prop, &fair);
        let brute = brute_force(&g, &prop, &fair, 7);
        match (&got, &brute) {
            (Ok(()), None) => {}
            (Err(l), _) => {
                if let Some(e) = lasso_error(&g, &prop, &fair, l) {
                    panic!("case {case}: invalid counterexample {l:?}: {e}\n{g:?}\n{prop:?}\n{fair:?}");
                }
                violations += 1;
                if brute.is_none() {
                    beyond_bound += 1;
                }
            }
            (Ok(()), Some(l)) => {
                panic!("case {case}: missed violation {l:?}\n{g:?}\n{prop:?}\n{fair:?}");
            }
        }
    }
    eprintln!("{cases} cases, {violations} violations ({beyond_bound} beyond brute-force bound)");
    assert!(violations > cases / 10 && violations < cases * 9 / 10);
}

/// TLC's algorithm (`check_concrete`) on a graph with one state per node
/// (no VIEW/SYMMETRY) agrees with `check_lasso`.
#[test]
fn tlc_algorithm_agrees_without_view() {
    use tlx_live::{check_concrete, Conc, Event, Expand, Expansion, Lasso, Succ};
    struct Ex<'a>(&'a Graph);
    impl Expand for Ex<'_> {
        type Error = String;
        fn expand(&mut self, from: u32, idx: u32) -> Result<Expansion, String> {
            Ok(expansion(self.0, self.0.edges[from as usize][idx as usize].0))
        }
    }
    fn expansion(g: &Graph, s: u32) -> Expansion {
        let succ = g.edges[s as usize]
            .iter()
            .enumerate()
            .map(|(i, (t, b))| Succ { node: *t, idx: i as u32, bits: g.state_bits[*t as usize].clone(), step: b.clone(), label: i as u32 })
            .collect();
        Expansion { conc: s, bits: g.state_bits[s as usize].clone(), succ }
    }
    let mut r = Rng::new(0x2545_f491_4f6c_dd1d);
    let cases = if cfg!(miri) { 40 } else { 5000 };
    let mut violations = 0;
    for case in 0..cases {
        let mut g = random_graph(&mut r);
        // TLC keeps one of parallel steps; in a state graph they have the
        // same action bits anyway.
        for es in &mut g.edges {
            let mut seen = Vec::new();
            es.retain(|(t, _)| {
                let new = !seen.contains(t);
                seen.push(*t);
                new
            });
        }
        let prop = random_formula(&mut r, 3);
        let fair = random_fairness(&mut r);
        // The events of a BFS from the initial states.
        let mut events: Vec<Event> = Vec::new();
        let mut order: Vec<u32> = Vec::new();
        for &s in &g.init {
            if !order.contains(&s) {
                order.push(s);
                events.push(Event::Init { node: s, conc: s, bits: g.state_bits[s as usize].clone() });
            }
        }
        let mut i = 0;
        while i < order.len() {
            let s = order[i];
            for (t, _) in &g.edges[s as usize] {
                if !order.contains(t) {
                    order.push(*t);
                }
            }
            events.push(Event::Next { node: s, exp: expansion(&g, s) });
            i += 1;
        }
        let want = check_lasso(&g, &prop, &fair);
        let got = check_concrete(&events, &mut Ex(&g), &prop, &fair).expect("no expansion errors");
        match (&want, &got) {
            (Ok(()), Ok(())) => {}
            (Err(_), Err(l)) => {
                violations += 1;
                // The concrete state of each position is the node's state.
                for s in l.prefix.iter().chain(&l.cycle) {
                    let conc = match s.conc {
                        Conc::State(c) => c,
                        Conc::Succ { from, idx } => g.edges[from as usize][idx as usize].0,
                    };
                    assert_eq!(conc, s.node, "case {case}: concrete state of {s:?}");
                }
                let l = Lasso {
                    prefix: l.prefix.iter().map(|s| (s.node, s.label)).collect(),
                    cycle: l.cycle.iter().map(|s| (s.node, s.label)).collect(),
                };
                if let Some(e) = lasso_error(&g, &prop, &fair, &l) {
                    panic!("case {case}: invalid counterexample {l:?}: {e}\n{g:?}\n{prop:?}\n{fair:?}");
                }
            }
            _ => panic!("case {case}: check_lasso {want:?}, TLC algorithm {got:?}\n{g:?}\n{prop:?}\n{fair:?}"),
        }
    }
    eprintln!("{cases} cases, {violations} violations");
    assert!(violations > cases / 10 && violations < cases * 9 / 10);
}

/// The CSR form of a graph with its states renumbered and its bits interned
/// (as the graph recorded during the search, whose states are numbered by
/// the worker that expanded them) gives the same counterexample, renumbered.
#[test]
fn csr_relabeled_agrees() {
    use tlx_live::{check_lasso_csr, Csr};
    let mut r = Rng::new(0x2545_f491_4f6c_dd1d);
    let intern = |pats: &mut Vec<Bits>, b: &Bits| -> u32 {
        let key = format!("{b:?}");
        match pats.iter().position(|p| format!("{p:?}") == key) {
            Some(i) => i as u32,
            None => {
                pats.push(b.clone());
                pats.len() as u32 - 1
            }
        }
    };
    let cases = if cfg!(miri) { 40 } else { 3000 };
    let mut violations = 0;
    for case in 0..cases {
        let g = random_graph(&mut r);
        let prop = random_formula(&mut r, 3);
        let fair = random_fairness(&mut r);
        let n = g.edges.len();
        // A random permutation: state s becomes perm[s].
        let mut perm: Vec<u32> = (0..n as u32).collect();
        for i in (1..n).rev() {
            perm.swap(i, r.below(i as u64 + 1) as usize);
        }
        let mut inv = vec![0usize; n];
        for (s, &p) in perm.iter().enumerate() {
            inv[p as usize] = s;
        }
        let mut c = Csr { init: g.init.iter().map(|&s| perm[s as usize]).collect(), off: vec![0], ..Csr::default() };
        for &s in &inv {
            let sp = intern(&mut c.state_pats, &g.state_bits[s]);
            c.state_pat.push(sp);
            for (t, b) in &g.edges[s] {
                c.tgt.push(perm[*t as usize]);
                let ep = intern(&mut c.action_pats, b);
                c.edge_pat.push(ep);
            }
            c.off.push(c.tgt.len());
        }
        let want = check_lasso(&g, &prop, &fair);
        assert_eq!(check_lasso_csr(&Csr::from_graph(&g), &prop, &fair), want, "case {case}: from_graph");
        let got = check_lasso_csr(&c, &prop, &fair).map_err(|l| {
            let back = |v: Vec<(u32, u32)>| v.into_iter().map(|(s, e)| (inv[s as usize] as u32, e)).collect();
            tlx_live::Lasso { prefix: back(l.prefix), cycle: back(l.cycle) }
        });
        violations += usize::from(want.is_err());
        assert_eq!(got, want, "case {case}\n{g:?}\n{prop:?}\n{fair:?}");
    }
    assert!(violations > cases / 10);
}

/// Exercise recurrence conjunctions deliberately (rare in a generic formula
/// generator): mixed state/action bodies, constants, and both fairness kinds.
#[cfg_attr(miri, ignore)]
#[test]
fn recurrence_conjunctions_agree_with_lasso_enumeration() {
    let mut r = Rng::new(0xa129_f21d_326b_e503);
    for case in 0..500 {
        let g = random_graph(&mut r);
        let fair = random_fairness(&mut r);
        let bodies = vec![and(vec![st(0), not(act(0))]), or(vec![not(st(1)), act(1)]), if case % 5 == 0 { Ltl::True } else { st(2) }];
        let prop = not(and(bodies.into_iter().map(|b| always(eventually(b))).collect()));
        match check_lasso(&g, &prop, &fair) {
            Err(l) => assert!(lasso_error(&g, &prop, &fair, &l).is_none(), "case {case}: {l:?}"),
            Ok(()) => assert!(brute_force(&g, &prop, &fair, 7).is_none(), "case {case}: missed violation"),
        }
    }
}

/// Conjunctions of properties: their negations have independent parts,
/// which several threads check at once with the same result as one, and
/// a valid counterexample.
#[test]
fn parts_on_threads_agree() {
    use tlx_live::{check_lasso_csr_stats, CheckStats, Csr};
    let mut r = Rng::new(0x5851_f42d_4c95_7f2d);
    let cases = if cfg!(miri) { 20 } else { 2000 };
    let (mut violations, mut parted) = (0, 0);
    for case in 0..cases {
        let g = random_graph(&mut r);
        let prop = and((0..3).map(|_| random_formula(&mut r, 3)).collect());
        let fair = random_fairness(&mut r);
        let c = Csr::from_graph(&g);
        let run = |threads| {
            let mut st = CheckStats::default();
            let l = check_lasso_csr_stats(&c, &prop, &fair, threads, &mut |_, _, _| true, &mut st).expect("no memory limit");
            (l, st.parts)
        };
        let (one, parts) = run(1);
        let (three, _) = run(3);
        assert_eq!(one, three, "case {case}\n{g:?}\n{prop:?}\n{fair:?}");
        parted += usize::from(parts > 1);
        if let Err(l) = &one {
            if let Some(e) = lasso_error(&g, &prop, &fair, l) {
                panic!("case {case}: invalid counterexample {l:?}: {e}\n{g:?}\n{prop:?}\n{fair:?}");
            }
            violations += 1;
        }
    }
    eprintln!("{cases} cases, {violations} violations, {parted} with several parts");
    assert!(parted > cases / 10 && violations > cases / 10);
}
