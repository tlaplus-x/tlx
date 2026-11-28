//! Scale smoke test: a large graph must be checked in reasonable time.
//! `TLX_LIVE_SCALE=<states>` overrides the size (default 200_000).

mod common;

use common::*;
use std::time::Instant;
use tlx_live::{check, check_lasso, Bits, Graph, Ltl};

/// A ring of `n` states, each with a stuttering step, a step forward (A) and
/// two pseudo-random jumps (J). State atom 0 = p (every 1000th state),
/// 1 = ENABLED A (everywhere). Action atom 0 = A, 1 = J.
fn ring(n: u32) -> Graph {
    let mut g = Graph { init: vec![0], state_bits: Vec::new(), edges: Vec::with_capacity(n as usize) };
    let mut x = 0x1234_5678_9abc_def0u64;
    for s in 0..n {
        let p = u64::from(s % 1000 == 0);
        g.state_bits.push(Bits::from_u64(p | 0b10));
        let mut es = vec![(s, Bits::new()), ((s + 1) % n, Bits::from_u64(0b01))];
        for _ in 0..2 {
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            es.push(((x % u64::from(n)) as u32, Bits::from_u64(0b10)));
        }
        g.edges.push(es);
    }
    g
}

#[test]
fn large_ring() {
    // Miri runs ~1000x slower; shrink the ring but keep it large enough that
    // the product exploration and SCC handling are exercised.
    let default_n = if cfg!(miri) { 1_000 } else { 200_000 };
    let n = std::env::var("TLX_LIVE_SCALE").ok().and_then(|v| v.parse().ok()).unwrap_or(default_n);
    let g = ring(n);
    let t = Instant::now();
    // Jumps can avoid p forever, so []<>p is violated even under WF(A).
    let prop = always(eventually(st(0)));
    let l = check_lasso(&g, &prop, &[wf(1, 0)]).expect_err("jumps can avoid p");
    assert!(lasso_error(&g, &prop, &[wf(1, 0)], &l).is_none());
    let t1 = t.elapsed();
    // Passing checks explore the whole product.
    let t = Instant::now();
    assert!(check(&g, &leads_to(st(1), st(1)), &[wf(1, 0)]).is_ok());
    // Under WF(A) every behavior takes A infinitely often.
    assert!(check(&g, &always(eventually(act(0))), &[wf(1, 0)]).is_ok());
    let t2 = t.elapsed();
    eprintln!("{n} states: violation {t1:?}, two passing checks {t2:?}");
}

#[test]
fn clock_settles_uses_linear_product() {
    use tlx_live::check_lasso_within;
    for n in [4, 8, 12, 16] {
        let g = graph(&[0], &(0..n).map(|i| 1 << i).collect::<Vec<_>>(), &(0..n).map(|i| (i, (i + 1) % n, 0)).collect::<Vec<_>>(), true);
        let prop = Ltl::Or((0..n).map(|i| eventually(always(st(i)))).collect());
        let mut peak = 0;
        let result = check_lasso_within(&g, &prop, &[], &mut |nodes, _, _| {
            peak = peak.max(nodes);
            nodes <= n as usize * 2
        });
        let lasso = result.expect("recurrence must not build an exponential product").expect_err("clock does not settle");
        assert!(lasso_error(&g, &prop, &[], &lasso).is_none());
        assert!(peak <= n as usize * 2);
    }
}

#[test]
fn budget_can_stop_before_product_construction() {
    use tlx_live::check_lasso_within;
    let g = graph(&[0], &[0], &[], true);
    let prop = Ltl::Or((0..8).map(|i| always(eventually(st(i)))).collect());
    let mut calls = 0;
    let result = check_lasso_within(&g, &prop, &[], &mut |nodes, edges, bytes| {
        calls += 1;
        assert_eq!((nodes, edges), (0, 0), "guard must run before tableau expansion");
        assert!(bytes > 0, "the formula interner is budgeted");
        false
    });
    assert!(result.is_err());
    assert_eq!(calls, 1);
}

#[test]
fn temporary_tableau_branches_are_budgeted() {
    use tlx_live::check_lasso_within;
    let g = graph(&[0], &[0], &[], true);
    // The negation is a conjunction of 16 eventualities (not conditions on
    // the cycle: a tableau of 2^16 states). Stop during partial expansion.
    let prop = or((0..16).map(|i| always(st(i))).collect());
    let mut calls = 0;
    let result = check_lasso_within(&g, &prop, &[], &mut |nodes, edges, bytes| {
        calls += 1;
        assert_eq!((nodes, edges), (0, 0));
        bytes < 128 * 1024
    });
    assert!(result.is_err());
    assert!(calls > 1);
}

#[test]
fn waiting_states_are_not_built() {
    use tlx_live::check_lasso_within;
    // A ring of n states with atoms p_i (state % 100 == i) and q_i (state
    // % 100 not in i..i + 5) for 8 properties p_i ~> q_i: their negations
    // each wait in a state without literals, which would copy the ring 8
    // times (16 with the nested `<>` of `~>` under `[]`). Miri keeps four
    // 100-state period cycles.
    let n = if cfg!(miri) { 400u32 } else { 20_000u32 };
    let k = 8;
    let states: Vec<u64> = (0..n)
        .map(|s| {
            (0..k).fold(0, |b, i| b | (u64::from(s % 100 == i) << (2 * i)) | (u64::from(!(i..i + 5).contains(&(s % 100))) << (2 * i + 1)))
        })
        .collect();
    let edges: Vec<(u32, u32, u64)> = (0..n).map(|s| (s, (s + 1) % n, 1)).collect();
    let g = graph(&[0], &states, &edges, true);
    let prop = and((0..k).map(|i| always(leads_to(st(2 * i), st(2 * i + 1)))).collect());
    // The ring always moves on (WF of action 0): every q_i comes.
    let fair = [wf(2 * k, 0)];
    let g = {
        let mut g = g;
        for b in &mut g.state_bits {
            b.set(2 * k, true);
        }
        g
    };
    let mut peak = 0;
    let r = check_lasso_within(&g, &prop, &fair, &mut |nodes, _, _| {
        peak = peak.max(nodes);
        true
    });
    assert!(matches!(r, Ok(Ok(()))));
    // Only the states where some p_i holds and q_i does not yet (the
    // entries), and then until q_i (the commitments): far fewer than n.
    assert!(peak < n as usize, "{peak} product nodes for {n} states");
    // Without fairness the ring may stutter where q_i fails: a violation.
    let l = tlx_live::check_lasso(&g, &prop, &[]).expect_err("stuttering before q_i");
    assert!(lasso_error(&g, &prop, &[], &l).is_none());
}

#[test]
fn parts_over_the_budget_together_run_one_at_a_time() {
    use tlx_live::{check_lasso_csr_stats, CheckStats, Csr};
    // 8 properties p_i ~> q_i on a ring (as above), without fairness: a
    // violation in every part. Miri keeps four 100-state period cycles.
    let n = if cfg!(miri) { 400u32 } else { 20_000u32 };
    let k = 8u32;
    let states: Vec<u64> = (0..n)
        .map(|s| {
            (0..k).fold(0, |b, i| b | (u64::from(s % 100 == i) << (2 * i)) | (u64::from(!(i..i + 50).contains(&(s % 100))) << (2 * i + 1)))
        })
        .collect();
    let edges: Vec<(u32, u32, u64)> = (0..n).map(|s| (s, (s + 1) % n, 1)).collect();
    let c = Csr::from_graph(&graph(&[0], &states, &edges, true));
    let prop = and((0..k).map(|i| always(leads_to(st(2 * i), st(2 * i + 1)))).collect());
    let run = |threads, limit: usize| {
        let (mut st, mut peak, mut refused) = (CheckStats::default(), 0, false);
        let r = check_lasso_csr_stats(
            &c,
            &prop,
            &[],
            threads,
            &mut |_, _, bytes| {
                peak = peak.max(bytes);
                refused |= bytes > limit;
                bytes <= limit
            },
            &mut st,
        );
        (r, peak, st.parts, refused)
    };
    let (one, peak, parts, _) = run(1, usize::MAX);
    assert_eq!(parts, k as usize);
    let one = one.expect("no limit");
    assert!(one.is_err());
    // A budget for one part at a time, not for eight.
    // (Whether the parts run at the same time depends on the scheduling:
    // the result must not.)
    let (eight, _, _, refused) = run(8, peak + peak / 2);
    eprintln!("8 threads over the budget together: {refused}");
    assert_eq!(eight.expect("one part at a time fits"), one);
    // A budget for none.
    assert!(run(8, peak / 2).0.is_err());
}

#[test]
fn persistence_assumptions_need_no_tableau() {
    use tlx_live::check_lasso_within;
    // `<>[][A_i]_v` assumptions of a specification (one per process) under
    // a property `[]<>p`: the negation is a conjunction of 21 `<>[]`
    // obligations, 2^21 tableau states as one formula. On a ring where
    // A_i (action atom i) is every step but the one out of state i, and
    // stuttering: a behavior with only A_i steps eventually, for every i,
    // ends stuttering; p holds only at state 0.
    let n = 1000u32;
    let k = 20u32;
    let states: Vec<u64> = (0..n).map(|s| u64::from(s == 0)).collect();
    let edges: Vec<(u32, u32, u64)> = (0..n).map(|s| (s, (s + 1) % n, ((1u64 << k) - 1) & !(1 << s.min(63)))).collect();
    let mut g = graph(&[0], &states, &edges, true);
    // Stuttering steps are A_i steps ([A_i]_v).
    for (s, es) in g.edges.iter_mut().enumerate() {
        es.last_mut().expect("stuttering step").1 = Bits::from_u64((1 << k) - 1);
        assert_eq!(es.last().unwrap().0, s as u32);
    }
    let assumptions = and((0..k).map(|i| eventually(always(act(i)))).collect());
    let prop = or(vec![not(assumptions), always(eventually(st(0)))]);
    let mut peak = 0;
    let r = check_lasso_within(&g, &prop, &[], &mut |nodes, _, _| {
        peak = peak.max(nodes);
        true
    });
    // Stuttering at state 1 forever satisfies every assumption, not p.
    let l = r.expect("small").expect_err("stuttering away from 0");
    assert!(lasso_error(&g, &prop, &[], &l).is_none());
    assert!(peak <= n as usize, "{peak} product nodes for {n} states");
}

#[test]
fn nested_tail_conditions_and_strong_fairness_startup_scale_linearly() {
    use tlx_live::{
        branches, check_lasso_csr_stats, check_size, reports_early, tableau_initial_checks, tableau_state_atoms, CheckStats, Csr,
    };
    // `[]( \E k \in 0..16 : s_k => <>[]r_k )` (`bcastFolklore`'s ReliableChan
    // pattern scaled to k = 16): without hoisting `[]<>~r_k` out of `<>`, the
    // negation `<>( /\ (s_k /\ []<>~r_k) )` builds >= 2^16 tableau states.
    // Miri scales the ring and the startup metadata workload; the same
    // helpers and shapes are exercised at a fraction of the size.
    let n = if cfg!(miri) { 100u32 } else { 1000u32 };
    let k = 16u32;
    let all_s = (1u64 << k) - 1;
    // State 0 sets all s_k; subsequent states cycle through clearing one r_k at
    // a time so every []<>~r_k holds on the cycle after leaving state 0.
    let states: Vec<u64> = (0..n)
        .map(|s| {
            let s_bits = if s == 0 { all_s } else { 0 };
            let r_clear = (s as u64) % u64::from(k);
            let r_bits = ((all_s) & !(1u64 << r_clear)) << k;
            s_bits | r_bits
        })
        .collect();
    let edges: Vec<(u32, u32, u64)> = (0..n).map(|s| (s, (s + 1) % n, 1)).collect();
    let g = graph(&[0], &states, &edges, true);
    let csr = Csr::from_graph(&g);
    let prop = always(or((0..k).map(|i| or(vec![not(st(i)), eventually(always(st(k + i)))])).collect()));
    let mut stats = CheckStats::default();
    let mut peak_bytes = 0usize;
    let res = check_lasso_csr_stats(
        &csr,
        &prop,
        &[wf(0, 0)],
        1,
        &mut |_, _, bytes| {
            peak_bytes = peak_bytes.max(bytes);
            true
        },
        &mut stats,
    )
    .expect("fits");
    let lasso = res.expect_err("every r_k fails infinitely often after state 0");
    assert!(lasso_error(&g, &prop, &[wf(0, 0)], &lasso).is_none());
    assert_eq!(stats.tableau_states, 3, "entry, waiting state, and accepting sink");
    assert_eq!(stats.waiting_states, 1);
    assert!(stats.product_nodes <= n as usize * 2);
    // Compacted `aq` (u8), `gedge` (u8), and level-span distances keep the
    // 1000-node, 2000-edge product well below 128 KiB.
    assert!(peak_bytes < 128 * 1024, "peak product bytes = {peak_bytes}");

    // Startup metadata helpers on 24 strong fairness constraints and 20-way
    // `([]<> \/ <>[])` conjunctions must not materialize 2^24 / 2^20 DNF rows.
    let many_sf: Vec<_> = (0..24).map(|i| sf(i, i)).collect();
    let t0 = Instant::now();
    assert!(check_size(&eventually(st(0)), &many_sf).is_ok());
    assert_eq!(tableau_state_atoms(&eventually(st(0)), &many_sf), vec![0]);
    assert_eq!(tableau_initial_checks(&eventually(st(0)), &many_sf), vec![vec![(0, false)]]);
    assert!(!reports_early(&always(or(vec![not(st(0)), always(st(1))])), &many_sf));

    let pem_conj = or((0..20).map(|i| and(vec![always(eventually(st(2 * i))), eventually(always(st(2 * i + 1)))])).collect());
    assert!(check_size(&pem_conj, &[]).is_ok());
    assert!(tableau_state_atoms(&pem_conj, &[]).is_empty());
    assert!(tableau_initial_checks(&pem_conj, &[]).is_empty());
    assert!(!reports_early(&pem_conj, &[]));
    assert_eq!(branches([&pem_conj]), 1);

    // 13 binary choices (8,192 distinct rows) must deduplicate in O(rows), not O(rows^2).
    // Miri checks 7 choices (128 rows); it cannot afford 8,192.
    let bin_k = if cfg!(miri) { 7 } else { 13 };
    let bin = or((0..bin_k).map(|i| and(vec![always(st(2 * i)), always(st(2 * i + 1))])).collect());
    assert_eq!(tableau_state_atoms(&bin, &[]).len(), 2 * bin_k as usize);
    assert_eq!(branches([&bin]), 1 << bin_k);
    // A wall-clock bound measures native performance; interpreter overhead
    // must not be mistaken for a regression.
    #[cfg(not(miri))]
    assert!(t0.elapsed().as_secs_f64() < 1.0, "startup metadata took {:?}", t0.elapsed());
}

#[test]
#[cfg_attr(miri, ignore)]
fn sparse_part_avoids_eager_dense_allocation() {
    use tlx_live::{check_lasso_csr_stats, CheckStats, Csr, Ids, Offsets};
    // A 1,000,000-state connected ring where atom 3 holds only on states
    // 0..200 (< 0.02% density). Negation of the property is
    // `st(0) /\ <>st(1) /\ <>st(2) /\ []st(3)`: no waiting states (so GraphBfs
    // is not built), >= 4 tableau states in one accepting part (`n * q >= 4M`,
    // which would eagerly allocate and pre-charge >= 16 MiB as Dense), while
    // only a few hundred product nodes are reachable.
    let n = 1_000_000usize;
    let active = 200usize;
    let mut off = Vec::with_capacity(n + 1);
    let mut tgt = Vec::with_capacity(2 * n);
    for s in 0..n {
        off.push(tgt.len() as u32);
        tgt.push(((s + 1) % n) as u32);
        tgt.push(s as u32); // stuttering self-loop
    }
    off.push(tgt.len() as u32);
    // Pattern 0: none; 1: st(3); 2: st(0)|st(3); 3: st(1)|st(3); 4: st(2)|st(3).
    let mut state_pat = vec![0u32; n];
    for pat in &mut state_pat[..active] {
        *pat = 1;
    }
    state_pat[0] = 2;
    state_pat[50] = 3;
    state_pat[100] = 4;
    let csr = Csr {
        init: vec![0],
        off: Offsets::U32(off),
        tgt,
        edge_pat: Ids::U8(vec![0; 2 * n]),
        state_pat,
        state_pats: vec![
            Bits::new(),
            Bits::from_u64(1 << 3),
            Bits::from_u64((1 << 0) | (1 << 3)),
            Bits::from_u64((1 << 1) | (1 << 3)),
            Bits::from_u64((1 << 2) | (1 << 3)),
        ],
        action_pats: vec![Bits::new()],
    };
    let prop = or(vec![not(st(0)), always(not(st(1))), always(not(st(2))), eventually(not(st(3)))]);

    // Budget is 256 KiB — 64x smaller than the 16+ MiB dense table.
    let limit = 256 * 1024;
    let mut peak_bytes = 0usize;
    let mut stats = CheckStats::default();
    let res = check_lasso_csr_stats(
        &csr,
        &prop,
        &[],
        1,
        &mut |_, _, bytes| {
            peak_bytes = peak_bytes.max(bytes);
            bytes <= limit
        },
        &mut stats,
    )
    .expect("sparse part must fit well below dense table size");
    assert_eq!(stats.waiting_states, 0, "no GraphBfs so within isolates Product + NodeMap");
    assert!(stats.tableau_states >= 4, "expected >= 4 tableau states, got {}", stats.tableau_states);
    assert!(stats.product_nodes > 0 && stats.product_nodes < 1_000, "sparse product: {} nodes", stats.product_nodes);
    assert!(peak_bytes <= limit, "peak_bytes {peak_bytes} exceeded {limit}");
    let lasso = res.expect_err("path 0 -> 50 -> 100 stuttering at 100 violates prop");
    assert!(!lasso.cycle.is_empty());
    assert_eq!(lasso.prefix.first().map(|&(s, _)| s), Some(0));

    // Removing st(2) makes the property hold with the same sparse footprint.
    let mut holding = csr;
    holding.state_pat[100] = 1;
    let mut hold_peak = 0usize;
    let hold_res = check_lasso_csr_stats(
        &holding,
        &prop,
        &[],
        1,
        &mut |_, _, bytes| {
            hold_peak = hold_peak.max(bytes);
            bytes <= limit
        },
        &mut CheckStats::default(),
    )
    .expect("holding sparse part fits in tight budget");
    assert!(hold_res.is_ok());
    assert!(hold_peak <= limit, "hold_peak {hold_peak} exceeded {limit}");
}

#[test]
#[cfg_attr(miri, ignore)]
fn dense_promotion_and_budget_declined_sparse_fallback() {
    use tlx_live::{check_lasso_csr_stats, CheckStats, Csr, Ids, Offsets};
    // Two independent non-waiting 1-state parts (`¬prop = []st(0) \/ []st(1)`)
    // on a 200,000-state ring where 15,500 states satisfy `st(0)` and `st(1)`:
    // `n * q = 200_000 > EAGER_DENSE_LIMIT` (`dense_bytes = 800,000 B`).
    // Reaching 14,337 nodes crosses the promotion threshold (`sparse = 213 KB`,
    // transient `sparse + dense = 1,013 KB`), whereas declining promotion
    // finishes all 15,500 nodes in `Sparse` (`cap = 28,672`, `426 KB`) inside
    // the same `16,384`-slot node vectors.
    let n = 200_000usize;
    let active = 15_500usize;
    let mut off = Vec::with_capacity(n + 1);
    let mut tgt = Vec::with_capacity(2 * n);
    for s in 0..n {
        off.push(tgt.len() as u32);
        tgt.push(((s + 1) % n) as u32);
        tgt.push(s as u32);
    }
    off.push(tgt.len() as u32);
    let mut state_pat = vec![0u32; n];
    for pat in &mut state_pat[..active] {
        *pat = 1;
    }
    let csr = Csr {
        init: vec![0],
        off: Offsets::U32(off),
        tgt,
        edge_pat: Ids::U8(vec![0; 2 * n]),
        state_pat,
        state_pats: vec![Bits::new(), Bits::from_u64(0b11)],
        action_pats: vec![Bits::new()],
    };
    let prop = and(vec![eventually(not(st(0))), eventually(not(st(1)))]);

    // Unlimited budget: promotes to Dense and reports peak including transient
    // `sparse + dense`.
    let mut dense_peak = 0usize;
    let mut dense_stats = CheckStats::default();
    let expected = check_lasso_csr_stats(
        &csr,
        &prop,
        &[],
        1,
        &mut |_, _, bytes| {
            dense_peak = dense_peak.max(bytes);
            true
        },
        &mut dense_stats,
    )
    .expect("unlimited")
    .expect_err("stuttering inside active prefix violates prop");
    assert_eq!(dense_stats.waiting_states, 0);
    assert_eq!(dense_stats.tableau_states, 2);
    assert_eq!(dense_stats.parts, 2);
    assert!(dense_peak > n * 4, "expected promotion peak above dense table size ({}), got {dense_peak}", n * 4);

    // Serial tight budget: below the transient `sparse + dense` promotion peak,
    // above the final `Sparse` footprint. Promotion is declined cleanly and
    // produces the exact same counterexample.
    let tight = dense_peak - 300 * 1024;
    let mut declined = false;
    let mut sparse_peak = 0usize;
    let got_serial = check_lasso_csr_stats(
        &csr,
        &prop,
        &[],
        1,
        &mut |_, _, bytes| {
            if bytes <= tight {
                sparse_peak = sparse_peak.max(bytes);
                true
            } else {
                declined = true;
                false
            }
        },
        &mut CheckStats::default(),
    )
    .expect("declining dense promotion must allow sparse completion")
    .expect_err("same counterexample");
    assert!(declined, "tight budget {tight} must refuse dense promotion peak {dense_peak}");
    assert!(sparse_peak < dense_peak, "sparse peak {sparse_peak} should be below dense promotion peak {dense_peak}");
    assert_eq!(got_serial, expected);

    // Parallel execution with two parts: budget fits both parts in Sparse
    // concurrently and refuses concurrent promotion peaks without poisoning
    // sibling workers.
    for limit in [tight, sparse_peak * 2 + 128 * 1024] {
        let got_par = check_lasso_csr_stats(&csr, &prop, &[], 2, &mut |_, _, bytes| bytes <= limit, &mut CheckStats::default())
            .expect("parallel sparse completion under tight budget")
            .expect_err("same counterexample");
        assert_eq!(got_par, expected);
    }
}

#[test]
#[cfg_attr(miri, ignore)]
fn high_outdegree_product_checks_budget_during_insertion() {
    use tlx_live::{check_lasso_csr_within, Csr, Ids, Offsets};
    // State 0 fans out directly to 100,000 distinct states (> GUARD_EVERY =
    // 65,536). Even while expanding `v == 0`, `Product::build` must consult
    // `within` when inserted `p.st.len()` crosses `GUARD_EVERY`.
    let fanout = 100_000usize;
    let n = fanout + 1;
    let mut off = Vec::with_capacity(n + 1);
    let mut tgt = Vec::with_capacity(2 * n);
    off.push(0);
    for t in 1..=fanout {
        tgt.push(t as u32);
    }
    tgt.push(0); // stuttering self-loop on state 0
    for s in 1..n {
        off.push(tgt.len() as u32);
        tgt.push(s as u32);
    }
    off.push(tgt.len() as u32);
    let csr = Csr {
        init: vec![0],
        off: Offsets::U32(off),
        tgt,
        edge_pat: Ids::U8(vec![0; 2 * n]),
        state_pat: vec![0; n],
        state_pats: vec![Bits::new()],
        action_pats: vec![Bits::new()],
    };
    let prop = eventually(st(0)); // ¬prop = []~st(0): 1 non-waiting accepting state
    let mut max_seen_nodes = 0usize;
    let res = check_lasso_csr_within(&csr, &prop, &[], &mut |nodes, _, _| {
        max_seen_nodes = max_seen_nodes.max(nodes);
        nodes < 65_536
    });
    assert!(res.is_err(), "budget must stop during state 0 fanout");
    assert_eq!(max_seen_nodes, 65_536, "guard must trigger at GUARD_EVERY inserted nodes, not after all {fanout}");
}
