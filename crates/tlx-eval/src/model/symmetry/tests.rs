use tlx_base::partition::Partition;

use super::factor::lex_permutations;
use super::*;

fn s3_perms(atoms: &[Sym; 3]) -> Vec<Perm> {
    let mut perms = Vec::new();
    for a in 0..3 {
        for b in 0..3 {
            if a == b {
                continue;
            }
            let c = 3 - a - b;
            let img = [a, b, c];
            if img == [0, 1, 2] {
                continue;
            }
            perms.push(
                atoms.iter().enumerate().filter_map(|(i, &s)| (i != img[i]).then_some((s, Value::ModelValue(atoms[img[i]])))).collect(),
            );
        }
    }
    perms
}

fn adjacent_transpositions(atoms: &[Sym]) -> Vec<Perm> {
    atoms.windows(2).map(|w| HashMap::from([(w[0], Value::ModelValue(w[1])), (w[1], Value::ModelValue(w[0]))])).collect()
}

fn explicit_group() -> (Group, [Sym; 3]) {
    let atoms = [Sym::new("bag_a"), Sym::new("bag_b"), Sym::new("bag_c")];
    (Group::explicit(s3_perms(&atoms)), atoms)
}

fn factorized_group() -> (Group, [Sym; 3]) {
    let atoms = [Sym::new("bag_a"), Sym::new("bag_b"), Sym::new("bag_c")];
    let g = Group::from_generators(adjacent_transpositions(&atoms)).unwrap();
    assert!(matches!(g.kind, GroupKind::Factorized(_)));
    (g, atoms)
}

fn bag(atoms: &[Sym; 3]) -> Value {
    let field = Sym::new("src");
    Value::fcn_from_pairs(vec![
        (Value::record(vec![(field, Value::ModelValue(atoms[0]))]), Value::Int(1)),
        (Value::record(vec![(field, Value::ModelValue(atoms[1]))]), Value::Int(1)),
    ])
    .unwrap()
}

fn apply_chosen(p: Option<ChosenPerm<'_>>, vals: &[Value]) -> Vec<Value> {
    match p {
        None => vals.to_vec(),
        Some(p) => vals.iter().map(|v| p.apply(v).unwrap().unwrap_or_else(|| v.clone())).collect(),
    }
}

fn brute_image(perms: &[FastPerm], vals: &[Value], order: &[usize]) -> EResult<Vec<Value>> {
    let mut best = vals.to_vec();
    for p in perms {
        let image: Vec<_> = vals.iter().map(|v| Ok(p.apply(v)?.unwrap_or_else(|| v.clone()))).collect::<EResult<_>>()?;
        let mut cmp = Ordering::Equal;
        for &j in order {
            cmp = cmp_tlc(&image[j], &best[j])?;
            if cmp != Ordering::Equal {
                break;
            }
        }
        if cmp == Ordering::Less {
            best = image;
        }
    }
    Ok(best)
}

fn brute_total_image(perms: &[FastPerm], val: &Value) -> EResult<Value> {
    let mut best = val.clone();
    for p in perms {
        let image = p.apply(val)?.unwrap_or_else(|| val.clone());
        if try_total_cmp(&image, &best)?.is_lt() {
            best = image;
        }
    }
    Ok(best)
}

fn brute_index(g: &Group, vals: &[Value], order: &[usize]) -> Option<usize> {
    let GroupKind::Explicit { perms, .. } = &g.kind else { unreachable!() };
    let mut best = vals.to_vec();
    let mut pi = None;
    for (i, p) in perms.iter().enumerate() {
        let image: Vec<_> = vals.iter().map(|v| p.apply(v).unwrap().unwrap_or_else(|| v.clone())).collect();
        let mut cmp = Ordering::Equal;
        for &j in order {
            cmp = cmp_tlc(&image[j], &best[j]).unwrap();
            if cmp != Ordering::Equal {
                break;
            }
        }
        if cmp == Ordering::Less {
            best = image;
            pi = Some(i);
        }
    }
    pi
}

#[test]
fn record_bag_candidates_keep_later_variable_ties() {
    let (g, atoms) = explicit_group();
    let net = bag(&atoms);
    for tail in atoms {
        let vals = [net.clone(), Value::ModelValue(tail)];
        assert_eq!(g.least_perm_index(&mut StateVals::Given(&vals), &[0, 1], true).unwrap(), brute_index(&g, &vals, &[0, 1]));
    }
    let (mut other, _) = explicit_group();
    if let GroupKind::Explicit { perms, raw, .. } = &mut other.kind {
        perms.reverse();
        raw.reverse();
    }
    let vals = [net, Value::ModelValue(atoms[1])];
    assert_eq!(other.least_perm_index(&mut StateVals::Given(&vals), &[0, 1], true).unwrap(), brute_index(&other, &vals, &[0, 1]));
}

#[test]
fn record_bag_candidates_match_full_images() {
    let (g, atoms) = explicit_group();
    let (fg, _) = factorized_group();
    let GroupKind::Explicit { perms, .. } = &g.kind else { unreachable!() };
    let mut keys = Vec::new();
    for &src in &atoms {
        for &dst in &atoms {
            if src != dst {
                keys.push(Value::record(vec![
                    (Sym::new("src"), Value::ModelValue(src)),
                    (Sym::new("dst"), Value::ModelValue(dst)),
                    (Sym::new("payload"), Value::tuple(vec![Value::Int(2), Value::ModelValue(src)])),
                ]));
            }
        }
    }
    for mask in 0..1usize << keys.len() {
        let bag = Value::fcn_from_pairs(
            keys.iter()
                .enumerate()
                .filter_map(|(i, k)| (mask & (1 << i) != 0).then_some((k.clone(), Value::Int((i % 3) as i64))))
                .collect(),
        )
        .unwrap();
        for &tail in &atoms {
            let vals = [bag.clone(), Value::ModelValue(tail), Value::Int(1)];
            for order in [[0, 1, 2], [2, 0, 1], [1, 0, 2]] {
                assert_eq!(
                    g.least_perm_index(&mut StateVals::Given(&vals), &order, true).unwrap(),
                    brute_index(&g, &vals, &order),
                    "explicit mask={mask}, order={order:?}"
                );
                let want = brute_image(perms, &vals, &order).unwrap();
                let got_noview = apply_chosen(fg.least_perm(&mut StateVals::Given(&vals), &order).unwrap(), &vals);
                let got_view = apply_chosen(fg.least_view_perm(&mut StateVals::Given(&vals), &order).unwrap(), &vals);
                assert_eq!(got_noview, want, "factorized no-view mask={mask}, order={order:?}");
                assert_eq!(got_view, want, "factorized view mask={mask}, order={order:?}");
            }
        }
    }
}

#[test]
fn nonidentity_bag_minima_are_decided_by_the_second_variable() {
    let (g, atoms) = explicit_group();
    let GroupKind::Explicit { perms, .. } = &g.kind else { unreachable!() };
    let net = bag(&[atoms[1], atoms[2], atoms[0]]);
    let candidates = BagCache::default().explicit_candidates(g.id, perms, &net).unwrap();
    assert_eq!(candidates.len(), 2);
    assert!(candidates.iter().all(Option::is_some), "identity must lose on the first variable");
    let mut winners = Vec::new();
    for tail in [atoms[1], atoms[2]] {
        let all = Value::set_from(atoms.iter().copied().map(Value::ModelValue).collect()).unwrap();
        let vals = [net.clone(), Value::ModelValue(tail), all];
        let expected = brute_index(&g, &vals, &[0, 1, 2]);
        assert!(expected.is_some());
        assert_eq!(g.least_perm_index(&mut StateVals::Given(&vals), &[0, 1, 2], true).unwrap(), expected);
        winners.push(expected);
    }
    assert_ne!(winners[0], winners[1], "the second variable must break the first-variable tie");
}

#[test]
fn incomparable_bag_keys_report_the_original_comparison_error() {
    let (g, atoms) = explicit_group();
    let (fg, _) = factorized_group();
    let rec = |v| Value::record(vec![(Sym::new("src"), v)]);
    for (i, pairs) in [
        vec![(Value::Int(1), Value::Int(0)), (rec(Value::ModelValue(atoms[0])), Value::Int(0))],
        vec![(rec(Value::Int(1)), Value::Int(0)), (rec(Value::Bool(true)), Value::Int(0))],
    ]
    .into_iter()
    .enumerate()
    {
        let bag = Value::Fcn(pairs.into(), tlx_value::FcnDom::Enumerated);
        let vals = [bag, Value::set_from(atoms.iter().copied().map(Value::ModelValue).collect()).unwrap()];
        let old = g.least_perm_index(&mut StateVals::Given(&vals), &[0, 1], false).unwrap_err();
        let cached = g.least_perm_index(&mut StateVals::Given(&vals), &[0, 1], true).unwrap_err();
        assert_eq!(cached.message, old.message);
        assert_eq!(cached.kind, old.kind);
        if i == 0 {
            let fact_old = fg.least_perm(&mut StateVals::Given(&vals), &[0, 1]).err().expect("factorized must error");
            let fact_cached = fg.least_view_perm(&mut StateVals::Given(&vals), &[0, 1]).err().expect("factorized view must error");
            assert_eq!(fact_old.kind, old.kind);
            assert_eq!(fact_cached.kind, old.kind);
            assert!(fact_old.message.contains("with non-record\n1"), "unexpected: {}", fact_old.message);
            assert_eq!(fact_cached.message, fact_old.message);
        } else {
            assert!(fg.least_perm(&mut StateVals::Given(&vals), &[0, 1]).unwrap().is_none());
            assert!(fg.least_view_perm(&mut StateVals::Given(&vals), &[0, 1]).unwrap().is_none());
        }
    }
    let no_atoms = [Value::Fcn(
        vec![(rec(Value::Int(1)), Value::Int(0)), (rec(Value::Bool(true)), Value::Int(0))].into(),
        tlx_value::FcnDom::Enumerated,
    )];
    assert!(g.least_perm(&mut StateVals::Given(&no_atoms), &[0]).unwrap().is_none());
    assert!(g.least_view_perm(&mut StateVals::Given(&no_atoms), &[0]).unwrap().is_none());
    assert!(fg.least_perm(&mut StateVals::Given(&no_atoms), &[0]).unwrap().is_none());
    assert!(fg.least_view_perm(&mut StateVals::Given(&no_atoms), &[0]).unwrap().is_none());
}

#[test]
fn symmetry_without_view_keeps_the_uncached_comparison_path() {
    let (g, atoms) = explicit_group();
    let vals = [bag(&atoms), Value::ModelValue(atoms[0])];
    CMP_CALLS.with(|n| n.set(0));
    g.least_perm(&mut StateVals::Given(&vals), &[0, 1]).unwrap();
    let cold = CMP_CALLS.with(|n| n.replace(0));
    g.least_perm(&mut StateVals::Given(&vals), &[0, 1]).unwrap();
    let warm = CMP_CALLS.with(|n| n.get());
    assert_eq!(warm, cold, "without VIEW, bag comparison must stay uncached");
}

#[test]
fn record_bag_comparison_errors_match_the_original_walk() {
    let (g, atoms) = explicit_group();
    let (fg, _) = factorized_group();
    let all = Value::set_from(atoms.iter().copied().map(Value::ModelValue).collect()).unwrap();
    let choices =
        [Value::Bool(false), Value::Bool(true), Value::Int(0), Value::Int(1), Value::tuple(vec![]), Value::tuple(vec![Value::Int(0)])];
    for mask in 1..64u32 {
        let mut pairs = Vec::new();
        let mut bit = 0;
        for &src in &atoms {
            for &dst in &atoms {
                if src == dst {
                    continue;
                }
                if mask & (1 << bit) != 0 {
                    pairs.push((
                        Value::record(vec![(Sym::new("src"), Value::ModelValue(src)), (Sym::new("dst"), Value::ModelValue(dst))]),
                        Value::Int(1),
                    ));
                }
                bit += 1;
            }
        }
        let net = Value::fcn_from_pairs(pairs).unwrap();
        for a in &choices {
            for b in &choices {
                for c in &choices {
                    let tail = Value::fcn_from_pairs(
                        atoms.into_iter().zip([a.clone(), b.clone(), c.clone()]).map(|(k, v)| (Value::ModelValue(k), v)).collect(),
                    )
                    .unwrap();
                    let vals = [net.clone(), tail, all.clone()];
                    let old = g.least_perm_index(&mut StateVals::Given(&vals), &[0, 1, 2], false);
                    let cached = g.least_perm_index(&mut StateVals::Given(&vals), &[0, 1, 2], true);
                    assert_eq!(old.is_err(), cached.is_err(), "mask={mask}, vals={vals:?}, old={old:?}, cached={cached:?}");
                    let f_old = fg.least_perm(&mut StateVals::Given(&vals), &[0, 1, 2]);
                    let f_cached = fg.least_view_perm(&mut StateVals::Given(&vals), &[0, 1, 2]);
                    assert_eq!(f_old.is_err(), old.is_err(), "factorized mask={mask}, vals={vals:?}");
                    assert_eq!(f_cached.is_err(), old.is_err(), "factorized view mask={mask}, vals={vals:?}");
                    if let Ok(oi) = old {
                        let GroupKind::Explicit { perms, .. } = &g.kind else { unreachable!() };
                        let want = apply_chosen(oi.map(|i| ChosenPerm::borrowed(&perms[i])), &vals);
                        assert_eq!(apply_chosen(f_old.unwrap(), &vals), want, "mask={mask}");
                        assert_eq!(apply_chosen(f_cached.unwrap(), &vals), want, "view mask={mask}");
                    }
                }
            }
        }
    }
}

#[test]
fn repeated_record_bag_reuses_permutation_comparisons() {
    let (g, atoms) = explicit_group();
    let (fg, _) = factorized_group();
    let net = bag(&atoms);
    let all = Value::set_from(atoms.iter().copied().map(Value::ModelValue).collect()).unwrap();
    let vals = [net.clone(), Value::ModelValue(atoms[0]), all.clone()];
    CMP_CALLS.with(|n| n.set(0));
    g.least_view_perm(&mut StateVals::Given(&vals), &[0, 1, 2]).unwrap();
    let cold = CMP_CALLS.with(|n| n.replace(0));
    let vals2 = [net.clone(), Value::ModelValue(atoms[1]), all.clone()];
    assert_eq!(g.least_perm_index(&mut StateVals::Given(&vals2), &[0, 1, 2], true).unwrap(), brute_index(&g, &vals2, &[0, 1, 2]));
    let warm = CMP_CALLS.with(|n| n.get());
    assert!(warm * 3 < cold, "repeated bag comparisons (explicit): cold={cold}, warm={warm}");

    CMP_CALLS.with(|n| n.set(0));
    fg.least_view_perm(&mut StateVals::Given(&vals), &[0, 1, 2]).unwrap();
    let f_cold = CMP_CALLS.with(|n| n.replace(0));
    fg.least_view_perm(&mut StateVals::Given(&vals2), &[0, 1, 2]).unwrap();
    let f_warm = CMP_CALLS.with(|n| n.get());
    assert!(f_warm * 3 < f_cold, "repeated bag comparisons (factorized): cold={f_cold}, warm={f_warm}");
}

#[test]
fn factorized_rank_matches_materialized_symmetry_maps() {
    let a = [Sym::new("rk_a0"), Sym::new("rk_a1"), Sym::new("rk_a2")];
    let b = [Sym::new("rk_b0"), Sym::new("rk_b1")];
    let mut gens = adjacent_transpositions(&a);
    gens.extend(adjacent_transpositions(&b));
    let g = Group::from_generators(gens).unwrap();
    let GroupKind::Factorized(fg) = &g.kind else { panic!("expected factorized group") };
    let maps = g.symmetry_maps();
    assert_eq!(maps.len(), 3 * 2 * 2 - 1);
    let n0 = fg.factors[0].keys.len();
    let n1 = fg.factors[1].keys.len();
    let pin_factor = |part: &mut Partition, g: usize, perm: &[u16]| {
        let off = fg.factors[g].offset;
        for (k, &t) in perm.iter().enumerate() {
            let p = part.pos_of()[off + k] as usize;
            let lo = part.block_lo()[off + p] as usize;
            let hi = part.block_hi()[off + p] as usize;
            let slot_pos = (lo..hi).find(|&q| part.tgt()[off + q] == t).expect("target in block");
            part.pin_to_slot(fg, g, k, slot_pos);
        }
    };
    for p0 in lex_permutations(n0) {
        for p1 in lex_permutations(n1) {
            let mut part = Partition::default();
            part.reset(fg);
            pin_factor(&mut part, 0, &p0);
            pin_factor(&mut part, 1, &p1);
            assert!(part.is_complete());
            let rank = fg.rank_of(&part);
            let is_id = p0.iter().enumerate().all(|(i, &t)| t as usize == i) && p1.iter().enumerate().all(|(i, &t)| t as usize == i);
            if is_id {
                assert_eq!(rank, None);
            } else {
                let r = rank.expect("non-identity rank");
                let fp = fg.to_fast_perm(&part);
                let expected = FastPerm::new(&maps[r]);
                for &s in a.iter().chain(b.iter()) {
                    assert_eq!(fp.get(s), expected.get(s), "rank={r}, sym={s:?}");
                }
            }
        }
    }
}

#[test]
fn non_full_subgroups_fall_back_to_explicit() {
    let a = [Sym::new("cyc_a"), Sym::new("cyc_b"), Sym::new("cyc_c")];
    let b = [Sym::new("cyc_d"), Sym::new("cyc_e")];
    let c3 = vec![HashMap::from([(a[0], Value::ModelValue(a[1])), (a[1], Value::ModelValue(a[2])), (a[2], Value::ModelValue(a[0]))])];
    let g_c3 = Group::from_generators(c3).unwrap();
    assert!(matches!(g_c3.kind, GroupKind::Explicit { .. }));
    assert_eq!(g_c3.symmetry_maps().len(), 2);

    let diag = vec![HashMap::from([
        (a[0], Value::ModelValue(a[1])),
        (a[1], Value::ModelValue(a[0])),
        (b[0], Value::ModelValue(b[1])),
        (b[1], Value::ModelValue(b[0])),
    ])];
    let g_diag = Group::from_generators(diag).unwrap();
    assert!(matches!(g_diag.kind, GroupKind::Explicit { .. }));
    assert_eq!(g_diag.symmetry_maps().len(), 1);

    let s3_2gen = vec![
        HashMap::from([(a[0], Value::ModelValue(a[1])), (a[1], Value::ModelValue(a[2])), (a[2], Value::ModelValue(a[0]))]),
        HashMap::from([(a[0], Value::ModelValue(a[1])), (a[1], Value::ModelValue(a[0]))]),
    ];
    let g_s3 = Group::from_generators(s3_2gen).unwrap();
    assert!(matches!(g_s3.kind, GroupKind::Factorized(_)));
    assert_eq!(g_s3.symmetry_maps().len(), 5);
}

#[test]
fn parity_with_brute_across_s4_keyed_sets_fcns_and_endomorphisms() {
    let a = [Sym::new("s4_0"), Sym::new("s4_1"), Sym::new("s4_2"), Sym::new("s4_3")];
    let gens = adjacent_transpositions(&a);
    let fg = Group::from_generators(gens.clone()).unwrap();
    assert!(matches!(fg.kind, GroupKind::Factorized(_)));
    let explicit = Group::explicit(closure(gens));
    let GroupKind::Explicit { perms, .. } = &explicit.kind else { unreachable!() };
    assert_eq!(perms.len(), 23);

    let mk_set = |mask: usize| {
        Value::set_from(a.iter().enumerate().filter_map(|(i, &s)| (mask & (1 << i) != 0).then_some(Value::ModelValue(s))).collect())
            .unwrap()
    };
    let int_patterns = [[0, 1, 2, 3], [2, 0, 2, 1], [1, 1, 1, 1], [3, 2, 1, 0], [0, 2, 0, 2]];
    let endo_patterns = [[1, 2, 3, 0], [1, 0, 3, 2], [2, 2, 0, 1], [0, 0, 0, 0], [3, 1, 1, 2]];
    for mask in 0..16usize {
        let s = mk_set(mask);
        for pat in &int_patterns {
            let f = Value::fcn_from_pairs(a.iter().zip(pat).map(|(&k, &v)| (Value::ModelValue(k), Value::Int(v))).collect()).unwrap();
            let partial = Value::fcn_from_pairs(
                a.iter()
                    .enumerate()
                    .filter(|&(i, _)| mask & (1 << i) != 0)
                    .map(|(i, &k)| (Value::ModelValue(k), Value::Int(pat[i])))
                    .collect(),
            )
            .unwrap();
            for &scalar in &a {
                let vals = [s.clone(), f.clone(), partial.clone(), Value::ModelValue(scalar)];
                for order in [[0, 1, 2, 3], [1, 2, 0, 3], [2, 3, 1, 0], [3, 0, 1, 2]] {
                    let want = brute_image(perms, &vals, &order).unwrap();
                    let got = apply_chosen(fg.least_perm(&mut StateVals::Given(&vals), &order).unwrap(), &vals);
                    assert_eq!(got, want, "S4 mask={mask} pat={pat:?} scalar={scalar:?} order={order:?}");
                    let idx = fg.least_perm_index(&mut StateVals::Given(&vals), &order, false).unwrap();
                    let idx_img = match idx {
                        None => vals.to_vec(),
                        Some(i) => {
                            let fp = FastPerm::new(&fg.symmetry_maps()[i]);
                            vals.iter().map(|v| fp.apply(v).unwrap().unwrap_or_else(|| v.clone())).collect()
                        }
                    };
                    assert_eq!(idx_img, want, "S4 index parity");
                }
            }
        }
        for endo in &endo_patterns {
            let ef =
                Value::fcn_from_pairs(a.iter().enumerate().map(|(i, &k)| (Value::ModelValue(k), Value::ModelValue(a[endo[i]]))).collect())
                    .unwrap();
            let vals = [ef, s.clone(), Value::ModelValue(a[mask % 4])];
            for order in [[0, 1, 2], [1, 0, 2], [2, 0, 1]] {
                let want = brute_image(perms, &vals, &order).unwrap();
                let got = apply_chosen(fg.least_perm(&mut StateVals::Given(&vals), &order).unwrap(), &vals);
                assert_eq!(got, want, "S4 endo={endo:?} mask={mask} order={order:?}");
            }
        }
    }
}

#[test]
fn parity_with_brute_across_multi_factor_s3_x_s3_including_nested_maps_and_total_order() {
    let k1 = [Sym::new("mf_a0"), Sym::new("mf_a1"), Sym::new("mf_a2")];
    let k2 = [Sym::new("mf_b0"), Sym::new("mf_b1"), Sym::new("mf_b2")];
    let mut gens = adjacent_transpositions(&k1);
    gens.extend(adjacent_transpositions(&k2));
    let fg = Group::from_generators(gens.clone()).unwrap();
    assert!(matches!(fg.kind, GroupKind::Factorized(_)));
    let explicit = Group::explicit(closure(gens));
    let GroupKind::Explicit { perms, .. } = &explicit.kind else { unreachable!() };
    assert_eq!(perms.len(), 35);

    let maps_k1_k2 = [[0, 0, 0], [0, 1, 2], [2, 0, 2], [1, 2, 0], [2, 2, 1]];
    let inner_rows = [[0, 1, 2], [2, 0, 1], [1, 1, 0], [0, 0, 0]];
    for &m in &maps_k1_k2 {
        let f_k1_k2 =
            Value::fcn_from_pairs(k1.iter().enumerate().map(|(i, &x)| (Value::ModelValue(x), Value::ModelValue(k2[m[i]]))).collect())
                .unwrap();
        let nested = Value::fcn_from_pairs(
            k1.iter()
                .enumerate()
                .map(|(i, &x)| {
                    let row = inner_rows[(i + m[i]) % inner_rows.len()];
                    let inner =
                        Value::fcn_from_pairs(k2.iter().zip(row).map(|(&y, v)| (Value::ModelValue(y), Value::Int(v))).collect()).unwrap();
                    (Value::ModelValue(x), inner)
                })
                .collect(),
        )
        .unwrap();
        let mixed_set =
            Value::set_from(vec![Value::ModelValue(k1[m[0]]), Value::ModelValue(k1[m[2]]), Value::ModelValue(k2[m[1]])]).unwrap();
        let rec = Value::record(vec![
            (Sym::new("f"), f_k1_k2.clone()),
            (Sym::new("owner"), Value::ModelValue(k2[m[2]])),
            (Sym::new("peers"), mixed_set.clone()),
        ]);
        let vals = [f_k1_k2, nested, rec, Value::ModelValue(k1[m[1]])];
        for order in [[0, 1, 2, 3], [1, 0, 3, 2], [2, 3, 1, 0], [3, 2, 0, 1]] {
            let want = brute_image(perms, &vals, &order).unwrap();
            let got = apply_chosen(fg.least_perm(&mut StateVals::Given(&vals), &order).unwrap(), &vals);
            assert_eq!(got, want, "S3xS3 m={m:?} order={order:?}");
        }
        let sentinel_fcn = Value::fcn_from_pairs(vec![
            (Value::ModelValue(k1[0]), Value::Bool(true)),
            (Value::ModelValue(k1[1]), Value::Int(0)),
            (Value::ModelValue(k1[2]), Value::ModelValue(k2[m[1]])),
        ])
        .unwrap();
        let proj = Value::tuple(vec![sentinel_fcn, mixed_set, Value::ModelValue(k2[m[0]])]);
        let want_total = brute_total_image(perms, &proj).unwrap();
        let got_total = match fg.least_total_perm(&proj).unwrap() {
            None => proj.clone(),
            Some(p) => p.apply(&proj).unwrap().unwrap_or_else(|| proj.clone()),
        };
        assert_eq!(got_total, want_total, "S3xS3 projected_orbit total order m={m:?}");
    }
}

#[test]
fn large_disjoint_products_scale_without_enumerating_group() {
    let s8: Vec<Sym> = (0..8).map(|i| Sym::new(&format!("big_n{i}"))).collect();
    let g_s8 = Group::from_generators(adjacent_transpositions(&s8)).unwrap();
    let GroupKind::Factorized(fg8) = &g_s8.kind else { panic!("expected factorized S_8") };
    assert_eq!(fg8.order, 40_320);
    assert!(g_s8.symmetry_maps().is_empty(), "order > 720 must not materialize symmetry_maps");

    let f_s8 = Value::fcn_from_pairs(s8.iter().enumerate().map(|(i, &k)| (Value::ModelValue(k), Value::Int((7 - i as i64) % 4))).collect())
        .unwrap();
    let set_s8 = Value::set_from(vec![Value::ModelValue(s8[5]), Value::ModelValue(s8[2]), Value::ModelValue(s8[7])]).unwrap();
    let vals_s8 = [set_s8, f_s8, Value::ModelValue(s8[6])];
    let t0 = std::time::Instant::now();
    let p8 = g_s8.least_perm(&mut StateVals::Given(&vals_s8), &[0, 1, 2]).unwrap();
    let img8 = apply_chosen(p8, &vals_s8);
    assert!(t0.elapsed() < std::time::Duration::from_millis(50), "S_8 canonicalization took {:?}", t0.elapsed());
    assert_eq!(img8[0], Value::set_from(vec![Value::ModelValue(s8[0]), Value::ModelValue(s8[1]), Value::ModelValue(s8[2])]).unwrap());
    assert!(g_s8.least_perm(&mut StateVals::Given(&img8), &[0, 1, 2]).unwrap().is_none());

    let txns: Vec<Sym> = (0..4).map(|i| Sym::new(&format!("big_t{i}"))).collect();
    let keys: Vec<Sym> = (0..4).map(|i| Sym::new(&format!("big_k{i}"))).collect();
    let nodes: Vec<Sym> = (0..4).map(|i| Sym::new(&format!("big_s{i}"))).collect();
    let mut gens = adjacent_transpositions(&txns);
    gens.extend(adjacent_transpositions(&keys));
    gens.extend(adjacent_transpositions(&nodes));
    let g_prod = Group::from_generators(gens).unwrap();
    let GroupKind::Factorized(fg_prod) = &g_prod.kind else { panic!("expected factorized S_4^3") };
    assert_eq!(fg_prod.order, 13_824);
    assert!(g_prod.symmetry_maps().is_empty());

    let f_txn =
        Value::fcn_from_pairs(txns.iter().enumerate().map(|(i, &k)| (Value::ModelValue(k), Value::Int(3 - i as i64))).collect()).unwrap();
    let f_key = Value::fcn_from_pairs(
        keys.iter().enumerate().map(|(i, &k)| (Value::ModelValue(k), Value::ModelValue(txns[(i + 2) % 4]))).collect(),
    )
    .unwrap();
    let f_node = Value::fcn_from_pairs(
        nodes.iter().enumerate().map(|(i, &k)| (Value::ModelValue(k), Value::ModelValue(keys[(3 - i) % 4]))).collect(),
    )
    .unwrap();
    let vals_prod = [f_txn, f_key, f_node];
    let t1 = std::time::Instant::now();
    let p_prod = g_prod.least_perm(&mut StateVals::Given(&vals_prod), &[0, 1, 2]).unwrap();
    let img_prod = apply_chosen(p_prod, &vals_prod);
    assert!(t1.elapsed() < std::time::Duration::from_millis(50), "S_4^3 canonicalization took {:?}", t1.elapsed());
    let want_txn =
        Value::fcn_from_pairs(txns.iter().enumerate().map(|(i, &k)| (Value::ModelValue(k), Value::Int(i as i64))).collect()).unwrap();
    assert_eq!(img_prod[0], want_txn);
    assert!(g_prod.least_perm(&mut StateVals::Given(&img_prod), &[0, 1, 2]).unwrap().is_none());

    let proj = Value::tuple(vals_prod.to_vec());
    let img_proj = match g_prod.least_total_perm(&proj).unwrap() {
        None => proj.clone(),
        Some(p) => p.apply(&proj).unwrap().unwrap_or_else(|| proj.clone()),
    };
    assert_eq!(img_proj, Value::tuple(img_prod));
    assert!(g_prod.least_total_perm(&img_proj).unwrap().is_none());
}

#[test]
fn decoded_state_skips_later_variables_once_partition_is_complete() {
    let a = [Sym::new("dec_a"), Sym::new("dec_b"), Sym::new("dec_c")];
    let fg = Group::from_generators(adjacent_transpositions(&a)).unwrap();
    let vals = [
        Value::fcn_from_pairs(vec![
            (Value::ModelValue(a[0]), Value::Int(2)),
            (Value::ModelValue(a[1]), Value::Int(0)),
            (Value::ModelValue(a[2]), Value::Int(1)),
        ])
        .unwrap(),
        Value::ModelValue(a[2]),
    ];
    let decoded_var1 = std::cell::Cell::new(false);
    let decode = |i: usize| {
        if i == 1 {
            decoded_var1.set(true);
        }
        vals[i].clone()
    };
    let mut sv = StateVals::decoded(2, &decode);
    let p = fg.least_perm(&mut sv, &[0, 1]).unwrap();
    assert!(p.is_some());
    assert!(!decoded_var1.get(), "second variable must not be decoded once partition is complete");
}

#[test]
fn typed_and_mixed_model_value_factors_behave_soundly() {
    let typed = [Sym::new("t_a"), Sym::new("t_b"), Sym::new("t_c")];
    let g_typed = Group::from_generators(adjacent_transpositions(&typed)).unwrap();
    assert!(matches!(g_typed.kind, GroupKind::Factorized(_)));
    let explicit_typed = Group::explicit(closure(adjacent_transpositions(&typed)));
    let GroupKind::Explicit { perms, .. } = &explicit_typed.kind else { unreachable!() };
    let f = Value::fcn_from_pairs(vec![
        (Value::ModelValue(typed[0]), Value::Int(2)),
        (Value::ModelValue(typed[1]), Value::Int(0)),
        (Value::ModelValue(typed[2]), Value::Int(1)),
    ])
    .unwrap();
    let vals = [f, Value::ModelValue(typed[2])];
    assert_eq!(
        apply_chosen(g_typed.least_perm(&mut StateVals::Given(&vals), &[0, 1]).unwrap(), &vals),
        brute_image(perms, &vals, &[0, 1]).unwrap()
    );

    let mixed = [Sym::new("t_mix1"), Sym::new("untyped_mix2")];
    let g_mixed = Group::from_generators(adjacent_transpositions(&mixed)).unwrap();
    assert!(matches!(g_mixed.kind, GroupKind::Explicit { .. }));
}

#[test]
fn symmetry_group_from_tla_expr_handles_large_products_overlaps_and_errors() {
    use crate::interp::Interp;
    use crate::model::InterpModel;
    use tlx_sema::Program;

    let spec_big = r#"---- MODULE BigSym ----
EXTENDS TLC, Naturals
CONSTANTS N, K, T
VARIABLE x, f
Sym8 == Permutations(N)
SymProd == Permutations(K) \cup Permutations(T)
Init == /\ x \in N /\ f = [k \in K |-> 0]
Next == UNCHANGED <<x, f>>
====
"#;
    let cfg_s8 = "CONSTANTS N = {n1, n2, n3, n4, n5, n6, n7, n8} K = {k1, k2} T = {t1, t2}\nINIT Init\nNEXT Next\nSYMMETRY Sym8\n";
    let dir = tlx_testkit::TempDir::with_spec("big-sym-s8", spec_big, cfg_s8);
    let t0 = std::time::Instant::now();
    let ip = Interp::new(Program::load(&dir.join("BigSym.tla"), &[]).unwrap(), tlx_front::cfg::parse_cfg(cfg_s8).unwrap()).unwrap();
    let m = InterpModel::new(ip).unwrap();
    assert!(t0.elapsed() < std::time::Duration::from_secs(2), "BigSym S_8 took {:?}", t0.elapsed());
    assert!(m.has_view_or_symmetry());
    assert!(m.symmetry_maps().is_empty(), "S_8 must not materialize 40,319 maps");
    let mut init_fps = HashSet::new();
    m.init_states_until(&mut |s| {
        init_fps.insert(s.fp);
        true
    })
    .unwrap();
    assert_eq!(init_fps.len(), 1, "all 8 initial states of x \\in N must collapse to 1 orbit");

    let spec_overlap = r#"---- MODULE OverlapSym ----
EXTENDS TLC
CONSTANTS a, b, c
VARIABLE x
Sym == Permutations({a, b}) \cup Permutations({b, c})
Init == x \in {a, b, c}
Next == UNCHANGED x
====
"#;
    let cfg_ov = "CONSTANTS a = a b = b c = c\nINIT Init\nNEXT Next\nSYMMETRY Sym\n";
    let dir_ov = tlx_testkit::TempDir::with_spec("overlap-sym", spec_overlap, cfg_ov);
    let ip_ov =
        Interp::new(Program::load(&dir_ov.join("OverlapSym.tla"), &[]).unwrap(), tlx_front::cfg::parse_cfg(cfg_ov).unwrap()).unwrap();
    let m_ov = InterpModel::new(ip_ov).unwrap();
    assert_eq!(m_ov.symmetry_maps().len(), 5);
    let mut ov_fps = HashSet::new();
    m_ov.init_states_until(&mut |s| {
        ov_fps.insert(s.fp);
        true
    })
    .unwrap();
    assert_eq!(ov_fps.len(), 1);

    let spec_bad = r#"---- MODULE BadSym ----
EXTENDS TLC
VARIABLE x
Sym == Permutations({1})
Init == x = 1
Next == UNCHANGED x
====
"#;
    let cfg_bad = "INIT Init\nNEXT Next\nSYMMETRY Sym\n";
    let dir_bad = tlx_testkit::TempDir::with_spec("bad-sym", spec_bad, cfg_bad);
    let ip_bad =
        Interp::new(Program::load(&dir_bad.join("BadSym.tla"), &[]).unwrap(), tlx_front::cfg::parse_cfg(cfg_bad).unwrap()).unwrap();
    let err = InterpModel::new(ip_bad).err().expect("non-model-value Permutations must fail");
    assert!(err.message.contains("SYMMETRY permutations must map model values, found 1"), "got: {}", err.message);
}

#[test]
fn tagged_rows_short_circuit_losing_payloads_before_incomparable_tails() {
    // Reproduces TaggedRows.tla: losing row starts with tag 1 (> 0) and has an
    // incomparable Bool vs Int function in tuple element 1. Must short-circuit
    // at tag 1 > 0 without comparing TRUE against 1.
    let ab = [Sym::new("tr_a"), Sym::new("tr_b")];
    let cd = [Sym::new("tr_c"), Sym::new("tr_d")];
    let mut gens = adjacent_transpositions(&ab);
    gens.extend(adjacent_transpositions(&cd));
    let fg = Group::from_generators(gens.clone()).unwrap();
    let explicit = Group::explicit(closure(gens));
    let GroupKind::Explicit { perms, .. } = &explicit.kind else { unreachable!() };

    let row_ok = Value::tuple(vec![
        Value::Int(0),
        Value::fcn_from_pairs(vec![(Value::ModelValue(cd[0]), Value::Int(0)), (Value::ModelValue(cd[1]), Value::Int(1))]).unwrap(),
    ]);
    let row_mixed = Value::tuple(vec![
        Value::Int(1),
        Value::fcn_from_pairs(vec![(Value::ModelValue(cd[0]), Value::Bool(true)), (Value::ModelValue(cd[1]), Value::Int(1))]).unwrap(),
    ]);
    // Both orientations (tag 0 first and tag 1 first) must match `brute`.
    for pairs in [
        vec![(Value::ModelValue(ab[0]), row_ok.clone()), (Value::ModelValue(ab[1]), row_mixed.clone())],
        vec![(Value::ModelValue(ab[0]), row_mixed.clone()), (Value::ModelValue(ab[1]), row_ok.clone())],
    ] {
        let rows = Value::fcn_from_pairs(pairs).unwrap();
        let vals = [rows];
        let want = brute_image(perms, &vals, &[0]).unwrap();
        let got = apply_chosen(fg.least_perm(&mut StateVals::Given(&vals), &[0]).unwrap(), &vals);
        assert_eq!(got, want);
    }

    // Also test tagged Record payloads with the same structure (use unique
    // symbols so `Sym` intern order places `tr_tag` before `tr_val`).
    let tag_f = Sym::new("tr_tag");
    let map_f = Sym::new("tr_val");
    let rec_ok = Value::record(vec![
        (tag_f, Value::Int(0)),
        (map_f, Value::fcn_from_pairs(vec![(Value::ModelValue(cd[0]), Value::Int(0)), (Value::ModelValue(cd[1]), Value::Int(1))]).unwrap()),
    ]);
    let rec_mixed = Value::record(vec![
        (tag_f, Value::Int(1)),
        (
            map_f,
            Value::fcn_from_pairs(vec![(Value::ModelValue(cd[0]), Value::Bool(true)), (Value::ModelValue(cd[1]), Value::Int(1))]).unwrap(),
        ),
    ]);
    let rec_rows = Value::fcn_from_pairs(vec![(Value::ModelValue(ab[0]), rec_ok), (Value::ModelValue(ab[1]), rec_mixed)]).unwrap();
    let rec_vals = [rec_rows];
    assert_eq!(
        apply_chosen(fg.least_perm(&mut StateVals::Given(&rec_vals), &[0]).unwrap(), &rec_vals),
        brute_image(perms, &rec_vals, &[0]).unwrap()
    );
}

#[test]
fn identity_and_self_equivariant_maps_keep_compact_stabilizer_and_preserve_freedom() {
    // S_9 (362,880 permutations): `[i \in N |-> i]` followed by a tie-breaking
    // scalar `x = n_7` must run in milliseconds with 1 compact stabilizer
    // partition and map `x` to `n_0` while fixing `[i \in N |-> i]`.
    let n9: Vec<Sym> = (0..9).map(|i| Sym::new(&format!("id9_{i}"))).collect();
    let g9 = Group::from_generators(adjacent_transpositions(&n9)).unwrap();
    let id_fcn = Value::fcn_from_pairs(n9.iter().map(|&k| (Value::ModelValue(k), Value::ModelValue(k))).collect()).unwrap();
    let self_rec_fcn = Value::fcn_from_pairs(
        n9.iter()
            .map(|&k| (Value::ModelValue(k), Value::record(vec![(Sym::new("id"), Value::ModelValue(k)), (Sym::new("st"), Value::Int(0))])))
            .collect(),
    )
    .unwrap();
    let partial_id_fcn =
        Value::fcn_from_pairs([n9[3], n9[6], n9[8]].into_iter().map(|k| (Value::ModelValue(k), Value::ModelValue(k))).collect()).unwrap();

    for f in [&id_fcn, &self_rec_fcn] {
        let t0 = std::time::Instant::now();
        // Alone: identity wins immediately.
        assert!(g9.least_perm(&mut StateVals::Given(std::slice::from_ref(f)), &[0]).unwrap().is_none());
        // Followed by a scalar: scalar must freely map to n9[0].
        let vals = [f.clone(), Value::ModelValue(n9[7])];
        let img = apply_chosen(g9.least_perm(&mut StateVals::Given(&vals), &[0, 1]).unwrap(), &vals);
        assert!(t0.elapsed() < std::time::Duration::from_millis(50), "S_9 identity map took {:?}", t0.elapsed());
        assert_eq!(img[0], *f);
        assert_eq!(img[1], Value::ModelValue(n9[0]));
    }

    // Partial identity map on {n3, n6, n8} followed by scalar n6 -> maps domain
    // to {n0, n1, n2} and scalar n6 to n0.
    let p_vals = [partial_id_fcn, Value::ModelValue(n9[6])];
    let p_img = apply_chosen(g9.least_perm(&mut StateVals::Given(&p_vals), &[0, 1]).unwrap(), &p_vals);
    let want_partial = Value::fcn_from_pairs(n9[..3].iter().map(|&k| (Value::ModelValue(k), Value::ModelValue(k))).collect()).unwrap();
    assert_eq!(p_img[0], want_partial);
    assert_eq!(p_img[1], Value::ModelValue(n9[0]));

    // Exhaustive S_4 brute parity on partial identity + self-equivariant record maps.
    let s4 = [Sym::new("id4_0"), Sym::new("id4_1"), Sym::new("id4_2"), Sym::new("id4_3")];
    let gens4 = adjacent_transpositions(&s4);
    let g4 = Group::from_generators(gens4.clone()).unwrap();
    let exp4 = Group::explicit(closure(gens4));
    let GroupKind::Explicit { perms, .. } = &exp4.kind else { unreachable!() };
    for mask in 1..16usize {
        let pf = Value::fcn_from_pairs(
            s4.iter()
                .enumerate()
                .filter(|&(i, _)| mask & (1 << i) != 0)
                .map(|(_, &k)| (Value::ModelValue(k), Value::ModelValue(k)))
                .collect(),
        )
        .unwrap();
        for &tail in &s4 {
            let vals = [pf.clone(), Value::ModelValue(tail)];
            assert_eq!(
                apply_chosen(g4.least_perm(&mut StateVals::Given(&vals), &[0, 1]).unwrap(), &vals),
                brute_image(perms, &vals, &[0, 1]).unwrap(),
                "S_4 partial id mask={mask}, tail={tail:?}"
            );
        }
    }

    // Singleton block carrying an unpinned atom while the non-singleton block
    // is self-equivariant: pinning `a` leaves `{b, c}` unpinned; `f[a] = {c}`
    // must still refine `{b, c}` so `c -> b` minimizes `f[a]`.
    let s3 = [Sym::new("s3_a"), Sym::new("s3_b"), Sym::new("s3_c")];
    let gens3 = adjacent_transpositions(&s3);
    let g3 = Group::from_generators(gens3.clone()).unwrap();
    let exp3 = Group::explicit(closure(gens3));
    let GroupKind::Explicit { perms: perms3, .. } = &exp3.kind else { unreachable!() };
    for &p0 in &s3 {
        for &target in &s3 {
            let f = Value::fcn_from_pairs(
                s3.iter()
                    .map(|&k| {
                        let payload = if k == p0 {
                            Value::set_from(vec![Value::ModelValue(target)]).unwrap()
                        } else {
                            Value::set_from(vec![Value::ModelValue(k)]).unwrap()
                        };
                        (Value::ModelValue(k), payload)
                    })
                    .collect(),
            )
            .unwrap();
            let vals = [Value::ModelValue(p0), f];
            assert_eq!(
                apply_chosen(g3.least_perm(&mut StateVals::Given(&vals), &[0, 1]).unwrap(), &vals),
                brute_image(perms3, &vals, &[0, 1]).unwrap(),
                "S_3 singleton unpinned payload p0={p0:?}, target={target:?}"
            );
        }
    }
}

#[test]
fn unknown_prefix_candidates_and_set_prefix_errors_match_tlc() {
    // FixedPrefix: `[high, b, low]` and `[a, high, low]` under S_3 share one orbit
    // because `b` is unpinned and can map to `a < low < high`.
    let a = Sym::new("fp_a");
    let b = Sym::new("fp_b");
    let c = Sym::new("fp_c");
    let low = Sym::new("fp_low");
    let high = Sym::new("fp_high");
    let gens = adjacent_transpositions(&[a, b, c]);
    let fg = Group::from_generators(gens.clone()).unwrap();
    let exp = Group::explicit(closure(gens));
    let GroupKind::Explicit { perms, .. } = &exp.kind else { unreachable!() };
    let f1 = Value::fcn_from_pairs(vec![
        (Value::ModelValue(a), Value::ModelValue(high)),
        (Value::ModelValue(b), Value::ModelValue(b)),
        (Value::ModelValue(c), Value::ModelValue(low)),
    ])
    .unwrap();
    let f2 = Value::fcn_from_pairs(vec![
        (Value::ModelValue(a), Value::ModelValue(a)),
        (Value::ModelValue(b), Value::ModelValue(high)),
        (Value::ModelValue(c), Value::ModelValue(low)),
    ])
    .unwrap();
    let img1 = apply_chosen(fg.least_perm(&mut StateVals::Given(std::slice::from_ref(&f1)), &[0]).unwrap(), std::slice::from_ref(&f1));
    let img2 = apply_chosen(fg.least_perm(&mut StateVals::Given(std::slice::from_ref(&f2)), &[0]).unwrap(), std::slice::from_ref(&f2));
    assert_eq!(img1, img2);
    assert_eq!(img1, brute_image(perms, std::slice::from_ref(&f1), &[0]).unwrap());

    // RowOrbit: S_3 x S_2 with payloads `(z, peer, y)` where `u < v < y < z`
    // must collapse all 12 permutations to one canonical image.
    let keys = [Sym::new("ro_a"), Sym::new("ro_b"), Sym::new("ro_c")];
    let peers = [Sym::new("ro_u"), Sym::new("ro_v")];
    let y = Sym::new("ro_y");
    let z = Sym::new("ro_z");
    let mut ro_gens = adjacent_transpositions(&keys);
    ro_gens.extend(adjacent_transpositions(&peers));
    let ro_fg = Group::from_generators(ro_gens.clone()).unwrap();
    let ro_exp = Group::explicit(closure(ro_gens));
    let GroupKind::Explicit { perms: ro_perms, .. } = &ro_exp.kind else { unreachable!() };
    let mut orbit_imgs = Vec::new();
    for perm in [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]] {
        for &peer in &peers {
            let rows = Value::fcn_from_pairs(vec![
                (Value::ModelValue(keys[perm[0]]), Value::ModelValue(z)),
                (Value::ModelValue(keys[perm[1]]), Value::ModelValue(peer)),
                (Value::ModelValue(keys[perm[2]]), Value::ModelValue(y)),
            ])
            .unwrap();
            let got = apply_chosen(
                ro_fg.least_perm(&mut StateVals::Given(std::slice::from_ref(&rows)), &[0]).unwrap(),
                std::slice::from_ref(&rows),
            );
            let want = brute_image(ro_perms, std::slice::from_ref(&rows), &[0]).unwrap();
            assert_eq!(got, want);
            orbit_imgs.push(got);
        }
    }
    assert!(orbit_imgs.windows(2).all(|w| w[0] == w[1]), "all 12 RowOrbit states must collapse to one image");

    // SetPrefix: swapping `b` and `c` fixes `{b, c}` and compares `FALSE` vs `0`
    // in TLC's `Permutations({a, b, c})` walk; factorized group must report the
    // same comparison error.
    let sa = Sym::new("sp_a");
    let sb = Sym::new("sp_b");
    let sc = Sym::new("sp_c");
    let sp_fg = Group::from_factors(vec![vec![sa, sb, sc]]);
    let inner = Value::fcn_from_pairs(vec![(Value::ModelValue(sb), Value::Int(0)), (Value::ModelValue(sc), Value::Bool(false))]).unwrap();
    let outer = Value::fcn_from_pairs(vec![
        (Value::ModelValue(sa), inner),
        (Value::ModelValue(sb), Value::Int(0)),
        (Value::ModelValue(sc), Value::Int(1)),
    ])
    .unwrap();
    let sp_val = Value::tuple(vec![Value::set_from(vec![Value::ModelValue(sb), Value::ModelValue(sc)]).unwrap(), outer]);
    let sp_err = sp_fg.least_perm(&mut StateVals::Given(std::slice::from_ref(&sp_val)), &[0]).err().expect("expected comparison error");
    assert!(sp_err.to_string().contains("non-integer") || sp_err.to_string().contains("non-boolean"), "unexpected error: {sp_err}");

    // SevenPrefix (S_7, order 5040 > 720): lazy ordered walk must still report
    // the TLC comparison error on `(f g)` without materializing 7! perms.
    let s7: Vec<Sym> = ["s7_a", "s7_b", "s7_c", "s7_d", "s7_e", "s7_f", "s7_g"].into_iter().map(Sym::new).collect();
    let g7 = Group::from_factors(vec![s7.clone()]);
    let s7_inner =
        Value::fcn_from_pairs(vec![(Value::ModelValue(s7[5]), Value::Int(0)), (Value::ModelValue(s7[6]), Value::Bool(false))]).unwrap();
    let s7_outer = Value::fcn_from_pairs(vec![
        (Value::ModelValue(s7[0]), s7_inner),
        (Value::ModelValue(s7[5]), Value::Int(0)),
        (Value::ModelValue(s7[6]), Value::Int(1)),
    ])
    .unwrap();
    let s7_val = Value::tuple(vec![Value::set_from(vec![Value::ModelValue(s7[5]), Value::ModelValue(s7[6])]).unwrap(), s7_outer]);
    assert!(g7.least_perm(&mut StateVals::Given(std::slice::from_ref(&s7_val)), &[0]).is_err());

    // ProductOrder (S_2 x S_3): smaller-cardinality factor {a0, a1} sorts before
    // {b0, b1, b2} in TLC's normalized union, lowering the leading scalar before
    // the 3-key factor can expose the incomparable tail.
    let po_b = [Sym::new("po_b0"), Sym::new("po_b1"), Sym::new("po_b2")];
    let po_a = [Sym::new("po_a0"), Sym::new("po_a1")];
    let po_g = Group::from_factors(vec![po_a.to_vec(), po_b.to_vec()]);
    let po_inner =
        Value::fcn_from_pairs(vec![(Value::ModelValue(po_b[1]), Value::Int(0)), (Value::ModelValue(po_b[2]), Value::Bool(false))]).unwrap();
    let po_outer =
        Value::fcn_from_pairs(vec![(Value::ModelValue(po_a[0]), po_inner), (Value::ModelValue(po_a[1]), Value::ModelValue(po_b[1]))])
            .unwrap();
    let po_val = Value::tuple(vec![Value::ModelValue(po_a[1]), po_outer]);
    assert!(po_g.least_perm(&mut StateVals::Given(std::slice::from_ref(&po_val)), &[0]).is_ok());

    // TaggedProduct (S_3 x S_2): smaller-cardinality factor {d, e} sorts before
    // {a, b, c} in TLC's normalized union, swapping {d, e} while row `a` is
    // still first and raising the comparison error on `1` vs `TRUE`.
    let tp_a = [Sym::new("tp_a"), Sym::new("tp_b"), Sym::new("tp_c")];
    let tp_b = [Sym::new("tp_d"), Sym::new("tp_e")];
    let tp_g = Group::from_factors(vec![tp_b.to_vec(), tp_a.to_vec()]);
    let tp_bad = Value::tuple(vec![
        Value::Int(1),
        Value::fcn_from_pairs(vec![(Value::ModelValue(tp_b[0]), Value::Bool(true)), (Value::ModelValue(tp_b[1]), Value::Int(1))]).unwrap(),
    ]);
    let tp_ok = Value::tuple(vec![
        Value::Int(0),
        Value::fcn_from_pairs(vec![(Value::ModelValue(tp_b[0]), Value::Int(0)), (Value::ModelValue(tp_b[1]), Value::Int(1))]).unwrap(),
    ]);
    let tp_rows = Value::fcn_from_pairs(vec![
        (Value::ModelValue(tp_a[0]), tp_bad),
        (Value::ModelValue(tp_a[1]), tp_ok.clone()),
        (Value::ModelValue(tp_a[2]), tp_ok),
    ])
    .unwrap();
    assert!(tp_g.least_perm(&mut StateVals::Given(std::slice::from_ref(&tp_rows)), &[0]).is_err());
}

#[test]
fn nine_pairs_rank_and_closure_order_and_tagged_status_fast_path() {
    // 1. Nine disjoint pairs (order 512 <= 720, 18 moved keys > INLINE_KEYS):
    // `rank_of` and `least_perm_index` must work cleanly without overflowing.
    let pairs: Vec<Vec<Sym>> = (1..=9).map(|i| vec![Sym::new(&format!("np_{i}a")), Sym::new(&format!("np_{i}b"))]).collect();
    let g9p = Group::from_factors(pairs.clone());
    let maps = g9p.symmetry_maps();
    assert_eq!(maps.len(), 511);
    for p in &pairs {
        let vals = [Value::ModelValue(p[1])];
        let idx = g9p.least_perm_index(&mut StateVals::Given(&vals), &[0], false).unwrap().expect("swap needed");
        assert_eq!(maps[idx].get(&p[1]), Some(&Value::ModelValue(p[0])));
    }

    // 2. Exact visit-sequence parity against `close_under_composition` for
    // three disjoint S_3 factors (215 non-identity perms, incl. 21st = (1,0,1))
    // AND for overlapping `Permutations({a, b}) \cup Permutations({b, c})`.
    let f0 = [Sym::new("co_a0"), Sym::new("co_a1"), Sym::new("co_a2")];
    let f1 = [Sym::new("co_b0"), Sym::new("co_b1"), Sym::new("co_b2")];
    let f2 = [Sym::new("co_c0"), Sym::new("co_c1"), Sym::new("co_c2")];
    let g333 = Group::from_factors(vec![f0.to_vec(), f1.to_vec(), f2.to_vec()]);
    let GroupKind::Factorized(fg333) = &g333.kind else { unreachable!() };
    let mut gens333 = Vec::new();
    for fac in [&f0, &f1, &f2] {
        for p in lex_permutations(3).into_iter().skip(1) {
            let mut m = HashMap::new();
            for (k, &t) in p.iter().enumerate() {
                if t as usize != k {
                    m.insert(fac[k], Value::ModelValue(fac[t as usize]));
                }
            }
            gens333.push(m);
        }
    }
    let want_seq: Vec<Vec<u16>> = closure(gens333).iter().map(|p| fg333.perm_to_img(p)).collect();
    let mut got_seq: Vec<Vec<u16>> = Vec::new();
    fg333
        .for_each_perm_tlc_order(|img| {
            got_seq.push(img.to_vec());
            Ok(std::ops::ControlFlow::Continue(()))
        })
        .unwrap();
    assert_eq!(got_seq, want_seq, "S_3 x S_3 x S_3 lazy order must match close_under_composition at every index");

    let oa = Sym::new("ov_a");
    let ob = Sym::new("ov_b");
    let oc = Sym::new("ov_c");
    let ov_g = Group::from_factors_with_fallback(vec![vec![oa, ob, oc]], FallbackOrder::OverlappingSets(vec![vec![oa, ob], vec![ob, oc]]))
        .unwrap();
    let GroupKind::Factorized(ov_fg) = &ov_g.kind else { unreachable!() };
    let ov_gens = vec![
        HashMap::from([(oa, Value::ModelValue(ob)), (ob, Value::ModelValue(oa))]),
        HashMap::from([(ob, Value::ModelValue(oc)), (oc, Value::ModelValue(ob))]),
    ];
    let ov_want: Vec<Vec<u16>> = closure(ov_gens).iter().map(|p| ov_fg.perm_to_img(p)).collect();
    let mut ov_got: Vec<Vec<u16>> = Vec::new();
    ov_fg
        .for_each_perm_tlc_order(|img| {
            ov_got.push(img.to_vec());
            Ok(std::ops::ControlFlow::Continue(()))
        })
        .unwrap();
    assert_eq!(ov_got, ov_want, "overlapping union must match close_under_composition");
    // The compiled VIEW+SYMMETRY path visits permutations in this order, so it
    // must be exposed as indices into the materialized `symmetry_maps`.
    let ov_ranks: Vec<usize> = ov_got.iter().map(|img| ov_fg.rank_of_img(img).expect("non-identity rank")).collect();
    assert_eq!(ov_g.symmetry_maps_tlc_order().unwrap(), ov_ranks);
    assert_eq!(ov_g.symmetry_maps().len(), ov_ranks.len());

    // 3. Tagged-variant status map on S_9 (`<<0, FALSE>>` vs `<<1, 42>>`) is
    // provably orbit-comparison-safe and stays on the O(n log n) refinement path.
    let s9: Vec<Sym> = (0..9).map(|i| Sym::new(&format!("st9_{i}"))).collect();
    let g9 = Group::from_factors(vec![s9.clone()]);
    let GroupKind::Factorized(fg9) = &g9.kind else { unreachable!() };
    let status = Value::fcn_from_pairs(
        s9[1..]
            .iter()
            .map(|&k| {
                let row = if k == s9[1] {
                    Value::tuple(vec![Value::Int(0), Value::Bool(false)])
                } else {
                    Value::tuple(vec![Value::Int(1), Value::Int(42)])
                };
                (Value::ModelValue(k), row)
            })
            .collect(),
    )
    .unwrap();
    assert!(is_orbit_cmp_safe(&status, fg9));
    let t0 = std::time::Instant::now();
    let chosen = g9.least_perm(&mut StateVals::Given(std::slice::from_ref(&status)), &[0]).unwrap();
    assert!(t0.elapsed() < std::time::Duration::from_millis(50), "S_9 tagged status took {:?}", t0.elapsed());
    let img = apply_chosen(chosen, std::slice::from_ref(&status));
    let Value::Fcn(ps, _) = &img[0] else { unreachable!() };
    assert_eq!(ps[0], (Value::ModelValue(s9[0]), Value::tuple(vec![Value::Int(0), Value::Bool(false)])));
}

#[test]
fn overlapping_closure_early_stops_and_fixed_domain_fcns_and_invariant_bags_scale() {
    use super::factor::BFS_COMPOSITIONS;

    // 1. Subset7 (`Permutations(N7) \cup Permutations({n5, n6})`): all 5039
    // non-identity perms are already generators, so BFS performs 0 compositions.
    let n7: Vec<Sym> = (0..7).map(|i| Sym::new(&format!("rm7_{i}"))).collect();
    let g_sub7 =
        Group::from_factors_with_fallback(vec![n7.clone()], FallbackOrder::OverlappingSets(vec![vec![n7[5], n7[6]], n7.clone()])).unwrap();
    let msg_sub = Value::tuple(vec![
        Value::ModelValue(n7[0]),
        Value::fcn_from_pairs(vec![(Value::ModelValue(n7[0]), Value::Bool(true)), (Value::ModelValue(n7[1]), Value::Int(0))]).unwrap(),
    ]);
    BFS_COMPOSITIONS.with(|c| c.set(0));
    let _ = g_sub7.least_perm(&mut StateVals::Given(std::slice::from_ref(&msg_sub)), &[0]).unwrap();
    assert_eq!(BFS_COMPOSITIONS.with(std::cell::Cell::get), 0, "Subset7 must perform 0 BFS compositions");

    // 2. Roles7 (`Permutations({n0..n5}) \cup Permutations({n5, n6})`): with
    // only 2 observed atoms (`n0, n1` or `n5, n6`), only 41 non-identity ordered
    // pairs exist, so subgroup-skip + 41-pair saturation stops BFS early.
    let g_roles7 =
        Group::from_factors_with_fallback(vec![n7.clone()], FallbackOrder::OverlappingSets(vec![vec![n7[5], n7[6]], n7[..6].to_vec()]))
            .unwrap();
    BFS_COMPOSITIONS.with(|c| c.set(0));
    let _ = g_roles7.least_perm(&mut StateVals::Given(std::slice::from_ref(&msg_sub)), &[0]).unwrap();
    let comps_r1 = BFS_COMPOSITIONS.with(std::cell::Cell::get);
    assert!(comps_r1 < 5_000, "Roles7 on (n0, n1) should saturate early in round 2, did {comps_r1} compositions");

    let msg_roles = Value::tuple(vec![
        Value::ModelValue(n7[5]),
        Value::fcn_from_pairs(vec![(Value::ModelValue(n7[5]), Value::Bool(true)), (Value::ModelValue(n7[6]), Value::Int(0))]).unwrap(),
    ]);
    BFS_COMPOSITIONS.with(|c| c.set(0));
    let chosen_roles = g_roles7.least_perm(&mut StateVals::Given(std::slice::from_ref(&msg_roles)), &[0]).unwrap();
    let comps_r2 = BFS_COMPOSITIONS.with(std::cell::Cell::get);
    assert!(comps_r2 < 120_000, "Roles7 on (n5, n6) should stop early in round 2, did {comps_r2} compositions");
    let img_roles = apply_chosen(chosen_roles, std::slice::from_ref(&msg_roles));
    assert_eq!(img_roles[0], msg_sub);

    // 2b. Verify intra-subgroup skip preserves exact `close_under_composition`
    // order even when two overlapping sets share 2 elements (`{a,b,c}` and `{b,c,d}`).
    let o4 = [Sym::new("ov4_a"), Sym::new("ov4_b"), Sym::new("ov4_c"), Sym::new("ov4_d")];
    let g_ov4 =
        Group::from_factors_with_fallback(vec![o4.to_vec()], FallbackOrder::OverlappingSets(vec![o4[0..3].to_vec(), o4[1..4].to_vec()]))
            .unwrap();
    let GroupKind::Factorized(fg_ov4) = &g_ov4.kind else { unreachable!() };
    let mut ov4_gens = Vec::new();
    for s in [&o4[0..3], &o4[1..4]] {
        for p in lex_permutations(3).into_iter().skip(1) {
            let mut m = HashMap::new();
            for (k, &t) in p.iter().enumerate() {
                if t as usize != k {
                    m.insert(s[k], Value::ModelValue(s[t as usize]));
                }
            }
            if !ov4_gens.contains(&m) {
                ov4_gens.push(m);
            }
        }
    }
    let ov4_want: Vec<Vec<u16>> = closure(ov4_gens).iter().map(|p| fg_ov4.perm_to_img(p)).collect();
    let mut ov4_got: Vec<Vec<u16>> = Vec::new();
    fg_ov4
        .for_each_perm_tlc_order(|img| {
            ov4_got.push(img.to_vec());
            Ok(std::ops::ControlFlow::Continue(()))
        })
        .unwrap();
    assert_eq!(ov4_got, ov4_want, "overlap-2 union must match close_under_composition bit-for-bit");

    // 3. WorkerStatus (`S_8` overlapping, nested fixed-domain function
    // `(enabled :> Bool) @@ (epoch :> Int)`): stays on the refinement path with
    // 0 BFS compositions.
    let w8: Vec<Sym> = (0..8).map(|i| Sym::new(&format!("ws8_{i}"))).collect();
    let k_enabled = Sym::new("ws_enabled");
    let k_epoch = Sym::new("ws_epoch");
    let g_w8 =
        Group::from_factors_with_fallback(vec![w8.clone()], FallbackOrder::OverlappingSets(vec![vec![w8[0], w8[7]], w8[..7].to_vec()]))
            .unwrap();
    let GroupKind::Factorized(fg_w8) = &g_w8.kind else { unreachable!() };
    let worker_status = Value::fcn_from_pairs(
        w8.iter()
            .map(|&k| {
                let row = Value::fcn_from_pairs(vec![
                    (Value::ModelValue(k_enabled), Value::Bool(k == w8[5])),
                    (Value::ModelValue(k_epoch), Value::Int(0)),
                ])
                .unwrap();
                (Value::ModelValue(k), row)
            })
            .collect(),
    )
    .unwrap();
    assert!(is_orbit_cmp_safe(&worker_status, fg_w8));
    BFS_COMPOSITIONS.with(|c| c.set(0));
    let t0 = std::time::Instant::now();
    let _ = g_w8.least_perm(&mut StateVals::Given(std::slice::from_ref(&worker_status)), &[0]).unwrap();
    assert_eq!(BFS_COMPOSITIONS.with(std::cell::Cell::get), 0);
    assert!(t0.elapsed() < std::time::Duration::from_millis(50), "WorkerStatus S_8 took {:?}", t0.elapsed());

    // 4. Heartbeats (`S_9` invariant record-key bag): adjacent block swaps fix
    // the entire bag, so `branch_general_value` keeps 1 compact partition and
    // leaves a trailing scalar variable free.
    let h9: Vec<Sym> = (0..9).map(|i| Sym::new(&format!("hb9_{i}"))).collect();
    let g_h9 = Group::from_factors(vec![h9.clone()]);
    let GroupKind::Factorized(fg_h9) = &g_h9.kind else { unreachable!() };
    let f_src = Sym::new("hb_src");
    let f_kind = Sym::new("hb_kind");
    let bag = Value::fcn_from_pairs(
        h9.iter()
            .map(|&n| (Value::record(vec![(f_src, Value::ModelValue(n)), (f_kind, Value::str("heartbeat"))]), Value::Int(1)))
            .collect(),
    )
    .unwrap();
    let mut part = Partition::default();
    part.reset(fg_h9);
    let t1 = std::time::Instant::now();
    let parts = branch_general_value(fg_h9, part, &bag, CmpMode::Tlc).unwrap();
    assert_eq!(parts.len(), 1, "invariant record-key bag must keep 1 compact partition");
    let vals = [bag.clone(), Value::ModelValue(h9[7])];
    let img = apply_chosen(g_h9.least_view_perm(&mut StateVals::Given(&vals), &[0, 1]).unwrap(), &vals);
    assert!(t1.elapsed() < std::time::Duration::from_millis(50), "Heartbeats S_9 took {:?}", t1.elapsed());
    assert_eq!(img[0], bag);
    assert_eq!(img[1], Value::ModelValue(h9[0]));
}

#[test]
fn factorized_symmetry_checks_partition_index_limits() {
    let max = usize::from(u16::MAX);
    let atoms: Vec<_> = (0..max + 2).map(|i| Sym::new(&format!("indexLimit{i}"))).collect();
    let build = |n| FactorizedGroup::new(vec![atoms[..n].to_vec()], FallbackOrder::DisjointFull);
    let group = build(max).unwrap();
    assert_eq!(group.lookup(atoms[max - 1]), Some((0, max - 1)));
    let mut part = Partition::default();
    part.reset(&group);
    assert_eq!(part.block_hi()[max - 1], u16::MAX);
    for n in [max + 1, max + 2] {
        let err = build(n).err().expect("oversized factor accepted");
        assert!(err.message.contains(&format!("{n} model values")));
    }
}

#[test]
fn factorized_symmetry_rejects_unrepresentable_factor_id() {
    let pair = vec![Sym::new("limitA"), Sym::new("limitB")];
    let factors = vec![pair; usize::from(u16::MAX) + 2];
    let err = FactorizedGroup::new(factors, FallbackOrder::DisjointFull).err().expect("excess factor id accepted");
    assert!(err.message.contains("65537 factors"));
}
