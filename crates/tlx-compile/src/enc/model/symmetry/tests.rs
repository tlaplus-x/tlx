//! Unit tests for encoded-word `SYMMETRY` canonicalization.

use std::sync::Arc;

use tlx_base::partition::Partition;
use tlx_layout::permute::{AtomPerm, FactorGroupSpec, FactorPlan, PermPlan};
use tlx_layout::{FcnWitness, Layout, Shape};
use tlx_testkit::spec::load;
use tlx_value::{Sym, Value};

use crate::enc::model::{EncModel, SemFp};
use crate::settings::Settings;

use super::branch::branch_single_word;
use super::order::{WordOrder, WorkItem};
use super::refine::FactorScratch;
use super::{apply_factor_img, least_perm_words_factorized, orbit_fp_explicit, orbit_fp_factorized, FactorSymmetry};

use super::*;

fn mv(s: &str) -> Value {
    Value::ModelValue(Sym::new(s))
}

fn atom_shape(xs: &[&str]) -> Shape {
    let mut v: Vec<Value> = xs.iter().map(|s| mv(s)).collect();
    v.sort();
    Shape::Atom(v.into())
}

fn build_explicit_group(fg: &FactorGroupSpec, layout: &Layout) -> Vec<Vec<PermPlan>> {
    fn lex_perms(n: usize) -> Vec<Vec<u16>> {
        let mut cur: Vec<u16> = (0..n as u16).collect();
        let mut out = Vec::new();
        loop {
            out.push(cur.clone());
            if n < 2 {
                break;
            }
            let mut i = n - 2;
            while cur[i] >= cur[i + 1] {
                if i == 0 {
                    return out;
                }
                i -= 1;
            }
            let mut j = n - 1;
            while cur[j] <= cur[i] {
                j -= 1;
            }
            cur.swap(i, j);
            cur[i + 1..].reverse();
        }
        out
    }
    let per_factor: Vec<Vec<Vec<u16>>> = fg.factors.iter().map(|f| lex_perms(f.keys.len())).collect();
    let mut imgs: Vec<Vec<u16>> = vec![vec![0u16; fg.total_keys]];
    for (g, perms) in per_factor.iter().enumerate() {
        let off = fg.factors[g].offset;
        let mut next = Vec::with_capacity(imgs.len() * perms.len());
        for base in &imgs {
            for p in perms {
                let mut v = base.clone();
                v[off..off + p.len()].copy_from_slice(p);
                next.push(v);
            }
        }
        imgs = next;
    }
    let id = fg.identity_img();
    let mut group = Vec::new();
    for img in imgs {
        if img == id {
            continue;
        }
        let fg_c = fg.clone();
        let perm: AtomPerm = Arc::new(move |v: &Value| {
            tlx_value::SymAtom::from_value(v).and_then(|atom| fg_c.map_atom(atom, &img)).cloned().unwrap_or_else(|| v.clone())
        });
        let plans: Vec<PermPlan> = layout.vars.iter().map(|s| PermPlan::compile(s, &perm).unwrap()).collect();
        group.push(plans);
    }
    group
}

#[test]
fn factorized_orbit_fp_matches_explicit_across_all_shapes() {
    for atom in [SymAtom::Model as fn(Sym) -> SymAtom, SymAtom::Str] {
        check_compound_orbits(atom);
    }
}

fn check_compound_orbits(atom: fn(Sym) -> SymAtom) {
    let mv = |name: &str| atom(Sym::new(name)).to_value();
    let atom_shape = |names: &[&str]| {
        let mut values: Vec<_> = names.iter().map(|name| mv(name)).collect();
        values.sort();
        Shape::Atom(values.into())
    };
    let mut k1 = [Sym::new("a1"), Sym::new("a2"), Sym::new("a3")];
    k1.sort_unstable();
    let mut k2 = [Sym::new("b1"), Sym::new("b2")];
    k2.sort_unstable();
    let fg = FactorGroupSpec::new(&[&k1.iter().copied().map(atom).collect::<Vec<_>>(), &k2.iter().copied().map(atom).collect::<Vec<_>>()]);

    let s_a = atom_shape(&["a1", "a2", "a3"]);
    let s_b = atom_shape(&["b1", "b2"]);
    let mut s_a_nil_vals = vec![mv("a1"), mv("a2"), mv("a3"), mv("nil")];
    s_a_nil_vals.sort();
    let s_a_nil = Shape::Atom(s_a_nil_vals.into());

    let mut dom_a: Vec<Value> = k1.iter().copied().map(|s| atom(s).to_value()).collect();
    dom_a.sort();

    // 0: packed Record with branching field followed by packed Atom (tests PendingItem::PackedAtom)
    let fcn_a_to_a = Shape::Fcn {
        dom: dom_a.clone().into(),
        range: Box::new(s_a_nil.clone()),
        witness: FcnWitness::Enumerated,
        key_variants: Arc::from([]),
    };
    let mut rec_fields = vec![(Sym::new("aa_fcn"), fcn_a_to_a.clone()), (Sym::new("zz_tail"), s_b.clone())];
    rec_fields.sort_by_key(|f| f.0);
    let rec_shape = Shape::Record(rec_fields.into());

    // 1: Fcn with word-aligned Record payload (Case A + bulk classes)
    let mut inner_fields = vec![(Sym::new("m"), Shape::Int { lo: 0, hi: 2 }), (Sym::new("p"), s_b.clone())];
    inner_fields.sort_by_key(|f| f.0);
    let fcn_words = Shape::Fcn {
        dom: dom_a.clone().into(),
        range: Box::new(Shape::Record(inner_fields.into())),
        witness: FcnWitness::Dynamic,
        key_variants: Arc::from([]),
    };

    // 2: Map keyed by DirectFactor(0) with packed Atom range
    let map_direct = Shape::Map { key: Box::new(s_a.clone()), range: Box::new(s_b.clone()), witness: FcnWitness::Enumerated };

    // 3: Bitset over compound Tuple(Atom, Bool) (BitsetRank -> Case B)
    let pair_shape = Shape::Tuple(vec![s_a.clone(), Shape::Bool].into());
    let bitset_pair = Shape::Set { elem: Box::new(pair_shape), max_card: 4 };

    // 4: SeqBits over K_1
    let seq_bits = Shape::Seq { elem: Box::new(s_a.clone()), max_len: 3 };

    // 5: Nested Ref inside Tuple(Bool, Ref)
    let store = tlx_layout::store::StoreRef::new(usize::MAX);
    let nested_ref = Shape::Tuple(vec![Shape::Bool, Shape::Ref(store.clone())].into());

    let layout = Layout::new(vec![rec_shape, fcn_words, map_direct, bitset_pair, seq_bits, nested_ref]);
    let plans: Vec<FactorPlan> = layout.vars.iter().map(|s| FactorPlan::compile(s, &fg).unwrap()).collect();
    let fsym = FactorSymmetry::new(fg.clone(), plans, &layout);
    let explicit = build_explicit_group(&fg, &layout);
    let sem = SemFp::of(&layout, None);

    let f_rec = |x: i64, p: &str| Value::record(vec![(Sym::new("m"), Value::Int(x)), (Sym::new("p"), mv(p))]);
    let states: Vec<Vec<Value>> = vec![
        vec![
            Value::record(vec![
                (
                    Sym::new("aa_fcn"),
                    Value::fcn_rcd_from_pairs(vec![(mv("a1"), mv("a2")), (mv("a2"), mv("nil")), (mv("a3"), mv("a1"))]).unwrap(),
                ),
                (Sym::new("zz_tail"), mv("b2")),
            ]),
            Value::fcn_rcd_from_pairs(vec![(mv("a1"), f_rec(1, "b2")), (mv("a2"), f_rec(0, "b1")), (mv("a3"), f_rec(0, "b1"))]).unwrap(),
            Value::fcn_rcd_from_pairs(vec![(mv("a2"), mv("b2")), (mv("a3"), mv("b1"))]).unwrap(),
            Value::set_from(vec![Value::tuple(vec![mv("a2"), Value::Bool(true)]), Value::tuple(vec![mv("a3"), Value::Bool(false)])])
                .unwrap(),
            Value::tuple(vec![mv("a3"), mv("a1")]),
            Value::tuple(vec![Value::Bool(true), Value::set_from(vec![mv("a3"), mv("b2")]).unwrap()]),
        ],
        // Tied bulk identical payloads + self-identity map
        vec![
            Value::record(vec![
                (
                    Sym::new("aa_fcn"),
                    Value::fcn_rcd_from_pairs(vec![(mv("a1"), mv("a1")), (mv("a2"), mv("a2")), (mv("a3"), mv("a3"))]).unwrap(),
                ),
                (Sym::new("zz_tail"), mv("b1")),
            ]),
            Value::fcn_rcd_from_pairs(vec![(mv("a1"), f_rec(0, "b2")), (mv("a2"), f_rec(0, "b2")), (mv("a3"), f_rec(0, "b2"))]).unwrap(),
            Value::fcn_rcd_from_pairs(vec![]).unwrap(),
            Value::set_from(vec![]).unwrap(),
            Value::tuple(vec![]),
            Value::tuple(vec![Value::Bool(false), Value::tuple(vec![mv("a2"), mv("b1")])]),
        ],
    ];

    for st in &states {
        let mut words = vec![0u64; layout.words];
        layout.encode_state(st, &mut words).unwrap();
        let got = orbit_fp_factorized(&fsym, &layout, &words, sem.as_ref());
        let want = orbit_fp_explicit(&explicit, &fsym.orbit_order, &layout, &words, sem.as_ref(), None).unwrap();
        assert_eq!(got, want, "factorized orbit_fp must equal exhaustive explicit orbit_fp");

        // Every group element must produce the identical orbit fingerprint.
        for p_plans in &explicit {
            let mut permuted = vec![0u64; layout.words];
            for (i, plan) in p_plans.iter().enumerate() {
                let r = layout.var_range(i);
                plan.apply(&words[r.clone()], &mut permuted[r]);
            }
            let p_fp = orbit_fp_factorized(&fsym, &layout, &permuted, sem.as_ref());
            assert_eq!(p_fp, got, "orbit_fp must be invariant across the entire S_3 x S_2 orbit");
        }
    }
}

#[test]
fn wide_two_word_bitset_is_orbit_invariant() {
    let mut keys: Vec<Sym> = (0..6).map(|i| Sym::new(&format!("m{i}"))).collect();
    keys.sort_unstable();
    let fg = FactorGroupSpec::new(&[&model_atoms(&keys)]);
    let mut univ: Vec<Value> = (0..64).map(|i| Value::Str(Sym::new(&format!("f{i:02}")))).collect();
    univ.extend(keys.iter().copied().map(Value::ModelValue));
    univ.sort();
    let set_shape = Shape::Set { elem: Box::new(Shape::Atom(univ.into())), max_card: 8 };
    let layout = Layout::new(vec![set_shape]);
    assert!(layout.words >= 2, "must exercise multi-word bitset");
    let plans = vec![FactorPlan::compile(&layout.vars[0], &fg).unwrap()];
    let fsym = FactorSymmetry::new(fg.clone(), plans, &layout);
    assert!(fsym.wide_bitset[0]);

    let st = vec![Value::set_from(vec![
        Value::Str(Sym::new("f00")),
        Value::ModelValue(keys[1]),
        Value::ModelValue(keys[4]),
        Value::ModelValue(keys[5]),
    ])
    .unwrap()];
    let mut words = vec![0u64; layout.words];
    layout.encode_state(&st, &mut words).unwrap();
    let base_fp = orbit_fp_factorized(&fsym, &layout, &words, None);

    let mut img = fg.identity_img();
    let mut swapped = vec![0u64; layout.words];
    for k in 0..keys.len() - 1 {
        img[k] = (k + 1) as u16;
        img[k + 1] = k as u16;
        apply_factor_img(&fsym, &layout, &img, &words, &mut swapped);
        assert_eq!(orbit_fp_factorized(&fsym, &layout, &swapped, None), base_fp);
        img[k] = k as u16;
        img[k + 1] = (k + 1) as u16;
    }
}

#[test]
fn large_groups_above_720_compile_to_factorized_word_engine() {
    let src = r#"---- MODULE LargeFactor ----
EXTENDS Naturals, TLC
CONSTANTS P, Q, R
VARIABLES x, f
Sym == Permutations(P) \cup Permutations(Q) \cup Permutations(R)
V == <<x, f>>
Init == x \in P /\ f = [q \in Q |-> [r \in R |-> 0]]
Next == UNCHANGED <<x, f>>
===="#;
    let cfg_noview = "CONSTANTS P = {p1,p2,p3,p4} Q = {q1,q2,q3,q4} R = {r1,r2,r3}\nINIT Init\nNEXT Next\nSYMMETRY Sym\n";
    let cfg_view = format!("{cfg_noview}VIEW V\n");
    let p_shape = atom_shape(&["p1", "p2", "p3", "p4"]);
    let mut q_dom: Vec<Value> = ["q1", "q2", "q3", "q4"].iter().map(|s| mv(s)).collect();
    q_dom.sort();
    let mut r_dom: Vec<Value> = ["r1", "r2", "r3"].iter().map(|s| mv(s)).collect();
    r_dom.sort();
    let f_shape = Shape::Fcn {
        dom: q_dom.into(),
        range: Box::new(Shape::Fcn {
            dom: r_dom.into(),
            range: Box::new(Shape::Int { lo: 0, hi: 1 }),
            witness: FcnWitness::Enumerated,
            key_variants: Arc::from([]),
        }),
        witness: FcnWitness::Enumerated,
        key_variants: Arc::from([]),
    };
    let settings = Settings::from_lookup(|k| match k {
        "TLX_NO_NATIVE" | "TLX_PARANOID" => Some("1".into()),
        _ => None,
    })
    .unwrap();

    let base_nv = Arc::new(load(src, cfg_noview));
    assert!(base_nv.symmetry_maps().is_empty(), "4!*4!*3! = 3456 > 720 must not materialize symmetry_maps");
    let model_nv = EncModel::new(base_nv, Arc::new(Layout::new(vec![p_shape.clone(), f_shape.clone()])), vec![], &settings);
    assert!(
        matches!(model_nv.fp, super::super::fingerprint::Fingerprint::Symmetry { engine: SymmetryEngine::Factorized(_), .. }),
        "expected factorized Symmetry engine for |G|=3456"
    );

    let base_v = Arc::new(load(src, &cfg_view));
    let view_def = crate::enc::speculate::view_def(&base_v).unwrap();
    let view_shape = Shape::Tuple(vec![p_shape.clone(), f_shape.clone()].into());
    let model_v = EncModel::new(base_v, Arc::new(Layout::new(vec![p_shape, f_shape])), vec![(view_def, view_shape)], &settings);
    assert!(
        matches!(model_v.fp, super::super::fingerprint::Fingerprint::SymView { engine: SymmetryEngine::Factorized(_), .. }),
        "expected factorized SymView engine for |G|=3456"
    );
}

#[test]
fn sym_view_dynamic_witness_ties_preserve_least_representative_inline_and_heap() {
    // Test both inline (`n = 3 <= INLINE_KEYS`) and heap (`n = 18 > INLINE_KEYS`)
    // bulk-class paths in `dfs_words` when payloads compare equal in TLC order
    // (and Orbit order) despite differing dynamic function-domain witness words.
    for n in [3usize, 18usize] {
        let mut k_a: Vec<Sym> = (1..=n).map(|i| Sym::new(&format!("a{i:02}"))).collect();
        k_a.sort_unstable();
        let mut k_b = vec![Sym::new("b1"), Sym::new("b2")];
        k_b.sort_unstable();
        let fg = FactorGroupSpec::new(&[&model_atoms(&k_a), &model_atoms(&k_b)]);

        let dom_a: Vec<Value> = k_a.iter().copied().map(Value::ModelValue).collect();
        let s_a = Shape::Atom(dom_a.clone().into());
        let s_b = atom_shape(&["b1", "b2"]);
        let inner_fcn = Shape::Fcn {
            dom: vec![Value::Int(1), Value::Int(2)].into(),
            range: Box::new(s_b.clone()),
            witness: FcnWitness::Dynamic,
            key_variants: Arc::from([]),
        };
        let x_shape = Shape::Fcn {
            dom: dom_a.clone().into(),
            range: Box::new(inner_fcn),
            witness: FcnWitness::Enumerated,
            key_variants: Arc::from([]),
        };
        let y_shape = Shape::Seq { elem: Box::new(s_a), max_len: n };

        let layout = Layout::new(vec![x_shape, y_shape]);
        let plans: Vec<FactorPlan> = layout.vars.iter().map(|s| FactorPlan::compile(s, &fg).unwrap()).collect();
        let fsym = FactorSymmetry::new(fg.clone(), plans, &layout);
        assert!(fsym.all_orbit_cmp_safe, "dynamic-witness Fcn + Seq must be orbit_cmp_safe");

        // Interval-witness vs enumerated-witness functions over 1..2 -> b2:
        // distinct raw witness words, semantically equal in TLC order.
        let f_interval = Value::fcn_from_pairs(vec![(Value::Int(1), mv("b2")), (Value::Int(2), mv("b2"))]).unwrap();
        let f_enum = Value::fcn_rcd_from_pairs(vec![(Value::Int(1), mv("b2")), (Value::Int(2), mv("b2"))]).unwrap();
        assert_eq!(f_interval, f_enum);

        let x_pairs: Vec<(Value, Value)> =
            dom_a.iter().enumerate().map(|(i, a)| (a.clone(), if i == 1 { f_enum.clone() } else { f_interval.clone() })).collect();
        let x_val = Value::fcn_rcd_from_pairs(x_pairs).unwrap();

        // 1) Already-least `y = <<a01, a02, ..., aN>>` must keep `y` untouched
        //    while minimizing `b2 -> b1` in `x`.
        let y_least = Value::tuple(dom_a.clone());
        let mut words = vec![0u64; layout.words];
        layout.encode_state(&[x_val.clone(), y_least.clone()], &mut words).unwrap();
        let mut best = Vec::new();
        let non_id = least_perm_words_factorized(&fsym, &[0, 1], &layout, &words, &mut best).expect("word-level SymView");
        assert!(non_id, "b2 must be mapped to b1");
        let dec = layout.decode_state(&best);
        assert_eq!(dec[1], y_least, "n={n}: bulk witness-tie grouping must not permute already-least y");

        // 2) Swapping positions 0 and 1 in `y` (moving the enumerated-witness
        //    entry across the tie) must still map back to `y_least`.
        let mut y_swapped_elems = dom_a.clone();
        y_swapped_elems.swap(0, 1);
        let y_swapped = Value::tuple(y_swapped_elems);
        layout.encode_state(&[x_val, y_swapped], &mut words).unwrap();
        let non_id2 = least_perm_words_factorized(&fsym, &[0, 1], &layout, &words, &mut best).expect("word-level SymView");
        assert!(non_id2);
        let dec2 = layout.decode_state(&best);
        assert_eq!(dec2[1], y_least, "n={n}: swapped y must canonicalize to the same least representative");
        assert_eq!(dec2, dec, "n={n}: both states in the orbit must select the identical least state");
    }
}

#[test]
fn orbit_fp_dyn_s8_is_generator_invariant_and_interns_zero_entries() {
    fn has_probe_sym(v: &Value, syms: &[Sym]) -> bool {
        match v {
            Value::ModelValue(m) => syms.contains(m),
            Value::Set(es) | Value::Tuple(es) => es.iter().any(|e| has_probe_sym(e, syms)),
            Value::Record(fs) => fs.iter().any(|(_, e)| has_probe_sym(e, syms)),
            Value::Fcn(ps, _) => ps.iter().any(|(k, e)| has_probe_sym(k, syms) || has_probe_sym(e, syms)),
            _ => false,
        }
    }
    let mut keys: Vec<Sym> = (1..=8).map(|i| Sym::new(&format!("dyn_probe_compile_s8_{i}"))).collect();
    keys.sort_unstable();
    let fg = FactorGroupSpec::new(&[&model_atoms(&keys)]);
    let layout = Layout::new(vec![Shape::Dyn]);
    let plans = vec![FactorPlan::compile(&Shape::Dyn, &fg).unwrap()];
    let fsym = FactorSymmetry::new(fg.clone(), plans, &layout);
    assert!(fsym.has_dyn);
    let sem = SemFp::of(&layout, None);

    // Pre-intern the base tuple and its 7 adjacent-transposition generator
    // images BEFORE measuring probe-attributed entries in `dynval`.
    let base_tup = Value::tuple(keys.iter().copied().map(Value::ModelValue).collect());
    let mut base_words = vec![0u64; layout.words];
    layout.encode_state(&[base_tup], &mut base_words).unwrap();

    let mut gen_states: Vec<Vec<u64>> = Vec::new();
    let mut img = fg.identity_img();
    for k in 0..keys.len() - 1 {
        img.swap(k, k + 1);
        let mut buf = Vec::new();
        apply_factor_img(&fsym, &layout, &img, &base_words, &mut buf);
        gen_states.push(buf);
        img.swap(k, k + 1);
    }

    let probe_count =
        || -> usize { tlx_layout::dynval::snapshot().iter().flat_map(|s| s.iter()).filter(|v| has_probe_sym(v, &keys)).count() };
    let before = probe_count();
    assert_eq!(before, 8, "expected exactly base + 7 generator tuples before orbit_fp");
    let base_fp = orbit_fp_factorized(&fsym, &layout, &base_words, sem.as_ref());
    assert_eq!(probe_count(), before, "orbit_fp_factorized on Dyn S_8 must intern 0 probe entries (not 8! = 40,320)");
    for (k, swapped) in gen_states.iter().enumerate() {
        let fp = orbit_fp_factorized(&fsym, &layout, swapped, sem.as_ref());
        assert_eq!(fp, base_fp, "orbit_fp_factorized on Dyn S_8 must be invariant under generator swap ({k}, {})", k + 1);
    }
    assert_eq!(probe_count(), before, "all generator checks of orbit_fp_factorized on Dyn S_8 must intern 0 probe entries");
}

#[test]
fn uniform_dyn_fcn_keeps_single_unpinned_block_as_domain_grows() {
    // Verifies that `Fcn(K_a -> Dyn)` where all keys hold the same value
    // (or TLA+-equal values with distinct `intern_exact` handles) keeps the
    // entire `K_a` domain in ONE unpinned block instead of retaining `n!`
    // tied partitions — across both inline (`n = 10`) and heap (`n = 18`)
    // bulk-class paths.
    for n in [10usize, 18usize] {
        let mut k_a: Vec<Sym> = (1..=n).map(|i| Sym::new(&format!("ud_a{i:02}"))).collect();
        k_a.sort_unstable();
        let mut k_b = vec![Sym::new("ud_b1"), Sym::new("ud_b2")];
        k_b.sort_unstable();
        let fg = FactorGroupSpec::new(&[&model_atoms(&k_a), &model_atoms(&k_b)]);

        let dom_a: Vec<Value> = k_a.iter().copied().map(Value::ModelValue).collect();
        let fcn_dyn = Shape::Fcn {
            dom: dom_a.clone().into(),
            range: Box::new(Shape::Dyn),
            witness: FcnWitness::Enumerated,
            key_variants: Arc::from([]),
        };
        let layout = Layout::new(vec![fcn_dyn]);
        let plans = vec![FactorPlan::compile(&layout.vars[0], &fg).unwrap()];
        let fsym = FactorSymmetry::new(fg.clone(), plans, &layout);
        let sem = SemFp::of(&layout, None);

        // Mix identical handles and a semantically-equal `intern_exact`
        // handle (interval vs enumerated function over 1..2 -> ud_b2).
        let v_int =
            Value::fcn_from_pairs(vec![(Value::Int(1), Value::ModelValue(k_b[1])), (Value::Int(2), Value::ModelValue(k_b[1]))]).unwrap();
        let v_enum =
            Value::fcn_rcd_from_pairs(vec![(Value::Int(1), Value::ModelValue(k_b[1])), (Value::Int(2), Value::ModelValue(k_b[1]))])
                .unwrap();
        assert_eq!(v_int, v_enum);

        let pairs: Vec<(Value, Value)> =
            dom_a.iter().enumerate().map(|(i, a)| (a.clone(), if i == 1 { v_enum.clone() } else { v_int.clone() })).collect();
        let f_val = Value::fcn_rcd_from_pairs(pairs).unwrap();
        let mut words = vec![0u64; layout.words];
        layout.encode_state(&[f_val], &mut words).unwrap();

        // Directly inspect `branch_single_word`: must return 1 partition
        // with `K_a` completely unpinned (`[0..n)`) rather than `n!` partitions.
        let mut scratch = FactorScratch::default();
        let mut part = Partition::default();
        part.reset(&fg);
        let mut canon = vec![0u64; layout.words];
        // SAFETY: valid encoded words from `layout.encode_state`.
        unsafe { fsym.plans[0].apply_orbit_unchecked(&fg, &fsym.id_img, &words, &mut canon) };
        let item = WorkItem { plan: &fsym.plans[0], node: layout.node(0), raw: &words, canon: &canon, wide_bitset: false };
        let cands = branch_single_word(&fg, part, item, WordOrder::Orbit, &mut scratch);
        assert_eq!(cands.len(), 1, "n={n}: uniform Dyn payloads must collapse to 1 candidate, not n!");
        assert_eq!(cands[0].block_lo()[0], 0, "n={n}: domain block must start at 0");
        assert_eq!(cands[0].block_hi()[0] as usize, n, "n={n}: entire domain must stay a single free block [0..n)");

        // Verify `orbit_fp_factorized` is invariant under swaps of both factors.
        let base_fp = orbit_fp_factorized(&fsym, &layout, &words, sem.as_ref());
        let mut img = fg.identity_img();
        let mut swapped = Vec::new();
        img.swap(0, 1);
        apply_factor_img(&fsym, &layout, &img, &words, &mut swapped);
        assert_eq!(orbit_fp_factorized(&fsym, &layout, &swapped, sem.as_ref()), base_fp);
        img.swap(0, 1);
        let boff = fg.factors[1].offset;
        img.swap(boff, boff + 1);
        apply_factor_img(&fsym, &layout, &img, &words, &mut swapped);
        assert_eq!(orbit_fp_factorized(&fsym, &layout, &swapped, sem.as_ref()), base_fp);
    }
}

fn model_atoms(keys: &[Sym]) -> Vec<tlx_value::SymAtom> {
    keys.iter().copied().map(tlx_value::SymAtom::Model).collect()
}

#[test]
fn string_symmetry_least_words_agree_with_interpreter() {
    let src = tlx_testkit::module("StringOrbit", "VARIABLE x\nInit == x = TRUE\nNext == UNCHANGED x");
    for size in [2, 3] {
        let mut model = load(&src, "INIT Init\nNEXT Next\n");
        let symbols = ["t_a", "t_b", "t_c"].map(Sym::new);
        let atoms: Vec<_> = symbols[..size].iter().copied().map(SymAtom::Str).collect();
        model
            .apply_symmetry(atoms.windows(2).map(|w| HashMap::from([(w[0], w[1].to_value()), (w[1], w[0].to_value())])).collect())
            .unwrap();
        let shape = Shape::Atom(atoms.iter().map(|a| a.to_value()).collect());
        let pair = Shape::Tuple(vec![shape.clone(), Shape::Int { lo: 1, hi: 1 }].into());
        let set = Shape::Set { elem: Box::new(pair), max_card: size };
        let layout = Layout::new(vec![Shape::Tuple(vec![set, shape, Shape::Atom(vec![Value::ModelValue(symbols[0])].into())].into())]);
        let fg = FactorGroupSpec::new(&[&atoms]);
        let fsym = FactorSymmetry::new(fg.clone(), vec![FactorPlan::compile(&layout.vars[0], &fg).unwrap()], &layout);
        let explicit = build_explicit_group(&fg, &layout);
        let pairs = Value::set_from(atoms.iter().map(|a| Value::tuple(vec![a.to_value(), Value::Int(1)])).collect()).unwrap();
        let state_with = |a: SymAtom| vec![Value::tuple(vec![pairs.clone(), a.to_value(), Value::ModelValue(symbols[0])])];
        for atom in &atoms {
            let state = state_with(*atom);
            let expected = state_with(atoms[0]);
            assert_eq!(model.least_state_in_orbit(&state).unwrap().unwrap_or_else(|| state.clone()), expected);
            let mut words = vec![0; layout.words];
            layout.encode_state(&state, &mut words).unwrap();
            let mut best = Vec::new();
            let moved = least_perm_words_factorized(&fsym, &[0], &layout, &words, &mut best).unwrap();
            assert_eq!(layout.decode_state(if moved { &best } else { &words }), expected);
            let mut canonical = vec![0; layout.words];
            layout.encode_state(&expected, &mut canonical).unwrap();
            assert_eq!(orbit_fp_factorized(&fsym, &layout, &words, None), fp_words(&canonical));
            assert_eq!(orbit_fp_explicit(&explicit, &[0], &layout, &words, None, None).unwrap(), fp_words(&canonical));
        }
    }
}
