use std::sync::Arc;

use tlx_value::{Sym, Value};

use super::*;
use crate::dynval;
use crate::layout::{decode, encode, rank, unrank, words};
use crate::shape::FcnWitness;
use crate::Shape;

fn mv(s: &str) -> Value {
    Value::ModelValue(Sym::new(s))
}

fn atoms(xs: &[&str]) -> Shape {
    let mut v: Vec<Value> = xs.iter().map(|x| mv(x)).collect();
    v.sort();
    Shape::Atom(v.into())
}

/// The swap a <-> b.
fn swap(a: &'static str, b: &'static str) -> AtomPerm {
    Arc::new(move |v: &Value| match v {
        Value::ModelValue(m) if m.as_str() == a => mv(b),
        Value::ModelValue(m) if m.as_str() == b => mv(a),
        _ => v.clone(),
    })
}

/// `plan(encode(v)) == encode(permute(v))` for every value of `shape`.
fn check_all(shape: &Shape, perm: &AtomPerm) {
    let plan = PermPlan::compile(shape, perm).expect("plan");
    let n = words(shape);
    let card = shape.cardinality().expect("finite shape");
    for r in 0..card {
        let v = unrank(shape, r);
        let mut src = vec![0u64; n];
        encode(shape, &v, &mut src).unwrap();
        let mut dst = vec![u64::MAX; n];
        plan.apply(&src, &mut dst);
        let want = tlx_value::ops::permute(&v, &|m| Some(perm(&Value::ModelValue(m)))).unwrap();
        let mut enc_want = vec![0u64; n];
        encode(shape, &want, &mut enc_want).unwrap();
        assert_eq!(dst, enc_want, "permuting {v} (got {})", decode(shape, &dst));
    }
}

#[test]
fn maps_permute_keys_and_values() {
    let a = atoms(&["a", "b", "c"]);
    let m = Shape::Map { key: Box::new(a.clone()), range: Box::new(a.clone()), witness: crate::FcnWitness::Enumerated };
    check_all(&m, &swap("a", "c"));
    let m2 = Shape::Map { key: Box::new(Shape::Int { lo: 0, hi: 2 }), range: Box::new(a.clone()), witness: crate::FcnWitness::Enumerated };
    check_all(&m2, &swap("a", "b"));
    // Dynamic-witness map preserves its trailing witness word under permutation.
    let md = Shape::Map { key: Box::new(a.clone()), range: Box::new(a.clone()), witness: crate::FcnWitness::Dynamic };
    let perm = swap("a", "c");
    let plan = PermPlan::compile(&md, &perm).unwrap();
    let v = Value::fcn_rcd_from_pairs(vec![(mv("a"), mv("b"))]).unwrap();
    let mut src = vec![0u64; words(&md)];
    encode(&md, &v, &mut src).unwrap();
    let mut dst = vec![u64::MAX; words(&md)];
    plan.apply(&src, &mut dst);
    let want = Value::fcn_rcd_from_pairs(vec![(mv("c"), mv("b"))]).unwrap();
    assert_eq!(decode(&md, &dst), want);
    assert!(matches!(decode(&md, &dst), Value::Fcn(_, tlx_value::FcnDom::Enumerated)));
    assert_eq!(dst[words(&md) - 1], 1);
}

#[test]
fn records_and_functions_flatten() {
    let a = atoms(&["a", "b"]);
    // Fields and domain in `Sym` order: the tests of this binary share
    // the intern table, so another test may have interned "b" or "y"
    // first.
    let mut fields = vec![(Sym::new("x"), a.clone()), (Sym::new("y"), Shape::Int { lo: 0, hi: 2 })];
    fields.sort_by_key(|f| f.0);
    let mut dom = vec![mv("a"), mv("b")];
    dom.sort();
    let r = Shape::Record(fields.into());
    let f = Shape::Fcn { dom: dom.into(), range: Box::new(r), witness: crate::FcnWitness::Enumerated, key_variants: Arc::from([]) };
    let p = PermPlan::compile(&f, &swap("a", "b")).unwrap();
    assert!(matches!(p, PermPlan::Flat(_)), "{p:?}");
    check_all(&f, &swap("a", "b"));
}

#[test]
fn unions_sets_and_sequences() {
    let a = atoms(&["a", "b", "c"]);
    let u = Shape::Union(vec![a.clone(), Shape::Record(vec![(Sym::new("n"), a.clone())].into())].into());
    check_all(&Shape::Seq { elem: Box::new(u.clone()), max_len: 2 }, &swap("a", "b"));
    check_all(&Shape::Set { elem: Box::new(a.clone()), max_card: 3 }, &swap("b", "c"));
    let pairs = Shape::Tuple(vec![a.clone(), Shape::Bool].into());
    check_all(&Shape::Set { elem: Box::new(pairs), max_card: 2 }, &swap("a", "c"));
}

#[test]
fn dyn_handles() {
    let perm = swap("a", "b");
    let plan = PermPlan::compile(&Shape::Dyn, &perm).unwrap();
    let v = Value::set_from(vec![mv("a"), mv("c")]).unwrap();
    let mut dst = [0u64];
    plan.apply(&[dynval::intern(&v)], &mut dst);
    assert_eq!(dynval::lookup(dst[0]), Value::set_from(vec![mv("b"), mv("c")]).unwrap());
}

#[test]
fn store_handles() {
    let store = crate::store::StoreRef::new(usize::MAX);
    let shape = Shape::Tuple(vec![Shape::Bool, Shape::Ref(store.clone())].into());
    let perm = swap("a", "b");
    let plan = PermPlan::compile(&shape, &perm).unwrap();
    let rec = |x: &str| Value::record(vec![(Sym::new("src"), mv(x)), (Sym::new("log"), Value::tuple(vec![mv("c"), mv(x)]))]);
    let bag = |x: &str, y: &str| {
        tlx_value::ops::fcn_merge(
            &tlx_value::ops::single_fcn(rec(x), Value::Int(1)).unwrap(),
            &tlx_value::ops::single_fcn(rec(y), Value::Int(2)).unwrap(),
        )
        .unwrap()
    };
    for (v, want) in [(bag("a", "c"), bag("b", "c")), (bag("b", "a"), bag("a", "b"))] {
        let src = [1, store.freeze(&v).unwrap()];
        let mut dst = [0u64; 2];
        plan.apply(&src, &mut dst);
        assert_eq!(dst[0], 1);
        // (The image is the permuted value as stored: same node, same
        // representation; memoized the second time.)
        assert_eq!(dst[1], store.freeze(&want).unwrap());
        assert_eq!(store.thaw(dst[1]), want);
        let mut again = [0u64; 2];
        plan.apply(&src, &mut again);
        assert_eq!(again, dst);
    }
}

#[test]
fn not_closed() {
    let a = atoms(&["a", "b"]);
    assert!(PermPlan::compile(&a, &swap("a", "c")).is_none());
}

fn sorted_syms(xs: &[&str]) -> Vec<Sym> {
    let mut s: Vec<Sym> = xs.iter().map(|x| Sym::new(x)).collect();
    s.sort_unstable();
    s
}

fn check_factor_all(shape: &Shape, fg: &FactorGroupSpec, img: &[u16]) {
    let plan = FactorPlan::compile(shape, fg).expect("factor plan");
    let n = words(shape);
    let card = shape.cardinality().expect("finite shape");
    for r in 0..card {
        let v = unrank(shape, r);
        let mut src = vec![0u64; n];
        encode(shape, &v, &mut src).unwrap();
        let mut dst = vec![u64::MAX; n];
        plan.apply(fg, img, &src, &mut dst);
        let want = tlx_value::ops::permute(&v, &|m| fg.map_sym(m, img).cloned()).unwrap();
        let mut enc_want = vec![0u64; n];
        encode(shape, &want, &mut enc_want).unwrap();
        assert_eq!(dst, enc_want, "factor permuting {v} (got {})", decode(shape, &dst));
    }
}

#[test]
fn factor_plans_cover_compound_shapes_and_rank_maps() {
    let k1 = sorted_syms(&["p1", "p2", "p3"]);
    let k2 = sorted_syms(&["q1", "q2"]);
    let fg = FactorGroupSpec::new(&[&k1, &k2]);
    // Cycle (0 1 2) on k1 and swap (0 1) on k2.
    let img = [1u16, 2, 0, 1, 0];

    let a1 = atoms(&["p1", "p2", "p3"]);
    let a2 = atoms(&["q1", "q2"]);
    let mixed = atoms(&["p1", "p2", "p3", "q1", "q2", "fixed"]);
    check_factor_all(&a1, &fg, &img);
    check_factor_all(&mixed, &fg, &img);
    check_factor_all(&Shape::Set { elem: Box::new(a1.clone()), max_card: 3 }, &fg, &img);
    check_factor_all(&Shape::Set { elem: Box::new(mixed.clone()), max_card: 3 }, &fg, &img);
    let pair = Shape::Tuple(vec![a1.clone(), Shape::Bool].into());
    check_factor_all(&Shape::Set { elem: Box::new(pair.clone()), max_card: 2 }, &fg, &img);
    check_factor_all(&Shape::Seq { elem: Box::new(a1.clone()), max_len: 2 }, &fg, &img);
    let mut rec_fields = vec![(Sym::new("a"), a1.clone()), (Sym::new("b"), a2.clone())];
    rec_fields.sort_by_key(|f| f.0);
    let rec = Shape::Record(rec_fields.into());
    check_factor_all(&rec, &fg, &img);
    let mut dom: Vec<Value> = k1.iter().copied().map(Value::ModelValue).collect();
    dom.sort();
    let fcn = Shape::Fcn { dom: dom.into(), range: Box::new(a2.clone()), witness: FcnWitness::Enumerated, key_variants: Arc::from([]) };
    check_factor_all(&fcn, &fg, &img);
    let map_atom = Shape::Map { key: Box::new(a1.clone()), range: Box::new(a2.clone()), witness: FcnWitness::Enumerated };
    check_factor_all(&map_atom, &fg, &img);
    let map_pair = Shape::Map { key: Box::new(pair), range: Box::new(Shape::Int { lo: 0, hi: 1 }), witness: FcnWitness::Enumerated };
    check_factor_all(&map_pair, &fg, &img);
    let u = Shape::Union(vec![a1.clone(), Shape::Record(vec![(Sym::new("n"), a2.clone())].into())].into());
    check_factor_all(&u, &fg, &img);
    // Set with Comb rank (max_card < universe) inside a bitset.
    let sub_set = Shape::Set { elem: Box::new(a1.clone()), max_card: 2 };
    let rp = RankPlan::compile(&sub_set, &fg).unwrap();
    for r in 0..sub_set.cardinality().unwrap() {
        let v = unrank(&sub_set, r);
        let want = tlx_value::ops::permute(&v, &|m| fg.map_sym(m, &img).cloned()).unwrap();
        assert_eq!(rp.map_rank(&fg, &img, r), rank(&sub_set, &want).unwrap());
    }
    // Not closed under fg: partial factor rejected.
    let partial = atoms(&["p1", "p2"]);
    assert!(FactorPlan::compile(&partial, &fg).is_none());
}

#[test]
fn deep_nested_product_plan_is_linear_in_depth() {
    fn count_nodes(plan: &FactorPlan) -> usize {
        match plan {
            FactorPlan::Product { fields, .. } => 1 + fields.iter().map(|(_, p)| count_nodes(p)).sum::<usize>(),
            _ => 1,
        }
    }
    let k = sorted_syms(&["a1", "a2"]);
    let fg = FactorGroupSpec::new(&[&k]);
    let mut s = atoms(&["a1", "a2"]);
    // Depth 24 would take ~2^24 (~16M) nodes if units cloned child plans.
    for _ in 0..24 {
        s = Shape::Tuple(vec![s].into());
    }
    let plan = FactorPlan::compile(&s, &fg).expect("nested tuple plan");
    assert_eq!(count_nodes(&plan), 25, "nested product plan must be O(depth) with no cloned subtrees");
    // Verify execution under swap (a1 <-> a2).
    let layout = crate::Layout::new(vec![s]);
    let mut v = Value::ModelValue(k[0]);
    let mut want = Value::ModelValue(k[1]);
    for _ in 0..24 {
        v = Value::tuple(vec![v]);
        want = Value::tuple(vec![want]);
    }
    let mut src = vec![0u64; layout.words];
    let mut dst = vec![0u64; layout.words];
    layout.encode_state(&[v], &mut src).unwrap();
    plan.apply(&fg, &[1, 0], &src, &mut dst);
    assert_eq!(layout.decode_state(&dst)[0], want);
}

#[test]
fn apply_orbit_dyn_does_not_intern_candidates() {
    fn has_probe_sym(v: &Value, syms: &[Sym]) -> bool {
        match v {
            Value::ModelValue(m) => syms.contains(m),
            Value::Set(es) | Value::Tuple(es) => es.iter().any(|e| has_probe_sym(e, syms)),
            Value::Record(fs) => fs.iter().any(|(_, e)| has_probe_sym(e, syms)),
            Value::Fcn(ps, _) => ps.iter().any(|(k, e)| has_probe_sym(k, syms) || has_probe_sym(e, syms)),
            _ => false,
        }
    }
    let keys: Vec<Sym> = (1..=8).map(|i| Sym::new(&format!("dyn_probe_layout_{i}"))).collect();
    let mut sorted = keys.clone();
    sorted.sort_unstable();
    let fg = FactorGroupSpec::new(&[&sorted]);
    let plan = FactorPlan::compile(&Shape::Dyn, &fg).expect("Dyn plan");
    assert!(plan.has_dyn());
    let tup = Value::tuple(sorted.iter().copied().map(Value::ModelValue).collect());
    let h = dynval::intern(&tup);
    let probe_count = || -> usize { dynval::snapshot().iter().flat_map(|s| s.iter()).filter(|v| has_probe_sym(v, &sorted)).count() };
    assert_eq!(probe_count(), 1, "only the pre-interned base tuple should exist in dynval");
    let mut dst = [0u64; 1];
    let mut img = fg.identity_img();
    for k in 0..sorted.len() - 1 {
        img.swap(k, k + 1);
        // SAFETY: `h` came from `dynval::intern` on this thread.
        unsafe { plan.apply_orbit_unchecked(&fg, &img, &[h], &mut dst) };
        img.swap(k, k + 1);
    }
    assert_eq!(probe_count(), 1, "apply_orbit_unchecked on Dyn must not intern losing candidates");
}

#[test]
fn orbit_closure_in_nested_map_preserves_fixed_atoms_and_separate_factors() {
    let mut servers = ["s1", "s2", "s3", "s4"].map(Sym::new);
    let mut clients = ["c1", "c2"].map(Sym::new);
    servers.sort();
    clients.sort();
    let factors = [&servers[..], &clients[..]];
    let shape = |server, client| {
        let record = |name, field| Shape::Record(vec![(Sym::new(name), field)].into());
        let key = record("dest", server).join(&record("sender", client));
        crate::shape::map_shape(key, crate::shape::set_shape(atoms(&["c1", "fixed"]), 2), FcnWitness::Enumerated)
    };
    let observed = shape(atoms(&["s1", "s2", "s3"]), atoms(&["c1"]));
    let group = FactorGroupSpec::new(&factors);
    assert!(FactorPlan::compile(&observed, &group).is_none());
    let closed = AtomOrbits::from_factors(&factors).close(&observed);
    let Shape::Map { key, range, .. } = &closed else { panic!("expected map") };
    let Shape::Map { key: expected, .. } = shape(atoms(&["s1", "s2", "s3", "s4"]), atoms(&["c1", "c2"])) else { unreachable!() };
    assert_eq!(key, &expected);
    assert_eq!(**range, crate::shape::set_shape(atoms(&["c1", "c2", "fixed"]), 2));
    assert!(FactorPlan::compile(&closed, &group).is_some());
}

#[test]
fn explicit_cyclic_orbit_closes_only_intersecting_universes() {
    let cycle = ["a", "b", "c"].map(Sym::new);
    let maps: Vec<std::collections::HashMap<_, _>> =
        [1, 2].map(|step| (0..3).map(|i| (cycle[i], Value::ModelValue(cycle[(i + step) % 3]))).collect()).into();
    let orbits = AtomOrbits::from_group(&maps);
    let closed = orbits.close(&atoms(&["b", "fixed"]));
    assert_eq!(closed, atoms(&["a", "b", "c", "fixed"]));
    assert_eq!(orbits.close(&atoms(&["fixed"])), atoms(&["fixed"]));
    for map in maps {
        let perm: AtomPerm = Arc::new(move |v| match v {
            Value::ModelValue(s) => map.get(s).unwrap_or(v).clone(),
            _ => v.clone(),
        });
        check_all(&closed, &perm);
    }
}
