//! Unit tests for shapes, rank/unrank and the fixed-width encoding.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use tlx_layout::infer::{widen, widen_int, widen_repeated, Hints, Observer};
use tlx_layout::layout::{decode, encode, rank, unrank, words};
use tlx_layout::shape::{KindKey, MAX_UNION_ARMS};
use tlx_layout::{dynval, FcnWitness, Layout, Shape};
use tlx_value::{Sym, Value};

// ---------------------------------------------------------------------------
// Helpers

fn int(n: i64) -> Value {
    Value::Int(n)
}
fn st(s: &str) -> Value {
    Value::str(s)
}
fn mv(s: &str) -> Value {
    Value::model_value(s)
}
fn set(mut es: Vec<Value>) -> Value {
    es.sort();
    es.dedup();
    Value::Set(Arc::from(es))
}
fn tup(es: Vec<Value>) -> Value {
    Value::tuple(es)
}
fn rec(fs: &[(&str, Value)]) -> Value {
    Value::record(fs.iter().map(|(k, v)| (Sym::new(k), v.clone())).collect())
}
fn fcn(ps: Vec<(Value, Value)>) -> Value {
    Value::fcn_from_pairs(ps).unwrap()
}

fn sint(lo: i64, hi: i64) -> Shape {
    Shape::Int { lo, hi }
}
fn satom(vs: Vec<Value>) -> Shape {
    let mut vs = vs;
    vs.sort();
    vs.dedup();
    Shape::Atom(Arc::from(vs))
}
fn sset(elem: Shape, max_card: usize) -> Shape {
    Shape::Set { elem: Box::new(elem), max_card }
}
fn sseq(elem: Shape, max_len: usize) -> Shape {
    Shape::Seq { elem: Box::new(elem), max_len }
}
fn stup(es: Vec<Shape>) -> Shape {
    Shape::Tuple(Arc::from(es))
}
fn srec(fs: &[(&str, Shape)]) -> Shape {
    let mut fs: Vec<(Sym, Shape)> = fs.iter().map(|(k, s)| (Sym::new(k), s.clone())).collect();
    fs.sort_by_key(|f| f.0);
    Shape::Record(Arc::from(fs))
}
fn sfcn(dom: Vec<Value>, range: Shape) -> Shape {
    let mut dom = dom;
    dom.sort();
    Shape::Fcn { dom: Arc::from(dom), range: Box::new(range), witness: FcnWitness::Enumerated, key_variants: Arc::from([]) }
}

fn enc(s: &Shape, v: &Value) -> Result<Vec<u64>, tlx_layout::Miss> {
    // Dirty buffer: encode must zero what it uses.
    let mut out = vec![0xdead_beef_u64; words(s) + 1];
    encode(s, v, &mut out)?;
    assert_eq!(out[words(s)], 0xdead_beef, "encode wrote past words(s)");
    out.truncate(words(s));
    Ok(out)
}

/// Exhaustive checks on a finite shape: rank/unrank bijection, contains,
/// encode/decode round trip, canonicality; optionally TLC-order monotonicity.
fn exhaustive(s: &Shape, monotone: bool) {
    let card = s.cardinality().expect("finite shape");
    assert!(card <= 200_000, "shape too large for exhaustive test: {card}");
    let mut prev: Option<Value> = None;
    let mut seen_vals = HashSet::new();
    let mut seen_enc = HashSet::new();
    for r in 0..card {
        let v = unrank(s, r);
        assert!(s.contains(&v), "unrank({r}) = {v} not contained in {s:?}");
        assert_eq!(rank(s, &v).unwrap(), r, "rank(unrank({r})) for {v}");
        if monotone {
            if let Some(p) = &prev {
                assert!(p < &v, "rank not monotone: {p} !< {v} in {s:?}");
            }
            prev = Some(v.clone());
        }
        let e = enc(s, &v).unwrap();
        assert_eq!(decode(s, &e), v);
        assert!(seen_vals.insert(v.clone()), "duplicate value {v}");
        assert!(seen_enc.insert(e), "two values share an encoding ({v})");
    }
}

use tlx_testkit::XorShift64Star as Rng;

/// Random value of a loose "type" chosen by `kind` (so that joins of many
/// values stay reasonably small), recursing up to `depth`.
fn random_value(rng: &mut Rng, depth: u32) -> Value {
    let k = if depth == 0 { rng.below(4) } else { rng.below(10) };
    match k {
        0 => Value::Bool(rng.below(2) == 1),
        1 => int(rng.below(7) as i64 - 3),
        2 => st(["a", "b", "c"][rng.below(3) as usize]),
        3 => mv(["m1", "m2"][rng.below(2) as usize]),
        4 | 5 => {
            let n = rng.below(4);
            let inner = rng.below(3);
            set((0..n)
                .map(|_| match inner {
                    0 => int(rng.below(5) as i64),
                    1 => st(["a", "b", "c", "d"][rng.below(4) as usize]),
                    _ => tup(vec![int(rng.below(2) as i64), Value::Bool(rng.below(2) == 0)]),
                })
                .collect())
        }
        6 => {
            let n = rng.below(4);
            tup((0..n).map(|_| random_value(rng, depth - 1)).collect())
        }
        7 => {
            let mut fs = vec![("a", random_value(rng, depth - 1))];
            if rng.below(2) == 0 {
                fs.push(("b", int(rng.below(3) as i64)));
            }
            rec(&fs)
        }
        8 => fcn(vec![(mv("m1"), int(rng.below(3) as i64)), (mv("m2"), int(rng.below(3) as i64))]),
        _ => Value::Interval(1, rng.below(4) as i64),
    }
}

// ---------------------------------------------------------------------------
// Shape::of / join / kind_key

#[test]
fn shape_of() {
    assert_eq!(Shape::of(&Value::TRUE), Shape::Bool);
    assert_eq!(Shape::of(&int(5)), sint(5, 5));
    assert_eq!(Shape::of(&st("x")), satom(vec![st("x")]));
    assert_eq!(Shape::of(&mv("m")), satom(vec![mv("m")]));
    assert_eq!(Shape::of(&set(vec![int(1), int(3)])), sset(sint(1, 3), 2));
    assert_eq!(Shape::of(&Value::empty_set()), sset(Shape::Never, 0));
    assert_eq!(Shape::of(&Value::Interval(2, 4)), Shape::Dyn);
    assert_eq!(Shape::of(&Value::Interval(2, 1)), Shape::Dyn);
    assert_eq!(Shape::of(&tup(vec![])), stup(vec![]));
    assert_eq!(Shape::of(&tup(vec![int(1), st("a")])), stup(vec![sint(1, 1), satom(vec![st("a")])]));
    assert_eq!(Shape::of(&rec(&[("b", int(1)), ("a", Value::TRUE)])), srec(&[("a", Shape::Bool), ("b", sint(1, 1))]));
    assert_eq!(Shape::of(&fcn(vec![(mv("p"), int(1)), (mv("q"), int(4))])), sfcn(vec![mv("p"), mv("q")], sint(1, 4)));
    // Heterogeneous set: union element shape.
    let s = Shape::of(&set(vec![int(1), st("a")]));
    match s {
        Shape::Set { elem, max_card: 2 } => assert!(matches!(*elem, Shape::Union(_))),
        _ => panic!("{s:?}"),
    }
}

#[test]
fn join_basic() {
    assert_eq!(Shape::Never.join(&Shape::Bool), Shape::Bool);
    assert_eq!(Shape::Bool.join(&Shape::Never), Shape::Bool);
    assert_eq!(Shape::Dyn.join(&Shape::Bool), Shape::Dyn);
    assert_eq!(Shape::Bool.join(&Shape::Dyn), Shape::Dyn);
    assert_eq!(sint(1, 2).join(&sint(5, 7)), sint(1, 7));
    assert_eq!(satom(vec![st("b")]).join(&satom(vec![st("a"), mv("m")])), satom(vec![st("a"), st("b"), mv("m")]));
    assert_eq!(sset(sint(0, 0), 1).join(&sset(sint(3, 3), 4)), sset(sint(0, 3), 4));
    assert_eq!(sset(Shape::Never, 0).join(&sset(Shape::Bool, 2)), sset(Shape::Bool, 2));
    // Functions.
    let d = vec![mv("p"), mv("q")];
    assert_eq!(sfcn(d.clone(), sint(0, 1)).join(&sfcn(d.clone(), sint(3, 3))), sfcn(d.clone(), sint(0, 3)));
    // Different domains: a map over the union of the keys.
    let m = Shape::Map { key: Box::new(satom(vec![mv("p"), mv("q")])), range: Box::new(sint(0, 1)), witness: FcnWitness::Enumerated };
    assert_eq!(sfcn(d, sint(0, 1)).join(&sfcn(vec![mv("p")], sint(0, 1))), m);
    // Tuples are functions on 1..n: with other functions they form a map.
    let ints = sfcn(vec![Value::Int(0)], sint(5, 5));
    let im = Shape::Map { key: Box::new(sint(0, 2)), range: Box::new(sint(1, 5)), witness: FcnWitness::Dynamic };
    assert_eq!(ints.join(&stup(vec![sint(1, 1), sint(2, 2)])), im);
    assert_eq!(sseq(sint(1, 1), 2).join(&ints), im);
    assert_eq!(
        stup(vec![]).join(&ints),
        Shape::Map { key: Box::new(sint(0, 0)), range: Box::new(sint(5, 5)), witness: FcnWitness::Dynamic }
    );
    // Records.
    assert_eq!(srec(&[("a", sint(0, 0))]).join(&srec(&[("a", sint(2, 2))])), srec(&[("a", sint(0, 2))]));
    let u = srec(&[("a", sint(0, 0))]).join(&srec(&[("b", sint(0, 0))]));
    match &u {
        Shape::Union(arms) => assert_eq!(arms.len(), 2),
        _ => panic!("{u:?}"),
    }
    // Tuples and sequences.
    assert_eq!(stup(vec![sint(0, 0), Shape::Bool]).join(&stup(vec![sint(2, 2), Shape::Bool])), stup(vec![sint(0, 2), Shape::Bool]));
    assert_eq!(stup(vec![]).join(&stup(vec![sint(1, 1), sint(4, 4)])), sseq(sint(1, 4), 2));
    assert_eq!(sseq(sint(0, 0), 3).join(&stup(vec![sint(5, 5)])), sseq(sint(0, 5), 3));
    assert_eq!(stup(vec![sint(5, 5)]).join(&sseq(sint(0, 0), 3)), sseq(sint(0, 5), 3));
    assert_eq!(sseq(sint(0, 0), 1).join(&sseq(sint(1, 1), 4)), sseq(sint(0, 1), 4));
}

#[test]
fn join_unions() {
    let u = sint(0, 1).join(&satom(vec![st("a")]));
    assert_eq!(u, Shape::Union(Arc::from(vec![sint(0, 1), satom(vec![st("a")])])));
    // Join into an existing arm, commutativity.
    let u2 = u.join(&sint(5, 5));
    assert_eq!(u2, Shape::Union(Arc::from(vec![sint(0, 5), satom(vec![st("a")])])));
    assert_eq!(sint(5, 5).join(&u), u2);
    // Union with union.
    let v = Shape::Bool.join(&satom(vec![st("b")]));
    let w = u.join(&v);
    assert_eq!(w, Shape::Union(Arc::from(vec![Shape::Bool, sint(0, 1), satom(vec![st("a"), st("b")])])));
    assert_eq!(v.join(&u), w);
    // Tuple arms of different lengths merge into a Seq arm.
    let t = Shape::Bool.join(&stup(vec![sint(1, 1)])).join(&stup(vec![sint(2, 2), sint(3, 3)]));
    assert_eq!(t, Shape::Union(Arc::from(vec![Shape::Bool, sseq(sint(1, 3), 2)])));
    // Union arms are sorted by kind key.
    if let Shape::Union(arms) = &w {
        let keys: Vec<KindKey> = arms.iter().map(|a| a.kind_key().unwrap()).collect();
        assert!(keys.windows(2).all(|k| k[0] < k[1]));
    }
    // Too many arms -> Dyn.
    let mut s = Shape::Never;
    for i in 0..=MAX_UNION_ARMS {
        let name = format!("f{i}");
        s = s.join(&srec(&[(name.as_str(), Shape::Bool)]));
    }
    assert_eq!(s, Shape::Dyn);
    // Fcn arms with different domains inside a union -> a map arm.
    let f = Shape::Bool.join(&sfcn(vec![mv("p")], Shape::Bool));
    let m = Shape::Map { key: Box::new(satom(vec![mv("p"), mv("q")])), range: Box::new(Shape::Bool), witness: FcnWitness::Enumerated };
    assert_eq!(f.join(&sfcn(vec![mv("q")], Shape::Bool)), Shape::Union(Arc::from(vec![Shape::Bool, m])));
    // Dyn absorbs unions.
    assert_eq!(f.join(&Shape::Dyn), Shape::Dyn);
}

#[test]
fn join_tuple_alternatives() {
    // `<<>>` next to `<<node, round>>` pairs: tuple arms by length.
    let nodes = satom(vec![mv("n1"), mv("n2")]);
    let pair = stup(vec![nodes.clone(), sint(1, 3)]);
    let u = Shape::Union(Arc::from(vec![stup(vec![]), pair.clone()]));
    assert_eq!(stup(vec![]).join(&pair), u);
    assert_eq!(pair.join(&stup(vec![])), u);
    // Same-length tuples join componentwise inside their arm.
    let u2 = u.join(&stup(vec![nodes.clone(), sint(0, 0)]));
    assert_eq!(u2, Shape::Union(Arc::from(vec![stup(vec![]), stup(vec![nodes.clone(), sint(0, 3)])])));
    // Other arms stay apart.
    let b = u.join(&Shape::Bool);
    assert_eq!(b, Shape::Union(Arc::from(vec![Shape::Bool, stup(vec![]), pair.clone()])));
    assert_eq!(Shape::Bool.join(&u), b);
    // A tuple of mixed families of another length adds an arm.
    let triple = stup(vec![nodes.clone(), sint(1, 1), Shape::Bool]);
    assert_eq!(u.join(&triple), Shape::Union(Arc::from(vec![stup(vec![]), pair.clone(), triple.clone()])));
    // A one-element tuple (a sequence growing by Append) or a sequence: one Seq.
    let one = stup(vec![sint(5, 5)]);
    assert_eq!(u.join(&one), sseq(Shape::Union(Arc::from(vec![sint(1, 5), nodes.clone()])), 2));
    assert_eq!(u.join(&sseq(sint(0, 0), 1)), sseq(Shape::Union(Arc::from(vec![sint(0, 3), nodes.clone()])), 2));
    // Homogeneous tuples of different lengths: a Seq, as before.
    assert_eq!(stup(vec![]).join(&stup(vec![sint(1, 1), sint(2, 2)])), sseq(sint(1, 2), 2));
    // Encoding: the arm of the value's length, ranks in TLC order.
    let t = sint(0, 1).join(&Shape::Never);
    let small = stup(vec![]).join(&stup(vec![satom(vec![mv("p"), mv("q")]), t.clone()])).join(&stup(vec![
        Shape::Bool,
        t.clone(),
        satom(vec![st("s")]),
    ]));
    exhaustive(&small, true);
    exhaustive(&sset(small.clone(), 3), false);
    exhaustive(&stup(vec![small.clone(), small.clone()]), true);
    assert!(enc(&small, &tup(vec![mv("p")])).is_err());
    assert!(enc(&small, &tup(vec![mv("p"), int(1)])).is_ok());
    // A miss on a new length widens into another arm.
    let w = widen(&u, &tup(vec![mv("n1"), int(2), Value::Bool(true)]));
    assert!(matches!(&w, Shape::Union(arms) if arms.len() == 3), "{w:?}");
}

#[test]
fn kind_keys() {
    assert_eq!(Shape::Never.kind_key(), None);
    assert_eq!(Shape::Dyn.kind_key(), None);
    assert_eq!(stup(vec![Shape::Bool; 3]).kind_key(), Some(KindKey::Tuple(3)));
    assert_eq!(sseq(Shape::Bool, 3).kind_key(), Some(KindKey::Seq));
    assert_eq!(srec(&[("x", Shape::Bool)]).kind_key(), Some(KindKey::Record(1, vec![Sym::new("x")])));
}

// ---------------------------------------------------------------------------
// cardinality / rank / unrank

#[test]
fn cardinalities() {
    assert_eq!(Shape::Never.cardinality(), Some(0));
    assert_eq!(Shape::Bool.cardinality(), Some(2));
    assert_eq!(sint(-3, 3).cardinality(), Some(7));
    assert_eq!(sint(i64::MIN, i64::MAX).cardinality(), None);
    assert_eq!(satom(vec![st("a"), mv("b")]).cardinality(), Some(2));
    assert_eq!(sset(sint(0, 4), 5).cardinality(), Some(32));
    assert_eq!(sset(sint(0, 4), 9).cardinality(), Some(32));
    assert_eq!(sset(sint(0, 4), 2).cardinality(), Some(1 + 5 + 10));
    assert_eq!(sset(sint(0, 63), 64).cardinality(), None);
    assert_eq!(sset(sint(0, 99), 2).cardinality(), Some(1 + 100 + 4950));
    assert_eq!(sfcn(vec![mv("p"), mv("q"), mv("r")], sint(0, 2)).cardinality(), Some(27));
    assert_eq!(srec(&[("a", Shape::Bool), ("b", sint(0, 2))]).cardinality(), Some(6));
    assert_eq!(stup(vec![]).cardinality(), Some(1));
    assert_eq!(sseq(sint(0, 2), 2).cardinality(), Some(1 + 3 + 9));
    assert_eq!(sseq(Shape::Never, 5).cardinality(), Some(1));
    assert_eq!(sseq(sint(0, 0), 5).cardinality(), Some(6));
    assert_eq!(Shape::Bool.join(&sint(0, 2)).cardinality(), Some(5));
    assert_eq!(Shape::Dyn.cardinality(), None);
    assert_eq!(sseq(Shape::Dyn, 1).cardinality(), None);
}

#[test]
fn exhaustive_monotone_shapes() {
    let a = satom(vec![st("x"), st("y"), mv("m1"), mv("m2")]);
    for s in [
        Shape::Bool,
        sint(-3, 4),
        a.clone(),
        stup(vec![]),
        stup(vec![Shape::Bool, sint(0, 2), a.clone()]),
        srec(&[("a", sint(0, 2)), ("b", Shape::Bool), ("c", a.clone())]),
        srec(&[("x", stup(vec![Shape::Bool, sint(1, 3)])), ("y", srec(&[("z", sint(0, 1))]))]),
    ] {
        exhaustive(&s, true);
    }
}

#[test]
fn exhaustive_other_shapes() {
    let a = satom(vec![st("x"), mv("m")]);
    for s in [
        sset(sint(0, 4), 5),
        sset(sint(0, 4), 2),
        sset(sint(0, 9), 3),
        sset(Shape::Never, 0),
        sset(stup(vec![Shape::Bool, a.clone()]), 4),
        sset(sset(sint(0, 2), 3), 2),
        sfcn(vec![mv("p"), mv("q"), mv("r")], sint(0, 2)),
        sfcn(vec![int(0), int(5)], sset(Shape::Bool, 2)),
        sseq(sint(0, 2), 3),
        sseq(Shape::Never, 2),
        sseq(sint(7, 7), 3),
        sseq(srec(&[("a", Shape::Bool)]), 3),
        Shape::Bool.join(&sint(0, 2)).join(&a).join(&srec(&[("f", Shape::Bool)])),
        sint(0, 1).join(&sseq(Shape::Bool, 2)).join(&sset(Shape::Bool, 2)),
        stup(vec![sset(sint(0, 3), 4), sseq(Shape::Bool, 2), Shape::Bool.join(&sint(0, 1))]),
    ] {
        exhaustive(&s, false);
    }
}

#[test]
fn large_combinatorial_set_rank() {
    // 2-element subsets of a 1000-element universe: spot-check round trips.
    let s = sset(sint(0, 999), 2);
    let card = s.cardinality().unwrap();
    assert_eq!(card, 1 + 1000 + 499_500);
    let mut rng = Rng::new(7);
    for _ in 0..2000 {
        let r = rng.below(card);
        let v = unrank(&s, r);
        assert_eq!(rank(&s, &v).unwrap(), r);
    }
    assert_eq!(unrank(&s, card - 1), set(vec![int(998), int(999)]));
}

#[test]
fn rank_misses() {
    assert!(rank(&sint(0, 3), &int(4)).is_err());
    assert!(rank(&Shape::Dyn, &int(4)).is_err());
    assert!(rank(&sseq(Shape::Dyn, 2), &tup(vec![])).is_err());
    assert!(rank(&sset(sint(0, 3), 1), &set(vec![int(0), int(1)])).is_err());
}

// ---------------------------------------------------------------------------
// encode / decode

#[test]
fn words_per_shape() {
    assert_eq!(words(&Shape::Never), 0);
    assert_eq!(words(&Shape::Bool), 1);
    assert_eq!(words(&sset(sint(0, 63), 64)), 1);
    assert_eq!(words(&sset(sint(0, 64), 3)), 2);
    assert_eq!(words(&sset(sint(0, 4095), 3)), 64);
    assert_eq!(words(&sset(sint(0, 4096), 3)), 1 + 3);
    assert_eq!(words(&sset(Shape::Dyn, 5)), 6);
    assert_eq!(words(&sset(stup(vec![sint(0, 9999), Shape::Bool]), 2)), 1 + 2);
    assert_eq!(words(&sseq(stup(vec![Shape::Bool, Shape::Bool]), 3)), 1 + 3);
    assert_eq!(words(&sfcn(vec![mv("a"), mv("b")], stup(vec![Shape::Bool; 3]))), 2);
    assert_eq!(words(&Shape::Bool.join(&stup(vec![Shape::Bool; 3]))), 2);
    assert_eq!(words(&stup(vec![Shape::Bool; 64])), 1);
    assert_eq!(words(&stup(vec![Shape::Bool; 65])), 2);
    assert_eq!(words(&sfcn((0..20).map(int).collect(), sint(0, 7))), 1);
    assert_eq!(words(&sseq(sint(0, 15), 16)), 2);
}

#[test]
fn sorted_array_sets() {
    // Element universe too large for a bitset.
    let s = sset(sint(-10_000, 10_000), 4);
    let vals =
        [Value::empty_set(), set(vec![int(-10_000)]), set(vec![int(3), int(-5), int(10_000)]), set(vec![int(1), int(2), int(3), int(4)])];
    for v in &vals {
        let e = enc(&s, v).unwrap();
        assert_eq!(decode(&s, &e), *v);
        assert!(s.contains(v));
    }
    // Intervals are rejected by exact `Shape::Set` (to preserve their witness)
    // but share the canonical semantic encoding with equal enumerated sets.
    let iv = Value::Interval(1, 4);
    assert!(!s.contains(&iv));
    assert!(enc(&s, &iv).is_err());
    assert!(s.contains_semantic(&iv));
    let mut sem = vec![0u64; words(&s)];
    tlx_layout::layout::encode_semantic(&s, &iv, &mut sem).unwrap();
    assert_eq!(enc(&s, &vals[3]).unwrap(), sem);
    assert_ne!(enc(&s, &vals[1]).unwrap(), enc(&s, &vals[2]).unwrap());
    assert!(enc(&s, &set(vec![int(1), int(2), int(3), int(4), int(5)])).is_err());
    assert!(enc(&s, &Value::Interval(1, 5)).is_err());
    assert!(!s.contains_semantic(&Value::Interval(1, 5)));
    assert!(enc(&s, &set(vec![int(10_001)])).is_err());

    // Dyn elements.
    let s = sset(Shape::Dyn, 3);
    let a = set(vec![st("q"), tup(vec![int(1)]), Value::empty_set()]);
    let b = set(vec![tup(vec![int(1)]), st("q"), Value::empty_set()]);
    assert_eq!(enc(&s, &a).unwrap(), enc(&s, &b).unwrap());
    assert_eq!(decode(&s, &enc(&s, &a).unwrap()), a);
}

fn assert_miss(s: &Shape, v: &Value, path: &str, offending: &Value) {
    assert!(!s.contains(v), "{v} unexpectedly contained in {s:?}");
    let m = enc(s, v).unwrap_err();
    assert_eq!(m.path, path, "miss path for {v}");
    assert_eq!(&m.value, offending, "miss value for {v}");
}

#[test]
fn misses() {
    assert_miss(&Shape::Bool, &int(0), "", &int(0));
    assert_miss(&Shape::Never, &int(0), "", &int(0));
    assert_miss(&sint(0, 3), &int(4), "", &int(4));
    assert_miss(&sint(0, 3), &int(-1), "", &int(-1));
    assert_miss(&sint(0, 3), &Value::TRUE, "", &Value::TRUE);
    assert_miss(&satom(vec![st("a")]), &st("b"), "", &st("b"));
    assert_miss(&satom(vec![st("a")]), &mv("a"), "", &mv("a"));
    let s2 = set(vec![int(0), int(1)]);
    assert_miss(&sset(sint(0, 3), 1), &s2, "", &s2);
    assert_miss(&sset(sint(0, 3), 4), &set(vec![int(0), int(7)]), "{}", &int(7));
    assert_miss(&sset(Shape::Never, 0), &set(vec![int(0)]), "", &set(vec![int(0)]));
    assert_miss(&sset(sint(0, 3), 4), &tup(vec![]), "", &tup(vec![]));
    let f = fcn(vec![(mv("p"), int(0)), (mv("q"), int(9))]);
    assert_miss(&sfcn(vec![mv("p"), mv("q")], sint(0, 3)), &f, "[q]", &int(9));
    assert_miss(&sfcn(vec![mv("p"), mv("r")], sint(0, 9)), &f, "", &f);
    assert_miss(&sfcn(vec![mv("p")], sint(0, 9)), &f, "", &f);
    let r = rec(&[("a", int(1)), ("b", tup(vec![int(2), int(5)]))]);
    assert_miss(&srec(&[("a", sint(0, 1)), ("b", stup(vec![sint(0, 9), sint(0, 4)]))]), &r, ".b[2]", &int(5));
    assert_miss(&srec(&[("a", sint(0, 1))]), &r, "", &r);
    assert_miss(&srec(&[("a", sint(0, 1)), ("b", Shape::Bool), ("c", Shape::Bool)]), &r, "", &r);
    let t = tup(vec![int(1), int(2)]);
    assert_miss(&stup(vec![sint(0, 9)]), &t, "", &t);
    assert_miss(&sseq(sint(0, 9), 1), &t, "", &t);
    assert_miss(&sseq(sint(0, 1), 2), &t, "[2]", &int(2));
    assert_miss(&sseq(sint(0, 1), 2), &rec(&[("a", int(0))]), "", &rec(&[("a", int(0))]));
    let u = Shape::Bool.join(&sint(0, 1));
    assert_miss(&u, &int(2), "", &int(2));
    assert_miss(&u, &st("x"), "", &st("x"));
    // Layout paths carry the variable index.
    let l = Layout::new(vec![Shape::Bool, srec(&[("a", sint(0, 1))])]);
    let mut out = vec![0; l.words];
    let m = l.encode_state(&[Value::TRUE, rec(&[("a", int(3))])], &mut out).unwrap_err();
    assert_eq!(m.path, "#1.a");
    assert_eq!(m.var_index(), Some(1));
    assert_eq!(m.value, int(3));
}

#[test]
fn dyn_slots() {
    let s = stup(vec![Shape::Dyn, Shape::Bool]);
    let v = tup(vec![set(vec![st("a"), int(1)]), Value::TRUE]);
    let e = enc(&s, &v).unwrap();
    assert_ne!(e[0], 0);
    assert_eq!(decode(&s, &e), v);
    // Interval and equal set share a handle.
    assert_eq!(dynval::intern(&Value::Interval(1, 3)), dynval::intern(&set(vec![int(1), int(2), int(3)])));
    let hs: Vec<u64> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..8).map(|i| sc.spawn(move || dynval::intern(&tup(vec![int(i % 2), st("thread")])))).collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    for (i, h) in hs.iter().enumerate() {
        assert_eq!(*h, hs[i % 2]);
        assert_eq!(dynval::lookup(*h), tup(vec![int(i as i64 % 2), st("thread")]));
    }
    assert_ne!(hs[0], hs[1]);
}

/// Scalars are encoded in their handles: they round-trip,
/// equal values share a handle and different ones do not, also next to
/// table handles of the same numbers.
#[test]
fn dyn_immediate_scalars() {
    let vals = vec![
        st(""),
        st("dyn_imm"),
        mv("dyn_imm"),
        Value::TRUE,
        Value::FALSE,
        int(0),
        int(-1),
        int(i32::MAX as i64),
        int(i32::MIN as i64),
        int((1 << 60) - 1),
        int(-(1 << 60)),
    ];
    let hs: Vec<u64> = vals.iter().map(dynval::intern).collect();
    for (i, (v, h)) in vals.iter().zip(&hs).enumerate() {
        assert_ne!(*h, 0);
        assert_eq!(&dynval::lookup(*h), v);
        assert_eq!(dynval::intern(&v.clone()), *h);
        assert!(hs[..i].iter().all(|g| g != h), "{v} shares a handle");
    }
    // Integers beyond the immediate range go to the table.
    for v in [int(1 << 60), int(i64::MIN), int(i64::MAX)] {
        let h = dynval::intern(&v);
        assert!(!hs.contains(&h));
        assert_eq!(dynval::lookup(h), v);
    }
    let t = dynval::intern(&tup(vec![int(1)]));
    assert!(!hs.contains(&t));
    assert_eq!(dynval::lookup(t), tup(vec![int(1)]));
}

/// The pre-run's observer takes an atom universe of more computed strings
/// than `MAX_OBSERVED_STRINGS` as open-ended (`Dyn`), also inside other
/// shapes; universes of hints stay atoms.
#[test]
fn observer_caps_computed_strings() {
    use tlx_layout::infer::MAX_OBSERVED_STRINGS;
    let hints = Hints { atoms: (0..10).map(|i| st(&format!("cap_hint_{i}"))).collect(), int_ranges: Vec::new() };
    let mut obs = Observer::new(2);
    for v in &hints.atoms {
        obs.observe_with(&[v.clone(), Value::set_from(vec![v.clone()]).unwrap()], &hints);
    }
    assert!(matches!(&obs.shapes[0], Shape::Atom(u) if u.len() == 10));
    for i in 0..MAX_OBSERVED_STRINGS {
        let v = st(&format!("cap_computed_{i}"));
        obs.observe_with(&[v.clone(), Value::set_from(vec![v]).unwrap()], &hints);
    }
    assert!(matches!(&obs.shapes[0], Shape::Atom(u) if u.len() == MAX_OBSERVED_STRINGS + 10));
    let v = st("cap_computed_last");
    assert!(obs.observe_with(&[v.clone(), Value::set_from(vec![v.clone()]).unwrap()], &hints));
    assert_eq!(obs.shapes[0], Shape::Dyn);
    assert!(matches!(&obs.shapes[1], Shape::Set { elem, .. } if **elem == Shape::Dyn));
    assert!(!obs.observe_with(&[st("cap_computed_more"), Value::set_from(vec![v]).unwrap()], &hints));
}

/// Randomized: shapes inferred from random values contain them, round-trip
/// them and encode distinct values distinctly; `contains` agrees with
/// `encode` on fresh random values.
#[test]
fn randomized_round_trip() {
    let mut rng = Rng::new(0x1234_5678_9abc_def1);
    for round in 0..200 {
        let n = 1 + rng.below(12) as usize;
        let vals: Vec<Value> = (0..n).map(|_| random_value(&mut rng, 2)).collect();
        let mut obs = Observer::new(1);
        for v in &vals {
            obs.observe(std::slice::from_ref(v));
        }
        let observed = obs.shapes[0].clone();
        for s in [observed.clone(), obs.finalize(&Hints::default()).pop().unwrap()] {
            let mut encs: HashMap<Vec<u64>, Value> = HashMap::new();
            for v in &vals {
                assert!(s.contains(v), "round {round}: {v} not in {s:?}");
                let e = enc(&s, v).unwrap();
                let d = decode(&s, &e);
                assert_eq!(&d, v, "round {round}: decode mismatch in {s:?}");
                if let Some(prev) = encs.insert(e, v.clone()) {
                    assert_eq!(&prev, v, "round {round}: two values share an encoding in {s:?}");
                }
            }
            for _ in 0..20 {
                let w = random_value(&mut rng, 2);
                let c = s.contains(&w);
                match enc(&s, &w) {
                    Ok(e) => {
                        assert!(c, "round {round}: encoded {w} but contains is false for {s:?}");
                        assert_eq!(decode(&s, &e), w);
                        if let Some(prev) = encs.insert(e, w.clone()) {
                            assert_eq!(prev, w, "round {round}: two values share an encoding in {s:?}");
                        }
                    }
                    Err(_) => assert!(!c, "round {round}: contains({w}) but encode failed for {s:?}"),
                }
                // widen always makes room.
                let ws = widen(&s, &w);
                assert!(ws.contains(&w), "round {round}: widen({s:?}, {w}) = {ws:?}");
                for v in &vals {
                    assert!(ws.contains(v));
                }
            }
        }
    }
}

// ---------------------------------------------------------------------------
// Observer / widen

#[test]
fn int_widening() {
    assert_eq!(widen_int(0, 0), (0, 2));
    assert_eq!(widen_int(1, 3), (0, 5));
    assert_eq!(widen_int(10, 30), (0, 40));
    assert_eq!(widen_int(-4, 4), (-8, 8));
    assert_eq!(widen_int(-3, -1), (-5, 0));
    assert_eq!(widen_int(0, i32::MAX as i64), (0, i32::MAX as i64));
}

#[test]
fn observer_finalize() {
    let mut obs = Observer::new(4);
    obs.observe(&[int(1), set(vec![mv("a")]), tup(vec![]), rec(&[("s", st("x"))])]);
    obs.observe(&[int(3), set(vec![mv("a"), mv("b")]), tup(vec![int(1)]), rec(&[("s", st("y"))])]);
    assert_eq!(obs.shapes[0], sint(1, 3));
    assert_eq!(obs.shapes[1], sset(satom(vec![mv("a"), mv("b")]), 2));
    assert_eq!(obs.shapes[2], sseq(sint(1, 1), 1));
    let hints = Hints { atoms: vec![mv("c"), st("z"), mv("a")], ..Default::default() };
    let f = obs.finalize(&hints);
    assert_eq!(f[0], sint(0, 5));
    // Universe {a, b, c}: max_card min(max(4, 4), 3) = 3.
    assert_eq!(f[1], sset(satom(vec![mv("a"), mv("b"), mv("c")]), 3));
    assert_eq!(f[2], sseq(sint(0, 3), 3));
    assert_eq!(f[3], srec(&[("s", satom(vec![st("x"), st("y"), st("z")]))]));
    let l = Layout::new(f);
    assert_eq!(l.offsets, vec![0, 1, 2, 4]);
    assert_eq!(l.words, 5);
    let st0 = [int(5), set(vec![mv("c")]), tup(vec![int(0), int(3), int(2)]), rec(&[("s", st("z"))])];
    let mut out = vec![0; l.words];
    l.encode_state(&st0, &mut out).unwrap();
    assert_eq!(l.decode_state(&out), st0.to_vec());
}

#[test]
fn widen_after_miss() {
    // Only the changed parts get headroom.
    let s = stup(vec![sint(0, 5), sseq(Shape::Bool, 2)]);
    let w = widen(&s, &tup(vec![int(9), tup(vec![Value::TRUE])]));
    assert_eq!(w, stup(vec![sint(0, 13), sseq(Shape::Bool, 2)]));
    let w = widen(&s, &tup(vec![int(1), tup(vec![Value::TRUE; 3])]));
    assert_eq!(w, stup(vec![sint(0, 5), sseq(Shape::Bool, 6)]));
    // Kind change: tuple -> seq.
    let w = widen(&stup(vec![]), &tup(vec![int(1)]));
    assert_eq!(w, sseq(sint(0, 3), 3));
    // Kind change: union.
    let w = widen(&Shape::Bool, &int(4));
    assert_eq!(w, Shape::Union(Arc::from(vec![Shape::Bool, sint(0, 6)])));
    // Set cardinality: a bitset admits every subset of its universe
    // (no headroom needed), a sorted array gets the usual headroom; a full bitset that
    // becomes a sorted array is sized by the value that missed.
    let w = widen(&sset(sint(0, 9), 1), &set(vec![int(1), int(2)]));
    assert_eq!(w, sset(sint(0, 9), 10));
    let w = widen(&sset(sint(0, 9999), 1), &set(vec![int(1), int(2)]));
    assert_eq!(w, sset(sint(0, 9999), 4));
    let w = widen(&sset(sint(0, 9), 10), &set(vec![int(1), int(5000)]));
    assert_eq!(w, sset(sint(0, 7500), 4));
    // A cardinality that grew past a settled bound doubles too: a set that
    // keeps growing with the depth (MultiPaxos_MC's `msgs`) would otherwise
    // miss again later, in a larger search (see `infer.rs::grow_len`).
    let w = widen(&sset(sint(0, 9999), 24), &set((0..25).map(int).collect()));
    assert_eq!(w, sset(sint(0, 9999), 50));
    let w = widen(&sset(sint(0, 9999), 6), &set((0..7).map(int).collect()));
    assert_eq!(w, sset(sint(0, 9999), 14));
    // Inside a set element the cardinality sizes the enclosing universe.
    let w = widen(&sset(sset(sint(0, 9), 1), 1), &set(vec![set(vec![int(1), int(2)])]));
    // (The outer bitset admits every subset of its 386 elements.)
    assert_eq!(w, sset(sset(sint(0, 9), 4), 386));
}

#[test]
fn repeated_misses_converge() {
    let hints = Hints { atoms: vec![st("a"), st("b"), mv("m1"), mv("m2")], ..Default::default() };
    // A literal string extends the universe; a computed one too, once.
    let s = satom(vec![st("a")]);
    assert_eq!(widen_repeated(&s, &st("b"), &hints, 0), satom(vec![st("a"), st("b")]));
    let w = widen_repeated(&s, &st("n1"), &hints, 0);
    assert_eq!(w, satom(vec![st("a"), st("b"), st("n1")]));
    // The next computed string: open-ended, Dyn (also nested, in value
    // positions and set elements; a union arm makes the union Dyn).
    assert_eq!(widen_repeated(&w, &st("n2"), &hints, 1), Shape::Dyn);
    let r = srec(&[("name", w.clone()), ("n", sint(0, 3))]);
    assert_eq!(widen_repeated(&r, &rec(&[("name", st("n2")), ("n", int(1))]), &hints, 0), srec(&[("name", Shape::Dyn), ("n", sint(0, 3))]));
    assert_eq!(widen_repeated(&sseq(w.clone(), 2), &tup(vec![st("n2")]), &hints, 0), sseq(Shape::Dyn, 2));
    assert_eq!(widen_repeated(&sset(w.clone(), 2), &set(vec![st("n2")]), &hints, 0), sset(Shape::Dyn, 2));
    let u = Shape::Union(Arc::from(vec![sint(0, 3), w.clone()]));
    assert_eq!(widen_repeated(&u, &st("n2"), &hints, 0), Shape::Dyn);
    // Without computed strings: Dyn on the third miss of the shape.
    assert_eq!(widen_repeated(&s, &st("b"), &hints, 1), satom(vec![st("a"), st("b")]));
    assert_eq!(widen_repeated(&s, &st("b"), &hints, 2), Shape::Dyn);
    // Model values get all hint model values at once and stay atoms.
    assert_eq!(widen_repeated(&satom(vec![mv("m1")]), &mv("m2"), &hints, 5), satom(vec![mv("m1"), mv("m2")]));
    // Integers in value positions grow by span * 4^prior; set elements
    // (encoding size) only get the usual headroom.
    assert_eq!(widen_repeated(&sint(0, 10), &int(11), &hints, 0), sint(0, 16));
    // (0..11 + 11 * 4 = 0..55, + 27 headroom; 0..11 + 11 * 16 = 0..187, + 93.)
    assert_eq!(widen_repeated(&sint(0, 10), &int(11), &hints, 1), sint(0, 82));
    assert_eq!(widen_repeated(&sint(0, 10), &int(11), &hints, 2), sint(0, 280));
    assert_eq!(widen_repeated(&sseq(sint(0, 10), 2), &tup(vec![int(11)]), &hints, 1), sseq(sint(0, 82), 2));
    assert_eq!(widen_repeated(&sset(sint(0, 10), 2), &set(vec![int(11)]), &hints, 1), sset(sint(0, 16), 17));
    // Only the side that grew: -11..0 - 44 = -55..0, then the headroom.
    assert_eq!(widen_repeated(&sint(-10, 0), &int(-11), &hints, 1), sint(-82, 27));
}

#[test]
fn records_with_the_same_fields_are_unified() {
    use tlx_layout::infer::unify_records;
    let p = sfcn(vec![mv("p"), mv("q")], srec(&[("den", sint(0, 23)), ("num", sint(0, 10))]));
    let msgs = sfcn(vec![mv("p"), mv("q")], sseq(srec(&[("den", sint(0, 23)), ("num", sint(0, 7))]), 8));
    let other = srec(&[("num", sint(-3, 1))]);
    let mut shapes = vec![p.clone(), msgs, other.clone()];
    unify_records(&mut shapes);
    assert_eq!(shapes[0], p);
    assert_eq!(shapes[1], sfcn(vec![mv("p"), mv("q")], sseq(srec(&[("den", sint(0, 23)), ("num", sint(0, 10))]), 8)));
    // Other field names: unchanged.
    assert_eq!(shapes[2], other);
}

#[test]
fn grown_integer_ranges() {
    use tlx_layout::infer::{grown_ints, map_value_ints};
    let old = sfcn(vec![mv("p")], srec(&[("a", sint(0, 12)), ("b", Shape::Bool)]));
    let new = sfcn(vec![mv("p")], srec(&[("a", sint(0, 19)), ("b", Shape::Bool)]));
    let mut g = Vec::new();
    grown_ints(&old, &new, &mut g);
    assert_eq!(g, vec![((0, 12), (0, 19))]);
    // Value positions only: set elements keep their range.
    let s = stup(vec![sint(-5, 12), sset(sint(0, 12), 3), sint(0, 11)]);
    let w = map_value_ints(&s, &mut |lo, hi| (hi == 12).then_some((lo, 19)));
    assert_eq!(w, stup(vec![sint(-5, 19), sset(sint(0, 12), 3), sint(0, 11)]));
}

fn lazy(l: tlx_value::LazySet) -> Value {
    Value::LazySet(Arc::new(l))
}

#[test]
fn type_invariant_bounds() {
    use tlx_layout::infer::{bound_covers, refine, set_elem_bound};
    use tlx_value::LazySet as L;
    let p = set(vec![mv("p"), mv("q")]);
    // Msg == [type : {"req"}, from : P, k : 0..2] \cup [type : {"ack"}]
    let req = lazy(L::RecordSet(vec![
        (Sym::new("from"), p.clone()),
        (Sym::new("k"), Value::Interval(0, 2)),
        (Sym::new("type"), set(vec![st("req")])),
    ]));
    let ack = lazy(L::RecordSet(vec![(Sym::new("type"), set(vec![st("ack")]))]));
    let msg = lazy(L::Cup(req, ack));
    let req_shape = srec(&[("from", satom(vec![mv("p"), mv("q")])), ("k", sint(0, 2)), ("type", satom(vec![st("req")]))]);
    let ack_shape = srec(&[("type", satom(vec![st("ack")]))]);
    let union = |arms: Vec<Shape>| {
        let mut arms = arms;
        arms.sort_by_cached_key(|a| a.kind_key());
        Shape::Union(Arc::from(arms))
    };
    assert_eq!(set_elem_bound(&msg), union(vec![req_shape.clone(), ack_shape.clone()]));
    // msgs \in SUBSET Msg
    let b = set_elem_bound(&lazy(L::Subset(msg.clone())));
    assert_eq!(b, sset(union(vec![req_shape.clone(), ack_shape.clone()]), 7));
    // [P -> 0..3], Seq(BOOLEAN), Nat
    assert_eq!(set_elem_bound(&lazy(L::FcnSet(p.clone(), Value::Interval(0, 3)))), sfcn(vec![mv("p"), mv("q")], sint(0, 3)));
    assert_eq!(set_elem_bound(&lazy(L::Seq(set(vec![Value::Bool(false), Value::Bool(true)])))), sseq(Shape::Bool, usize::MAX));
    assert_eq!(set_elem_bound(&lazy(L::Nat)), Shape::Dyn);

    // The pre-run saw only requests; the layout shape has headroom (integer
    // ranges and atom universes larger than the bound) and is a sorted
    // array of records (too many possible elements for a bitset).
    let all = satom(vec![st("ack"), st("req"), st("idle")]);
    let seen = sset(srec(&[("from", satom(vec![mv("p")])), ("k", sint(0, 1)), ("type", satom(vec![st("req")]))]), 2);
    let layout = sset(srec(&[("from", satom(vec![mv("p"), mv("q")])), ("k", sint(0, 1000)), ("type", all.clone())]), 4);
    assert_eq!(words(&layout), 1 + 4);
    assert!(bound_covers(&b, &seen));
    // Refined: a bitset over all messages (the unobserved arm added, the
    // field `type` alike in both arms, exact ranges).
    let types = satom(vec![st("ack"), st("req")]);
    let r = refine(&layout, &b);
    let want_req = srec(&[("from", satom(vec![mv("p"), mv("q")])), ("k", sint(0, 2)), ("type", types.clone())]);
    assert_eq!(r, sset(union(vec![want_req, srec(&[("type", types)])]), 7));
    assert_eq!(words(&r), 1);
    assert!(bound_covers(&r, &seen));
    // Not a bound of values outside it.
    assert!(!bound_covers(&b, &sset(srec(&[("type", satom(vec![st("other")]))]), 1)));
    // A set that is a bitset already stays.
    let small = sset(satom(vec![mv("p"), mv("q"), mv("r")]), 3);
    assert_eq!(refine(&small, &sset(satom(vec![mv("p"), mv("q")]), 2)), small);
    // Outside set elements, atom universes keep the hint atoms; integer
    // ranges grow to include the bound's; sequences get the bound's length.
    let v = refine(
        &srec(&[("k", sint(0, 3)), ("s", all.clone()), ("q", sseq(sint(0, 3), 8))]),
        &srec(&[("k", sint(0, 9)), ("s", satom(vec![st("idle")])), ("q", sseq(sint(1, 2), 4))]),
    );
    assert_eq!(v, srec(&[("k", sint(0, 9)), ("s", all), ("q", sseq(sint(0, 3), 4))]));
}

#[test]
fn packed_industrial_shapes_achieve_over_3x_compression_and_canonical_words() {
    use tlx_layout::permute::PermPlan;
    use tlx_layout::LayoutNode;

    // 1. ReprMoveRange-style shard descriptor record + per-key routing function:
    //    Unpacked would take 6 + 8 = 14 words; packed takes 1 + 1 = 2 words (7x).
    let owners = vec![mv("n1"), mv("n2"), mv("n3")];
    let phases = satom(vec![st("idle"), st("moving"), st("splitting"), st("ready")]);
    let move_rec = srec(&[
        ("active", Shape::Bool),
        ("epoch", sint(0, 15)),
        ("hi", sint(0, 31)),
        ("lo", sint(0, 31)),
        ("owner", satom(owners.clone())),
        ("phase", phases),
    ]);
    let routing = sfcn((1..=8).map(int).collect(), satom(owners.clone()));
    let move_layout = Layout::new(vec![move_rec.clone(), routing]);
    assert_eq!(words(&move_rec), 1);
    assert_eq!(move_layout.words, 2, "expected 7x compression (14 -> 2 words)");

    // 2. ReprZab-style per-replica scalar functions, replica descriptor record, and zxid sequence:
    //    Unpacked would take 4 * 5 + 4 + (1 + 8) = 33 words; packed takes 4 * 1 + 1 + 2 = 7 words (4.7x),
    //    and a function of replica records shrinks 20 -> 5 words (4.0x).
    let servers: Vec<Value> = (1..=5).map(|i| mv(&format!("s{i}"))).collect();
    let roles = satom(vec![st("election"), st("following"), st("leading")]);
    let zab_replica = srec(&[("epoch", sint(0, 7)), ("role", roles.clone()), ("synced", Shape::Bool), ("zxid", sint(0, 31))]);
    assert_eq!(words(&sfcn(servers.clone(), zab_replica.clone())), 5);
    let zab_layout = Layout::new(vec![
        sfcn(servers.clone(), sint(0, 7)),
        sfcn(servers.clone(), roles),
        sfcn(servers.clone(), Shape::Bool),
        sfcn(servers, sint(0, 31)),
        zab_replica,
        sseq(sint(0, 31), 8),
    ]);
    assert_eq!(zab_layout.words, 7, "expected 4.7x compression (33 -> 7 words)");

    // 3. MultiPaxos_MC-style acceptor state + partial slot maps:
    //    Unpacked would take 3 * 3 + (1 + 8) + (1 + 8) = 27 words; packed takes 3 + 2 + 2 = 7 words (3.86x).
    let accs = vec![mv("a1"), mv("a2"), mv("a3")];
    let vals = vec![mv("v1"), mv("v2")];
    let acc_state =
        sfcn(accs, srec(&[("maxBal", sint(-1, 7)), ("maxVBal", sint(-1, 7)), ("maxVal", satom(vec![mv("none"), mv("v1"), mv("v2")]))]));
    let slot_bal = Shape::Map { key: Box::new(sint(1, 8)), range: Box::new(sint(0, 7)), witness: FcnWitness::Enumerated };
    let slot_val = Shape::Map { key: Box::new(sint(1, 8)), range: Box::new(satom(vals)), witness: FcnWitness::Enumerated };
    let paxos_layout = Layout::new(vec![acc_state, slot_bal, slot_val]);
    assert_eq!(paxos_layout.words, 7, "expected >3.8x compression (27 -> 7 words)");

    // Canonical zero-padding and permutation invariance: encoding into dirty buffers yields
    // identical raw words, and applying a symmetry permutation + inverse restores exact words.
    let s_val = [
        fcn(vec![
            (mv("a1"), rec(&[("maxBal", int(2)), ("maxVBal", int(1)), ("maxVal", mv("v1"))])),
            (mv("a2"), rec(&[("maxBal", int(-1)), ("maxVBal", int(-1)), ("maxVal", mv("none"))])),
            (mv("a3"), rec(&[("maxBal", int(4)), ("maxVBal", int(3)), ("maxVal", mv("v2"))])),
        ]),
        fcn(vec![(int(1), int(2)), (int(5), int(4))]),
        fcn(vec![(int(1), mv("v1")), (int(5), mv("v2"))]),
    ];
    let (mut w1, mut w2) = (vec![u64::MAX; paxos_layout.words], vec![0xaaaa_5555_aaaa_5555; paxos_layout.words]);
    paxos_layout.encode_state(&s_val, &mut w1).unwrap();
    paxos_layout.encode_state(&s_val, &mut w2).unwrap();
    assert_eq!(w1, w2, "dirty buffer bits leaked into canonical encoding");
    paxos_layout.validate_words(&w1).unwrap();
    assert_eq!(paxos_layout.decode_state(&w1), s_val.to_vec());

    // Symmetry permutation (swap a1 <-> a3 and v1 <-> v2 twice = identity) preserves exact words.
    let atom_perm: tlx_layout::permute::AtomPerm = Arc::new(|v: &Value| match v {
        Value::ModelValue(m) if m.as_str() == "a1" => mv("a3"),
        Value::ModelValue(m) if m.as_str() == "a3" => mv("a1"),
        Value::ModelValue(m) if m.as_str() == "v1" => mv("v2"),
        Value::ModelValue(m) if m.as_str() == "v2" => mv("v1"),
        _ => v.clone(),
    });
    let state_tup = stup(paxos_layout.vars.to_vec());
    let perm = PermPlan::compile(&state_tup, &atom_perm).expect("closed symmetry plan");
    let (mut p1, mut p2) = (vec![0xdead_beef; paxos_layout.words], vec![0xcafe_babe; paxos_layout.words]);
    perm.apply(&w1, &mut p1);
    paxos_layout.validate_words(&p1).unwrap();
    perm.apply(&p1, &mut p2);
    assert_eq!(p2, w1, "double involution symmetry permutation drifted from canonical words");

    // LayoutNode transcode across packed bit-width growth preserves exact values and zero padding.
    let wider_node = LayoutNode::new(&srec(&[
        ("active", Shape::Bool),
        ("epoch", sint(0, 1023)),
        ("hi", sint(-100, 500)),
        ("lo", sint(-100, 500)),
        ("owner", satom(vec![mv("n1"), mv("n2"), mv("n3"), mv("n4"), mv("n5")])),
        ("phase", satom(vec![st("done"), st("idle"), st("moving"), st("ready"), st("splitting")])),
    ]));
    let narrow_node = LayoutNode::new(&move_rec);
    let sample =
        rec(&[("active", Value::TRUE), ("epoch", int(9)), ("hi", int(25)), ("lo", int(3)), ("owner", mv("n2")), ("phase", st("moving"))]);
    let mut nw = vec![0u64; narrow_node.words()];
    narrow_node.encode(&sample, &mut nw).unwrap();
    let mut ww = vec![0u64; wider_node.words()];
    assert!(tlx_layout::layout_tree::transcode(&narrow_node, &wider_node, &nw, &mut ww));
    wider_node.validate_words(&ww).unwrap();
    assert_eq!(wider_node.decode(&ww), sample);
}

#[test]
fn validate_words_rejects_corrupted_packed_bits_and_padding() {
    use tlx_layout::pack::{FieldLayout, FieldLoc, SlotLayout};
    use tlx_layout::LayoutNode;

    // 1. Packed Record: 3-element Atom (2 bits, valid codes 0..=2), Int 10..12 (2 bits, valid 0..=2), Bool (1 bit).
    //    Bits 59..64 are used; bits 0..59 are unused padding and must be 0.
    let rec_shape = srec(&[("atom", satom(vec![st("a"), st("b"), st("c")])), ("flag", Shape::Bool), ("num", sint(10, 12))]);
    let node = LayoutNode::new(&rec_shape);
    let fl = FieldLayout::of_shape(&rec_shape).unwrap();
    let mut valid = vec![0u64; node.words()];
    node.encode(&rec(&[("atom", st("b")), ("flag", Value::TRUE), ("num", int(12))]), &mut valid).unwrap();
    node.validate_words(&valid).unwrap();

    // Corrupt a low padding bit.
    let mut bad_pad = valid.clone();
    bad_pad[0] |= 1;
    assert!(node.validate_words(&bad_pad).is_err(), "accepted non-zero padding bit");

    // Corrupt 2-bit Atom code to 3 (universe has 3 elements: 0, 1, 2).
    let Shape::Record(fields) = &rec_shape else { unreachable!() };
    let atom_idx = fields.iter().position(|(k, _)| k.as_str() == "atom").unwrap();
    let num_idx = fields.iter().position(|(k, _)| k.as_str() == "num").unwrap();
    let FieldLoc::Bits(atom_pos) = fl.locs[atom_idx] else { panic!("expected packed atom") };
    let mut bad_atom = valid.clone();
    atom_pos.insert(&mut bad_atom, 3);
    assert!(node.validate_words(&bad_atom).is_err(), "accepted out-of-range packed atom code");

    // Corrupt 2-bit Int code to 3 (span is 2: valid codes 0, 1, 2).
    let FieldLoc::Bits(num_pos) = fl.locs[num_idx] else { panic!("expected packed int") };
    let mut bad_int = valid.clone();
    num_pos.insert(&mut bad_int, 3);
    assert!(node.validate_words(&bad_int).is_err(), "accepted out-of-range packed int code");

    // 2. Packed Map: key 1..4, range Int 0..2 (2 bits).
    //    Absent key slots and presence-word tail bits must be 0.
    let map_shape = Shape::Map { key: Box::new(sint(1, 4)), range: Box::new(sint(0, 2)), witness: FcnWitness::Enumerated };
    let map_node = LayoutNode::new(&map_shape);
    let mut map_w = vec![0u64; map_node.words()];
    map_node.encode(&fcn(vec![(int(1), int(2)), (int(3), int(1))]), &mut map_w).unwrap();
    map_node.validate_words(&map_w).unwrap();

    // Corrupt presence tail bit (key universe is 4, so bit 4 is out of range).
    let mut bad_pres = map_w.clone();
    bad_pres[0] |= 1 << 4;
    assert!(map_node.validate_words(&bad_pres).is_err(), "accepted map presence tail bit");

    // Corrupt absent slot 1 (key = 2 is absent) in the packed value word.
    let mut bad_absent = map_w.clone();
    SlotLayout::insert(2, &mut bad_absent[1..], 1, 1);
    assert!(map_node.validate_words(&bad_absent).is_err(), "accepted non-zero absent map slot");

    // 3. Packed Seq: max_len = 5, elem = Int 0..2 (2 bits).
    //    Inactive tail slot (index >= len) and tail padding bits must be 0.
    let seq_shape = sseq(sint(0, 2), 5);
    let seq_node = LayoutNode::new(&seq_shape);
    let mut seq_w = vec![0u64; seq_node.words()];
    seq_node.encode(&tup(vec![int(2), int(1)]), &mut seq_w).unwrap();
    seq_node.validate_words(&seq_w).unwrap();

    let mut bad_tail = seq_w.clone();
    SlotLayout::insert(2, &mut bad_tail[1..], 2, 1);
    assert!(seq_node.validate_words(&bad_tail).is_err(), "accepted non-zero inactive sequence slot");
}

#[test]
fn packed_zero_width_middle_preserves_symmetry_orbits() {
    use tlx_layout::permute::{AtomPerm, PermPlan};

    let a = mv("a");
    let b = mv("b");
    let atoms = satom(vec![a.clone(), b.clone()]);
    let swap: AtomPerm = Arc::new({
        let (a, b) = (a.clone(), b.clone());
        move |x| if x == &a { b.clone() } else { a.clone() }
    });

    // Empty tuple between Bool and Atom shares physical word 0: swapping a <-> b
    // must preserve the leading Bool (`<<TRUE, <<>>, a>>` -> `<<TRUE, <<>>, b>>`).
    let bool_mid = stup(vec![Shape::Bool, stup(vec![]), atoms.clone()]);
    assert_eq!(words(&bool_mid), 1);
    let p_bool = PermPlan::compile(&bool_mid, &swap).unwrap();
    let src_val = tup(vec![Value::TRUE, tup(vec![]), a.clone()]);
    let expected = tup(vec![Value::TRUE, tup(vec![]), b.clone()]);
    let src_w = enc(&bool_mid, &src_val).unwrap();
    let mut dst_w = vec![0u64; words(&bool_mid)];
    p_bool.apply(&src_w, &mut dst_w);
    assert_eq!(decode(&bool_mid, &dst_w), expected);

    // Two atoms separated by an empty tuple stay in one word and keep distinct orbits.
    let atom_mid = stup(vec![atoms.clone(), stup(vec![]), atoms]);
    assert_eq!(words(&atom_mid), 1);
    let p_atom = PermPlan::compile(&atom_mid, &swap).unwrap();
    let mut dst = vec![0u64; 1];
    p_atom.apply(&[0], &mut dst);
    assert_eq!(dst, vec![3 << 62]);
    let rep = |word: u64| {
        let mut out = [0];
        p_atom.apply(&[word], &mut out);
        word.min(out[0])
    };
    assert_ne!(rep(0), rep(1 << 62));
}

#[test]
fn transcode_union_payload_to_packed_scalar_field() {
    use tlx_layout::layout_tree::{transcode, LayoutNode};

    let union = Shape::Union(vec![Shape::Bool, sint(0, 1)].into());
    let old = LayoutNode::new(&stup(vec![union]));
    let new = LayoutNode::new(&stup(vec![Shape::Bool]));
    let value = tup(vec![Value::TRUE]);
    let mut src = vec![0u64; old.words()];
    old.encode(&value, &mut src).unwrap();
    let mut dst = vec![0u64; new.words()];
    assert!(transcode(&old, &new, &src, &mut dst));
    new.validate_words(&dst).unwrap();
    assert_eq!(new.decode(&dst), value);
}

#[test]
fn large_child_widths_preserve_host_size_and_map_budget() {
    let inner = sseq(sint(i64::MIN, i64::MAX), u32::MAX as usize);
    assert_eq!(words(&inner), 1usize << 32);
    let outer = sseq(inner.clone(), 1);
    assert_eq!(words(&outer), (1usize << 32) + 1);
    assert_eq!(tlx_layout::shape::map_shape(Shape::Bool, inner, FcnWitness::Enumerated), Shape::Dyn);
}
