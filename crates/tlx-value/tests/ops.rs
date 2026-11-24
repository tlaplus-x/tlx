mod common;

use std::sync::Arc;

use common::*;
use tlx_value::fingerprint::fingerprint;
use tlx_value::order::eq_tlc;
use tlx_value::{ops, CustomSet, LazySet, Sym, Value, ValueErrorKind};

fn lazy(l: LazySet) -> Value {
    Value::LazySet(Arc::new(l))
}

fn nat() -> Value {
    lazy(LazySet::Nat)
}

#[test]
fn heterogeneous_literal_defers_comparisons_until_consumed() {
    let values = vec![int(0), rec(&[("a", int(1))])];
    let mixed = Value::set_enum(values).unwrap();
    assert!(ops::member(&int(0), &mixed).unwrap());
    assert!(ops::cardinality(&mixed).is_err());
    assert!(fingerprint(&mixed).is_err());
    assert!(ops::enumerate(&mixed).is_err());
    assert!(eq_tlc(&mixed, &mixed).is_err());
}

#[test]
fn heterogeneous_filter_scans_without_normalizing_source() {
    let f = ops::single_fcn(int(1), int(-1)).unwrap();
    let r = rec(&[("a", int(1)), ("b", int(0))]);
    let mixed = Value::set_enum(vec![f.clone(), r.clone()]).unwrap();
    let singleton = Value::set_enum(vec![f.clone()]).unwrap();
    assert_eq!(ops::difference(&mixed, &singleton).unwrap().normalize().unwrap(), set(vec![r]));
    assert_eq!(ops::intersect(&mixed, &singleton).unwrap().normalize().unwrap(), set(vec![f]));
}

// ---- canonical forms ----

#[test]
fn canonical_forms() {
    assert!(matches!(fcn(vec![]), Value::Tuple(ref t) if t.is_empty()));
    assert!(matches!(Value::record(vec![]), Value::Tuple(ref t) if t.is_empty()));
    let t = fcn(vec![(int(2), s("cfx_b")), (int(1), s("cfx_a"))]);
    assert!(matches!(t, Value::Tuple(_)));
    assert_eq!(t.to_string(), r#"<<"cfx_a", "cfx_b">>"#);
    Sym::new("cf_a");
    Sym::new("cf_b");
    let r = fcn(vec![(s("cf_b"), int(2)), (s("cf_a"), int(1))]);
    assert!(matches!(r, Value::Record(_)));
    assert_eq!(r.to_string(), "[cf_a |-> 1, cf_b |-> 2]");
    let f = fcn(vec![(int(1), int(1)), (int(0), int(0))]);
    assert!(matches!(f, Value::Fcn(..)));
    assert_eq!(f.to_string(), "(0 :> 0 @@ 1 :> 1)");
    let f = fcn(vec![(int(2), int(1)), (int(3), int(0))]);
    assert!(matches!(f, Value::Fcn(..)));
    assert!(Value::fcn_from_pairs(vec![(int(1), int(1)), (int(1), int(2))]).is_err());
    assert!(Value::fcn_from_pairs(vec![(int(1), int(1)), (s("a"), int(2))]).is_err());
    // records: duplicates, last wins
    let r = Value::record(vec![(Sym::new("cf_b"), int(1)), (Sym::new("cf_a"), int(2)), (Sym::new("cf_b"), int(3))]);
    assert_eq!(r.to_string(), "[cf_a |-> 2, cf_b |-> 3]");
    // :> builds a function over an enumerated domain (TLC FcnRcdValue),
    // equal to the canonical form
    let t = ops::single_fcn(int(1), s("x")).unwrap();
    assert!(matches!(t, Value::Fcn(..)));
    assert_eq!(t, tup(vec![s("x")]));
    assert_eq!(t.to_string(), "<<\"x\">>");
    let r = ops::single_fcn(s("cf_a"), int(1)).unwrap();
    assert!(matches!(r, Value::Fcn(..)));
    assert_eq!(r, rec(&[("cf_a", int(1))]));
    assert_eq!(r.to_string(), "[cf_a |-> 1]");
    assert!(matches!(ops::single_fcn(int(0), int(1)).unwrap(), Value::Fcn(..)));
    // set-of-sets with mixed representations deduplicates
    let v = set(vec![ops::interval(1, 2), ints(&[1, 2]), ints(&[])]);
    assert_eq!(ops::cardinality(&v).unwrap(), 2);
}

#[test]
fn except_keeps_representation() {
    let t = tup(vec![int(1), int(2)]);
    let t2 = ops::except(&t, &int(2), int(9)).unwrap();
    assert!(matches!(t2, Value::Tuple(_)));
    assert_eq!(t2.to_string(), "<<1, 9>>");
    assert!(ops::except(&t, &int(3), int(9)).is_err());
    assert!(ops::except(&t, &s("a"), int(9)).is_err());
    let r = rec(&[("ex_a", int(1)), ("ex_b", int(2))]);
    let r2 = ops::except(&r, &s("ex_b"), int(5)).unwrap();
    assert!(matches!(r2, Value::Record(_)));
    assert_eq!(ops::field(&r2, Sym::new("ex_b")).unwrap(), int(5));
    assert!(ops::except(&r, &s("ex_c"), int(5)).is_err());
    let f = fcn(vec![(int(0), int(0)), (int(5), int(5))]);
    let f2 = ops::except(&f, &int(5), int(6)).unwrap();
    assert_eq!(f2.to_string(), "(0 :> 0 @@ 5 :> 6)");
    assert!(ops::except(&f, &int(1), int(6)).is_err());
    // lazy function EXCEPT stays lazy and overrides one point
    let lf = scale(ops::interval(1, 3), 10);
    let lf2 = ops::except(&lf, &int(2), int(0)).unwrap();
    assert!(matches!(lf2, Value::LazyFcn(_)));
    assert_eq!(lf2.normalize().unwrap().to_string(), "<<10, 0, 30>>");
    assert!(ops::except(&lf, &int(4), int(0)).is_err());
    // select: TLC-style lookup without erroring on missing keys
    assert_eq!(ops::select(&t, &int(3)).unwrap(), None);
    assert_eq!(ops::select(&t, &int(1)).unwrap(), Some(int(1)));
    assert!(ops::select(&t, &s("a")).is_err());
    assert_eq!(ops::select(&r, &s("ex_c")).unwrap(), None);
    assert!(ops::select(&r, &int(1)).is_err());
}

#[test]
fn function_ops() {
    let t = tup(vec![s("a"), s("b")]);
    assert_eq!(ops::apply(&t, &int(2)).unwrap(), s("b"));
    assert_eq!(err_msg(ops::apply(&t, &int(3))), "Attempted to access index 3 of tuple\n<<\"a\", \"b\">>\nwhich is out of bounds.");
    assert!(ops::apply(&t, &s("x")).is_err());
    assert_eq!(ops::domain(&t).unwrap(), ops::interval(1, 2));
    assert_eq!(ops::domain(&tup(vec![])).unwrap(), Value::empty_set());
    let r = rec(&[("fo_a", int(1))]);
    assert_eq!(ops::apply(&r, &s("fo_a")).unwrap(), int(1));
    assert!(ops::apply(&r, &s("fo_zz")).is_err());
    assert!(ops::field(&r, Sym::new("fo_zz")).is_err());
    assert!(ops::field(&t, Sym::new("fo_a")).is_err());
    assert_eq!(ops::domain(&r).unwrap(), set(vec![s("fo_a")]));
    let f = fcn(vec![(ints(&[1]), int(1)), (ints(&[]), int(0))]);
    assert_eq!(ops::apply(&f, &ops::interval(1, 1)).unwrap(), int(1));
    assert!(ops::apply(&f, &ints(&[2])).is_err());
    assert!(ops::apply(&f, &int(2)).is_err()); // integer vs set: comparison error
    assert!(ops::apply(&int(1), &int(1)).is_err());
    assert!(ops::domain(&ints(&[1])).is_err());
    // big Fcn uses binary search
    let big = fcn((0..100).map(|i| (int(i * 2), int(i))).collect());
    assert_eq!(ops::apply(&big, &int(42)).unwrap(), int(21));
    assert!(ops::apply(&big, &int(43)).is_err());
    // lazy function
    let lf = scale(nat(), 3);
    assert_eq!(ops::apply(&lf, &int(4)).unwrap(), int(12));
    assert!(ops::is_finite_set(&lf).is_ok_and(|b| !b));
    assert!(lf.normalize().is_err());
}

#[test]
fn fcn_merge() {
    let a = ops::single_fcn(int(1), s("x")).unwrap();
    let b = ops::single_fcn(int(2), s("y")).unwrap();
    assert_eq!(ops::fcn_merge(&a, &b).unwrap().to_string(), r#"<<"x", "y">>"#);
    assert_eq!(ops::fcn_merge(&b, &a).unwrap().to_string(), r#"<<"x", "y">>"#);
    let c = ops::single_fcn(int(1), s("z")).unwrap();
    assert_eq!(ops::fcn_merge(&a, &c).unwrap(), a); // left wins
    let d = ops::single_fcn(int(3), s("w")).unwrap();
    assert_eq!(ops::fcn_merge(&a, &d).unwrap().to_string(), r#"(1 :> "x" @@ 3 :> "w")"#);
    let r1 = rec(&[("fm_a", int(1))]);
    let r2 = rec(&[("fm_a", int(2)), ("fm_b", int(3))]);
    assert_eq!(ops::fcn_merge(&r1, &r2).unwrap().to_string(), "[fm_a |-> 1, fm_b |-> 3]");
    assert!(ops::fcn_merge(&a, &r1).is_err()); // 1 vs "fm_a": incomparable
    assert!(ops::fcn_merge(&a, &ints(&[1])).is_err());
    let e = tup(vec![]);
    assert_eq!(ops::fcn_merge(&e, &r1).unwrap(), r1);
}

// ---- sets ----

#[test]
fn union_preserves_incomparable_operand_errors() {
    for (left, right) in [(ints(&[1]), set(vec![s("a")])), (set(vec![ints(&[1])]), ints(&[1]))] {
        assert!(ops::union(&left, &right).is_err());
        assert!(ops::union(&right, &left).is_err());
    }
}

#[test]
fn union_keeps_unchanged_contents_and_interval_representation() {
    let left = ints(&[1, 3, 5]);
    for right in [ints(&[]), ints(&[3]), ints(&[1, 3, 5])] {
        let result = ops::union(&left, &right).unwrap();
        assert_eq!(result, left);
        let (Value::Set(a), Value::Set(b)) = (&left, &result) else { unreachable!() };
        assert!(Arc::ptr_eq(a, b), "inert unchanged contents should share");
    }
    for right in [ints(&[0]), ints(&[2, 3]), ints(&[6]), ints(&[0, 3, 6])] {
        let mut all = ops::enumerate_normalized(&left).unwrap();
        all.extend(ops::enumerate_normalized(&right).unwrap());
        assert_eq!(ops::union(&left, &right).unwrap(), set(all));
    }
    assert!(matches!(ops::union(&ops::interval(1, 2), &ints(&[])).unwrap(), Value::Set(_)));
}

#[test]
fn union_does_not_hide_a_later_comparison_error_in_its_unchanged_tail() {
    let records: Vec<_> =
        (1..=6).map(|i| rec(&[("a", int(i)), ("b", if i == 6 { ops::interval(0, i32::MAX as i64) } else { ints(&[]) })])).collect();
    let left = set(records.clone());
    // Different `a` fields determine the merge before `b` is compared.
    for right in [set(records[..1].to_vec()), set(records[..5].to_vec())] {
        let result = ops::union(&left, &right).unwrap();
        assert!(Value::set_from(vec![left.clone(), result]).is_err());
    }
}

#[test]
fn self_comparison_proof_checks_every_materialized_child() {
    use tlx_value::order::self_comparison_is_inert as inert;
    let bad = ops::interval(0, i32::MAX as i64);
    for v in [
        int(1),
        Value::Bool(true),
        s("a"),
        mv("a_1"),
        ops::interval(1, 3),
        ints(&[1, 2]),
        tup(vec![int(1)]),
        rec(&[("a", int(1))]),
        ops::single_fcn(int(0), int(1)).unwrap(),
    ] {
        assert!(inert(&v), "{v}");
    }
    for v in [
        bad.clone(),
        set(vec![bad.clone()]),
        tup(vec![bad.clone()]),
        rec(&[("a", bad.clone())]),
        ops::single_fcn(bad.clone(), int(1)).unwrap(),
        ops::single_fcn(int(0), bad).unwrap(),
        nat(),
        scale(nat(), 1),
    ] {
        assert!(!inert(&v), "{v}");
    }
}

#[test]
fn union_tail_lazy_values_keep_later_forcing_errors() {
    for bad in [ops::powerset(&nat()).unwrap(), scale(nat(), 1)] {
        let first = rec(&[("a", int(0)), ("b", int(0))]);
        let left = set(vec![first.clone(), rec(&[("a", int(1)), ("b", bad)])]);
        let result = ops::union(&left, &set(vec![first])).unwrap();
        assert!(Value::set_from(vec![left, result]).is_err());
    }
}

#[test]
fn union_tail_predicate_keeps_later_effects_and_errors() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    #[derive(Debug)]
    struct Predicate(Arc<AtomicUsize>);
    impl CustomSet for Predicate {
        fn contains(&self, _: &Value) -> tlx_value::Result<bool> {
            unreachable!("comparison enumerates this predicate")
        }
        fn enumerate(&self) -> tlx_value::Result<Option<Vec<Value>>> {
            if self.0.fetch_add(1, Ordering::SeqCst) == 0 {
                Ok(Some(vec![int(1)]))
            } else {
                Err(tlx_value::ValueError::new("predicate evaluated twice"))
            }
        }
    }
    let calls = Arc::new(AtomicUsize::new(0));
    let predicate = lazy(LazySet::Custom(Box::new(Predicate(calls.clone()))));
    let first = rec(&[("a", int(0)), ("b", int(0))]);
    let left = set(vec![first.clone(), rec(&[("a", int(1)), ("b", predicate)])]);
    let result = ops::union(&left, &set(vec![first])).unwrap();
    assert_eq!(calls.load(Ordering::SeqCst), 0, "the guard must not evaluate a predicate");
    assert!(Value::set_from(vec![left, result]).is_err());
    assert_eq!(calls.load(Ordering::SeqCst), 2);
}

#[test]
fn union_eager_and_lazy() {
    let u = ops::union(&ints(&[1, 3]), &ints(&[2, 3])).unwrap();
    assert!(matches!(u, Value::Set(_)));
    assert_eq!(u.to_string(), "{1, 2, 3}");
    let u = ops::union(&ops::interval(1, 3), &ints(&[0])).unwrap();
    assert!(matches!(u, Value::Set(_)));
    assert_eq!(u.to_string(), "{0, 1, 2, 3}");
    assert!(ops::union(&ints(&[1]), &set(vec![s("a")])).is_err());
    // empty enumerated side returns the other side unchanged (lazy stays lazy)
    let p = ops::powerset(&ints(&[1])).unwrap();
    assert!(matches!(ops::union(&Value::empty_set(), &p).unwrap(), Value::LazySet(_)));
    assert!(matches!(ops::union(&p, &ops::interval(1, 0)).unwrap(), Value::LazySet(_)));
    // (SUBSET {1}) \cup (SUBSET {1, 2}) is lazy and enumerates duplicates
    let q = ops::powerset(&ints(&[1, 2])).unwrap();
    let c = ops::union(&p, &q).unwrap();
    assert!(matches!(c, Value::LazySet(ref l) if matches!(**l, LazySet::Cup(..))));
    assert_eq!(enum_str(&c), "{} {1} {} {1} {2} {1, 2}");
    assert_eq!(ops::cardinality(&c).unwrap(), 4);
    assert_eq!(show(&ops::enumerate_normalized(&c).unwrap()), "{} {1} {2} {1, 2}");
    // one enumerated side: that side is enumerated first (TLC: arg2.cup(arg1))
    let c2 = ops::union(&p, &set(vec![ints(&[7])])).unwrap();
    assert_eq!(enum_str(&c2), "{7} {} {1}");
    assert!(ops::member(&ints(&[1]), &c2).unwrap());
    assert!(!ops::member(&ints(&[2]), &c2).unwrap());
    // a non-set operand is not checked (TLC: SetCupValue): it fails when used
    let c3 = ops::union(&int(1), &ints(&[1])).unwrap();
    assert!(matches!(c3, Value::LazySet(ref l) if matches!(**l, LazySet::Cup(..))));
    assert!(ops::member(&int(1), &c3).unwrap());
    assert!(ops::member(&int(2), &c3).is_err());
    assert_eq!(ops::union(&Value::empty_set(), &int(3)).unwrap(), int(3));
}

#[test]
fn big_union() {
    let u = ops::big_union(&set(vec![ints(&[1, 2]), ints(&[2, 3])])).unwrap();
    assert!(matches!(u, Value::Set(_)));
    assert_eq!(u.to_string(), "{1, 2, 3}");
    // UNION {1..2, 2..3}: elements are intervals -> lazy, duplicates on enumeration
    let u = ops::big_union(&set(vec![ops::interval(1, 2), ops::interval(2, 3)])).unwrap();
    assert!(matches!(u, Value::LazySet(_)));
    assert_eq!(enum_str(&u), "1 2 2 3");
    assert_eq!(ops::cardinality(&u).unwrap(), 3);
    assert!(ops::member(&int(3), &u).unwrap());
    assert!(!ops::member(&int(4), &u).unwrap());
    assert_eq!(u.to_string(), "{1, 2, 3}");
    let u = ops::big_union(&ops::powerset(&ints(&[1, 2])).unwrap()).unwrap();
    assert_eq!(enum_str(&u), "1 2 1 2");
    assert_eq!(ops::big_union(&Value::empty_set()).unwrap(), Value::empty_set());
}

#[test]
fn intersect_and_difference() {
    let i = ops::intersect(&ints(&[1, 2, 3]), &ops::interval(2, 9)).unwrap();
    assert!(matches!(i, Value::Set(_)));
    assert_eq!(i.to_string(), "{2, 3}");
    // lazy left, enumerated right: filters the right side
    let i = ops::intersect(&nat(), &ints(&[-1, 0, 5])).unwrap();
    assert_eq!(i.to_string(), "{0, 5}");
    let p = ops::powerset(&ints(&[1, 2])).unwrap();
    let i = ops::intersect(&p, &nat()).unwrap();
    assert!(matches!(i, Value::LazySet(_)));
    assert!(ops::enumerate(&i).is_err()); // {} \in Nat errors when filtering
    let i = ops::intersect(&p, &ops::powerset(&ints(&[2, 3])).unwrap()).unwrap();
    assert_eq!(enum_str(&i), "{} {2}");
    let d = ops::difference(&ops::interval(1, 5), &ints(&[2, 4])).unwrap();
    assert_eq!(d.to_string(), "{1, 3, 5}");
    let d = ops::difference(&p, &set(vec![ints(&[])])).unwrap();
    assert!(matches!(d, Value::LazySet(_)));
    assert_eq!(enum_str(&d), "{1} {2} {1, 2}");
    assert!(ops::member(&ints(&[1]), &d).unwrap());
    assert!(!ops::member(&ints(&[]), &d).unwrap());
    let d = ops::difference(&nat(), &ints(&[0])).unwrap();
    assert!(ops::member(&int(1), &d).unwrap());
    assert!(!ops::member(&int(0), &d).unwrap());
    assert!(ops::enumerate(&d).is_err());
    assert!(!ops::is_finite_set(&d).unwrap());
}

#[test]
fn subset_enumeration_order() {
    let p = ops::powerset(&ints(&[3, 1, 2])).unwrap();
    assert_eq!(enum_str(&p), "{} {1} {2} {3} {1, 2} {1, 3} {2, 3} {1, 2, 3}");
    assert_eq!(show(&ops::enumerate_normalized(&p).unwrap()), enum_str(&p));
    assert_eq!(enum_str(&ops::powerset(&Value::empty_set()).unwrap()), "{}");
    assert_eq!(ops::cardinality(&p).unwrap(), 8);
    assert!(ops::member(&ints(&[1, 3]), &p).unwrap());
    assert!(!ops::member(&ints(&[1, 4]), &p).unwrap());
    assert!(ops::member(&ops::interval(1, 2), &p).unwrap());
    assert!(ops::member(&int(1), &p).is_err());
    // infinite base
    let pn = ops::powerset(&nat()).unwrap();
    assert!(ops::member(&ints(&[1, 5]), &pn).unwrap());
    assert!(!ops::member(&ints(&[-1]), &pn).unwrap());
    assert!(ops::enumerate(&pn).is_err());
    // size guards
    let big = ops::powerset(&ops::interval(1, 31)).unwrap();
    assert!(err_msg(ops::cardinality(&big)).starts_with("Overflow"));
    assert!(err_msg(ops::enumerate(&big)).starts_with("Overflow"));
    assert_eq!(ops::cardinality(&ops::powerset(&ops::interval(1, 30)).unwrap()).unwrap(), 1 << 30);
    // the visitor works without the size guard (early exit)
    let mut first = None;
    ops::for_each_element(&big, &mut |e| {
        first = Some(e);
        Ok(false)
    })
    .unwrap();
    assert_eq!(first.unwrap(), Value::empty_set());
    // SUBSET A \subseteq SUBSET B reduces to A \subseteq B
    assert!(ops::subseteq(&big, &ops::powerset(&nat()).unwrap()).unwrap());
}

/// TLC's `Enumerable.elements()` (the default order) never asks a set for its
/// `size()`, so a set whose size overflows TLC's int is still enumerated
/// element by element: `Cardinality` (TLC's `Value.size`) and materializing the
/// set error, but the streaming enumeration visits its elements, and a caller
/// that stops early never needs the whole set. This is the path of `x' \in S`,
/// of a set filter and of printing; TLC's *bound* asks for the normalized order
/// instead, which materializes all but `SUBSET S` (`docs/compat.md` section 5).
///
/// `SpanningTree/SpanTreeTest5Nodes` (`Edges \in {E \in SUBSET (SUBSET Nodes) :
/// ...}`) and `CarTalkPuzzle/.../Model_3` (printing a set filter over
/// `[1..5 -> 1..121]`) used to fail with the overflow on this path.
#[test]
fn enumerating_a_set_whose_size_overflows() {
    let five = ops::interval(1, 5);
    let cases: Vec<Value> = vec![
        // 2^31 subsets of 31 elements.
        ops::powerset(&ops::interval(1, 31)).unwrap(),
        // `SUBSET (SUBSET Nodes)` with five nodes: 2^32 subsets (the domain of
        // `Edges` in `SpanningTree/SpanTreeTest5Nodes`).
        ops::powerset(&ops::powerset(&five).unwrap()).unwrap(),
        // `[1..5 -> 1..121]`: 121^5 functions (the domain of `Break` in
        // `CarTalkPuzzle/.../Model_3`).
        ops::fcn_set(&five, &ops::interval(1, 121)).unwrap(),
        // 2^40 functions 1..40 -> {0, 1}.
        ops::fcn_set(&ops::interval(1, 40), &ints(&[0, 1])).unwrap(),
    ];
    for s in &cases {
        assert!(ops::cardinality(s).is_err_and(|e| e.kind == ValueErrorKind::Overflow), "n({s}) does not overflow");
        assert!(ops::enumerate(s).is_err_and(|e| e.kind == ValueErrorKind::Overflow), "enumerate({s}) does not overflow");
        assert!(matches!(ops::materialization_error(s), Some(e) if e.kind == ValueErrorKind::Overflow));
        assert!(ops::materialization_error(&ops::powerset(&ops::interval(1, 30)).unwrap()).is_none());
        // The streaming enumeration yields the same elements in the same order
        // as `for_each_element` (which never had the size check), and it stops
        // early instead of enumerating the whole set.
        let mut streamed = Vec::new();
        ops::for_each_enumerated(s, &mut |e| {
            streamed.push(e);
            Ok(streamed.len() < 3)
        })
        .unwrap();
        let mut direct = Vec::new();
        ops::for_each_element(s, &mut |e| {
            direct.push(e);
            Ok(direct.len() < 3)
        })
        .unwrap();
        assert_eq!(streamed, direct);
        assert_eq!(streamed.len(), 3);
    }
    // A tuple or record set materializes its constituents (TLC's
    // SetOfTuplesValue/SetOfRcdsValue enumerator converts each of them with
    // `toSetEnum`, which asks for `size()`): a constituent that cannot be
    // materialized keeps the overflow here, as in TLC.
    let nested = ops::product(vec![ops::powerset(&ops::interval(1, 31)).unwrap(), five.clone()]).unwrap();
    assert!(ops::for_each_enumerated(&nested, &mut |_| Ok(true)).is_err());
    let rec = ops::record_set(vec![(Sym::new("ovf_a"), ops::powerset(&ops::interval(1, 31)).unwrap())]).unwrap();
    assert!(ops::for_each_enumerated(&rec, &mut |_| Ok(true)).is_err());
}

/// A bound variable's domain is streamed (`for_each_enumerated`) where it used
/// to be materialized and sorted (`enumerate_normalized`), so the streaming
/// order must be the normalized order: the evaluation order is tier 2 (`\E`
/// witness choice, the order of `Print` and of effects in a quantified body).
#[test]
fn streaming_order_is_the_normalized_order() {
    let cases: Vec<Value> = vec![
        ops::powerset(&ops::interval(1, 4)).unwrap(),
        ops::powerset(&ops::powerset(&ops::interval(1, 3)).unwrap()).unwrap(),
        ops::fcn_set(&ops::interval(1, 3), &set(vec![s("a"), s("b")])).unwrap(),
        ops::fcn_set(&ops::interval(1, 4), &ints(&[0, 1])).unwrap(),
        ops::product(vec![ints(&[1, 2]), set(vec![s("a"), s("b")])]).unwrap(),
        ops::record_set(vec![(Sym::new("ord_a"), ints(&[1, 2])), (Sym::new("ord_b"), set(vec![s("a"), s("b")]))]).unwrap(),
    ];
    for s in &cases {
        let normalized = ops::enumerate_normalized(s).unwrap();
        let mut streamed = Vec::new();
        ops::for_each_enumerated(s, &mut |e| {
            streamed.push(e);
            Ok(true)
        })
        .unwrap();
        assert_eq!(show(&streamed), show(&normalized), "{s} (n = {})", normalized.len());
    }
}

#[test]
fn fcn_set_enumeration_order() {
    let fs = ops::fcn_set(&ints(&[1, 2]), &set(vec![s("a"), s("b")])).unwrap();
    assert_eq!(enum_str(&fs), r#"<<"a", "a">> <<"a", "b">> <<"b", "a">> <<"b", "b">>"#);
    assert_eq!(ops::cardinality(&fs).unwrap(), 4);
    assert_eq!(enum_str(&ops::fcn_set(&Value::empty_set(), &nat()).unwrap()), "<<>>");
    assert_eq!(enum_str(&ops::fcn_set(&ints(&[1]), &Value::empty_set()).unwrap()), "");
    assert_eq!(ops::cardinality(&ops::fcn_set(&ints(&[1]), &Value::empty_set()).unwrap()).unwrap(), 0);
    Sym::new("fs_x");
    Sym::new("fs_y");
    let fs = ops::fcn_set(&set(vec![s("fs_y"), s("fs_x")]), &ints(&[0, 1])).unwrap();
    assert_eq!(enum_str(&fs), "[fs_x |-> 0, fs_y |-> 0] [fs_x |-> 0, fs_y |-> 1] [fs_x |-> 1, fs_y |-> 0] [fs_x |-> 1, fs_y |-> 1]");
    let fs = ops::fcn_set(&ints(&[0, 1]), &ints(&[5])).unwrap();
    assert_eq!(enum_str(&fs), "(0 :> 5 @@ 1 :> 5)");
    // membership, including infinite ranges and representation changes
    let fs = ops::fcn_set(&ops::interval(1, 2), &nat()).unwrap();
    assert!(ops::member(&tup(vec![int(0), int(7)]), &fs).unwrap());
    assert!(!ops::member(&tup(vec![int(0), int(-7)]), &fs).unwrap());
    assert!(!ops::member(&tup(vec![int(0)]), &fs).unwrap());
    assert!(ops::member(&scale(ops::interval(1, 2), 2), &fs).unwrap());
    assert!(ops::member(&int(1), &fs).is_err());
    assert!(!ops::member(&mv("fs_m"), &fs).unwrap());
    let fs = ops::fcn_set(&set(vec![s("fs_x")]), &ints(&[1])).unwrap();
    assert!(ops::member(&rec(&[("fs_x", int(1))]), &fs).unwrap());
    assert!(!ops::is_finite_set(&ops::fcn_set(&ints(&[1]), &nat()).unwrap()).unwrap());
    assert!(ops::is_finite_set(&ops::fcn_set(&Value::empty_set(), &nat()).unwrap()).unwrap());
    assert!(err_msg(ops::cardinality(&ops::fcn_set(&ops::interval(1, 40), &ints(&[0, 1])).unwrap())).starts_with("Overflow"));
}

#[test]
fn product_and_record_set_order() {
    let p = ops::product(vec![ints(&[1, 2]), set(vec![s("a"), s("b")])]).unwrap();
    assert_eq!(enum_str(&p), r#"<<1, "a">> <<1, "b">> <<2, "a">> <<2, "b">>"#);
    assert_eq!(ops::cardinality(&p).unwrap(), 4);
    assert!(ops::member(&tup(vec![int(2), s("a")]), &p).unwrap());
    assert!(!ops::member(&tup(vec![int(2)]), &p).unwrap());
    assert!(ops::member(&rec(&[("pr_a", int(1))]), &p).is_err());
    assert!(!ops::member(&fcn(vec![(int(0), int(1))]), &p).unwrap());
    // components are enumerated with their own (possibly duplicating) order
    let cup = ops::union(&ops::powerset(&ints(&[1])).unwrap(), &ops::powerset(&ints(&[1])).unwrap()).unwrap();
    let p = ops::product(vec![cup, ints(&[0])]).unwrap();
    assert_eq!(enum_str(&p), "<<{}, 0>> <<{1}, 0>> <<{}, 0>> <<{1}, 0>>");
    assert_eq!(ops::cardinality(&p).unwrap(), 2);
    let pn = ops::product(vec![nat(), ints(&[1])]).unwrap();
    assert!(ops::member(&tup(vec![int(3), int(1)]), &pn).unwrap());
    assert!(ops::enumerate(&pn).is_err());
    assert_eq!(enum_str(&ops::product(vec![nat(), Value::empty_set()]).unwrap()), "");

    Sym::new("rs_a");
    Sym::new("rs_b");
    let rs = ops::record_set(vec![(Sym::new("rs_b"), ints(&[1, 2])), (Sym::new("rs_a"), ints(&[3, 4]))]).unwrap();
    assert_eq!(enum_str(&rs), "[rs_a |-> 3, rs_b |-> 1] [rs_a |-> 3, rs_b |-> 2] [rs_a |-> 4, rs_b |-> 1] [rs_a |-> 4, rs_b |-> 2]");
    assert_eq!(ops::cardinality(&rs).unwrap(), 4);
    assert!(ops::member(&rec(&[("rs_a", int(3)), ("rs_b", int(2))]), &rs).unwrap());
    assert!(!ops::member(&rec(&[("rs_a", int(3))]), &rs).unwrap());
    assert!(!ops::member(&rec(&[("rs_a", int(5)), ("rs_b", int(2))]), &rs).unwrap());
    assert!(ops::member(&tup(vec![int(1)]), &rs).is_err());
    let rn = ops::record_set(vec![(Sym::new("rs_a"), nat())]).unwrap();
    assert!(ops::member(&rec(&[("rs_a", int(3))]), &rn).unwrap());
    assert!(ops::enumerate(&rn).is_err());
    assert_eq!(rs.to_string(), "{[rs_a |-> 3, rs_b |-> 1], [rs_a |-> 3, rs_b |-> 2], [rs_a |-> 4, rs_b |-> 1], [rs_a |-> 4, rs_b |-> 2]}");
    assert_eq!(rn.to_string(), "[rs_a: Nat]");
}

#[test]
fn enumerate_normalized_for_choose() {
    let c = ops::union(&ops::powerset(&ints(&[2])).unwrap(), &ops::powerset(&ints(&[1])).unwrap()).unwrap();
    assert_eq!(enum_str(&c), "{} {2} {} {1}");
    assert_eq!(show(&ops::enumerate_normalized(&c).unwrap()), "{} {1} {2}");
    let p = ops::product(vec![ints(&[2, 1]), ints(&[1])]).unwrap();
    assert_eq!(show(&ops::enumerate_normalized(&p).unwrap()), "<<1, 1>> <<2, 1>>");
    assert!(ops::enumerate_normalized(&nat()).is_err());
    assert!(ops::enumerate_normalized(&int(1)).is_err());
}

#[test]
fn normalized_and_cardinality_from_one_enumeration() {
    // (The compiler's constant lowering enumerates a set once and derives
    // the normalized elements and the cardinality from that.)
    let sets = [
        ints(&[3, 1, 2]),
        ops::interval(2, 5),
        ops::powerset(&ints(&[3, 1, 2])).unwrap(),
        ops::union(&ops::powerset(&ints(&[2])).unwrap(), &ops::powerset(&ints(&[1])).unwrap()).unwrap(),
        ops::product(vec![ints(&[2, 1]), ints(&[1])]).unwrap(),
        ops::fcn_set(&ints(&[1, 2]), &ints(&[5, 4])).unwrap(),
    ];
    for s in &sets {
        let elems = ops::enumerate(s).unwrap();
        let n = ops::normalize_enumerated(s, elems).unwrap();
        assert_eq!(show(&n), show(&ops::enumerate_normalized(s).unwrap()));
        assert_eq!(ops::cardinality_of_normalized(s, &n).unwrap(), ops::cardinality(s).unwrap());
    }
    assert!(ops::normalize_enumerated(&int(1), vec![]).is_err());
}

#[test]
fn infinite_sets() {
    let int_set = lazy(LazySet::Int);
    let string = lazy(LazySet::StringSet);
    assert!(ops::member(&int(0), &nat()).unwrap());
    assert!(!ops::member(&int(-1), &nat()).unwrap());
    assert!(ops::member(&int(-1), &int_set).unwrap());
    assert!(!ops::member(&mv("inf_m"), &nat()).unwrap());
    assert!(ops::member(&s("x"), &string).unwrap());
    assert!(ops::member(&s("x"), &int_set).is_err());
    let seq = ops::seq_set(&ints(&[1, 2])).unwrap();
    assert!(ops::member(&tup(vec![]), &seq).unwrap());
    assert!(ops::member(&tup(vec![int(1), int(2), int(1)]), &seq).unwrap());
    assert!(!ops::member(&tup(vec![int(3)]), &seq).unwrap());
    assert!(ops::member(&scale(ops::interval(1, 2), 1), &seq).unwrap());
    assert!(ops::member(&s("ab"), &seq).is_err());
    assert!(ops::member(&ints(&[1]), &seq).is_err());
    assert!(!ops::member(&fcn(vec![(int(0), int(1))]), &seq).unwrap_or(false));
    for x in [nat(), int_set.clone(), string.clone(), seq.clone()] {
        assert!(ops::enumerate(&x).is_err());
        assert!(ops::cardinality(&x).is_err());
        assert!(!ops::is_finite_set(&x).unwrap());
        assert!(x.normalize().is_err());
        assert!(tlx_value::fingerprint::fingerprint(&x).is_err());
    }
    assert!(ops::is_finite_set(&ops::seq_set(&Value::empty_set()).unwrap()).unwrap());
    assert!(ops::subseteq(&ints(&[1, 2]), &nat()).unwrap());
    assert!(!ops::subseteq(&ints(&[-1, 2]), &nat()).unwrap());
    assert!(ops::subseteq(&nat(), &int_set).is_err());
    assert!(tlx_value::order::eq_tlc(&nat(), &nat()).unwrap());
    assert!(!tlx_value::order::eq_tlc(&nat(), &int_set).unwrap());
    assert!(tlx_value::order::eq_tlc(&nat(), &ints(&[1])).is_err());
    assert!(tlx_value::order::eq_tlc(&ints(&[1]), &nat()).is_err());
    // infinite builtins still have a total order / hash for maps
    assert!(ints(&[1]) < nat() && nat() < int_set);
    let mut h = std::collections::HashSet::new();
    h.insert(nat());
    assert!(h.contains(&nat()));
}

#[derive(Debug)]
struct Evens;

impl CustomSet for Evens {
    fn contains(&self, v: &Value) -> tlx_value::Result<bool> {
        Ok(v.as_int()? % 2 == 0)
    }
    fn enumerate(&self) -> tlx_value::Result<Option<Vec<Value>>> {
        Ok(None)
    }
}

#[derive(Debug)]
struct Small;

impl CustomSet for Small {
    fn contains(&self, v: &Value) -> tlx_value::Result<bool> {
        Ok(matches!(v, Value::Int(1 | 2)))
    }
    fn enumerate(&self) -> tlx_value::Result<Option<Vec<Value>>> {
        Ok(Some(vec![int(2), int(1), int(2)]))
    }
}

#[test]
fn custom_sets() {
    let evens = lazy(LazySet::Custom(Box::new(Evens)));
    assert!(ops::member(&int(4), &evens).unwrap());
    assert!(!ops::member(&int(3), &evens).unwrap());
    assert!(ops::enumerate(&evens).is_err());
    assert!(!ops::is_finite_set(&evens).unwrap());
    let small = lazy(LazySet::Custom(Box::new(Small)));
    assert_eq!(enum_str(&small), "2 1 2");
    assert_eq!(ops::cardinality(&small).unwrap(), 2);
    assert_eq!(small, ints(&[1, 2]));
    assert_eq!(small.to_string(), "{1, 2}");
    assert_eq!(ops::intersect(&small, &evens).unwrap().normalize().unwrap(), ints(&[2]));
}

#[test]
fn cardinality_and_finiteness() {
    assert_eq!(ops::cardinality(&ops::interval(1, 5)).unwrap(), 5);
    assert_eq!(ops::cardinality(&ops::interval(5, 1)).unwrap(), 0);
    assert!(ops::cardinality(&ops::interval(-2147483648, 2147483647)).is_err());
    assert!(ops::cardinality(&int(3)).is_err());
    assert!(ops::cardinality(&tup(vec![])).is_err());
    assert!(ops::is_finite_set(&ops::interval(1, 5)).unwrap());
    assert!(ops::is_finite_set(&int(1)).is_err());
    assert!(ops::is_finite_set(&ops::powerset(&ints(&[1])).unwrap()).unwrap());
    assert!(!ops::is_finite_set(&ops::powerset(&nat()).unwrap()).unwrap());
    assert!(ops::is_finite_set(&ops::product(vec![nat(), Value::empty_set()]).unwrap()).unwrap());
    assert!(!ops::is_finite_set(&ops::product(vec![nat(), ints(&[1])]).unwrap()).unwrap());
    let cap = ops::intersect(&nat(), &lazy(LazySet::Int)).unwrap();
    assert!(ops::is_finite_set(&cap).is_err());
}

#[test]
fn subseteq() {
    assert!(ops::subseteq(&ops::interval(2, 3), &ops::interval(1, 5)).unwrap());
    assert!(ops::subseteq(&ints(&[2, 3]), &ops::interval(1, 5)).unwrap());
    assert!(!ops::subseteq(&ints(&[2, 7]), &ops::interval(1, 5)).unwrap());
    assert!(ops::subseteq(&Value::empty_set(), &ints(&[])).unwrap());
    assert!(ops::subseteq(&int(1), &ints(&[1])).is_err());
    assert!(ops::subseteq(&ints(&[1]), &set(vec![s("a")])).is_err());
}

// ---- sequences ----

#[test]
fn sequences() {
    let t = tup(vec![int(1), int(2), int(3)]);
    assert_eq!(ops::len(&t).unwrap(), 3);
    assert_eq!(ops::len(&s("abcd")).unwrap(), 4);
    assert_eq!(ops::len(&scale(ops::interval(1, 2), 1)).unwrap(), 2);
    assert!(ops::len(&ints(&[1])).is_err());
    assert!(ops::len(&rec(&[("sq_a", int(1))])).is_err());
    assert_eq!(ops::append(&t, int(4)).unwrap().to_string(), "<<1, 2, 3, 4>>");
    assert!(ops::append(&Value::empty_set(), int(1)).is_err());
    assert!(ops::append(&s("ab"), s("c")).is_err());
    assert_eq!(ops::concat(&t, &tup(vec![int(9)])).unwrap().to_string(), "<<1, 2, 3, 9>>");
    assert_eq!(ops::concat(&tup(vec![]), &t).unwrap(), t);
    assert_eq!(ops::concat(&s("ab"), &s("cd")).unwrap(), s("abcd"));
    assert!(ops::concat(&s("ab"), &tup(vec![])).is_err());
    assert!(ops::concat(&tup(vec![]), &s("ab")).is_err());
    assert!(ops::concat(&ints(&[1]), &t).is_err());
    assert_eq!(ops::head(&t).unwrap(), int(1));
    assert_eq!(err_msg(ops::head(&tup(vec![]))), "Attempted to apply Head to the empty sequence.");
    assert!(ops::head(&s("abc")).is_err()); // Head does not support strings
    assert_eq!(ops::tail(&t).unwrap().to_string(), "<<2, 3>>");
    assert_eq!(ops::tail(&s("abc")).unwrap(), s("bc"));
    assert_eq!(err_msg(ops::tail(&tup(vec![]))), "Attempted to apply Tail to the empty sequence.");
    assert!(ops::tail(&s("")).is_err());
    assert_eq!(ops::subseq(&t, 2, 3).unwrap().to_string(), "<<2, 3>>");
    assert_eq!(ops::subseq(&t, 3, 2).unwrap(), tup(vec![]));
    assert_eq!(ops::subseq(&t, 10, 2).unwrap(), tup(vec![])); // m > n: no bounds check
    assert_eq!(ops::subseq(&tup(vec![]), 1, 0).unwrap(), tup(vec![]));
    assert!(ops::subseq(&t, 0, 2).is_err());
    assert!(ops::subseq(&t, 2, 4).is_err());
    assert_eq!(ops::subseq(&s("hello"), 2, 4).unwrap(), s("ell"));
    assert_eq!(ops::subseq(&s("hello"), 4, 2).unwrap(), s(""));
    assert!(ops::subseq(&ints(&[1]), 1, 1).is_err());
    let fs = fcn(vec![(int(1), int(5))]);
    assert_eq!(ops::head(&fs).unwrap(), int(5)); // [i \in {1} |-> 5] is a sequence
}

/// A tuple or record built as a function over an enumerated domain (TLC's
/// FcnRcdValue) equals, hashes, fingerprints and prints like the canonical
/// form, but EXCEPT / select look keys up by equality: a model value is not
/// in its domain.
#[test]
fn fcn_over_enumerated_domain() {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};
    let hash = |v: &Value| {
        let mut h = DefaultHasher::new();
        v.hash(&mut h);
        h.finish()
    };
    let m = Value::model_value("fe_m");
    let t = tup(vec![int(7), int(8)]);
    let f = Value::fcn_over(&ints(&[1, 2]), vec![(int(2), int(8)), (int(1), int(7))]).unwrap();
    assert!(matches!(f, Value::Fcn(..)));
    assert_eq!(tlx_value::FcnKind::of_value(&f), tlx_value::FcnKind::Tuple);
    assert_eq!(f, t);
    assert_eq!(hash(&f), hash(&t));
    assert_eq!(fingerprint(&f).unwrap(), fingerprint(&t).unwrap());
    assert!(eq_tlc(&f, &t).unwrap() && eq_tlc(&t, &f).unwrap());
    assert_eq!(f.to_string(), "<<7, 8>>");
    assert_eq!(ops::len(&f).unwrap(), 2);
    assert_eq!(ops::apply(&f, &int(2)).unwrap(), int(8));
    assert_eq!(ops::domain(&f).unwrap().to_string(), "{1, 2}");
    // Interval-backed non-1-based functions yield an Interval domain (matching
    // TLC's FcnRcdValue.getDomainAsSet), while enumerated domains yield a Set.
    let fi = Value::fcn_over(&ops::interval(0, 1), vec![(int(0), int(7)), (int(1), int(8))]).unwrap();
    let fe = Value::fcn_over(&ints(&[0, 1]), vec![(int(0), int(7)), (int(1), int(8))]).unwrap();
    assert!(matches!(ops::domain(&fi).unwrap(), Value::Interval(0, 1)));
    assert!(matches!(ops::domain(&fe).unwrap(), Value::Set(_)));
    // The interval domain gives the tuple (TLC: an interval FcnRcdValue).
    assert!(matches!(Value::fcn_over(&ops::interval(1, 2), vec![(int(1), int(7)), (int(2), int(8))]).unwrap(), Value::Tuple(_)));
    // EXCEPT with a model value: unchanged (FcnRcdValue) vs an error (tuple).
    assert_eq!(ops::select(&f, &m).unwrap(), None);
    assert!(ops::select(&t, &m).is_err());
    assert!(ops::select(&f, &s("a")).is_err());
    let f2 = ops::except(&f, &int(1), int(0)).unwrap();
    assert!(matches!(f2, Value::Fcn(..)));
    assert_eq!(f2, tup(vec![int(0), int(8)]));
    // Records.
    let r = rec(&[("fe_a", int(1)), ("fe_b", int(2))]);
    let g = Value::fcn_rcd_from_pairs(vec![(s("fe_b"), int(2)), (s("fe_a"), int(1))]).unwrap();
    assert!(matches!(g, Value::Fcn(..)));
    assert_eq!(g, r);
    assert_eq!(hash(&g), hash(&r));
    assert_eq!(fingerprint(&g).unwrap(), fingerprint(&r).unwrap());
    assert!(eq_tlc(&g, &r).unwrap() && eq_tlc(&r, &g).unwrap());
    assert_eq!(g.to_string(), "[fe_a |-> 1, fe_b |-> 2]");
    assert_eq!(ops::field(&g, Sym::new("fe_b")).unwrap(), int(2));
    assert_eq!(ops::select(&g, &m).unwrap(), None);
    assert!(ops::select(&r, &m).is_err());
    // In sets: one element.
    assert_eq!(ops::cardinality(&set(vec![f.clone(), t.clone()])).unwrap(), 1);
    assert_eq!(ops::cardinality(&set(vec![g.clone(), r.clone()])).unwrap(), 1);
    // @@ builds a function over an enumerated domain, also from tuples.
    let h = ops::fcn_merge(&t, &tup(vec![int(0), int(0), int(9)])).unwrap();
    assert!(matches!(h, Value::Fcn(..)));
    assert_eq!(h, tup(vec![int(7), int(8), int(9)]));
}

/// `apply_tuple_ref` gives `apply_ref`'s value whenever it answers, and
/// answers for tuples of integers, strings or booleans, linear and binary
/// search alike.
#[test]
fn apply_tuple_ref_agrees_with_apply_ref() {
    let grid = |n: i64| fcn((0..n).flat_map(|x| (0..n).map(move |y| (tup(vec![int(x), int(y)]), int(10 * x + y)))).collect());
    // (Keys TLC can sort: of different lengths, or with an untyped model
    // value, which compares with anything.)
    let mixed = fcn(vec![
        (tup(vec![int(1), int(2)]), int(1)),
        (tup(vec![int(2)]), int(2)),
        (tup(vec![int(1), int(2), int(3)]), int(3)),
        (tup(vec![mv("atr_m"), int(1)]), int(4)),
    ]);
    let strs = fcn(vec![(tup(vec![s("atr_a"), s("atr_b")]), int(1)), (tup(vec![s("atr_b"), s("atr_a")]), int(2))]);
    let bools = fcn(vec![(tup(vec![Value::Bool(false)]), int(1)), (tup(vec![Value::Bool(true)]), int(2))]);
    let fs = [grid(3), grid(7), mixed, strs, bools, tup(vec![int(1)]), rec(&[("atr_f", int(1))])];
    let keys = [
        vec![int(1), int(2)],
        vec![int(6), int(6)],
        vec![int(7), int(0)],
        vec![int(1)],
        vec![int(2)],
        vec![s("atr_b"), s("atr_a")],
        vec![s("atr_b"), int(1)],
        vec![Value::Bool(true)],
        vec![mv("atr_m"), int(1)],
        vec![int(1), int(2), int(3)],
        vec![],
    ];
    let mut answered = 0;
    for f in &fs {
        for k in &keys {
            let want = ops::apply_ref(f, &tup(k.clone()));
            if let Some(v) = ops::apply_tuple_ref(f, k) {
                answered += 1;
                assert!(matches!(&want, Ok(Some(w)) if *w == v), "{f}[{}]: {v} but apply_ref gives {want:?}", tup(k.clone()));
            }
        }
    }
    assert!(answered >= 6, "answered {answered}");
}

#[test]
fn search_threshold_preserves_first_comparison_and_direction() {
    for len in [31, 32, 33] {
        let pairs = (0..len).map(|i| (int(i), int(i))).collect();
        let f = Value::fcn_rcd_from_pairs(pairs).unwrap();
        for i in [0, len / 2, len - 1] {
            assert_eq!(ops::apply(&f, &int(i)).unwrap(), int(i));
        }
        assert_eq!(ops::select(&f, &int(len)).unwrap(), None);
        let error = err_msg(ops::apply(&f, &s("probe")));
        assert!(error.contains("integer"), "stored key must direct lookup: {error}");
        // Scan begins at key 0; bisection begins at key len/2.
        let first = if len < 32 { 0 } else { len / 2 };
        assert!(error.contains(&format!("integer {first}")), "{error}");
        let error = err_msg(ops::fcn_merge(&f, &ops::single_fcn(s("probe"), int(0)).unwrap()));
        assert!(error.contains("string"), "probe must direct merge: {error}");
        let error = err_msg(ops::member(&s("probe"), &Value::set_from((0..len).map(int).collect()).unwrap()));
        assert!(error.contains("string"), "probe must direct membership: {error}");
    }
}
