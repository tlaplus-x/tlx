//! Constant comparisons of a mixed atom universe stay native while preserving
//! errors for differently typed model values (including unreachable shapes),
//! and equality of encoded values stays native where TLC's comparison of the
//! two kinds is total (a union arm-wise, a record against a tuple).
use std::collections::BTreeSet;
use std::sync::Arc;

use tlx_layout::Shape;
use tlx_testkit::diff::{expr_kinds, DiffReport, Harness};
use tlx_testkit::module;
use tlx_value::{Sym, Value};

#[test]
fn mixed_atom_constant_equality_is_native_and_checks_types() {
    let src = module(
        "AtomEquality",
        r#"CONSTANTS A, B, C, U
VARIABLE x
Init == x = A
Next == UNCHANGED x
Same == x = A
Reverse == A = x
OtherType == x = C
Untyped == x = U
String == x = "text"
"#,
    );
    let cfg = "CONSTANTS A = T_a B = T_b C = S_c U = plain\nINIT Init\nNEXT Next\nINVARIANTS Same Reverse OtherType Untyped String\n";
    let mut values: Vec<_> = ["T_a", "T_b", "S_c", "plain"].into_iter().map(|s| Value::ModelValue(Sym::new(s))).collect();
    values.push(Value::str("text"));
    values.sort();
    let h = Harness::with_shapes(&src, cfg, vec![Shape::Atom(Arc::from(values.clone()))]);
    assert!(h.not_native().is_empty(), "constant atom equality needs host regions: {:?}", h.not_native());
    let mut report = DiffReport::default();
    for value in values {
        h.check_state(&[value], &mut report);
    }
    report.assert_ok("atom equality");
    let (ir, native) = report.totals();
    assert_eq!(native.unsupported, 0, "{}", report.render());
    assert!(ir.agree > 0 && native.agree > 0 && ir.both_fail > 0 && native.both_fail > 0, "{}", report.render());
}

/// The IR kinds of the invariant `name`: a boxed operation (`ValOp`,
/// `Interp`) would become a host region in the generated C.
fn kinds(h: &Harness, name: &str) -> BTreeSet<&'static str> {
    let mut kinds = BTreeSet::new();
    for p in &h.invariants {
        if &*p.name == name {
            expr_kinds(&p.body, &mut kinds);
        }
    }
    kinds
}

/// A boxed node is what a host region is made of: `Eq` over two encoded
/// operands is a word comparison in the generated C, a `ValOp` or `Interp`
/// node is a region.
fn assert_not_boxed(h: &Harness, names: &[&str]) {
    for name in names {
        let k = kinds(h, name);
        assert!(!k.contains("ValOp") && !k.contains("Interp"), "{name} is boxed: {k:?}\n{}", h.dump(name));
    }
}

/// A variable holding either `<<>>` or a record: one union of a record arm
/// and an empty-tuple arm. TLC compares two of its values arm-wise (an
/// equal arm index compares the payload, a different one is `false`).
#[test]
fn union_of_record_and_empty_tuple_equality_is_native() {
    let src = module(
        "UnionRecordTupleEquality",
        r#"VARIABLE x
Init == x = <<>>
Next == x' = [a |-> 1, b |-> 2]
AsEmpty == x = <<>>
AsRecord == x = [a |-> 1, b |-> 2]
Mirror == <<>> = x
"#,
    );
    let cfg = "INIT Init\nNEXT Next\nINVARIANTS AsEmpty AsRecord Mirror\n";
    let record = Shape::Record(Arc::from(vec![(Sym::new("a"), Shape::Int { lo: 1, hi: 1 }), (Sym::new("b"), Shape::Int { lo: 2, hi: 2 })]));
    let union = Shape::Union(Arc::from(vec![record, Shape::Tuple(Arc::from(Vec::new()))]));
    let h = Harness::with_shapes(&src, cfg, vec![union]);
    assert!(h.not_native().is_empty(), "{:?}", h.not_native());
    assert_not_boxed(&h, &["AsEmpty", "AsRecord", "Mirror"]);
    for name in ["AsEmpty", "AsRecord", "Mirror"] {
        assert!(kinds(&h, name).contains("Eq"), "{name} lost its encoded equality: {}", h.dump(name));
    }
    let record = record_value(&[("a", 1), ("b", 2)]);
    let mut report = DiffReport::default();
    for value in [Value::tuple(Vec::new()), record] {
        h.check_state(&[value], &mut report);
    }
    report.assert_ok("union equality");
    let (ir, native) = report.totals();
    assert_eq!(native.unsupported, 0, "{}", report.render());
    assert!(ir.agree > 0 && native.agree > 0, "{}", report.render());
}

/// A tuple compared with a union of records: no arm holds a tuple, so the
/// comparison is `false` for every pair and the encodings need no join.
#[test]
fn tuple_against_a_union_of_records_is_native() {
    let src = module(
        "TupleUnionEquality",
        r#"VARIABLES t, h
Init == t = <<1, 2>> /\ h = [a |-> 1]
Next == \/ t' = t /\ h' = [b |-> 2]
        \/ UNCHANGED <<t, h>>
TupleFirst == t = h
UnionFirst == h = t
"#,
    );
    let cfg = "INIT Init\nNEXT Next\nINVARIANTS TupleFirst UnionFirst\n";
    let tuple = Shape::Tuple(Arc::from(vec![Shape::Int { lo: 1, hi: 2 }, Shape::Int { lo: 1, hi: 2 }]));
    let union = Shape::Union(Arc::from(vec![
        Shape::Record(Arc::from(vec![(Sym::new("a"), Shape::Int { lo: 1, hi: 1 })])),
        Shape::Record(Arc::from(vec![(Sym::new("b"), Shape::Int { lo: 2, hi: 2 })])),
    ]));
    let h = Harness::with_shapes(&src, cfg, vec![tuple, union]);
    assert!(h.not_native().is_empty(), "{:?}", h.not_native());
    assert_not_boxed(&h, &["TupleFirst", "UnionFirst"]);
    let mut report = h.run_reachable(6);
    h.run_random(&mut tlx_testkit::Rng::new(4411), 60, &mut report);
    report.assert_ok("tuple against a union");
    let (_, native) = report.totals();
    assert_eq!(native.unsupported, 0, "{}", report.render());
    assert!(native.agree > 0, "{}", report.render());
}

/// Two kinds with no common value still evaluate *both* operands: TLC
/// reports an error inside either of them, so a comparison that answers
/// without looking at the values must keep it (`f[3]` is outside its
/// domain, `g[f[3]]` fails before the comparison does).
#[test]
fn disjoint_kinds_evaluate_both_operands() {
    let src = module(
        "DisjointKindEquality",
        r#"EXTENDS Naturals
VARIABLES f, g, h
Init == f = <<1, 2>> /\ g = <<[a |-> 1], [a |-> 1]>> /\ h = <<1, 2>>
Next == UNCHANGED <<f, g, h>>
Found == g[1] = h
Missing == g[f[3]] = h
"#,
    );
    let cfg = "INIT Init\nNEXT Next\nINVARIANTS Found Missing\n";
    let ints = Shape::Tuple(Arc::from(vec![Shape::Int { lo: 1, hi: 2 }, Shape::Int { lo: 1, hi: 2 }]));
    let record = Shape::Record(Arc::from(vec![(Sym::new("a"), Shape::Int { lo: 1, hi: 1 })]));
    let g = Shape::Tuple(Arc::from(vec![record.clone(), record]));
    let harness = Harness::with_shapes(&src, cfg, vec![ints.clone(), g, ints.clone()]);
    let ints_value = || Value::tuple(vec![Value::Int(1), Value::Int(2)]);
    let mut report = DiffReport::default();
    harness
        .check_state(&[ints_value(), Value::tuple(vec![record_value(&[("a", 1)]), record_value(&[("a", 1)])]), ints_value()], &mut report);
    report.assert_ok("disjoint kinds");
    let (ir, native) = report.totals();
    // `g[f[3]]` is outside the domain: both tiers report the error.
    assert!(ir.both_fail > 0 && native.both_fail > 0, "{}", report.render());
    assert!(ir.agree > 0 && native.agree > 0, "{}", report.render());
    assert_not_boxed(&harness, &["Found", "Missing"]);
}

/// A record of integer fields (TLC order of the names).
fn record_value(fields: &[(&str, i64)]) -> Value {
    Value::record(fields.iter().map(|(n, v)| (Sym::new(n), Value::Int(*v))).collect())
}

/// A tuple tested for membership in a *sorted* set of records (its element
/// shape has no bitset universe, so the elements are a sorted array). The
/// comparison can never fail and is never true, but the element cannot be
/// re-encoded into the record's encoding either: the tiers have to agree
/// with the interpreter all the same (the guard that keeps membership
/// boxed is `shapes_comparable`, which does not cover this pair).
#[test]
fn tuple_in_a_sorted_record_set_agrees_with_the_interpreter() {
    let src = module(
        "SortedRecordSetMembership",
        r#"EXTENDS Naturals
VARIABLES x, s
Init == x = <<1, 2>> /\ s = {[a |-> i] : i \in 1..5000}
Next == UNCHANGED <<x, s>>
Member == x \in s
Absent == <<3, 4>> \in s
"#,
    );
    let cfg = "INIT Init\nNEXT Next\nINVARIANTS Member Absent\n";
    let tuple = Shape::Tuple(Arc::from(vec![Shape::Int { lo: 1, hi: 4 }, Shape::Int { lo: 1, hi: 4 }]));
    let record = Shape::Record(Arc::from(vec![(Sym::new("a"), Shape::Int { lo: 1, hi: 5000 })]));
    let set = Shape::Set { elem: Box::new(record), max_card: 3 };
    let h = Harness::with_shapes(&src, cfg, vec![tuple, set]);
    let mut report = DiffReport::default();
    h.check_state(
        &[
            Value::tuple(vec![Value::Int(1), Value::Int(2)]),
            Value::set_from(vec![record_value(&[("a", 1)]), record_value(&[("a", 2)])]).expect("set"),
        ],
        &mut report,
    );
    report.assert_ok("tuple in a sorted record set");
    let (ir, native) = report.totals();
    assert_eq!(ir.wrong + native.wrong + ir.unsupported, 0, "{}", report.render());
    assert!(ir.agree > 0, "{}", report.render());
}

/// Force a Dyn state slot so layout inference cannot specialize the fixture away.
/// The harness runs each predicate against the interpreter, closure executor
/// and a native library loaded without a host-region table.
#[test]
fn dynamic_scalar_predicates_execute_without_host_regions() {
    let mut body = String::from(
        r#"EXTENDS Integers
VARIABLES x, i, b, s
Init == x = 0 /\ i = 0 /\ b = TRUE /\ s = {}
Next == UNCHANGED <<x, i, b, s>>
"#,
    );
    let mut cfg = String::from("INIT Init\nNEXT Next\nINVARIANTS");
    let predicates = [
        "x = i",
        "i = x",
        "x # i",
        "i # x",
        "x < i",
        "i < x",
        "x <= i",
        "i <= x",
        "x > i",
        "i > x",
        "x >= i",
        "i >= x",
        r"x \in i..(i+2)",
        r"x \in 1..5",
        r"x \in Nat",
        r"x \in Int",
        r"x \in s",
        r"x \notin s",
        "x = b",
        "b = x",
        "x # b",
        "b # x",
    ];
    for (index, expr) in predicates.iter().enumerate() {
        body.push_str(&format!("P{index} == {expr}\n"));
        cfg.push_str(&format!(" P{index}"));
    }
    let int = Shape::Int { lo: -8, hi: 8 };
    let shapes = vec![Shape::Dyn, int.clone(), Shape::Bool, Shape::Set { elem: Box::new(int), max_card: 3 }];
    let h = Harness::with_shapes(&module("DynamicScalar", &body), &cfg, shapes);
    assert!(h.native.invariants.iter().all(|&native| native), "{:?}", h.not_native());
    assert_eq!(h.lib.as_ref().unwrap().n_regions(), 0);
    for x in [
        Value::Int(-7),
        Value::Int(0),
        Value::Int(3),
        Value::Bool(false),
        Value::Bool(true),
        Value::str("abc"),
        Value::ModelValue(Sym::new("a_1")),
        Value::ModelValue(Sym::new("m")),
    ] {
        let mut report = DiffReport::default();
        h.check_state(
            &[x.clone(), Value::Int(-7), Value::Bool(true), Value::set_from(vec![Value::Int(-7), Value::Int(3)]).unwrap()],
            &mut report,
        );
        report.assert_ok("dynamic scalar");
        for (index, expr) in predicates.iter().enumerate() {
            let comparable = if expr.contains('b') { matches!(x, Value::Bool(_)) } else { matches!(x, Value::Int(_)) };
            if comparable {
                let (ir, native) = report.tallies[&format!("invariant P{index}")];
                assert_eq!((ir.agree, native.agree), (1, 1), "{x:?} {expr}\n{}", report.render());
            }
        }
    }
}
