//! Unit tests for the closure analysis.

use std::sync::Arc;

use tlx_layout::FcnWitness;
use tlx_testkit::spec;
use tlx_value::{Sym, Value};

use super::expr::{shape_of_value, value_within_domain_bound};
use super::*;

fn model(src: &str) -> InterpModel {
    let src = tlx_testkit::module("Closed", src);
    spec::load(&src, "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n")
}

fn int(lo: i64, hi: i64) -> Shape {
    Shape::Int { lo, hi }
}

fn closed(m: &InterpModel, vars: Vec<Shape>) -> Result<(), String> {
    layout_is_closed(m, &vars, &[])
}

#[test]
fn boolean_and_bounded_integer_slots_are_closed() {
    let m = model("EXTENDS Naturals\nVARIABLES b, n\nInit == b = FALSE /\\ n = 0\nNext == b' = ~b /\\ n' = IF n < 3 THEN n + 1 ELSE 0");
    assert_eq!(closed(&m, vec![Shape::Bool, int(0, 5)]), Ok(()));
}

#[test]
fn a_too_narrow_integer_slot_keeps_the_archive() {
    let m = model("EXTENDS Naturals\nVARIABLES b, n\nInit == b = FALSE /\\ n = 0\nNext == b' = ~b /\\ n' = IF n < 3 THEN n + 1 ELSE 0");
    assert!(closed(&m, vec![Shape::Bool, int(0, 2)]).is_err());
}

#[test]
fn dyn_slots_accept_anything() {
    let m = model("EXTENDS TLC\nVARIABLE x\nInit == x = \"a\"\nNext == x' = ToString(TLCGet(\"level\"))");
    assert_eq!(closed(&m, vec![Shape::Dyn]), Ok(()));
}

#[test]
fn set_membership_assignments_use_the_element_shape() {
    let m = model("EXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' \\in 1..3");
    assert_eq!(closed(&m, vec![int(0, 5)]), Ok(()));
    assert!(closed(&m, vec![int(2, 5)]).is_err());
}

#[test]
fn subset_assignments_become_set_shapes() {
    let m = model("EXTENDS Naturals\nVARIABLE x\nInit == x = {}\nNext == x' \\subseteq 1..3");
    assert_eq!(closed(&m, vec![Shape::Set { elem: Box::new(int(1, 3)), max_card: 3 }]), Ok(()));
    assert!(closed(&m, vec![Shape::Set { elem: Box::new(int(1, 3)), max_card: 2 }]).is_err());
}

#[test]
fn an_interval_value_only_fits_a_dyn_slot() {
    let src = "EXTENDS Naturals\nVARIABLE x\nInit == x = {}\nNext == x' = 1..3";
    let m = model(src);
    // A `Value::Interval` is not encoded as a fixed `Set` layout.
    assert_eq!(closed(&m, vec![Shape::Dyn]), Ok(()));
    assert!(closed(&m, vec![Shape::Set { elem: Box::new(int(1, 3)), max_card: 3 }]).is_err());
}

#[test]
fn function_witness_flips_keep_the_archive() {
    let src = "EXTENDS Naturals\nVARIABLE f\n\
        Init == f = [i \\in {1, 2} |-> 0]\n\
        Next == f' = IF f[1] = 0 THEN <<1, 2>> ELSE [i \\in 1..2 |-> 0]";
    let m = model(src);
    let en = Shape::Fcn {
        dom: Arc::from([Value::Int(1), Value::Int(2)]),
        range: Box::new(int(0, 2)),
        witness: FcnWitness::Enumerated,
        key_variants: Arc::from([]),
    };
    assert!(closed(&m, vec![en]).is_err());
    // A Dyn slot accepts the tuple and the interval-domain function.
    assert_eq!(closed(&m, vec![Shape::Dyn]), Ok(()));
}

#[test]
fn a_constant_set_domain_function_fits_its_fixed_domain_slot() {
    let src = "EXTENDS Naturals\nVARIABLE f\n\
        Init == f = [i \\in {1, 2} |-> 0]\n\
        Next == f' = [i \\in {1, 2} |-> i]";
    let m = model(src);
    let en = Shape::Fcn {
        dom: Arc::from([Value::Int(1), Value::Int(2)]),
        range: Box::new(int(0, 2)),
        witness: FcnWitness::Enumerated,
        key_variants: Arc::from([]),
    };
    assert_eq!(closed(&m, vec![en]), Ok(()));
}

#[test]
fn guarded_updates_are_narrowed_before_the_assignment() {
    let src = "EXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 4 /\\ x' = x + 1";
    let m = model(src);
    // x in 0..4 is narrowed to 0..3 by the guard, so x + 1 stays in 0..4.
    assert_eq!(closed(&m, vec![int(0, 4)]), Ok(()));
}

#[test]
fn materialized_definitions_must_fit_their_shape() {
    let src = "EXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x' = IF x < 2 THEN x + 1 ELSE 0\nD == x + 1";
    let m = model(src);
    let d = m.ip.prog.defs.iter().position(|def| &*def.name == "D").expect("D") as u32;
    let d = DefId(d);
    // `x` carries the speculation's headroom (0..4), so `x + 1` reaches 5.
    assert_eq!(layout_is_closed(&m, &[int(0, 4)], &[(d, int(0, 5))]), Ok(()));
    assert!(layout_is_closed(&m, &[int(0, 4)], &[(d, int(0, 4))]).is_err());
}

#[test]
fn an_unprovable_assignment_value_keeps_the_archive() {
    let src = "EXTENDS TLC\nVARIABLE x\nInit == x = \"a\"\nNext == x' = ToString(TLCGet(\"level\"))";
    let m = model(src);
    assert!(closed(&m, vec![Shape::Atom(Arc::from([Value::Str(Sym::new("a"))]))]).is_err());
    assert_eq!(closed(&m, vec![Shape::Dyn]), Ok(()));
}

#[test]
fn unknown_quantifier_domain_still_checks_body_assignments() {
    // `S` is Dyn (or an IF joining interval and set -> Dyn): the body
    // assigns 42 to a slot holding 0, so the proof must fail.
    let src = "EXTENDS Naturals\nVARIABLES S, x\nInit == S = 1..1 /\\ x = 0\nNext == \\E i \\in S : x' = 42 /\\ UNCHANGED S";
    let m = model(src);
    assert!(closed(&m, vec![Shape::Dyn, int(0, 0)]).is_err());
    assert_eq!(closed(&m, vec![Shape::Dyn, int(0, 42)]), Ok(()));

    let src2 = "EXTENDS Naturals\nVARIABLES a, x\nInit == a = FALSE /\\ x = 0\n\
        Next == a' = TRUE /\\ \\E i \\in (IF a THEN 0..1 ELSE {0}) : x' = 100";
    let m2 = model(src2);
    assert!(closed(&m2, vec![Shape::Bool, int(0, 0)]).is_err());
}

#[test]
fn guard_refinements_do_not_escape_their_branch() {
    // Outer guard `x >= 0` creates a refinement; the IF's true arm narrows
    // to `x < 2`, which must not overwrite the outer refinement for the
    // false arm or subsequent conjuncts.
    let src = "EXTENDS Naturals\nVARIABLES x, y\nInit == x \\in 0..9 /\\ y = 0\n\
        Next == x >= 0 /\\ x' = x /\\ y' = IF x < 2 THEN 0 ELSE x";
    let m = model(src);
    assert!(closed(&m, vec![int(0, 9), int(0, 0)]).is_err());
    assert_eq!(closed(&m, vec![int(0, 9), int(0, 9)]), Ok(()));

    // Guard refinement inside one conjunct's IF must not leak `Never` to a
    // later conjunct assigning `n` to a string slot.
    let src2 = "EXTENDS Naturals\nVARIABLES n, y\nInit == n \\in 0..2 /\\ y = \"ok\"\n\
        Next == n >= 0 /\\ n' = IF n < 1 THEN n ELSE n /\\ y' = n";
    let m2 = model(src2);
    let ok = Shape::Atom(Arc::from([Value::Str(Sym::new("ok"))]));
    assert!(closed(&m2, vec![int(0, 2), ok]).is_err());
}

#[test]
fn interval_membership_narrows_union_to_integer_elements() {
    // `x` has a Union(Int, Atom) slot; `x \in 0..1` must narrow `x` to
    // `Int(0..1)`, not `Never` (which would falsely certify `y`'s string slot).
    let src = "EXTENDS Integers\nVARIABLES x, y\n\
        Init == (x = \"hi\" \\/ x = 0) /\\ y = \"ok\"\n\
        Next == x' = x /\\ y' = IF x \\in 0..1 THEN x ELSE \"ok\"";
    let m = model(src);
    let u = Shape::Union(Arc::from([int(0, 0), Shape::Atom(Arc::from([Value::Str(Sym::new("hi"))]))]));
    let ok = Shape::Atom(Arc::from([Value::Str(Sym::new("ok"))]));
    assert!(closed(&m, vec![u, ok]).is_err());
}

#[test]
fn grouped_binders_multiply_set_comprehension_cardinality() {
    // `{<<i, j>> : i, j \in {0, 1, 2}}` has 9 elements, not 3.
    let src = "EXTENDS Naturals, FiniteSets\nVARIABLE x\n\
        Init == x = 0\nNext == x' = Cardinality({<<i, j>> : i, j \\in {0, 1, 2}})";
    let m = model(src);
    assert!(closed(&m, vec![int(0, 3)]).is_err());
    assert!(closed(&m, vec![int(0, 8)]).is_err());
    assert_eq!(closed(&m, vec![int(0, 9)]), Ok(()));
}

#[test]
fn function_set_uses_range_element_shape_and_cardinality() {
    // `x' \in [{1} -> {0}]` assigns functions mapping 1 to the integer 0,
    // not to the set `{0}`.
    let src = "EXTENDS Naturals\nVARIABLE x\n\
        Init == x = [i \\in {1} |-> {0}]\nNext == x' \\in [{1} -> {0}]";
    let m = model(src);
    let set_range = Shape::Fcn {
        dom: Arc::from([Value::Int(1)]),
        range: Box::new(Shape::Set { elem: Box::new(int(0, 0)), max_card: 1 }),
        witness: FcnWitness::Enumerated,
        key_variants: Arc::from([]),
    };
    assert!(closed(&m, vec![set_range]).is_err());

    let src2 = "EXTENDS Naturals\nVARIABLE x\n\
        Init == x = [i \\in {1} |-> 0]\nNext == x' \\in [{1} -> {0, 1}]";
    let m2 = model(src2);
    let int_range = Shape::Fcn {
        dom: Arc::from([Value::Int(1)]),
        range: Box::new(int(0, 1)),
        witness: FcnWitness::Enumerated,
        key_variants: Arc::from([]),
    };
    assert_eq!(closed(&m2, vec![int_range]), Ok(()));
}

#[test]
fn single_component_tuple_binder_destructures_tuple_elements() {
    // `[<<i>> \in {<<1>>} |-> i]` binds `i` to 1, not `<<1>>`.
    let src = "EXTENDS Naturals\nVARIABLE x\n\
        Init == x = [t \\in {<<1>>} |-> t]\nNext == x' = [<<i>> \\in {<<1>>} |-> i]";
    let m = model(src);
    let tuple_range = Shape::Fcn {
        dom: Arc::from([Value::Tuple(Arc::from([Value::Int(1)]))]),
        range: Box::new(Shape::Tuple(Arc::from([int(1, 1)]))),
        witness: FcnWitness::Enumerated,
        key_variants: Arc::from([]),
    };
    assert!(closed(&m, vec![tuple_range]).is_err());

    // Also check application of a 1-tuple binder function.
    let src2 = "EXTENDS Naturals\nVARIABLE x\n\
        F[<<i>> \\in {<<1>>}] == i\nInit == x = <<1>>\nNext == x' = F[<<1>>]";
    let m2 = model(src2);
    assert!(closed(&m2, vec![Shape::Tuple(Arc::from([int(1, 1)]))]).is_err());
}

#[test]
fn tlc_assert_returns_boolean_not_diagnostic_argument() {
    let src = "EXTENDS TLC\nVARIABLE x\nInit == x = \"ok\"\nNext == x' = Assert(TRUE, \"ok\")";
    let m = model(src);
    let ok = Shape::Atom(Arc::from([Value::Str(Sym::new("ok"))]));
    assert!(closed(&m, vec![ok]).is_err());

    let src2 = "EXTENDS TLC\nVARIABLE x\nInit == x = TRUE\nNext == x' = Assert(TRUE, \"ok\")";
    let m2 = model(src2);
    assert_eq!(closed(&m2, vec![Shape::Bool]), Ok(()));
}

#[test]
fn all_unbounded_slots_take_fast_path_without_action_proof() {
    // Even with unanalyzable / recursive actions, all-Ref / all-Dyn slots
    // can never raise a layout miss.
    let src = "EXTENDS Naturals\nVARIABLE x\n\
        RECURSIVE Loop(_)\nLoop(n) == IF n = 0 THEN x' = 0 ELSE Loop(n - 1)\n\
        Init == x = 0\nNext == Loop(1)";
    let m = model(src);
    let store = tlx_layout::store::StoreRef::new(usize::MAX);
    assert_eq!(closed(&m, vec![Shape::Ref(store.clone())]), Ok(()));
    assert_eq!(closed(&m, vec![Shape::Dyn]), Ok(()));
    assert!(closed(&m, vec![int(0, 0)]).is_err());
}

#[test]
fn compose_does_not_leak_pre_state_refinements_into_second_action() {
    // `x < 2` holds on `s0`, not on the intermediate state produced by
    // `x' = 5`, so `y' = x` in the second operand can read 5.
    let src = "EXTENDS Naturals\nVARIABLES x, y\n\
        Init == x = 0 /\\ y = 0\n\
        Next == x < 2 /\\ ((x' = 5 /\\ y' = y) \\cdot (x' = x /\\ y' = x))";
    let m = model(src);
    assert!(closed(&m, vec![int(0, 5), int(0, 1)]).is_err());
    assert_eq!(closed(&m, vec![int(0, 5), int(0, 5)]), Ok(()));
}

#[test]
fn dyn_membership_guard_does_not_assume_compound_representation() {
    // `1..2 \in {{1, 2}}` is true under TLA+ equality even though `1..2`
    // is an interval value that misses a fixed `Set` slot.
    let src = "EXTENDS Naturals\nVARIABLES s, y\n\
        Init == s = 1..2 /\\ y = {1, 2}\n\
        Next == s' = s /\\ y' = IF s \\in {{1, 2}} THEN s ELSE {1, 2}";
    let m = model(src);
    let set_slot = Shape::Set { elem: Box::new(int(1, 2)), max_card: 2 };
    assert!(closed(&m, vec![Shape::Dyn, set_slot]).is_err());
}

#[test]
fn overridden_comparison_guard_does_not_narrow_branch() {
    // `CONSTANT < <- AlwaysLT` makes `x < 1` true even when `x = 12`, so
    // `refine_guard` must not narrow `x < 1` to `Never`.
    let src = tlx_testkit::module(
        "Closed",
        "EXTENDS Naturals\nVARIABLES x, y\n\
         AlwaysLT(u, v) == TRUE\n\
         Init == x = 12 /\\ y = 0\n\
         Next == x' = x /\\ y' = IF x < 1 THEN x ELSE 0",
    );
    let m = spec::load(&src, "INIT Init\nNEXT Next\nCONSTANT < <- AlwaysLT\nCHECK_DEADLOCK FALSE\n");
    assert!(closed(&m, vec![int(12, 12), int(0, 0)]).is_err());
}

#[test]
fn constant_substitution_honors_configured_def_value() {
    // `K <- F` and `F = 100` overrides the source body `F == "ok"`, so `K`
    // evaluates to 100 and must not be certified for a string slot.
    let src = tlx_testkit::module(
        "Closed",
        "EXTENDS Integers\nCONSTANT K\nVARIABLE x\n\
         F == \"ok\"\n\
         Init == x = \"ok\"\n\
         Next == x' = K",
    );
    let m = spec::load(&src, "INIT Init\nNEXT Next\nCONSTANT K <- F\nCONSTANT F = 100\nCHECK_DEADLOCK FALSE\n");
    let ok = Shape::Atom(Arc::from([Value::Str(Sym::new("ok"))]));
    assert!(closed(&m, vec![ok.clone()]).is_err());
    assert_eq!(closed(&m, vec![Shape::Union(Arc::from([int(100, 100), ok]))]), Ok(()));
}

#[test]
fn huge_lazy_domain_does_not_materialize_or_exhaust_budget() {
    // `SUBSET (1..19)` (524,288 subsets), `[1..250000 -> {0}]` (singleton
    // outer set with a 250,000-entry function element), and
    // `[pool: {SUBSET (1..19)}]` (singleton outer set with a nested lazy
    // powerset) must all be rejected before normalization.
    for def in ["Huge == SUBSET (1..19)", "Huge == [1..250000 -> {0}]", "Huge == [pool: {SUBSET (1..19)}]"] {
        let src = format!(
            "EXTENDS Naturals\n{def}\nVARIABLES b, x\n\
             Init == b = FALSE /\\ x = 0\n\
             Next == b' = b /\\ x' = IF b THEN [i \\in Huge |-> b] ELSE x"
        );
        let m = model(&src);
        let err = closed(&m, vec![Shape::Bool, int(0, 0)]).unwrap_err();
        assert!(!err.contains("budget is exhausted"), "{def}: unexpected budget exhaustion: {err}");
    }
    // Direct admission check: a singleton lazy function set over a huge
    // domain is rejected before normalization in both admission and shape
    // inspection.
    let wide = Value::LazySet(Arc::new(tlx_value::LazySet::FcnSet(Value::Interval(1, 250_000), Value::Set(Arc::from([Value::Int(0)])))));
    assert!(!value_within_domain_bound(&wide));
    assert!(matches!(shape_of_value(&wide), VShape::Shape(Shape::Dyn)));
    let nested = Value::LazySet(Arc::new(tlx_value::LazySet::RecordSet(vec![(
        Sym::new("pool"),
        Value::Set(Arc::from([Value::LazySet(Arc::new(tlx_value::LazySet::Subset(Value::Interval(1, 19))))])),
    )])));
    assert!(!value_within_domain_bound(&nested));
    assert!(matches!(shape_of_value(&nested), VShape::Shape(Shape::Dyn)));
}
