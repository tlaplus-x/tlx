//! `[f EXCEPT ![k1]... = v]` on a union whose function-like arm holds the
//! function (a per-transaction snapshot that is a function, or a
//! placeholder value before the transaction starts): the arm's tag selects
//! the update, the arms that are not function-like are the interpreter's
//! non-function error, and the replacement is evaluated exactly where the
//! interpreter evaluates it.
//!
//! Every case runs in the closure IR, in generated C and (with
//! `--features tlx-testkit/jit`) in the JIT, against the interpreter.

use std::sync::Arc;

use tlx_layout::Shape;
use tlx_testkit::diff::Harness;
use tlx_testkit::module;
use tlx_value::Value;

/// The model values `names`, in TLC order.
fn atoms(names: &[&str]) -> Arc<[Value]> {
    let mut v: Vec<Value> = names.iter().map(|n| Value::model_value(n)).collect();
    v.sort();
    Arc::from(v)
}

fn int(lo: i64, hi: i64) -> Shape {
    Shape::Int { lo, hi }
}

const KEYS: &[&str] = &["k1", "k2"];
const PLACEHOLDERS: &[&str] = &["Empty", "v1", "v2"];

/// A snapshot that is a function over `{k1, k2}` or the `Empty`
/// placeholder: the union of the two arms.
fn snapshot_shape() -> Shape {
    Shape::Union(
        vec![
            Shape::Atom(atoms(&["Empty"])),
            Shape::Fcn {
                dom: atoms(KEYS),
                range: Box::new(Shape::Atom(atoms(PLACEHOLDERS))),
                witness: tlx_layout::FcnWitness::Enumerated,
                key_variants: std::sync::Arc::from([]),
            },
        ]
        .into(),
    )
}

const CFG: &str = "CONSTANTS k1 = k1 k2 = k2 v1 = v1 Empty = Empty\nINIT Init\nNEXT Next\n";

const SPEC: &str = r#"EXTENDS Naturals
CONSTANTS k1, k2, v1, Empty
VARIABLES snap, n
Init == snap = Empty /\ n = 0
Start == snap = Empty /\ snap' = [k \in {k1, k2} |-> Empty] /\ n' = n + 1
Put == snap' = [snap EXCEPT ![k1] = v1] /\ n' = n + 1
Keep == snap' = [snap EXCEPT ![k2] = @] /\ n' = n + 1
Next == Start \/ Put \/ Keep
"#;

fn harness(name: &str) -> Harness {
    Harness::with_shapes(&module(name, SPEC), CFG, vec![snapshot_shape(), int(0, 3)])
}

#[test]
fn except_on_a_union_arm_is_native() {
    let h = harness("ExceptUnionNative");
    assert!(h.not_native().is_empty(), "{:?}", h.not_native());
    for a in ["Put", "Keep"] {
        let d = h.dump(a);
        assert!(!d.contains("interp "), "{a} fell back to the interpreter:\n{d}");
        assert!(d.contains("except"), "{a} has no EXCEPT:\n{d}");
    }
}

#[test]
fn except_on_a_union_arm_agrees_with_the_interpreter() {
    let h = harness("ExceptUnionDiff");
    let mut report = h.run_reachable(30);
    h.run_random(&mut tlx_testkit::Rng::new(917), 200, &mut report);
    report.assert_ok("EXCEPT on a union arm");
    let (ir, native) = report.totals();
    // `snap = Empty` is not a function, so the interpreter rejects the
    // update there and every tier must reject it too (a compiled success
    // would be a wrong result).
    assert!(ir.both_fail > 0 && native.both_fail > 0, "the non-function arm was never exercised:\n{}", report.render());
    assert!(ir.agree > 0 && native.agree > 0, "{}", report.render());
    assert_eq!((ir.wrong, native.wrong), (0, 0), "{}", report.render());
}

#[test]
fn nested_except_on_a_union_arm_is_native() {
    let nested = r#"EXTENDS Naturals
CONSTANTS k1, k2, v1, v2, Empty
VARIABLES snap, n
Init == snap = Empty /\ n = 0
Start == snap = Empty /\ snap' = [k \in {k1, k2} |-> [j \in {k1, k2} |-> Empty]] /\ n' = n + 1
Put == snap' = [snap EXCEPT ![k1][k2] = v1] /\ n' = n + 1
Keep == snap' = [snap EXCEPT ![k2][k1] = @] /\ n' = n + 1
Next == Start \/ Put \/ Keep
"#;
    let cfg = "CONSTANTS k1 = k1 k2 = k2 v1 = v1 v2 = v2 Empty = Empty\nINIT Init\nNEXT Next\n";
    let inner = Shape::Fcn {
        dom: atoms(KEYS),
        range: Box::new(Shape::Fcn {
            dom: atoms(KEYS),
            range: Box::new(Shape::Atom(atoms(PLACEHOLDERS))),
            witness: tlx_layout::FcnWitness::Enumerated,
            key_variants: std::sync::Arc::from([]),
        }),
        witness: tlx_layout::FcnWitness::Enumerated,
        key_variants: std::sync::Arc::from([]),
    };
    let snap = Shape::Union(vec![Shape::Atom(atoms(&["Empty"])), inner].into());
    let h = Harness::with_shapes(&module("ExceptUnionNested", nested), cfg, vec![snap, int(0, 3)]);
    assert!(h.not_native().is_empty(), "{:?}", h.not_native());
    for a in ["Put", "Keep"] {
        assert!(!h.dump(a).contains("interp "), "{a}:\n{}", h.dump(a));
    }
    let mut report = h.run_reachable(30);
    h.run_random(&mut tlx_testkit::Rng::new(918), 200, &mut report);
    report.assert_ok("nested EXCEPT on a union arm");
}

/// A union of a record and a placeholder: `!.field` selects the record
/// arm's slot, and the tag puts the updated arm back.
#[test]
fn field_except_on_a_union_arm_is_native() {
    let spec = r#"EXTENDS Naturals
CONSTANTS f1, f2, v1, Empty
VARIABLES box, n
Init == box = Empty /\ n = 0
Fill == box = Empty /\ box' = [f1 |-> Empty, f2 |-> Empty] /\ n' = n + 1
Set == box' = [box EXCEPT !.f1 = v1] /\ n' = n + 1
Same == box' = [box EXCEPT !.f2 = @] /\ n' = n + 1
Next == Fill \/ Set \/ Same
"#;
    let cfg = "CONSTANTS f1 = f1 f2 = f2 v1 = v1 Empty = Empty\nINIT Init\nNEXT Next\n";
    let atom = Shape::Atom(atoms(PLACEHOLDERS));
    let record = Shape::Record(vec![(tlx_value::Sym::new("f1"), atom.clone()), (tlx_value::Sym::new("f2"), atom)].into());
    let box_ = Shape::Union(vec![Shape::Atom(atoms(&["Empty"])), record].into());
    let h = Harness::with_shapes(&module("ExceptUnionRecord", spec), cfg, vec![box_, int(0, 3)]);
    assert!(h.not_native().is_empty(), "{:?}", h.not_native());
    for a in ["Set", "Same"] {
        assert!(!h.dump(a).contains("interp "), "{a}:\n{}", h.dump(a));
    }
    let mut report = h.run_reachable(30);
    h.run_random(&mut tlx_testkit::Rng::new(920), 200, &mut report);
    report.assert_ok("field EXCEPT on a union arm");
    let (ir, native) = report.totals();
    assert!(ir.both_fail > 0 && native.both_fail > 0, "the placeholder arm was never exercised:\n{}", report.render());
}

/// The replacement is evaluated exactly where the interpreter evaluates it:
/// the update is not taken when the value is not a function or the key is
/// outside the arm's domain, and an erroring replacement must not turn
/// those successes into failures.
#[test]
fn the_replacement_is_evaluated_only_where_the_update_is_taken() {
    let spec = r#"EXTENDS Naturals
CONSTANTS k1, k2, elsewhere, Empty
VARIABLES snap, key, n
Init == snap = Empty /\ key = k1 /\ n = 0
Start == snap = Empty /\ snap' = [k \in {k1, k2} |-> 0] /\ UNCHANGED <<key, n>>
Pick == key' = elsewhere /\ UNCHANGED <<snap, n>>
Put == snap' = [snap EXCEPT ![key] = 1 \div (n - n)] /\ UNCHANGED <<key, n>>
Next == Start \/ Pick \/ Put
"#;
    let cfg = "CONSTANTS k1 = k1 k2 = k2 elsewhere = elsewhere Empty = Empty\nINIT Init\nNEXT Next\n";
    let snap = Shape::Union(
        vec![
            Shape::Atom(atoms(&["Empty"])),
            Shape::Fcn {
                dom: atoms(KEYS),
                range: Box::new(int(0, 2)),
                witness: tlx_layout::FcnWitness::Enumerated,
                key_variants: std::sync::Arc::from([]),
            },
        ]
        .into(),
    );
    let key = Shape::Atom(atoms(&["k1", "k2", "elsewhere"]));
    let h = Harness::with_shapes(&module("ExceptUnionLazy", spec), cfg, vec![snap, key, int(0, 8)]);
    let dump = h.dump("Put");
    assert!(!dump.contains("interp "), "Put fell back to the interpreter:\n{dump}");
    assert!(dump.contains("not a function"), "no arm error branch:\n{dump}");
    let taken = dump.find("Concat").unwrap_or_else(|| panic!("no arm branch:\n{dump}"));
    let value = dump.find("DivFloor").unwrap_or_else(|| panic!("no replacement:\n{dump}"));
    assert!(value > taken, "the replacement is not inside the arm's branch:\n{dump}");
    let mut report = h.run_reachable(30);
    h.run_random(&mut tlx_testkit::Rng::new(919), 200, &mut report);
    report.assert_ok("deferred replacement");
    let t = &report.tallies["action Put"];
    // `snap = Empty` and a key outside the arm's domain leave the value
    // alone (`n` is not reassigned, so the layout never rejects the
    // successor); an eagerly evaluated `1 \div 0` would fail where the
    // interpreter succeeds.
    assert_eq!((t.0.bailout, t.1.bailout), (0, 0), "{}", report.render());
    assert!(t.0.both_fail > 0 && t.1.both_fail > 0, "{}", report.render());
    assert!(t.0.agree > 0 && t.1.agree > 0, "{}", report.render());
    assert_eq!((t.0.wrong, t.1.wrong), (0, 0), "{}", report.render());
}
