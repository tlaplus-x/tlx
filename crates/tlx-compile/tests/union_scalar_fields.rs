//! A union of records whose arms encode the same field as an atom of a
//! *per-arm* universe (the layout gives each arm a universe as wide as the
//! atoms seen in that arm) keeps the field read in the encoding: the arms'
//! slots are re-encoded into the union of those universes (`Recode`), so a
//! function application or a comparison on the field stays native.
//!
//! The boxed fallback (`ValField` on the decoded record) is what puts the
//! widest interpreter regions of the Raft models back in the host: the whole
//! record is decoded and the operation on the field with it.
//!
//! - `union_field_with_per_arm_universes_stays_encoded`: the read lowerers to
//!   an arm switch over re-encoded slots, with no host region, and every tier
//!   agrees with the interpreter on the reachable states, on random states of
//!   the layout, and on the error paths (an arm without the field, and a field
//!   atom outside the applied function's domain);
//! - `equal_arm_shapes_keep_the_cheap_union_field`: the same spec with one
//!   shared universe keeps the single-node `UnionField` read (a new lowering
//!   must never run ahead of a cheaper existing one);
//! - `union_field_universes_stay_inline_in_c`: the generated C switches on the
//!   union tag and re-encodes with a static table, with no host delegation.

use std::sync::Arc;

use tlx_layout::Shape;
use tlx_testkit::diff::{Backend, Consumer, DiffReport, Harness};
use tlx_testkit::{module, seed, Rng};
use tlx_value::{Sym, Value};

/// Model values in intern order: `Shape::Atom` universes must be sorted by
/// `Value::cmp`, so the names are interned before they are used and every
/// universe is built from this one list.
fn atoms(names: &[&str]) -> Vec<Value> {
    let mut values: Vec<Value> = names.iter().map(|s| Value::model_value(s)).collect();
    values.sort();
    values
}

/// `ufield` is `p1` in the first arm (universe `{p1}` there) and `p1`, `p2` or
/// `p3` in the second; `uextra` exists in the second arm only, and `f` is only
/// defined on `p1` and `p2`, so `p3` reaches the domain error of `f[m.ufield]`.
const SRC: &str = r#"EXTENDS Integers
CONSTANTS p1, p2, p3
VARIABLES m, f
Init == m = [ukind |-> 1, ufield |-> p1] /\ f = [q \in {p1, p2} |-> 0]
Next == \/ m' = [ukind |-> 1, ufield |-> p1] /\ UNCHANGED f
        \/ m' = [ukind |-> 2, ufield |-> p1, uextra |-> FALSE] /\ f' = [f EXCEPT ![p1] = 1]
        \/ m' = [ukind |-> 2, ufield |-> p2, uextra |-> TRUE] /\ f' = [f EXCEPT ![p2] = 1]
        \/ m' = [ukind |-> 2, ufield |-> p3, uextra |-> TRUE] /\ UNCHANGED f
Read == m.ufield = p1 \/ m.ufield = p2 \/ m.ufield = p3
Applied == f[m.ufield] >= 0
Missing == m.uextra = TRUE
"#;
const CFG: &str = "CONSTANTS p1 = T_p1 p2 = T_p2 p3 = T_p3\nINIT Init\nNEXT Next\nINVARIANTS Read Applied Missing\n";

/// The field names, interned in one order for both arms (record fields are
/// sorted by `Sym`, so the arms must agree on it).
fn field(name: &str) -> Sym {
    Sym::new(name)
}

/// `[ukind |-> k, ufield |-> <universe>]` with an optional `uextra: BOOLEAN`.
fn arm(k: i64, universe: &[Value], extra: bool, ukind: Sym, ufield: Sym, uextra: Sym) -> Shape {
    let mut fields: Vec<(Sym, Shape)> = vec![(ukind, Shape::Int { lo: k, hi: k }), (ufield, Shape::Atom(Arc::from(universe)))];
    if extra {
        fields.push((uextra, Shape::Bool));
    }
    Shape::Record(fields.into())
}

fn harness(narrow_first_arm: bool) -> Harness {
    let vs = atoms(&["T_p1", "T_p2", "T_p3"]);
    let (ukind, ufield, uextra) = (field("ukind"), field("ufield"), field("uextra"));
    let first = if narrow_first_arm { &vs[..1] } else { &vs[..] };
    let m = Shape::Union(vec![arm(1, first, false, ukind, ufield, uextra), arm(2, &vs, true, ukind, ufield, uextra)].into());
    let f = Shape::Fcn {
        dom: Arc::from(&vs[..2]),
        range: Box::new(Shape::Int { lo: 0, hi: 1 }),
        witness: tlx_layout::FcnWitness::Enumerated,
        key_variants: Arc::from([]),
    };
    Harness::with_shapes(&module("UnionScalarField", SRC), CFG, vec![m, f])
}

fn check(h: &Harness, what: &str) -> DiffReport {
    assert!(h.notes.is_empty(), "{what}: not lowered: {:?}", h.notes);
    assert!(h.not_native().is_empty(), "{what}: needs a host region: {:?}\n{}", h.not_native(), h.c_src);
    let mut report = h.run_reachable(200);
    h.run_random(&mut Rng::new(seed(0x0f05)), 200, &mut report);
    report.assert_ok(what);
    let (exec, native) = report.totals();
    assert!(exec.agree > 0 && native.agree > 0, "{what}: nothing compared\n{}", report.render());
    assert_eq!(exec.wrong + native.wrong, 0, "{what}\n{}", report.render());
    assert_eq!(native.unsupported, 0, "{what}: a tier stopped being native\n{}", report.render());
    report
}

#[test]
fn union_field_with_per_arm_universes_stays_encoded() {
    let h = harness(true);
    let read = h.dump("Read");
    assert!(!read.contains("ValField"), "the field read is boxed again:\n{read}");
    assert!(read.contains("Recode"), "the narrower arm is not re-encoded:\n{read}");
    assert!(!h.dump("Applied").contains("ValField"), "the applied field is boxed again:\n{}", h.dump("Applied"));
    let report = check(&h, "union field with per-arm universes");
    // An arm without the field (`m.uextra` on the first) and an atom outside
    // the applied function's domain (`f[p3]`) are errors in both tiers.
    let (exec, native) = report.totals();
    assert!(exec.both_fail > 0 && native.both_fail > 0, "no error path compared\n{}", report.render());
}

#[test]
fn equal_arm_shapes_keep_the_cheap_union_field() {
    let h = harness(false);
    let read = h.dump("Read");
    assert!(read.contains("UnionField"), "the shared arm shape lost the single-node read:\n{read}");
    assert!(!read.contains("Recode"), "a cheaper read was replaced by a re-encode table:\n{read}");
    check(&h, "union field with one shared universe");
}

#[test]
fn union_field_universes_stay_inline_in_c() {
    let h = harness(true);
    let c = &h.c_src;
    // Re-encoded arm slots: a static code table with its bound check and
    // unmapped-code error, switched on the union tag.
    assert!(c.contains("static const uint64_t"), "the re-encode has no static code table");
    assert!(c.contains("if (c_ >= "), "the re-encode has no code bound");
    assert!(c.contains("== (uint64_t)-1) return TLX_ERR;"), "the re-encode has no unmapped-code error");
    // The family runs in the active native tier and nowhere is it delegated to the host.
    let native = match h.backend {
        Backend::C => Consumer::C,
        Backend::Jit => Consumer::Jit,
    };
    h.consumers("union scalar fields", &["Recode"], &[]).assert_ok().assert_lowered().assert_executed(native).assert_gap(Consumer::Host);
}
