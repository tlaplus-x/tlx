//! A set of records holding a function of a fixed domain (and a nested
//! record, and the empty set) has an encoded order plan: its elements are
//! iterated in TLC order while staying encoded, so the binder keeps the
//! record's encoding and every field of it (including the function slot)
//! is read and compared natively.
//!
//! Without the plan the whole iteration source is boxed: the elements decode
//! to values and every operation on their fields returns to the host.
//!
//! - `function_field_sets_order_like_the_interpreter`: `CHOOSE` and `\E` over
//!   such a set pick the same first witness in every tier, so a plan whose
//!   order differs from TLC's is caught by the differential comparison, not
//!   only by the shape assertions;
//! - `the_iteration_stays_encoded`: the lowered `CHOOSE` uses the ordered set
//!   (no boxed element, no `ValField`) and C runs it without a host region.

use std::sync::Arc;

use tlx_layout::Shape;
use tlx_testkit::diff::{Backend, Consumer, Harness};
use tlx_testkit::{module, seed, Rng};
use tlx_value::Value;

const SRC: &str = r#"EXTENDS Integers, FiniteSets
CONSTANTS p1, p2
VARIABLES msgs, witness, tags
Init == msgs = {} /\ witness = 0 /\ tags = {}
Send == \E i \in 1..2 :
          msgs' = msgs \cup {[idx |-> i, tag |-> i,
                              fn |-> [q \in {p1, p2} |-> i],
                              inner |-> [lo |-> 0, hi |-> i],
                              empty |-> {}]}
          /\ UNCHANGED <<witness, tags>>
Pick == msgs # {}
        /\ LET m == CHOOSE x \in msgs : TRUE
           IN witness' = m.tag /\ tags' = {y.tag : y \in msgs} /\ UNCHANGED msgs
Next == Send \/ Pick
WitnessInRange == witness \in 0..2
SlotRead == \A m \in msgs : m.fn[p1] \in 0..2 /\ m.fn[p2] \in 0..2
Nested == \A m \in msgs : m.inner.lo <= m.inner.hi
EmptyField == \A m \in msgs : m.empty = {}
SlotCard == \A m \in msgs : Cardinality(m.slot) >= 1
"#;
const CFG: &str = "CONSTANTS p1 = T_p1 p2 = T_p2\nINIT Init\nNEXT Next\nINVARIANTS WitnessInRange SlotRead Nested EmptyField SlotCard\n";

fn harness() -> Harness {
    let mut dom: Vec<Value> = ["T_p1", "T_p2"].into_iter().map(Value::model_value).collect();
    dom.sort();
    let dom: Arc<[Value]> = dom.into();
    let elem = Shape::Record(
        vec![
            (tlx_value::Sym::new("idx"), Shape::Int { lo: 0, hi: 1000 }),
            (tlx_value::Sym::new("tag"), Shape::Int { lo: 1, hi: 2 }),
            (tlx_value::Sym::new("fn"), Shape::Fcn { dom, range: Box::new(Shape::Int { lo: 1, hi: 2 }) }),
            (
                tlx_value::Sym::new("inner"),
                Shape::Record(
                    vec![
                        (tlx_value::Sym::new("lo"), Shape::Int { lo: 0, hi: 0 }),
                        (tlx_value::Sym::new("hi"), Shape::Int { lo: 0, hi: 2 }),
                    ]
                    .into(),
                ),
            ),
            (tlx_value::Sym::new("empty"), Shape::Set { elem: Box::new(Shape::Never), max_card: 0 }),
            (tlx_value::Sym::new("slot"), Shape::Set { elem: Box::new(Shape::Int { lo: 1, hi: 2 }), max_card: 2 }),
        ]
        .into(),
    );
    let tags = Shape::Set { elem: Box::new(Shape::Int { lo: 1, hi: 2 }), max_card: 2 };
    Harness::with_shapes(
        &module("OrderedFunctionSet", SRC),
        CFG,
        vec![Shape::Set { elem: Box::new(elem), max_card: 2 }, Shape::Int { lo: 0, hi: 2 }, tags],
    )
}

#[test]
fn function_field_sets_order_like_the_interpreter() {
    let h = harness();
    assert!(h.notes.is_empty(), "not lowered: {:?}", h.notes);
    let mut report = h.run_reachable(200);
    h.run_random(&mut Rng::new(seed(0x0f06)), 200, &mut report);
    report.assert_ok("sets of function-carrying records");
    let (exec, native) = report.totals();
    assert!(exec.agree > 0 && native.agree > 0, "nothing compared\n{}", report.render());
    assert_eq!(exec.wrong + native.wrong, 0, "a tier disagreed with the interpreter\n{}", report.render());
    assert_eq!(native.unsupported, 0, "a tier stopped being native\n{}", report.render());
}

#[test]
fn the_iteration_stays_encoded() {
    let h = harness();
    assert!(h.node_kinds().contains("OrderedSet"), "the element plan is missing: {:?}", h.node_kinds());
    let pick = h.dump("Pick");
    assert!(!pick.contains("ValField"), "the element is boxed again:\n{pick}");
    assert!(h.not_native().is_empty(), "needs a host region: {:?}", h.not_native());
    let native = match h.backend {
        Backend::C => Consumer::C,
        Backend::Jit => Consumer::Jit,
    };
    h.consumers("ordered function sets", &["OrderedSet"], &[])
        .assert_ok()
        .assert_lowered()
        .assert_executed(native)
        .assert_gap(Consumer::Host);
    let c = &h.c_src;
    assert!(c.contains("switch (x_[0]) {") || c.contains("tlx_order_"), "the plan is not a static comparison: {c}");
}
