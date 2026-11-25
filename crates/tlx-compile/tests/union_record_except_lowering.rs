//! Lowering of heterogeneous `Union` record fields, intermediate `LET`-bound
//! records (including runtime bitset-domain functions), `EXCEPT` over encoded
//! values/sequences/sets, and ordered iteration over sorted sets of `Union`
//! records carrying `Map` fields.
//!
//! Every case runs in the closure IR, in generated C, and (with
//! `--features tlx-testkit/jit`) in the Cranelift JIT against the interpreter.

use std::sync::Arc;

use tlx_layout::{FcnWitness, Shape};
use tlx_testkit::diff::Harness;
use tlx_testkit::{module, seed, Rng};
use tlx_value::Value;

fn atoms(names: &[&str]) -> Arc<[Value]> {
    let mut v: Vec<Value> = names.iter().map(|n| Value::model_value(n)).collect();
    v.sort();
    Arc::from(v)
}

fn assert_fully_native(h: &Harness, actions: &[&str]) {
    assert!(h.notes.is_empty(), "not lowered: {:?}", h.notes);
    assert!(h.not_native().is_empty(), "needs host regions: {:?}", h.not_native());
    for a in actions {
        let d = h.dump(a);
        assert!(!d.contains("interp "), "{a} fell back to interpreter:\n{d}");
        assert!(!d.contains("ValField"), "{a} boxed a field read:\n{d}");
        assert!(!d.contains("valop "), "{a} boxed an operator:\n{d}");
    }
}

/// Heterogeneous union record fields (`Int` in arm 0 vs `Union([Int, Atom])`
/// in arm 1) flowing into a `LET`-bound record literal, `>`, `\in`, `=`,
/// `EXCEPT` with `@ \o SubSeq(...)`, and `Append` into a `Seq` of `Union`
/// records (`ReceiveMetadataUpdate` / `ApplyPartitionChange` pattern).
#[test]
fn union_record_field_and_except_stay_native() {
    let src = module(
        "UnionRecordExcept",
        r#"EXTENDS Naturals, Sequences, FiniteSets
CONSTANTS NoLeader, Nil
VARIABLES con_log, broker_log, part_md

Brokers == {1, 2}
BlankMd == [replicas |-> {}, isr |-> {}, leader |-> NoLeader, epoch |-> 0]

Init ==
    /\ con_log = <<[replicas |-> {1, 2}, isr |-> {1, 2}, leader |-> 1, epoch |-> 1]>>
    /\ broker_log = [b \in Brokers |-> <<>>]
    /\ part_md = [b \in Brokers |-> BlankMd]

MaybeShrink(s, b) == IF Cardinality(s) = 1 THEN s ELSE s \ {b}

AppendChange(b, new_leader, new_isr) ==
    con_log' = Append(con_log,
        [replicas |-> {1, 2},
         isr |-> new_isr,
         leader |-> new_leader,
         epoch |-> Len(con_log) + 1,
         extra |-> {}])

ControllerChange ==
    /\ Len(con_log) < 3
    /\ \E b \in Brokers :
        /\ AppendChange(b, NoLeader, MaybeShrink(con_log[Len(con_log)].isr, b))
        /\ UNCHANGED <<broker_log, part_md>>

ReceiveUpdate ==
    \E b \in Brokers :
        \E off \in (Len(broker_log[b]) + 1)..Len(con_log) :
            LET md == con_log[off]
                app == SubSeq(con_log, Len(broker_log[b]) + 1, off)
                curr == part_md[b]
                next_md == [replicas |-> md.replicas,
                            isr |-> md.isr,
                            leader |-> md.leader,
                            epoch |-> md.epoch]
            IN /\ broker_log' = [broker_log EXCEPT ![b] = @ \o app]
               /\ IF next_md.epoch > curr.epoch
                  THEN part_md' = [part_md EXCEPT ![b] =
                          IF b \in next_md.replicas THEN next_md ELSE BlankMd]
                  ELSE UNCHANGED part_md
               /\ UNCHANGED con_log

Next == ControllerChange \/ ReceiveUpdate
"#,
    );
    let cfg = "CONSTANTS NoLeader = NoLeader Nil = Nil\nINIT Init\nNEXT Next\n";
    let h = Harness::new(&src, cfg);
    assert_fully_native(&h, &["ControllerChange", "ReceiveUpdate"]);
    let mut report = h.run_reachable(80);
    h.run_random(&mut Rng::new(seed(0x6201)), 200, &mut report);
    report.assert_ok("union record field and EXCEPT");
    let (ir, native) = report.totals();
    assert!(ir.agree > 0 && native.agree > 0, "{}", report.render());
    assert_eq!((ir.wrong, native.wrong, native.unsupported, native.bailout), (0, 0, 0, 0), "{}", report.render());
}

/// Runtime bitset-domain function construction `[b1 \in proposed |-> ...]`
/// inside a `LET`-bound record literal, membership/insertion into a sorted set
/// of `Union` records, `EXCEPT` with bitset union, and `EXCEPT` wrapping a
/// record into a `Union([Atom, Record])` (`SendAlterPartitionRequest` pattern).
#[test]
fn bitset_fn_in_let_record_and_union_except_stay_native() {
    let src = module(
        "BitsetFnRecord",
        r#"EXTENDS Naturals, FiniteSets
CONSTANTS Req, Resp, Controller, Nil
VARIABLES msgs, pending, md, epochs

Brokers == {1, 2}

Init ==
    /\ msgs = {[type |-> Resp, dest |-> 1, epoch |-> 1]}
    /\ pending = [b \in Brokers |-> [epoch |-> 0, req |-> Nil]]
    /\ md = [b \in Brokers |-> [replicas |-> {1, 2}, isr |-> {1}, max_isr |-> {1}, epoch |-> 1]]
    /\ epochs = [b \in Brokers |-> b]

EpochsMap(b, proposed, curr) ==
    [b1 \in proposed |-> CASE b = b1 -> epochs[b]
                           [] b1 \in curr -> 0
                           [] OTHER -> epochs[b1]]

SendReq ==
    \E b \in Brokers :
        \E dropped \in SUBSET md[b].isr :
            LET curr == md[b].isr
                proposed == {b1 \in md[b].replicas : b1 = b \/ b1 \notin dropped}
                req == [type |-> Req,
                        isr |-> proposed,
                        isr_epochs |-> EpochsMap(b, proposed, curr),
                        dest |-> Controller,
                        source |-> b]
            IN /\ proposed # curr
               /\ ~(req \in msgs)
               /\ msgs' = msgs \cup {req}
               /\ md' = [md EXCEPT ![b].max_isr = proposed \cup curr]
               /\ pending' = [pending EXCEPT ![b] = [epoch |-> md[b].epoch + 1, req |-> req]]
               /\ UNCHANGED epochs

CheckPending ==
    \E b \in Brokers :
        /\ pending[b].req # Nil
        /\ \A k \in DOMAIN pending[b].req.isr_epochs : pending[b].req.isr_epochs[k] >= 0
        /\ UNCHANGED <<msgs, pending, md, epochs>>

Next == SendReq \/ CheckPending
"#,
    );
    let cfg = "CONSTANTS Req = Req Resp = Resp Controller = Controller Nil = Nil\nINIT Init\nNEXT Next\n";
    let h = Harness::new(&src, cfg);
    assert_fully_native(&h, &["SendReq", "CheckPending"]);
    assert!(h.dump("SendReq").contains("mapbuild"), "expected mapbuild in SendReq:\n{}", h.dump("SendReq"));
    let mut report = h.run_reachable(80);
    let (ir_r, native_r) = report.totals();
    assert_eq!((ir_r.bailout, native_r.bailout), (0, 0), "{}", report.render());
    h.run_random(&mut Rng::new(seed(0x6202)), 200, &mut report);
    report.assert_ok("bitset fn in LET record");
    let (ir, native) = report.totals();
    assert!(ir.agree > 0 && native.agree > 0, "{}", report.render());
    assert_eq!((ir.wrong, native.wrong, native.unsupported), (0, 0, 0), "{}", report.render());
}

/// Ordered iteration over a sorted set of `Union` records carrying a `Map`
/// arm, heterogeneous `m.dest` (`Int | Atom(Controller)`), `b = m.dest`,
/// `state[m.dest]`, `msgs \ {m}`, and inserting `m` into a `discard` set
/// whose union has fewer arms (`ReceiveBrokerRegResponse` pattern).
#[test]
fn union_message_dispatch_and_partial_union_coerce_stay_native() {
    let src = module(
        "UnionMessageDispatch",
        r#"EXTENDS Naturals, Sequences
CONSTANTS Req, Resp, Ack, Controller
VARIABLES msgs, discard, bstate, blog

Brokers == {1, 2}

Init ==
    /\ msgs = {
        [type |-> Resp, dest |-> 1, epoch |-> 2, offset |-> 1],
        [type |-> Ack, dest |-> 2, ok |-> TRUE],
        [type |-> Req, dest |-> Controller, epochs |-> [k \in {1} |-> k]]
       }
    /\ discard = {
        [type |-> Resp, dest |-> 2, epoch |-> 1, offset |-> 0],
        [type |-> Ack, dest |-> 1, ok |-> FALSE]
       }
    /\ bstate = [b \in Brokers |-> [epoch |-> 0, ready |-> FALSE]]
    /\ blog = [b \in Brokers |-> <<1>>]

SendReq ==
    \E s \in SUBSET Brokers :
        LET req == [type |-> Req, dest |-> Controller, epochs |-> [k \in s |-> k]]
        IN /\ s # {}
           /\ ~(req \in msgs)
           /\ msgs' = msgs \cup {req}
           /\ UNCHANGED <<discard, bstate, blog>>

HandleResp ==
    \E b \in Brokers :
        \E m \in msgs :
            /\ m.type = Resp
            /\ b = m.dest
            /\ bstate' = [bstate EXCEPT ![b] = [epoch |-> m.epoch, ready |-> ~bstate[m.dest].ready]]
            /\ blog' = [blog EXCEPT ![b] = IF m.offset <= 0 THEN <<>> ELSE SubSeq(blog[m.dest], 1, m.offset)]
            /\ msgs' = msgs \ {m}
            /\ discard' = discard \cup {m}

Next == SendReq \/ HandleResp
"#,
    );
    let cfg = "CONSTANTS Req = Req Resp = Resp Ack = Ack Controller = Controller\nINIT Init\nNEXT Next\n";
    let h = Harness::new(&src, cfg);
    assert_fully_native(&h, &["SendReq", "HandleResp"]);
    assert!(h.dump("HandleResp").contains("OrderedSet"), "expected OrderedSet in HandleResp:\n{}", h.dump("HandleResp"));
    let mut report = h.run_reachable(40);
    let (ir_r, native_r) = report.totals();
    assert_eq!((ir_r.bailout, native_r.bailout), (0, 0), "{}", report.render());
    h.run_random(&mut Rng::new(seed(0x6203)), 200, &mut report);
    report.assert_ok("union message dispatch");
    let (ir, native) = report.totals();
    assert!(ir.agree > 0 && native.agree > 0, "{}", report.render());
    assert_eq!((ir.wrong, native.wrong, native.unsupported), (0, 0, 0), "{}", report.render());
}

/// An enumerated-domain `Fcn` updated with a `Union([Int, Atom(Nil)])` key
/// must match TLC: updating at `Nil` leaves the function unchanged (no error),
/// while updating a `Tuple` at `Nil` errors as in TLC.
#[test]
fn union_key_except_respects_fcn_vs_tuple_witness() {
    let spec = r#"EXTENDS Naturals
CONSTANTS Nil
VARIABLES f, k
Init == f = [x \in {1, 2} |-> 0] /\ k = Nil
Toggle == k' = IF k = Nil THEN 1 ELSE Nil /\ UNCHANGED f
Update == f' = [f EXCEPT ![k] = 1] /\ UNCHANGED k
Next == Toggle \/ Update
"#;
    let cfg = "CONSTANTS Nil = Nil\nINIT Init\nNEXT Next\n";
    let fcn = Shape::Fcn {
        dom: Arc::from([Value::Int(1), Value::Int(2)]),
        range: Box::new(Shape::Int { lo: 0, hi: 1 }),
        witness: FcnWitness::Enumerated,
        key_variants: Arc::from([]),
    };
    let key = Shape::Union(Arc::from([Shape::Int { lo: 1, hi: 2 }, Shape::Atom(atoms(&["Nil"]))]));
    let h = Harness::with_shapes(&module("UnionKeyExceptFcn", spec), cfg, vec![fcn, key]);
    let mut report = h.run_reachable(20);
    h.run_random(&mut Rng::new(seed(0x6204)), 100, &mut report);
    report.assert_ok("union key EXCEPT on enumerated Fcn");
    let (ir, native) = report.totals();
    assert!(ir.agree > 0 && native.agree > 0, "{}", report.render());
    assert_eq!((ir.wrong, native.wrong), (0, 0), "{}", report.render());
}

/// `EXCEPT` storing a `LazySet` (`SUBSET S`) or `Interval` (`1..2`) must
/// preserve lazy-set / interval witness semantics (agreeing with interpreter).
#[test]
fn except_preserves_lazy_set_and_interval_semantics() {
    let src = module(
        "ExceptPreservesLazy",
        r#"EXTENDS Naturals
VARIABLES r, s
Init == r = [a |-> {}, b |-> 1] /\ s = {1, 2}
StoreSubset ==
    /\ r' = [r EXCEPT !.a = SUBSET s]
    /\ UNCHANGED s
StoreInterval ==
    /\ r' = [r EXCEPT !.a = 1..2]
    /\ UNCHANGED s
Next == StoreSubset \/ StoreInterval
"#,
    );
    let h = Harness::new(&src, "INIT Init\nNEXT Next\n");
    let mut report = h.run_reachable(20);
    h.run_random(&mut Rng::new(seed(0x6205)), 100, &mut report);
    report.assert_ok("EXCEPT preserves lazy sets and intervals");
    let (ir, native) = report.totals();
    assert!(ir.agree > 0 && native.agree > 0, "{}", report.render());
    assert_eq!((ir.wrong, native.wrong), (0, 0), "{}", report.render());
}

/// Set difference against an empty `Set { elem: Never }` stays native.
#[test]
fn set_diff_against_never_set_stays_native() {
    let src = module(
        "SetDiffNever",
        r#"EXTENDS Naturals
VARIABLES s, empty_rec
Init == s = {1, 2} /\ empty_rec = [rm |-> {}]
Next == s' = s \ empty_rec.rm /\ UNCHANGED empty_rec
"#,
    );
    let h = Harness::new(&src, "INIT Init\nNEXT Next\n");
    assert_fully_native(&h, &["Next"]);
    let mut report = h.run_reachable(20);
    h.run_random(&mut Rng::new(seed(0x6206)), 100, &mut report);
    report.assert_ok("set diff against Never set");
    let (ir, native) = report.totals();
    assert!(ir.agree > 0 && native.agree > 0, "{}", report.render());
    assert_eq!((ir.wrong, native.wrong, native.unsupported, native.bailout), (0, 0, 0, 0), "{}", report.render());
}

/// `[k \in S |-> body]` over a runtime bitset of set-valued keys (where bitset
/// rank order differs from TLC order, e.g. `{1, 2}` has rank 3 while `{3}` has
/// rank 4, yet TLC orders `{3} < {1, 2}`) must decline `Shape::Map` via
/// `tlx_layout::shape::map_shape` so decoded function pairs stay TLC-sorted.
#[test]
fn bitset_fn_set_valued_keys_preserve_tlc_order() {
    let src = module(
        "BitsetFnSetKeys",
        r#"EXTENDS Naturals, FiniteSets
VARIABLES keys, eq_ok
Init ==
    /\ keys = {{1, 2}, {3}}
    /\ eq_ok = TRUE
Next ==
    /\ LET m == [k \in keys |-> Cardinality(k)]
           ref == [k \in {{3}, {1, 2}} |-> Cardinality(k)]
       IN eq_ok' = (m = ref /\ m[{3}] = 1 /\ m[{1, 2}] = 2)
    /\ keys' \in {{{1, 2}, {3}}, {{1}, {2, 3}}}
"#,
    );
    let key = Shape::Set { elem: Box::new(Shape::Int { lo: 1, hi: 3 }), max_card: 3 };
    let keys = Shape::Set { elem: Box::new(key), max_card: 8 };
    let h = Harness::with_shapes(&src, "INIT Init\nNEXT Next\n", vec![keys, Shape::Bool]);
    assert!(!h.dump("Next").contains("mapbuild"), "set-key map must decline MapBuild:\n{}", h.dump("Next"));
    let mut report = h.run_reachable(40);
    h.run_random(&mut Rng::new(seed(0x6207)), 200, &mut report);
    report.assert_ok("bitset fn with set-valued keys");
    let (ir, native) = report.totals();
    assert!(ir.agree > 0 && native.agree > 0, "{}", report.render());
    assert_eq!((ir.wrong, native.wrong), (0, 0), "{}", report.render());
}

/// Immediate application `[k \in keys |-> body][2]` evaluates under TLC's
/// `KeepLazy` semantics: `body` runs only at key 2, so neither string creation
/// order (affecting `CHOOSE`) nor errors at unapplied keys may be observed.
#[test]
fn bitset_fn_lazy_application_preserves_key_order_and_errors() {
    let src = module(
        "BitsetFnKeyOrder",
        r#"EXTENDS Naturals, TLC
VARIABLES keys, n, ok
Init == keys = {1, 2, 3} /\ n = 10 /\ ok = TRUE
StepStrings ==
    /\ n < 25
    /\ ok' = IF [k \in keys |-> ToString(700000 + n + k) # ""][2]
             THEN (CHOOSE s \in {ToString(700000 + n + 1), ToString(700000 + n + 2)} : TRUE) = ToString(700000 + n + 2)
             ELSE FALSE
    /\ n' = n + 3
    /\ UNCHANGED keys
StepDeferredError ==
    /\ n < 25
    /\ ok' = ([k \in keys |-> IF k = 2 THEN 1 ELSE 1 \div 0][2] = 1)
    /\ n' = n + 3
    /\ UNCHANGED keys
Next == StepStrings \/ StepDeferredError
"#,
    );
    let h = Harness::new(&src, "INIT Init\nNEXT Next\n");
    assert!(!h.dump("StepStrings").contains("mapbuild"), "KeepLazy FnApp must not eagerly MapBuild:\n{}", h.dump("StepStrings"));
    assert!(
        !h.dump("StepDeferredError").contains("mapbuild"),
        "KeepLazy FnApp must not eagerly MapBuild:\n{}",
        h.dump("StepDeferredError")
    );
    let report = h.run_reachable(40);
    report.assert_ok("bitset fn lazy application");
    let (ir, native) = report.totals();
    assert!(ir.agree > 0 && native.agree > 0, "{}", report.render());
    assert_eq!((ir.wrong, native.wrong), (0, 0), "{}", report.render());
}

/// Eager `[k \in keys |-> body]` with observable string creation must visit
/// keys in TLC order (both when `keys` has set-valued elements whose bitset
/// rank disagrees with TLC order, and when building into an eager map).
#[test]
fn bitset_fn_eager_build_preserves_tlc_iteration_order() {
    let src = module(
        "BitsetFnBuildOrder",
        r#"EXTENDS Naturals, FiniteSets, TLC
VARIABLES keys, n, ok
Init == keys = {{"a", "b"}, {"c"}} /\ n = 10 /\ ok = TRUE
Next ==
    /\ n < 25
    /\ ok' = LET m == [k \in keys |-> ToString(800000 + n + Cardinality(k)) # ""]
             IN IF Cardinality(DOMAIN m) = 2
                THEN (CHOOSE s \in {ToString(800000 + n + 2), ToString(800000 + n + 1)} : TRUE) = ToString(800000 + n + 1)
                ELSE FALSE
    /\ n' = n + 3
    /\ UNCHANGED keys
"#,
    );
    let h = Harness::new(&src, "INIT Init\nNEXT Next\n");
    assert!(!h.dump("Next").contains("mapbuild"), "string-creating set-key fn must decline MapBuild:\n{}", h.dump("Next"));
    let report = h.run_reachable(40);
    report.assert_ok("bitset fn eager build order");
    let (ir, native) = report.totals();
    assert!(ir.agree > 0 && native.agree > 0, "{}", report.render());
    assert_eq!((ir.wrong, native.wrong), (0, 0), "{}", report.render());
}

/// Multi-parameter `RECURSIVE` operator inlining shares the caller's `LEnv`
/// across every parameter; string-creation analysis must deduplicate shared
/// environments rather than traversing them exponentially during map lowering.
#[test]
fn recursive_operator_map_build_avoids_env_blowup() {
    let src = module(
        "RecursiveRouteMap",
        r#"EXTENDS Naturals
VARIABLES brokers, live, load
Init == /\ brokers = {1, 2, 3} /\ live = {3} /\ load = [b \in {1, 2, 3} |-> 0]
RECURSIVE Route(_, _, _)
Route(node, left, amount) ==
    IF node \in live THEN
        /\ load' = [b \in brokers |-> IF b = node THEN amount ELSE load[b]]
        /\ UNCHANGED <<brokers, live>>
    ELSE /\ left > 0 /\ Route((node % 3) + 1, left - 1, amount)
Next == Route(1, 3, 1)
"#,
    );
    let h = Harness::new(&src, "INIT Init\nNEXT Next\n");
    let report = h.run_reachable(20);
    report.assert_ok("recursive operator map build");
    let (ir, native) = report.totals();
    assert!(ir.agree > 0 && native.agree > 0, "{}", report.render());
    assert_eq!((ir.wrong, native.wrong), (0, 0), "{}", report.render());
}
