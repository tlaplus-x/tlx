//! Applicability is proved from transfers, never assumed from TypeOK.
use tlx_front::cfg::parse_cfg;
use tlx_sema::{
    hir::{Expr, ExprKind, OpRef, RootSymbol},
    optimize::age_projection,
    Program,
};

const BODY: &str = r#"
VARIABLE clock, records, h
Empty == [status |-> "empty", payload |-> ""]
Init == /\ clock = 0 /\ records = [k \in {1, 2} |-> Empty] /\ h = <<>>
Tick == /\ clock' = clock + 1 /\ UNCHANGED <<records, h>>
Put == \E k \in {1, 2}:
         /\ records' = [records EXCEPT ![k] = [created |-> clock, payload |-> "x"]]
         /\ h' = Append(h, "put") /\ UNCHANGED clock
Drop == \E k \in {1, 2}:
          /\ records[k] # Empty /\ records[k].created + 2 <= clock
          /\ records' = [records EXCEPT ![k] = Empty]
          /\ h' = Append(h, "drop") /\ UNCHANGED clock
Next == Tick \/ Put \/ Drop
Inv == /\ clock \in Nat
       /\ records \in [{1, 2} -> [created: Nat, payload: {"x"}] \cup {Empty}]
       /\ h \in Seq({"put", "drop"})
"#;

fn projection(body: &str) -> Vec<String> {
    let dir = tlx_testkit::TempDir::new("age-sema");
    let path = dir.write("Age.tla", &format!("---- MODULE Age ----\nEXTENDS Integers, Sequences\n{body}\n====\n"));
    let mut p = Program::load(&path, &[]).unwrap();
    p.resolve_all_root();
    let roots = ["Init", "Next", "Inv"].map(|name| {
        let Some(RootSymbol::Def(id)) = p.lookup_root(name) else { panic!("missing {name}") };
        Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
    });
    age_projection(&p, &parse_cfg("INIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap(), &roots[0], &roots[1], &roots[2..])
        .map(|p| {
            assert!(p.certificate.as_ref().unwrap().contains("GeneratedAge"));
            p.fields
        })
        .unwrap_or_default()
}

#[test]
fn infers_certified_age_and_history_composition() {
    assert_eq!(projection(BODY), ["records.created.age<=2", "clock.logical-clock", "h.history"]);
    let renamed = BODY.replace("clock", "epoch").replace("created", "born").replace("records", "slots");
    assert_eq!(projection(&renamed), ["slots.born.age<=2", "epoch.logical-clock", "h.history"]);
}

#[test]
fn preserves_strict_and_exact_thresholds_in_both_directions() {
    for (comparison, cap) in [("<= clock", 2), ("< clock", 3), (">= clock", 3), ("> clock", 2), ("= clock", 3), ("# clock", 3)] {
        let body = BODY.replace("<= clock", comparison);
        assert!(projection(&body).contains(&format!("records.created.age<={cap}")), "{comparison}");
    }
    for (comparison, cap) in [
        ("clock >= records[k].created + 2", 2),
        ("clock > records[k].created + 2", 3),
        ("clock <= records[k].created + 2", 3),
        ("clock < records[k].created + 2", 2),
    ] {
        let body = BODY.replace("records[k].created + 2 <= clock", comparison);
        assert!(projection(&body).contains(&format!("records.created.age<={cap}")), "{comparison}");
    }
}

#[test]
fn refuses_observed_magnitudes_future_stamps_and_unknown_transfers() {
    for body in [
        BODY.replace("clock' = clock + 1", "clock' = clock - 1"),
        BODY.replace("created |-> clock", "created |-> clock + 1"),
        BODY.replace("created |-> clock", "created |-> 0"),
        BODY.replace("clock = 0", "clock = 1"),
        BODY.replace("<= clock", "<= 3"),
        BODY.replace("<= clock", "<= clock + 1"),
        BODY.replace("<= clock", "<= records[1].created"),
        BODY.replace("Inv ==", "Inv == clock < 10 /\\"),
        BODY.replace("Inv ==", "Inv == records[1] = records[2] /\\"),
        BODY.replace("Inv ==", "Inv == records[1].created = 0 /\\"),
        BODY.replace("clock' = clock + 1", "clock' = clock + 1 /\\ UNCHANGED clock"),
        BODY.replace("payload |-> \"x\"", "payload |-> clock"),
    ] {
        assert!(projection(&body).is_empty(), "{body}");
    }
}

#[test]
fn certificate_rejects_age_dependent_payloads_and_map_conditions() {
    // The applicability scan accepts these deadline reads, but the narrower
    // certificate must not interpret them as age-independent HIR leaves.
    for body in [
        BODY.replace("payload |-> \"x\"", "payload |-> IF records[1].created + 2 <= clock THEN \"x\" ELSE \"y\""),
        BODY.replace(
            "records' = [records EXCEPT ![k] = Empty]",
            "records' = IF records[k].created + 2 <= clock THEN [records EXCEPT ![k] = Empty] ELSE records",
        ),
    ] {
        assert!(projection(&body).is_empty(), "{body}");
    }
}

#[test]
fn finite_filters_and_quantifiers_are_certified_but_dynamic_domains_are_not() {
    let spec = include_str!("../../../proofs/age/FilteredAge.tla");
    let body = spec.split("VARIABLE").nth(1).unwrap().split("====").next().unwrap();
    let body = format!("VARIABLE{body}");
    assert!(!projection(&body).is_empty());
    let dynamic = body.replace("k \\in {1}: records[k] # Empty", "k \\in selected: records[k] # Empty");
    assert!(projection(&dynamic).is_empty());
    let filter = r#"{k \in {1}: records[k] # Empty /\ records[k].created + 2 <= clock}"#;
    assert!(projection(&body.replace(filter, &format!("({filter})'"))).is_empty());
    let observed = body.replace("Inv ==", "Inv == (\\A k \\in {1}: records[k] = Empty \\/ records[k].created <= clock) /\\");
    assert!(!projection(&observed).is_empty());
}

#[test]
fn composition_refuses_age_dependent_events() {
    for body in [
        BODY.replace("Append(h, \"drop\")", "Append(h, IF records[k].created + 2 <= clock THEN \"drop\" ELSE \"put\")"),
        BODY.replace("Append(h, \"put\")", "Append(h, clock)"),
        BODY.replace("Append(h, \"put\")", "Append(h, IF (\"created\" \\in DOMAIN records[k])' THEN \"put\" ELSE \"drop\")"),
    ] {
        assert!(!projection(&body).contains(&"h.history".to_owned()), "{body}");
    }
}

#[test]
fn composition_certifies_history_feedback() {
    for body in [
        BODY.replace("Tick ==", "Tick == h = <<>> /\\"),
        BODY.replace("Append(h, \"put\")", "(IF h = <<>> THEN Append(h, \"put\") ELSE h)"),
    ] {
        assert!(projection(&body).contains(&"h.history".to_owned()), "{body}");
    }
}

#[test]
fn composition_keeps_uncertified_feedback_boundaries() {
    for body in [
        BODY.replace("Tick ==", "Tick == (h = <<>>)' /\\"),
        BODY.replace("k \\in {1, 2}:", "k \\in (IF h = <<>> THEN {1} ELSE {2}):"),
        BODY.replace(
            "records' = [records EXCEPT ![k] = Empty]",
            "records' = (IF h = <<>> THEN [records EXCEPT ![k] = Empty] ELSE records)",
        ),
    ] {
        assert!(!projection(&body).contains(&"h.history".to_owned()), "{body}");
    }
}

#[test]
fn composition_certifies_mixed_history_and_age_consumers() {
    let source = include_str!("../../../proofs/age/AgeHistory.tla");
    let body = source.split("VARIABLE").nth(1).unwrap().split("====").next().unwrap();
    let body = format!("VARIABLE{body}")
        .replace("selected' = {k", "selected' = (IF history = <<>> THEN {} ELSE {k")
        .replace("created + 2 <= clock}", "created + 2 <= clock})");
    assert!(projection(&body).contains(&"history.history".to_owned()));
}

#[test]
fn mixed_consumers_refuse_dynamic_domains_and_primed_inputs() {
    let source = include_str!("../../../proofs/age/MixedHistory.tla");
    let body = source.split("VARIABLE").nth(1).unwrap().split("====").next().unwrap();
    let body = format!("VARIABLE{body}");
    for body in [
        body.replace("IF Ready /\\", "IF Ready' /\\"),
        body.replace("THEN Expired ELSE", "THEN Expired' ELSE"),
        body.replace("{k \\in Keys:", "{k \\in (IF history = <<>> THEN {1} ELSE Keys):"),
    ] {
        assert!(!projection(&body).contains(&"history.history".to_owned()), "{body}");
    }
}
