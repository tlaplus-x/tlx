use super::*;

const SPEC: &str = r#"---- MODULE Allocation ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
VARIABLE frontier, stored, versions
Init == /\ frontier = 1 /\ stored = [slots |-> <<[tag |-> 0]>>]
        /\ versions = [t \in {frontier} |-> FALSE]
Next == /\ frontier' = frontier + 1
        /\ stored' = [slots |-> <<[tag |-> frontier]>>]
        /\ versions' = versions @@ [t \in {frontier + 1} |-> TRUE]
Inv == /\ stored.slots[1].tag <= frontier /\ versions[frontier] \in BOOLEAN
====
"#;

fn plan(source: &str) -> Option<FieldProjection> {
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    let dir = tlx_testkit::TempDir::with_spec("ordered-analysis", source, cfg);
    let program = Program::load(&dir.join("Allocation.tla"), &[]).unwrap();
    let expr = |name: &str| {
        let def = program.defs.iter().find(|d| &*d.name == name).unwrap();
        let DefKind::Op(e) = &def.kind else { panic!() };
        e.clone()
    };
    candidate(&program, &tlx_front::cfg::parse_cfg(cfg).unwrap(), &expr("Init"), &expr("Next"), &[expr("Inv")])
}

#[test]
fn follows_structures_without_schema_names() {
    for source in [
        SPEC.to_string(),
        SPEC.replace("frontier", "serial")
            .replace("stored", "objects")
            .replace("versions", "archive")
            .replace("slots", "items")
            .replace("tag", "generation"),
    ] {
        let p = plan(&source).unwrap().ordered.unwrap();
        assert_eq!(p.history.unwrap().variable, 2);
        assert_eq!(p.variables[0].family, Some(0));
        assert!(p.variables[1].fields.values().next().unwrap().value.as_ref().unwrap().fields.values().next().unwrap().family.is_some());
    }
}

#[test]
fn refuses_non_equivariant_reads_and_transfers() {
    for (old, new) in [
        (
            "stored' = [slots |-> <<[tag |-> frontier]>>]",
            "stored' = [slots |-> <<[tag |-> frontier]>>] /\\ stored' = stored /\\ stored' \\in {stored}",
        ),
        ("stored.slots[1].tag <= frontier", "frontier < 10"),
        ("stored.slots[1].tag <= frontier", "ToString(frontier) = \"1\""),
        ("stored.slots[1].tag <= frontier", "Print(frontier, TRUE)"),
        ("stored.slots[1].tag <= frontier", "frontier - stored.slots[1].tag = 1"),
        ("stored.slots[1].tag <= frontier", "Cardinality(DOMAIN versions) = frontier"),
        ("stored.slots[1].tag <= frontier", "versions[frontier - 1] = TRUE"),
        ("stored.slots[1].tag <= frontier", "versions = [t \\in {frontier} |-> TRUE]"),
        ("stored.slots[1].tag <= frontier", "Len([t \\in {frontier} |-> TRUE]) = 1"),
        ("frontier' = frontier + 1", "frontier' = stored.slots[1].tag + 1"),
        ("tag |-> frontier]", "tag |-> frontier + 2]"),
        ("|-> TRUE]", "|-> frontier]"),
    ] {
        assert!(plan(&SPEC.replace(old, new)).is_none(), "accepted {new}");
    }
}

#[test]
fn rank_without_history_still_generalizes() {
    let source = SPEC.replace("versions @@ [t \\in {frontier + 1} |-> TRUE]", "[t \\in {frontier + 1} |-> TRUE]");
    let p = plan(&source).unwrap().ordered.unwrap();
    assert!(p.history.is_none());
}

#[test]
fn mutable_maps_are_ranked_but_not_garbage_collected() {
    let source = SPEC.replace("versions @@ [t \\in {frontier + 1} |-> TRUE]", "[versions EXCEPT ![frontier] = TRUE]");
    assert!(plan(&source).unwrap().ordered.unwrap().history.is_none());
}

#[test]
fn batch_allocations_and_independent_families() {
    let source = r#"---- MODULE Allocation ----
EXTENDS Naturals, FiniteSets
VARIABLE serial, other, tickets
Init == /\ serial = 1 /\ other = 100 /\ tickets = {}
Next == /\ serial' = serial + Cardinality({"a", "b"})
        /\ other' = other + 1
        /\ tickets' = serial..(serial + Cardinality({"a", "b"}))
Inv == (\A t \in tickets : t <= serial) /\ other > 0
====
"#;
    let p = plan(source).unwrap().ordered.unwrap();
    assert_eq!(p.anchors.len(), 2);
    assert!(plan(&source.replace("other > 0", "other > serial")).is_none());
    assert!(plan(&source.replace("other > 0", "other - 100 = serial")).is_none());
}

#[test]
fn universal_frame_requires_a_nonempty_domain() {
    let source = SPEC.replace("Next ==", "Step ==").replace(
        "Inv ==",
        "Next == Step \\/ (\\A member \\in {1} : stored.slots[1].tag = 0 /\\ UNCHANGED <<frontier, stored, versions>>)\nInv ==",
    );
    assert!(plan(&source).is_some());
    assert!(plan(&source.replace("member \\in {1}", "member \\in {}")).is_none());
}

#[test]
fn unknown_container_results_do_not_become_empty_provenance() {
    for replacement in [
        "Head(SubSeq(<<[slots |-> <<[tag |-> 100]>>]>>, 1, 1))",
        "SubSeq(<<[slots |-> <<[tag |-> 100]>>]>>, 1, 1)[1]",
        "[slots |-> SubSeq(<<[tag |-> 100]>>, 1, 1)]",
    ] {
        let source = SPEC.replace("stored = [slots |-> <<[tag |-> 0]>>]", &format!("stored = {replacement}"));
        assert!(plan(&source).is_none(), "accepted opaque result: {replacement}");
    }
    let colored_record = Shape { fields: BTreeMap::from([(Arc::from("id"), Shape::family(0))]), ..Default::default() };
    assert!(Shape::plain().joined(&colored_record).is_none());
}

#[test]
fn negation_keeps_unknown_integer_origins() {
    let source = SPEC
        .replace("EXTENDS Naturals", "EXTENDS Integers")
        .replace("VARIABLE frontier", "VARIABLE raw, frontier")
        .replace("Init ==", "Init == raw = 0 /\\")
        .replace("Next ==", "Next == raw' = raw - 1 /\\")
        .replace("stored.slots[1].tag <= frontier", "-raw < frontier");
    assert!(plan(&source).is_none());
}

const SCALAR: &str = r#"---- MODULE Allocation ----
EXTENDS Naturals, FiniteSets
VARIABLE frontier, bit
Init == frontier = 1 /\ bit = FALSE
Next == frontier' = frontier + 1 /\ bit' = IF Cardinality({frontier, 1}) = 2 THEN TRUE ELSE bit
Inv == frontier \in Nat /\ ~bit
====
"#;

#[test]
fn intermediate_consumers_keep_anchors_and_generate_a_certificate() {
    for expression in ["Cardinality({frontier, 1})", "Cardinality({frontier} \\cup {1})"] {
        let source = SCALAR.replace("Cardinality({frontier, 1})", expression);
        let p = plan(&source).unwrap();
        assert_eq!(p.ordered.unwrap().anchors, [vec![1]]);
        if expression == "Cardinality({frontier, 1})" {
            let proof = p.certificate.unwrap();
            assert!(proof.contains("Test.pairCardinalityEq 2"));
            assert!(proof.contains("namespace TlxOptimization.GeneratedOrdered"));
            assert!(proof.contains("theorem certificate : Certificate"));
        } else {
            // Analysis knows this anchor; the proof lowerer still refuses
            // syntax it does not give explicit semantics to.
            assert!(p.certificate.is_none());
        }
    }
    assert!(plan(&SCALAR.replace("{frontier, 1}", "{frontier, 10}")).is_none());
}

#[test]
fn uncertified_candidates_are_not_accepted_as_reductions() {
    for source in [SPEC, SCALAR] {
        let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
        let dir = tlx_testkit::TempDir::with_spec("ordered-certificate-gate", source, cfg);
        let program = Program::load(&dir.join("Allocation.tla"), &[]).unwrap();
        let expr = |name: &str| {
            let def = program.defs.iter().find(|d| &*d.name == name).unwrap();
            let DefKind::Op(e) = &def.kind else { panic!() };
            e.clone()
        };
        let result = ordered_projection(&program, &tlx_front::cfg::parse_cfg(cfg).unwrap(), &expr("Init"), &expr("Next"), &[expr("Inv")]);
        assert_eq!(result.is_some(), source == SCALAR);
    }
}

#[test]
fn certificates_follow_renamed_seeds_branches_and_observations() {
    let source = SCALAR
        .replace("frontier", "ticket")
        .replace("ticket = 1", "ticket = 7")
        .replace("ticket + 1", "ticket + 3")
        .replace("{ticket, 1}", "{ticket, 7}")
        .replace("Next ==", "Step ==")
        .replace("Inv ==", "Next == Step \\/ UNCHANGED <<ticket, bit>>\nInv ==");
    let p = plan(&source).unwrap();
    assert_eq!(p.ordered.unwrap().anchors, [vec![7]]);
    let proof = p.certificate.unwrap();
    assert!(proof.contains("seed := 7"));
    assert!(proof.contains("| 0 => 3"));
    assert!(proof.contains("| 1 => 0"));
    for condition in ["frontier # 1", "1 < frontier", "~(frontier <= 1)", "(frontier >= 1) /\\ ~(frontier = 1)"] {
        assert!(plan(&SCALAR.replace("Cardinality({frontier, 1}) = 2", condition)).unwrap().certificate.is_some(), "{condition}");
    }
    // The nested order-pattern model also certifies direct reference comparisons
    // when no fixed anchor is observed, even with no stored copies.
    let proof = plan(&SCALAR.replace("Cardinality({frontier, 1}) = 2", "frontier = frontier")).unwrap().certificate.unwrap();
    assert!(proof.contains("namespace TlxOptimization.GeneratedNested"));
}
