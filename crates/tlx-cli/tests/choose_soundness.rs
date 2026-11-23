//! End-to-end CLI soundness regression tests for certified choice-irrelevant automatic symmetry.

use std::time::Duration;

fn run_spec(body: &str, cfg: &str, args: &[&str], env: &[(&str, &str)]) -> tlx_testkit::cli::Run {
    let dir = tlx_testkit::TempDir::new("choose-soundness");
    std::fs::write(dir.join("Spec.tla"), format!("---- MODULE Spec ----\nEXTENDS Integers, FiniteSets\nCONSTANT Proc\n{body}\n====\n"))
        .unwrap();
    std::fs::write(dir.join("Spec.cfg"), format!("CONSTANT Proc = {{p1, p2, p3}}\nINIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n{cfg}\n"))
        .unwrap();
    tlx_testkit::tlx_default!()
        .args(["check", "Spec.tla"])
        .args(args)
        .env("TLX_PROOF_DIR", dir.join("proofs"))
        .envs(env.iter().copied())
        .dir(&dir)
        .timeout(Duration::from_secs(60))
        .run()
}

fn assert_refused_and_matches_unreduced(body: &str, cfg: &str) {
    for tier in ["-interp", "-compile"] {
        let reference = run_spec(body, cfg, &[tier, "-noautosymmetry"], &[]);
        let default = run_spec(body, cfg, &[tier], &[("TLX_SYMMETRY_PARANOID", "1")]);
        assert_eq!(default.code, reference.code, "tier={tier}\nref:\n{}\ndefault:\n{}", reference.text(), default.text());
        assert!(!default.stdout.contains("(symmetry-reduced)"), "unsound spec must not apply symmetry (tier={tier}):\n{}", default.text());
        assert_eq!(
            tlx_testkit::cli::counts(&default.stdout),
            tlx_testkit::cli::counts(&reference.stdout),
            "tier={tier}\nref:\n{}\ndefault:\n{}",
            reference.text(),
            default.text()
        );
    }
}

#[test]
fn non_capture_avoiding_only_pattern_is_refused_end_to_end() {
    // `(y = x \/ pc < 0) => y = x` holds for every `x` when `pc >= 0`, so `CHOOSE` is NOT unique.
    let body = r#"
VARIABLES pc, picked, target
Init == pc = 0 /\ picked = "none" /\ target \in Proc
Next ==
    /\ pc = 0
    /\ pc' = 1
    /\ picked' = CHOOSE x \in Proc : (x = x \/ pc < 0) /\ \A y \in Proc : (y = x \/ pc < 0) => y = x
    /\ UNCHANGED target
Inv == picked = "none" \/ picked = target
"#;
    assert_refused_and_matches_unreduced(body, "INVARIANT Inv");
}

#[test]
fn scalar_slot_membership_with_multiple_primed_equalities_is_refused_end_to_end() {
    let body = r#"
VARIABLES x
Pick == CHOOSE p \in Proc : TRUE
Init == x \in Proc
Next == x' \in Proc /\ x' = x /\ x' = Pick
Inv == x \in Proc
"#;
    assert_refused_and_matches_unreduced(body, "INVARIANT Inv");
}

#[test]
fn choose_sum_fold_with_32bit_overflow_risk_is_refused_end_to_end() {
    // Under checked 32-bit signed arithmetic, `(2147483647 + 1) + (-1)` overflows while
    // `(2147483647 + (-1)) + 1` succeeds; permutations of `{2147483647, 1, -1}` differ!
    let body = r#"
VARIABLES votes
RECURSIVE Sum(_)
Sum(S) == IF S = {} THEN 0 ELSE LET p == CHOOSE x \in S : TRUE IN votes[p] + Sum(S \ {p})
Init == votes \in [Proc -> {2147483647, 1, -1}]
Next == UNCHANGED votes
Inv == Sum(Proc) >= -3
"#;
    assert_refused_and_matches_unreduced(body, "INVARIANT Inv");
}

#[test]
fn partial_power_zero_pow_zero_in_choose_predicate_is_refused_end_to_end() {
    // `0 ^ 0` errors while `1 ^ 1 = 1` succeeds; candidate evaluation order determines whether
    // `CHOOSE m \in msgs : m.tag ^ m.tag = 1` succeeds or fails with an evaluation error!
    let body = r#"
VARIABLES msgs
Init == \E p \in Proc : msgs = {[from |-> p, tag |-> 0, val |-> 7]}
Next == \E p \in Proc : msgs' = msgs \cup {[from |-> p, tag |-> 1, val |-> 7]}
Inv == (msgs # {} /\ \E m \in msgs : m.tag = 1) => (CHOOSE m \in msgs : m.tag ^ m.tag = 1).val = 7
"#;
    assert_refused_and_matches_unreduced(body, "INVARIANT Inv");
}

#[test]
fn hoisted_choice_and_correlated_init_certify_and_match_unreduced_verdicts() {
    let hoisted = r#"
VARIABLES votes, owner, leaders
Init ==
    /\ votes = [p \in Proc |-> 0]
    /\ owner = "none"
    /\ \E p \in Proc : leaders = {p}
Next ==
    \E p \in Proc :
        /\ votes[p] < 1
        /\ votes' = [votes EXCEPT ![p] = @ + 1]
        /\ owner' = CHOOSE q \in Proc : q \in leaders
        /\ UNCHANGED leaders
Inv == \A p \in Proc : votes[p] \in 0..1
"#;
    let correlated = r#"
VARIABLES owner, leaders
Init == \E p \in Proc : owner = p /\ leaders = {p}
Next ==
    /\ owner' = CHOOSE q \in Proc : q \in leaders
    /\ UNCHANGED leaders
Inv == owner \in leaders
"#;
    for body in [hoisted, correlated] {
        for tier in ["-interp", "-compile"] {
            let reference = run_spec(body, "INVARIANT Inv", &[tier, "-noautosymmetry"], &[]);
            let reduced = run_spec(body, "INVARIANT Inv", &[tier], &[("TLX_SYMMETRY_PARANOID", "1")]);
            assert_eq!(reference.code, 0, "{}", reference.text());
            assert_eq!(reduced.code, 0, "{}", reduced.text());
            assert!(reduced.stdout.contains("(symmetry-reduced)"), "{}", reduced.text());
            assert!(reduced.stdout.contains("certificate generated"), "{}", reduced.text());
        }
    }
}

#[test]
fn non_boolean_choose_predicate_is_refused_end_to_end() {
    // Exact Codex Astra Round-2 counterexample:
    // For `owner = p1`, the first candidate matches `m.from = owner` and returns `TRUE`,
    // whereas for `owner = p2`, evaluating the `ELSE 1` branch fails with a non-boolean error.
    let body = r#"
VARIABLES owner, msgs
Init ==
    /\ owner \in Proc
    /\ msgs = {[from |-> p, val |-> 7] : p \in Proc}
Next == UNCHANGED <<owner, msgs>>
Inv == (CHOOSE m \in msgs : IF m.from = owner THEN TRUE ELSE 1).val = 7
"#;
    let reference = run_spec(body, "INVARIANT Inv", &["-interp", "-noautosymmetry"], &[]);
    assert_ne!(reference.code, 0, "unreduced check must catch non-boolean CHOOSE predicate:\n{}", reference.text());
    assert_refused_and_matches_unreduced(body, "INVARIANT Inv");
}

#[test]
fn incomparable_subseteq_in_choose_predicate_is_refused_end_to_end() {
    // Exact Codex Astra Round-2 counterexample:
    // `{1} \subseteq {"x"}` compares integer `1` with string `"x"` and errors when `owner /= p1`.
    let body = r#"
VARIABLES owner, msgs
Init ==
    /\ owner \in Proc
    /\ msgs = {[from |-> p, val |-> 7] : p \in Proc}
Next == UNCHANGED <<owner, msgs>>
Inv == (CHOOSE m \in msgs : IF m.from = owner THEN TRUE ELSE {1} \subseteq {"x"}).val = 7
"#;
    let reference = run_spec(body, "INVARIANT Inv", &["-interp", "-noautosymmetry"], &[]);
    assert_ne!(reference.code, 0, "unreduced check must catch incomparable \\subseteq error:\n{}", reference.text());
    assert_refused_and_matches_unreduced(body, "INVARIANT Inv");
}

#[test]
fn typed_model_value_set_comparison_in_choose_predicate_is_refused_end_to_end() {
    // Typed model value `P_1` is incomparable with integer `1` under `eq_tlc`/`cmp_tlc`.
    let dir = tlx_testkit::TempDir::new("choose-soundness-typed-mv");
    std::fs::write(
        dir.join("Spec.tla"),
        r#"---- MODULE Spec ----
EXTENDS Integers, FiniteSets
CONSTANTS Proc, Tag
VARIABLES owner, msgs
Init ==
    /\ owner \in Proc
    /\ msgs = {[from |-> p, val |-> 7] : p \in Proc}
Next == UNCHANGED <<owner, msgs>>
Inv == (CHOOSE m \in msgs : IF m.from = owner THEN TRUE ELSE {Tag} \subseteq {1}).val = 7
====
"#,
    )
    .unwrap();
    std::fs::write(
        dir.join("Spec.cfg"),
        "CONSTANTS\n  Proc = {p1, p2, p3}\n  Tag = P_1\nINIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\nINVARIANT Inv\n",
    )
    .unwrap();
    for tier in ["-interp", "-compile"] {
        let reference = tlx_testkit::tlx_default!()
            .args(["check", "Spec.tla", tier, "-noautosymmetry"])
            .env("TLX_PROOF_DIR", dir.join("proofs-ref"))
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        let default = tlx_testkit::tlx_default!()
            .args(["check", "Spec.tla", tier])
            .env("TLX_PROOF_DIR", dir.join("proofs-def"))
            .env("TLX_SYMMETRY_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_ne!(reference.code, 0, "unreduced check must fail on typed model value vs int (tier={tier}):\n{}", reference.text());
        assert_eq!(default.code, reference.code, "tier={tier}\nref:\n{}\ndefault:\n{}", reference.text(), default.text());
        assert!(!default.stdout.contains("(symmetry-reduced)"), "unsound spec must not apply symmetry (tier={tier}):\n{}", default.text());
    }
}
