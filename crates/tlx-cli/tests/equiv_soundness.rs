//! End-to-end CLI soundness regression tests for `equiv_sym` / `EquivSymCertificate`.

use std::time::Duration;

fn run_spec(body: &str, cfg_extra: &str, args: &[&str], env: &[(&str, &str)]) -> tlx_testkit::cli::Run {
    let dir = tlx_testkit::TempDir::new("equiv-soundness");
    std::fs::write(
        dir.join("Spec.tla"),
        format!("---- MODULE Spec ----\nEXTENDS TLC, Naturals, Sequences, FiniteSets\nCONSTANT Proc\n{body}\n====\n"),
    )
    .unwrap();
    std::fs::write(
        dir.join("Spec.cfg"),
        format!("CONSTANT Proc = {{p1, p2, p3}}\nINIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n{cfg_extra}\n"),
    )
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

#[test]
fn quantified_zero_pow_zero_fails_identically_with_and_without_autosym() {
    // Codex Astra's exact non-CHOOSE counterexample: scan order in `\E p \in Proc`
    // can short-circuit on `parent[p1] = p1` (1^1 = 1) for one orbit representative
    // while another orbit representative hits `0^0` first and errors.
    let body = "\
VARIABLE parent
Init == \\E r \\in Proc : parent = [p \\in Proc |-> r]
Next == UNCHANGED parent
Inv == \\E p \\in Proc :
         LET n == IF parent[p] = p THEN 1 ELSE 0
         IN n ^ n = 1";
    for tier in ["-interp", "-compile"] {
        let unreduced = run_spec(body, "INVARIANT Inv", &[tier, "-noautosymmetry"], &[]);
        let default = run_spec(body, "INVARIANT Inv", &[tier], &[]);
        assert_ne!(unreduced.code, 0, "{tier} unreduced must hit 0^0 error: {}", unreduced.text());
        assert_eq!(
            default.code,
            unreduced.code,
            "{tier} default must fail identically:\nDEFAULT:\n{}\nUNREDUCED:\n{}",
            default.text(),
            unreduced.text()
        );
        assert!(!default.stdout.contains("(symmetry-reduced)"), "{tier} must not apply symmetry: {}", default.text());
    }
}

#[test]
fn quantified_out_of_domain_indexing_fails_identically() {
    let body = "\
VARIABLE parent
Init == \\E r \\in Proc : parent = [q \\in {r} |-> r]
Next == UNCHANGED parent
Inv == \\E p \\in Proc : parent[p] = p";
    for tier in ["-interp", "-compile"] {
        let unreduced = run_spec(body, "INVARIANT Inv", &[tier, "-noautosymmetry"], &[]);
        let default = run_spec(body, "INVARIANT Inv", &[tier], &[]);
        assert_ne!(unreduced.code, 0, "{tier} unreduced must error: {}", unreduced.text());
        assert_eq!(default.code, unreduced.code, "{tier} default must fail identically:\n{}\n{}", default.text(), unreduced.text());
        assert!(!default.stdout.contains("(symmetry-reduced)"), "{tier} must not apply symmetry: {}", default.text());
    }
}

#[test]
fn tuple_arity_mismatch_fails_identically() {
    // Sequence-valued state forces equiv_sym (not keyed), which must refuse the
    // unproved 3-tuple destructuring `<<a, b>> \in {<<1, 2, 3>>}`.
    let body = "\
VARIABLE x
Init == x \\in {<<p>> : p \\in Proc}
Next == UNCHANGED x
Inv == \\A <<a, b>> \\in {<<1, 2, 3>>} : TRUE";
    for tier in ["-interp", "-compile"] {
        let unreduced = run_spec(body, "INVARIANT Inv", &[tier, "-noautosymmetry"], &[]);
        let default = run_spec(body, "INVARIANT Inv", &[tier], &[]);
        assert_ne!(unreduced.code, 0, "{tier} unreduced must raise arity error: {}", unreduced.text());
        assert_eq!(default.code, unreduced.code, "{tier} default must fail identically:\n{}\n{}", default.text(), unreduced.text());
        assert!(!default.stdout.contains("(symmetry-reduced)"), "{tier} must not apply symmetry: {}", default.text());
    }
}

#[test]
fn seq_fn_equality_oob_except_and_is_finite_set_reduce_soundly() {
    let body = "\
VARIABLE s
Init == s \\in {<<p>> : p \\in Proc}
Next == \\E p \\in Proc : s' = <<p>>
Inv ==
  /\\ \\A p \\in Proc : <<p>> = [i \\in 1..1 |-> p]
  /\\ \\A p \\in Proc : Cardinality({<<p>>, [i \\in 1..1 |-> p]}) = 1
  /\\ [s EXCEPT ![2] = 1 \\div 0] = s
  /\\ IsFiniteSet(s)
  /\\ IsFiniteSet([a |-> s])";
    let unreduced = run_spec(body, "INVARIANT Inv", &["-interp", "-noautosymmetry"], &[]);
    assert_eq!(unreduced.code, 0, "{}", unreduced.text());
    assert!(unreduced.stdout.contains("3 distinct states found"), "{}", unreduced.text());

    for tier in ["-interp", "-compile"] {
        let reduced = run_spec(body, "INVARIANT Inv", &[tier], &[("TLX_SYMMETRY_PARANOID", "1")]);
        assert_eq!(reduced.code, 0, "{tier}: {}", reduced.text());
        assert!(reduced.stdout.contains("certificate generated"), "{tier}: {}", reduced.text());
        assert!(
            reduced.stdout.contains("1 distinct states found, 0 states left on queue (symmetry-reduced)."),
            "{tier}: {}",
            reduced.text()
        );
    }
}

#[test]
fn round2_soundness_repros_fail_identically_without_symmetry() {
    // End-to-end verification across both interpreter and compiled tiers that
    // Round-2 totality counterexamples refuse automatic symmetry and fail identically
    // to `-noautosymmetry`.
    let cases: &[(&str, &str, &str)] = &[
        (
            "keyed_div_zero",
            "CONSTANT Proc = {p1, p2, p3}",
            "VARIABLE owner\n\
             Init == owner \\in Proc\n\
             Next == UNCHANGED owner\n\
             Inv == \\E p \\in Proc : owner = p \\/ 1 \\div 0 = 0",
        ),
        (
            "top_level_fn_neq_type_err",
            "CONSTANT Proc = {p1, p2, p3}",
            "VARIABLE f\n\
             Init == \\E r \\in Proc : f = [p \\in Proc |-> IF p = r THEN 0 ELSE \"a\"]\n\
             Next == UNCHANGED f\n\
             Inv == f # [p \\in Proc |-> 1]",
        ),
        (
            "value_pos_exists_in_next",
            "CONSTANT Proc = {p1, p2, p3}",
            "VARIABLES parent, ok\n\
             Init == (\\E r \\in Proc : parent = [p \\in Proc |-> r]) /\\ ok = TRUE\n\
             Next == parent' = parent /\\ ok' = (\\E p \\in Proc : parent'[p] = p \\/ parent[1] = p)\n\
             Inv == ok",
        ),
        (
            "typed_model_value_cmp",
            "CONSTANT Proc = {P_1, P_2, P_3}",
            "VARIABLE owner\n\
             Init == owner \\in Proc\n\
             Next == UNCHANGED owner\n\
             Inv == \\E p \\in Proc : owner = p \\/ 1 = p",
        ),
        (
            "str_index_record_except_div_zero",
            "CONSTANT Proc = {p1, p2, p3}",
            "VARIABLES rec, owner\n\
             Init == rec = [n |-> 1] /\\ owner \\in Proc\n\
             Next == rec' = [rec EXCEPT ![\"n\"] = 0] /\\ UNCHANGED owner\n\
             Inv == \\E p \\in Proc : owner = p \\/ 1 \\div rec.n = 1",
        ),
    ];

    for (name, const_cfg, body) in cases {
        let dir = tlx_testkit::TempDir::new(&format!("r2-{name}"));
        std::fs::write(
            dir.join("Spec.tla"),
            format!("---- MODULE Spec ----\nEXTENDS TLC, Naturals, Sequences, FiniteSets\nCONSTANT Proc\n{body}\n====\n"),
        )
        .unwrap();
        std::fs::write(dir.join("Spec.cfg"), format!("{const_cfg}\nINIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\nINVARIANT Inv\n")).unwrap();
        for tier in ["-interp", "-compile"] {
            let unreduced = tlx_testkit::tlx_default!()
                .args(["check", "Spec.tla", tier, "-noautosymmetry"])
                .env("TLX_PROOF_DIR", dir.join("proofs"))
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            let default = tlx_testkit::tlx_default!()
                .args(["check", "Spec.tla", tier])
                .env("TLX_PROOF_DIR", dir.join("proofs"))
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            assert_ne!(unreduced.code, 0, "{name} ({tier}) unreduced must fail: {}", unreduced.text());
            assert_eq!(
                default.code,
                unreduced.code,
                "{name} ({tier}) default must fail identically:\nDEFAULT:\n{}\nUNREDUCED:\n{}",
                default.text(),
                unreduced.text()
            );
            assert!(!default.stdout.contains("(symmetry-reduced)"), "{name} ({tier}) must not apply symmetry: {}", default.text());
        }
    }
}
