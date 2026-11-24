//! Bounded checks of declared symmetry use unreduced states.
use crate::common::run_spec;

#[test]
fn sound_symmetry_checks_generators() {
    let r = run_spec("SymCheckSound", &["-checksymmetry"]);
    assert_eq!(r.code, 0, "{}", r.text());
    assert!(r.stdout.contains("No symmetry violation found within bounds"), "{}", r.text());
    assert!(r.stdout.contains("2 permutations"), "{}", r.text());
}

#[test]
fn choose_breaks_next_equivariance() {
    let r = run_spec("SymCheckChoose", &["-checksymmetry"]);
    assert_eq!(r.code, 1, "{}", r.text());
    for text in ["SYMMETRY violation", "successor", "Pick", "State 1:", "a1", "a2"] {
        assert!(r.stdout.contains(text), "missing {text}: {}", r.text());
    }
}

fn custom(body: &str, cfg: &str, args: &[&str]) -> tlx_testkit::cli::Run {
    let dir = tlx_testkit::TempDir::new("symcheck");
    std::fs::write(
        dir.join("Spec.tla"),
        format!("---- MODULE Spec ----\nEXTENDS TLC, Naturals\nCONSTANT Nodes\nVARIABLE x\n{body}\n====\n"),
    )
    .unwrap();
    std::fs::write(
        dir.join("Spec.cfg"),
        format!("CONSTANT Nodes = {{a1, a2, a3}}\nINIT Init\nNEXT Next\nSYMMETRY Sym\nCHECK_DEADLOCK FALSE\n{cfg}\n"),
    )
    .unwrap();
    tlx_testkit::tlx!().args(["check", "Spec.tla", "-checksymmetry"]).args(args).dir(&dir).timeout(std::time::Duration::from_secs(10)).run()
}

#[test]
fn each_predicate_is_checked_independently() {
    for (body, cfg, part) in [
        ("Init == x = CHOOSE n \\in Nodes: TRUE\nNext == UNCHANGED x", "", "Init"),
        ("Init == x \\in Nodes\nNext == UNCHANGED x\nInv == x = CHOOSE n \\in Nodes: TRUE", "INVARIANT Inv", "invariant Inv"),
        ("Init == x \\in Nodes\nNext == UNCHANGED x\nV == x = CHOOSE n \\in Nodes: TRUE", "VIEW V", "VIEW"),
        ("Init == x \\in Nodes\nNext == UNCHANGED x\nC == x = CHOOSE n \\in Nodes: TRUE", "CONSTRAINT C", "state constraint C"),
        ("Init == x \\in Nodes\nNext == UNCHANGED x\nC == x' = CHOOSE n \\in Nodes: TRUE", "ACTION_CONSTRAINT C", "action constraint C"),
    ] {
        let r = custom(&format!("{body}\nSym == Permutations(Nodes)"), cfg, &[]);
        assert_eq!(r.code, 1, "{}", r.text());
        assert!(r.stdout.contains(part), "missing {part}: {}", r.text());
    }
}

#[test]
fn successor_cutoff_is_inconclusive_not_a_violation() {
    let r = run_spec("SymCheckSound", &["-checksymmetry", "-symmetryedges", "1"]);
    assert_eq!(r.code, 2, "{}", r.text());
    assert!(r.stdout.contains("incomplete"), "{}", r.text());
    assert!(!r.stdout.contains("SYMMETRY violation"), "{}", r.text());
}

#[test]
fn generators_avoid_factorial_startup() {
    let r = custom("CONSTANTS b1, b2, b3, b4, b5, b6, b7\nInit == x = Nodes\nNext == UNCHANGED x\nSym == Permutations(Nodes \\cup {b1, b2, b3, b4, b5, b6, b7})", "CONSTANTS b1=b1 b2=b2 b3=b3 b4=b4 b5=b5 b6=b6 b7=b7", &[]);
    // Init itself distinguishes Nodes from the other constants, so this
    // checks generator construction even though the declaration is unsound.
    assert_eq!(r.code, 1, "{}", r.text());
    assert!(r.stdout.contains("Init"), "{}", r.text());
}

#[test]
fn raw_successor_sets_allow_action_names_to_change() {
    let r = custom(
        "Init == x \\in Nodes\nA == x' = CHOOSE n \\in Nodes: TRUE\nB == \\E n \\in Nodes: x' = n\nNext == A \\/ B\nSym == Permutations(Nodes)",
        "", &[],
    );
    assert_eq!(r.code, 0, "{}", r.text());
}

#[test]
fn fallback_checks_declared_cycle_without_group_closure() {
    let r = custom(
        "CONSTANTS a1, a2, a3\nInit == x \\in Nodes\nNext == UNCHANGED x\nSym == {[n \\in Nodes |-> CASE n = a1 -> a2 [] n = a2 -> a3 [] OTHER -> a1]}\n",
        "CONSTANTS a1=a1 a2=a2 a3=a3", &[],
    );
    assert_eq!(r.code, 0, "{}", r.text());
    assert!(r.stdout.contains("1 permutations"), "{}", r.text());
}

#[test]
fn bounds_are_reported_and_cutoffs_do_not_claim_completion() {
    let r = run_spec("SymCheckSound", &["-checksymmetry", "-symmetrystates", "1", "-symmetrydepth", "0"]);
    assert_eq!(r.code, 0, "{}", r.text());
    assert!(r.stdout.contains("1 states checked"), "{}", r.text());
    assert!(r.stdout.contains("search bound reached"), "{}", r.text());
    assert!(r.stdout.contains("not a proof"), "{}", r.text());
    let r = run_spec("SymCheckSound", &["-checksymmetry", "-symmetryperms", "1"]);
    assert_eq!(r.code, 2, "{}", r.text());
    assert!(r.stdout.contains("incomplete"), "{}", r.text());
}

#[test]
fn no_declaration_and_conflicting_modes_are_rejected() {
    let r = run_spec("NeonLowering", &["-checksymmetry"]);
    assert_eq!(r.code, 2, "{}", r.text());
    assert!(r.stdout.contains("requires a SYMMETRY declaration"), "{}", r.text());
    let r = run_spec("SymCheckSound", &["-checksymmetry", "-simulate"]);
    assert_eq!(r.code, 2, "{}", r.text());
    assert!(r.text().contains("cannot be combined"), "{}", r.text());
}

#[test]
fn view_commutes_with_model_value_renaming() {
    let r =
        custom("Init == x \\in Nodes\nNext == x' \\in Nodes\nV == <<x, [n \\in Nodes |-> n]>>\nSym == Permutations(Nodes)", "VIEW V", &[]);
    assert_eq!(r.code, 0, "{}", r.text());
}

#[test]
fn permutations_override_is_respected() {
    let r = custom(
        "IdentityPerms(S) == {[n \\in S |-> n]}\nInit == x = CHOOSE n \\in Nodes: TRUE\nNext == UNCHANGED x\nSym == Permutations(Nodes)",
        "CONSTANT Permutations <- IdentityPerms",
        &[],
    );
    assert_eq!(r.code, 0, "{}", r.text());
    assert!(r.stdout.contains("0 permutations"), "{}", r.text());
}

#[test]
fn diagnostic_uses_interpreter_even_with_compile_and_workers() {
    let r = run_spec("SymCheckChoose", &["-checksymmetry", "-compile", "-workers", "4", "-tool"]);
    assert_eq!(r.code, 1, "{}", r.text());
    assert!(r.stdout.contains("one interpreter worker"), "{}", r.text());
    assert!(r.stdout.contains("SYMMETRY violation"), "{}", r.text());
    assert!(r.stdout.contains("@!@!@STARTMSG 2217:4"), "{}", r.text());
}
