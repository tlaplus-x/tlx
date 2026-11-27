//! Certified supersets of a declared `.cfg` `SYMMETRY` in the default mode:
//! the declared group factors into full symmetric groups, disjoint proven
//! candidates extend it, and one connected Lean certificate covers the whole
//! product. `-tlc` and `-noautosymmetry` keep the declared group verbatim.

use std::time::Duration;

const TLA: &str = include_str!("../../../proofs/symmetry/DeclaredProduct.tla");
const CFG: &str = include_str!("../../../proofs/symmetry/DeclaredProduct.cfg");

/// Run the checked-in declared-product example (or a variant that keeps its
/// module name) with `args`.
fn run(src: &str, cfg: &str, args: &[&str], env: &[(&str, &str)]) -> (tlx_testkit::cli::Run, tlx_testkit::TempDir) {
    let dir = tlx_testkit::TempDir::with_spec("autosym-augment", src, cfg);
    let run = tlx_testkit::tlx_default!()
        .args(["check", "DeclaredProduct.tla"])
        .args(args)
        .env("TLX_PROOF_DIR", dir.join("proofs"))
        .envs(env.iter().copied())
        .dir(&dir)
        .timeout(Duration::from_secs(120))
        .run();
    (run, dir)
}

/// The distinct-state count of a run's final statistics line.
fn distinct(stdout: &str) -> u64 {
    stdout
        .lines()
        .find_map(|l| l.split_once(" distinct states found"))
        .and_then(|(prefix, _)| prefix.split_whitespace().last())
        .expect("a distinct-state statistics line")
        .replace(',', "")
        .parse()
        .unwrap()
}

const AUGMENTED: &str = "Optimizations: symmetry Permutations(TxId) x Permutations(Key) x Permutations(Val) (certificate generated";

#[test]
fn default_mode_certifies_the_declared_product_superset() {
    for tier in ["-interp", "-compile"] {
        for env in [vec![], vec![("TLX_SYMMETRY_PARANOID", "1")]] {
            let (r, dir) = run(TLA, CFG, &[tier], &env);
            assert_eq!(r.code, 0, "{tier} {env:?}: {}", r.text());
            assert!(r.stdout.contains(AUGMENTED), "{tier} {env:?}: {}", r.text());
            assert!(r.stdout.contains("Lean output:"), "{tier} {env:?}: {}", r.text());
            // 2^3 x 2^3 x 2^2 concrete states quotiented by S_3 x S_3 x S_2.
            assert_eq!(distinct(&r.stdout), 48, "{tier} {env:?}: {}", r.text());
            assert!(r.stdout.contains("48 distinct states found"), "{tier} {env:?}: {}", r.text());
            assert!(r.stdout.contains("(symmetry-reduced)"), "{tier} {env:?}: {}", r.text());
            // No suggestion line in the default mode: the group is applied.
            assert!(!r.stdout.contains("Symmetry: "), "{tier} {env:?}: {}", r.text());
            if tier == "-interp" && env.is_empty() {
                let proof = std::fs::read_dir(dir.join("proofs"))
                    .unwrap()
                    .map(|e| e.unwrap().path().join("Optimization.lean"))
                    .find(|p| p.exists())
                    .expect("a generated certificate");
                let lean = std::fs::read_to_string(proof).unwrap();
                assert!(lean.contains("namespace TlxOptimization.GeneratedSymmetry"), "{lean}");
                assert!(lean.contains("theorem counterexample_lifts"), "{lean}");
                assert!(!lean.contains("sorry"), "{lean}");
            }
        }
    }
}

#[test]
fn tlc_and_noautosymmetry_keep_the_declared_group() {
    for args in [vec!["-tlc", "-interp"], vec!["-noautosymmetry", "-interp"], vec!["-tlc", "-compile"], vec!["-noautosymmetry", "-compile"]]
    {
        let (r, _) = run(TLA, CFG, &args, &[]);
        assert_eq!(r.code, 0, "{args:?}: {}", r.text());
        // Only TxIdSymmetric: 4 TxId classes x 2^3 Key states x 2^2 Val states.
        assert_eq!(distinct(&r.stdout), 128, "{args:?}: {}", r.text());
        assert!(!r.stdout.contains("(symmetry-reduced)"), "{args:?}: {}", r.text());
        assert!(!r.stdout.contains(AUGMENTED), "{args:?}: {}", r.text());
    }
}

#[test]
fn augmentation_preserves_counterexample_and_deadlock_verdicts() {
    let states = |s: &str| s.lines().filter(|l| l.starts_with("State ")).count();
    // A violated symmetric invariant.
    let bad = TLA.replace(
        "Inv == \\A t \\in TxId : tx[t] <= 1\n    /\\ \\A k \\in Key : key[k] <= 1\n    /\\ \\A v \\in Val : val[v] <= 1",
        "Inv == Cardinality({k \\in Key : key[k] = 1}) < 2",
    );
    assert_ne!(bad, TLA, "the invariant replacement must match");
    let (bad_tlc, _) = run(&bad, CFG, &["-tlc", "-interp"], &[]);
    assert_eq!(bad_tlc.code, 12, "{}", bad_tlc.text());
    for tier in ["-interp", "-compile"] {
        let (r, _) = run(&bad, CFG, &[tier], &[]);
        assert_eq!(r.code, 12, "{tier}: {}", r.text());
        assert!(r.stdout.contains(AUGMENTED), "{tier}: {}", r.text());
        assert!(r.stdout.contains("Error: Invariant Inv is violated."), "{tier}: {}", r.text());
        assert!(states(&r.stdout) > 0, "{tier}: {}", r.text());
    }
    // A reachable deadlock: every map is saturated, so no action is enabled.
    let deadlock = CFG.replace("CHECK_DEADLOCK FALSE", "CHECK_DEADLOCK TRUE");
    let (tlc, _) = run(TLA, &deadlock, &["-tlc", "-interp"], &[]);
    assert_eq!(tlc.code, 11, "{}", tlc.text());
    for tier in ["-interp", "-compile"] {
        let (r, _) = run(TLA, &deadlock, &[tier], &[]);
        assert_eq!(r.code, 11, "{tier}: {}", r.text());
        assert!(r.stdout.contains(AUGMENTED), "{tier}: {}", r.text());
        assert!(r.stdout.contains("Error: Deadlock reached."), "{tier}: {}", r.text());
    }
}

#[test]
fn an_asymmetric_constant_is_not_added() {
    // `key[k1]` singles out k1, so Permutations(Key) is not proven; Key is
    // left out while the independent Val group is still certified.
    let tla = TLA
        .replace("CONSTANTS TxId, Key, Val", "CONSTANTS TxId, Key, Val, k1")
        .replace("    /\\ \\A v \\in Val : val[v] <= 1", "    /\\ \\A v \\in Val : val[v] <= 1\n    /\\ key[k1] <= 1");
    let cfg = CFG.replace("  Val = {v1, v2}", "  Val = {v1, v2}\n  k1 = k1");
    for tier in ["-interp", "-compile"] {
        let (r, _) = run(&tla, &cfg, &[tier, "-stats"], &[]);
        assert_eq!(r.code, 0, "{tier}: {}", r.text());
        assert!(
            r.stdout.contains("Optimizations: symmetry Permutations(TxId) x Permutations(Val) (certificate generated"),
            "{tier}: {}",
            r.text()
        );
        assert!(!r.stdout.contains("Permutations(Key)"), "{tier}: {}", r.text());
        assert!(r.text().contains("Key: proven Permutations(Key \\ {k1})"), "{tier}: {}", r.text());
        // 4 TxId classes x 2^3 Key states x 3 Val classes.
        assert_eq!(distinct(&r.stdout), 96, "{tier}: {}", r.text());
    }
}

#[test]
fn a_non_factorized_declared_symmetry_falls_back_to_it() {
    // A three-cycle generates C_3, not a disjoint product of full symmetric
    // groups: the declared group is kept verbatim and no superset is claimed.
    let tla = TLA.replace("CONSTANTS TxId, Key, Val", "CONSTANTS TxId, Key, Val, t1, t2, t3").replace(
        "TxIdSymmetric == Permutations(TxId)",
        "Rotate == { [t \\in TxId |-> IF t = t1 THEN t2 ELSE IF t = t2 THEN t3 ELSE t1],\n\
             \x20          [t \\in TxId |-> IF t = t1 THEN t3 ELSE IF t = t2 THEN t1 ELSE t2] }",
    );
    let cfg = CFG
        .replace("SYMMETRY TxIdSymmetric", "SYMMETRY Rotate")
        .replace("  Val = {v1, v2}", "  Val = {v1, v2}\n  t1 = t1\n  t2 = t2\n  t3 = t3");
    for tier in ["-interp", "-compile"] {
        let (r, _) = run(&tla, &cfg, &[tier, "-stats"], &[]);
        assert_eq!(r.code, 0, "{tier}: {}", r.text());
        assert!(r.stdout.contains("Optimizations: none applicable."), "{tier}: {}", r.text());
        assert!(!r.stdout.contains("(symmetry-reduced)"), "{tier}: {}", r.text());
        assert!(
            r.text().contains("not applied: the declared SYMMETRY is not a disjoint product of full symmetric groups"),
            "{tier}: {}",
            r.text()
        );
        // The declared C_3 orbit has the same classes as S_3 on this spec.
        assert_eq!(distinct(&r.stdout), 128, "{tier}: {}", r.text());
    }
}

#[test]
fn an_uncertifiable_superset_keeps_the_declared_group() {
    // ALIAS is outside the certified checking subset: the superset must not
    // be applied, and the declared group stays in force unchanged.
    let tla = TLA.replace("\n====\n", "\nAlias == [tx_ |-> tx]\n====\n");
    let cfg = format!("{CFG}ALIAS Alias\n");
    for tier in ["-interp", "-compile"] {
        let (r, _) = run(&tla, &cfg, &[tier, "-stats"], &[]);
        assert_eq!(r.code, 0, "{tier}: {}", r.text());
        assert!(r.stdout.contains("Optimizations: none applicable."), "{tier}: {}", r.text());
        assert!(!r.stdout.contains("(symmetry-reduced)"), "{tier}: {}", r.text());
        assert!(r.text().contains("not applied: no connected Lean certificate for the declared SYMMETRY superset"), "{tier}: {}", r.text());
        assert_eq!(distinct(&r.stdout), 128, "{tier}: {}", r.text());
    }
}
