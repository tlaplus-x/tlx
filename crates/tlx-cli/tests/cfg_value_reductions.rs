//! End-to-end certified reductions over `.cfg` value assignments on zero-arity
//! definitions (`Def = value`) and fixed-atom stratified `k`-subset constants.
//! The equivariant symmetry families lower both; state projections stay refused
//! for such configurations.

use std::time::Duration;

const VALUE_TLA: &str = include_str!("../../../proofs/symmetry/CfgValueOverride.tla");
const VALUE_CFG: &str = include_str!("../../../proofs/symmetry/CfgValueOverride.cfg");
const SUBSET_TLA: &str = include_str!("../../../proofs/symmetry/FixedAtomSubsets.tla");
const SUBSET_CFG: &str = include_str!("../../../proofs/symmetry/FixedAtomSubsets.cfg");

fn run(spec: (&str, &str), module: &str, args: &[&str]) -> (tlx_testkit::cli::Run, tlx_testkit::TempDir) {
    let dir = tlx_testkit::TempDir::with_spec("cfg-value-reduction", spec.0, spec.1);
    let run = tlx_testkit::tlx_default!()
        .args(["check", &format!("{module}.tla")])
        .args(args)
        .env("TLX_PROOF_DIR", dir.join("proofs"))
        .dir(&dir)
        .timeout(Duration::from_secs(120))
        .run();
    (run, dir)
}

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

fn generated_certificate(dir: &tlx_testkit::TempDir) -> String {
    let path = std::fs::read_dir(dir.join("proofs"))
        .unwrap()
        .map(|e| e.unwrap().path().join("Optimization.lean"))
        .find(|p| p.exists())
        .expect("a generated certificate");
    std::fs::read_to_string(path).unwrap()
}

#[test]
fn cfg_value_definitions_certify_symmetry_in_every_tier() {
    for tier in ["-interp", "-compile"] {
        for env in [vec![], vec![("TLX_SYMMETRY_PARANOID", "1")]] {
            let dir = tlx_testkit::TempDir::with_spec("cfg-value-tier", VALUE_TLA, VALUE_CFG);
            let r = tlx_testkit::tlx_default!()
                .args(["check", "CfgValueOverride.tla", tier])
                .env("TLX_PROOF_DIR", dir.join("proofs"))
                .envs(env.iter().copied())
                .dir(&dir)
                .timeout(Duration::from_secs(120))
                .run();
            assert_eq!(r.code, 0, "{tier} {env:?}: {}", r.text());
            assert!(r.stdout.contains("Optimizations: symmetry Permutations(Proc) (certificate generated"), "{tier} {env:?}: {}", r.text());
            // 7 concrete states quotiented by S_3.
            assert_eq!(distinct(&r.stdout), 3, "{tier} {env:?}: {}", r.text());
        }
    }
    // The emitted certificate records the configured literals and their use
    // sites instead of running the shadowed bodies.
    let (r, dir) = run((VALUE_TLA, VALUE_CFG), "CfgValueOverride", &["-interp"]);
    assert_eq!(r.code, 0, "{}", r.text());
    let lean = generated_certificate(&dir);
    assert!(lean.contains("namespace TlxOptimization.GeneratedEquivSymmetry"), "{lean}");
    assert!(lean.contains("theorem certificate_with_overrides"), "{lean}");
    assert!(lean.contains(r#"Lit(Model(\"NoVal\"))"#), "missing model-value literal");
    assert!(lean.contains(r#"Lit(Set([Int(0),Int(1)]))"#), "missing set literal");
    assert!(lean.contains(r#"Lit(Str(\"idle\"))"#), "missing string literal");
    assert!(!lean.contains("sorry"), "{lean}");
}

#[test]
fn noautosymmetry_and_tlc_keep_the_value_bound_search() {
    for args in [vec!["-noautosymmetry", "-interp"], vec!["-tlc", "-interp"]] {
        let (r, _) = run((VALUE_TLA, VALUE_CFG), "CfgValueOverride", &args);
        assert_eq!(r.code, 0, "{args:?}: {}", r.text());
        assert_eq!(distinct(&r.stdout), 7, "{args:?}: {}", r.text());
        assert!(!r.stdout.contains("(symmetry-reduced)"), "{args:?}: {}", r.text());
    }
}

#[test]
fn fixed_atom_stratified_k_subsets_certify() {
    let (r, dir) = run((SUBSET_TLA, SUBSET_CFG), "FixedAtomSubsets", &["-interp"]);
    assert_eq!(r.code, 0, "{}", r.text());
    assert!(
        r.stdout.contains("Optimizations: symmetry Permutations(Value) x Permutations(Acceptor) (certificate generated"),
        "{}",
        r.text()
    );
    // 27 concrete states quotiented by S_2 x S_3.
    assert_eq!(distinct(&r.stdout), 6, "{}", r.text());
    let lean = generated_certificate(&dir);
    assert!(lean.contains("Expr.setMap"), "missing stratified setMap lowering: {lean}");
    assert!(!lean.contains("sorry"), "{lean}");
}

#[test]
fn state_projections_stay_refused_for_cfg_value_definitions() {
    // A zero-arity `Def = value` binding is certified by the symmetry families
    // only; a projection keeps the concrete search.
    let (r, _) = run((VALUE_TLA, VALUE_CFG), "CfgValueOverride", &["-interp", "-optimize", "-noautosymmetry"]);
    assert_eq!(r.code, 0, "{}", r.text());
    assert!(r.stdout.contains("Optimizations: none applicable."), "{}", r.text());
    assert_eq!(distinct(&r.stdout), 7, "{}", r.text());
}
