//! The emitted composition certificate must describe the installed projected key.
use std::time::Duration;
const SPEC: &str = include_str!("../../../proofs/symmetry/Erased.tla");
const CFG: &str = include_str!("../../../proofs/symmetry/Erased.cfg");

#[test]
fn erasure_precedes_symmetry_and_preserves_concrete_traces() {
    for (label, spec, cfg, code, states) in [
        ("safe", SPEC.to_owned(), CFG.to_owned(), 0, 10),
        ("hidden-loops", SPEC.to_owned(), CFG.replace("Limit = 2", "Limit = 0").replace("FALSE", "TRUE"), 0, 1),
        ("failure", SPEC.replace("pc[p].n <= Limit", "pc[p].n < Limit"), CFG.to_owned(), 12, 0),
        ("deadlock", SPEC.replace(" \\/ Swap \\/ Forget", ""), CFG.replace("FALSE", "TRUE"), 11, 0),
    ] {
        let dir = tlx_testkit::TempDir::with_spec(label, &spec, &cfg);
        for (tier, args, env) in tlx_testkit::cli::TIERS {
            let run = tlx_testkit::tlx_default!()
                .check("Erased.tla")
                .args(args)
                .args(["-optimize", "-maxmem", "32"])
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .env("TLX_SYMMETRY_PARANOID", "1")
                .dir(&dir)
                .timeout(Duration::from_secs(600))
                .run();
            assert_eq!(run.code, code, "{label}/{tier}: {}", run.text());
            assert!(run.stdout.contains("composed with symmetry"), "{}", run.text());
            assert!(run.stdout.contains("erasure/keyed-symmetry composition certificate"), "{}", run.text());
            if code == 0 {
                assert!(run.stdout.contains(&format!("{states} distinct state")), "{}", run.text());
            } else {
                assert!(run.stdout.contains("snapshot ="), "{}", run.text());
                assert!(run.stdout.contains("previous ="), "{}", run.text());
            }
        }
        for entry in std::fs::read_dir(dir.join(".tlx-proofs")).unwrap() {
            let lean = std::fs::read_to_string(entry.unwrap().path().join("Optimization.lean")).unwrap();
            assert!(lean.contains("namespace TlxOptimization.GeneratedErasedSymmetry"));
            assert!(lean.contains("theorem erasure_certificate"));
        }
    }
}

#[test]
fn disabling_symmetry_retains_only_the_erasure_certificate() {
    let dir = tlx_testkit::TempDir::with_spec("compose-disabled", SPEC, CFG);
    let run = tlx_testkit::tlx_default!()
        .check("Erased.tla")
        .args(["-optimize", "-noautosymmetry", "-interp"])
        .dir(&dir)
        .timeout(Duration::from_secs(600))
        .run();
    assert_eq!(run.code, 0, "{}", run.text());
    assert!(run.stdout.contains("27 distinct states found"), "{}", run.text());
    assert!(!run.stdout.contains("composed with symmetry"));
    let proof = std::fs::read_dir(dir.join(".tlx-proofs")).unwrap().next().unwrap().unwrap().path().join("Optimization.lean");
    assert!(std::fs::read_to_string(proof).unwrap().contains("namespace TlxOptimization.GeneratedErasure"));
}

#[test]
fn ordered_projection_keeps_its_proof_when_composition_is_unsupported() {
    let spec = include_str!("../../../proofs/ordered/Nested.tla");
    let cfg = include_str!("../../../proofs/ordered/Nested.cfg");
    let dir = tlx_testkit::TempDir::with_spec("ordered-no-composition", spec, cfg);
    let run =
        tlx_testkit::tlx_default!().check("Nested.tla").args(["-optimize", "-interp"]).dir(&dir).timeout(Duration::from_secs(600)).run();
    assert_eq!(run.code, 0, "{}", run.text());
    assert!(run.stdout.contains("13 distinct states found"), "{}", run.text());
    assert!(!run.stdout.contains("composed with symmetry"));
    let proof = std::fs::read_dir(dir.join(".tlx-proofs")).unwrap().next().unwrap().unwrap().path().join("Optimization.lean");
    let lean = std::fs::read_to_string(proof).unwrap();
    assert!(lean.contains("namespace TlxOptimization.GeneratedNested"));
    assert!(!lean.contains("namespace TlxOptimization.GeneratedSymmetry"));
}
