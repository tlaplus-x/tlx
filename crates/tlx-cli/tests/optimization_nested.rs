//! Fixed nested allocation paths use the same connected certificate in every tier.
use std::time::Duration;

const SPEC: &str = include_str!("../../../proofs/ordered/Nested.tla");
const CFG: &str = include_str!("../../../proofs/ordered/Nested.cfg");

#[test]
fn nested_allocation_is_finite_and_preserves_concrete_failures() {
    for fails in [false, true] {
        let spec = if fails { SPEC.replace("records[a].ready \\in BOOLEAN", "records[a].ready = FALSE") } else { SPEC.to_owned() };
        let dir = tlx_testkit::TempDir::with_spec("nested-cli", &spec, CFG);
        let mut counts = None;
        for (tier, args, env) in tlx_testkit::cli::TIERS {
            let run = tlx_testkit::tlx_default!()
                .check("Nested.tla")
                .args(args)
                .args(["-optimize", "-noautosymmetry", "-maxmem", "32"])
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .env("TLX_PROOF_DIR", dir.join("proofs"))
                .dir(&dir)
                .timeout(Duration::from_secs(600))
                .run();
            assert_eq!(run.code, if fails { 12 } else { 0 }, "{tier}: {}", run.text());
            assert!(run.stdout.contains("ordered-allocation-projection"), "{tier}: {}", run.text());
            if fails {
                assert!(run.stdout.contains("frontier = 2"), "{}", run.text());
                assert!(run.stdout.contains("serial = 102"), "{}", run.text());
            } else {
                let normalized = run.stdout.replace(" (optimization-reduced).", ".");
                let result: Vec<String> = tlx_testkit::cli::counts(&normalized).into_iter().map(str::to_owned).collect();
                assert!(!result.is_empty(), "{}", run.text());
                if let Some(previous) = &counts {
                    assert_eq!(&result, previous);
                } else {
                    counts = Some(result);
                }
            }
        }
        for entry in std::fs::read_dir(dir.join("proofs")).unwrap() {
            let lean = std::fs::read_to_string(entry.unwrap().path().join("Optimization.lean")).unwrap();
            assert!(lean.contains("namespace TlxOptimization.GeneratedNested"));
            assert!(lean.contains("theorem runtime_key_equivalent"));
        }
    }
}

#[test]
fn nested_projection_preserves_deadlocks() {
    let spec = SPEC
        .replace("Reserve(a) ==", "Reserve(a) == /\\ ~records[a].ready")
        .replace("Reserve(a) \\/ Reset(a) \\/ (\\E b \\in Actors : Copy(a,b))", "Reserve(a)");
    let dir = tlx_testkit::TempDir::with_spec("nested-deadlock", &spec, &CFG.replace("FALSE", "TRUE"));
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("Nested.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry", "-maxmem", "32"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(600))
            .run();
        assert_eq!(run.code, 11, "{tier}: {}", run.text());
        assert!(run.stdout.contains("ordered-allocation-projection"), "{}", run.text());
        assert!(run.stdout.contains("frontier = 3"), "{}", run.text());
        assert!(run.stdout.contains("serial = 104"), "{}", run.text());
    }
}
