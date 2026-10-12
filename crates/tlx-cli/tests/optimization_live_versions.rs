//! Live-version certificates must follow actual payload feedback and source traces.
use std::time::Duration;
const SPEC: &str = include_str!("../../../proofs/ordered/LiveVersions.tla");
const CFG: &str = include_str!("../../../proofs/ordered/LiveVersions.cfg");

#[test]
fn immutable_history_collection_is_finite_and_retains_payloads() {
    let mut counts = None;
    for fails in [false, true] {
        let spec = if fails { SPEC.replace("observed \\in BOOLEAN", "observed = FALSE") } else { SPEC.to_owned() };
        let dir = tlx_testkit::TempDir::with_spec("live-versions", &spec, CFG);
        for (tier, args, env) in tlx_testkit::cli::TIERS {
            let run = tlx_testkit::tlx_default!()
                .check("LiveVersions.tla")
                .args(args)
                .args(["-optimize", "-noautosymmetry", "-maxmem", "32"])
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .dir(&dir)
                .timeout(Duration::from_secs(600))
                .run();
            assert_eq!(run.code, if fails { 12 } else { 0 }, "{tier}: {}", run.text());
            assert!(run.stdout.contains("versions.live-versions"), "{}", run.text());
            if fails {
                assert!(run.stdout.contains("observed = TRUE"), "{}", run.text());
                assert!(run.stdout.contains("frontier = 2"), "{}", run.text());
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
        for entry in std::fs::read_dir(dir.join(".tlx-proofs")).unwrap() {
            let lean = std::fs::read_to_string(entry.unwrap().path().join("Optimization.lean")).unwrap();
            assert!(lean.contains("namespace TlxOptimization.GeneratedLive"));
            assert!(lean.contains("theorem runtime_key_equivalent"));
        }
    }
}

#[test]
fn live_payload_guards_preserve_deadlocks() {
    let spec = SPEC
        .replace("Publish ==", "Publish == /\\ versions[frontier] = FALSE")
        .replace("Next == Publish \\/ (\\E a \\in Actors : Acquire(a) \\/ (\\E b \\in Actors : Share(a,b)))", "Next == Publish");
    let dir = tlx_testkit::TempDir::with_spec("live-deadlock", &spec, &CFG.replace("FALSE", "TRUE"));
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("LiveVersions.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry", "-maxmem", "32"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(600))
            .run();
        assert_eq!(run.code, 11, "{tier}: {}", run.text());
        assert!(run.stdout.contains("versions.live-versions"), "{}", run.text());
        assert!(run.stdout.contains("frontier = 2"), "{}", run.text());
    }
}
