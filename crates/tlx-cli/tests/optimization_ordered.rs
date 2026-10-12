//! General allocation families and immutable version maps, across execution tiers.
use std::time::Duration;

const SPEC: &str = r#"---- MODULE Allocation ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
VARIABLE frontier, stored, versions, bit
Init == /\ frontier = 1 /\ stored = [slots |-> <<[tag |-> 0]>>]
        /\ versions = [t \in {frontier} |-> FALSE] /\ bit = FALSE
Next == /\ frontier' = frontier + 1
        /\ stored' = [slots |-> <<[tag |-> frontier]>>]
        /\ versions' = versions @@ [t \in {frontier + 1} |-> ~bit]
        /\ bit' = ~bit
Inv == /\ stored.slots[1].tag < frontier /\ versions[frontier] = bit
====
"#;
const CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";

#[test]
fn unbounded_versions_complete_and_emit_the_actual_plan() {
    let dir = tlx_testkit::TempDir::with_spec("ordered-cli", SPEC, CFG);
    let mut counts = None;
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("Allocation.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry", "-maxmem", "16"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{tier}: {}", run.text());
        assert!(run.stdout.contains("ordered-allocation-projection"), "{tier}: {}", run.text());
        let normalized = run.stdout.replace(" (optimization-reduced).", ".");
        let result: Vec<String> = tlx_testkit::cli::counts(&normalized).into_iter().map(str::to_owned).collect();
        assert!(!result.is_empty(), "{}", run.text());
        if let Some(previous) = &counts {
            assert_eq!(&result, previous);
        } else {
            counts = Some(result);
        }
    }
    for entry in std::fs::read_dir(dir.join(".tlx-proofs")).unwrap() {
        let lean = std::fs::read_to_string(entry.unwrap().path().join("Optimization.lean")).unwrap();
        assert!(lean.contains("def structuralOrderPlan"));
        assert!(lean.contains("OrderedHistory"));
        assert!(lean.contains("theorem retained_lookup"));
        assert!(lean.contains("No model-level Certificate is constructed"));
    }
}

#[test]
fn reduced_failures_keep_concrete_allocation_values() {
    let source = SPEC.replace("versions[frontier] = bit", "versions[frontier] = FALSE");
    let dir = tlx_testkit::TempDir::with_spec("ordered-trace", &source, CFG);
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("Allocation.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry", "-tool", "-maxmem", "16"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 12, "{tier}: {}", run.text());
        assert!(run.stdout.contains("ordered-allocation-projection"), "{}", run.text());
        assert!(run.stdout.contains("frontier = 2"), "{}", run.text());
    }
}

#[test]
fn compatibility_bypasses_order_projection() {
    let source = SPEC.replace("Next == /\\", "Next == frontier < 4 /\\");
    let dir = tlx_testkit::TempDir::with_spec("ordered-compat", &source, CFG);
    for flags in [["-tlc", "-optimize"], ["-optimize", "-tlc"]] {
        let run = tlx_testkit::tlx_default!()
            .check("Allocation.tla")
            .args(flags)
            .args(["-interp", "-noautosymmetry"])
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{}", run.text());
        assert!(run.stdout.contains("4 distinct states found"), "{}", run.text());
        assert!(!run.stdout.contains("ordered-allocation-projection"));
        assert!(!dir.join(".tlx-proofs").exists());
    }
}

#[test]
#[ignore = "requires the pinned local MongoDB external corpus; allows 600 seconds"]
fn external_mongodb_incarnations_match_independent_tlc_view() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let source =
        std::fs::read_to_string(root.join("third_party/external/mongo/Sharding/TxnsCollectionIncarnation/TxnsCollectionIncarnation.tla"))
            .unwrap();
    let cfg = include_str!("fixtures/optimization_ordered/Unbounded.cfg");
    let dir = tlx_testkit::TempDir::with_spec("ordered-mongo", &source, cfg);
    let oracle = include_str!("fixtures/optimization_ordered/GeneralIncarnation.tlc.out");
    for mode in ["-interp", "-compile"] {
        let run = tlx_testkit::tlx_default!()
            .check("TxnsCollectionIncarnation.tla")
            .args([mode, "-optimize", "-noautosymmetry", "-workers", "1", "-maxmem", "512"])
            .dir(&dir)
            .timeout(Duration::from_secs(600))
            .run();
        assert_eq!(run.code, 0, "{mode}: {}", run.text());
        assert!(run.stdout.contains("ordered-allocation-projection"), "{}", run.text());
        assert_eq!(
            tlx_testkit::cli::counts(&run.stdout.replace(" (optimization-reduced).", ".")),
            tlx_testkit::cli::counts(oracle),
            "{mode}: {}",
            run.text()
        );
    }
}

#[test]
fn ordered_keys_compose_with_model_value_symmetry() {
    let source = SPEC
        .replace("VARIABLE frontier", "CONSTANT Nodes\nVARIABLE owner, frontier")
        .replace("Init ==", "Init == owner \\in Nodes /\\")
        .replace("Next ==", "Next == UNCHANGED owner /\\")
        .replace("Inv ==", "Group == Permutations(Nodes)\nInv == owner \\in Nodes /\\");
    let cfg = format!("{CFG}CONSTANT Nodes = {{a, b}}\nSYMMETRY Group\n");
    let dir = tlx_testkit::TempDir::with_spec("ordered-symmetry", &source, &cfg);
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("Allocation.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry", "-maxmem", "16"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{tier}: {}", run.text());
        assert!(run.stdout.contains("ordered-allocation-projection"), "{}", run.text());
        assert!(run.stdout.contains("composed with symmetry Group"), "{}", run.text());
        assert!(run.stdout.contains("3 distinct states found"), "{}", run.text());
    }
}
