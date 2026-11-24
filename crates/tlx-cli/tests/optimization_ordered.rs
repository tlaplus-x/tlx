//! Certified scalar allocation and refusal of candidates without certificates.
use std::time::Duration;

const SPEC: &str = r#"---- MODULE Allocation ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
VARIABLE frontier, bit
Init == /\ frontier = 1 /\ bit = FALSE
Next == /\ frontier' = frontier + 1
        /\ bit' = IF frontier = 1 THEN bit ELSE ~bit
Inv == /\ frontier \in Nat /\ bit \in BOOLEAN
====
"#;
const CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";

#[test]
fn certified_scalar_allocation_completes_and_emits_connected_proof() {
    let dir = tlx_testkit::TempDir::with_spec("ordered-cli", SPEC, CFG);
    let mut counts = None;
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("Allocation.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry", "-maxmem", "16"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .env("TLX_PROOF_DIR", dir.join("proofs"))
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
    assert!(!dir.join(".tlx-proofs").exists());
    for entry in std::fs::read_dir(dir.join("proofs")).unwrap() {
        let lean = std::fs::read_to_string(entry.unwrap().path().join("Optimization.lean")).unwrap();
        assert!(lean.contains("def structuralOrderPlan"));
        assert!(lean.contains("namespace TlxOptimization.GeneratedOrdered"));
        assert!(lean.contains("theorem retained_lookup"));
        assert!(lean.contains("theorem certificate : Certificate (before sem) (after sem) (project sem)"));
        assert!(!lean.contains("No model-level Certificate is constructed"));
    }
}

#[test]
fn reduced_failures_keep_concrete_allocation_values() {
    let source = SPEC.replace("bit \\in BOOLEAN", "bit = FALSE");
    let dir = tlx_testkit::TempDir::with_spec("ordered-trace", &source, CFG);
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("Allocation.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry", "-tool", "-maxmem", "16"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .env("TLX_PROOF_DIR", dir.join("proofs"))
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 12, "{tier}: {}", run.text());
        assert!(run.stdout.contains("ordered-allocation-projection"), "{}", run.text());
        assert!(run.stdout.contains("frontier = 3"), "{}", run.text());
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
            .env("TLX_PROOF_DIR", dir.join("proofs"))
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{}", run.text());
        assert!(run.stdout.contains("4 distinct states found"), "{}", run.text());
        assert!(!run.stdout.contains("ordered-allocation-projection"));
        assert!(!dir.join("proofs").exists());
        assert!(!dir.join(".tlx-proofs").exists());
    }
}

#[test]
#[ignore = "requires the pinned local MongoDB external corpus; analysis only"]
fn external_mongodb_is_refused_until_its_reduction_has_a_certificate() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let source =
        std::fs::read_to_string(root.join("third_party/external/mongo/Sharding/TxnsCollectionIncarnation/TxnsCollectionIncarnation.tla"))
            .unwrap();
    let cfg = include_str!("fixtures/optimization_ordered/Unbounded.cfg");
    let dir = tlx_testkit::TempDir::with_spec("ordered-mongo", &source, cfg);
    let program = tlx_sema::Program::load(&dir.join("TxnsCollectionIncarnation.tla"), &[]).unwrap();
    let ip = tlx_eval::Interp::new(program, tlx_front::cfg::parse_cfg(cfg).unwrap()).unwrap();
    let mut model = tlx_eval::model::InterpModel::new(ip).unwrap();
    assert!(model.project_state().is_none());
    assert!(model.projection_certificate().is_none());
}

#[test]
fn ordered_symmetry_composition_requires_its_own_certificate() {
    let source = SPEC
        .replace("VARIABLE frontier", "CONSTANT Nodes\nVARIABLE owner, frontier")
        .replace("Init ==", "Init == owner \\in Nodes /\\")
        .replace("Next ==", "Next == UNCHANGED owner /\\")
        .replace("Inv ==", "Group == Permutations(Nodes)\nInv == owner \\in Nodes /\\");
    let cfg = format!("{CFG}CONSTANT Nodes = {{a, b}}\nSYMMETRY Group\n");
    let dir = tlx_testkit::TempDir::with_spec("ordered-symmetry", &source, &cfg);
    // The source clock is unbounded: test refusal without exploring it.
    let program = tlx_sema::Program::load(&dir.join("Allocation.tla"), &[]).unwrap();
    let ip = tlx_eval::Interp::new(program, tlx_front::cfg::parse_cfg(&cfg).unwrap()).unwrap();
    let mut model = tlx_eval::model::InterpModel::new(ip).unwrap();
    assert!(model.project_state().is_none());
    assert!(model.projection_certificate().is_none());
}

#[test]
fn cardinality_must_not_hide_an_allocation_anchor() {
    let spec = include_str!("fixtures/optimization_ordered/HiddenAnchor.tla");
    let dir = tlx_testkit::TempDir::with_spec("ordered-hidden-anchor", spec, CFG);
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("HiddenAnchor.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry", "-maxmem", "16"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .env("TLX_PROOF_DIR", dir.join("proofs"))
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 12, "{tier}: {}", run.text());
        assert!(run.stdout.contains("ordered-allocation-projection"), "{}", run.text());
        assert!(run.stdout.contains("parametric ordered-allocation rule-IR certificate"), "{}", run.text());
        assert!(run.stdout.contains("clock = 3"), "{}", run.text());
        assert!(run.stdout.contains("bad = TRUE"), "{}", run.text());
    }
}

#[test]
fn constrained_ordered_rule_emits_constrained_certificate() {
    let dir = tlx_testkit::TempDir::with_spec("ordered-constraint", SPEC, &format!("{CFG}CONSTRAINT Inv\n"));
    let program = tlx_sema::Program::load(&dir.join("Allocation.tla"), &[]).unwrap();
    let cfg = tlx_front::cfg::parse_cfg(&format!("{CFG}CONSTRAINT Inv\n")).unwrap();
    let mut model = tlx_eval::model::InterpModel::new(tlx_eval::Interp::new(program, cfg).unwrap()).unwrap();
    let (rule, _) = model.project_state().expect("ordered projection with state CONSTRAINT");
    assert_eq!(rule, "ordered-allocation-projection");
    let cert = model.projection_certificate().unwrap();
    assert!(cert.contains("namespace TlxOptimization.GeneratedOrdered"));
    assert!(cert.contains("theorem constrained_certificate"));
}

#[test]
fn unsupported_certificate_observations_refuse_the_ordered_rule() {
    let source = SPEC.replace("====", "ActLimit == bit' \\in BOOLEAN\n====");
    let cfg_str = format!("{CFG}ACTION_CONSTRAINT ActLimit\n");
    let dir = tlx_testkit::TempDir::with_spec("ordered-action-constraint", &source, &cfg_str);
    let program = tlx_sema::Program::load(&dir.join("Allocation.tla"), &[]).unwrap();
    let cfg = tlx_front::cfg::parse_cfg(&cfg_str).unwrap();
    let mut model = tlx_eval::model::InterpModel::new(tlx_eval::Interp::new(program, cfg).unwrap()).unwrap();
    assert!(model.project_state().is_none());
    assert!(model.projection_certificate().is_none());
}
