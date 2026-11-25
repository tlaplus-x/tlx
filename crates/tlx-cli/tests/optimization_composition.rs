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
                .env("TLX_PROOF_DIR", dir.join("proofs"))
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
        assert!(!dir.join(".tlx-proofs").exists());
        for entry in std::fs::read_dir(dir.join("proofs")).unwrap() {
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
        .env("TLX_PROOF_DIR", dir.join("proofs"))
        .dir(&dir)
        .timeout(Duration::from_secs(600))
        .run();
    assert_eq!(run.code, 0, "{}", run.text());
    assert!(run.stdout.contains("27 distinct states found"), "{}", run.text());
    assert!(!run.stdout.contains("composed with symmetry"));
    let proof = std::fs::read_dir(dir.join("proofs")).unwrap().next().unwrap().unwrap().path().join("Optimization.lean");
    assert!(std::fs::read_to_string(proof).unwrap().contains("namespace TlxOptimization.GeneratedErasure"));
}

#[test]
fn ordered_projection_keeps_its_proof_when_composition_is_unsupported() {
    let spec = include_str!("../../../proofs/ordered/Nested.tla");
    let cfg = include_str!("../../../proofs/ordered/Nested.cfg");
    let dir = tlx_testkit::TempDir::with_spec("ordered-no-composition", spec, cfg);
    let run = tlx_testkit::tlx_default!()
        .check("Nested.tla")
        .args(["-optimize", "-interp"])
        .env("TLX_PROOF_DIR", dir.join("proofs"))
        .dir(&dir)
        .timeout(Duration::from_secs(600))
        .run();
    assert_eq!(run.code, 0, "{}", run.text());
    assert!(run.stdout.contains("13 distinct states found"), "{}", run.text());
    assert!(!run.stdout.contains("composed with symmetry"));
    let proof = std::fs::read_dir(dir.join("proofs")).unwrap().next().unwrap().unwrap().path().join("Optimization.lean");
    let lean = std::fs::read_to_string(proof).unwrap();
    assert!(lean.contains("namespace TlxOptimization.GeneratedNested"));
    assert!(!lean.contains("namespace TlxOptimization.GeneratedSymmetry"));
}

const MULTI_SPEC: &str = include_str!("../../../proofs/symmetry/ErasedMultiKey.tla");
const MULTI_CFG: &str = include_str!("../../../proofs/symmetry/ErasedMultiKey.cfg");

const ALL_TIERS: [(&str, &[&str], &[(&str, &str)]); 4] = [
    ("interpreter", &["-interp"], &[]),
    ("compiled IR", &["-compile"], &[("TLX_PRERUN_REUSE", "0"), ("TLX_NO_NATIVE", "1")]),
    ("cranelift JIT", &["-compile"], &[("TLX_PRERUN_REUSE", "0"), ("TLX_JIT", "only"), ("TLX_JIT_VERIFY", "1")]),
    ("C backend", &["-compile"], &[("TLX_PRERUN_REUSE", "0"), ("TLX_JIT", "0"), ("TLX_NATIVE_SYNC", "1")]),
];

#[test]
fn erased_equiv_composition_works_across_all_tiers_and_preserves_concrete_traces() {
    for (label, spec, cfg, code, states) in [
        ("safe", MULTI_SPEC.to_owned(), MULTI_CFG.to_owned(), 0, 19),
        ("failure", MULTI_SPEC.replace("Cardinality(msgs) <= 2", "Cardinality(msgs) < 2"), MULTI_CFG.to_owned(), 12, 0),
        ("deadlock", MULTI_SPEC.replace(" \\/ DropHead", ""), MULTI_CFG.replace("CHECK_DEADLOCK FALSE", "CHECK_DEADLOCK TRUE"), 11, 0),
    ] {
        let dir = tlx_testkit::TempDir::with_spec(&format!("erased-equiv-{label}"), &spec, &cfg);
        for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
            let proof_dir = dir.join(format!("proofs-{idx}"));
            let cache_dir = dir.join(format!("cache-{idx}"));
            let run = tlx_testkit::tlx_default!()
                .check("ErasedMultiKey.tla")
                .args(["-workers", "1", "-optimize", "-maxmem", "32"])
                .args(*args)
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .env("TLX_SYMMETRY_PARANOID", "1")
                .env("TLX_PROOF_DIR", &proof_dir)
                .env("TLX_CACHE", &cache_dir)
                .dir(&dir)
                .timeout(Duration::from_secs(600))
                .run();
            assert_eq!(run.code, code, "{label}/{tier}: {}", run.text());
            assert!(run.stdout.contains("composed with symmetry Permutations(Node)"), "{label}/{tier}: {}", run.text());
            assert!(run.stdout.contains("erasure/equivariant-symmetry composition certificate"), "{label}/{tier}: {}", run.text());
            if code == 0 {
                assert!(run.stdout.contains(&format!("{states} distinct state")), "{label}/{tier}: {}", run.text());
            } else {
                for ghost in ["audit =", "lastAction =", "stats ="] {
                    assert!(run.stdout.contains(ghost), "{label}/{tier} missing concrete ghost `{ghost}`:\n{}", run.text());
                }
            }
            for entry in std::fs::read_dir(&proof_dir).unwrap() {
                let lean = std::fs::read_to_string(entry.unwrap().path().join("Optimization.lean")).unwrap();
                assert!(lean.contains("namespace TlxOptimization.GeneratedErasedEquivSymmetry"));
                assert!(lean.contains("theorem erasure_certificate"));
                assert!(!lean.contains("sorry"));
            }
        }
    }

    // Disabling symmetry retains GeneratedErasure (100 distinct), while -tlc bypasses both (136 distinct).
    let dir = tlx_testkit::TempDir::with_spec("erased-equiv-modes", MULTI_SPEC, MULTI_CFG);
    let erasure_only = tlx_testkit::tlx_default!()
        .check("ErasedMultiKey.tla")
        .args(["-optimize", "-noautosymmetry", "-interp", "-workers", "1"])
        .env("TLX_PARANOID", "1")
        .env("TLX_PROOF_DIR", dir.join("proofs-erasure"))
        .dir(&dir)
        .timeout(Duration::from_secs(600))
        .run();
    assert_eq!(erasure_only.code, 0, "{}", erasure_only.text());
    assert!(erasure_only.stdout.contains("100 distinct states found"), "{}", erasure_only.text());
    assert!(!erasure_only.stdout.contains("composed with symmetry"));
    let lean = std::fs::read_to_string(
        std::fs::read_dir(dir.join("proofs-erasure")).unwrap().next().unwrap().unwrap().path().join("Optimization.lean"),
    )
    .unwrap();
    assert!(lean.contains("namespace TlxOptimization.GeneratedErasure"));

    let tlc_mode = tlx_testkit::tlx_default!()
        .check("ErasedMultiKey.tla")
        .args(["-optimize", "-tlc", "-interp", "-workers", "1"])
        .dir(&dir)
        .timeout(Duration::from_secs(600))
        .run();
    assert_eq!(tlc_mode.code, 0, "{}", tlc_mode.text());
    assert!(tlc_mode.stdout.contains("136 distinct states found"), "{}", tlc_mode.text());
    assert!(!tlc_mode.stdout.contains("Optimizations:"));
}

#[test]
fn erased_equiv_constrained_works_across_all_tiers_and_refuses_omitted_subscript() {
    let spec = r#"---- MODULE ErasedEquivConstrained ----
EXTENDS Naturals, FiniteSets
CONSTANTS Node, Cap, n1, n2, n3
DefaultNode == {n1, n2, n3}
DefaultCap == 2
VARIABLES msgs, audit
Init == msgs = {} /\ audit = [kind |-> "init", count |-> 0]
Next == \E p, q \in Node :
          /\ p # q
          /\ Cardinality(msgs) < Cap
          /\ [src |-> p, dst |-> q] \notin msgs
          /\ msgs' = msgs \cup {[src |-> p, dst |-> q]}
          /\ audit' = [kind |-> "send", count |-> Cardinality(msgs)]
Inv == Cardinality(msgs) <= Cap
InitProp == msgs = {}
StateLimit == Cardinality(msgs) < Cap
ActLimit == Cardinality(msgs') >= Cardinality(msgs)
ActPropSafe == [][Cardinality(msgs') >= Cardinality(msgs)]_msgs
ActPropMentionsAudit == [][Cardinality(msgs') >= Cardinality(msgs)]_<<msgs, audit>>
====
"#;
    let cfg = "\
INIT Init
NEXT Next
CONSTANTS
  n1 = n1
  n2 = n2
  n3 = n3
  Node <- DefaultNode
  Cap <- DefaultCap
INVARIANT Inv
PROPERTY InitProp
PROPERTY ActPropSafe
CONSTRAINT StateLimit
ACTION_CONSTRAINT ActLimit
CHECK_DEADLOCK FALSE
";
    let dir = tlx_testkit::TempDir::with_spec("erased-equiv-constrained", spec, cfg);
    let baseline = tlx_testkit::tlx_default!()
        .check("ErasedEquivConstrained.tla")
        .args(["-tlc", "-interp", "-workers", "1"])
        .dir(&dir)
        .timeout(Duration::from_secs(600))
        .run();
    assert_eq!(baseline.code, 0, "{}", baseline.text());

    for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
        let proof_dir = dir.join(format!("proofs-{idx}"));
        let cache_dir = dir.join(format!("cache-{idx}"));
        let run = tlx_testkit::tlx_default!()
            .check("ErasedEquivConstrained.tla")
            .args(["-workers", "1", "-optimize", "-maxmem", "32"])
            .args(*args)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .env("TLX_SYMMETRY_PARANOID", "1")
            .env("TLX_PROOF_DIR", &proof_dir)
            .env("TLX_CACHE", &cache_dir)
            .dir(&dir)
            .timeout(Duration::from_secs(600))
            .run();
        assert_eq!(run.code, 0, "{tier}: {}", run.text());
        assert!(run.stdout.contains("composed with symmetry Permutations(Node)"), "{tier}: {}", run.text());
        let lean =
            std::fs::read_to_string(std::fs::read_dir(&proof_dir).unwrap().next().unwrap().unwrap().path().join("Optimization.lean"))
                .unwrap();
        assert!(lean.contains("namespace TlxOptimization.GeneratedErasedEquivSymmetry"));
        assert!(lean.contains("theorem erasure_constrained_certificate"));
        assert!(lean.contains("theorem constrained_certificate"));
        assert!(!lean.contains("sorry"));
    }

    // Mentioning `audit` in `[][A]_<<msgs, audit>>` must refuse erasing `audit`.
    let bad_cfg = cfg.replace("ActPropSafe", "ActPropMentionsAudit");
    let bad_dir = tlx_testkit::TempDir::with_spec("erased-equiv-bad-sub", spec, &bad_cfg);
    let bad_run = tlx_testkit::tlx_default!()
        .check("ErasedEquivConstrained.tla")
        .args(["-optimize", "-noautosymmetry", "-interp", "-workers", "1"])
        .dir(&bad_dir)
        .timeout(Duration::from_secs(600))
        .run();
    assert_eq!(bad_run.code, 0, "{}", bad_run.text());
    assert!(!bad_run.stdout.contains("unobserved-state-projection"), "{}", bad_run.text());
}

#[test]
fn erasure_refuses_partial_overflow_multi_binding_and_prunes_iteratively() {
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
    let refusal_cases = [
        (
            "partial-div",
            "---- MODULE Refusal ----\nEXTENDS Integers\nVARIABLES x, h\nInit == x = 0 /\\ h = 0\nNext == x' = x /\\ h' = 1 \\div x\nInv == x = 0\n====\n",
            true,
        ),
        (
            "empty-head",
            "---- MODULE Refusal ----\nEXTENDS Naturals, Sequences\nVARIABLES x, h\nInit == x = 0 /\\ h = 0\nNext == x' = x /\\ h' = Head(<<>>)\nInv == x = 0\n====\n",
            true,
        ),
        (
            "overflow",
            "---- MODULE Refusal ----\nEXTENDS Naturals\nVARIABLES x, h\nInit == x = 0 /\\ h = 2147483647\nNext == x' = 1 - x /\\ h' = h + 1\nInv == x \\in {0, 1}\n====\n",
            true,
        ),
        (
            "multi-binding",
            "---- MODULE Refusal ----\nEXTENDS Naturals\nVARIABLES x, h\nInit == x = 0 /\\ h = 0\nNext == x' = 1 - x /\\ UNCHANGED h /\\ h' = 1\nInv == x \\in {0, 1}\n====\n",
            false,
        ),
        (
            "primed-rhs",
            "---- MODULE Refusal ----\nEXTENDS Naturals\nVARIABLES x, h\nInit == x = 0 /\\ h = 0\nNext == x' = 1 - x /\\ h' = x'\nInv == x \\in {0, 1}\n====\n",
            false,
        ),
    ];
    for (label, spec, expect_error) in refusal_cases {
        let dir = tlx_testkit::TempDir::with_spec(&format!("refuse-{label}"), spec, cfg);
        let run = tlx_testkit::tlx_default!()
            .check("Refusal.tla")
            .args(["-optimize", "-noautosymmetry", "-interp", "-workers", "1"])
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert!(!run.stdout.contains("unobserved-state-projection"), "{label} unexpectedly erased:\n{}", run.text());
        if expect_error {
            assert_ne!(run.code, 0, "{label} must preserve runtime error:\n{}", run.text());
        } else {
            assert_eq!(run.code, 0, "{label} should complete unreduced:\n{}", run.text());
        }
    }

    // Iterative pruning: `bad` fails static overflow totality (no upper guard on `bad + dep + 1`,
    // though alternating `x` keeps the concrete state space finite) and reads `dep`, so promoting
    // `bad` to live must transitively retain `dep`, while independent `good` is still erased.
    let prune_spec = r#"---- MODULE Prune ----
EXTENDS Naturals
VARIABLES x, bad, dep, good
Init == x = 0 /\ bad = 0 /\ dep = 0 /\ good = [v |-> 0, tag |-> "init"]
Next == /\ x' = 1 - x
        /\ bad' = IF x = 0 THEN bad + dep + 1 ELSE 0
        /\ dep' = x
        /\ good' = [v |-> x, tag |-> IF x = 0 THEN "a" ELSE "b"]
Inv == x \in {0, 1}
====
"#;
    let prune_dir = tlx_testkit::TempDir::with_spec("iterative-prune", prune_spec, cfg);
    for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
        let proof_dir = prune_dir.join(format!("proofs-{idx}"));
        let cache_dir = prune_dir.join(format!("cache-{idx}"));
        let run = tlx_testkit::tlx_default!()
            .check("Prune.tla")
            .args(["-optimize", "-noautosymmetry", "-workers", "1"])
            .args(*args)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .env("TLX_PROOF_DIR", &proof_dir)
            .env("TLX_CACHE", &cache_dir)
            .dir(&prune_dir)
            .timeout(Duration::from_secs(600))
            .run();
        assert_eq!(run.code, 0, "{tier}: {}", run.text());
        assert!(run.stdout.contains("unobserved-state-projection (good;"), "{tier}: {}", run.text());
        let lean =
            std::fs::read_to_string(std::fs::read_dir(&proof_dir).unwrap().next().unwrap().unwrap().path().join("Optimization.lean"))
                .unwrap();
        assert!(lean.contains("namespace TlxOptimization.GeneratedErasure"));
    }
}

#[test]
fn erasure_accounts_for_implies_writes_and_preserves_eval_error() {
    let spec = r#"---- MODULE P ----
EXTENDS Naturals
VARIABLES x, h
Init == x = 1 /\ h = 1
Next == \/ ((x >= 1 => x' = 2) /\ h' = x)
        \/ (UNCHANGED x /\ h' = <<1>>[h])
Inv == x \in {1, 2}
====
"#;
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
    let dir = tlx_testkit::TempDir::with_spec("erasure-implies-error", spec, cfg);
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let base = tlx_testkit::tlx_default!()
            .check("P.tla")
            .args(["-workers", "1", "-noautosymmetry"])
            .args(args)
            .envs(env.iter().copied())
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        let opt = tlx_testkit::tlx_default!()
            .check("P.tla")
            .args(["-workers", "1", "-noautosymmetry", "-optimize"])
            .args(args)
            .envs(env.iter().copied())
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(base.code, 75, "{tier} baseline: {}", base.text());
        assert_eq!(opt.code, 75, "{tier} optimized must preserve eval error: {}", opt.text());
        assert!(!opt.stdout.contains("unobserved-state-projection"), "{tier} unexpectedly erased h:\n{}", opt.text());
    }
}

#[test]
fn erased_equiv_orbit_fingerprint_is_stable_across_equal_set_representations() {
    let cases = [
        (
            "OrbitSize",
            r#"---- MODULE OrbitSize ----
EXTENDS Naturals
CONSTANT Node
VARIABLES x, y, audit
Init == \E p, q \in Node :
    /\ p # q
    /\ x = <<p, 1..2>>
    /\ y = <<q, 0>>
    /\ audit = FALSE
Next == /\ x' = <<x[1], {1, 2}>>
        /\ UNCHANGED y
        /\ audit' = TRUE
Inv == x[1] \in Node /\ y[1] \in Node
====
"#,
            "CONSTANT Node = {n1, n2}\nINIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n",
        ),
        (
            "Rep",
            r#"---- MODULE Rep ----
EXTENDS Naturals
CONSTANT Node
VARIABLES x, y, h
Init == \E p, q \in Node :
          /\ p # q
          /\ (x = <<p, 1..3>> \/ x = <<p, {1,2,3}>>)
          /\ y = <<q, {1,2}>>
          /\ h = 0
Next == UNCHANGED <<x, y, h>>
Inv == x[1] # y[1]
====
"#,
            "CONSTANT Node = {n1, n2}\nINIT Init\nNEXT Next\nINVARIANT Inv\n",
        ),
    ];
    for (name, spec, cfg) in cases {
        let dir = tlx_testkit::TempDir::with_spec(&format!("orbit-rep-{name}"), spec, cfg);
        for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
            let proof_dir = dir.join(format!("proofs-{idx}"));
            let cache_dir = dir.join(format!("cache-{idx}"));
            let run = tlx_testkit::tlx_default!()
                .check(format!("{name}.tla"))
                .args(["-workers", "1", "-optimize", "-maxmem", "32"])
                .args(*args)
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .env("TLX_SYMMETRY_PARANOID", "1")
                .env("TLX_PROOF_DIR", &proof_dir)
                .env("TLX_CACHE", &cache_dir)
                .dir(&dir)
                .timeout(Duration::from_secs(600))
                .run();
            assert_eq!(run.code, 0, "{name}/{tier}: {}", run.text());
            assert!(run.stdout.contains("1 distinct state"), "{name}/{tier} split orbit:\n{}", run.text());
            let lean =
                std::fs::read_to_string(std::fs::read_dir(&proof_dir).unwrap().next().unwrap().unwrap().path().join("Optimization.lean"))
                    .unwrap();
            assert!(lean.contains("namespace TlxOptimization.GeneratedErasedEquivSymmetry"));
        }
    }
}
