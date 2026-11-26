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

fn parse_distinct(stdout: &str) -> u64 {
    for line in stdout.lines() {
        if let Some(idx) = line.find(" distinct states found") {
            let prefix = line[..idx].trim_end();
            if let Some(num) = prefix.rsplit(|c: char| !c.is_ascii_digit()).next() {
                if let Ok(v) = num.parse::<u64>() {
                    return v;
                }
            }
        }
    }
    panic!("missing distinct state count in:\n{stdout}");
}

fn read_single_lean(proof_dir: &std::path::Path) -> String {
    let entries: Vec<_> = std::fs::read_dir(proof_dir).unwrap().map(|e| e.unwrap().path().join("Optimization.lean")).collect();
    assert_eq!(entries.len(), 1, "expected 1 certificate under {}, found {entries:?}", proof_dir.display());
    std::fs::read_to_string(&entries[0]).unwrap()
}

fn trace_lines(stdout: &str) -> Vec<&str> {
    stdout.lines().filter(|l| l.starts_with("State ") || l.starts_with("/\\ ")).collect()
}

#[test]
fn field_sym_record_and_parallel_maps_compose_across_all_tiers() {
    let record_spec = r#"---- MODULE FieldSymRec ----
EXTENDS Integers
CONSTANT Actors
VARIABLE r, done
Init == r = [a \in Actors |-> [mode |-> "idle", buf |-> 0]] /\ done = FALSE
Start(a) == \E v \in {0, 1, 2} :
              /\ r[a].mode = "idle"
              /\ r' = [r EXCEPT ![a].mode = "busy", ![a].buf = v]
              /\ UNCHANGED done
Finish(a) == /\ r[a].mode = "busy"
             /\ r[a].buf >= 0
             /\ r' = [r EXCEPT ![a].mode = "idle"]
             /\ done' = (done \/ r[a].buf = 2)
Next == \E a \in Actors : Start(a) \/ Finish(a)
Inv == (\A a \in Actors : r[a].mode \in {"idle", "busy"} /\ (r[a].mode = "busy" => r[a].buf \in {0, 1, 2})) /\ done \in BOOLEAN
====
"#;
    let parallel_spec = r#"---- MODULE FieldSymPar ----
EXTENDS Integers
CONSTANT Actors
VARIABLES pc, buf, done
Init == pc = [a \in Actors |-> "idle"] /\ buf = [a \in Actors |-> 0] /\ done = FALSE
Start(a) == \E v \in {0, 1, 2} :
              /\ pc[a] = "idle"
              /\ pc' = [pc EXCEPT ![a] = "busy"]
              /\ buf' = [buf EXCEPT ![a] = v]
              /\ UNCHANGED done
Finish(a) == /\ pc[a] = "busy"
             /\ buf[a] >= 0
             /\ pc' = [pc EXCEPT ![a] = "idle"]
             /\ done' = (done \/ buf[a] = 2)
             /\ UNCHANGED buf
Next == \E a \in Actors : Start(a) \/ Finish(a)
Inv == (\A a \in Actors : pc[a] \in {"idle", "busy"} /\ (pc[a] = "busy" => buf[a] \in {0, 1, 2})) /\ done \in BOOLEAN
====
"#;
    let cfg = "INIT Init\nNEXT Next\nCONSTANT Actors = {a1, a2, a3}\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
    for (name, spec) in [("FieldSymRec", record_spec), ("FieldSymPar", parallel_spec)] {
        let dir = tlx_testkit::TempDir::with_spec(&format!("field-sym-{name}"), spec, cfg);
        let file = format!("{name}.tla");
        let proj_only = tlx_testkit::tlx_default!()
            .check(&file)
            .args(["-interp", "-workers", "1", "-optimize", "-noautosymmetry"])
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(proj_only.code, 0, "{name} proj-only: {}", proj_only.text());
        let proj_distinct = parse_distinct(&proj_only.stdout);

        let sym_only =
            tlx_testkit::tlx_default!().check(&file).args(["-interp", "-workers", "1"]).dir(&dir).timeout(Duration::from_secs(60)).run();
        assert_eq!(sym_only.code, 0, "{name} sym-only: {}", sym_only.text());
        let sym_distinct = parse_distinct(&sym_only.stdout);

        for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
            let proof_dir = dir.join(format!("proofs-{idx}"));
            let cache_dir = dir.join(format!("cache-{idx}"));
            let run = tlx_testkit::tlx_default!()
                .check(&file)
                .args(["-workers", "1", "-optimize", "-maxmem", "32"])
                .args(*args)
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .env("TLX_SYMMETRY_PARANOID", "1")
                .env("TLX_PROOF_DIR", &proof_dir)
                .env("TLX_CACHE", &cache_dir)
                .dir(&dir)
                .timeout(Duration::from_secs(120))
                .run();
            assert_eq!(run.code, 0, "{name}/{tier}: {}", run.text());
            assert!(run.stdout.contains("phase-field-projection"), "{name}/{tier}: {}", run.text());
            assert!(run.stdout.contains("composed with symmetry Permutations(Actors)"), "{name}/{tier}: {}", run.text());
            assert!(run.stdout.contains("phase-field/equivariant-symmetry composition certificate"), "{name}/{tier}: {}", run.text());
            let composed = parse_distinct(&run.stdout);
            assert!(
                composed < proj_distinct && composed < sym_distinct,
                "{name}/{tier}: expected composed {composed} < min(proj={proj_distinct}, sym={sym_distinct})"
            );
            let lean = read_single_lean(&proof_dir);
            for expected in [
                "namespace TlxOptimization.GeneratedFieldSymmetry",
                "theorem field_certificate",
                "theorem symmetry_certificate",
                "theorem certificate",
                "theorem orbit_key_equivalent",
            ] {
                assert!(lean.contains(expected), "{name}/{tier}: missing `{expected}`");
            }
            assert!(!lean.contains("sorry"), "{name}/{tier}");
        }
    }

    // Concrete safety violation and deadlock traces preserve real unmasked field values across all tiers.
    let bad_spec = record_spec.replace("done \\in BOOLEAN", "~done");
    let bad_dir = tlx_testkit::TempDir::with_spec("field-sym-cex", &bad_spec, cfg);
    for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
        let run = tlx_testkit::tlx_default!()
            .check("FieldSymRec.tla")
            .args(["-workers", "1", "-optimize"])
            .args(*args)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .env("TLX_SYMMETRY_PARANOID", "1")
            .env("TLX_PROOF_DIR", bad_dir.join(format!("proofs-{idx}")))
            .env("TLX_CACHE", bad_dir.join(format!("cache-{idx}")))
            .dir(&bad_dir)
            .timeout(Duration::from_secs(120))
            .run();
        assert_eq!(run.code, 12, "cex/{tier}: {}", run.text());
        assert!(run.stdout.contains("composed with symmetry Permutations(Actors)"), "cex/{tier}: {}", run.text());
        assert!(run.stdout.contains("buf |-> 2"), "cex/{tier} must retain concrete unmasked buf = 2:\n{}", run.text());
        assert!(run.stdout.contains("done = TRUE"), "cex/{tier}: {}", run.text());
    }

    let dl_spec = r#"---- MODULE FieldSymDeadlock ----
EXTENDS Integers
CONSTANT Actors
VARIABLE r
Init == r = [a \in Actors |-> [mode |-> "idle", buf |-> 0]]
Start(a) == \E v \in {0, 1} :
              /\ r[a].mode = "idle"
              /\ r' = [r EXCEPT ![a].mode = "busy", ![a].buf = v]
Stop(a) == /\ r[a].mode = "busy"
           /\ r[a].buf = 1
           /\ r' = [r EXCEPT ![a].mode = "done"]
Next == \E a \in Actors : Start(a) \/ Stop(a)
Inv == \A a \in Actors : r[a].mode \in {"idle", "busy", "done"}
====
"#;
    let dl_cfg = "INIT Init\nNEXT Next\nCONSTANT Actors = {a1, a2}\nINVARIANT Inv\nCHECK_DEADLOCK TRUE\n";
    let dl_dir = tlx_testkit::TempDir::with_spec("field-sym-dl", dl_spec, dl_cfg);
    for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
        let run = tlx_testkit::tlx_default!()
            .check("FieldSymDeadlock.tla")
            .args(["-workers", "1", "-optimize"])
            .args(*args)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .env("TLX_SYMMETRY_PARANOID", "1")
            .env("TLX_PROOF_DIR", dl_dir.join(format!("proofs-{idx}")))
            .env("TLX_CACHE", dl_dir.join(format!("cache-{idx}")))
            .dir(&dl_dir)
            .timeout(Duration::from_secs(120))
            .run();
        assert_eq!(run.code, 11, "dl/{tier}: {}", run.text());
        assert!(run.stdout.contains("composed with symmetry Permutations(Actors)"), "dl/{tier}: {}", run.text());
        assert!(run.stdout.contains("Deadlock reached"), "dl/{tier}: {}", run.text());
    }
}

#[test]
fn field_sym_dead_field_holding_moved_keys_uses_key_free_sentinel_across_all_tiers() {
    // Dead field `partner` ranges strictly over moved symmetric keys `Actors`.
    // Installing a moved key (e.g. `a1`) as the dead-field sentinel would break
    // equivariance and split orbits; `project_state_with_sym_keys` must pick a
    // key-free sentinel so `GeneratedFieldSymmetry` certifies and merges orbits.
    let spec = r#"---- MODULE MovedKeySentinel ----
EXTENDS Integers
CONSTANT Actors
VARIABLES pc, partner, seen
Init == /\ pc = [a \in Actors |-> "idle"]
        /\ partner = [a \in Actors |-> a]
        /\ seen = FALSE
Start(a) == \E other \in Actors :
              /\ pc[a] = "idle"
              /\ pc' = [pc EXCEPT ![a] = "busy"]
              /\ partner' = [partner EXCEPT ![a] = other]
              /\ UNCHANGED seen
Finish(a) == /\ pc[a] = "busy"
             /\ partner[a] \in Actors
             /\ pc' = [pc EXCEPT ![a] = "idle"]
             /\ seen' = (seen \/ partner[a] = a)
             /\ UNCHANGED partner
Next == \E a \in Actors : Start(a) \/ Finish(a)
Inv == /\ pc \in [Actors -> {"idle", "busy"}]
       /\ seen \in BOOLEAN
       /\ \A a \in Actors : pc[a] = "busy" => partner[a] \in Actors
====
"#;
    let cfg = "INIT Init\nNEXT Next\nCONSTANT Actors = {a1, a2, a3}\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
    let dir = tlx_testkit::TempDir::with_spec("field-sym-moved-key", spec, cfg);

    let proj_only = tlx_testkit::tlx_default!()
        .check("MovedKeySentinel.tla")
        .args(["-interp", "-workers", "1", "-optimize", "-noautosymmetry"])
        .dir(&dir)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(proj_only.code, 0, "proj-only: {}", proj_only.text());
    let proj_distinct = parse_distinct(&proj_only.stdout);

    let sym_only = tlx_testkit::tlx_default!()
        .check("MovedKeySentinel.tla")
        .args(["-interp", "-workers", "1"])
        .dir(&dir)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(sym_only.code, 0, "sym-only: {}", sym_only.text());
    let sym_distinct = parse_distinct(&sym_only.stdout);

    for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
        let proof_dir = dir.join(format!("proofs-{idx}"));
        let cache_dir = dir.join(format!("cache-{idx}"));
        let run = tlx_testkit::tlx_default!()
            .check("MovedKeySentinel.tla")
            .args(["-workers", "1", "-optimize", "-maxmem", "32"])
            .args(*args)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .env("TLX_SYMMETRY_PARANOID", "1")
            .env("TLX_PROOF_DIR", &proof_dir)
            .env("TLX_CACHE", &cache_dir)
            .dir(&dir)
            .timeout(Duration::from_secs(120))
            .run();
        assert_eq!(run.code, 0, "{tier}: {}", run.text());
        assert!(run.stdout.contains("phase-field-projection (partner[*]"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("composed with symmetry Permutations(Actors)"), "{tier}: {}", run.text());
        let composed = parse_distinct(&run.stdout);
        assert!(
            composed < proj_distinct && composed < sym_distinct,
            "{tier}: expected composed {composed} < min(proj={proj_distinct}, sym={sym_distinct})"
        );
        let lean = read_single_lean(&proof_dir);
        assert!(lean.contains("namespace TlxOptimization.GeneratedFieldSymmetry"), "{tier}");
        assert!(!lean.contains("sorry"), "{tier}");
    }
}

#[test]
fn field_sym_constrained_action_checks_and_action_prop_violation_across_all_tiers() {
    let spec = r#"---- MODULE FieldSymConstrained ----
EXTENDS Naturals
CONSTANTS Actors, MaxRounds, a1, a2, a3
DefaultActors == {a1, a2, a3}
DefaultMaxRounds == 2
VARIABLE r, count
Init == r = [a \in Actors |-> [mode |-> "idle", buf |-> 0]] /\ count = 0
Start == \E a \in Actors :
           /\ r[a].mode = "idle"
           /\ count < MaxRounds
           /\ \E v \in {0, 1} : r' = [r EXCEPT ![a].mode = "busy", ![a].buf = v]
           /\ count' = count + 1
Finish == \E a \in Actors :
            /\ r[a].mode = "busy"
            /\ r[a].buf >= 0
            /\ r' = [r EXCEPT ![a].mode = "idle"]
            /\ count' = count
Next == Start \/ Finish
Inv == \A a \in Actors : r[a].mode \in {"idle", "busy"} /\ count <= MaxRounds
InitProp == count = 0
StateLimit == count <= MaxRounds
ActLimit == \A a \in Actors : r[a].mode \in {"idle", "busy"}
ActPropOk == [][ \A a \in Actors : r'[a].mode \in {"idle", "busy"} ]_count
ActPropBad == [][ count' <= 1 ]_count
====
"#;
    let ok_cfg = "\
INIT Init
NEXT Next
CONSTANTS
  a1 = a1
  a2 = a2
  a3 = a3
  Actors <- DefaultActors
  MaxRounds <- DefaultMaxRounds
INVARIANT Inv
PROPERTY InitProp
PROPERTY ActPropOk
CONSTRAINT StateLimit
ACTION_CONSTRAINT ActLimit
CHECK_DEADLOCK FALSE
";
    let dir = tlx_testkit::TempDir::with_spec("field-sym-constrained", spec, ok_cfg);
    let proj_only = tlx_testkit::tlx_default!()
        .check("FieldSymConstrained.tla")
        .args(["-interp", "-workers", "1", "-optimize", "-noautosymmetry"])
        .dir(&dir)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(proj_only.code, 0, "proj-only: {}", proj_only.text());
    let proj_distinct = parse_distinct(&proj_only.stdout);

    let sym_only = tlx_testkit::tlx_default!()
        .check("FieldSymConstrained.tla")
        .args(["-interp", "-workers", "1"])
        .dir(&dir)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(sym_only.code, 0, "sym-only: {}", sym_only.text());
    let sym_distinct = parse_distinct(&sym_only.stdout);

    for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
        let proof_dir = dir.join(format!("proofs-{idx}"));
        let cache_dir = dir.join(format!("cache-{idx}"));
        let run = tlx_testkit::tlx_default!()
            .check("FieldSymConstrained.tla")
            .args(["-workers", "1", "-optimize", "-maxmem", "32"])
            .args(*args)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .env("TLX_SYMMETRY_PARANOID", "1")
            .env("TLX_PROOF_DIR", &proof_dir)
            .env("TLX_CACHE", &cache_dir)
            .dir(&dir)
            .timeout(Duration::from_secs(120))
            .run();
        assert_eq!(run.code, 0, "{tier}: {}", run.text());
        assert!(run.stdout.contains("composed with symmetry Permutations(Actors)"), "{tier}: {}", run.text());
        let composed = parse_distinct(&run.stdout);
        assert!(
            composed < proj_distinct && composed < sym_distinct,
            "{tier}: expected composed {composed} < min(proj={proj_distinct}, sym={sym_distinct})"
        );
        let lean = read_single_lean(&proof_dir);
        for expected in [
            "namespace TlxOptimization.GeneratedFieldSymmetry",
            "theorem field_constrained_certificate",
            "theorem symmetry_constrained_certificate",
            "theorem constrained_certificate",
            "theorem const_subst_bindings_match",
            "theorem const_subst_constrained_sound",
        ] {
            assert!(lean.contains(expected), "{tier}: missing `{expected}`");
        }
        assert!(!lean.contains("sorry"), "{tier}");
    }

    // Violated `[][A]_sub` action property lifts concrete counterexample matching `-tlc`.
    let bad_cfg = ok_cfg.replace("ActPropOk", "ActPropBad");
    let bad_dir = tlx_testkit::TempDir::with_spec("field-sym-act-bad", spec, &bad_cfg);
    let tlc = tlx_testkit::tlx_default!()
        .check("FieldSymConstrained.tla")
        .args(["-tlc", "-interp", "-workers", "1"])
        .dir(&bad_dir)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(tlc.code, 13, "tlc: {}", tlc.text());
    for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
        let run = tlx_testkit::tlx_default!()
            .check("FieldSymConstrained.tla")
            .args(["-workers", "1", "-optimize"])
            .args(*args)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .env("TLX_SYMMETRY_PARANOID", "1")
            .env("TLX_PROOF_DIR", bad_dir.join(format!("proofs-{idx}")))
            .env("TLX_CACHE", bad_dir.join(format!("cache-{idx}")))
            .dir(&bad_dir)
            .timeout(Duration::from_secs(120))
            .run();
        assert_eq!(run.code, 13, "act-bad/{tier}: {}", run.text());
        assert!(run.stdout.contains("composed with symmetry Permutations(Actors)"), "act-bad/{tier}: {}", run.text());
        assert!(run.stdout.contains("Action property ActPropBad is violated."), "act-bad/{tier}: {}", run.text());
        assert_eq!(trace_lines(&run.stdout).len(), trace_lines(&tlc.stdout).len(), "act-bad/{tier}: {}", run.text());
    }
}

#[test]
fn threshold_sym_scalar_and_map_counters_compose_across_all_tiers() {
    let spec = r#"---- MODULE ThreshSym ----
EXTENDS Naturals
CONSTANT Actor
VARIABLES phase, step, retries, failures
Init == /\ phase = "idle"
        /\ step = 0
        /\ retries = 0
        /\ failures = [a \in Actor |-> 0]
Start == /\ phase = "idle"
         /\ phase' = "busy"
         /\ UNCHANGED <<step, retries, failures>>
Retry == /\ phase = "busy"
         /\ step < 5
         /\ step' = step + 1
         /\ retries' = retries + 1
         /\ phase' = IF retries >= 1 THEN "escalated" ELSE "busy"
         /\ UNCHANGED failures
Fail == \E a \in Actor :
          /\ phase \in {"busy", "escalated"}
          /\ step < 5
          /\ step' = step + 1
          /\ failures' = [failures EXCEPT ![a] = @ + 1]
          /\ phase' = IF failures[a] >= 1 THEN "degraded" ELSE phase
          /\ UNCHANGED retries
Tick == \E a \in Actor :
          /\ phase = "degraded"
          /\ step < 5
          /\ step' = step + 1
          /\ failures' = [failures EXCEPT ![a] = @ + 1]
          /\ UNCHANGED <<phase, retries>>
Reset == /\ phase' = "idle"
         /\ retries' = 0
         /\ failures' = [a \in Actor |-> 0]
         /\ UNCHANGED step
Next == Start \/ Retry \/ Fail \/ Tick \/ Reset
TypeOK == /\ phase \in {"idle", "busy", "escalated", "degraded"}
          /\ step \in Nat
          /\ retries \in Nat
          /\ failures \in [Actor -> Nat]
EscCheck == (phase = "escalated") => (retries >= 2)
DegCheck == (phase = "degraded") => (\E a \in Actor : failures[a] >= 2)
StateLimit == step <= 5
ActLimit == phase' \in {"idle", "busy", "escalated", "degraded"}
ActPropOk == [][ phase' \in {"idle", "busy", "escalated", "degraded"} ]_<<phase, step>>
ActPropBad == [][ phase' # "degraded" ]_<<phase, step>>
====
"#;
    for (mode, extra_cfg) in
        [("unconstrained", ""), ("constrained", "CONSTRAINT StateLimit\nACTION_CONSTRAINT ActLimit\nPROPERTY ActPropOk\n")]
    {
        let cfg = format!(
            "INIT Init\nNEXT Next\nCONSTANT Actor = {{a1, a2, a3}}\nINVARIANTS\n  TypeOK\n  EscCheck\n  DegCheck\n{extra_cfg}CHECK_DEADLOCK TRUE\n"
        );
        let dir = tlx_testkit::TempDir::with_spec(&format!("thresh-sym-{mode}"), spec, &cfg);

        let proj_only = tlx_testkit::tlx_default!()
            .check("ThreshSym.tla")
            .args(["-interp", "-workers", "1", "-optimize", "-noautosymmetry"])
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(proj_only.code, 0, "{mode} proj-only: {}", proj_only.text());
        let proj_distinct = parse_distinct(&proj_only.stdout);

        let sym_only = tlx_testkit::tlx_default!()
            .check("ThreshSym.tla")
            .args(["-interp", "-workers", "1"])
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(sym_only.code, 0, "{mode} sym-only: {}", sym_only.text());
        let sym_distinct = parse_distinct(&sym_only.stdout);

        for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
            let proof_dir = dir.join(format!("proofs-{idx}"));
            let cache_dir = dir.join(format!("cache-{idx}"));
            let run = tlx_testkit::tlx_default!()
                .check("ThreshSym.tla")
                .args(["-workers", "1", "-optimize", "-maxmem", "32"])
                .args(*args)
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .env("TLX_SYMMETRY_PARANOID", "1")
                .env("TLX_PROOF_DIR", &proof_dir)
                .env("TLX_CACHE", &cache_dir)
                .dir(&dir)
                .timeout(Duration::from_secs(120))
                .run();
            assert_eq!(run.code, 0, "{mode}/{tier}: {}", run.text());
            assert!(run.stdout.contains("threshold-counter-projection"), "{mode}/{tier}: {}", run.text());
            assert!(run.stdout.contains("composed with symmetry Permutations(Actor)"), "{mode}/{tier}: {}", run.text());
            assert!(run.stdout.contains("threshold-counter/equivariant-symmetry composition certificate"), "{mode}/{tier}: {}", run.text());
            let composed = parse_distinct(&run.stdout);
            assert!(
                composed < proj_distinct && composed < sym_distinct,
                "{mode}/{tier}: expected composed {composed} < min(proj={proj_distinct}, sym={sym_distinct})"
            );
            let lean = read_single_lean(&proof_dir);
            for expected in [
                "namespace TlxOptimization.GeneratedThresholdSymmetry",
                "theorem threshold_certificate",
                "theorem symmetry_certificate",
                "theorem certificate",
                "theorem orbit_key_equivalent",
            ] {
                assert!(lean.contains(expected), "{mode}/{tier}: missing `{expected}`");
            }
            if mode == "constrained" {
                for expected in [
                    "theorem threshold_constrained_certificate",
                    "theorem symmetry_constrained_certificate",
                    "theorem constrained_certificate",
                ] {
                    assert!(lean.contains(expected), "{mode}/{tier}: missing `{expected}`");
                }
            }
            assert!(!lean.contains("sorry"), "{mode}/{tier}");
        }
    }

    // Concrete un-capped safety violation, action-property violation, and deadlock traces across all 4 tiers.
    let cex_spec = r#"---- MODULE ThreshSymCex ----
EXTENDS Naturals
CONSTANT Actor
VARIABLES pos, fails
Init == pos = 0 /\ fails = [a \in Actor |-> 0]
Step == \E a \in Actor :
          /\ pos < 4
          /\ pos' = pos + 1
          /\ fails' = [fails EXCEPT ![a] = @ + 1]
Linger == \E a \in Actor :
            /\ pos < 4
            /\ pos' = pos + 1
            /\ fails' = [fails EXCEPT ![a] = @ + 4]
Next == Step \/ Linger
TypeOK == pos \in 0..4 /\ fails \in [Actor -> Nat]
Guard == \A a \in Actor : (fails[a] < 2) \/ (fails[a] >= 2)
NotFour == pos # 4
ActBad == [][ pos' < 4 ]_pos
====
"#;
    let cex_cfg = "INIT Init\nNEXT Next\nCONSTANT Actor = {a1, a2}\nINVARIANTS\n  TypeOK\n  Guard\n  NotFour\nCHECK_DEADLOCK FALSE\n";
    let cex_dir = tlx_testkit::TempDir::with_spec("thresh-sym-cex", cex_spec, cex_cfg);
    for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
        let run = tlx_testkit::tlx_default!()
            .check("ThreshSymCex.tla")
            .args(["-workers", "1", "-optimize"])
            .args(*args)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .env("TLX_SYMMETRY_PARANOID", "1")
            .env("TLX_PROOF_DIR", cex_dir.join(format!("proofs-{idx}")))
            .env("TLX_CACHE", cex_dir.join(format!("cache-{idx}")))
            .dir(&cex_dir)
            .timeout(Duration::from_secs(120))
            .run();
        assert_eq!(run.code, 12, "cex/{tier}: {}", run.text());
        assert!(run.stdout.contains("composed with symmetry Permutations(Actor)"), "cex/{tier}: {}", run.text());
        assert!(run.stdout.contains("Invariant NotFour is violated"), "cex/{tier}: {}", run.text());
        // Must retain concrete un-capped counter value >= 4 (cap is 2).
        assert!(
            run.stdout.contains(" :> 4") || run.stdout.contains(" :> 5") || run.stdout.contains(" :> 8") || run.stdout.contains(" :> 16"),
            "cex/{tier} must reconstruct un-capped concrete counter value:\n{}",
            run.text()
        );
    }

    let act_bad_cfg =
        "INIT Init\nNEXT Next\nCONSTANT Actor = {a1, a2}\nINVARIANTS\n  TypeOK\n  Guard\nPROPERTY ActBad\nCHECK_DEADLOCK FALSE\n";
    let act_dir = tlx_testkit::TempDir::with_spec("thresh-sym-act-bad", cex_spec, act_bad_cfg);
    for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
        let run = tlx_testkit::tlx_default!()
            .check("ThreshSymCex.tla")
            .args(["-workers", "1", "-optimize"])
            .args(*args)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .env("TLX_SYMMETRY_PARANOID", "1")
            .env("TLX_PROOF_DIR", act_dir.join(format!("proofs-{idx}")))
            .env("TLX_CACHE", act_dir.join(format!("cache-{idx}")))
            .dir(&act_dir)
            .timeout(Duration::from_secs(120))
            .run();
        assert_eq!(run.code, 13, "act-bad/{tier}: {}", run.text());
        assert!(run.stdout.contains("composed with symmetry Permutations(Actor)"), "act-bad/{tier}: {}", run.text());
        assert!(run.stdout.contains("Action property ActBad is violated."), "act-bad/{tier}: {}", run.text());
    }

    let dl_cfg = "INIT Init\nNEXT Next\nCONSTANT Actor = {a1, a2}\nINVARIANTS\n  TypeOK\n  Guard\nCHECK_DEADLOCK TRUE\n";
    let dl_dir = tlx_testkit::TempDir::with_spec("thresh-sym-dl", cex_spec, dl_cfg);
    for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
        let run = tlx_testkit::tlx_default!()
            .check("ThreshSymCex.tla")
            .args(["-workers", "1", "-optimize"])
            .args(*args)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .env("TLX_SYMMETRY_PARANOID", "1")
            .env("TLX_PROOF_DIR", dl_dir.join(format!("proofs-{idx}")))
            .env("TLX_CACHE", dl_dir.join(format!("cache-{idx}")))
            .dir(&dl_dir)
            .timeout(Duration::from_secs(120))
            .run();
        assert_eq!(run.code, 11, "dl/{tier}: {}", run.text());
        assert!(run.stdout.contains("composed with symmetry Permutations(Actor)"), "dl/{tier}: {}", run.text());
        assert!(run.stdout.contains("Deadlock reached"), "dl/{tier}: {}", run.text());
        assert!(run.stdout.contains("pos = 4"), "dl/{tier}: {}", run.text());
    }
}

#[test]
fn uncomposable_projection_does_not_displace_stronger_certified_symmetry() {
    // Unique-witness `CHOOSE` over `Actors` is certified by `ChooseSymCertificate`
    // (default automatic symmetry), while `FieldSymCertificate` / `ThresholdSymCertificate`
    // decline `CHOOSE` over keys. With 4 symmetric actors, certified symmetry beats
    // the standalone uncomposable projection on the bounded probe, so `-optimize`
    // must keep `Permutations(Actors)` rather than regressing to projection-only.
    let field_choose_spec = r#"---- MODULE UncomposableField ----
EXTENDS Integers
CONSTANT Actors
VARIABLES pc, buf, picked
Init == /\ pc = [a \in Actors |-> "idle"]
        /\ buf = [a \in Actors |-> 0]
        /\ picked = [a \in Actors |-> FALSE]
Start(a) == \E v \in {0, 1} :
              /\ pc[a] = "idle"
              /\ (CHOOSE x \in Actors : x = a) = a
              /\ pc' = [pc EXCEPT ![a] = "busy"]
              /\ buf' = [buf EXCEPT ![a] = v]
              /\ picked' = [k \in Actors |-> k = a]
Finish(a) == /\ pc[a] = "busy"
             /\ buf[a] >= 0
             /\ pc' = [pc EXCEPT ![a] = "idle"]
             /\ UNCHANGED <<buf, picked>>
Next == \E a \in Actors : Start(a) \/ Finish(a)
Inv == /\ pc \in [Actors -> {"idle", "busy"}]
       /\ picked \in [Actors -> BOOLEAN]
       /\ \A a \in Actors : pc[a] = "busy" => buf[a] \in {0, 1}
====
"#;
    let cfg = "INIT Init\nNEXT Next\nCONSTANT Actors = {a1, a2, a3, a4}\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
    let dir = tlx_testkit::TempDir::with_spec("uncomposable-field-vs-sym", field_choose_spec, cfg);
    let sym_only = tlx_testkit::tlx_default!()
        .check("UncomposableField.tla")
        .args(["-interp", "-workers", "1"])
        .dir(&dir)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(sym_only.code, 0, "sym-only: {}", sym_only.text());
    assert!(sym_only.stdout.contains("symmetry Permutations(Actors)"), "sym-only: {}", sym_only.text());
    let sym_distinct = parse_distinct(&sym_only.stdout);

    let opt = tlx_testkit::tlx_default!()
        .check("UncomposableField.tla")
        .args(["-interp", "-workers", "1", "-optimize"])
        .env("TLX_PARANOID", "1")
        .env("TLX_SYMMETRY_PARANOID", "1")
        .dir(&dir)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(opt.code, 0, "opt: {}", opt.text());
    let opt_distinct = parse_distinct(&opt.stdout);
    assert!(
        opt_distinct <= sym_distinct,
        "uncomposable projection must not regress past certified symmetry ({opt_distinct} > {sym_distinct}):\n{}",
        opt.text()
    );
    assert!(opt.stdout.contains("symmetry Permutations(Actors)"), "opt: {}", opt.text());

    // Uncomposable `threshold-counter-projection` with `ChooseSym` symmetry:
    // 4 actors with boolean state + bounded counter (cap 2, reaches 3) so
    // `Permutations(Actors)` beats standalone threshold saturation and must not be displaced.
    let thresh_choose_spec = r#"---- MODULE UncomposableThresh ----
EXTENDS Naturals
CONSTANT Actors
VARIABLES st, cnt
Init == st = [a \in Actors |-> 0] /\ cnt = 0
Flip(a) == /\ (CHOOSE x \in Actors : x = a) = a
           /\ st' = [st EXCEPT ![a] = 1 - @]
           /\ cnt' = IF cnt < 3 THEN cnt + 1 ELSE 3
Next == \E a \in Actors : Flip(a)
Inv == st \in [Actors -> {0, 1}] /\ cnt \in Nat /\ (cnt < 2 \/ cnt >= 2)
====
"#;
    let t_dir = tlx_testkit::TempDir::with_spec("uncomposable-thresh-vs-sym", thresh_choose_spec, cfg);
    let t_sym = tlx_testkit::tlx_default!()
        .check("UncomposableThresh.tla")
        .args(["-interp", "-workers", "1"])
        .dir(&t_dir)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(t_sym.code, 0, "t-sym: {}", t_sym.text());
    assert!(t_sym.stdout.contains("symmetry Permutations(Actors)"), "t-sym: {}", t_sym.text());
    let t_sym_distinct = parse_distinct(&t_sym.stdout);

    let t_opt = tlx_testkit::tlx_default!()
        .check("UncomposableThresh.tla")
        .args(["-interp", "-workers", "1", "-optimize"])
        .env("TLX_PARANOID", "1")
        .env("TLX_SYMMETRY_PARANOID", "1")
        .dir(&t_dir)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(t_opt.code, 0, "t-opt: {}", t_opt.text());
    let t_opt_distinct = parse_distinct(&t_opt.stdout);
    assert!(
        t_opt_distinct <= t_sym_distinct,
        "uncomposable threshold projection must not regress past certified symmetry ({t_opt_distinct} > {t_sym_distinct}):\n{}",
        t_opt.text()
    );
    assert!(t_opt.stdout.contains("symmetry Permutations(Actors)"), "t-opt: {}", t_opt.text());
}

#[test]
fn field_sym_witness_bound_records_live_field_reads_and_reproduces_violation() {
    // `Finish(a)` reads `r[a].buf` ONLY inside a witness bound domain `{r[a].buf}`
    // (not in the guard terms or writes). `lower_step_cases` must record that read
    // in `readsActor` so `FieldRule.enabled` supplies the live buffer value rather
    // than the dead-field sentinel 0.
    let spec = r#"---- MODULE FieldSymBoundRead ----
EXTENDS Integers
CONSTANT Actors
VARIABLES r, done
Init == r = [a \in Actors |-> [mode |-> "idle", buf |-> 0]] /\ done = FALSE
Start(a) == \E v \in {0, 2} :
              /\ r[a].mode = "idle"
              /\ r' = [r EXCEPT ![a].mode = "busy", ![a].buf = v]
              /\ UNCHANGED done
Finish(a) == /\ r[a].mode = "busy"
             /\ \E seen \in {r[a].buf} :
                  /\ r' = [r EXCEPT ![a].mode = "idle"]
                  /\ done' = (done \/ seen = 2)
Next == \E a \in Actors : Start(a) \/ Finish(a)
Inv == (\A a \in Actors : r[a].mode \in {"idle", "busy"} /\ (r[a].mode = "busy" => r[a].buf \in {0, 2})) /\ ~done
====
"#;
    let cfg = "INIT Init\nNEXT Next\nCONSTANT Actors = {a1, a2}\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
    let dir = tlx_testkit::TempDir::with_spec("field-sym-bound-read", spec, cfg);
    for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
        let proof_dir = dir.join(format!("proofs-{idx}"));
        let cache_dir = dir.join(format!("cache-{idx}"));
        let run = tlx_testkit::tlx_default!()
            .check("FieldSymBoundRead.tla")
            .args(["-workers", "1", "-optimize"])
            .args(*args)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .env("TLX_SYMMETRY_PARANOID", "1")
            .env("TLX_PROOF_DIR", &proof_dir)
            .env("TLX_CACHE", &cache_dir)
            .dir(&dir)
            .timeout(Duration::from_secs(120))
            .run();
        assert_eq!(run.code, 12, "{tier}: {}", run.text());
        assert!(run.stdout.contains("composed with symmetry Permutations(Actors)"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("Invariant Inv is violated"), "{tier}: {}", run.text());
        let lean = read_single_lean(&proof_dir);
        assert!(lean.contains("namespace TlxOptimization.GeneratedFieldSymmetry"), "{tier}");
        let reads_actor_block = lean
            .split("def readsActor (b : Fin BranchCount) (f : Fin FieldCount) : Bool :=")
            .nth(1)
            .and_then(|s| s.split("def readsGlobal").next())
            .expect("readsActor table");
        assert!(
            reads_actor_block.contains("=> true"),
            "{tier}: witness-bound live field read must be recorded in readsActor:\n{reads_actor_block}"
        );
    }
}

#[test]
fn overlapping_except_at_declines_composed_certificate_and_preserves_violation() {
    // 1. Overlapping `@` in a retained core map (`[marked EXCEPT ![a] = TRUE, ![b] = ~@]`):
    //    when `a = b`, sequential EXCEPT semantics leaves `marked[a] = FALSE`, violating
    //    `BusyMarked` on the first step. `ThresholdSym` must decline composition rather
    //    than rewriting `@` against the original `marked`.
    let overlap_thresh = r#"---- MODULE OverlapThresh ----
EXTENDS Naturals
CONSTANT Actors
VARIABLES phase, marked, retries
Init == phase = "idle" /\ marked = [a \in Actors |-> FALSE] /\ retries = 0
Step == \E a, b \in Actors :
          /\ phase = "idle"
          /\ phase' = "busy"
          /\ marked' = [marked EXCEPT ![a] = TRUE, ![b] = ~@]
          /\ retries' = retries + 1
Tick == /\ phase = "busy"
        /\ retries' = retries + 1
        /\ UNCHANGED <<phase, marked>>
Reset == /\ phase = "busy"
         /\ retries >= 2
         /\ phase' = "idle"
         /\ retries' = 0
         /\ marked' = [a \in Actors |-> FALSE]
Next == Step \/ Tick \/ Reset
TypeOK == phase \in {"idle", "busy"} /\ marked \in [Actors -> BOOLEAN] /\ retries \in Nat
BusyMarked == (phase = "busy") => (\E a \in Actors : marked[a])
====
"#;
    let cfg = "INIT Init\nNEXT Next\nCONSTANT Actors = {a1, a2}\nINVARIANTS\n  TypeOK\n  BusyMarked\nCHECK_DEADLOCK FALSE\n";
    let dir = tlx_testkit::TempDir::with_spec("overlap-except-thresh", overlap_thresh, cfg);
    for (idx, (tier, args, env)) in [ALL_TIERS[0], ALL_TIERS[2]].iter().enumerate() {
        let proof_dir = dir.join(format!("proofs-{idx}"));
        let cache_dir = dir.join(format!("cache-{idx}"));
        let run = tlx_testkit::tlx_default!()
            .check("OverlapThresh.tla")
            .args(["-workers", "1", "-optimize"])
            .args(*args)
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .env("TLX_SYMMETRY_PARANOID", "1")
            .env("TLX_PROOF_DIR", &proof_dir)
            .env("TLX_CACHE", &cache_dir)
            .dir(&dir)
            .timeout(Duration::from_secs(120))
            .run();
        assert_eq!(run.code, 12, "thresh/{tier}: {}", run.text());
        assert!(run.stdout.contains("Invariant BusyMarked is violated"), "thresh/{tier}: {}", run.text());
        for entry in std::fs::read_dir(&proof_dir).unwrap() {
            let lean = std::fs::read_to_string(entry.unwrap().path().join("Optimization.lean")).unwrap();
            assert!(
                !lean.contains("namespace TlxOptimization.GeneratedThresholdSymmetry"),
                "thresh/{tier}: overlapping EXCEPT @ must not emit GeneratedThresholdSymmetry"
            );
        }
    }

    // 2. Overlapping `@` on a symmetric counter map (`[fails EXCEPT ![a] = @ + 1, ![b] = @ + 1]`):
    //    must also decline `GeneratedThresholdSymmetry`.
    let overlap_counter = r#"---- MODULE OverlapCounter ----
EXTENDS Naturals
CONSTANT Actors
VARIABLES step, fails
Init == step = 0 /\ fails = [a \in Actors |-> 0]
Bump == \E a, b \in Actors :
          /\ step < 3
          /\ step' = step + 1
          /\ fails' = [fails EXCEPT ![a] = @ + 1, ![b] = @ + 1]
Next == Bump
TypeOK == step \in 0..3 /\ fails \in [Actors -> Nat]
Guard == \A a \in Actors : (fails[a] < 2) \/ (fails[a] >= 2)
NotTwoInOneStep == (step = 1) => (\A a \in Actors : fails[a] < 2)
====
"#;
    let c_cfg =
        "INIT Init\nNEXT Next\nCONSTANT Actors = {a1, a2}\nINVARIANTS\n  TypeOK\n  Guard\n  NotTwoInOneStep\nCHECK_DEADLOCK FALSE\n";
    let c_dir = tlx_testkit::TempDir::with_spec("overlap-except-counter", overlap_counter, c_cfg);
    let c_proof = c_dir.join("proofs");
    let c_run = tlx_testkit::tlx_default!()
        .check("OverlapCounter.tla")
        .args(["-interp", "-workers", "1", "-optimize"])
        .env("TLX_PARANOID", "1")
        .env("TLX_SYMMETRY_PARANOID", "1")
        .env("TLX_PROOF_DIR", &c_proof)
        .dir(&c_dir)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(c_run.code, 12, "counter: {}", c_run.text());
    assert!(c_run.stdout.contains("Invariant NotTwoInOneStep is violated"), "counter: {}", c_run.text());
    for entry in std::fs::read_dir(&c_proof).unwrap() {
        let lean = std::fs::read_to_string(entry.unwrap().path().join("Optimization.lean")).unwrap();
        assert!(
            !lean.contains("namespace TlxOptimization.GeneratedThresholdSymmetry"),
            "counter: overlapping EXCEPT @ on counter map must decline GeneratedThresholdSymmetry"
        );
    }

    // 3. Overlapping `@` in a phase-field spec (`[marked EXCEPT ![a] = TRUE, ![b] = ~@]`):
    //    must decline `GeneratedFieldSymmetry` and preserve the concrete violation.
    let overlap_field = r#"---- MODULE OverlapField ----
EXTENDS Integers
CONSTANT Actors
VARIABLES r, marked
Init == r = [a \in Actors |-> [mode |-> "idle", buf |-> 0]] /\ marked = [a \in Actors |-> FALSE]
Start == \E a, b \in Actors :
           \E v \in {0, 1} :
             /\ r[a].mode = "idle"
             /\ r' = [r EXCEPT ![a].mode = "busy", ![a].buf = v]
             /\ marked' = [marked EXCEPT ![a] = TRUE, ![b] = ~@]
Finish == \E a \in Actors :
            /\ r[a].mode = "busy"
            /\ r[a].buf >= 0
            /\ r' = [r EXCEPT ![a].mode = "idle"]
            /\ UNCHANGED marked
Next == Start \/ Finish
TypeOK == (\A a \in Actors : r[a].mode \in {"idle", "busy"}) /\ marked \in [Actors -> BOOLEAN]
BusyMarked == (\E a \in Actors : r[a].mode = "busy") => (\E a \in Actors : marked[a])
====
"#;
    let f_dir = tlx_testkit::TempDir::with_spec("overlap-except-field", overlap_field, cfg);
    let f_proof = f_dir.join("proofs");
    let f_run = tlx_testkit::tlx_default!()
        .check("OverlapField.tla")
        .args(["-interp", "-workers", "1", "-optimize"])
        .env("TLX_PARANOID", "1")
        .env("TLX_SYMMETRY_PARANOID", "1")
        .env("TLX_PROOF_DIR", &f_proof)
        .dir(&f_dir)
        .timeout(Duration::from_secs(60))
        .run();
    assert_eq!(f_run.code, 12, "field: {}", f_run.text());
    assert!(f_run.stdout.contains("Invariant BusyMarked is violated"), "field: {}", f_run.text());
    if f_proof.exists() {
        for entry in std::fs::read_dir(&f_proof).unwrap() {
            let lean = std::fs::read_to_string(entry.unwrap().path().join("Optimization.lean")).unwrap();
            assert!(
                !lean.contains("namespace TlxOptimization.GeneratedFieldSymmetry"),
                "field: overlapping EXCEPT @ must decline GeneratedFieldSymmetry"
            );
        }
    }
}
