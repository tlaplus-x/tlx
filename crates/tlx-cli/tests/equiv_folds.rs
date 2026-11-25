//! End-to-end cross-tier paranoid regression tests for commutative-associative
//! finite folds and index-ordered sequence folds in `EquivSymCertificate` and
//! composed `ErasedEquivCertificate`.

use std::time::Duration;

const ALL_TIERS: [(&str, &[&str], &[(&str, &str)]); 4] = [
    ("interpreter", &["-interp"], &[]),
    ("compiled IR", &["-compile"], &[("TLX_PRERUN_REUSE", "0"), ("TLX_NO_NATIVE", "1")]),
    ("cranelift JIT", &["-compile"], &[("TLX_PRERUN_REUSE", "0"), ("TLX_JIT", "only"), ("TLX_JIT_VERIFY", "1")]),
    ("C backend", &["-compile"], &[("TLX_PRERUN_REUSE", "0"), ("TLX_JIT", "0"), ("TLX_NATIVE_SYNC", "1")]),
];

fn read_single_lean(proof_dir: &std::path::Path) -> String {
    let entries: Vec<_> = std::fs::read_dir(proof_dir).unwrap().map(|e| e.unwrap().path()).collect();
    assert_eq!(entries.len(), 1, "expected 1 certificate directory in {proof_dir:?}");
    std::fs::read_to_string(entries[0].join("Optimization.lean")).unwrap()
}

#[test]
fn ac_folds_and_helpers_certify_across_all_tiers() {
    let spec = r#"---- MODULE AcFolds ----
EXTENDS Integers, FiniteSets, Sequences, SequencesExt, Functions, FiniteSetsExt, Folds

CONSTANT Node
VARIABLES val, tags, flags, seq

Init ==
  /\ val = [n \in Node |-> 1]
  /\ tags = [n \in Node |-> {n}]
  /\ flags = [n \in Node |-> FALSE]
  /\ seq = <<>>

Next ==
  \/ \E n \in Node :
       /\ val[n] < 2
       /\ val' = [val EXCEPT ![n] = @ + 1]
       /\ flags' = [flags EXCEPT ![n] = TRUE]
       /\ UNCHANGED <<tags, seq>>
  \/ \E n \in Node :
       /\ Len(seq) < 2
       /\ seq' = Append(seq, n)
       /\ UNCHANGED <<val, tags, flags>>

Inv ==
  /\ FoldFunction(+, 0, [n \in Node |-> 1]) = Cardinality(Node)
  /\ FoldFunction(+, 0, val) >= Cardinality(Node)
  /\ FoldFunction(+, 0, val) <= 2 * Cardinality(Node)
  /\ FoldFunctionOnSet(+, 0, val, Node) = FoldFunction(+, 0, val)
  /\ FoldSet(+, 0, {val[n] : n \in Node}) <= 3
  /\ FoldSet(LAMBDA a, b : a * b, 1, {val[n] : n \in Node}) <= 2
  /\ FoldFunction(LAMBDA a, b : a * b, 1, val) <= 8
  /\ FoldFunction(LAMBDA a, b : a \cup b, {}, tags) = Node
  /\ FoldFunction(LAMBDA a, b : a \cap b, Node, tags) = {}
  /\ FoldFunction(LAMBDA a, b : a /\ b, TRUE, flags) = (\A n \in Node : flags[n])
  /\ FoldFunction(LAMBDA a, b : a \/ b, FALSE, flags) = (\E n \in Node : flags[n])
  /\ MapThenFoldSet(+, 0, LAMBDA x : val[x], LAMBDA s : CHOOSE y \in s : TRUE, Node) = FoldFunction(+, 0, val)
  /\ FoldSeq(+, 0, val) = FoldFunction(+, 0, val)
  /\ Quantify(Node, LAMBDA n : flags[n]) <= Cardinality(Node)
  /\ Range(seq) \subseteq Node
====
"#;
    let cfg = "CONSTANT Node = {n1, n2, n3}\nINIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
    let dir = tlx_testkit::TempDir::with_spec("equiv-ac-folds", spec, cfg);

    let unreduced = tlx_testkit::tlx_default!()
        .check("AcFolds.tla")
        .args(["-interp", "-noautosymmetry", "-workers", "1"])
        .dir(&dir)
        .timeout(Duration::from_secs(120))
        .run();
    assert_eq!(unreduced.code, 0, "{}", unreduced.text());
    assert!(unreduced.stdout.contains("104 distinct states found"), "{}", unreduced.text());

    let tlc_mode = tlx_testkit::tlx_default!()
        .check("AcFolds.tla")
        .args(["-tlc", "-interp", "-workers", "1"])
        .dir(&dir)
        .timeout(Duration::from_secs(120))
        .run();
    assert_eq!(tlc_mode.code, 0, "{}", tlc_mode.text());
    assert!(tlc_mode.stdout.contains("104 distinct states found"), "{}", tlc_mode.text());
    assert!(!tlc_mode.stdout.contains("(symmetry-reduced)"), "{}", tlc_mode.text());

    for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
        let proof_dir = dir.join(format!("proofs-{idx}"));
        let cache_dir = dir.join(format!("cache-{idx}"));
        let run = tlx_testkit::tlx_default!()
            .check("AcFolds.tla")
            .args(["-workers", "1"])
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
        assert!(run.stdout.contains("certificate generated"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("24 distinct states found, 0 states left on queue (symmetry-reduced)."), "{tier}: {}", run.text());
        let lean = read_single_lean(&proof_dir);
        let gen = lean.split("namespace TlxOptimization.GeneratedEquivSymmetry").nth(1).expect("GeneratedEquivSymmetry");
        assert!(gen.contains("Expr.foldSetAC"), "{tier}: expected Expr.foldSetAC in generated certificate");
        assert!(!lean.contains("sorry"));
    }
}

#[test]
fn sequence_folds_certify_direction_domain_traces_and_deadlocks_across_all_tiers() {
    let base_spec = r#"---- MODULE SeqFolds ----
EXTENDS Integers, FiniteSets, Sequences, SequencesExt, Folds

CONSTANT Node
VARIABLE log

Init == log = <<>>

Push ==
  \E n \in Node :
    /\ Len(log) < 3
    /\ log' = Append(log, [who |-> n, w |-> IF Len(log) = 0 THEN 1 ELSE 2])

Pop ==
  /\ Len(log) > 0
  /\ log' = Tail(log)

Next == Push \/ Pop

LeftCode == FoldLeft(LAMBDA acc, e : 3 * acc + e.w, 0, log)
RightCode == FoldRight(LAMBDA e, acc : 3 * acc + e.w, log, 0)
SeqCode == FoldSeq(LAMBDA e, acc : 3 * acc + e.w, 0, log)
LeftDomSum == FoldLeftDomain(LAMBDA acc, i : acc + i * log[i].w, 0, log)
RightDomCode == FoldRightDomain(LAMBDA i, acc : 3 * acc + log[i].w, log, 0)

Inv ==
  /\ SeqCode = LeftCode
  /\ RightDomCode = RightCode
  /\ LeftDomSum >= 0
  /\ (Len(log) = 2 /\ log[1].w = 1 /\ log[2].w = 2 => LeftCode = 5 /\ RightCode = 7)
  /\ Len(log) <= 3
====
"#;
    let base_cfg = "CONSTANT Node = {n1, n2, n3}\nINIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";

    // Unreduced baseline on safe spec.
    let safe_dir = tlx_testkit::TempDir::with_spec("equiv-seq-safe", base_spec, base_cfg);
    let unreduced = tlx_testkit::tlx_default!()
        .check("SeqFolds.tla")
        .args(["-interp", "-noautosymmetry", "-workers", "1"])
        .dir(&safe_dir)
        .timeout(Duration::from_secs(120))
        .run();
    assert_eq!(unreduced.code, 0, "{}", unreduced.text());
    assert!(unreduced.stdout.contains("79 distinct states found"), "{}", unreduced.text());

    for (label, spec, cfg, expected_code) in [
        ("safe", base_spec.to_owned(), base_cfg.to_owned(), 0),
        ("violation", base_spec.replace("Len(log) <= 3", "Len(log) < 3"), base_cfg.to_owned(), 12),
        (
            "deadlock",
            base_spec.replace("Next == Push \\/ Pop", "Next == Push"),
            base_cfg.replace("CHECK_DEADLOCK FALSE", "CHECK_DEADLOCK TRUE"),
            11,
        ),
    ] {
        let dir = tlx_testkit::TempDir::with_spec(&format!("equiv-seq-{label}"), &spec, &cfg);
        for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
            let proof_dir = dir.join(format!("proofs-{idx}"));
            let cache_dir = dir.join(format!("cache-{idx}"));
            let run = tlx_testkit::tlx_default!()
                .check("SeqFolds.tla")
                .args(["-workers", "1"])
                .args(*args)
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .env("TLX_SYMMETRY_PARANOID", "1")
                .env("TLX_PROOF_DIR", &proof_dir)
                .env("TLX_CACHE", &cache_dir)
                .dir(&dir)
                .timeout(Duration::from_secs(120))
                .run();
            assert_eq!(run.code, expected_code, "{label}/{tier}: {}", run.text());
            assert!(run.stdout.contains("certificate generated"), "{label}/{tier}: {}", run.text());
            if expected_code == 0 {
                assert!(
                    run.stdout.contains("17 distinct states found, 0 states left on queue (symmetry-reduced)."),
                    "{label}/{tier}: {}",
                    run.text()
                );
            } else {
                assert!(run.stdout.contains("State 4:"), "{label}/{tier} missing concrete lifted trace:\n{}", run.text());
                assert!(run.stdout.contains("log ="), "{label}/{tier} missing concrete state var:\n{}", run.text());
            }
            let lean = read_single_lean(&proof_dir);
            let gen = lean.split("namespace TlxOptimization.GeneratedEquivSymmetry").nth(1).expect("GeneratedEquivSymmetry");
            assert!(gen.contains("Expr.foldSeq"), "{label}/{tier}: expected Expr.foldSeq in generated certificate");
            assert!(!lean.contains("sorry"));
        }
    }
}

#[test]
fn recursive_choose_folds_and_erased_equiv_composition_across_all_tiers() {
    let base_spec = r#"---- MODULE RecFoldErased ----
EXTENDS Integers, FiniteSets, Sequences, SequencesExt

CONSTANT Node
VARIABLES weight, owned, log, audit

RECURSIVE SumOp(_, _)
SumOp(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + SumOp(f, S \ {x})

RECURSIVE ProdOp(_, _)
ProdOp(f, S) ==
  IF S = {} THEN 1
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] * ProdOp(f, S \ {x})

RECURSIVE CupOp(_, _)
CupOp(f, S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] \cup CupOp(f, S \ {x})

RECURSIVE CapOp(_, _)
CapOp(f, S) ==
  IF S = {} THEN Node
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] \cap CapOp(f, S \ {x})

FnSum(f, T) ==
  LET g[S \in SUBSET Node] ==
        IF S = {} THEN 0
        ELSE LET x == CHOOSE y \in S : TRUE
             IN f[x] + g[S \ {x}]
  IN g[T]

Init ==
  /\ weight = [n \in Node |-> 1]
  /\ owned = [n \in Node |-> {n}]
  /\ log = <<>>
  /\ audit = [steps |-> 0]

Grow ==
  \E n \in Node :
    /\ weight[n] < 2
    /\ weight' = [weight EXCEPT ![n] = @ + 1]
    /\ audit' = [steps |-> IF audit.steps < 5 THEN audit.steps + 1 ELSE audit.steps]
    /\ UNCHANGED <<owned, log>>

Record ==
  \E a, b \in Node :
    /\ Len(log) < 2
    /\ log' = Append(log, [src |-> a, dst |-> b])
    /\ audit' = [steps |-> IF audit.steps < 5 THEN audit.steps + 1 ELSE audit.steps]
    /\ UNCHANGED <<weight, owned>>

Reset ==
  /\ Len(log) > 0
  /\ log' = Tail(log)
  /\ audit' = [steps |-> 0]
  /\ UNCHANGED <<weight, owned>>

Next == Grow \/ Record \/ Reset

Inv ==
  /\ SumOp(weight, Node) = FnSum(weight, Node)
  /\ ProdOp(weight, Node) <= 8
  /\ CupOp(owned, Node) = Node
  /\ CapOp(owned, Node) = {}
  /\ FoldLeft(LAMBDA acc, e : acc + 1, 0, log) = Len(log)
  /\ SumOp(weight, Node) <= 2 * Cardinality(Node)
====
"#;
    let base_cfg = "CONSTANT Node = {n1, n2, n3}\nINIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";

    // Unreduced (-tlc) vs erasure-only (-optimize -noautosymmetry) vs composed (-optimize).
    let mode_dir = tlx_testkit::TempDir::with_spec("rec-fold-erased-modes", base_spec, base_cfg);
    let tlc_run = tlx_testkit::tlx_default!()
        .check("RecFoldErased.tla")
        .args(["-optimize", "-tlc", "-interp", "-workers", "1"])
        .dir(&mode_dir)
        .timeout(Duration::from_secs(120))
        .run();
    assert_eq!(tlc_run.code, 0, "{}", tlc_run.text());
    let erase_only = tlx_testkit::tlx_default!()
        .check("RecFoldErased.tla")
        .args(["-optimize", "-noautosymmetry", "-interp", "-workers", "1"])
        .env("TLX_PROOF_DIR", mode_dir.join("proofs-erase"))
        .dir(&mode_dir)
        .timeout(Duration::from_secs(120))
        .run();
    assert_eq!(erase_only.code, 0, "{}", erase_only.text());
    assert!(!erase_only.stdout.contains("composed with symmetry"), "{}", erase_only.text());

    for (label, spec, cfg, expected_code) in [
        ("safe", base_spec.to_owned(), base_cfg.to_owned(), 0),
        (
            "violation",
            base_spec.replace("SumOp(weight, Node) <= 2 * Cardinality(Node)", "SumOp(weight, Node) < 2 * Cardinality(Node)"),
            base_cfg.to_owned(),
            12,
        ),
        (
            "deadlock",
            base_spec.replace("Next == Grow \\/ Record \\/ Reset", "Next == Grow"),
            base_cfg.replace("CHECK_DEADLOCK FALSE", "CHECK_DEADLOCK TRUE"),
            11,
        ),
    ] {
        let dir = tlx_testkit::TempDir::with_spec(&format!("rec-fold-erased-{label}"), &spec, &cfg);
        for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
            let proof_dir = dir.join(format!("proofs-{idx}"));
            let cache_dir = dir.join(format!("cache-{idx}"));
            let run = tlx_testkit::tlx_default!()
                .check("RecFoldErased.tla")
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
            assert_eq!(run.code, expected_code, "{label}/{tier}: {}", run.text());
            assert!(run.stdout.contains("composed with symmetry Permutations(Node)"), "{label}/{tier}: {}", run.text());
            assert!(run.stdout.contains("erasure/equivariant-symmetry composition certificate"), "{label}/{tier}: {}", run.text());
            if expected_code != 0 {
                assert!(run.stdout.contains("audit ="), "{label}/{tier} missing concrete erased variable:\n{}", run.text());
            }
            let lean = read_single_lean(&proof_dir);
            let gen = lean.split("namespace TlxOptimization.GeneratedErasedEquivSymmetry").nth(1).expect("GeneratedErasedEquivSymmetry");
            assert!(gen.contains("theorem erasure_certificate"), "{label}/{tier}");
            assert!(gen.contains("Expr.foldSetAC"), "{label}/{tier}: expected Expr.foldSetAC");
            assert!(gen.contains("Expr.foldSeq"), "{label}/{tier}: expected Expr.foldSeq");
            assert!(!lean.contains("sorry"));
        }
    }
}

#[test]
fn fold_soundness_refusals_match_unreduced_across_tiers() {
    let cases: &[(&str, &str)] = &[
        (
            "non_ca_fold_set",
            "VARIABLE f\n\
             Init == f \\in {[n \\in Node |-> IF n = r THEN 1 ELSE 0] : r \\in Node}\n\
             Next == UNCHANGED f\n\
             Inv == FoldSet(LAMBDA x, y : x - y, 0, {f[n] : n \\in Node}) <= 10",
        ),
        (
            "non_ca_fold_function",
            "VARIABLE f\n\
             Init == f \\in {[n \\in Node |-> IF n = r THEN 1 ELSE 0] : r \\in Node}\n\
             Next == UNCHANGED f\n\
             Inv == FoldFunction(LAMBDA x, y : x - y, 0, f) <= 10",
        ),
        (
            "non_chooses_first_map_then_fold",
            "VARIABLE f\n\
             Init == f \\in {[n \\in Node |-> IF n = r THEN 1 ELSE 0] : r \\in Node}\n\
             Next == UNCHANGED f\n\
             Inv == MapThenFoldSet(+, 0, LAMBDA x : f[x], LAMBDA s : CHOOSE y \\in s : y = y, Node) <= 10",
        ),
        (
            "non_ca_fold_seq_on_non_sequence_map",
            "VARIABLE f\n\
             Init == f \\in {[n \\in Node |-> IF n = r THEN 1 ELSE 0] : r \\in Node}\n\
             Next == UNCHANGED f\n\
             Inv == FoldSeq(LAMBDA x, acc : acc - x, 0, f) <= 10",
        ),
        (
            "out_of_domain_fold_function_on_set",
            "VARIABLE f\n\
             Init == \\E r \\in Node : f = [n \\in {r} |-> 1]\n\
             Next == UNCHANGED f\n\
             Inv == FoldFunctionOnSet(+, 0, f, Node) >= 0",
        ),
        (
            "overflowing_partial_sum",
            "VARIABLE f\n\
             Init == \\E r \\in Node : f = [n \\in Node |-> IF n = r THEN 2147483647 ELSE 1]\n\
             Next == UNCHANGED f\n\
             Inv == FoldFunction(+, 0, f) >= 0",
        ),
        (
            "overflowing_partial_product",
            "VARIABLE f\n\
             Init == \\E r \\in Node : f = [n \\in Node |-> IF n = r THEN 0 ELSE 100000]\n\
             Next == UNCHANGED f\n\
             Inv == FoldFunction(LAMBDA a, b : a * b, 1, f) = 0",
        ),
        (
            "overflowing_product_i32_min_base",
            "VARIABLE f\n\
             Init == f = [n \\in Node |-> -1]\n\
             Next == UNCHANGED f\n\
             Inv == FoldFunction(LAMBDA a, b : a * b, -2147483648, f) <= 0",
        ),
    ];

    for (name, body) in cases {
        let spec = format!(
            "---- MODULE Refusal ----\nEXTENDS Integers, FiniteSets, Sequences, Functions, SequencesExt, FiniteSetsExt, Folds\nCONSTANT Node\n{body}\n====\n"
        );
        let cfg = "CONSTANT Node = {n1, n2, n3}\nINIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
        let dir = tlx_testkit::TempDir::with_spec(&format!("fold-refusal-{name}"), &spec, cfg);
        for tier in ["-interp", "-compile"] {
            let unreduced = tlx_testkit::tlx_default!()
                .check("Refusal.tla")
                .args([tier, "-noautosymmetry", "-workers", "1"])
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            let default = tlx_testkit::tlx_default!()
                .check("Refusal.tla")
                .args([tier, "-workers", "1"])
                .env("TLX_PROOF_DIR", dir.join(format!("proofs-{tier}")))
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            assert_ne!(unreduced.code, 150, "{name}/{tier}: refusal fixture must parse cleanly:\n{}", unreduced.text());
            assert_eq!(
                default.code,
                unreduced.code,
                "{name}/{tier}: exit code mismatch:\nDEFAULT:\n{}\nUNREDUCED:\n{}",
                default.text(),
                unreduced.text()
            );
            assert!(!default.stdout.contains("(symmetry-reduced)"), "{name}/{tier}: must refuse automatic symmetry:\n{}", default.text());
        }
    }
}

#[test]
fn erasure_preserves_recursive_fold_domain_and_native_literal_operator_verdicts() {
    let cases: &[(&str, &str, &str, i32)] = &[
        (
            "FoldDomain",
            r#"---- MODULE FoldDomain ----
EXTENDS Integers
VARIABLES x, tick, audit
Read ==
  LET g[S \in SUBSET (IF tick < 2 THEN {1} ELSE {})] ==
        IF S = {} THEN 0
        ELSE LET k == CHOOSE y \in S : TRUE
             IN k + g[S \ {k}]
  IN g[{1}]
Init == x = 0 /\ tick = 0 /\ audit = 0
Next == x' = x /\ tick' = (IF tick < 2 THEN tick + 1 ELSE tick)
        /\ audit' = Read
Inv == x = 0
====
"#,
            "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n",
            75,
        ),
        (
            "ObservedDomain",
            r#"---- MODULE ObservedDomain ----
EXTENDS Integers
VARIABLES x, tick, audit
Read ==
  LET g[S \in SUBSET (IF tick < 2 THEN {1} ELSE {})] ==
        IF S = {} THEN 0
        ELSE LET k == CHOOSE y \in S : TRUE
             IN k + g[S \ {k}]
  IN g[{1}]
Init == x = 0 /\ tick = 0 /\ audit = 0
Next == x' = x /\ tick' = (IF tick < 2 THEN tick + 1 ELSE tick)
        /\ audit' = 0
Inv == x = 0 /\ Read = 1
====
"#,
            "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n",
            76,
        ),
        (
            "RecFnOutOfStaticDomain",
            r#"---- MODULE RecFnOutOfStaticDomain ----
EXTENDS Integers, SequencesExt, FiniteSets
VARIABLES live, ghost
G[S \in SUBSET {1}] ==
  IF S = {} THEN 0 ELSE LET x == CHOOSE t \in S : TRUE IN x + G[S \ {x}]

Init == /\ live = 0 /\ ghost = 0
Next == /\ UNCHANGED live /\ ghost' = IF ghost = 0 THEN 1 ELSE G[{2}]
Inv == live = 0
====
"#,
            "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n",
            75,
        ),
        (
            "RecFnDynamicInvariantDomain",
            r#"---- MODULE RecFnDynamicInvariantDomain ----
EXTENDS Integers, SequencesExt, FiniteSets
VARIABLES live, ghost
G[S \in SUBSET (IF ghost < 2 THEN {1} ELSE {})] ==
  IF S = {} THEN 0 ELSE LET x == CHOOSE t \in S : TRUE IN x + G[S \ {x}]

Init == /\ live = 0 /\ ghost = 0
Next == /\ UNCHANGED live /\ ghost' = IF ghost < 2 THEN ghost + 1 ELSE 2
Inv == live = 0 /\ G[{1}] = 1
====
"#,
            "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n",
            76,
        ),
        (
            "NativeLiteralFoldLeft",
            r#"---- MODULE NativeLiteralFoldLeft ----
EXTENDS Integers, SequencesExt, FiniteSets
VARIABLES live, ghost

Init == /\ live = 0 /\ ghost = 0
Next == /\ UNCHANGED live /\ ghost' = IF ghost = 0 THEN 1 ELSE FoldLeft(LAMBDA a, b : 2, 0, <<1>>)
Inv == live = 0
====
"#,
            "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n",
            255,
        ),
        (
            "NativeLiteralFoldLeftEmptySeq",
            r#"---- MODULE NativeLiteralFoldLeftEmptySeq ----
EXTENDS Integers, SequencesExt
VARIABLES live, ghost
ConstStr(a, b) == "x"
Init == /\ live = 0 /\ ghost = ""
Next == /\ UNCHANGED live /\ ghost' = IF ghost = "" THEN "ok" ELSE FoldSeq(ConstStr, "", <<>>)
Inv == live = 0
====
"#,
            "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n",
            255,
        ),
    ];

    for (name, spec, cfg, expected_code) in cases {
        let dir = tlx_testkit::TempDir::with_spec(&format!("erasure-fold-{name}"), spec, cfg);
        let tla = format!("{name}.tla");
        for tier in ["-interp", "-compile"] {
            let unreduced = tlx_testkit::tlx_default!()
                .check(&tla)
                .args([tier, "-noautosymmetry", "-workers", "1", "-maxmem", "32"])
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            assert_eq!(unreduced.code, *expected_code, "{name}/{tier} unreduced:\n{}", unreduced.text());

            let optimized = tlx_testkit::tlx_default!()
                .check(&tla)
                .args([tier, "-optimize", "-noautosymmetry", "-workers", "1", "-maxmem", "32"])
                .env("TLX_PROOF_DIR", dir.join(format!("proofs-{tier}")))
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            assert_eq!(
                optimized.code,
                unreduced.code,
                "{name}/{tier}: -optimize verdict must match unreduced:\nOPTIMIZED:\n{}\nUNREDUCED:\n{}",
                optimized.text(),
                unreduced.text()
            );
        }
    }
}
