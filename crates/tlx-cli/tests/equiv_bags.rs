//! End-to-end cross-tier paranoid regression tests for `Bags` and `BagsExt`
//! (`FoldBag`, `BagAdd`, `BagRemove`, `BagRemoveAll`, `SumBag`, `ProductBag`)
//! in `EquivSymCertificate` and composed `ErasedEquivCertificate`.

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
fn bags_operators_and_bagsext_certify_across_all_tiers() {
    let spec = r#"---- MODULE EquivBags ----
EXTENDS Integers, FiniteSets, Bags, BagsExt

CONSTANT Node
VARIABLES bag, aux

Init ==
  /\ bag = EmptyBag
  /\ aux = EmptyBag

AddOnce ==
  \E n \in Node :
    /\ CopiesIn(n, bag) < 2
    /\ BagCardinality(bag) < 3
    /\ BagCardinality(aux) < 3
    /\ bag' = BagAdd(bag, n)
    /\ aux' = aux (+) SetToBag({n})

RemoveOne ==
  \E n \in Node :
    /\ BagIn(n, bag)
    /\ bag' = BagRemove(bag, n)
    /\ aux' = aux (-) SetToBag({n})

ClearOne ==
  \E n \in Node :
    /\ BagIn(n, bag)
    /\ bag' = BagRemoveAll(bag, n)
    /\ aux' = BagRemoveAll(aux, n)

Next == AddOnce \/ RemoveOne \/ ClearOne

NumBag == BagOfAll(LAMBDA n : IF n \in Node THEN 2 ELSE 0, bag)
SingletonSetBag == BagOfAll(LAMBDA n : {n}, bag)
BoolBag == BagOfAll(LAMBDA n : n \in Node, bag)
ZeroMap == [n \in Node |-> 0]
NegMap == [n \in Node |-> -1]

Inv ==
  /\ bag = aux
  /\ IsABag(EmptyBag)
  /\ IsABag(bag)
  /\ IsABag(<<1, 2>>)
  /\ ~IsABag(<<0, 1>>)
  /\ ~IsABag(ZeroMap)
  /\ ~IsABag(NegMap)
  /\ ~IsABag(Node)
  /\ ~IsABag(42)
  /\ ~IsABag("x")
  /\ \A n \in Node :
       /\ (BagIn(n, bag) <=> CopiesIn(n, bag) > 0)
       /\ (BagIn(n, bag) => bag[n] >= 1)
       /\ CopiesIn(n, ZeroMap) = 0
       /\ CopiesIn(n, NegMap) = -1
  /\ BagToSet(bag) \subseteq Node
  /\ SetToBag(BagToSet(bag)) \sqsubseteq bag
  /\ EmptyBag \sqsubseteq bag
  /\ bag \sqsubseteq (bag (+) SetToBag(Node))
  /\ (bag (-) bag) = EmptyBag
  /\ BagCardinality(bag) <= 3
  /\ BagCardinality(bag) >= Cardinality(BagToSet(bag))
  /\ BagCardinality(BagUnion({bag, bag (+) SetToBag(Node)})) = 2 * BagCardinality(bag) + Cardinality(Node)
  /\ BagCardinality(NumBag) = BagCardinality(bag)
  /\ CopiesIn(2, NumBag) = BagCardinality(bag)
  /\ SumBag(NumBag) = 2 * BagCardinality(bag)
  /\ ProductBag(NumBag) >= 1
  /\ FoldBag(+, 0, NumBag) = 2 * BagCardinality(bag)
  /\ FoldBag(LAMBDA a, b : a * b, 1, NumBag) <= 8
  /\ FoldBag(LAMBDA a, b : a \cup b, {}, SingletonSetBag) = BagToSet(bag)
  /\ FoldBag(LAMBDA a, b : a \cap b, Node, BagOfAll(LAMBDA n : Node, bag)) = Node
  /\ FoldBag(LAMBDA a, b : a /\ b, TRUE, BoolBag) = TRUE
  /\ FoldBag(LAMBDA a, b : a \/ b, FALSE, BoolBag) = (bag # EmptyBag)
====
"#;
    let cfg = "CONSTANT Node = {n1, n2, n3}\nINIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
    let dir = tlx_testkit::TempDir::with_spec("equiv-bags-all", spec, cfg);

    let unreduced = tlx_testkit::tlx_default!()
        .check("EquivBags.tla")
        .args(["-interp", "-noautosymmetry", "-workers", "1"])
        .dir(&dir)
        .timeout(Duration::from_secs(120))
        .run();
    assert_eq!(unreduced.code, 0, "{}", unreduced.text());
    assert!(unreduced.stdout.contains("17 distinct states found"), "{}", unreduced.text());

    let tlc_mode = tlx_testkit::tlx_default!()
        .check("EquivBags.tla")
        .args(["-tlc", "-interp", "-workers", "1"])
        .dir(&dir)
        .timeout(Duration::from_secs(120))
        .run();
    assert_eq!(tlc_mode.code, 0, "{}", tlc_mode.text());
    assert!(tlc_mode.stdout.contains("17 distinct states found"), "{}", tlc_mode.text());
    assert!(!tlc_mode.stdout.contains("(symmetry-reduced)"), "{}", tlc_mode.text());

    for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
        let proof_dir = dir.join(format!("proofs-{idx}"));
        let cache_dir = dir.join(format!("cache-{idx}"));
        let run = tlx_testkit::tlx_default!()
            .check("EquivBags.tla")
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
        assert!(run.stdout.contains("6 distinct states found, 0 states left on queue (symmetry-reduced)."), "{tier}: {}", run.text());
        let lean = read_single_lean(&proof_dir);
        let gen = lean.split("namespace TlxOptimization.GeneratedEquivSymmetry").nth(1).expect("GeneratedEquivSymmetry");
        for needle in [
            "Expr.copiesIn",
            "Expr.bagCup",
            "Expr.bagDiff",
            "Expr.bagUnion",
            "Expr.bagCard",
            "Expr.bagOfAll",
            "Expr.foldBag",
            "Form.isABag",
            "Form.bagIn",
            "Form.sqSubseteq",
        ] {
            assert!(gen.contains(needle), "{tier}: expected {needle} in generated certificate");
        }
        assert!(!lean.contains("sorry"));
    }
}

#[test]
fn bags_erased_equiv_composition_traces_and_deadlocks_across_all_tiers() {
    let base_spec = r#"---- MODULE EquivBagsErased ----
EXTENDS Integers, FiniteSets, Bags, BagsExt

CONSTANT Node
VARIABLES bag, audit

Init ==
  /\ bag = EmptyBag
  /\ audit = [steps |-> 0]

Add ==
  \E n \in Node :
    /\ CopiesIn(n, bag) < 2
    /\ BagCardinality(bag) < 3
    /\ bag' = BagAdd(bag, n)
    /\ audit' = [steps |-> IF audit.steps < 5 THEN audit.steps + 1 ELSE audit.steps]

Drop ==
  \E n \in Node :
    /\ BagIn(n, bag)
    /\ bag' = BagRemove(bag, n)
    /\ audit' = [steps |-> 0]

Next == Add \/ Drop

Inv ==
  /\ IsABag(bag)
  /\ BagCardinality(bag) <= 3
  /\ SumBag(BagOfAll(LAMBDA n : IF n \in Node THEN 1 ELSE 0, bag)) = BagCardinality(bag)
====
"#;
    let base_cfg = "CONSTANT Node = {n1, n2, n3}\nINIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";

    let mode_dir = tlx_testkit::TempDir::with_spec("equiv-bags-erased-modes", base_spec, base_cfg);
    let tlc_run = tlx_testkit::tlx_default!()
        .check("EquivBagsErased.tla")
        .args(["-optimize", "-tlc", "-interp", "-workers", "1"])
        .dir(&mode_dir)
        .timeout(Duration::from_secs(120))
        .run();
    assert_eq!(tlc_run.code, 0, "{}", tlc_run.text());
    assert!(!tlc_run.stdout.contains("(symmetry-reduced)"), "{}", tlc_run.text());

    let erase_only = tlx_testkit::tlx_default!()
        .check("EquivBagsErased.tla")
        .args(["-optimize", "-noautosymmetry", "-interp", "-workers", "1"])
        .env("TLX_PROOF_DIR", mode_dir.join("proofs-erase"))
        .dir(&mode_dir)
        .timeout(Duration::from_secs(120))
        .run();
    assert_eq!(erase_only.code, 0, "{}", erase_only.text());
    assert!(!erase_only.stdout.contains("composed with symmetry"), "{}", erase_only.text());

    for (label, spec, cfg, expected_code) in [
        ("safe", base_spec.to_owned(), base_cfg.to_owned(), 0),
        ("violation", base_spec.replace("BagCardinality(bag) <= 3", "BagCardinality(bag) < 3"), base_cfg.to_owned(), 12),
        (
            "deadlock",
            base_spec.replace("Next == Add \\/ Drop", "Next == Add"),
            base_cfg.replace("CHECK_DEADLOCK FALSE", "CHECK_DEADLOCK TRUE"),
            11,
        ),
    ] {
        let dir = tlx_testkit::TempDir::with_spec(&format!("equiv-bags-erased-{label}"), &spec, &cfg);
        for (idx, (tier, args, env)) in ALL_TIERS.iter().enumerate() {
            let proof_dir = dir.join(format!("proofs-{idx}"));
            let cache_dir = dir.join(format!("cache-{idx}"));
            let run = tlx_testkit::tlx_default!()
                .check("EquivBagsErased.tla")
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
            if expected_code == 0 {
                assert!(run.stdout.contains("6 distinct states found, 0 states left on queue"), "{label}/{tier}: {}", run.text());
            } else {
                assert!(run.stdout.contains("State 4:"), "{label}/{tier} missing concrete lifted trace:\n{}", run.text());
                assert!(run.stdout.contains("audit ="), "{label}/{tier} missing concrete erased variable:\n{}", run.text());
            }
            let lean = read_single_lean(&proof_dir);
            let gen = lean.split("namespace TlxOptimization.GeneratedErasedEquivSymmetry").nth(1).expect("GeneratedErasedEquivSymmetry");
            assert!(gen.contains("theorem erasure_certificate"), "{label}/{tier}");
            assert!(gen.contains("Expr.bagCard"), "{label}/{tier}: expected Expr.bagCard");
            assert!(gen.contains("Expr.foldBag"), "{label}/{tier}: expected Expr.foldBag");
            assert!(!lean.contains("sorry"));
        }
    }
}

#[test]
fn bags_soundness_refusals_match_unreduced_across_tiers() {
    let cases: &[(&str, &str)] = &[
        (
            "bag_cup_zero_count",
            "VARIABLE b\n\
             Init == b \\in {[n \\in Node |-> IF n = r THEN 0 ELSE 1] : r \\in Node}\n\
             Next == UNCHANGED b\n\
             Inv == IsABag(b (+) EmptyBag)",
        ),
        (
            "bag_cup_negative_count",
            "VARIABLE b\n\
             Init == b \\in {[n \\in Node |-> IF n = r THEN -1 ELSE 1] : r \\in Node}\n\
             Next == UNCHANGED b\n\
             Inv == IsABag(b (+) EmptyBag)",
        ),
        (
            "bag_diff_non_int_range",
            "VARIABLE b\n\
             Init == b \\in {[n \\in Node |-> IF n = r THEN \"x\" ELSE 1] : r \\in Node}\n\
             Next == UNCHANGED b\n\
             Inv == IsABag(b (-) EmptyBag)",
        ),
        (
            "bag_of_all_native_literal_op",
            "VARIABLE b\n\
             Init == b = EmptyBag\n\
             Next == UNCHANGED b\n\
             Inv == IsABag(BagOfAll(LAMBDA x : 1, b))",
        ),
        (
            "bag_card_non_bag",
            "VARIABLE b\n\
             Init == b \\in {[n \\in Node |-> IF n = r THEN 0 ELSE 1] : r \\in Node}\n\
             Next == UNCHANGED b\n\
             Inv == BagCardinality(b) >= 0",
        ),
        (
            "bag_union_non_bag_elem",
            "VARIABLE b\n\
             Init == b \\in {[n \\in Node |-> IF n = r THEN 0 ELSE 1] : r \\in Node}\n\
             Next == UNCHANGED b\n\
             Inv == IsABag(BagUnion({b}))",
        ),
        (
            "bag_of_all_non_bag",
            "VARIABLE b\n\
             Init == b \\in {[n \\in Node |-> IF n = r THEN 0 ELSE 1] : r \\in Node}\n\
             Next == UNCHANGED b\n\
             Inv == IsABag(BagOfAll(LAMBDA x : x, b))",
        ),
        (
            "fold_bag_non_bag",
            "VARIABLE b\n\
             Init == b \\in {[n \\in Node |-> IF n = r THEN 0 ELSE 1] : r \\in Node}\n\
             Next == UNCHANGED b\n\
             Inv == FoldBag(+, 0, b) >= 0",
        ),
        (
            "fold_bag_non_ca",
            "VARIABLE b\n\
             Init == \\E r \\in Node : b = BagOfAll(LAMBDA x : IF x = r THEN 2 ELSE 1, SetToBag(Node))\n\
             Next == UNCHANGED b\n\
             Inv == FoldBag(LAMBDA x, y : x - y, 0, b) <= 10",
        ),
        (
            "bag_cup_overflow",
            "VARIABLE b\n\
             Init == \\E r \\in Node : b = [n \\in Node |-> IF n = r THEN 2147483647 ELSE 1]\n\
             Next == UNCHANGED b\n\
             Inv == IsABag(b (+) SetToBag(Node))",
        ),
        (
            "bag_card_overflow",
            "VARIABLE b\n\
             Init == \\E r \\in Node : b = [n \\in Node |-> IF n = r THEN 2147483647 ELSE 1]\n\
             Next == UNCHANGED b\n\
             Inv == BagCardinality(b) >= 0",
        ),
        (
            "bag_union_overflow",
            "VARIABLE b\n\
             Init == \\E r \\in Node : b = [n \\in Node |-> IF n = r THEN 2147483647 ELSE 1]\n\
             Next == UNCHANGED b\n\
             Inv == IsABag(BagUnion({b, SetToBag(Node)}))",
        ),
        (
            "bag_of_all_overflow",
            "VARIABLE b\n\
             Init == \\E r \\in Node : b = [n \\in Node |-> IF n = r THEN 2147483647 ELSE 1]\n\
             Next == UNCHANGED b\n\
             Inv == IsABag(BagOfAll(LAMBDA x : IF x \\in Node THEN 1 ELSE 0, b))",
        ),
        (
            "fold_bag_add_overflow",
            "VARIABLE b\n\
             Init == \\E r \\in Node : b = [n \\in Node |-> IF n = r THEN 2 ELSE 1]\n\
             Next == UNCHANGED b\n\
             Inv == FoldBag(+, 0, BagOfAll(LAMBDA x : IF x \\in Node THEN 2147483647 ELSE 0, b)) >= 0",
        ),
        (
            "fold_bag_mul_overflow",
            "VARIABLE b\n\
             Init == \\E r \\in Node : b = [n \\in Node |-> IF n = r THEN 2 ELSE 1]\n\
             Next == UNCHANGED b\n\
             Inv == FoldBag(LAMBDA x, y : x * y, 1, BagOfAll(LAMBDA x : IF x \\in Node THEN 100000 ELSE 0, b)) >= 0",
        ),
    ];

    for (name, body) in cases {
        let spec = format!("---- MODULE BagRefusal ----\nEXTENDS Integers, FiniteSets, Bags, BagsExt\nCONSTANT Node\n{body}\n====\n");
        let cfg = "CONSTANT Node = {n1, n2, n3}\nINIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
        let dir = tlx_testkit::TempDir::with_spec(&format!("bag-refusal-{name}"), &spec, cfg);
        for tier in ["-interp", "-compile"] {
            let unreduced = tlx_testkit::tlx_default!()
                .check("BagRefusal.tla")
                .args([tier, "-noautosymmetry", "-workers", "1"])
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            let default = tlx_testkit::tlx_default!()
                .check("BagRefusal.tla")
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
