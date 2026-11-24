//! Regression tests for compiled-tier point bugs:
//! - C-3: saturating `u64` multiplication and unsigned loop bound in `Stmt::Repeat`
//!   across IR fast-exec, Cranelift JIT, and generated C;
//! - C-4: multi-bound quantifier iteration order (first variable fastest) and
//!   upfront domain validation across empty `{}` bounds;
//! - C-6: upfront rejection of numeric/string literal operator bodies in
//!   `SortSeq`, `SelectSeq`, `FoldFunction`, `FoldSeq`, and `FoldFunctionOnSet`.

use tlx_testkit::TempDir;

type Backend = (&'static str, &'static [&'static str], &'static [(&'static str, &'static str)]);

const BACKENDS: [Backend; 4] = [
    ("interp", &["-interp"], &[]),
    ("fast-ir", &["-compile"], &[("TLX_PRERUN_REUSE", "0"), ("TLX_NO_NATIVE", "1")]),
    ("jit", &["-compile"], &[("TLX_PRERUN_REUSE", "0"), ("TLX_JIT", "only"), ("TLX_JIT_VERIFY", "1")]),
    ("cgen", &["-compile"], &[("TLX_PRERUN_REUSE", "0"), ("TLX_JIT", "0"), ("TLX_NATIVE_SYNC", "1")]),
];

fn check_all_backends(name: &str, spec: &str, cfg: &str, expected_code: i32, expected_substr: &str) {
    let dir = TempDir::with_spec(name, spec, cfg);
    let tla = format!("{name}.tla");
    let cfg_file = format!("{name}.cfg");
    for (backend, args, envs) in BACKENDS {
        let out =
            tlx_testkit::tlx!().check(&tla).cfg(&cfg_file).args(["-workers", "1"]).args(args).dir(&dir).envs(envs.iter().copied()).run();
        let text = out.text();
        assert_eq!(out.code, expected_code, "{name} ({backend}): unexpected exit code\n{text}");
        if !expected_substr.is_empty() {
            assert!(text.contains(expected_substr), "{name} ({backend}): missing {expected_substr:?} in output:\n{text}");
        }
    }
}

#[test]
fn repeat_overflow_saturates_across_backends() {
    let spec_2_64 = r#"---- MODULE RepeatOverflowBug ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Act  == (\A i \in 1..32 : \E k \in 1..4 : TRUE) /\ x' = 1
Inv  == ENABLED Act
====
"#;
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    check_all_backends("RepeatOverflowBug", spec_2_64, cfg, 0, "No error has been found");

    let spec_2_63 = r#"---- MODULE RepeatSignedOverflowBug ----
EXTENDS Naturals
VARIABLE x
Init == x = 0
Next == UNCHANGED x
Act  == (\A i \in 1..63 : \E k \in 1..2 : TRUE) /\ x' = 1
Inv  == ENABLED Act
====
"#;
    check_all_backends("RepeatSignedOverflowBug", spec_2_63, cfg, 0, "No error has been found");
}

#[test]
fn quant_multi_bound_order_and_domain_validation() {
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";

    let order_spec = r#"---- MODULE QuantOrderBug ----
EXTENDS Naturals
VARIABLE v
Init == v = 0
Next == UNCHANGED v
Inv ==
  \E x \in {1, 2}, y \in {1, 2} :
    IF x = 1 /\ y = 2 THEN v = 0
    ELSE IF x = 2 /\ y = 1 THEN (1 \div v) = 0
    ELSE FALSE
====
"#;
    check_all_backends("QuantOrderBug", order_spec, cfg, 75, "The second argument of \\div is 0.");

    let forall_invalid_left = r#"---- MODULE QuantEmptyInvalidLeft ----
VARIABLE v
Init == v = 0
Next == UNCHANGED v
Inv  == \A x \in 42, y \in {} : TRUE
====
"#;
    check_all_backends("QuantEmptyInvalidLeft", forall_invalid_left, cfg, 75, "");

    let exists_invalid_right = r#"---- MODULE QuantEmptyInvalidRight ----
VARIABLE v
Init == v = 0
Next == UNCHANGED v
Inv  == \E x \in {}, y \in 42 : TRUE
====
"#;
    check_all_backends("QuantEmptyInvalidRight", exists_invalid_right, cfg, 75, "");

    let action_exists_invalid_left = r#"---- MODULE ActionExistsEmptyInvalidLeft ----
VARIABLE x
Init == x = 0
Next == \E a \in 42, b \in {} : x' = a
====
"#;
    check_all_backends("ActionExistsEmptyInvalidLeft", action_exists_invalid_left, "INIT Init\nNEXT Next\n", 75, "");
}

#[test]
fn literal_op_rejected_upfront_in_higher_order_builtins() {
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";

    let sort_seq = r#"---- MODULE SortSeqLiteralOpBug ----
EXTENDS Naturals, TLC
VARIABLE s
Init == s \in {<<1>>, <<1, 2>>}
Next == UNCHANGED s
Inv  == s = <<1, 2>> \/ SortSeq(s, LAMBDA a, b : 2) = <<1>>
====
"#;
    check_all_backends(
        "SortSeqLiteralOpBug",
        sort_seq,
        cfg,
        75,
        "The second argument of SortSeq should be an operator, but instead it is: 2",
    );

    let select_seq = r#"---- MODULE SelectSeqLiteralOpBug ----
EXTENDS Naturals, Sequences
VARIABLE s
Init == s \in {<<>>, <<1>>}
Next == UNCHANGED s
Inv  == s = <<1>> \/ SelectSeq(s, LAMBDA a : 2) = <<>>
====
"#;
    check_all_backends(
        "SelectSeqLiteralOpBug",
        select_seq,
        cfg,
        75,
        "The second argument of SelectSeq should be an operator, but instead it is: 2",
    );

    let fold_fn = r#"---- MODULE FoldFunctionLiteralOpBug ----
EXTENDS Naturals, Functions
VARIABLE f
Init == f = [i \in {1, 2} |-> i]
Next == UNCHANGED f
Inv  == FoldFunction(LAMBDA a, b : 2, 0, f) = 2
====
"#;
    check_all_backends(
        "FoldFunctionLiteralOpBug",
        fold_fn,
        cfg,
        75,
        "The first argument of FoldFunction should be an operator, but instead it is: 2",
    );

    let fold_seq = r#"---- MODULE FoldSeqLiteralOpBug ----
EXTENDS Naturals, SequencesExt
VARIABLE s
Init == s \in {<<>>, <<1>>}
Next == UNCHANGED s
Inv  == s = <<1>> \/ FoldSeq(LAMBDA a, b : "a", 0, s) = 0
====
"#;
    check_all_backends(
        "FoldSeqLiteralOpBug",
        fold_seq,
        cfg,
        75,
        "The first argument of FoldSeq should be an operator, but instead it is: \"a\"",
    );

    let fold_fn_on_set = r#"---- MODULE FoldFunctionOnSetLiteralOpBug ----
EXTENDS Naturals, Functions
VARIABLE f
LitOp(a, b) == 2
Init == f = [i \in {1, 2} |-> i]
Next == UNCHANGED f
Inv  == FoldFunctionOnSet(LitOp, 0, f, DOMAIN f) = 2
====
"#;
    check_all_backends(
        "FoldFunctionOnSetLiteralOpBug",
        fold_fn_on_set,
        cfg,
        75,
        "The first argument of FoldFunctionOnSet should be an operator, but instead it is: 2",
    );
}
