//! Regression tests for Structural Issue #2:
//! - S-1: User modules named after bundled modules (`Bitwise.tla`) vs. real
//!   strict bundled overrides (`EXTENDS Bitwise` with `shiftR(1 \div 0, 0)`).
//! - C-1: Preserving `Scope::Single` across `LET` definitions in mixed-mode
//!   host-region memoization (`MixedLetScopeMemoBug`).
//! - C-2: Preserving lexical closures for parameterized `LET` operator
//!   arguments (`LetHigherOrderClosureBug`).
//! - E-5: Unwrapping call-by-name `Local` parameters and `LET` in `UNCHANGED`
//!   (`UnchangedParamTuple`).

use std::time::Duration;

fn run_spec(tag: &str, name: &str, spec: &str, cfg: &str, args: &[&str], env: &[(&str, &str)]) -> (i32, String) {
    let dir = tlx_testkit::TempDir::new(&format!("call-sem-{tag}"));
    std::fs::write(dir.join(format!("{name}.tla")), spec).unwrap();
    std::fs::write(dir.join(format!("{name}.cfg")), cfg).unwrap();
    let mut cmd = tlx_testkit::tlx!();
    cmd.args(["check", &format!("{name}.tla"), "-config", &format!("{name}.cfg"), "-workers", "1"]).args(args).dir(&dir);
    cmd.command().env_remove("RUST_BACKTRACE");
    let out = cmd.envs(env.iter().copied()).timeout(Duration::from_secs(60)).run();
    (out.code, out.text())
}

#[test]
fn bitwise_module_and_bundled_strict_errors_are_preserved() {
    // As in TLC (`CG1`, `CG2`), Java `@TLAPlusOperator` overrides match by
    // `(module, operator)` regardless of load path: `Bitwise!Xor(1 \div 0, 0)`
    // evaluates `1 \div 0` strictly, and `SymNormalizer` must refuse erasing
    // it so default mode, `-tlc`, and `TLX_PARANOID=1` all report exit 75.
    let user_spec = r#"---- MODULE Bitwise ----
EXTENDS Naturals
CONSTANT Proc
VARIABLE owner
Xor(a, b) == TRUE
Init == owner \in Proc
Next == owner' \in Proc
Inv  == \E p \in Proc : p = owner \/ Xor(1 \div 0, 0)
====
"#;
    let cfg = "CONSTANT Proc = {p1, p2}\nINIT Init\nNEXT Next\nINVARIANT Inv\n";
    for (tag, args, env) in [
        ("user-bitwise-default", &[][..], &[][..]),
        ("user-bitwise-tlc", &["-tlc"][..], &[][..]),
        ("user-bitwise-paranoid", &["-compile", "-tlc"][..], &[("TLX_PARANOID", "1"), ("TLX_PRERUN_REUSE", "0")][..]),
    ] {
        let (code, out) = run_spec(tag, "Bitwise", user_spec, cfg, args, env);
        assert_eq!(code, 75, "{tag}:\n{out}");
        assert!(!out.contains("(symmetry-reduced)"), "{tag}:\n{out}");
    }

    // Conversely, when extending the bundled CommunityModule `Bitwise`,
    // `shiftR` is a strict override: `shiftR(1 \div 0, 0)` must raise a
    // division-by-zero error even in default mode (must NOT be erased by
    // certified symmetry).
    let bundled_spec = r#"---- MODULE BundledBitwiseStrict ----
EXTENDS Naturals, Bitwise
CONSTANT Proc
VARIABLE owner
Init == owner \in Proc
Next == owner' \in Proc
Inv  == \E p \in Proc : p = owner \/ shiftR(1 \div 0, 0) = 0
====
"#;
    for (tag, args) in [("bundled-bitwise-default", &[][..]), ("bundled-bitwise-tlc", &["-tlc"][..])] {
        let (code, out) = run_spec(tag, "BundledBitwiseStrict", bundled_spec, cfg, args, &[]);
        assert_eq!(code, 75, "{tag}:\n{out}");
        assert!(out.contains("\\div is 0"), "{tag}:\n{out}");
    }
}

#[test]
fn mixed_let_scope_memo_bug_passes_under_compile_and_paranoid() {
    let spec = r#"---- MODULE MixedLetScopeMemoBug ----
EXTENDS Naturals, Bags
VARIABLE x
Step(Op(_)) ==
  /\ BagOfAll(LAMBDA u : LET y == Op(u) IN y, SetToBag({1})) = SetToBag({2})
  /\ x' = IF x = 2 THEN 0 ELSE 1
Init == x \in {1, 2}
Next == Step(LAMBDA z : z + x)
Inv  == x /= 0
====
"#;
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
    let (code, out) =
        run_spec("mixed-let-scope", "MixedLetScopeMemoBug", spec, cfg, &["-compile"], &[("TLX_PARANOID", "1"), ("TLX_PRERUN_REUSE", "0")]);
    assert_eq!(code, 0, "{out}");
    assert!(out.contains("No error has been found"), "{out}");
}

#[test]
fn let_higher_order_closure_bug_passes_under_compile_and_paranoid() {
    let spec = r#"---- MODULE LetHigherOrderClosureBug ----
EXTENDS Naturals
VARIABLES s, x
Id(z) == z
RECURSIVE Walk(_, _)
Walk(Op(_), n) ==
  LET AddN(z) == z + n
  IN IF n = 2 THEN Walk(AddN, 1) ELSE Op(100)
Init == s = 2 /\ x = 102
Next == s' = s /\ x' = Walk(Id, s)
Inv  == x = 102
====
"#;
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    let (code, out) =
        run_spec("let-closure", "LetHigherOrderClosureBug", spec, cfg, &["-compile"], &[("TLX_PARANOID", "1"), ("TLX_PRERUN_REUSE", "0")]);
    assert_eq!(code, 0, "{out}");
    assert!(out.contains("No error has been found"), "{out}");
}

#[test]
fn unchanged_param_tuple_and_let_work_across_tiers() {
    let spec = r#"---- MODULE UnchangedParamTuple ----
EXTENDS Naturals
VARIABLES x, y
Keep(v) == UNCHANGED v
KeepBox(v) == [x' = 1 /\ y' = 0]_v
Init == x = 0 /\ y = 0
Next ==
  \/ Keep(<<x, y>>)
  \/ UNCHANGED (LET pair == <<x, y>> IN pair)
  \/ KeepBox(<<x, y>>)
Inv == ENABLED Keep(<<x, y>>) /\ x \in {0, 1} /\ y = 0
====
"#;
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    for (tag, args, env) in [
        ("unchanged-interp", &["-interp"][..], &[][..]),
        ("unchanged-tlc", &["-tlc"][..], &[][..]),
        ("unchanged-paranoid", &["-compile"][..], &[("TLX_PARANOID", "1"), ("TLX_PRERUN_REUSE", "0")][..]),
    ] {
        let (code, out) = run_spec(tag, "UnchangedParamTuple", spec, cfg, args, env);
        assert_eq!(code, 0, "{tag}:\n{out}");
        assert!(out.contains("No error has been found"), "{tag}:\n{out}");
    }
}
