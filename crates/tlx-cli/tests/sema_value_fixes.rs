//! Regression tests for nested module scoping, `!: ` subexpression selector
//! memoization, lazy `FilterSet` streaming, and canonical empty-function
//! union layout.

use std::path::Path;

fn run(dir: &Path, spec: &str, args: &[&str], env: &[(&str, &str)]) -> (i32, String) {
    let mut cmd = tlx_testkit::tlx!();
    cmd.args(["check", spec]).args(args).dir(dir);
    let out = cmd.envs(env.iter().copied()).run();
    (out.code, out.text())
}

#[test]
fn nested_module_collision() {
    let spec = r#"---- MODULE NestedCollision ----
VARIABLE x
---- MODULE A ----
  ---- MODULE Sub ----
  Val == 1
  ====
  IA == INSTANCE Sub
  Get == IA!Val
====
---- MODULE B ----
  ---- MODULE Sub ----
  Val == 2
  ====
  IB == INSTANCE Sub
  Get == IB!Val
====
MB == INSTANCE B
Init == x = MB!Get
Next == UNCHANGED x
Inv  == x = 2
====
"#;
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    let dir = tlx_testkit::TempDir::with_spec("nested_collision", spec, cfg);
    for args in [&["-tlc"][..], &["-compile"][..]] {
        let (code, out) = run(&dir, "NestedCollision.tla", args, &[("TLX_PRERUN_REUSE", "0")]);
        assert_eq!(code, 0, "args={args:?}:\n{out}");
    }
}

#[test]
fn colon_selector_memoization() {
    let spec = r#"---- MODULE ColonSel ----
EXTENDS Naturals
VARIABLE x
D == LET F == 1 IN (F :: 2) + F
Init == x = <<D!F, D!:!F>>
Next == UNCHANGED x
Inv  == x = <<2, 1>>
====
"#;
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    let dir = tlx_testkit::TempDir::with_spec("colon_sel", spec, cfg);
    for args in [&["-tlc"][..], &["-compile"][..]] {
        let (code, out) = run(&dir, "ColonSel.tla", args, &[("TLX_PRERUN_REUSE", "0")]);
        assert_eq!(code, 0, "args={args:?}:\n{out}");
    }
}

#[test]
fn lazy_filter_early_stop() {
    let spec = r#"---- MODULE LazyFilterEarlyStop ----
EXTENDS Naturals, FiniteSets
VARIABLE x
S == {f \in [1..2 -> 0..1] : IF f[1] = 0 THEN TRUE ELSE (1 \div 0 = 0)}
Init == x = Cardinality([S -> {}])
Next == UNCHANGED x
Inv  == x = 0
====
"#;
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    let dir = tlx_testkit::TempDir::with_spec("lazy_filter_early_stop", spec, cfg);
    for args in [&["-tlc"][..], &["-compile"][..]] {
        let (code, out) = run(&dir, "LazyFilterEarlyStop.tla", args, &[("TLX_PRERUN_REUSE", "0")]);
        assert_eq!(code, 0, "args={args:?}:\n{out}");
    }
}

#[test]
fn empty_fcn_union_canonical_compiled() {
    let spec = r#"---- MODULE EmptyFcnUnionBug ----
EXTENDS Naturals, Sequences
VARIABLE x
EmptyMap == [k \in {} |-> 1]
Init == x \in {[k \in {"a"} |-> 1], <<1>>, <<>>}
Next ==
  \/ x' = EmptyMap
  \/ x' = <<>>
  \/ x' = <<1, 2>>
  \/ x' = [k \in {"a"} |-> 2]
Inv == (EmptyMap = <<>>)
====
"#;
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    let dir = tlx_testkit::TempDir::with_spec("empty_fcn_union", spec, cfg);
    let (code_tlc, out_tlc) = run(&dir, "EmptyFcnUnionBug.tla", &["-tlc"], &[]);
    assert_eq!(code_tlc, 0, "{out_tlc}");
    let (code_cmp, out_cmp) = run(&dir, "EmptyFcnUnionBug.tla", &["-compile"], &[("TLX_PRERUN_REUSE", "0"), ("TLX_PARANOID", "1")]);
    assert_eq!(code_cmp, 0, "{out_cmp}");
    assert_eq!(tlx_testkit::cli::counts(&out_cmp), tlx_testkit::cli::counts(&out_tlc), "{out_cmp}");
}
