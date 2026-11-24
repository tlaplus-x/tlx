//! Differential tests for structural set membership lowering (`RecordSet`,
//! `Product`, `FcnSet`, `Map` in `FcnSet`, and `Cup`) ensuring `-compile`
//! matches `-interp` on type/comparability errors and short-circuiting.

use tlx_testkit::diff::Harness;

fn check_diff(source: &str, cfg: &str, expect_error: bool) {
    let h = Harness::new(source, cfg);
    let report = h.run_reachable(10);
    report.assert_ok(source);
    let (exec, native) = report.tallies.get("invariant Inv").expect("invariant evaluated");
    assert_eq!(exec.wrong + native.wrong + exec.unsupported, 0, "{}", report.render());
    if expect_error {
        assert!(exec.both_fail > 0 && native.both_fail + native.unsupported > 0, "{}", report.render());
    } else {
        assert!(exec.agree > 0 && native.agree + native.unsupported > 0, "{}", report.render());
    }
}

#[test]
fn tuple_in_record_set_preserves_error() {
    let source = "\
---- MODULE StructuralMemberErrorBug ----
EXTENDS Naturals
VARIABLE x
Init == x = <<1>>
Next == UNCHANGED x
Inv == ~(x \\in [a : Nat])
====
";
    check_diff(source, "INIT Init\nNEXT Next\nINVARIANT Inv\n", true);
}

#[test]
fn record_in_product_preserves_error() {
    let source = "\
---- MODULE RecordInProductBug ----
EXTENDS Naturals
VARIABLE x
Init == x = [a |-> 1]
Next == UNCHANGED x
Inv == ~(x \\in (Nat \\X Nat))
====
";
    check_diff(source, "INIT Init\nNEXT Next\nINVARIANT Inv\n", true);
}

#[test]
fn record_earlier_field_error_before_name_mismatch() {
    let source = "\
---- MODULE RecordFieldOrderError ----
EXTENDS Naturals
VARIABLE x
Init == x = [a |-> \"bad\", c |-> 1]
Next == UNCHANGED x
Inv == ~(x \\in [a : Nat, b : Nat])
====
";
    check_diff(source, "INIT Init\nNEXT Next\nINVARIANT Inv\n", true);
}

#[test]
fn fcn_set_incomparable_domain_preserves_error() {
    let record_case = "\
---- MODULE FcnSetRecordDomError ----
EXTENDS Naturals
VARIABLE x
Init == x = [a |-> 1]
Next == UNCHANGED x
Inv == ~(x \\in [{1} -> Nat])
====
";
    check_diff(record_case, "INIT Init\nNEXT Next\nINVARIANT Inv\n", true);

    let tuple_case = "\
---- MODULE FcnSetTupleDomError ----
EXTENDS Naturals
VARIABLE x
Init == x = <<1>>
Next == UNCHANGED x
Inv == ~(x \\in [{\"a\"} -> Nat])
====
";
    check_diff(tuple_case, "INIT Init\nNEXT Next\nINVARIANT Inv\n", true);

    let map_case = "\
---- MODULE FcnSetMapDomError ----
EXTENDS Naturals
VARIABLE f
Init == f \\in {[k \\in {1} |-> 0], [k \\in {1, 2} |-> 0]}
Next == UNCHANGED f
Inv == ~(f \\in [{\"a\"} -> Nat])
====
";
    check_diff(map_case, "INIT Init\nNEXT Next\nINVARIANT Inv\n", true);
}

#[test]
fn cup_membership_preserves_incomparability_and_short_circuit() {
    // Untyped model value in union of incomparable sets: union itself must error.
    let incomparable = "\
---- MODULE CupIncomparableError ----
CONSTANT m
VARIABLE x
Init == x = 1
Next == UNCHANGED x
Inv == ~(m \\in ({x} \\cup {\"a\"}))
====
";
    check_diff(incomparable, "CONSTANT m = m\nINIT Init\nNEXT Next\nINVARIANT Inv\n", true);

    // Reducible left side matches `x = 1`; lazy right side `[a : Nat]` must not be checked.
    let short_circuit = "\
---- MODULE CupLazyShortCircuit ----
EXTENDS Naturals
VARIABLE x
Init == x = 1
Next == UNCHANGED x
Inv == x \\in ({x} \\cup [a : Nat])
====
";
    check_diff(short_circuit, "INIT Init\nNEXT Next\nINVARIANT Inv\n", false);
}
