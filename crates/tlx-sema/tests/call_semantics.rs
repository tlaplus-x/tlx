//! Regression tests for canonical module origin (`ModuleOrigin`),
//! `Program::is_strict_call_def`, and strict-override argument preservation
//! during HIR normalization (`Normalizer` and `SymNormalizer`).

use tlx_front::cfg;
use tlx_sema::{
    hir::RootSymbol,
    optimize::{phase_projection, symmetry_certificate, SymNormalizer},
    ModuleOrigin, Program,
};

fn load(name: &str, src: &str) -> (tlx_testkit::TempDir, Program) {
    let dir = tlx_testkit::TempDir::new(&format!("call_semantics-{name}"));
    let path = dir.join(format!("{name}.tla"));
    std::fs::write(&path, src).unwrap();
    let prog = Program::load(&path, &[]).unwrap_or_else(|e| panic!("load {name}: {e:?}"));
    (dir, prog)
}

fn def_id(prog: &mut Program, name: &str) -> tlx_sema::hir::DefId {
    match prog.lookup_root(name) {
        Some(RootSymbol::Def(d)) => d,
        other => panic!("expected def {name}, got {other:?}"),
    }
}

#[test]
fn user_bitwise_module_origin_is_user_and_not_strict() {
    let (_dir, mut prog) = load(
        "Bitwise",
        "---- MODULE Bitwise ----\n\
         EXTENDS Naturals\n\
         Xor(a, b) == TRUE\n\
         ====\n",
    );
    let xor = def_id(&mut prog, "Xor");
    assert_eq!(prog.file(prog.defs[xor.idx()].span.file).origin, ModuleOrigin::User);
    assert!(!prog.is_strict_call_def(xor), "user Bitwise.tla must not be misclassified as a CommunityModule override");
}

#[test]
fn bundled_stdlib_and_community_origins_and_strict_defs() {
    let (_dir, mut prog) = load(
        "UseBundled",
        "---- MODULE UseBundled ----\n\
         EXTENDS Naturals, Bags, TLCExt, Bitwise, Functions\n\
         UserOp(a) == TRUE\n\
         ====\n",
    );
    let user_op = def_id(&mut prog, "UserOp");
    let sub_bag = def_id(&mut prog, "SubBag");
    let assert_eq = def_id(&mut prog, "AssertEq");
    let tlc_noop = def_id(&mut prog, "TLCNoOp");
    let tlc_mv = def_id(&mut prog, "TLCModelValue");
    let shift_r = def_id(&mut prog, "shiftR");
    let is_inj = def_id(&mut prog, "IsInjective");
    let range = def_id(&mut prog, "Range");

    assert_eq!(prog.file(prog.defs[user_op.idx()].span.file).origin, ModuleOrigin::User);
    assert_eq!(prog.file(prog.defs[tlc_noop.idx()].span.file).origin, ModuleOrigin::Stdlib);
    assert_eq!(prog.file(prog.defs[shift_r.idx()].span.file).origin, ModuleOrigin::Community);
    assert_eq!(prog.file(prog.defs[is_inj.idx()].span.file).origin, ModuleOrigin::Community);

    assert!(!prog.is_strict_call_def(user_op));
    assert!(!prog.is_strict_call_def(sub_bag));
    assert!(!prog.is_strict_call_def(assert_eq));
    assert!(prog.is_strict_call_def(tlc_noop));
    assert!(prog.is_strict_call_def(tlc_mv));
    assert!(prog.is_strict_call_def(shift_r));
    assert!(prog.is_strict_call_def(is_inj));
    assert!(!prog.is_strict_call_def(range));

    // LET-local definitions inside bundled modules are never strict overrides.
    for (i, _) in prog.defs.iter().enumerate() {
        let d = tlx_sema::hir::DefId(i as u32);
        if prog.def_is_let(d) {
            assert!(!prog.is_strict_call_def(d));
        }
    }
}

#[test]
fn strict_override_conditional_or_unused_arg_is_not_erased() {
    // Bundled `Bitwise!shiftR(n, pos)` is a strict override whose body branches
    // on `pos = 0` (`IF pos = 0 THEN n ELSE LET ... IN shiftR(...)`); its
    // call-by-name inlining must be refused so partial arguments (`1 \div 0`)
    // cannot be erased by `Normalizer` or `SymNormalizer`.
    let spec = r#"---- MODULE StrictErase ----
EXTENDS Naturals, Bitwise
CONSTANT Proc
VARIABLE owner
Init == owner \in Proc
Next == owner' \in Proc
Inv  == \E p \in Proc : p = owner \/ shiftR(1 \div 0, 0) = 0
====
"#;
    let (_dir, mut prog) = load("StrictErase", spec);
    let init = def_id(&mut prog, "Init");
    let next = def_id(&mut prog, "Next");
    let inv = def_id(&mut prog, "Inv");
    let tlx_sema::hir::DefKind::Op(init_e) = prog.defs[init.idx()].kind.clone() else { panic!() };
    let tlx_sema::hir::DefKind::Op(next_e) = prog.defs[next.idx()].kind.clone() else { panic!() };
    let tlx_sema::hir::DefKind::Op(inv_e) = prog.defs[inv.idx()].kind.clone() else { panic!() };

    let mut norm = SymNormalizer::new(&prog);
    assert!(norm.normalize(&inv_e).is_none(), "SymNormalizer must refuse inlining strict shiftR whose parameter is conditional");

    let cfg = cfg::parse_cfg("CONSTANT Proc = {p1, p2}\nINIT Init\nNEXT Next\nINVARIANT Inv\n").unwrap();
    let groups = vec![vec!["p1".to_string(), "p2".to_string()]];
    assert!(
        symmetry_certificate(&prog, &cfg, &init_e, &next_e, std::slice::from_ref(&inv_e), &groups).is_none(),
        "symmetry certification must refuse spec with strict override on 1 \\div 0"
    );
    assert!(
        phase_projection(&prog, &cfg, &init_e, &next_e, &[inv_e]).is_none(),
        "phase projection must refuse spec with strict override on 1 \\div 0"
    );
}
