//! The IR executor reports an error (and the compiled tier then bails out
//! to the interpreter) wherever the generated C does: an error evaluating
//! the index of an EXCEPT, and an unknown union tag when re-encoding or
//! ranking a union value. It must neither swallow the error nor panic.

use std::sync::Arc;

use tlx_compile::exec::fast;
use tlx_compile::ir::{ActionFn, Expr, ExprKind, IndexMap, SlotLayout, Stmt, Ty};
use tlx_compile::types::Typing;
use tlx_eval::Interp;
use tlx_layout::{Layout, Shape};

const SPEC: &str = r#"---- MODULE ExecErrors ----
VARIABLES u, f
Init == u = 0 /\ f = <<0, 0, 0>>
Next == UNCHANGED <<u, f>>
====
"#;

/// The interpreter of the spec, and a typing where `u` is a union of
/// integers 0..1 and booleans, and `f` a triple of integers 0..1.
fn setup(name: &str) -> (Arc<Interp>, Typing) {
    let ip = tlx_testkit::spec::interpreter(name, SPEC, "INIT Init\nNEXT Next\n");
    let bit = Shape::Int { lo: 0, hi: 1 };
    let union = Shape::Union(vec![bit.clone(), Shape::Bool].into());
    let triple = Shape::Tuple(vec![bit.clone(); 3].into());
    (ip, Typing::new(Arc::new(Layout::new(vec![union, triple]))))
}

/// Run `let t0 = value in stop` on state `words` (where variable `u` has
/// union tag `tag`): the executor's result.
fn eval_in(ip: &Arc<Interp>, typing: &Typing, value: Expr, tag: u64) -> Result<(), String> {
    let mut words = vec![0u64; typing.var_offset(1) + typing.words(sid(typing.var_ty(1))) as usize];
    words[typing.var_offset(0)] = tag;
    words[typing.var_offset(0) + 1] = 1;
    let f = ActionFn { name: "test".into(), temps: vec![value.ty], body: Stmt::Let { temp: 0, value, body: Box::new(Stmt::Stop) } };
    let program = fast::Program::new(typing);
    let action = program.action(typing, &f).expect("closure compilation");

    // SAFETY: valid words from the matching encoder/program, with published Dyn handles.
    unsafe { fast::run_action_words(&fast::Run::words(ip, typing, &program, 1), &action, &words, &mut |_| Ok(true)) }
        .map(|_| ())
        .map_err(|error| error.into_message())
}

fn sid(ty: Ty) -> u32 {
    match ty {
        Ty::Enc(s) => s,
        _ => panic!("not encoded"),
    }
}

#[test]
fn except_index_reports_an_index_error() {
    let (ip, mut typing) = setup("except");
    let f = Expr::new(typing.var_ty(1), ExprKind::Var(1));
    let bit = typing.id(&Shape::Int { lo: 0, hi: 1 });
    let fail = |ty| Expr::new(ty, ExprKind::Fail("index failed".into()));
    let value = Expr::new(Ty::Enc(bit), ExprKind::ConstWords(vec![1u64].into()));
    let except = |arg: Expr| {
        let kind = ExprKind::ExceptIndex {
            base: f.clone(),
            arg,
            map: IndexMap::IntRange { lo: 1, n: 3 },
            slot: SlotLayout::Bits(1),
            value: value.clone(),
        };
        Expr::new(f.ty, kind)
    };
    // An index outside the domain leaves the function unchanged (TLC)...
    let outside = Expr::new(Ty::Int, ExprKind::Const(tlx_value::Value::Int(7)));
    assert_eq!(eval_in(&ip, &typing, except(outside), 0), Ok(()));
    // ... but an error evaluating the index is an error.
    assert!(eval_in(&ip, &typing, except(fail(Ty::Int)), 0).is_err());
}

/// `Recode` and `RankUnion` of variable `u` (a union of two arms of two
/// values each).
fn union_exprs(typing: &mut Typing) -> (Expr, Expr) {
    let u = Expr::new(typing.var_ty(0), ExprKind::Var(0));
    let target = typing.id(&Shape::Int { lo: 0, hi: 3 });
    // Codes: 0..1 for the integers, 2..3 for the booleans.
    let recode = Expr::new(
        Ty::Enc(target),
        ExprKind::Recode { x: u.clone(), arm_base: vec![0, 2].into(), table: vec![0, 1, 2, 3].into(), words: 1 },
    );
    let rank = Expr::new(Ty::Int, ExprKind::RankUnion { x: u, arms: vec![Arc::from(vec![2u64]), Arc::from(vec![2u64])].into() });
    (recode, rank)
}

#[test]
fn recode_of_an_unknown_union_tag_is_an_error() {
    let (ip, mut typing) = setup("recode");
    let (recode, _) = union_exprs(&mut typing);
    for tag in [0, 1] {
        assert_eq!(eval_in(&ip, &typing, recode.clone(), tag), Ok(()));
    }
    // A tag beyond the arms (here one whose wrapped-around code would be
    // valid): an error, as in the generated C.
    assert!(eval_in(&ip, &typing, recode, 2).is_err());
}

#[test]
fn rank_of_an_unknown_union_tag_is_an_error() {
    let (ip, mut typing) = setup("rank");
    let (_, rank) = union_exprs(&mut typing);
    for tag in [0, 1] {
        assert_eq!(eval_in(&ip, &typing, rank.clone(), tag), Ok(()));
    }
    // (Not a panic.)
    assert!(eval_in(&ip, &typing, rank, 2).is_err());
}
