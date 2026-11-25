use std::sync::Arc;

use tlx_layout::{Layout, Shape};
use tlx_value::Value;

use super::*;
use crate::enc::mixed::{Region, RegionCtx, RegionInfo};

fn typing() -> Typing {
    Typing::new(Arc::new(Layout::new(vec![Shape::Int { lo: 0, hi: 2 }])))
}
fn int() -> Expr {
    Expr::new(Ty::Int, ExprKind::Const(Value::Int(0)))
}
fn boolean() -> Expr {
    Expr::new(Ty::Bool, ExprKind::Const(Value::TRUE))
}
fn enc(t: &mut Typing, s: Shape) -> Expr {
    let sid = t.id(&s);
    Expr::new(Ty::Enc(sid), ExprKind::ConstWords(vec![0; t.words(sid) as usize].into()))
}
fn reject(t: &Typing, e: Expr, why: &str) {
    let error = expression(t, &[], &[], &e).unwrap_err();
    assert!(error.contains(why), "expected {why:?}, got {error:?}");
}

#[test]
fn operand_and_result_types() {
    let t = typing();
    for e in [
        Expr::new(Ty::Bool, ExprKind::Const(Value::Int(0))),
        Expr::new(Ty::Int, ExprKind::Not(boolean())),
        Expr::new(Ty::Bool, ExprKind::Not(int())),
        Expr::new(Ty::Bool, ExprKind::Eq(int(), boolean())),
        Expr::new(Ty::Int, ExprKind::If(boolean(), int(), boolean())),
        Expr::new(Ty::Int, ExprKind::IntBin(IntOp::Add, int(), boolean())),
        Expr::new(Ty::Val, ExprKind::Apply(int(), int())),
    ] {
        reject(&t, e, "type mismatch");
    }
}
#[test]
fn shape_ids_and_variable_types() {
    let t = typing();
    reject(&t, Expr::new(Ty::Enc(999), ExprKind::Fail("unused".into())), "unknown shape");
    reject(&t, Expr::new(Ty::Enc(0), ExprKind::Var(999)), "unknown state variable");
    reject(&t, Expr::new(Ty::Int, ExprKind::Var(0)), "type mismatch");
}
#[test]
fn layout_offsets_widths_and_shapes() {
    let mut t = typing();
    Arc::make_mut(&mut t.layout).offsets[0] = usize::MAX;
    assert!(super::typing(&t).unwrap_err().contains("offset"));
    let mut t = typing();
    Arc::make_mut(&mut t.layout).words += 1;
    assert!(super::typing(&t).unwrap_err().contains("width"));
    let mut t = typing();
    t.var_sid[0] = t.id(&Shape::Bool);
    assert!(super::typing(&t).unwrap_err().contains("shape"));
}
#[test]
fn constant_and_concatenation_widths() {
    let t = typing();
    reject(&t, Expr::new(Ty::Enc(0), ExprKind::ConstWords(vec![0, 0].into())), "width");
    let x = Expr::new(Ty::Enc(0), ExprKind::Var(0));
    reject(&t, Expr::new(Ty::Enc(0), ExprKind::Concat(vec![x.clone(), x])), "width");
}
#[test]
fn slice_and_except_ranges() {
    let t = typing();
    let x = Expr::new(Ty::Enc(0), ExprKind::Var(0));
    for loc in [
        FieldLoc::Words(1),
        FieldLoc::Words(usize::MAX),
        FieldLoc::Bits(BitPos::new(1, 0, 2)),
        FieldLoc::Bits(BitPos::new(0, 60, 8)),
        FieldLoc::Bits(BitPos::new(0, 0, 0)),
        FieldLoc::Bits(BitPos::new(0, 0, 64)),
    ] {
        reject(&t, Expr::new(x.ty, ExprKind::Slice { base: x.clone(), loc }), "outside base");
        reject(&t, Expr::new(x.ty, ExprKind::ExceptAt { base: x.clone(), loc, value: x.clone() }), "outside base");
    }
}
#[test]
fn pack_bounds_and_overlaps() {
    let mut t = typing();
    let tup = enc(&mut t, Shape::Tuple(vec![Shape::Bool, Shape::Int { lo: 0, hi: 2 }].into()));
    let b = enc(&mut t, Shape::Bool);
    let x = Expr::new(Ty::Enc(0), ExprKind::Var(0));
    reject(
        &t,
        Expr::new(tup.ty, ExprKind::Pack { locs: vec![FieldLoc::Bits(BitPos::new(0, 63, 1))].into(), parts: vec![b.clone(), x.clone()] }),
        "count mismatch",
    );
    reject(
        &t,
        Expr::new(
            tup.ty,
            ExprKind::Pack {
                locs: vec![FieldLoc::Bits(BitPos::new(0, 62, 2)), FieldLoc::Bits(BitPos::new(0, 61, 2))].into(),
                parts: vec![b.clone(), x.clone()],
            },
        ),
        "overlapping",
    );
    reject(
        &t,
        Expr::new(
            tup.ty,
            ExprKind::Pack {
                locs: vec![FieldLoc::Bits(BitPos::new(1, 63, 1)), FieldLoc::Bits(BitPos::new(0, 61, 2))].into(),
                parts: vec![b, x],
            },
        ),
        "outside target",
    );
}
#[test]
fn index_spans_widths_and_tables() {
    let mut t = typing();
    let x = enc(&mut t, Shape::Tuple(vec![Shape::Int { lo: 0, hi: 2 }; 2].into()));
    let atom = enc(&mut t, Shape::Bool);
    for (arg, map, slot, why) in [
        (int(), IndexMap::IntRange { lo: 0, n: 3 }, SlotLayout::Bits(2), "span"),
        (int(), IndexMap::IntRange { lo: i64::MAX, n: 2 }, SlotLayout::Bits(2), "overflow"),
        (int(), IndexMap::IntRange { lo: 0, n: 2 }, SlotLayout::Words(2), "width"),
        (int(), IndexMap::IntRange { lo: 0, n: 2 }, SlotLayout::Bits(3), "width"),
        (atom.clone(), IndexMap::Table(vec![0, 2].into()), SlotLayout::Bits(2), "outside base"),
        (atom, IndexMap::Table(vec![-2, 0].into()), SlotLayout::Bits(2), "outside base"),
    ] {
        reject(&t, Expr::new(Ty::Enc(0), ExprKind::Index { base: x.clone(), arg, map, slot }), why);
    }
}
#[test]
fn sequences_and_sorted_sets() {
    let mut t = typing();
    let seq = enc(&mut t, Shape::Seq { elem: Box::new(Shape::Int { lo: 0, hi: 2 }), max_len: 3 });
    reject(&t, Expr::new(Ty::Enc(0), ExprKind::SeqIndex { base: seq.clone(), arg: int(), slot: SlotLayout::Words(2) }), "width");
    reject(&t, Expr::new(seq.ty, ExprKind::SeqConcat { a: seq.clone(), b: seq, slot: SlotLayout::Bits(2), max_len: 4 }), "capacity");
    let set = enc(&mut t, Shape::Set { elem: Box::new(Shape::Dyn), max_card: 2 });
    reject(&t, Expr::new(set.ty, ExprKind::SortedOp { op: SetOp::Union, a: set.clone(), b: set, elem_words: 1, max_card: 3 }), "capacity");
}
#[test]
fn union_fields_and_recode_widths() {
    let mut t = typing();
    let x = enc(&mut t, Shape::Union(vec![Shape::Bool, Shape::Int { lo: 0, hi: 2 }].into()));
    reject(&t, Expr::new(Ty::Enc(0), ExprKind::UnionField { base: x.clone(), locs: vec![Some(FieldLoc::Words(0))].into() }), "length");
    reject(
        &t,
        Expr::new(Ty::Int, ExprKind::UnionFieldInt { base: x.clone(), entries: vec![Some((FieldLoc::Words(1), 0)), None].into() }),
        "outside arm",
    );
    reject(&t, Expr::new(Ty::Enc(0), ExprKind::Recode { x, arm_base: vec![0, 2].into(), table: vec![0].into(), words: 0 }), "width");
}
#[test]
fn union_fold_requires_a_bitset_result() {
    let mut t = typing();
    // A set of `Dyn` elements has no bitset universe: its encoding is a sorted
    // array, which the word-wise fold would corrupt.
    let sorted = enc(&mut t, Shape::Set { elem: Box::new(Shape::Dyn), max_card: 2 });
    let member = enc(&mut t, Shape::Set { elem: Box::new(Shape::Bool), max_card: 2 });
    reject(&t, Expr::new(sorted.ty, ExprKind::UnionFold { bind: 0, set: member, body: sorted }), "bitset");
}
#[test]
fn ranks_and_maps() {
    let mut t = typing();
    let x = enc(&mut t, Shape::Tuple(vec![Shape::Bool; 2].into()));
    reject(&t, Expr::new(Ty::Int, ExprKind::RankFlat { x, radices: vec![2, 3].into() }), "radices");
    let scalar = Expr::new(Ty::Enc(0), ExprKind::Var(0));
    reject(&t, Expr::new(Ty::Enc(0), ExprKind::MapGet { base: scalar, rank: int() }), "non-map");
    reject(&t, Expr::new(Ty::Bool, ExprKind::BitMember { set: int(), rank: int() }), "encoded");
}
#[test]
fn temps_definition_type_and_scope() {
    let t = typing();
    let temp = Expr::new(Ty::Int, ExprKind::Temp(0));
    assert!(expression(&t, &[Ty::Int], &[], &temp).unwrap_err().contains("scope"));
    assert!(expression(&t, &[], &[], &temp).unwrap_err().contains("unknown temporary"));
    let bad = Expr::new(Ty::Int, ExprKind::Let { temp: 0, value: boolean(), body: temp.clone() });
    assert!(expression(&t, &[Ty::Int], &[], &bad).unwrap_err().contains("type mismatch"));
    let bound = Expr::new(Ty::Int, ExprKind::Let { temp: 0, value: int(), body: temp.clone() });
    let escaped = Expr::new(Ty::Int, ExprKind::IntBin(IntOp::Add, bound, temp));
    assert!(expression(&t, &[Ty::Int], &[], &escaped).unwrap_err().contains("scope"));
}
#[test]
fn iteration_source_context_and_width() {
    let t = typing();
    let source = Expr::new(Ty::Val, ExprKind::ConstElems { elem: 0, words: vec![0].into(), count: 2 });
    reject(&t, source.clone(), "iteration source used as a value");
    let e = Expr::new(Ty::Bool, ExprKind::Exists { bind: 0, set: source, body: boolean() });
    assert!(expression(&t, &[Ty::Enc(0)], &[], &e).unwrap_err().contains("width/count"));
    let source = Expr::new(Ty::Val, ExprKind::IntRange(int(), int()));
    let e = Expr::new(Ty::Bool, ExprKind::Forall { bind: 0, set: source, body: boolean() });
    assert!(expression(&t, &[Ty::Bool], &[], &e).unwrap_err().contains("type mismatch"));
}
#[test]
fn ordered_set_sources() {
    let mut t = typing();
    let elem = Shape::Int { lo: 0, hi: 100 };
    let set = enc(&mut t, Shape::Set { elem: Box::new(elem.clone()), max_card: 3 });
    let ety = Ty::Enc(t.id(&elem));
    let plan = crate::encoded_order::plan(&elem).expect("an integer has a plan");
    let plan = crate::encoded_order::with_rank_keys(plan, &elem, bitset_universe(&elem).unwrap());
    let ordered = |plan: Arc<[u64]>| Expr::new(Ty::Val, ExprKind::OrderedSet { set: set.clone(), plan });
    let exists = |src: Expr| Expr::new(Ty::Bool, ExprKind::Exists { bind: 0, set: src, body: boolean() });
    expression(&t, &[ety], &[], &exists(ordered(plan.clone()))).expect("a well-formed ordered source");
    reject(&t, ordered(plan.clone()), "iteration source used as a value");
    let mut wide = plan.to_vec();
    wide[1] += 1;
    assert!(expression(&t, &[ety], &[], &exists(ordered(wide.into()))).unwrap_err().contains("width mismatch"));
    let mut keys = plan.to_vec();
    keys.push(5);
    assert!(expression(&t, &[ety], &[], &exists(ordered(keys.into()))).unwrap_err().contains("rank key"));
    assert!(expression(&t, &[ety], &[], &exists(ordered(vec![0, 1].into()))).unwrap_err().contains("too short"));
}

fn check_ordered_plan(elem: Shape, plan: Vec<u64>) -> Result {
    let mut t = typing();
    let set = enc(&mut t, Shape::Set { elem: Box::new(elem.clone()), max_card: 3 });
    let ety = Ty::Enc(t.id(&elem));
    let source = Expr::new(Ty::Val, ExprKind::OrderedSet { set, plan: plan.into() });
    let expr = Expr::new(Ty::Bool, ExprKind::Exists { bind: 0, set: source, body: boolean() });
    expression(&t, &[ety], &[], &expr)
}

#[test]
fn ordered_plan_rejects_malformed_subtrees() {
    let set = Shape::Set { elem: Box::new(Shape::Int { lo: 1, hi: 4 }), max_card: 4 };
    let union = Shape::Union(vec![Shape::Atom(vec![Value::model_value("NULL")].into()), set].into());
    let elem = Shape::Tuple(vec![union, Shape::Int { lo: 0, hi: 10000 }].into());
    let valid = crate::encoded_order::plan(&elem).unwrap().to_vec();
    check_ordered_plan(elem.clone(), valid.clone()).unwrap();
    for (name, offset, value) in [
        ("root opcode", 0, 99),
        ("nested opcode", 8, 99),
        ("wrong shape opcode", 4, 2),
        ("root span", 2, 4),
        ("short child span", 6, 3),
        ("child outside parent", 6, u64::MAX),
        ("missing child", 7, 1),
        ("extra child", 7, 3),
        ("huge child count", 7, u64::MAX),
        ("leaf children", 11, 1),
        ("leaf trailing words", 10, 5),
        ("product child width", 17, 2),
        ("union child width", 9, 2),
        ("bitset child width", 13, 2),
    ] {
        let mut bad = valid.clone();
        bad[offset] = value;
        assert!(check_ordered_plan(elem.clone(), bad).is_err(), "accepted {name}");
    }
    for length in 0..valid.len() {
        assert!(check_ordered_plan(elem.clone(), valid[..length].to_vec()).is_err(), "accepted prefix {length}");
    }
    let mut bad = valid;
    bad.push(0);
    assert!(check_ordered_plan(elem, bad).is_err(), "accepted trailing non-bitset key");
}

#[test]
fn ordered_plan_rank_cardinality_and_permutation() {
    let elem = Shape::Int { lo: 0, hi: 3 };
    for keys in [vec![], vec![0, 1, 2], vec![0, 1, 2, 3, 4], vec![0, 1, 2, 4], vec![0, 1, 1, 3], vec![0, 1, 2, u64::MAX]] {
        let mut plan = vec![0, 1, 4, 0];
        plan.extend(keys);
        assert!(check_ordered_plan(elem.clone(), plan).is_err());
    }
    check_ordered_plan(elem, vec![0, 1, 4, 0, 0, 1, 2, 3]).unwrap();
}

#[test]
fn ordered_plan_wire_fixtures() {
    let scalar = Shape::Int { lo: 0, hi: 10000 };
    let set = Shape::Set { elem: Box::new(Shape::Int { lo: 1, hi: 4 }), max_card: 4 };
    let union = Shape::Union(vec![Shape::Atom(vec![Value::model_value("NULL")].into()), set.clone()].into());
    for (elem, tree) in [
        (scalar.clone(), vec![0, 1, 4, 0]),
        (set.clone(), vec![1, 1, 4, 0]),
        (Shape::Tuple(vec![set, scalar].into()), vec![2, 2, 12, 2, 1, 1, 4, 0, 0, 1, 4, 0]),
        (union, vec![3, 2, 12, 2, 0, 1, 4, 0, 1, 1, 4, 0]),
        (Shape::Tuple(vec![].into()), vec![0, 0, 4, 0]),
    ] {
        let plan = crate::encoded_order::plan(&elem).unwrap();
        assert_eq!(&*plan, tree, "wire bytes for {elem:?}");
        let plan = match bitset_universe(&elem) {
            Some(n) => crate::encoded_order::with_rank_keys(plan, &elem, n),
            None => plan,
        };
        check_ordered_plan(elem, plan.to_vec()).unwrap();
    }
}
#[test]
fn calls_and_recursive_signatures() {
    let mut t = typing();
    t.funcs.push(FnDef { name: "f".into(), params: vec![0], temps: vec![Ty::Int], ret: Ty::Int, body: int(), budgeted: false });
    for (func, args, ret, why) in [
        (1, vec![int()], Ty::Int, "unknown callee"),
        (0, vec![], Ty::Int, "arity"),
        (0, vec![boolean()], Ty::Int, "type mismatch"),
        (0, vec![int()], Ty::Bool, "type mismatch"),
    ] {
        reject(&t, Expr::new(ret, ExprKind::Call { func, args }), why);
    }
    t.funcs[0].body = Expr::new(Ty::Int, ExprKind::Call { func: 0, args: vec![Expr::new(Ty::Int, ExprKind::Temp(0))] });
    t.funcs_changed();
    super::typing(&t).unwrap();
    t.funcs[0].params.push(0);
    t.funcs_changed();
    assert!(super::typing(&t).unwrap_err().contains("duplicate function parameter"));
}
#[test]
fn state_scope_emit_and_repeat() {
    let t = typing();
    let action = |body| ActionFn { name: "test".into(), temps: vec![], body };
    assert!(super::action(&t, &action(Stmt::Emit), Context::Action).unwrap_err().contains("unassigned"));
    assert!(super::action(&t, &action(Stmt::Count(0)), Context::Action).unwrap_err().contains("outside"));
    let p = PredFn {
        name: "p".into(),
        temps: vec![],
        body: Expr::new(Ty::Bool, ExprKind::Eq(Expr::new(Ty::Enc(0), ExprKind::NextVar(0)), Expr::new(Ty::Enc(0), ExprKind::NextVar(0)))),
    };
    assert!(predicate(&t, &p, Context::State).unwrap_err().contains("before assignment"));
    predicate(&t, &p, Context::Transition).unwrap();
    let e = Expr::new(Ty::Bool, ExprKind::Enabled(Box::new(Stmt::Emit)));
    expression(&t, &[], &[], &e).unwrap();
}
#[test]
fn region_inputs_outputs_and_state_contract() {
    let t = typing();
    let mut r = Region {
        expr: Expr::new(Ty::Int, ExprKind::Temp(0)),
        temps: vec![Ty::Int].into(),
        inputs: vec![0],
        ctx: RegionCtx::StatePred,
        assigned: vec![].into(),
        info: RegionInfo::default(),
    };
    region(&t, &r).unwrap();
    r.inputs = vec![0, 0];
    assert!(region(&t, &r).unwrap_err().contains("duplicate"));
    r.inputs.clear();
    assert!(region(&t, &r).unwrap_err().contains("free temporaries"));
    r.inputs = vec![1];
    assert!(region(&t, &r).unwrap_err().contains("unknown temporary"));
    r.inputs = vec![0];
    r.expr.ty = Ty::Bool;
    assert!(region(&t, &r).unwrap_err().contains("type mismatch"));
    r.expr.ty = Ty::Int;
    r.ctx = RegionCtx::Action;
    assert!(region(&t, &r).unwrap_err().contains("assignment contract"));
}
#[test]
fn verified_program_rejects_before_backend_construction() {
    let t = typing();
    let a = [Some(ActionFn { name: "broken".into(), temps: vec![], body: Stmt::Emit })];
    assert!(Program::new(&t, None, &a, &[], &[]).is_err());
    assert!(std::panic::catch_unwind(|| enforce::<()>(Err("malformed IR".into()))).is_err());
}

#[test]
fn unused_shape_hints_are_not_runtime_encodings() {
    let mut t = typing();
    // Lowering can intern a candidate shape before rejecting specialization.
    // It may also annotate an iteration-only node with such a set shape.
    let huge = t.id(&Shape::Set { elem: Box::new(Shape::Int { lo: i32::MIN.into(), hi: i32::MAX.into() }), max_card: 1usize << 32 });
    super::typing(&t).unwrap();
    reject(&t, Expr::new(Ty::Enc(huge), ExprKind::Fail("never reached".into())), "width exceeds");
    let source = Expr::new(Ty::Enc(huge), ExprKind::ConstElems { elem: 0, words: vec![0, 1].into(), count: 2 });
    let e = Expr::new(Ty::Bool, ExprKind::Exists { bind: 0, set: source, body: boolean() });
    expression(&t, &[Ty::Enc(0)], &[], &e).unwrap();
}

#[test]
fn recursive_calls_propagate_state_requirements() {
    let mut t = typing();
    let call = Expr::new(Ty::Enc(0), ExprKind::Call { func: 1, args: vec![] });
    t.funcs.push(FnDef { name: "outer".into(), params: vec![], temps: vec![], ret: Ty::Enc(0), body: call, budgeted: false });
    t.funcs.push(FnDef {
        name: "inner".into(),
        params: vec![],
        temps: vec![],
        ret: Ty::Enc(0),
        body: Expr::new(Ty::Enc(0), ExprKind::NextVar(0)),
        budgeted: false,
    });
    let call = Expr::new(Ty::Enc(0), ExprKind::Call { func: 0, args: vec![] });
    let p = PredFn { name: "p".into(), temps: vec![], body: Expr::new(Ty::Bool, ExprKind::Eq(call.clone(), call.clone())) };
    assert!(predicate(&t, &p, Context::State).unwrap_err().contains("callee reads unassigned"));
    predicate(&t, &p, Context::Transition).unwrap();
    let e = Expr::new(Ty::Bool, ExprKind::Enabled(Box::new(Stmt::Guard { cond: p.body.clone(), then: Box::new(Stmt::Emit) })));
    reject(&t, e, "callee reads unassigned");
    t.funcs[1].body = Expr::new(Ty::Enc(0), ExprKind::Var(0));
    t.funcs_changed();
    let init = ActionFn { name: "init".into(), temps: vec![], body: Stmt::Assign { var: 0, value: call, body: Box::new(Stmt::Emit) } };
    assert!(action(&t, &init, Context::Init).unwrap_err().contains("callee reads unavailable"));
}

#[test]
fn region_call_matches_the_caller_abi() {
    let r = Region {
        expr: int(),
        temps: vec![Ty::Bool].into(),
        inputs: vec![0],
        ctx: RegionCtx::Action,
        assigned: vec![false].into(),
        info: RegionInfo::default(),
    };
    region_call(&r, &[Ty::Bool], Ty::Int, RegionCtx::Action).unwrap();
    assert!(region_call(&r, &[Ty::Int], Ty::Int, RegionCtx::Action).unwrap_err().contains("type mismatch"));
    assert!(region_call(&r, &[Ty::Bool], Ty::Bool, RegionCtx::Action).unwrap_err().contains("type mismatch"));
    assert!(region_call(&r, &[], Ty::Int, RegionCtx::Action).unwrap_err().contains("caller frame"));
    assert!(region_call(&r, &[Ty::Bool], Ty::Int, RegionCtx::Init).unwrap_err().contains("context mismatch"));
}

#[test]
fn composition_assignment_contracts() {
    let t = typing();
    let step = || Stmt::Assign { var: 0, value: int(), body: Box::new(Stmt::Emit) };
    let action = |assigned| ActionFn {
        name: "compose".into(),
        temps: vec![],
        body: Stmt::Compose {
            first: Box::new(step()),
            second: Box::new(step()),
            count: true,
            paths: vec![ComposePath { assigned, rest: Stmt::Emit }],
        },
    };
    assert!(super::action(&t, &action(vec![true]), Context::Action).is_ok());
    assert!(super::action(&t, &action(vec![]), Context::Action).unwrap_err().contains("mask length"));
    assert!(super::action(&t, &action(vec![false]), Context::Action).unwrap_err().contains("mask mismatch"));
}

/// The verification is cached per typing: a change of its functions
/// without `funcs_changed` is caught (tests and paranoid runs recheck).
#[test]
#[should_panic(expected = "stale IR verification")]
fn stale_verification_is_caught() {
    let mut t = typing();
    t.funcs.push(FnDef { name: "f".into(), params: vec![0], temps: vec![Ty::Int], ret: Ty::Int, body: int(), budgeted: false });
    super::typing(&t).unwrap();
    t.funcs[0].params.push(0);
    let _ = super::typing(&t);
}

/// A constant sorted array of composite encodings (`member_enum`) is a
/// word array typed as a sequence of one-word integers.
#[test]
fn sorted_member_of_a_constant_word_array() {
    let mut t = typing();
    let pair = t.id(&Shape::Tuple(vec![Shape::Int { lo: 0, hi: 3 }, Shape::Int { lo: 0, hi: 3 }].into()));
    let words = t.id(&Shape::Seq { elem: Box::new(Shape::Int { lo: i64::MIN, hi: i64::MAX }), max_len: 2 });
    let set = |data: Vec<u64>| Expr::new(Ty::Enc(words), ExprKind::ConstWords(data.into()));
    let elem = Expr::new(Ty::Enc(pair), ExprKind::ConstWords(vec![0].into()));
    let member = |set| Expr::new(Ty::Bool, ExprKind::SortedMember { set, elem: elem.clone(), elem_words: 1 });
    super::expression(&t, &[], &[], &member(set(vec![2, 1, 2]))).unwrap();
    reject(&t, member(set(vec![3, 1, 2])), "sorted word array shorter");
    let wide = Expr::new(Ty::Bool, ExprKind::SortedMember { set: set(vec![1, 1, 0]), elem: elem.clone(), elem_words: 2 });
    reject(&t, wide, "width mismatch");
}

#[test]
fn if_and_then_stmt_contracts() {
    let t = typing();
    let assign0 = |body| Stmt::Assign { var: 0, value: int(), body: Box::new(body) };
    let ok = ActionFn {
        name: "then_ok".into(),
        temps: vec![],
        body: Stmt::Then {
            first: Box::new(Stmt::If { cond: boolean(), then: Box::new(assign0(Stmt::Emit)), els: Box::new(assign0(Stmt::Emit)) }),
            assigned: vec![true],
            rest: Box::new(Stmt::Emit),
        },
    };
    super::action(&t, &ok, Context::Action).unwrap();

    // Non-deterministic `first` is rejected.
    let nondet = ActionFn {
        name: "then_nondet".into(),
        temps: vec![],
        body: Stmt::Then {
            first: Box::new(Stmt::Branches(vec![assign0(Stmt::Emit), assign0(Stmt::Emit)])),
            assigned: vec![true],
            rest: Box::new(Stmt::Emit),
        },
    };
    assert!(super::action(&t, &nondet, Context::Action).unwrap_err().contains("deterministic"));

    // Wrong mask length is rejected.
    let bad_mask = ActionFn {
        name: "then_mask_len".into(),
        temps: vec![],
        body: Stmt::Then { first: Box::new(assign0(Stmt::Emit)), assigned: vec![], rest: Box::new(Stmt::Emit) },
    };
    assert!(super::action(&t, &bad_mask, Context::Action).unwrap_err().contains("mask length"));

    // `first` emitting without assigning a promised variable is rejected.
    let missing_assign = ActionFn {
        name: "then_missing".into(),
        temps: vec![],
        body: Stmt::Then {
            first: Box::new(Stmt::If { cond: boolean(), then: Box::new(assign0(Stmt::Emit)), els: Box::new(Stmt::Emit) }),
            assigned: vec![true],
            rest: Box::new(Stmt::Emit),
        },
    };
    assert!(super::action(&t, &missing_assign, Context::Action).unwrap_err().contains("required assignments"));

    // Temps bound inside `first` are not in scope in `rest`.
    let leaked_temp = ActionFn {
        name: "then_temp_leak".into(),
        temps: vec![Ty::Bool],
        body: Stmt::Then {
            first: Box::new(Stmt::Let { temp: 0, value: boolean(), body: Box::new(assign0(Stmt::Emit)) }),
            assigned: vec![true],
            rest: Box::new(Stmt::Guard { cond: Expr::new(Ty::Bool, ExprKind::Temp(0)), then: Box::new(Stmt::Emit) }),
        },
    };
    assert!(super::action(&t, &leaked_temp, Context::Action).unwrap_err().contains("outside its definition scope"));
}
