use std::sync::Arc;

use super::*;
use crate::ir::{ExprKind as K, IndexMap, SetOp, Stmt};

// Hash arbitrary syntax directly: these payload fixtures intentionally do not
// satisfy type/layout contracts and must never become executable regions.
fn digest(e: Expr) -> (u64, u64) {
    let mut h = Hashing { fnv: FNV_BASIS, second: StableHasher::new(), consts: Default::default() };
    hash_expr(&mut h, &e);
    (h.fnv, h.second.finish())
}

fn int(kind: K) -> Expr {
    Expr::new(Ty::Int, kind)
}

fn var(v: u32) -> Expr {
    int(K::Var(v))
}

/// Pairs of expressions that differ only in one payload that is not a
/// child expression.
fn pairs() -> Vec<(&'static str, Expr, Expr)> {
    let union_field = |o: u32| int(K::UnionField { base: var(0), offsets: Arc::from([Some(1), Some(o), None]) });
    let lookup = |x: i32| int(K::Lookup { x: var(0), table: Arc::from([0, x, -1]) });
    let recode = |x: u64| int(K::Recode { x: var(0), arm_base: Arc::from([0]), table: Arc::from([1, x]), words: 1 });
    let rank_flat = |r: u64| int(K::RankFlat { x: var(0), radices: Arc::from([3, r]) });
    let index = |map: IndexMap| int(K::Index { base: var(0), arg: var(0), map, elem_words: 1 });
    let sorted_op = |max_card: u32| int(K::SortedOp { op: SetOp::Union, a: var(0), b: var(0), elem_words: 1, max_card });
    let map_put = |insert: bool| {
        let absent = if insert { tlx_value::plan::Absent::Insert } else { tlx_value::plan::Absent::Unchanged };
        let plan = crate::ir::MapPutPlan { absent, reject_when_empty: Arc::from([]) };
        int(K::MapPut { base: var(0), rank: var(0), value: var(0), plan })
    };
    let seq_sub = |elem_words: u32| int(K::SeqSub { base: var(0), lo: var(0), hi: var(0), elem_words });
    let map_set = |cond: Option<Expr>| int(K::MapSet { bind: 0, set: var(0), elem: var(0), cond });
    let enabled = |v: u32| Expr::new(Ty::Bool, K::Enabled(Box::new(Stmt::Assign { var: v, value: var(0), body: Box::new(Stmt::Emit) })));
    let tuple = |xs: Vec<Expr>| int(K::Tuple(xs));
    vec![
        ("UnionField offsets", union_field(2), union_field(3)),
        ("Lookup table", lookup(1), lookup(2)),
        ("Recode table", recode(1), recode(2)),
        ("RankFlat radices", rank_flat(2), rank_flat(4)),
        ("IndexMap table", index(IndexMap::Table(Arc::from([0, 1]))), index(IndexMap::Table(Arc::from([1, 0])))),
        ("IndexMap range", index(IndexMap::IntRange { lo: 0, n: 2 }), index(IndexMap::IntRange { lo: 1, n: 2 })),
        ("SortedOp max_card", sorted_op(4), sorted_op(5)),
        ("MapPut insert", map_put(false), map_put(true)),
        ("SeqSub elem_words", seq_sub(1), seq_sub(2)),
        ("MapSet cond", map_set(Some(var(0))), int(K::MapSet { bind: 0, set: var(0), elem: var(0), cond: None })),
        ("ENABLED statement payload", enabled(0), enabled(1)),
        // Pre-order the same nodes: the arity tells them apart.
        ("arity", tuple(vec![tuple(vec![var(0)]), var(1)]), tuple(vec![tuple(vec![var(0), var(1)])])),
    ]
}

#[test]
fn every_payload_is_in_the_digest() {
    for (what, a, b) in pairs() {
        let (ta, tb) = (digest(a.clone()), digest(b));
        assert_ne!(ta.0, tb.0, "{what}: same FNV hash");
        assert_ne!(ta.1, tb.1, "{what}: same digest");
        assert_eq!(ta, digest(a), "{what}: digest not deterministic");
    }
}

/// Constants are digested by contents (computed once per shared value): a
/// long log in many regions does not cost its printed form each time.
#[test]
fn constants_are_digested_by_contents() {
    let log = |n: i64| {
        let lines: Vec<Value> = (0..n).map(|i| Value::record(vec![(tlx_value::Sym::new("i"), Value::Int(i))])).collect();
        Expr::new(Ty::Val, K::Const(Value::tuple(lines)))
    };
    assert_eq!(digest(log(1000)), digest(log(1000)));
    assert_ne!(digest(log(1000)), digest(log(1001)));
    let a = Value::tuple(vec![Value::Int(1), Value::Int(2)]);
    let b = Value::tuple(vec![Value::Int(1), Value::Int(3)]);
    assert_ne!(digest(Expr::new(Ty::Val, K::Const(a))), digest(Expr::new(Ty::Val, K::Const(b))));
}

/// A region the closure compiler cannot lower is cached as `None` (the slots
/// carry no cause; `FastRegions::compile`/`slots` stay the cheap
/// `Option`-per-region tables), and the diagnostic boundary recompiles it to
/// recover the cause (`HostRegions::eval_now`) — the property this protects.
#[test]
fn not_covered_region_slot_caches_only_the_fact_and_recompiling_recovers_the_cause() {
    let mut typing = Typing::new(Arc::new(tlx_layout::Layout::new(vec![tlx_layout::Shape::Int { lo: 0, hi: 10 }])));
    // A function the verifier accepts but the closure compiler rejects: a
    // `Filter` over a boxed `Val` set (the verifier does not shape-check the
    // `Val` state read).
    typing.funcs = vec![crate::ir::FnDef {
        name: "rejected".into(),
        params: Vec::new(),
        temps: vec![Ty::Val],
        ret: Ty::Val,
        body: Expr::new(
            Ty::Val,
            K::Filter { bind: 0, set: Expr::new(Ty::Val, K::Var(0)), pred: Expr::new(Ty::Bool, K::Const(Value::TRUE)) },
        ),
        budgeted: false,
    }];
    typing.funcs_changed();
    let prog = crate::exec::fast::Program::new(&typing);
    let table = RegionTable::new(
        &typing,
        vec![Region {
            expr: Expr::new(Ty::Val, K::Call { func: 0, args: Vec::new() }),
            temps: Arc::from([]),
            inputs: Vec::new(),
            ctx: RegionCtx::StatePred,
            assigned: Arc::from([]),
            info: RegionInfo::default(),
        }],
    );
    // Eager compile (the coverage mask is known before exploration).
    assert!(FastRegions::compile(&table, &typing, &prog)[0].get().is_some_and(Option::is_none), "a not-covered region is cached as None");
    // Lazy slots: empty until first use, then the same fact, still no cause.
    let lazy = FastRegions::slots(&table);
    assert!(lazy[0].get().is_none(), "slots start uninitialized");
    let r = &table.regions()[0];
    assert!(lazy[0].get_or_init(|| prog.expr(&typing, &r.temps, &r.inputs, &r.expr).ok()).is_none());
    // The cause the slot dropped is exactly what `eval_now` recompiles for.
    let why = prog.expr(&typing, &r.temps, &r.inputs, &r.expr).err().unwrap();
    assert_eq!(why, "call of uncompiled function rejected (expected an encoded type, got Val)");
    assert!(format!("region 0: IR closure not covered: {why}").contains("(expected an encoded type, got Val)"));
}

#[test]
fn census_region_json_uses_search_counts_without_initial_predicate_work() {
    let typing = Typing::new(Arc::new(tlx_layout::Layout::new(vec![])));
    let region = Region {
        expr: Expr::new(Ty::Int, K::Const(tlx_value::Value::Int(0))),
        temps: Arc::from([]),
        inputs: vec![],
        ctx: RegionCtx::StatePred,
        assigned: Arc::from([]),
        info: RegionInfo { func: "predicate".into(), ..Default::default() },
    };
    let table = RegionTable::new(&typing, vec![region]);
    let source = table.json_source(&typing);
    assert!(source().contains("\"calls\":0"));
    // All-stage and search-only values deliberately differ. Initial-state
    // predicates have the same RegionCtx as search predicates.
    TALLY.with(|t| {
        let mut t = t.borrow_mut();
        t.counts = vec![[10, 1, 100, 2, 0, 20]];
        t.touched = vec![0];
    });
    assert_eq!(table.drain_counts(), (10, 1));
    let json = source();
    assert!(json.contains("\"calls\":2,\"errors\":0,\"time_s\":0.000000020"), "{json}");
    assert!(table.report(&[]).contains("10 evals"));
    drop(table);
    assert_eq!(source(), json, "the source owns its counters independently of the table");
}
