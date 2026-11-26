use super::*;

#[test]
fn same_rep_preserves_function_domain_witness() {
    use tlx_value::FcnDom;
    let pairs: Arc<[(Value, Value)]> = vec![(Value::Int(0), Value::Int(7))].into();
    let enumerated = Value::Fcn(pairs.clone(), FcnDom::Enumerated);
    let interval = Value::Fcn(pairs, FcnDom::Interval);
    assert!(same_rep(&enumerated, &enumerated.clone()));
    assert!(same_rep(&interval, &interval.clone()));
    assert!(!same_rep(&enumerated, &interval));
    assert!(!same_rep(&interval, &enumerated));
}

fn interpreter() -> (Arc<Interp>, LocalId, Expr) {
    let dir = tlx_testkit::TempDir::new("binding");
    let path = dir.write("Binding.tla", "---- MODULE Binding ----\nId(arg) == arg\nCall == Id(42)\n====\n");
    let mut prog = tlx_sema::Program::load(&path, &[]).unwrap();
    let Some(RootSymbol::Def(def)) = prog.lookup_root("Id") else { panic!("Id") };
    let param = prog.defs[def.idx()].params[0];
    let Some(RootSymbol::Def(call)) = prog.lookup_root("Call") else { panic!("Call") };
    let DefKind::Op(body) = &prog.defs[call.idx()].kind else { panic!("body") };
    let ExprKind::Apply { args, .. } = &*body.kind else { panic!("apply") };
    let argument = args[0].clone();
    let ip = Interp::new(prog, Default::default()).unwrap();
    (ip, param, argument)
}

#[test]
fn synthesized_by_name_arguments_are_owned() {
    let (ip, param, _) = interpreter();
    let args = vec![Expr::new(ExprKind::Num(42), Span::default())];
    let bound = ip.bind_params(&[param], &args, &Env::default(), &Ctx::NONE, Env::default(), true, false).unwrap();
    assert!(matches!(bound.lookup(param), Some(Binding::Thunk(_))));
    drop(args);
    let local = Expr::new(ExprKind::Local(param), Span::default());
    assert_eq!(ip.eval(&local, &bound, &Ctx::NONE).unwrap(), Value::Int(42));
}

#[test]
fn program_arguments_do_not_clone_shared_expressions() {
    let (ip, param, argument) = interpreter();
    let before = Arc::strong_count(&argument.kind);
    let bound =
        ip.bind_params(&[param], std::slice::from_ref(&argument), &Env::default(), &Ctx::NONE, Env::default(), true, false).unwrap();
    assert!(matches!(bound.lookup(param), Some(Binding::Name(..))));
    assert_eq!(Arc::strong_count(&argument.kind), before);
    let cloned = bound.clone();
    drop(argument);
    let local = Expr::new(ExprKind::Local(param), Span::default());
    assert_eq!(ip.eval(&local, &cloned, &Ctx::NONE).unwrap(), Value::Int(42));
}

#[test]
fn rewritten_and_foreign_arguments_use_owned_thunks() {
    let (ip, param, mut argument) = interpreter();
    argument.kind = Arc::new(ExprKind::Num(43));
    let rewritten = ip.bind_by_name(&argument, &Env::default());
    assert!(matches!(rewritten, Binding::Thunk(_)));
    let (foreign, _, foreign_argument) = interpreter();
    let foreign_bound = ip.bind_by_name(&foreign_argument, &Env::default());
    assert!(matches!(foreign_bound, Binding::Thunk(_)));
    drop((argument, foreign, foreign_argument));
    for (binding, expected) in [(rewritten, 43), (foreign_bound, 42)] {
        let bound = Env::default().bind(param, binding);
        let local = Expr::new(ExprKind::Local(param), Span::default());
        assert_eq!(ip.eval(&local, &bound, &Ctx::NONE).unwrap(), Value::Int(expected));
    }
}

#[test]
fn state_arguments_cache_unprimed_reads_and_keep_the_primed_expression() {
    let (ip, param, _) = interpreter();
    let args = [Expr::new(ExprKind::Var(VarId(0)), Span::default())];
    let state = [Value::Int(42)];
    let next = [Some(Value::Int(43))];
    let cx = Ctx { s0: Some(&state), ..Ctx::NONE };
    let bound = ip.bind_params(&[param], &args, &Env::default(), &cx, Env::default(), true, true).unwrap();
    let Some(Binding::Thunk(thunk)) = bound.lookup(param) else { panic!("cached expression") };
    assert!(thunk.memo.as_ref().unwrap().get().is_none());
    let local = Expr::new(ExprKind::Local(param), Span::default());
    assert_eq!(ip.eval(&local, &bound, &cx).unwrap(), Value::Int(42));
    assert_eq!(thunk.memo.as_ref().and_then(|m| m.get()), Some(&Value::Int(42)));
    let primed = Ctx { s1: Some(&next), primed: true, ..cx };
    assert_eq!(ip.eval(&local, &bound, &primed).unwrap(), Value::Int(43));
}

#[test]
fn deferred_argument_errors_are_owned_and_not_memoized() {
    let (ip, param, _) = interpreter();
    let args = vec![Expr::new(ExprKind::Local(LocalId(0)), Span::default())];
    let bound = ip.bind_params(&[param], &args, &Env::default(), &Ctx::NONE, Env::default(), false, true).unwrap();
    let Some(Binding::Thunk(thunk)) = bound.lookup(param) else { panic!("owned thunk") };
    assert!(thunk.memo.is_none());
    drop(args);
    let local = Expr::new(ExprKind::Local(param), Span::default());
    assert!(ip.eval(&local, &bound, &Ctx::NONE).is_err());
}

#[test]
fn state_memo_caches_the_value_per_definition() {
    let memo = StateMemo::default();
    let evals = std::cell::Cell::new(0);
    let value = |v: i64| {
        evals.set(evals.get() + 1);
        Value::Int(v)
    };
    let (d0, d1) = (DefId(0), DefId(1));
    assert_eq!(memo.get_or_eval(d0, || Ok(value(7))).unwrap(), Value::Int(7));
    assert_eq!(memo.get_or_eval(d0, || Ok(value(8))).unwrap(), Value::Int(7));
    assert_eq!(evals.get(), 1, "a known definition must not be re-evaluated");
    assert_eq!(memo.get_or_eval(d1, || Ok(value(9))).unwrap(), Value::Int(9));
    assert_eq!(evals.get(), 2, "the memo is keyed by definition, not one value");
}

#[test]
fn def_cache_over_shares_one_memo_and_reports_missing_primed() {
    let memo = std::rc::Rc::new(StateMemo::default());
    let (d, other) = (DefId(3), DefId(4));
    let mut first = DefCache::over(memo.clone(), None);
    first.seed(d, false, Value::Int(1));
    // A second cache over the same state sees the seeded value: the memo is
    // the state's, not the context's.
    let second = DefCache::over(memo, None);
    assert!(second.knows(d, false));
    assert!(!second.knows(other, false));
    assert!(!second.knows(d, true), "no primed memo was handed out");
}

#[test]
fn def_cache_unprimed_does_not_memoize_primed_values() {
    let (d, other) = (DefId(0), DefId(1));
    let mut cache = DefCache::unprimed();
    cache.seed(d, false, Value::Int(1));
    assert!(cache.knows(d, false));
    assert!(!cache.knows(d, true), "a partial next state has no primed memo");
    // A primed seed turns the primed memo on for this cache only.
    cache.seed(d, true, Value::Int(2));
    assert!(cache.knows(d, true));
    assert!(!cache.knows(other, true));
}

#[test]
fn def_cache_seed_keeps_the_first_value() {
    let d = DefId(0);
    let mut cache = DefCache::unprimed();
    cache.seed(d, false, Value::Int(1));
    cache.seed(d, false, Value::Int(2));
    assert_eq!(cache.current().get_or_eval(d, || unreachable!()).unwrap(), Value::Int(1));
}

#[test]
fn def_cache_from_source_defers_the_lookup_and_shares_it() {
    struct Shared<'a> {
        lookups: &'a std::cell::Cell<u32>,
        memo: std::rc::Rc<StateMemo>,
    }
    impl MemoSource for Shared<'_> {
        fn memo(&self, _next: bool) -> std::rc::Rc<StateMemo> {
            self.lookups.set(self.lookups.get() + 1);
            self.memo.clone()
        }
    }
    let d = DefId(0);
    let lookups = std::cell::Cell::new(0);
    let memo = std::rc::Rc::new(StateMemo::default());
    let source = || Shared { lookups: &lookups, memo: memo.clone() };
    let mut first = DefCache::from_source(Box::new(source()), false);
    assert_eq!(lookups.get(), 0, "a context that reads no definition does not look the memo up");
    first.seed(d, false, Value::Int(1));
    assert_eq!(lookups.get(), 1);
    // The second cache starts from the same source, so it shares the state's
    // memo instead of getting a fresh one.
    let second = DefCache::from_source(Box::new(source()), true);
    assert_eq!(lookups.get(), 1, "still deferred");
    assert!(second.knows(d, false));
    assert_eq!(lookups.get(), 2);
}

#[test]
fn for_each_binding_streams_first_variable_fastest() {
    let dir = tlx_testkit::TempDir::new("stream_order");
    let path = dir.write(
        "StreamOrder.tla",
        "---- MODULE StreamOrder ----\n\
         EXTENDS Naturals\n\
         Big == \\E x, y \\in SUBSET (1..31) : TRUE\n\
         Mixed == \\E x \\in SUBSET (1..2), y \\in {10, 20} : TRUE\n\
         ====\n",
    );
    let mut prog = tlx_sema::Program::load(&path, &[]).unwrap();
    let quant_bounds = |prog: &mut tlx_sema::Program, name: &str| -> (Vec<Bound>, LocalId, LocalId) {
        let Some(RootSymbol::Def(def)) = prog.lookup_root(name) else { panic!("{name}") };
        let DefKind::Op(body) = &prog.defs[def.idx()].kind else { panic!("body") };
        let ExprKind::Quant { bounds, .. } = &*body.kind else { panic!("quant") };
        let mut locals = Vec::new();
        for b in bounds {
            if let BoundVars::Many(ls) = &b.vars {
                locals.extend_from_slice(ls);
            }
        }
        (bounds.clone(), locals[0], locals[1])
    };
    let (big_bounds, bx, by) = quant_bounds(&mut prog, "Big");
    let (mix_bounds, mx, my) = quant_bounds(&mut prog, "Mixed");
    let ip = Interp::new(prog, Default::default()).unwrap();

    // First 5 bindings of `x, y \in SUBSET (1..31)`: `x` varies fastest.
    let mut seen = Vec::new();
    let completed = ip
        .for_each_binding(&big_bounds, &Env::default(), &Ctx::NONE, &mut |env| {
            let x = ip.read_local(bx, env, &Ctx::NONE)?.to_string();
            let y = ip.read_local(by, env, &Ctx::NONE)?.to_string();
            seen.push((x, y));
            Ok(seen.len() < 5)
        })
        .unwrap();
    assert!(!completed, "visitor stopped after 5 bindings");
    assert_eq!(
        seen,
        vec![
            ("{}".into(), "{}".into()),
            ("{1}".into(), "{}".into()),
            ("{2}".into(), "{}".into()),
            ("{3}".into(), "{}".into()),
            ("{4}".into(), "{}".into()),
        ]
    );

    // Exhaustive mixed `x \in SUBSET (1..2), y \in {10, 20}`: first variable fastest.
    let mut mixed = Vec::new();
    let completed = ip
        .for_each_binding(&mix_bounds, &Env::default(), &Ctx::NONE, &mut |env| {
            let x = ip.read_local(mx, env, &Ctx::NONE)?.to_string();
            let y = ip.read_local(my, env, &Ctx::NONE)?.to_string();
            mixed.push((x, y));
            Ok(true)
        })
        .unwrap();
    assert!(completed);
    assert_eq!(
        mixed,
        vec![
            ("{}".into(), "10".into()),
            ("{1}".into(), "10".into()),
            ("{2}".into(), "10".into()),
            ("{1, 2}".into(), "10".into()),
            ("{}".into(), "20".into()),
            ("{1}".into(), "20".into()),
            ("{2}".into(), "20".into()),
            ("{1, 2}".into(), "20".into()),
        ]
    );
}
