use std::path::Path;

use tlx_sema::hir::{DefKind, ExprKind, OpRef, RootSymbol};
use tlx_sema::Program;

/// Write modules into a fresh temp dir and load the first one.
fn load(mods: &[(&str, &str)]) -> Program {
    let dir = tlx_testkit::TempDir::new("resolve");
    let root = dir.write_modules(mods);
    let mut p = match Program::load(&root, &[]) {
        Ok(p) => p,
        Err(es) => panic!("load failed: {es:?}"),
    };
    p.resolve_all_root();
    let es = p.take_errors();
    assert!(es.is_empty(), "resolve errors: {es:?}");
    p
}

fn def_body<'a>(p: &'a mut Program, name: &str) -> &'a tlx_sema::hir::Expr {
    let Some(RootSymbol::Def(d)) = p.lookup_root(name) else { panic!("{name} not a def") };
    match &p.defs[d.idx()].kind {
        DefKind::Op(e) => e,
        k => panic!("{name}: {k:?}"),
    }
}

#[test]
fn basic_scoping() {
    let mut p = load(&[(
        "M",
        "---- MODULE M ----\n\
         EXTENDS Naturals\n\
         CONSTANT N\n\
         VARIABLE x\n\
         Inc(a) == a + 1\n\
         Init == x = 0\n\
         Next == x < N /\\ x' = Inc(x)\n\
         Q == \\A i \\in 1..N : \\E j \\in {i} : i = j\n\
         L == LET y == x + 1  z(w) == w + y IN z(2)\n\
         ====\n",
    )]);
    assert_eq!(p.vars.len(), 1);
    assert_eq!(p.consts.len(), 1);
    let b = def_body(&mut p, "Next");
    let ExprKind::And(cs) = &*b.kind else { panic!("{b:?}") };
    assert!(matches!(&*cs[0].kind, ExprKind::Builtin { .. }), "x < N uses native <");
    let b = def_body(&mut p, "L");
    assert!(matches!(&*b.kind, ExprKind::Let { defs, .. } if defs.len() == 2));
}

#[test]
fn hir_arena_indexes_applications_and_nested_expressions() {
    let prog = load(&[("Arena", "---- MODULE Arena ----\nEXTENDS Naturals\nId(arg) == arg\nCall == LET Inner(arg) == Id(arg) IN Inner(42)\nf[index \\in {0}] == Id(index)\nASSUME Id(TRUE)\n====\n")]);
    fn check(prog: &Program, expr: &tlx_sema::hir::Expr) {
        let id = prog.expr_id(expr).expect("program expression is indexed");
        let stored = prog.arena_expr(id);
        assert!(std::sync::Arc::ptr_eq(&expr.kind, &stored.kind));
        assert_eq!(expr.span, stored.span);
        assert_eq!(prog.expr_id(&expr.clone()), Some(id));
        tlx_sema::visit::children(expr, &mut |child| check(prog, child));
    }
    for def in &prog.defs {
        match &def.kind {
            DefKind::Op(body) => check(&prog, body),
            DefKind::Fn { bounds, body } => {
                for bound in bounds {
                    check(&prog, &bound.set);
                }
                check(&prog, body);
            }
            DefKind::Pending => panic!("unresolved definition"),
        }
    }
    for assume in &prog.assumes {
        check(&prog, assume);
    }
    let synthetic = tlx_sema::hir::Expr::new(ExprKind::Num(42), Default::default());
    assert!(prog.expr_id(&synthetic).is_none());
    assert_eq!(std::mem::size_of::<tlx_sema::hir::Expr>(), 32);
}

#[test]
fn higher_order_and_recursion() {
    let mut p = load(&[(
        "M",
        "---- MODULE M ----\n\
         EXTENDS Naturals, Sequences\n\
         Apply(F(_), v) == F(v)\n\
         Dbl(v) == 2 * v\n\
         T == Apply(Dbl, 3)\n\
         U == Apply(LAMBDA q : q + 1, 3)\n\
         RECURSIVE Fact(_)\n\
         Fact(n) == IF n = 0 THEN 1 ELSE n * Fact(n - 1)\n\
         f[i \\in Nat] == IF i = 0 THEN 0 ELSE f[i - 1] + 1\n\
         S == SelectSeq(<<1, 2>>, LAMBDA e : e > 1)\n\
         ====\n",
    )]);
    let b = def_body(&mut p, "T").clone();
    let ExprKind::Apply { args, .. } = &*b.kind else { panic!() };
    assert!(matches!(&*args[0].kind, ExprKind::OpArg(OpRef::Def(_))));
    let Some(RootSymbol::Def(f)) = p.lookup_root("f") else { panic!() };
    assert!(matches!(p.defs[f.idx()].kind, DefKind::Fn { .. }));
}

#[test]
fn instance_with_substitution() {
    let mut p = load(&[
        (
            "Top",
            "---- MODULE Top ----\n\
             EXTENDS Naturals\n\
             VARIABLE a\n\
             I == INSTANCE Inner WITH z <- a, K <- 2\n\
             J(c) == INSTANCE Inner WITH z <- a, K <- c\n\
             Step == I!IStep\n\
             Step2 == J(5)!IStep\n\
             Val == I!Twice(1) + J(1)!Twice(2)\n\
             ====\n",
        ),
        (
            "Inner",
            "---- MODULE Inner ----\n\
             EXTENDS Naturals\n\
             CONSTANT K\n\
             VARIABLE z\n\
             Twice(v) == v * K\n\
             IStep == z' = Twice(z)\n\
             ====\n",
        ),
    ]);
    // Inner's declarations are substituted, never global.
    assert_eq!(p.vars.len(), 1);
    assert_eq!(p.consts.len(), 0);
    let b = def_body(&mut p, "Step2").clone();
    let ExprKind::Apply { op: OpRef::Def(d), args } = &*b.kind else { panic!("{b:?}") };
    assert_eq!(args.len(), 1, "J(5)!IStep passes the instance argument");
    assert_eq!(p.defs[d.idx()].params.len(), 1);
}

#[test]
fn nested_parameterized_instances() {
    let mut p = load(&[
        (
            "Top",
            "---- MODULE Top ----\n\
             EXTENDS Naturals\n\
             VARIABLE x\n\
             I(p1) == INSTANCE Mid WITH a <- p1 * 10, u <- x\n\
             IExpr(p1) == INSTANCE Mid WITH a <- p1 * 10, u <- x * 2\n\
             R2 == I(2)!J(3)!Val\n\
             R3 == I(1)!J(2)!K(3)!LeafVal\n\
             RNested == I(4)!Sub!FromMid\n\
             E3 == IExpr(1)!J(2)!K(3)!CanStep\n\
             WithLet == I(5)!ViaLet\n\
             ====\n",
        ),
        (
            "Mid",
            "---- MODULE Mid ----\n\
             EXTENDS Naturals\n\
             CONSTANT a\n\
             VARIABLE u\n\
             J(p2) == INSTANCE Inner WITH b <- a + p2, v <- u\n\
             ---- MODULE SubMod ----\n\
             FromMid == a + u\n\
             ====\n\
             Sub == INSTANCE SubMod\n\
             ViaLet == LET L == INSTANCE Leaf WITH c <- a + 1, w <- u IN L!LeafVal\n\
             ====\n",
        ),
        (
            "Inner",
            "---- MODULE Inner ----\n\
             EXTENDS Naturals\n\
             CONSTANT b\n\
             VARIABLE v\n\
             K(p3) == INSTANCE Leaf WITH c <- b + p3, w <- v\n\
             Val == b + v\n\
             ====\n",
        ),
        (
            "Leaf",
            "---- MODULE Leaf ----\n\
             EXTENDS Naturals\n\
             CONSTANT c\n\
             VARIABLE w\n\
             LeafVal == c + w\n\
             Step == w' = w + c\n\
             CanStep == ENABLED Step\n\
             ====\n",
        ),
    ]);
    assert_eq!(p.vars.len(), 1);
    assert_eq!(p.consts.len(), 0);
    // No definition left pending (including LET INSTANCE created inside WITH/bodies).
    assert!(p.defs.iter().all(|d| !matches!(d.kind, DefKind::Pending)));

    // 2-level nested parameterized instance passes both instance arguments.
    let (r2, n2) = applied(&mut p, "R2");
    assert_eq!(n2, 2);
    assert_eq!(p.defs[r2.idx()].params.len(), 2);

    // 3-level nested parameterized instance passes all three instance arguments.
    let (r3, n3) = applied(&mut p, "R3");
    assert_eq!(n3, 3);
    assert_eq!(p.defs[r3.idx()].params.len(), 3);

    // Nested module instantiated inside a parameterized instance retains the outer parameter.
    let (rn, nn) = applied(&mut p, "RNested");
    assert_eq!(nn, 1);
    assert_eq!(p.defs[rn.idx()].params.len(), 1);

    // ENABLED inside a 3-level nested parameterized instance with expression variable substitution
    // produces an InstVar reference inside `CanStep`'s body.
    let (can_step, n_e3) = applied(&mut p, "E3");
    assert_eq!(n_e3, 3);
    assert!(p.mentions_inst_var(op_body(&p, can_step)), "expected InstVar under ENABLED in nested instance");
    assert!(!p.inst_vars.is_empty(), "expected an allocated InstVar slot");
}

#[test]
fn enabled_inside_nested_module_preserves_aliased_parent_vars() {
    let mut p = load(&[(
        "Top",
        "---- MODULE Top ----\n\
         EXTENDS Naturals\n\
         ---- MODULE Mid ----\n\
         CONSTANT k\n\
         VARIABLE v, w\n\
         ---- MODULE Inner ----\n\
         Can == ENABLED (v' = k /\\ w' = k + 1)\n\
         ====\n\
         J == INSTANCE Inner\n\
         ====\n\
         VARIABLE x\n\
         I(p) == INSTANCE Mid WITH k <- p, v <- x, w <- x\n\
         Inv == I(2)!J!Can\n\
         ====\n",
    )]);
    let (can_d, argc) = applied(&mut p, "Inv");
    assert_eq!(argc, 1);
    assert!(p.mentions_inst_var(op_body(&p, can_d)), "inherited aliased parent variables must become InstVars under ENABLED");
    assert_eq!(p.inst_vars.len(), 2, "v and w must receive distinct InstVar slots");
}

#[test]
fn operator_valued_instance_parameters() {
    let mut p = load(&[
        (
            "Top",
            "---- MODULE Top ----\n\
             EXTENDS Naturals\n\
             VARIABLE x\n\
             Inc(z) == z + 1\n\
             U(F(_)) == INSTANCE Unary WITH Op <- F\n\
             B(Op(_, _)) == INSTANCE Binary WITH Bin <- Op\n\
             W(F(_)) == INSTANCE Applied WITH c <- F(3)\n\
             Outer(F(_)) == INSTANCE NestHO WITH OutF <- F\n\
             WithLetInst(F(_)) == INSTANCE Applied WITH c <- LET L == INSTANCE Applied WITH c <- F(2) IN L!Val\n\
             R1 == U(Inc)!Main(x)\n\
             R2 == U(LAMBDA z : z * 2)!Main(x)\n\
             R3 == U(LAMBDA z : LET w == z + 1 IN w * 2)!Main(x)\n\
             R4 == B( + )!Wrap(x, 1)\n\
             R5 == B(/\\)!Wrap(TRUE, FALSE)\n\
             R6 == W(Inc)!Val\n\
             R7 == Outer(Inc)!In(LAMBDA z : z * 3)!Combine(x)\n\
             R8 == WithLetInst(Inc)!Val\n\
             ====\n",
        ),
        (
            "Unary",
            "---- MODULE Unary ----\n\
             EXTENDS Naturals\n\
             CONSTANT Op(_)\n\
             Helper(a) == Op(a) + 1\n\
             Main(b) == Helper(b) * 2\n\
             ====\n",
        ),
        (
            "Binary",
            "---- MODULE Binary ----\n\
             CONSTANT Bin(_, _)\n\
             Apply2(a, b) == Bin(a, b)\n\
             Wrap(a, b) == Apply2(a, b)\n\
             ====\n",
        ),
        (
            "Applied",
            "---- MODULE Applied ----\n\
             EXTENDS Naturals\n\
             CONSTANT c\n\
             Val == c + 10\n\
             ====\n",
        ),
        (
            "NestHO",
            "---- MODULE NestHO ----\n\
             EXTENDS Naturals\n\
             CONSTANT OutF(_)\n\
             ---- MODULE InHO ----\n\
             EXTENDS Naturals\n\
             CONSTANT InG(_)\n\
             CONSTANT base\n\
             Combine(v) == InG(v) + base\n\
             ====\n\
             In(H(_)) == INSTANCE InHO WITH InG <- H, base <- OutF(1)\n\
             ====\n",
        ),
    ]);
    assert!(p.defs.iter().all(|d| !matches!(d.kind, DefKind::Pending)));

    // Main(b) calls Helper(b), forwarding the operator-valued instance parameter as
    // `OpArg(OpRef::Param(_))` (not `ExprKind::Local(_)`) with declared arity 1.
    let (main_d, main_argc) = applied(&mut p, "R1");
    assert_eq!(main_argc, 2);
    let inst_param = p.defs[main_d.idx()].params[0];
    assert_eq!(p.locals[inst_param.idx()].arity, 1);
    let ExprKind::Builtin { args: mul_args, .. } = &*op_body(&p, main_d).kind else { panic!() };
    let ExprKind::Apply { args: helper_args, .. } = &*mul_args[0].kind else { panic!() };
    assert!(
        matches!(&*helper_args[0].kind, ExprKind::OpArg(OpRef::Param(l)) if *l == inst_param),
        "cross-def call must forward higher-order instance param as OpArg(Param), got {:?}",
        helper_args[0].kind
    );

    // Nested operator-parameterized instance carries both higher-order params (arity 1 each) plus v (arity 0).
    let (comb_d, comb_argc) = applied(&mut p, "R7");
    assert_eq!(comb_argc, 3);
    assert_eq!(p.locals[p.defs[comb_d.idx()].params[0].idx()].arity, 1);
    assert_eq!(p.locals[p.defs[comb_d.idx()].params[1].idx()].arity, 1);
    assert_eq!(p.locals[p.defs[comb_d.idx()].params[2].idx()].arity, 0);
}

#[test]
fn anonymous_instance_and_local() {
    load(&[
        (
            "Top",
            "---- MODULE Top ----\n\
             VARIABLE a\n\
             INSTANCE Inner WITH z <- a\n\
             LOCAL Helper == 1\n\
             X == IStep /\\ Helper = 1\n\
             ====\n",
        ),
        (
            "Inner",
            "---- MODULE Inner ----\n\
             LOCAL INSTANCE Naturals\n\
             VARIABLE z\n\
             IStep == z' = z + 1\n\
             ====\n",
        ),
    ]);
}

/// The errors of loading and resolving the module at `path`.
fn load_errors(path: &Path) -> Vec<tlx_sema::SemaError> {
    match Program::load(path, &[]) {
        Ok(mut p) => {
            p.resolve_all_root();
            p.take_errors()
        }
        Err(es) => es,
    }
}

#[test]
fn unknown_identifier_is_error() {
    let dir = tlx_testkit::TempDir::new("sema-unknown");
    let f = dir.write("M.tla", "---- MODULE M ----\nEXTENDS Naturals\nX == y + 1\n====\n");
    let es = load_errors(&f);
    assert!(es.iter().any(|e| e.message == "Unknown operator: `y'."), "{es:?}");
}

/// `Apply { op: Def(d), args }` of a definition body: (d, number of args).
fn applied(p: &mut Program, name: &str) -> (tlx_sema::hir::DefId, usize) {
    let b = def_body(p, name).clone();
    let ExprKind::Apply { op: OpRef::Def(d), args } = &*b.kind else { panic!("{name}: {b:?}") };
    (*d, args.len())
}

fn op_body(p: &Program, d: tlx_sema::hir::DefId) -> &tlx_sema::hir::Expr {
    match &p.defs[d.idx()].kind {
        DefKind::Op(e) => e,
        k => panic!("{k:?}"),
    }
}

#[test]
fn subexpression_selectors() {
    let mut p = load(&[(
        "M",
        "---- MODULE M ----\n\
         EXTENDS Naturals\n\
         VARIABLE x\n\
         Inv == /\\ x = 0\n\
         \x20      /\\ x < 7\n\
         \x20      /\\ L:: x > 5\n\
         A == Inv!2\n\
         A2 == Inv!2\n\
         B == Inv!L\n\
         C == Inv!:\n\
         D == Inv!3!1\n\
         Op(a) == /\\ a > 0\n\
         \x20        /\\ IF a = 1 THEN x ELSE a + 2\n\
         E == Op(1)!2\n\
         F == Op(1)!2!3!1\n\
         THEOREM Thm == x \\in {0}\n\
         G == Thm!:\n\
         H == LET Q(a) == /\\ a > 1 /\\ a < 3 IN Q(2)!1!2\n\
         K == \\A v \\in {1} : LET R == /\\ v > 1 /\\ P:: v < 3 IN R!P /\\ R!1\n\
         ====\n",
    )]);
    let (a, n) = applied(&mut p, "A");
    assert_eq!(n, 0);
    assert_eq!(&*p.defs[a.idx()].name, "Inv!2");
    assert!(matches!(&*op_body(&p, a).kind, ExprKind::Builtin { .. }), "x < 7");
    assert_eq!(applied(&mut p, "A2").0, a, "synthetic definitions are shared");
    let (b, _) = applied(&mut p, "B");
    assert_eq!(&*p.defs[b.idx()].name, "Inv!L");
    let (c, _) = applied(&mut p, "C");
    let Some(RootSymbol::Def(inv)) = p.lookup_root("Inv") else { panic!() };
    assert_eq!(c, inv, "`!:` is the definition itself");
    // `Inv!3` is the labeled conjunct; its first operand is x.
    let (d, _) = applied(&mut p, "D");
    assert!(matches!(&*op_body(&p, d).kind, ExprKind::Var(_)));
    // Operator arguments are passed to the synthetic definition.
    let (e, n) = applied(&mut p, "E");
    assert_eq!(n, 1);
    assert_eq!(p.defs[e.idx()].params.len(), 1);
    assert!(matches!(&*op_body(&p, e).kind, ExprKind::If { .. }));
    let (f, n) = applied(&mut p, "F");
    assert_eq!(n, 1);
    // `a` of `a + 2` (the ELSE branch), i.e. the synthetic definition's parameter.
    assert!(matches!(&*op_body(&p, f).kind, ExprKind::Local(l) if *l == p.defs[f.idx()].params[0]));
    let (g, _) = applied(&mut p, "G");
    let Some(RootSymbol::Def(thm)) = p.lookup_root("Thm") else { panic!() };
    assert_eq!(g, thm);
    // LET definitions (also under a binder of the enclosing expression); the
    // one-line `/\ a > 1 /\ a < 3` is a list of one (infix) conjunct.
    let h = def_body(&mut p, "H").clone();
    let ExprKind::Let { body, .. } = &*h.kind else { panic!("{h:?}") };
    let ExprKind::Apply { op: OpRef::Def(q2), args } = &*body.kind else { panic!() };
    assert_eq!(args.len(), 1);
    assert!(p.def_is_let(*q2));
    def_body(&mut p, "K");
}

#[test]
fn subexpression_selectors_through_instance() {
    let mut p = load(&[
        (
            "Top",
            "---- MODULE Top ----\n\
             EXTENDS Naturals\n\
             VARIABLE a\n\
             I == INSTANCE Inner WITH z <- a\n\
             J(c) == INSTANCE Inner WITH z <- c\n\
             S1 == I!Inv!2\n\
             S2 == J(5)!Inv!2\n\
             S3 == J(5)!Inv!P\n\
             S4 == J(5)!Inv!P!:\n\
             S5 == J(5)!Op(1)!1\n\
             S6 == I!Inv!P\n\
             S7 == I!Inv!:\n\
             ====\n",
        ),
        (
            "Inner",
            "---- MODULE Inner ----\n\
             EXTENDS Naturals\n\
             VARIABLE z\n\
             Inv == /\\ z \\in Nat\n\
             \x20      /\\ P:: z > 0\n\
             Op(v) == z + v > 2\n\
             ====\n",
        ),
    ]);
    let (s1, n) = applied(&mut p, "S1");
    assert_eq!(n, 0);
    assert_eq!(&*p.defs[s1.idx()].name, "Inv!2");
    // The substitution z <- a is applied inside the synthetic definition.
    let ExprKind::Builtin { args, .. } = &*op_body(&p, s1).kind else { panic!() };
    assert!(matches!(&*args[0].kind, ExprKind::Var(_)));
    let (s2, n) = applied(&mut p, "S2");
    assert_eq!(n, 1, "instance argument");
    assert_eq!(p.defs[s2.idx()].params.len(), 1);
    let (s3, _) = applied(&mut p, "S3");
    let (s4, _) = applied(&mut p, "S4");
    assert_eq!(s3, s4);
    assert_ne!(s2, s3, "`Inv!2` and `Inv!P` are different paths");
    let (s5, n) = applied(&mut p, "S5");
    assert_eq!(n, 2, "instance argument and operator argument");
    assert_eq!(p.defs[s5.idx()].params.len(), 2);
    let (s6, n) = applied(&mut p, "S6");
    assert_eq!(n, 0);
    assert_ne!(s6, s3, "different instance contexts");
    let (s7, _) = applied(&mut p, "S7");
    assert_eq!(&*p.defs[s7.idx()].name, "Inv");
}

#[test]
fn subexpression_selector_errors() {
    let dir = tlx_testkit::TempDir::new("sema-subexpr");
    let cases = [
        ("Q == \\A i \\in {1} : i = 0\nX == Q!2", "out of range"),
        ("Q == \\A i \\in {1} : i = 0\nX == Q!(1, 2)", "selector with 2 argument(s)"),
        ("Q == \\A i \\in {1} : L(i):: i = 0\nX == Q!L", "label `L` has 1 parameter(s), 0 argument(s) given"),
        ("Q == \\A i \\in {1} : L:: i = 0\nX == Q!L", "Label L must contain formal parameter `i'."),
        ("Q == \\A i \\in {1} : i = 0\nX == Q!@", "can only be used as an operator argument"),
        ("Q == /\\ TRUE /\\ FALSE\nX == Q!3", "out of range"),
        ("Q == /\\ TRUE /\\ FALSE\nX == Q!Nope", "label `Nope` not found"),
        ("Q == LET R == L:: TRUE IN R\nX == Q!L", "not found"),
        ("X == Undefined!1", "Unknown operator: `Undefined'."),
    ];
    for (i, (body, msg)) in cases.iter().enumerate() {
        let f = dir.write(&format!("M{i}.tla"), &format!("---- MODULE M{i} ----\n{body}\n====\n"));
        let es = load_errors(&f);
        assert!(es.iter().any(|e| e.message.contains(msg)), "{body}: {es:?}");
    }
}

/// Every exhaustive-search model in the tlaplus/Examples corpus must resolve,
/// including all names referenced by its .cfg.
#[test]
fn corpus_resolves() {
    let Some(ex) = tlx_testkit::require_third_party("corpus_resolves", "Examples/specifications") else {
        return;
    };
    let search = tlx_testkit::library_paths();
    // Known gaps; currently none.
    let known: [&str; 0] = [];
    let mut models = Vec::new();
    for entry in std::fs::read_dir(&ex).unwrap() {
        let manifest = entry.unwrap().path().join("manifest.json");
        let Ok(text) = std::fs::read_to_string(&manifest) else { continue };
        // Minimal JSON scraping: pair each module path with following .cfg model paths.
        let mut cur_tla: Option<String> = None;
        for line in text.lines() {
            let line = line.trim();
            if let Some(rest) = line.strip_prefix("\"path\": \"") {
                let path = rest.trim_end_matches(['"', ',']).to_string();
                if path.ends_with(".tla") {
                    cur_tla = Some(path);
                } else if path.ends_with(".cfg") {
                    if let Some(t) = &cur_tla {
                        models.push((t.clone(), path));
                    }
                }
            }
        }
    }
    models.sort();
    let root = ex.parent().expect("Examples").to_path_buf();
    let mut failures = Vec::new();
    for (tla, cfg) in &models {
        if std::env::var("TLX_TRACE").is_ok() {
            eprintln!("model {cfg}");
        }
        let r = (|| -> Result<(), String> {
            let cfg_text = std::fs::read_to_string(root.join(cfg)).map_err(|e| e.to_string())?;
            let cfg = tlx_front::cfg::parse_cfg(&cfg_text).map_err(|e| format!("cfg: {e:?}"))?;
            let mut p = Program::load(&root.join(tla), &search).map_err(|es| {
                format!(
                    "load: {}",
                    es.iter().map(|e| format!("{}:{} {}", e.span.line, e.span.col, e.message)).collect::<Vec<_>>().join("; ")
                )
            })?;
            let mut names: Vec<&String> = Vec::new();
            names.extend(cfg.init.iter());
            names.extend(cfg.next.iter());
            names.extend(cfg.specification.iter());
            names.extend(cfg.invariants.iter());
            names.extend(cfg.properties.iter());
            names.extend(cfg.constraints.iter());
            names.extend(cfg.action_constraints.iter());
            for n in names {
                if p.lookup_root(n).is_none() {
                    return Err(format!("cfg name `{n}` not found"));
                }
            }
            p.resolve_all_root();
            let es = p.take_errors();
            if !es.is_empty() {
                let e = &es[0];
                let file = p.file(e.span.file).path.display().to_string();
                return Err(format!("{} error(s), first: {file}:{}:{} {}", es.len(), e.span.line, e.span.col, e.message));
            }
            Ok(())
        })();
        match r {
            Err(e) if !known.contains(&cfg.as_str()) => failures.push(format!("{cfg}: {e}")),
            Ok(()) if known.contains(&cfg.as_str()) => failures.push(format!("{cfg}: unexpectedly passes; remove from known gaps")),
            _ => {}
        }
    }
    eprintln!("{} models, {} failures", models.len(), failures.len());
    for f in &failures {
        eprintln!("  {f}");
    }
    assert!(failures.is_empty());
}
