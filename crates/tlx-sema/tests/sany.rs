//! SANY's semantic checks (scoping, arities, levels): specs SANY rejects must
//! fail `Program::load` with SANY's message, and close variants SANY accepts
//! must load. Expected messages were checked against SANY
//! (tla2sany.SANY from third_party/tla2tools.jar).

use tlx_sema::Program;

/// Write the modules into a fresh directory and load the first one.
fn load(mods: &[(&str, &str)]) -> Result<Program, Vec<String>> {
    let dir = tlx_testkit::TempDir::new("sany");
    let root = dir.write_modules(mods);
    Program::load(&root, &[]).map_err(|es| es.into_iter().map(|e| e.message).collect())
}

/// A module `M` with `EXTENDS Naturals`, `VARIABLE x` and the given body.
fn spec(body: &str) -> String {
    format!("---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\n{body}\n====\n")
}

#[track_caller]
fn rejects(body: &str, msg: &str) {
    match load(&[("M", &spec(body))]) {
        Ok(_) => panic!("accepted, expected `{msg}`:\n{body}"),
        Err(es) => assert!(es.iter().any(|e| e.contains(msg)), "expected `{msg}`, got {es:?}:\n{body}"),
    }
}

#[track_caller]
fn accepts(body: &str) {
    if let Err(es) = load(&[("M", &spec(body))]) {
        panic!("rejected: {es:?}:\n{body}");
    }
}

#[test]
fn definition_before_use() {
    rejects("Init == x = m1\nm1 == 0", "Unknown operator: `m1'.");
    rejects("F(n) == IF n = 0 THEN 0 ELSE F(n - 1)", "Unknown operator: `F'.");
    rejects("A == LET a == b\n          b == 1 IN a", "Unknown operator: `b'.");
    accepts("RECURSIVE F(_)\nF(n) == IF n = 0 THEN 0 ELSE F(n - 1)");
    accepts("f[n \\in Nat] == IF n = 0 THEN 0 ELSE f[n - 1]");
    accepts("A == LET RECURSIVE G(_)\n         G(n) == IF n = 0 THEN 0 ELSE G(n - 1) IN G(3)");
    // A nested module sees the enclosing module's earlier definitions only.
    rejects("Op == 1\n---- MODULE Inner ----\nB == Op\nC == Op2\n====\nOp2 == 2", "Unknown operator: `Op2'.");
    accepts("Op == 1\n---- MODULE Inner ----\nB == Op\n====");
}

#[test]
fn multiply_defined() {
    rejects("A == \\E x \\in {1} : TRUE", "Multiply-defined symbol 'x'");
    rejects("A == 1\nA == 2", "Multiple declarations or definitions for symbol A.");
    rejects("Init == 1\nA(Init) == 1", "Multiply-defined symbol 'Init'");
    rejects("A == LET a == 1 IN LET a == 2 IN a", "Multiple declarations or definitions for symbol a.");
    rejects("A == \\E y \\in {1} : \\E y \\in {2} : y", "Multiply-defined symbol 'y'");
    rejects("A(a, a) == a", "Multiply-defined symbol 'a'");
    rejects("TRUE == 1", "Symbol TRUE is a built-in operator, and cannot be redefined.");
    // Redefining an imported operator.
    let m = "---- MODULE M ----\nEXTENDS Naturals, Sequences\nLen(s) == 1\n====\n";
    assert!(load(&[("M", m)]).is_err());
    // Disjoint scopes may reuse names.
    accepts("A == (\\E y \\in {1} : y = 1) /\\ (\\E y \\in {2} : y = 2)");
    // Conflicting imports of the same kind and arity: a warning in SANY.
    let m = "---- MODULE M ----\n---- MODULE Inner ----\nNat == TRUE\n====\nINSTANCE Inner\nINSTANCE Naturals\n====\n";
    assert!(load(&[("M", m)]).is_ok());
}

#[test]
fn arities() {
    rejects("Op(a) == a\nA == Op", "The operator Op requires 1 arguments.");
    rejects("Op(a) == a\nA == Op(1, 2)", "The operator Op requires 1 arguments.");
    rejects("D(F(_)) == F(1)\nA == D(1)", "in a position an operator is required");
    rejects("D(F(_)) == F(1)\nG(a, b) == a\nA == D(G)", "Expected arity 1 but found operator of arity 2.");
    rejects("D(F(_)) == F(1)\nA == D(LAMBDA a, b : a)", "Lambda expression with arity 2");
    rejects("D(a) == a\nA == D(LAMBDA a : a)", "LAMBDA expression used where an expression is required.");
    rejects("D(Op(_)) == Op(42)\nA == D(D)", "should be a 1-parameter operator");
    rejects("f[a \\in Nat, b \\in Nat] == a\nA == f[1, 2, 3]", "Function 'f' is defined with 2 parameters, but is applied to 3 arguments.");
    rejects("A == [a |-> 1, a |-> 2]", "Non-unique fields in constructor.");
    accepts("D(F(_)) == F(1)\nG(a) == a\nA == D(G) + D(LAMBDA a : a)\nB == D(SUBSET)");
    accepts("f[a \\in Nat, <<b, c>> \\in Nat \\X Nat] == a\nA == f[1, <<2, 3>>] + f[<<1, <<2, 3>>>>]");
    accepts(r"T(Op(_, _)) == Op(TRUE, FALSE)\nA == T(/\) /\ T(\/)".replace("\\n", "\n").as_str());
}

#[test]
fn recursive_declarations() {
    rejects("RECURSIVE F(_)\nA == 1", "Symbol F declared in RECURSIVE statement but not defined.");
    rejects("RECURSIVE F(_)\nF(a, b) == 1", "Definition of F has different arity than its RECURSIVE declaration.");
    rejects("RECURSIVE F\nCONSTANT c\nF == c", "may not appear within a recursive definition section");
    rejects("RECURSIVE F(_)\nF(a) == a'", "Argument 1 of recursive operator F is primed");
    // The declaration gives the number of parameters; operator parameters
    // are allowed in any position (SANY rejects one in the last position,
    // compat.md D-17).
    accepts("RECURSIVE F(_, _)\nF(G(_), n) == n");
    accepts("RECURSIVE F(_, _)\nF(n, G(_)) == n");
    accepts("RECURSIVE F(_, _)\nF(n, m) == n");
    accepts("RECURSIVE F\nF == 1");
}

#[test]
fn instances() {
    let inner = "---- MODULE I ----\nCONSTANT c\nVARIABLE v\nA == v' = c\n====\n";
    let root = |w: &str| format!("---- MODULE M ----\nVARIABLE x\nJ == INSTANCE I WITH {w}\n====\n");
    let check = |w: &str, msg: Option<&str>| match (load(&[("M", &root(w)), ("I", inner)]), msg) {
        (Ok(_), None) => {}
        (Err(es), Some(m)) => assert!(es.iter().any(|e| e.contains(m)), "{w}: {es:?}"),
        (r, m) => panic!("{w}: expected {m:?}, got {:?}", r.err()),
    };
    check("c <- 1, v <- x", None);
    check("c <- x, v <- x", Some("The level of the expression or operator substituted for 'c' \nmust be at most 0."));
    check("c <- 1, v <- x'", Some("substituted for 'v' \nmust be at most 1."));
    check("c <- 1", Some("Substitution missing for symbol v"));
    check("c <- 1, v <- x, c <- 2", Some("Multiple substitutions for symbol 'c'"));
    check("c <- 1, v <- x, w <- 2", Some("Identifier 'w' is not a legal target of a substitution."));
    // INSTANCE does not import declarations.
    let m = "---- MODULE M ----\nVARIABLE x\nJ == INSTANCE I WITH c <- 1, v <- x\nA == J!c\n====\n";
    let es = load(&[("M", m), ("I", inner)]).err().unwrap();
    assert!(es.iter().any(|e| e.contains("Unknown operator: `J!c'.")), "{es:?}");
    // Anything can be substituted for the constants of a constant module.
    let cmod = "---- MODULE C ----\nCONSTANT c\nop == c\n====\n";
    let m = "---- MODULE M ----\nVARIABLE x\nJ == INSTANCE C WITH c <- x'\nK == INSTANCE C WITH c <- []x\n====\n";
    assert!(load(&[("M", m), ("C", cmod)]).is_ok());
    // ... but not non-Leibniz operators.
    let cmod = "---- MODULE C ----\nCONSTANT F(_)\n====\n";
    let m = "---- MODULE M ----\nVARIABLE x\nop(a) == a'\nINSTANCE C WITH F <- op\n====\n";
    let es = load(&[("M", m), ("C", cmod)]).err().unwrap();
    assert!(es.iter().any(|e| e.contains("A non-Leibniz operator substituted for 'F'")), "{es:?}");
    // The implicit substitution must have the declared arity.
    let cmod = "---- MODULE C ----\nCONSTANT F(_)\nD(a) == F(a)\n====\n";
    let m = "---- MODULE M ----\nF(a, b) == a\nINSTANCE C\n====\n";
    let es = load(&[("M", m), ("C", cmod)]).err().unwrap();
    assert!(es.iter().any(|e| e.contains("An operator must be substituted for symbol 'F', and it must have arity 1.")), "{es:?}");

    // Operator-valued instance parameters: arity and level checks match SANY.
    let hmod = "---- MODULE H ----\nCONSTANT F(_)\nVARIABLE v\nD(a) == F(a)\nBad == F(v')\n====\n";
    let ok = "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nInc(z) == z + 1\nI(G(_)) == INSTANCE H WITH F <- G, v <- x\nA == I(Inc)!D(1) + I(LAMBDA z : z + 2)!D(3)\n====\n";
    assert!(load(&[("M", ok), ("H", hmod)]).is_ok());

    let bad_val = "---- MODULE M ----\nVARIABLE x\nI(G(_)) == INSTANCE H WITH F <- G, v <- x\nA == I(1)!D(1)\n====\n";
    let es = load(&[("M", bad_val), ("H", hmod)]).err().unwrap();
    assert!(es.iter().any(|e| e.contains("in a position an operator is required")), "{es:?}");

    let bad_arity = "---- MODULE M ----\nVARIABLE x\nAdd(a, b) == a\nI(G(_)) == INSTANCE H WITH F <- G, v <- x\nA == I(Add)!D(1)\n====\n";
    let es = load(&[("M", bad_arity), ("H", hmod)]).err().unwrap();
    assert!(es.iter().any(|e| e.contains("Expected arity 1 but found operator of arity 2.")), "{es:?}");

    let bad_lam = "---- MODULE M ----\nVARIABLE x\nI(G(_)) == INSTANCE H WITH F <- G, v <- x\nA == I(LAMBDA a, b : a)!D(1)\n====\n";
    let es = load(&[("M", bad_lam), ("H", hmod)]).err().unwrap();
    assert!(es.iter().any(|e| e.contains("Lambda expression with arity 2")), "{es:?}");

    let bad_level = "---- MODULE M ----\nVARIABLE x\nPrime(a) == a'\nI(G(_)) == INSTANCE H WITH F <- G, v <- x\nA == I(Prime)!Bad\n====\n";
    let es = load(&[("M", bad_level), ("H", hmod)]).err().unwrap();
    assert!(es.iter().any(|e| e.contains("The permitted level of argument 1 of the operator argument 1")), "{es:?}");

    let c0 = "---- MODULE C0 ----\nCONSTANT c\nD == c\n====\n";
    let lam_for_val = "---- MODULE M ----\nI(p) == INSTANCE C0 WITH c <- p\nA == I(LAMBDA a : a)!D\n====\n";
    let es = load(&[("M", lam_for_val), ("C0", c0)]).err().unwrap();
    assert!(es.iter().any(|e| e.contains("LAMBDA expression used where an expression is required.")), "{es:?}");

    // Nested parameterized instance with wrong operator arity is rejected.
    let mid = "---- MODULE Mid ----\nCONSTANT k\nJ(G(_)) == INSTANCE H WITH F <- G, v <- k\n====\n";
    let bad_nested = "---- MODULE M ----\nVARIABLE x\nAdd(a, b) == a\nI(p) == INSTANCE Mid WITH k <- p\nA == I(x)!J(Add)!D(1)\n====\n";
    let es = load(&[("M", bad_nested), ("Mid", mid), ("H", hmod)]).err().unwrap();
    assert!(es.iter().any(|e| e.contains("Expected arity 1 but found operator of arity 2.")), "{es:?}");

    // Qualified operator arguments from parameterized instances: bare `S!Read`
    // has full signature (prefix + own formals), while `S(1)!Pair` with a
    // selector argument is rejected by SANY.
    let src = "---- MODULE Source ----\nCONSTANT k\nRead == k\nPair(v) == <<v, k>>\n====\n";
    let tgt = "---- MODULE Target ----\nCONSTANT F(_)\nResult == F(1)\n====\n";
    let ok_qual_op =
        "---- MODULE M ----\nS(n) == INSTANCE Source WITH k <- n\nI(H(_)) == INSTANCE Target WITH F <- H\nA == I(S!Read)!Result\n====\n";
    assert!(load(&[("M", ok_qual_op), ("Source", src), ("Target", tgt)]).is_ok());

    let bad_sel_arg =
        "---- MODULE M ----\nS(n) == INSTANCE Source WITH k <- n\nI(H(_)) == INSTANCE Target WITH F <- H\nA == I(S(1)!Pair)!Result\n====\n";
    let es = load(&[("M", bad_sel_arg), ("Source", src), ("Target", tgt)]).err().unwrap();
    assert!(es.iter().any(|e| e.contains("Selector `S' should not have argument(s).")), "{es:?}");

    let bad_qual_arity =
        "---- MODULE M ----\nS(n) == INSTANCE Source WITH k <- n\nI(H(_)) == INSTANCE Target WITH F <- H\nA == I(S!Pair)!Result\n====\n";
    let es = load(&[("M", bad_qual_arity), ("Source", src), ("Target", tgt)]).err().unwrap();
    assert!(es.iter().any(|e| e.contains("Expected arity 1 but found operator of arity 2.")), "{es:?}");

    // Inherited operator from declaration-free extended module through parameterized
    // instance has full public signature (prefix + own formals); labeled expression
    // S!Read!HERE keeps S's parameter; value operand S!Read + 1 rejects missing arg.
    let pure = "---- MODULE Pure ----\nEXTENDS Naturals\nTwice(v) == v + v\n====\n";
    let src_ext = "---- MODULE SourceExt ----\nEXTENDS Pure\nCONSTANT k\nRead == HERE::k\n====\n";
    let tgt2 = "---- MODULE Target2 ----\nCONSTANT F(_, _)\nVal == F(10, 3)\n====\n";
    let ok_reexport = "---- MODULE M ----\nS(p) == INSTANCE SourceExt WITH k <- p\nC(G(_, _)) == INSTANCE Target2 WITH F <- G\nI(H(_)) == INSTANCE Target WITH F <- H\nA == C(S!Twice)!Val\nB == I(S!Read!HERE)!Result\n====\n";
    assert!(load(&[("M", ok_reexport), ("SourceExt", src_ext), ("Pure", pure), ("Target2", tgt2), ("Target", tgt)]).is_ok());

    let bad_reexport_arity = "---- MODULE M ----\nS(p) == INSTANCE SourceExt WITH k <- p\nI(H(_)) == INSTANCE Target WITH F <- H\nA == I(S!Twice)!Result\n====\n";
    let es = load(&[("M", bad_reexport_arity), ("SourceExt", src_ext), ("Pure", pure), ("Target", tgt)]).err().unwrap();
    assert!(es.iter().any(|e| e.contains("Expected arity 1 but found operator of arity 2.")), "{es:?}");

    let bad_val_operand = "---- MODULE M ----\nEXTENDS Naturals\nS(n) == INSTANCE Source WITH k <- n\nA == S!Read + 1\n====\n";
    let es = load(&[("M", bad_val_operand), ("Source", src)]).err().unwrap();
    assert!(es.iter().any(|e| e.contains("instance `S` expects 1 argument(s)")), "{es:?}");

    // Level bounds on CONSTANT / VARIABLE substitutions of parameterized
    // instances must be enforced at the call site when the definition uses them.
    let sub_mod = "---- MODULE SubMod ----\nCONSTANT c(_)\nVARIABLE v\nTest == c(0) = v\nUnused == v = 0\n====\n";
    let bad_op_sub_level = "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nIx(G(_)) == INSTANCE SubMod WITH c <- G, v <- x\nRead(a) == x + a\nInv == Ix(Read)!Test\n====\n";
    let es = load(&[("M", bad_op_sub_level), ("SubMod", sub_mod)]).err().unwrap();
    assert!(es.iter().any(|e| e.contains("Level error in applying operator Test:")), "{es:?}");

    let ok_unused_sub_level = "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nIx(G(_)) == INSTANCE SubMod WITH c <- G, v <- x\nRead(a) == x + a\nInv == Ix(Read)!Unused\n====\n";
    assert!(load(&[("M", ok_unused_sub_level), ("SubMod", sub_mod)]).is_ok());

    let val_mod = "---- MODULE ValMod ----\nCONSTANT c\nVARIABLE v\nTestC == c = v\nTestV == v = 0\n====\n";
    let bad_val_sub_level =
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nIx(p) == INSTANCE ValMod WITH c <- p, v <- x\nInv == Ix(x)!TestC\n====\n";
    let es = load(&[("M", bad_val_sub_level), ("ValMod", val_mod)]).err().unwrap();
    assert!(es.iter().any(|e| e.contains("Level error in applying operator TestC:")), "{es:?}");

    let ok_split_cv =
        "---- MODULE M ----\nEXTENDS Naturals\nVARIABLE x\nIx(p) == INSTANCE ValMod WITH c <- p, v <- p\nInv == Ix(x)!TestV\n====\n";
    assert!(load(&[("M", ok_split_cv), ("ValMod", val_mod)]).is_ok());
}

#[test]
fn levels() {
    rejects("ASSUME x = 0", "Level error: assumptions must be level 0 (Constant),\nbut this one has level 1.");
    rejects(
        "A == x'' = x",
        "Level error in applying operator ':\nThe level of argument 1 exceeds the maximum level allowed by the operator.",
    );
    rejects("A == UNCHANGED (x')", "Level error in applying operator UNCHANGED:");
    rejects("A == ENABLED [](x = 1)", "Level error in applying operator ENABLED:");
    rejects("Op(a) == a'\nA == Op(x') = x", "Level error in applying operator Op:");
    rejects("Op(a) == LET B == a' IN B\nA == Op(x')", "Level error in applying operator Op:");
    rejects("A == {[](x = 1)}", "Level error in applying operator $SetEnumerate:");
    rejects("A == CHOOSE y \\in {1} : [](x = y)", "Level error in applying operator $BoundedChoose:");
    rejects("A == [x EXCEPT ![1] = [](x = 1)]", "The level of argument 2 exceeds");
    rejects("A == [][x' = x]_(x')", "Level error in applying operator $SquareAct:");
    rejects("A == WF_x([](x = 1))", "Level error in applying operator $WF:");
    rejects("A == [](x' = x)", "[] followed by action not of form [A]_v.");
    rejects("Op(a) == a\nA == [](Op(x' = x))", "[] followed by action not of form [A]_v.");
    rejects("A == <>(x' = x)", "<> followed by action not of form <<A>>_v.");
    rejects("A == (x' = x) ~> TRUE", "Action used where only temporal formula or state predicate allowed.");
    rejects("A == x' = x /\\ [](x = 0)", "\\land has both temporal formula and action as arguments.");
    rejects("A == /\\ x' = x\n     /\\ [](x = 0)", "Conjunction list has both temporal formula and action as arguments.");
    rejects("A == \\E y \\in {x'} : [](x = y)", "Action-level bound of quantified temporal formula.");
    rejects(
        "Op(F(_)) == F(x')\nG(a) == a'\nA == Op(G)",
        "The permitted level of argument 1 of the operator argument 1 \nmust be at least 2.",
    );
    rejects("apply(F(_), a) == F(a)\nA == apply(', x')", "Level error in applying operator apply:\nThe level of argument 2 exceeds");
    // Accepted by SANY.
    accepts("A == \\E y \\in {x'} : TRUE");
    accepts("A == {y \\in {1} : y' = 1}");
    accepts("A == [](LET y == 1 IN x' = x)");
    accepts("A == [][x' = x]_x /\\ WF_x(x' = x) /\\ []<>(x = 1)");
    accepts("A == CASE [](x = 1) -> 1 [] OTHER -> 2");
    accepts("A == [n \\in {1} |-> [](x = 1)]");
    accepts("A == ENABLED (x' = x) /\\ x' = x");
    accepts("CONSTANT F(_)\nA == F(x') = 1\nB == [](F([](x = 1)))");
    accepts("Op(F(_)) == F(x)\nG(a) == a'\nA == Op(G)");
}

#[test]
fn labels() {
    rejects("A == \\A y \\in {} : lbl(y, y) :: TRUE", "Repeated formal parameter y");
    rejects("f[y \\in {}] == lbl :: 0", "Label lbl must contain formal parameter `y'.");
    rejects("A(y) == lbl(y) :: 0", "Label lbl declares extra parameter(s)  y");
    rejects("A == {lbl :: 0, lbl :: 1}", "Duplicate label `lbl'.");
    rejects("ASSUME lbl :: TRUE", "Label not in definition or proof step.");
    rejects("f[y \\in {}] == y\nA == [f EXCEPT ![0] = lbl :: 0]", "Labels inside EXCEPT clauses are not yet implemented.");
    // Labels inside a label are parameterized by the identifiers bound inside it.
    rejects("A == \\E i \\in {1} : o(i) :: \\E j \\in {2} : n(i, j) :: TRUE", "Label n declares extra parameter(s)  i");
    accepts("A == \\E i \\in {1} : o(i) :: \\E j \\in {2} : n(j) :: TRUE");
    accepts("A == lbl :: lbl :: TRUE");
    accepts("THEOREM T == /\\ l1 :: TRUE\n             /\\ l2 :: TRUE");
}

#[test]
fn program_levels() {
    let mut p = load(&[("M", &spec("S == x + 1\nA == x' = x\nT == [][A]_x\nC == 3"))]).unwrap();
    let level = |p: &mut Program, n: &str| match p.lookup_root(n) {
        Some(tlx_sema::hir::RootSymbol::Def(d)) => p.def_level(d),
        _ => None,
    };
    assert_eq!(level(&mut p, "C"), Some(0));
    assert_eq!(level(&mut p, "S"), Some(1));
    assert_eq!(level(&mut p, "A"), Some(2));
    assert_eq!(level(&mut p, "T"), Some(3));
}

#[test]
fn proofs() {
    // Scopes in proofs: NEW (statement and proof), SUFFICES (rest of the
    // proof), DEFINE, TAKE / PICK, step names; theorem names in own proof.
    accepts(
        "THEOREM T == ASSUME NEW c \\in Nat PROVE c >= 0\n\
         <1>1. c = c BY T\n\
         <1> DEFINE G == c\n\
         <1>2 SUFFICES ASSUME NEW d PROVE G = G\n  OBVIOUS\n\
         <1>3 PICK p \\in Nat : p = d\n\
         <1> QED BY <1>1, <1>3 DEF G",
    );
    rejects("THEOREM TRUE\n<1>1. Undefined\n<1> QED", "Unknown operator: `Undefined'.");
    rejects("THEOREM ASSUME NEW c PROVE TRUE\nTHEOREM c = c", "Unknown operator: `c'.");
    rejects("THEOREM TRUE\n<1>1. HAVE TRUE\n<1>2. <1>1\n<1> QED", "HAVE proof step selected instead of expression.");
    accepts("THEOREM TRUE\n<1>1. TRUE\n<1>2. <1>1\n<1> QED BY <1>1");
    rejects("THEOREM TRUE\n<*>a TRUE\n<*> QED", "<*> and <+> cannot be used for a named step.");
    // USE / HIDE.
    rejects("def == TRUE\nHIDE def", "The only expression allowed as a fact in a HIDE is");
    rejects("THEOREM bar == TRUE\nHIDE bar, TRUE", "The only expression allowed as a fact in a HIDE is");
    accepts("THEOREM bar == TRUE\nHIDE bar\nUSE bar, TRUE");
    rejects("USE DEF DoesNotExist", "Unknown operator: `DoesNotExist'.");
    rejects("USE DEF x", "DEF clause entry should describe a defined operator.");
    // Labels.
    rejects("THEOREM lbl :: TRUE", "Label not in definition or proof step.");
    accepts("THEOREM T == lbl :: TRUE");
    rejects(
        "THEOREM thm == ASSUME ASSUME NEW c \\in {}, lbl :: TRUE PROVE TRUE PROVE TRUE",
        "Label not allowed within scope of declaration in nested ASSUME/PROVE.",
    );
    // RECURSIVE sections.
    rejects("RECURSIVE op\nTHEOREM TRUE\nop == 0", "A THEOREM may not appear within a recursive definition section.");
    rejects("RECURSIVE op\nUSE TRUE\nop == 0", "A USE or HIDE may not appear within a recursive definition section.");
}

#[test]
fn proof_levels() {
    rejects("THEOREM []x\n<1> HAVE x\n<1> QED", "Non-constant TAKE, WITNESS, or HAVE for temporal goal.");
    rejects("THEOREM []x\n<1> TAKE c \\in x\n<1> QED", "Non-constant TAKE, WITNESS, or HAVE for temporal goal.");
    rejects("THEOREM []x\n<1> WITNESS x\n<1> QED", "Non-constant TAKE, WITNESS, or HAVE for temporal goal.");
    rejects("THEOREM []x\n<1> CASE x\n<1> QED", "Non-constant CASE for temporal goal.");
    accepts("THEOREM x = 1\n<1> HAVE x\n<1> QED");
    accepts("THEOREM []x\n<1> HAVE 1\n<1> QED");
    rejects("THEOREM TRUE\n<1> PICK c \\in x : []x\n<1> QED", "Non-constant bound of temporal PICK.");
    rejects("THEOREM ASSUME NEW c \\in []x PROVE TRUE", "Temporal formula used as set.");
}

#[test]
fn subexpression_selectors() {
    // Infix `/\` chains are binary (left-associative); a one-line `/\ a /\ b`
    // is a list of one conjunct.
    accepts("D == 1 = 1 /\\ 2 = 2 /\\ 3 = 3\nA == D!1!2\nB == D!2");
    rejects("D == 1 = 1 /\\ 2 = 2 /\\ 3 = 3\nA == D!3", "out of range");
    rejects("A == LET Q(a) == /\\ a > 1 /\\ a < 3 IN Q(2)!2", "out of range");
    // Operators defined in a LET (`D!1!Op`), named by symbols too, and
    // references used as operator arguments (`!@`, labels without arguments).
    accepts(
        "T(Op(_)) == Op(42)\n\
         U == /\\ LET Op(y) == y + 1 IN 44\n     /\\ TRUE\n\
         A == T(U!1!Op) + U!1!Op(42)\n\
         V == \\A y \\in {} : 2 * y\n\
         B == T(V!@)\n\
         COp(q, p) == CHOOSE z : lab(z) :: LET a ++ b == {a, b, q, p, z} IN <<q, 99 ++ p>>\n\
         O5(F(_, _, _, _, _)) == F(1, 2, 3, 4, 5)\n\
         C == COp(1, 2)!(3)!++(4, 5) = O5(COp!@!++)\n\
         D == COp(1, 2)!lab(3)!:!++(4, 5)\n\
         O3(F(_, _, _)) == F(1, 2, 3)\n\
         E == O3(COp!lab)",
    );
    rejects("V == \\A y \\in {} : 2 * y\nB == V!@", "can only be used as an operator argument");
    rejects("V == \\A y \\in {} : L(y) :: 2 * y\nB == V!L", "label `L` has 1 parameter(s), 0 argument(s) given");
}

#[test]
fn nested_module_let_instance() {
    // SANY quirk: a LET INSTANCE of a nested module defines the module twice.
    rejects("---- MODULE Inner ----\nfoo == 42\n====\nop == LET I == INSTANCE Inner IN I!foo", "Multiply-defined module 'Inner'");
    accepts("---- MODULE Inner ----\nfoo == 42\n====\nI == INSTANCE Inner\nop == I!foo");
}

#[test]
fn modules() {
    // The module must be named after its file.
    let es = load(&[("M", "---- MODULE N ----\n====\n")]).err().unwrap();
    assert!(es[0].contains("File name 'M' does not match the name 'N'"), "{es:?}");
    // Circular dependencies.
    let es = load(&[("A", "---- MODULE A ----\nEXTENDS B\n====\n"), ("B", "---- MODULE B ----\nEXTENDS A\n====\n")]).err().unwrap();
    assert!(es[0].contains("Circular dependency among .tla files"), "{es:?}");
}

#[test]
fn instance_op_level_forwarding() {
    // Forwarding a qualified operator's constant-level parameter bound through
    // a LET helper (both captured-op and captured-arg forms) or SelectSeq must
    // reject state-level arguments, matching SANY.
    let bounds_const = "---- MODULE Bounds ----\nCONSTANT candidate\nVARIABLE limit\nKeep == candidate <= limit\n====\n";
    let bounds_var = "---- MODULE Bounds ----\nVARIABLE candidate, limit\nKeep == candidate <= limit\n====\n";
    rejects(
        &format!(
            "{bounds_const}\
             ---- MODULE Batch ----\nCONSTANT Filter(_)\nPick(s) == LET Apply(a) == Filter(a) IN Apply(s)\n====\n\
             S(i) == INSTANCE Bounds WITH candidate <- i, limit <- x\n\
             B(P(_)) == INSTANCE Batch WITH Filter <- P\n\
             Op == B(S!Keep)!Pick(x)"
        ),
        "exceeds the maximum level allowed by the operator",
    );
    rejects(
        &format!(
            "{bounds_const}\
             ---- MODULE Batch ----\nCONSTANT Filter(_)\nPick(s) == LET Apply(F(_)) == F(s) IN Apply(Filter)\n====\n\
             S(i) == INSTANCE Bounds WITH candidate <- i, limit <- x\n\
             B(P(_)) == INSTANCE Batch WITH Filter <- P\n\
             Op == B(S!Keep)!Pick(x)"
        ),
        "exceeds the maximum level allowed by the operator",
    );
    let seq_reject = load(&[(
        "M",
        &format!(
            "---- MODULE M ----\nEXTENDS Naturals, Sequences\n{bounds_const}\
             ---- MODULE Batch ----\nCONSTANT Filter(_)\nPick(s) == SelectSeq(s, Filter)\n====\n\
             VARIABLE x\n\
             S(i) == INSTANCE Bounds WITH candidate <- i, limit <- x\n\
             B(P(_)) == INSTANCE Batch WITH Filter <- P\n\
             Op == B(S!Keep)!Pick(<<x, x + 1>>)\n===="
        ),
    )])
    .err()
    .expect("SelectSeq with constant-level predicate on state sequence must fail");
    assert!(seq_reject.iter().any(|e| e.contains("exceeds the maximum level allowed by the operator")), "{seq_reject:?}");
    load(&[(
        "M",
        &format!(
            "---- MODULE M ----\nEXTENDS Naturals, Sequences\n{bounds_var}\
             ---- MODULE Batch ----\nCONSTANT Filter(_)\nPick(s) == SelectSeq(s, Filter)\n====\n\
             VARIABLE x\n\
             S(i) == INSTANCE Bounds WITH candidate <- i, limit <- x\n\
             B(P(_)) == INSTANCE Batch WITH Filter <- P\n\
             Op == B(S!Keep)!Pick(<<x, x + 1>>)\n===="
        ),
    )])
    .expect("SelectSeq with variable-substituted predicate on state sequence must pass");
}
