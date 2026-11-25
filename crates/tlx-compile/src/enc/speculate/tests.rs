use super::*;

/// Whether the search of the module with body `body` (with `Init`,
/// `Next`, and the cfg lines `cfg`) may create strings, its liveness
/// atoms included: the pre-run is faithful.
fn creates_strings(body: &str, cfg: &str) -> bool {
    let src = tlx_testkit::module("S", &format!("EXTENDS Naturals, Sequences, SequencesExt, TLC\n{body}"));
    let m = tlx_testkit::spec::load(&src, &format!("INIT Init\nNEXT Next\n{cfg}"));
    let strings = model_strings(&m);
    search_makes_strings(&m, &strings) || live_makes_strings(&m, &strings)
}

#[test]
fn sequence_operators_on_sequences_create_no_strings() {
    // A queue of records with string fields.
    let queue = "VARIABLE q\nInit == q = <<[t |-> \"a\", v |-> 1]>>\nNext == (q /= <<>> /\\ q' = Tail(q)) \\/ (Len(q) < 3 /\\ q' = q \\o <<[t |-> \"b\", v |-> 2]>>) \\/ (q /= <<>> /\\ q' = SubSeq(q, 1, Len(q) - 1) \\o <<>>)";
    assert!(!creates_strings(queue, ""));
    // A sequence of strings.
    assert!(!creates_strings("VARIABLE q\nInit == q = <<\"ab\", \"c\">>\nNext == q /= <<>> /\\ q' = Tail(q)", ""));
    // A function of sequences, EXCEPT and @.
    assert!(!creates_strings(
        "VARIABLE f\nInit == f = [i \\in 1..2 |-> <<\"a\">>]\nNext == \\E i \\in 1..2 : f[i] /= <<>> /\\ f' = [f EXCEPT ![i] = Tail(@)]",
        ""
    ));
    // A recursive operator on a sequence.
    assert!(!creates_strings("VARIABLE q, n\nRECURSIVE Sum(_)\nSum(s) == IF s = <<>> THEN 0 ELSE Head(s) + Sum(Tail(s))\nInit == q = <<1, 2>> /\\ n = 0\nNext == n' = Sum(q) /\\ UNCHANGED q", ""));
    // An operator argument applied to a sequence.
    assert!(!creates_strings(
        "VARIABLE q\nApp(F(_), s) == F(s)\nInit == q = <<1, 2>>\nNext == q /= <<>> /\\ q' = App(LAMBDA s : Tail(s), q)",
        ""
    ));
    // An action instance's parameter.
    assert!(!creates_strings("VARIABLE q\nA(p) == q' = Tail(p)\nInit == q = <<1>>\nNext == \\E s \\in {<<1, 2>>, <<3>>} : A(s)", ""));
    // An invariant and a liveness property.
    assert!(!creates_strings(
        "VARIABLE q\nInit == q = <<1, 2>>\nNext == UNCHANGED q\nInv == q = <<>> \\/ Len(Tail(q)) >= 0\nLive == <>(Tail(q) = <<2>>)",
        "INVARIANT Inv\nPROPERTY Live\n"
    ));
}

#[test]
fn replace_all_sub_seqs_creates_strings_only_for_strings() {
    // Three strings: the result is a new string (as `\o` of strings).
    assert!(creates_strings("VARIABLE x\nInit == x = \"banana\"\nNext == x' = ReplaceAllSubSeqs(\"x\", \"a\", x)", ""));
    // A constant application also creates a string.
    assert!(creates_strings("VARIABLE q\nInit == q = <<1>>\nNext == q' = ReplaceAllSubSeqs(\"x\", \"a\", \"banana\")", ""));
    // Sequences of elements: the result reuses them, no string is created.
    assert!(!creates_strings("VARIABLE q\nInit == q = <<1, 2>>\nNext == q' = ReplaceAllSubSeqs(<<1>>, <<2>>, q)", ""));
    // Also when the elements themselves are strings.
    assert!(!creates_strings("VARIABLE q\nInit == q = <<\"ab\", \"cd\">>\nNext == q' = ReplaceAllSubSeqs(<<\"x\">>, <<\"ab\">>, q)", ""));
}

#[test]
fn sequence_operators_on_strings_create_strings() {
    // A string variable.
    assert!(creates_strings("VARIABLE x\nInit == x = \"abc\"\nNext == x /= \"\" /\\ x' = Tail(x)", ""));
    // A sequence variable that later holds a string.
    assert!(creates_strings(
        "VARIABLE x, y\nInit == x = <<1>> /\\ y = 0\nNext == (x' = \"ab\" /\\ UNCHANGED y) \\/ (y' = Len(x \\o x) /\\ UNCHANGED x)",
        ""
    ));
    // Assigned through a parameter passed by name.
    assert!(creates_strings(
        "VARIABLE x, y\nSet(v, e) == v' = e\nInit == x = <<1>> /\\ y = <<>>\nNext == Set(x, \"ab\") /\\ y' = SubSeq(x, 1, 1)",
        ""
    ));
    // An element of a sequence.
    assert!(creates_strings("VARIABLE q\nInit == q = <<\"ab\">>\nNext == q' = <<Tail(Head(q))>>", ""));
    // An action instance's parameter.
    assert!(creates_strings("VARIABLE x\nA(p) == x' = Tail(p)\nInit == x = \"\"\nNext == \\E s \\in {\"ab\", \"cd\"} : A(s)", ""));
    // A record field set by EXCEPT.
    assert!(creates_strings("VARIABLE r\nInit == r = [f |-> <<1>>]\nNext == r' = [r EXCEPT !.f = \"ab\"] \\/ r' = [f |-> Tail(r.f)]", ""));
    // A recursive operator on a string.
    assert!(creates_strings("VARIABLE x, n\nRECURSIVE L(_)\nL(s) == IF s = \"\" THEN 0 ELSE 1 + L(Tail(s))\nInit == x = \"ab\" /\\ n = 0\nNext == n' = L(x) /\\ UNCHANGED x", ""));
    // Assigned in the initial predicate through a parameter.
    assert!(creates_strings("VARIABLE x\nSet(v) == v = \"ab\"\nInit == Set(x)\nNext == x /= \"\" /\\ x' = Tail(x)", ""));
    // Assigned by a recursive operator through a primed argument.
    assert!(creates_strings("VARIABLE x, y\nRECURSIVE R(_, _)\nR(m, n) == IF n = 0 THEN m = \"ab\" ELSE R(m, n - 1)\nInit == x = <<1>> /\\ y = <<>>\nNext == R(x', 1) /\\ y' = Tail(x)", ""));
    // A recursive operator applied to a string by its recursion.
    assert!(creates_strings("VARIABLE x, n\nRECURSIVE L(_, _)\nL(s, k) == IF k = 0 THEN Len(Tail(s)) ELSE L(\"ab\", k - 1)\nInit == x = <<1, 2>> /\\ n = 0\nNext == n' = L(x, 1) /\\ UNCHANGED x", ""));
    // An operator argument applied to a string.
    assert!(creates_strings(
        "VARIABLE x\nApp(F(_), s) == F(s)\nInit == x = \"ab\"\nNext == x /= \"\" /\\ x' = App(LAMBDA s : Tail(s), x)",
        ""
    ));
    // A primed variable assigned a string under ENABLED in an invariant.
    assert!(creates_strings(
        "VARIABLE x\nInit == x = <<1>>\nNext == UNCHANGED x\nInv == ENABLED (x' = \"ab\" /\\ Tail(x') = \"b\")",
        "INVARIANT Inv\n"
    ));
    // A liveness atom.
    assert!(creates_strings("VARIABLE x\nInit == x = \"ab\"\nNext == UNCHANGED x\nLive == <>(Tail(x) = \"b\")", "PROPERTY Live\n"));
    // A string constant.
    assert!(creates_strings("CONSTANT C\nVARIABLE x\nInit == x = C\nNext == x /= \"\" /\\ x' = Tail(x)", "CONSTANT C = \"abc\"\n"));
    // Other builtins creating strings.
    assert!(creates_strings("VARIABLE x\nInit == x = 1\nNext == x' = x /\\ ToString(x) /= \"\"", ""));
}

fn load(body: &str, cfg: &str) -> InterpModel {
    let src = tlx_testkit::module("S", &format!("EXTENDS Naturals, Sequences, TLC\n{body}"));
    tlx_testkit::spec::load(&src, &format!("INIT Init\nNEXT Next\n{cfg}"))
}

#[test]
fn syntactic_analysis_sees_arguments_passed_by_name() {
    // The action instance's body sees `Tail(q)` only through its
    // parameter.
    let m = load("VARIABLE q\nA(p) == q' = p\nInit == q = \"ab\"\nNext == \\E s \\in {1} : A(Tail(q))", "");
    let a = &m.actions()[0];
    assert!(StringMakers::new(&m.ip).expr_in(&a.expr, &a.env));
    let m = load("VARIABLE q\nA(p) == q' = p\nInit == q = \"ab\"\nNext == \\E s \\in {1} : A(q)", "");
    let a = &m.actions()[0];
    assert!(!StringMakers::new(&m.ip).expr_in(&a.expr, &a.env));
}

#[test]
fn sequence_definitions_are_materialization_candidates() {
    let names =
        |m: &InterpModel| -> Vec<String> { materialize_candidates(m).iter().map(|d| m.ip.prog.defs[d.idx()].name.to_string()).collect() };
    // `Tail` and `\o` of a queue of numbers create no strings.
    let m = load("VARIABLE q\nRest == Tail(q)\nBoth == q \\o q\nInit == q = <<1, 2>>\nNext == q /= <<>> /\\ q' = Tail(q)\nInv == Len(Rest) < 5 /\\ Len(Both) < 9", "INVARIANT Inv\n");
    let cands = names(&m);
    assert!(cands.contains(&"Rest".to_string()) && cands.contains(&"Both".to_string()), "{cands:?}");
    // Of a string they do.
    let m = load(
        "VARIABLE q\nRest == Tail(q)\nInit == q = \"ab\"\nNext == q /= \"\" /\\ q' = Tail(q)\nInv == Len(Rest) < 5",
        "INVARIANT Inv\n",
    );
    let cands = names(&m);
    assert!(!cands.contains(&"Rest".to_string()), "{cands:?}");
}

#[test]
fn settle_rule_is_a_function_of_cpu_time_and_state_counts() {
    let ms = Duration::from_millis;
    // The last miss at state 3000, 20 ms of CPU time in; 2000 states settle,
    // a quarter of it is 500.
    let (settle, last, found) = (2000, 3000, ms(20));
    // Never before a quarter of `settle` states fit, however long it took.
    assert!(!settle_rule(settle, last + 499, last, found, ms(100_000)));
    // By count: three times the states before the miss.
    assert!(settle_rule(settle, 3 * last, last, found, found));
    // By time: 50 ms of CPU time fitting, and twice the time to find it.
    assert!(!settle_rule(settle, last + 500, last, found, found + ms(49)));
    assert!(settle_rule(settle, last + 500, last, found, found + ms(50)));
    assert!(!settle_rule(settle, last + 500, last, ms(100), ms(299)));
    assert!(settle_rule(settle, last + 500, last, ms(100), ms(300)));
    assert!(!settle_rule(0, last + 5000, last, found, ms(1000)));
    // A loaded machine stretches the wall clock by a factor f without doing
    // more work: the 500 states that took 20 ms of CPU time after the miss
    // read as 20 * f ms of wall time. On wall times the rule settles under
    // load (f = 3: 60 ms) and not on an idle machine (20 ms); on the CPU
    // times it reads, every run gives the idle machine's answer.
    let cpu_fit = ms(20);
    for f in [1u32, 2, 3, 8] {
        let by_wall = settle_rule(settle, last + 500, last, found, found + cpu_fit * f);
        assert_eq!(by_wall, f >= 3, "wall time, load factor {f}");
        assert!(!settle_rule(settle, last + 500, last, found, found + cpu_fit), "CPU time, load factor {f}");
    }
}
