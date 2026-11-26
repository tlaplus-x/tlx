use std::sync::Arc;

use tlx_eval::env::Env;
use tlx_eval::eval::Ctx;
use tlx_eval::{Interp, InterpModel};
use tlx_runtime::{explore, Options, Outcome};
use tlx_sema::hir::{ExprKind, OpRef, RootSymbol};
use tlx_sema::Program;

fn write_spec(name: &str, body: &str) -> (tlx_testkit::TempDir, std::path::PathBuf) {
    let dir = tlx_testkit::TempDir::new("eval");
    let path = dir.write(&format!("{name}.tla"), &tlx_testkit::module(name, body));
    (dir, path)
}

fn interp(body: &str, cfg: &str) -> Arc<Interp> {
    let (_dir, path) = write_spec("M", body);
    let prog = Program::load(&path, &[]).unwrap_or_else(|e| panic!("{e:?}"));
    let cfg = tlx_front::cfg::parse_cfg(cfg).unwrap();
    Interp::new(prog, cfg).unwrap_or_else(|e| panic!("{e}"))
}

/// Evaluate the constant definitions `T1 .. Tn` and return their printed values.
fn eval_defs(body: &str, names: &[&str]) -> Vec<String> {
    let mut defs = String::from("EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC\n");
    defs.push_str(body);
    let (_dir, path) = write_spec("M", &defs);
    let mut prog = Program::load(&path, &[]).unwrap_or_else(|e| panic!("{e:?}"));
    let ids: Vec<_> = names
        .iter()
        .map(|n| match prog.lookup_root(n) {
            Some(RootSymbol::Def(d)) => d,
            _ => panic!("{n} not defined"),
        })
        .collect();
    let ip = Interp::new(prog, Default::default()).unwrap_or_else(|e| panic!("{e}"));
    ids.iter()
        .map(|d| {
            let e = tlx_sema::hir::Expr::new(ExprKind::Apply { op: OpRef::Def(*d), args: vec![] }, Default::default());
            match ip.eval(&e, &Env::default(), &Ctx::NONE) {
                Ok(v) => v.to_string(),
                Err(e) => format!("ERROR: {e}"),
            }
        })
        .collect()
}

#[test]
fn constant_expressions() {
    let cases: &[(&str, &str)] = &[
        ("1 + 2 * 3", "7"),
        ("{3, 1, 2} \\cup {5}", "{1, 2, 3, 5}"),
        ("CHOOSE x \\in {3, 1, 2} : TRUE", "1"),
        ("{x \\in 1..10 : x % 2 = 0}", "{2, 4, 6, 8, 10}"),
        ("{x * x : x \\in 1..3}", "{1, 4, 9}"),
        ("[i \\in 1..3 |-> i * i]", "<<1, 4, 9>>"),
        ("LET f[n \\in 0..5] == IF n = 0 THEN 1 ELSE n * f[n - 1] IN f[5]", "120"),
        ("[[a |-> 1, b |-> 2] EXCEPT !.a = @ + 10]", "[a |-> 11, b |-> 2]"),
        ("[<<1, 2, 3>> EXCEPT ![2] = 7]", "<<1, 7, 3>>"),
        ("\\A x \\in 1..3 : \\E y \\in 1..3 : y > x \\/ x = 3", "TRUE"),
        ("Cardinality(SUBSET (1..4))", "16"),
        ("Append(<<1>>, 2) \\o <<3>>", "<<1, 2, 3>>"),
        ("SelectSeq(<<1, 2, 3, 4>>, LAMBDA x : x % 2 = 0)", "<<2, 4>>"),
        ("Len(SubSeq(<<1, 2, 3, 4>>, 2, 3))", "2"),
        ("DOMAIN [a |-> 1, b |-> 2]", "{\"a\", \"b\"}"),
        ("(1 :> \"x\") @@ (2 :> \"y\")", "<<\"x\", \"y\">>"),
        ("CASE 1 > 2 -> \"a\" [] 2 > 1 -> \"b\" [] OTHER -> \"c\"", "\"b\""),
        ("<<1, 2>> \\in {1, 2} \\X {2, 3}", "TRUE"),
        ("[x \\in {1, 2} |-> x] \\in [{1, 2} -> {1, 2}]", "TRUE"),
        ("Cardinality([{1, 2, 3} -> {1, 2}])", "8"),
        ("-3 \\div 2", "-1"),
        ("(-3) \\div 2", "-2"),
        ("-3 % 2", "1"),
        ("5 \\in Nat /\\ -5 \\in Int /\\ -5 \\notin Nat", "TRUE"),
        ("Cardinality(Permutations({1, 2, 3}))", "6"),
        ("SortSeq(<<3, 1, 2>>, <)", "<<1, 2, 3>>"),
        ("Twice(LAMBDA x : x + 1, 3)", "5"),
        ("Fib[10]", "55"),
    ];
    let mut body = String::from("Twice(F(_), x) == F(F(x))\nFib[n \\in Nat] == IF n < 2 THEN n ELSE Fib[n - 1] + Fib[n - 2]\n");
    let names: Vec<String> = (0..cases.len()).map(|i| format!("T{i}")).collect();
    for (i, (e, _)) in cases.iter().enumerate() {
        body.push_str(&format!("T{i} == {e}\n"));
    }
    let got = eval_defs(&body, &names.iter().map(|s| s.as_str()).collect::<Vec<_>>());
    let mut bad = Vec::new();
    for ((e, want), got) in cases.iter().zip(&got) {
        if got != want {
            bad.push(format!("{e}: want {want}, got {got}"));
        }
    }
    assert!(bad.is_empty(), "\n{}", bad.join("\n"));
}

/// A recursive function defined in a LET is freed with its value: the
/// LET's value cache of `f` held the function, and the function held the
/// environment with that cache (a reference cycle that leaked the function,
/// its memo and the state it was made in on every evaluation).
/// A `SUBSET S` domain cannot be materialized, so it is streamed, in the
/// normalized order
/// (`tlx-value/tests/ops.rs::streaming_order_is_the_normalized_order`): the
/// answer is known as soon as an element satisfies the body. TLC streams it
/// too (`SubsetValue` implements the normalized enumeration by streaming), so
/// that case agrees. A `[S -> T]` domain is materialized by both: its size
/// overflows TLC's int, and TLC's growing `ValueVec` reports its
/// `-maxSetSize` bound first, so tlx reports that error too. `CHOOSE` streams
/// `SUBSET S` in normalized order as well; a bound of several variables still
/// needs the whole set.
#[test]
fn quantifiers_stream_subsets_whose_size_overflows() {
    let body = "\
BigSubset == \\E s \\in SUBSET (1..31) : s = {}\n\
BigFcn == \\E f \\in [1..5 -> 1..121] : f[1] = 1 /\\ f[5] = 3\n\
CardinalityOf == Cardinality(SUBSET (1..31))\n\
Chosen == CHOOSE s \\in SUBSET (1..31) : s = {}\n\
Pair == \\E x, y \\in SUBSET (1..31) : x = y";
    let out = eval_defs(body, &["BigSubset", "BigFcn", "CardinalityOf", "Chosen", "Pair"]);
    assert_eq!(out[0], "TRUE", "{out:?}");
    assert!(
        out[1].starts_with("ERROR:") && out[1].contains("Attempted to construct a set with too many elements (>1000000)"),
        "BigFcn: {}",
        out[1]
    );
    assert_eq!(out[3], "{}", "{out:?}");
    for (i, what) in [(2, "Cardinality"), (4, "a bound of two variables")] {
        assert!(out[i].starts_with("ERROR:") && out[i].contains("Overflow when computing the number of elements in"), "{what}: {}", out[i]);
    }
}

#[test]
fn choose_streams_normalized_subset_and_ksubset() {
    let body = "\
EXTENDS Naturals, FiniteSets, FiniteSetsExt\n\
PickEmpty == CHOOSE s \\in SUBSET (1..31) : s = {}\n\
PickTwo == CHOOSE s \\in SUBSET (1..31) : 2 \\in s\n\
PickTrue == CHOOSE s \\in SUBSET (1..31) : TRUE\n\
PickParam(k) == CHOOSE s \\in SUBSET (1..31) : k \\in s\n\
PickParamTwo == PickParam(2)\n\
PickKSubFirst == CHOOSE s \\in kSubset(10, 1..30) : 1 \\in s\n\
PickKSubSecond == CHOOSE s \\in kSubset(10, 1..30) : 11 \\in s\n\
PickKSubZeroNat == CHOOSE s \\in kSubset(0, Nat) : TRUE\n\
PickKSubEmpty == CHOOSE s \\in kSubset(2, {1}) : TRUE\n\
PickSubsetNat == CHOOSE s \\in SUBSET Nat : TRUE\n\
PickTupleOnSubset == CHOOSE <<a, b>> \\in SUBSET (1..31) : TRUE\n\
PickBigFcn == CHOOSE f \\in [1..5 -> 1..121] : TRUE\n";
    let (_dir, path) = write_spec("M", body);
    let mut prog = Program::load(&path, &[]).unwrap_or_else(|e| panic!("{e:?}"));
    let names = [
        "PickEmpty",
        "PickTwo",
        "PickTrue",
        "PickParamTwo",
        "PickKSubFirst",
        "PickKSubSecond",
        "PickKSubZeroNat",
        "PickKSubEmpty",
        "PickSubsetNat",
        "PickTupleOnSubset",
        "PickBigFcn",
    ];
    let ids: Vec<_> = names
        .iter()
        .map(|n| match prog.lookup_root(n) {
            Some(RootSymbol::Def(d)) => d,
            _ => panic!("{n} not defined"),
        })
        .collect();
    let ip = Interp::new(prog, Default::default()).unwrap_or_else(|e| panic!("{e}"));
    let out: Vec<String> = ids
        .iter()
        .map(|d| {
            let e = tlx_sema::hir::Expr::new(ExprKind::Apply { op: OpRef::Def(*d), args: vec![] }, Default::default());
            match ip.eval(&e, &Env::default(), &Ctx::NONE) {
                Ok(v) => v.to_string(),
                Err(e) => format!("ERROR: {e}"),
            }
        })
        .collect();
    assert_eq!(out[0], "{}", "PickEmpty: {out:?}");
    assert_eq!(out[1], "{2}", "PickTwo: {out:?}");
    assert_eq!(out[2], "{}", "PickTrue: {out:?}");
    assert_eq!(out[3], "{2}", "PickParamTwo: {out:?}");
    assert_eq!(out[4], "{1, 2, 3, 4, 5, 6, 7, 8, 9, 10}", "PickKSubFirst: {out:?}");
    assert_eq!(out[5], "{1, 2, 3, 4, 5, 6, 7, 8, 9, 11}", "PickKSubSecond: {out:?}");
    assert_eq!(out[6], "{}", "PickKSubZeroNat: {out:?}");
    assert!(out[7].starts_with("ERROR:") && out[7].contains("no element of S satisfied P"), "PickKSubEmpty: {}", out[7]);
    assert!(out[8].starts_with("ERROR:") && out[8].contains("non-enumerable"), "PickSubsetNat: {}", out[8]);
    assert!(out[9].starts_with("ERROR:") && out[9].contains("non-tuple"), "PickTupleOnSubset: {}", out[9]);
    assert!(
        out[10].starts_with("ERROR:") && out[10].contains("Attempted to construct a set with too many elements (>1000000)"),
        "PickBigFcn: {}",
        out[10]
    );
    // Also exercise the uncompiled tree-walker path (`eval_tree` on a
    // synthetic `ExprKind::Choose` not in `prog`'s `code_of` table).
    let tlx_sema::hir::DefKind::Op(pick_two_body) = &ip.prog.defs[ids[1].idx()].kind else {
        panic!("PickTwo is an operator");
    };
    let synthetic = tlx_sema::hir::Expr::new((*pick_two_body.kind).clone(), pick_two_body.span);
    assert_eq!(ip.eval(&synthetic, &Env::default(), &Ctx::NONE).unwrap().to_string(), "{2}");
}

#[test]
fn init_subseteq_streams_overflowing_powerset_in_normalized_order() {
    let (_dir, path) = write_spec("M", "EXTENDS Naturals\nVARIABLE x\nInit == x \\subseteq (1..31)\nNext == x' = x\n");
    let mut prog = Program::load(&path, &[]).unwrap_or_else(|e| panic!("{e:?}"));
    let Some(RootSymbol::Def(init_def)) = prog.lookup_root("Init") else { panic!("Init not defined") };
    let ip = Interp::new(prog, Default::default()).unwrap_or_else(|e| panic!("{e}"));
    let tlx_sema::hir::DefKind::Op(init_body) = &ip.prog.defs[init_def.idx()].kind else { panic!("Init is an operator") };
    let mut seen = Vec::new();
    let mut emit = |s1: &[Option<tlx_value::Value>]| {
        seen.push(s1[0].as_ref().unwrap().to_string());
        Ok(seen.len() < 5)
    };
    ip.init_states(init_body, &mut emit).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(seen, ["{}", "{1}", "{2}", "{3}", "{4}"]);
}

#[test]
fn let_recursive_function_is_freed() {
    let (_dir, path) = write_spec("M", "EXTENDS Naturals\nT == LET f[n \\in 0..5] == IF n = 0 THEN 1 ELSE n * f[n - 1] IN f");
    let mut prog = Program::load(&path, &[]).unwrap_or_else(|e| panic!("{e:?}"));
    let Some(RootSymbol::Def(d)) = prog.lookup_root("T") else { panic!("T not defined") };
    let ip = Interp::new(prog, Default::default()).unwrap_or_else(|e| panic!("{e}"));
    // (The body, not `T`: the value of a constant definition is kept.)
    let tlx_sema::hir::DefKind::Op(body) = &ip.prog.defs[d.idx()].kind else { panic!("T is an operator") };
    let v = ip.eval(body, &Env::default(), &Ctx::NONE).unwrap();
    let tlx_value::Value::LazyFcn(f) = &v else { panic!("{v} is not a lazy function") };
    assert_eq!(f.apply(&tlx_value::Value::Int(5)).unwrap(), tlx_value::Value::Int(120));
    let weak = Arc::downgrade(f);
    drop(v);
    assert!(weak.upgrade().is_none(), "the recursive function was not freed");
}

/// ToString prints from the expanded copy (`tlx_value::fmt::printable`): the
/// same text as `Display` of the lazy value, for the sets that are expanded
/// and for those that keep their symbolic form.
#[test]
fn to_string_matches_display() {
    let cases = [
        "{x \\in 1..5 : x > 2}",
        "SUBSET {1, 2}",
        "SUBSET (1..8)",
        "[{1, 2} -> {3, 4}]",
        "{1} \\X {2, 3}",
        "[a : {1, 2}, b : {3}]",
        "<<{x \\in 1..3 : TRUE}, SUBSET {1}>>",
        "[k \\in {1, 2} |-> {y \\in 1..k : TRUE}]",
        "UNION {{1}, {x \\in 2..3 : TRUE}}",
        "{x \\in SUBSET {1, 2} : Cardinality(x) # 1}",
        "{{x \\in 1..k : TRUE} : k \\in 1..3}",
        "Seq({1})",
        "[n \\in Nat |-> n]",
        "[a |-> {x \\in 1..2 : TRUE}, b |-> Nat]",
        "{x \\in 1..4 : x > 1} \\ {3}",
        "[{1, 2} -> {x \\in 1..2 : TRUE}]",
    ];
    let mut body = String::new();
    for (i, e) in cases.iter().enumerate() {
        body.push_str(&format!("A{i} == {e}\nB{i} == ToString(A{i})\n"));
    }
    let names: Vec<String> = (0..cases.len()).flat_map(|i| [format!("A{i}"), format!("B{i}")]).collect();
    let got = eval_defs(&body, &names.iter().map(|s| s.as_str()).collect::<Vec<_>>());
    let mut bad = Vec::new();
    for (i, e) in cases.iter().enumerate() {
        let (shown, s) = (&got[2 * i], &got[2 * i + 1]);
        if *s != format!("{shown:?}") {
            bad.push(format!("{e}: Display {shown}, ToString {s}"));
        }
    }
    assert!(bad.is_empty(), "\n{}", bad.join("\n"));
}

/// Filters over sets of sequences decided on prefixes enumerate
/// the elements and fail as the interpreter's element-by-element filter:
/// `P{i}` is filtered on prefixes where it can be, `Q{i}` (the same
/// predicate under a LET, which `seqfilter` does not compile) element by
/// element.
#[test]
fn sequence_filters_decided_on_prefixes() {
    let cases = [
        ("UNION {[1..n -> 1..3] : n \\in 1..4}", "\\A i, j \\in 1..Len(s) : i < j => s[i] =< s[j]"),
        ("[1..4 -> 1..4]", "\\A i, j \\in DOMAIN s : i # j => s[i] # s[j]"),
        ("[1..3 -> 1..3]", "\\E i \\in 1..Len(s) : s[i] = 2"),
        ("[1..3 -> {3, 1, 2}]", "IF s[1] > 1 THEN s[2] = 1 ELSE s[Len(s)] = 3"),
        ("UNION {[1..n -> 0..2] : n \\in 0..3}", "Sorted(s)"),
        ("[1..3 -> BOOLEAN]", "(s[1] => s[2]) /\\ (s[1] \\/ ~s[3])"),
        ("[1..3 -> BOOLEAN]", "s[2]"),
        ("[1..3 -> 1..3]", "s[1] + 1 = s[2]"),
        ("[1..3 -> 1..3]", "s[Len(s) + 1] = 1"),
        ("[1..3 -> 1..2]", "s[1] = 1 \\/ s[5] = 2"),
        ("[1..2 -> 1..2]", "s[1] < \"a\""),
        ("[1..2 -> {\"a\", \"b\"}]", "s[1] # s[2] /\\ s[2] \\in {\"b\"}"),
        ("[1..2 -> {1, \"a\"}]", "s[1] = 1"),
        ("[1..2 -> {1, 2}] \\cup UNION {[1..n -> {1, 2}] : n \\in 2..3}", "s[1] =< s[2]"),
        ("(UNION {[1..n -> 1..3] : n \\in 1..3}) \\X {1}", "s[1][1] = 1"),
        ("UNION {{<<1>>, <<2, 1>>}, [1..2 -> 1..2]}", "s[1] >= s[Len(s)]"),
        ("[1..3 -> 1..3]", "\\A i \\in 1..Len(s) - 1 : -s[i] >= -s[i + 1] \\/ FALSE"),
        ("[1..3 -> 1..3]", "TRUE"),
        ("[1..3 -> 1..3]", "Len(s) = 2"),
        ("[1..3 -> 1..3]", "\\E v \\in {1, 3} : \\A i \\in DOMAIN s : s[i] # v"),
        ("[1..2 -> 1..3]", "Two(s, 2)"),
        (
            "[1..5 -> 1..5]",
            "\\A i \\in 1..Len(s) - 1 : \\A j \\in i + 1..Len(s) : ~(s[i] = s[j] \\/ s[i] - s[j] = i - j \\/ s[j] - s[i] = i - j)",
        ),
        ("[1..2 -> 1..3]", "s[2] = 1 \\/ s[1] * 2147483647 > 0"),
        ("[1..3 -> 1..3]", "IF s[1] = 1 THEN s[2] + s[3] = 4 ELSE s[2] = s[1]"),
    ];
    let mut body = String::from("Sorted(t) == \\A i \\in 1..Len(t) - 1 : t[i] =< t[i + 1]\nTwo(t, k) == t[1] = k /\\ t[k] # k + 1\n");
    for (i, (base, pred)) in cases.iter().enumerate() {
        body.push_str(&format!("P{i} == {{s \\in {base} : {pred}}}\nQ{i} == {{s \\in {base} : LET u == 0 IN {pred}}}\n"));
    }
    // An operator's parameter (in the environment of the filter).
    let n = cases.len();
    body.push_str(&format!("F(k) == {{s \\in [1..2 -> 1..3] : s[1] = k}}\nG(k) == {{s \\in [1..2 -> 1..3] : LET u == 0 IN s[1] = k}}\nP{n} == F(2)\nQ{n} == G(2)\n"));
    let cases: Vec<(&str, &str)> = cases.iter().copied().chain([("[1..2 -> 1..3]", "s[1] = k")]).collect();
    let mut defs = String::from("EXTENDS Naturals, Integers, Sequences\n");
    defs.push_str(&body);
    let (_dir, path) = write_spec("M", &defs);
    let mut prog = Program::load(&path, &[]).unwrap_or_else(|e| panic!("{e:?}"));
    let mut ids = Vec::new();
    for i in 0..cases.len() {
        for n in [format!("P{i}"), format!("Q{i}")] {
            match prog.lookup_root(&n) {
                Some(RootSymbol::Def(d)) => ids.push(d),
                _ => panic!("{n} not defined"),
            }
        }
    }
    let ip = Interp::new(prog, Default::default()).unwrap_or_else(|e| panic!("{e}"));
    let elems = |d| {
        let e = tlx_sema::hir::Expr::new(ExprKind::Apply { op: OpRef::Def(d), args: vec![] }, Default::default());
        let v = ip.eval(&e, &Env::default(), &Ctx::NONE).map_err(|e| e.to_string())?;
        tlx_value::ops::enumerate(&v).map(|es| es.iter().map(|x| x.to_string()).collect::<Vec<_>>()).map_err(|e| e.to_string())
    };
    let mut bad = Vec::new();
    for (i, case) in cases.iter().enumerate() {
        let (p, q) = (elems(ids[2 * i]), elems(ids[2 * i + 1]));
        if p != q {
            bad.push(format!("{case:?}:\n  on prefixes {p:?}\n  plain       {q:?}"));
        }
    }
    assert!(bad.is_empty(), "\n{}", bad.join("\n"));
}

fn check(body: &str, cfg: &str, workers: usize) -> tlx_runtime::Report<tlx_eval::model::State> {
    let ip = interp(body, cfg);
    let m = InterpModel::new(ip).unwrap_or_else(|e| panic!("{e}"));
    explore(&m, &Options { workers, check_deadlock: m.check_deadlock, ..Default::default() })
}

#[test]
fn singleton_difference_compares_each_element_once() {
    let source = include_str!("../../../tests/specs/SetDifferenceComparisonEffects.tla");
    let body = source.split_once('\n').unwrap().1.rsplit_once("====").unwrap().0;
    let report = check(body, include_str!("../../../tests/specs/SetDifferenceComparisonEffects.cfg"), 1);
    // Each side of the sole comparison enumerates the two-element filter.
    // Repeating that comparison evaluates the predicate a fifth time and fails.
    assert_eq!(report.outcome, Outcome::Ok);
    assert_eq!((report.stats.generated, report.stats.distinct, report.stats.depth), (2, 1, 1));
}

#[test]
fn die_hard() {
    let spec = "EXTENDS Naturals\nVARIABLES big, small\n\
        TypeOK == small \\in 0..3 /\\ big \\in 0..5\n\
        Init == big = 0 /\\ small = 0\n\
        FillSmall == small' = 3 /\\ big' = big\n\
        FillBig == big' = 5 /\\ small' = small\n\
        EmptySmall == small' = 0 /\\ big' = big\n\
        EmptyBig == big' = 0 /\\ small' = small\n\
        SmallToBig == IF big + small =< 5 THEN big' = big + small /\\ small' = 0 \
                      ELSE big' = 5 /\\ small' = small - (5 - big)\n\
        BigToSmall == IF big + small =< 3 THEN big' = 0 /\\ small' = big + small \
                      ELSE big' = small - (3 - big) /\\ small' = 3\n\
        Next == FillSmall \\/ FillBig \\/ EmptySmall \\/ EmptyBig \\/ SmallToBig \\/ BigToSmall\n\
        NotSolved == big # 4";
    let r = check(spec, "INIT Init\nNEXT Next\nINVARIANT TypeOK", 1);
    assert_eq!(r.outcome, Outcome::Ok);
    // TLC: 97 states generated, 16 distinct states found, depth 8.
    assert_eq!((r.stats.generated, r.stats.distinct, r.stats.depth), (97, 16, 8));
    let r = check(spec, "INIT Init\nNEXT Next\nINVARIANT NotSolved", 1);
    assert_eq!(r.outcome, Outcome::InvariantViolated("NotSolved".into()));
    assert_eq!(r.trace.len(), 7);
}

#[test]
fn unchanged_and_exists() {
    let spec = "EXTENDS Naturals\nCONSTANT N\nVARIABLES x, y\n\
        vars == <<x, y>>\n\
        Init == x \\in 1..N /\\ y = 0\n\
        Next == \\E i \\in 1..N : x' = i /\\ UNCHANGED y\n\
        Spec == Init /\\ [][Next]_vars";
    let r = check(spec, "CONSTANT N = 3\nSPECIFICATION Spec", 1);
    assert_eq!(r.outcome, Outcome::Ok);
    assert_eq!((r.stats.init_distinct, r.stats.distinct, r.stats.generated), (3, 3, 3 + 9));
}

/// TLC passes arguments lazily to every definition it evaluates from TLA+
/// text, also standard-module ones without a Java override, and
/// evaluates them for the Java overrides tlx runs from their TLA+ text.
#[test]
fn std_definitions_without_override_take_lazy_arguments() {
    let (_dir, path) = write_spec("M", "EXTENDS Naturals, Bags, TLCExt, Randomization\nUse(a) == 0");
    let mut prog = Program::load(&path, &[]).unwrap_or_else(|e| panic!("{e:?}"));
    let ids: Vec<_> = ["SubBag", "AssertEq", "TestRandomSetOfSubsets", "TLCModelValue", "TLCGetOrDefault", "Use"]
        .iter()
        .map(|n| match prog.lookup_root(n) {
            Some(RootSymbol::Def(d)) => d,
            _ => panic!("{n} not defined"),
        })
        .collect();
    let ip = Interp::new(prog, Default::default()).unwrap_or_else(|e| panic!("{e}"));
    let lazy: Vec<bool> = ids.iter().map(|d| ip.defers_arg_errors(*d)).collect();
    assert_eq!(lazy, [true, true, true, false, false, true]);
}

/// A 0-ary definition applying a higher-order operator is cacheable per
/// state when the operators it passes are state-level, not when a
/// LAMBDA or a definition it passes reads the next state or is random.
#[test]
fn higher_order_applications_are_state_cacheable() {
    let body = "EXTENDS Naturals, Sequences, TLC\nVARIABLES q, n\n\
                MapSeq(s, Op(_)) == [i \\in DOMAIN s |-> Op(s[i])]\n\
                Inc(x) == x + 1\nNextInc(x) == x + n'\n\
                Doubled == MapSeq(q, LAMBDA x : 2 * x)\nBumped == MapSeq(q, Inc)\n\
                Shifted == MapSeq(q, LAMBDA x : x + n')\nPushed == MapSeq(q, NextInc)\n\
                Random == MapSeq(q, LAMBDA x : RandomElement({x, x + 1}))";
    let (_dir, path) = write_spec("M", body);
    let mut prog = Program::load(&path, &[]).unwrap_or_else(|e| panic!("{e:?}"));
    let ids: Vec<_> = ["Doubled", "Bumped", "Shifted", "Pushed", "Random", "MapSeq"]
        .iter()
        .map(|n| match prog.lookup_root(n) {
            Some(RootSymbol::Def(d)) => d,
            _ => panic!("{n} not defined"),
        })
        .collect();
    let ip = Interp::new(prog, Default::default()).unwrap_or_else(|e| panic!("{e}"));
    let cacheable: Vec<bool> = ids.iter().map(|d| ip.is_state_cacheable(*d)).collect();
    assert_eq!(cacheable, [true, true, false, false, false, false]);
    // (Arguments are still passed by name to higher-order definitions in actions.)
    assert!(ip.is_action_level(ids[5]));
}

#[test]
fn deadlock_detected() {
    let spec = "EXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 3 /\\ x' = x + 1";
    let r = check(spec, "INIT Init\nNEXT Next", 1);
    assert_eq!(r.outcome, Outcome::Deadlock);
    assert_eq!(r.trace.len(), 4);
}

#[test]
fn synthesized_apply_can_drop_before_its_lazy_result() {
    use tlx_sema::hir::{DefKind, Expr, VarId};
    use tlx_value::{ops, Value};

    let ip = interp("VARIABLE x\nCapture(arg) == [index \\in {0} |-> arg']", "");
    let def = ip.prog.defs.iter().position(|def| &*def.name == "Capture").unwrap();
    assert!(matches!(ip.prog.defs[def].kind, DefKind::Op(_)));
    let before = vec![Value::Int(1)];
    let after = vec![Some(Value::Int(2))];
    let mut context = Ctx::action(&before, &after, 1);
    context.keep_lazy = true;
    let result = {
        let argument = Expr::new(ExprKind::Var(VarId(0)), Default::default());
        let apply =
            Expr::new(ExprKind::Apply { op: OpRef::Def(tlx_sema::hir::DefId(def as u32)), args: vec![argument] }, Default::default());
        ip.eval(&apply, &Env::default(), &context).unwrap()
    };
    drop((ip, before, after));
    assert!(matches!(result, Value::LazyFcn(_)));
    assert_eq!(ops::apply(&result, &Value::Int(0)).unwrap(), Value::Int(2));
}

#[test]
fn selecting_a_lazy_function_does_not_force_its_body() {
    let got = eval_defs(
        r#"T1 == DOMAIN (<<[x \in {3} |-> (1 :> "ab")[x]]>>)[1]
T3 == ((<<[x \in {3} |-> (1 :> "ab")[x]]>>)[1])[3]
"#,
        &["T1", "T3"],
    );
    assert_eq!(got[0], "{3}");
    assert!(got[1].starts_with("ERROR:"), "applying the selected function must fail: {}", got[1]);
}

/// Equal pairs can still carry different lookup witnesses. EXCEPT must retain
/// the replacement even when both functions share the pair allocation.
#[test]
fn except_preserves_replacement_domain_witness() {
    use tlx_sema::hir::DefKind;
    use tlx_value::{ops, FcnDom, Value};

    let ip = interp(
        r#"EXTENDS Naturals
Direct(f, g) == [<<f>> EXCEPT ![1] = g]
Nested(f, g) == [<<[a |-> f]>> EXCEPT ![1].a = g]
"#,
        "",
    );
    let pairs: Arc<[(Value, Value)]> = vec![(Value::Int(0), Value::Int(7))].into();
    for name in ["Direct", "Nested"] {
        let def = ip.prog.defs.iter().find(|d| &*d.name == name).expect("definition");
        let DefKind::Op(body) = &def.kind else { panic!("body") };
        for (before, after) in [(FcnDom::Enumerated, FcnDom::Interval), (FcnDom::Interval, FcnDom::Enumerated)] {
            let env = Env::default()
                .bind_val(def.params[0], Value::Fcn(pairs.clone(), before))
                .bind_val(def.params[1], Value::Fcn(pairs.clone(), after));
            // A fresh HIR root bypasses code_of and exercises the tree's
            // EXCEPT path; the program-owned root uses code.rs.
            let mut tree = body.clone();
            tree.kind = Arc::new((*body.kind).clone());
            assert!(ip.prog.expr_id(body).is_some());
            assert!(ip.prog.expr_id(&tree).is_none());
            for expr in [body, &tree] {
                let result = ip.eval(expr, &env, &Ctx::NONE).unwrap();
                let mut inner = ops::select(&result, &Value::Int(1)).unwrap().unwrap();
                if name == "Nested" {
                    inner = ops::select(&inner, &Value::Str(tlx_value::intern::Sym::new("a"))).unwrap().unwrap();
                }
                assert!(
                    matches!(&inner, Value::Fcn(ps, dom) if Arc::ptr_eq(ps, &pairs) && *dom == after),
                    "{name}: {before:?} -> {after:?}"
                );
                assert_eq!(
                    ops::select(&inner, &Value::ModelValue(tlx_value::intern::Sym::new("absent"))).is_err(),
                    after == FcnDom::Interval
                );
            }
        }
    }
}

#[test]
fn except_noop_keeps_rhs_effects_and_lazy_tuple_key_update() {
    use std::sync::atomic::{AtomicUsize, Ordering};
    use tlx_sema::hir::DefKind;
    use tlx_value::{lazy::LazyFcn, ops, Value};

    #[derive(Debug)]
    struct CountingFcn(Arc<AtomicUsize>);
    impl LazyFcn for CountingFcn {
        fn domain(&self) -> tlx_value::Result<Value> {
            Ok(Value::Set(vec![Value::tuple(vec![Value::Int(1), Value::Int(2)])].into()))
        }
        fn apply(&self, _: &Value) -> tlx_value::Result<Value> {
            self.0.fetch_add(1, Ordering::Relaxed);
            Ok(Value::Int(7))
        }
    }
    let ip = interp(
        r#"EXTENDS Naturals, TLC
Update(f) == [f EXCEPT ![1, 2] = @]
Effect(f) == [f EXCEPT ![1] = IF TLCSet(1, 123) THEN @ ELSE @]
Get == TLCGet(1)
"#,
        "",
    );
    let eval = |name: &str, arg: Option<Value>| {
        let d = ip.prog.defs.iter().find(|d| &*d.name == name).unwrap();
        let DefKind::Op(body) = &d.kind else { panic!("operator body") };
        let env = arg.map_or_else(Env::default, |v| Env::default().bind_val(d.params[0], v));
        ip.eval(body, &env, &Ctx::NONE).unwrap()
    };
    let calls = Arc::new(AtomicUsize::new(0));
    let result = eval("Update", Some(Value::LazyFcn(Arc::new(CountingFcn(calls.clone())))));
    assert_eq!(calls.load(Ordering::Relaxed), 1, "only the updated point is evaluated");
    assert_eq!(ops::apply(&result, &Value::tuple(vec![Value::Int(1), Value::Int(2)])).unwrap(), Value::Int(7));
    assert_eq!(calls.load(Ordering::Relaxed), 1, "even an equal replacement is stored on a lazy function");
    let original = Value::tuple(vec![Value::Int(7)]);
    assert_eq!(eval("Effect", Some(original.clone())), original);
    assert_eq!(eval("Get", None), Value::Int(123), "the no-op replacement still runs its effect");
}
