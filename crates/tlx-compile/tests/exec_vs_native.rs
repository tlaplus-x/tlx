//! Differential tests: the IR executor (`exec`) against the generated C
//! code, with the interpreter as the reference (see `tlx_testkit::diff`).
//!
//! Each case is a small spec whose actions, invariants and action
//! properties exercise some IR node kinds; every lowered function runs in
//! the three tiers on the reachable states, the steps between them and on
//! random states of the layout. `ir_node_coverage` checks that the cases
//! together exercise every IR node kind the lowering produces for them.
//!
//! Environment:
//! - `TLX_DIFF_VERBOSE=1`: print each case's tallies, node kinds and what
//!   is not native;
//! - `TLX_DIFF_STRICT=1`: also fail when the IR executor and native code
//!   disagree only on bailing out (see `DiffReport::asymmetries`);
//! - `TLX_SEED=n`: seed of the random states;
//! - `TLX_DIFF_DUMP=name`: print the IR of the functions called `name`.

use std::collections::BTreeSet;
use std::sync::Arc;

use tlx_layout::Shape;
use tlx_testkit::diff::{DiffReport, Harness};
use tlx_testkit::{module, note, seed, Rng};
use tlx_value::Value;

/// Reachable states checked per case.
const REACHABLE: usize = 400;
/// Random states checked per case.
const RANDOM: usize = 300;

struct Case {
    name: &'static str,
    body: &'static str,
    cfg: &'static str,
    /// Variable shapes (default: speculated from the reachable states).
    shapes: Option<fn() -> Vec<Shape>>,
    /// Functions allowed not to be native (default: all must be).
    not_native: &'static [&'static str],
}

const CFG: &str = "INIT Init\nNEXT Next\n";

fn verbose() -> bool {
    std::env::var_os("TLX_DIFF_VERBOSE").is_some()
}

/// Run `case`; returns its harness's IR node kinds.
fn run(case: &Case) -> BTreeSet<&'static str> {
    let src = module(case.name, case.body);
    let h = match case.shapes {
        Some(f) => Harness::with_shapes(&src, case.cfg, f()),
        None => Harness::new(&src, case.cfg),
    };
    let mut rep: DiffReport = h.run_reachable(REACHABLE);
    let s = seed(0x5eed ^ case.name.len() as u64);
    h.run_random(&mut Rng::new(s), RANDOM, &mut rep);
    let kinds = h.node_kinds();
    if let Ok(name) = std::env::var("TLX_DIFF_DUMP") {
        note(&h.dump(&name));
    }
    if verbose() {
        note(&format!(
            "== {} (seed {s})\nlayout: {:?}\nnotes: {:?}\nnot native: {:?}\nkinds: {kinds:?}\n{}",
            case.name,
            h.layout.vars,
            h.notes,
            h.not_native(),
            rep.render()
        ));
    }
    rep.assert_ok(case.name);
    let missing: Vec<String> = h.not_native().into_iter().filter(|n| !case.not_native.contains(&n.as_str())).collect();
    assert!(missing.is_empty(), "{}: not native: {missing:?} (notes: {:?})", case.name, h.notes);
    assert!(h.notes.is_empty(), "{}: not lowered: {:?}", case.name, h.notes);
    let (e, n) = rep.totals();
    assert!(e.agree > 0 && n.agree > 0, "{}: nothing compared\n{}", case.name, rep.render());
    kinds
}

fn atoms(names: &[&str]) -> Shape {
    let mut v: Vec<Value> = names.iter().map(|n| Value::str(n)).collect();
    v.sort();
    Shape::Atom(Arc::from(v))
}

// ---------------------------------------------------------------------------
// Cases

#[test]
fn records_with_set_fields_iterate_without_boxing() {
    let src = module(
        "RecordSetOrder",
        r#"EXTENDS Naturals, FiniteSets
VARIABLE r
Init == r = [generation |-> 1, members |-> {1, 4}]
Next == r' = CHOOSE c \in {r} \cup {[generation |-> 1, members |-> {2, 3}]}: TRUE
"#,
    );
    for hi in [1, 10000] {
        let elem = Shape::Record(Arc::from(vec![
            (tlx_value::intern::Sym::new("generation"), Shape::Int { lo: 0, hi }),
            (tlx_value::intern::Sym::new("members"), Shape::Set { elem: Box::new(Shape::Int { lo: 1, hi: 4 }), max_card: 4 }),
        ]));
        let h = Harness::with_shapes(&src, CFG, vec![elem]);
        let rep = h.run_reachable(20);
        rep.assert_ok("record set enumeration");
        let action = h.actions[0].as_ref().unwrap();
        assert_eq!(tlx_compile::coverage::Coverage::of_stmt(&action.body).boxed, 0, "record enumeration should keep its elements encoded");
    }
}

const SCALARS: Case = Case {
    name: "Scalars",
    body: r#"EXTENDS Naturals, Integers
VARIABLES x, b
Init == x = 0 /\ b = FALSE
Inc == x < 5 /\ x' = x + 1 /\ b' = ~b
Dec == \E d \in 1..2 : x - d >= -3 /\ x' = x - d /\ UNCHANGED b
Arith == x' = (IF b THEN (x * 3) % 7 ELSE -x \div 2) /\ b' = (x > 1 \/ b)
DivErr == x' = 10 \div (x - 2) /\ b' = b
Pow == x \in 0..3 /\ x' = 2^x - 1 /\ b' = (x = 2)
Partial == x = 3 /\ x' = 1
Next == Inc \/ Dec \/ Arith \/ DivErr \/ Pow \/ Partial
Inv1 == x >= -10
Inv2 == b => x # 100
Inv3 == 7 \div (x + 3) >= 0
TPos == [][x' # x \/ b' # b \/ x = x']_<<x, b>>
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2 Inv3\nPROPERTY TPos\n",
    shapes: None,
    not_native: &[],
};

const BITSETS: Case = Case {
    name: "Bitsets",
    body: r#"EXTENDS Naturals, FiniteSets
VARIABLES S, T
Init == S = {} /\ T = {1, 2}
Add == \E i \in 1..4 : i \notin S /\ S' = S \cup {i} /\ T' = T
Rem == \E i \in S : S' = S \ {i} /\ T' = T \cup {i}
Mix == S' = S \cap T /\ T' = (T \ S) \cup {Cardinality(S)}
Filt == S' = {i \in T : i > 1} /\ T' = {i + 1 : i \in S \cap 0..3}
Next == Add \/ Rem \/ Mix \/ Filt
Inv1 == Cardinality(S) <= 4
Inv2 == \A i \in S : i \in 0..5
Inv3 == (CHOOSE i \in 0..9 : i \notin S) >= 0
Inv4 == \E i \in T : i >= 0
Inv5 == S \subseteq 0..5 /\ (T = {} \/ 2 \in T \/ T # {2})
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2 Inv3 Inv4 Inv5\n",
    shapes: None,
    not_native: &[],
};

const RECORDS: Case = Case {
    name: "Records",
    body: r#"EXTENDS Naturals
VARIABLES r, p
Init == r = [a |-> 0, b |-> FALSE] /\ p = <<1, 2>>
Step == r' = [r EXCEPT !.a = (@ + 1) % 3, !.b = ~@] /\ p' = <<p[2], p[1]>>
Set1 == r.b /\ r' = [a |-> p[1], b |-> r.a = 0] /\ p' = [p EXCEPT ![1] = r.a + 1]
Next == Step \/ Set1
Inv1 == r.a \in 0..3
Inv2 == p[1] + p[2] <= 6
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2\n",
    shapes: None,
    not_native: &[],
};

const FUNCTIONS: Case = Case {
    name: "Functions",
    body: r#"EXTENDS Naturals
CONSTANTS P
VARIABLES f, g, who
Init == f = [i \in 1..3 |-> 0] /\ g = [q \in P |-> FALSE] /\ who \in P
Inc == \E i \in 1..3 : f[i] < 2 /\ f' = [f EXCEPT ![i] = @ + 1] /\ UNCHANGED <<g, who>>
Flip == \E q \in P : g' = [g EXCEPT ![q] = ~@] /\ who' = q /\ f' = f
Mine == g' = [g EXCEPT ![who] = TRUE] /\ f' = [f EXCEPT ![1] = IF g[who] THEN 1 ELSE 0] /\ who' = who
Outside == f' = [f EXCEPT ![f[1] + 3] = 1] /\ UNCHANGED <<g, who>>
IdxErr == f' = [f EXCEPT ![10 \div (f[2] - f[1])] = 0] /\ UNCHANGED <<g, who>>
IdxErr2 == f' = [f EXCEPT ![CHOOSE j \in 1..3 : f[j] = 2] = 0] /\ UNCHANGED <<g, who>>
IdxErr3 == \E i \in 1..3 : f' = [f EXCEPT ![i \div f[1]] = 0] /\ UNCHANGED <<g, who>>
Next == Inc \/ Flip \/ Mine \/ Outside \/ IdxErr \/ IdxErr2 \/ IdxErr3
Inv1 == \A i \in 1..3 : f[i] \in 0..2
Inv2 == g[who] \/ ~g[who]
Inv3 == f[f[1] + 1] >= 0
Inv4 == [f EXCEPT ![10 \div (f[2] - f[1])] = 0] # <<1, 1, 1>>
Inv5 == \A i \in 1..3 : [f EXCEPT ![CHOOSE j \in 1..3 : f[j] = i] = 0][1] <= 2
"#,
    cfg: "INIT Init\nNEXT Next\nCONSTANTS P = {p1, p2, p3}\nINVARIANT Inv1 Inv2 Inv3 Inv4 Inv5\n",
    shapes: None,
    not_native: &[],
};

const SEQUENCES: Case = Case {
    name: "SeqOps",
    body: r#"EXTENDS Naturals, Sequences
VARIABLE q
Init == q = <<>>
Push == Len(q) < 3 /\ \E v \in 1..2 : q' = Append(q, v)
Pop == Len(q) > 0 /\ q' = Tail(q)
Cat == Len(q) <= 1 /\ q' = q \o q
Sub == Len(q) >= 2 /\ q' = SubSeq(q, 2, Len(q))
Flt == q' = SelectSeq(q, LAMBDA e : e = 1)
HeadErr == q' = <<Head(q)>>
Next == Push \/ Pop \/ Cat \/ Sub \/ Flt \/ HeadErr
Inv1 == \A i \in 1..Len(q) : q[i] \in 1..2
Inv2 == Len(q) = 0 \/ q[Len(q)] >= 1
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2\n",
    shapes: None,
    not_native: &[],
};

const MAPS: Case = Case {
    name: "Maps",
    body: r#"EXTENDS Naturals, TLC
VARIABLE m
Init == m = [k \in {} |-> 0]
Put == \E k \in 1..3 : k \notin DOMAIN m /\ m' = m @@ (k :> 0)
Upd == \E k \in DOMAIN m : m' = [m EXCEPT ![k] = (@ + 1) % 2]
Del == \E k \in DOMAIN m : m' = [j \in DOMAIN m \ {k} |-> m[j]]
Next == Put \/ Upd \/ Del
Inv1 == \A k \in DOMAIN m : m[k] \in 0..1
Inv2 == 2 \in DOMAIN m => m[2] < 2
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2\n",
    shapes: None,
    not_native: &[],
};

const SORTED: Case = Case {
    name: "Sorted",
    body: r#"EXTENDS Naturals, FiniteSets
VARIABLE msgs
Init == msgs = {}
Send == \E s \in 1..3, v \in {0, 50, 99} : Cardinality(msgs) < 3 /\ msgs' = msgs \cup {[src |-> s, val |-> v, seq |-> <<s, v>>]}
Recv == \E m \in msgs : msgs' = msgs \ {m}
Keep == msgs' = {m \in msgs : m.val > 0}
Both == \E m \in msgs : msgs' = msgs \cap {m, [src |-> 1, val |-> 0, seq |-> <<1, 0>>]}
Next == Send \/ Recv \/ Keep \/ Both
Inv1 == \A m \in msgs : m.src \in 1..3
Inv2 == [src |-> 1, val |-> 0, seq |-> <<1, 0>>] \notin msgs \/ Cardinality(msgs) >= 1
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2\n",
    shapes: None,
    not_native: &[],
};

const UNIONS: Case = Case {
    name: "Unions",
    body: r#"EXTENDS Naturals
VARIABLES msg, n
Init == msg = [type |-> "req", src |-> 1] /\ n = 0
Req == \E s \in 1..2 : msg' = [type |-> "req", src |-> s] /\ n' = n
Ack == msg.type = "req" /\ msg' = [type |-> "ack", dst |-> msg.src + 3, ok |-> TRUE, src |-> msg.src + 5] /\ n' = (n + 1) % 3
Src == msg' = msg /\ n' = msg.src % 4
Fld == msg' = msg /\ n' = IF msg.type = "ack" THEN msg.dst % 3 ELSE msg.src % 3
NoFld == msg' = msg /\ n' = IF msg.ok THEN 1 ELSE 2
Next == Req \/ Ack \/ Fld \/ NoFld \/ Src
Inv1 == msg.type \in {"req", "ack"}
Inv2 == msg.type = "ack" => msg.dst > 3
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2\n",
    shapes: None,
    not_native: &[],
};

fn recode_shapes() -> Vec<Shape> {
    vec![atoms(&["a", "b"]), atoms(&["a", "b", "c"]), Shape::Set { elem: Box::new(atoms(&["a", "b", "c"])), max_card: 3 }]
}

const RECODE: Case = Case {
    name: "Recode",
    body: r#"VARIABLES x, y, s
Init == x = "a" /\ y = "c" /\ s = {}
Swap == x' = y /\ y' = x /\ s' = s
Copy == y' = x /\ x' = x /\ s' = s \cup {x}
Turn == x' = (IF x = "a" THEN "b" ELSE "a") /\ y' = y /\ s' = s \cup {y}
Next == Swap \/ Copy \/ Turn
Inv1 == x \in s \/ x \notin s
Inv2 == y # "d"
"#,
    cfg: CFG,
    shapes: Some(recode_shapes),
    not_native: &[],
};

const QUANTIFIERS: Case = Case {
    name: "Quantifiers",
    body: r#"EXTENDS Naturals, FiniteSets
VARIABLES x, S
Init == x = 0 /\ S = {1}
All == \A i \in S : i # 7
Grow == x < 3 /\ x' = x + 1 /\ S' = S \cup {x + 1}
Pick == S # {} /\ x' = (CHOOSE i \in S : \A j \in S : i >= j) /\ S' = S
Each == (\A i \in 1..2 : x' \in {x, x + i} /\ x' = x) /\ S' = S
Ch == x' = (CHOOSE i \in 0..3 : i > x) /\ S' = S
Rep == (\A i \in 1..2 : i > x \/ i < 3) /\ x' = x /\ S' = S
Next == Grow \/ Pick \/ Each \/ Ch \/ Rep
Inv1 == All
Inv2 == \E i \in S : i = x \/ i # x
Inv3 == LET m == CHOOSE i \in S : TRUE IN m \in S
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2 Inv3\n",
    shapes: None,
    not_native: &[],
};

const ENABLED: Case = Case {
    name: "Enabled",
    body: r#"EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y = 0
A == x < 2 /\ x' = x + 1 /\ y' = y
B == y < x /\ y' = y + 1 /\ x' = x
Next == A \/ B
Inv1 == ENABLED A \/ x = 2
Inv2 == (ENABLED B) = (y < x)
Inv3 == ENABLED Next
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2 Inv3\n",
    shapes: None,
    not_native: &[],
};

const PRODUCTS: Case = Case {
    name: "Products",
    body: r#"EXTENDS Naturals, FiniteSets
CONSTANTS P
VARIABLES S, x, who, h
Init == S = {} /\ x = 0 /\ who \in P /\ h = [k \in P \X {0, 1} |-> 0]
Add == S' = S \cup {<<x, x % 2>>} /\ x' = (x + 1) % 3 /\ UNCHANGED <<who, h>>
Del == \E t \in S : S' = S \ {t} /\ UNCHANGED <<x, who, h>>
Mark == h[<<who, x % 2>>] < 2 /\ h' = [h EXCEPT ![<<who, x % 2>>] = @ + 1] /\ UNCHANGED <<S, x, who>>
Move == \E q \in P : who' = q /\ UNCHANGED <<S, x, h>>
Next == Add \/ Del \/ Mark \/ Move
Inv1 == <<x, 0>> \in S \/ <<x, 1>> \in S \/ Cardinality(S) <= 6
Inv2 == h[<<who, 1>>] <= 2
"#,
    cfg: "INIT Init\nNEXT Next\nCONSTANTS P = {p1, p2}\nINVARIANT Inv1 Inv2\n",
    shapes: None,
    not_native: &[],
};

const UNION_SETS: Case = Case {
    name: "UnionSets",
    body: r#"EXTENDS Naturals
CONSTANTS P
VARIABLES S, z
Init == S = {} /\ z = 0
Put == S' = S \cup {z} /\ z' = z
Step == z' = (IF z \in P THEN 0 ELSE IF z < 2 THEN z + 1 ELSE CHOOSE p \in P : TRUE) /\ S' = S
Other == \E p \in P : z' = p /\ S' = S
Del == z \in S /\ S' = S \ {z} /\ z' = z
Next == Put \/ Step \/ Other \/ Del
Inv1 == z \in S \/ z \notin S
Inv2 == \A p \in P : p \in S => z # 7
"#,
    cfg: "INIT Init\nNEXT Next\nCONSTANTS P = {p1, p2}\nINVARIANT Inv1 Inv2\n",
    shapes: None,
    not_native: &[],
};

#[test]
fn union_sets() {
    run(&UNION_SETS);
}

const RECURSION: Case = Case {
    name: "Recursion",
    body: r#"EXTENDS Naturals, Sequences, FiniteSets
VARIABLES S, q
RECURSIVE SumSet(_)
SumSet(X) == IF X = {} THEN 0 ELSE LET x == CHOOSE x \in X : TRUE IN x + SumSet(X \ {x})
RECURSIVE Rev(_)
Rev(t) == IF t = <<>> THEN <<>> ELSE Append(Rev(Tail(t)), Head(t))
IsInjective(f) == \A a, b \in DOMAIN f : f[a] = f[b] => a = b
SetToSeq(X) == CHOOSE f \in [1..Cardinality(X) -> X] : IsInjective(f)
Init == S = {} /\ q = <<>>
Add == \E i \in 0..3 : i \notin S /\ S' = S \cup {i} /\ q' = q
Del == \E i \in S : S' = S \ {i} /\ q' = q
Snap == q' = SetToSeq(S) /\ S' = S
Flip == q' = Rev(q) /\ S' = S
Count == \E i \in 0..2 : (\/ i \in S \/ i + 1 \in S) /\ S' = S \ {i} /\ q' = q
Next == Add \/ Del \/ Snap \/ Flip \/ Count
Inv1 == SumSet(S) <= 6
Inv2 == Len(Rev(q)) = Len(q)
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2\n",
    shapes: None,
    not_native: &[],
};

#[test]
fn recursion() {
    run(&RECURSION);
}

/// `FoldFunction` / `FoldSeq` unrolled over functions, records, tuples and
/// sequences: an order-sensitive operator, integer and record
/// accumulators that leave the ranges of the elements (DyadicRationals
/// sums, products that overflow on random states).
const FOLDS: Case = Case {
    name: "FoldCases",
    body: r#"EXTENDS Naturals, Sequences, Functions, SequencesExt, DyadicRationals
VARIABLES w, s, r
Mix(x, acc) == acc * 7 + x
Init == w = [i \in {"a", "b", "c"} |-> Zero] /\ s = <<>> /\ r = [lo |-> 1, hi |-> 2]
Throw == \E k \in {"a", "b", "c"} : w[k].den < 8 /\ w' = [w EXCEPT ![k] = IF @ = Zero THEN Half(One) ELSE Add(@, Half(@))] /\ s' = s /\ r' = r
Push == \E k \in 1..3 : Len(s) < 3 /\ FoldFunction(Mix, 0, s) % 4 # k /\ s' = Append(s, k) /\ w' = w /\ r' = r
Pop == s # <<>> /\ FoldSeq(Mix, 1, s) % 3 # 0 /\ s' = Tail(s) /\ w' = w /\ r' = r
Swap == r' = [lo |-> r.hi, hi |-> (r.lo + Len(s)) % 4] /\ w' = w /\ s' = s
Next == Throw \/ Push \/ Pop \/ Swap
Inv1 == LET t == FoldFunction(Add, Zero, w) IN t.num <= 3 * t.den
Inv2 == FoldFunction(Mix, 0, r) # 23 /\ FoldFunction(LAMBDA x, a : a * x.den, 1, w) < 4096
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2\n",
    shapes: None,
    not_native: &[],
};

#[test]
fn folds() {
    run(&FOLDS);
}

/// A recursive operator following pointers that terminates on the
/// reachable states (a chain) and recurses forever on random states with
/// a cycle: every tier reports the runaway recursion as an error.
const POINTER_CYCLES: Case = Case {
    name: "PointerCycles",
    body: r#"EXTENDS Naturals
VARIABLES nxt
RECURSIVE Dist(_)
Dist(n) == IF n = 0 THEN 0 ELSE 1 + Dist(nxt[n])
Init == nxt = [n \in 1..3 |-> n - 1]
Swap == nxt' = [nxt EXCEPT ![3] = IF @ = 2 THEN 1 ELSE 2, ![2] = IF @ = 1 THEN 0 ELSE 1]
Next == Swap
Inv == Dist(3) <= 3
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv\n",
    shapes: None,
    not_native: &[],
};

#[test]
fn pointer_cycles() {
    run(&POINTER_CYCLES);
}

/// Recursive function definitions as compiled functions: module
/// level and in LETs, branching recursion, captured operator parameters,
/// a captured LAMBDA with its captured local, domain checks.
const RECURSIVE_FNS: Case = Case {
    name: "RecursiveFns",
    body: r#"EXTENDS Naturals, Sequences
VARIABLES x, s
Fact[n \in Nat] == IF n = 0 THEN 1 ELSE n * Fact[n - 1]
FibTo(m) == LET F[i \in 0..m] == IF i < 2 THEN i ELSE F[i - 1] + F[i - 2] IN F[m]
SumSeq(q) == LET F[i \in 0..Len(q)] == IF i = 0 THEN 0 ELSE q[i] + F[i - 1] IN F[Len(q)]
MapSeq(q, Op(_)) == LET G[i \in 0..Len(q)] == IF i = 0 THEN << >> ELSE Append(G[i - 1], Op(q[i])) IN G[Len(q)]
SumSet(S) == LET H[T \in SUBSET S] == IF T = {} THEN 0 ELSE LET e == CHOOSE e \in T : TRUE IN e + H[T \ {e}] IN H[S]
Short[n \in 0..5] == IF n = 0 THEN 0 ELSE 1 + Short[n - 1]
Init == x = 0 /\ s = << >>
Grow == x < 9 /\ x' = x + 1 /\ s' = IF Len(s) < 4 THEN Append(s, x % 3) ELSE s
Mix == Len(s) > 0 /\ \E k \in 1..2 :
         /\ x' = (FibTo(x) + Fact[x % 8] + k) % 10
         /\ s' = MapSeq(Tail(s), LAMBDA v : (v + k + SumSeq(s)) % 3)
Next == Grow \/ Mix
Inv1 == SumSeq(s) <= 2 * Len(s) /\ SumSet({v + x : v \in {1, 2, 3}}) = 6 + 3 * x
Inv2 == x > 7 \/ Short[x] = x
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2\n",
    shapes: None,
    not_native: &[],
};

#[test]
fn recursive_fns() {
    run(&RECURSIVE_FNS);
}

fn bound_set_shapes() -> Vec<Shape> {
    let int = |lo, hi| Shape::Int { lo, hi };
    let rec = |fs: Vec<(&str, Shape)>| {
        let mut fs: Vec<(tlx_value::Sym, Shape)> = fs.into_iter().map(|(k, s)| (tlx_value::Sym::new(k), s)).collect();
        fs.sort_by_key(|f| f.0);
        Shape::Record(Arc::from(fs))
    };
    let mut arms = vec![rec(vec![("type", atoms(&["p", "v"]))]), rec(vec![("type", atoms(&["p", "v"])), ("v", int(0, 3))])];
    arms.sort_by_cached_key(|a| a.kind_key());
    vec![
        Shape::Set { elem: Box::new(int(0, 7)), max_card: 8 },
        Shape::Set { elem: Box::new(int(1, 3)), max_card: 3 },
        Shape::Set { elem: Box::new(Shape::Union(Arc::from(arms))), max_card: 10 },
    ]
}

/// Bitsets with exact element shapes, as type-invariant bounds give them
/// (integers of a smaller range copied into a larger one, set maps
/// and filters over union-of-record elements, a constant record outside
/// the elements).
const BOUND_SETS: Case = Case {
    name: "BoundSets",
    body: r#"EXTENDS Naturals
VARIABLES S, T, m
Init == S = {} /\ T = {1} /\ m = {}
Copy == S' = T /\ T' = T /\ m' = m
Grow == \E i \in 1..3 : T' = T \cup {i} /\ S' = S /\ m' = m
Send == m' = m \cup {[type |-> "v", v |-> i] : i \in T} /\ S' = S /\ T' = T
Ping == m' = m \cup {[type |-> "p"]} /\ S' = S /\ T' = T
Keep == m' = {x \in m : x.type = "v"} /\ S' = S /\ T' = T
Next == Copy \/ Grow \/ Send \/ Ping \/ Keep
Inv1 == [type |-> "q"] \notin m
Inv2 == [type |-> "v", v |-> 7] \notin m
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2\n",
    shapes: Some(bound_set_shapes),
    not_native: &[],
};

#[test]
fn bound_sets() {
    run(&BOUND_SETS);
}

/// Unions of tuple arms discriminated by length: `<<>>` or
/// `<<node, round>>` vertices, a bitset of them and of pairs of them
/// (nested ranks), SUBSET iteration, `v[2]` and `Len` on the union, an IF
/// yielding either kind, recursive operators over them.
const TUPLE_UNIONS: Case = Case {
    name: "TupleUnions",
    body: r#"EXTENDS Integers, FiniteSets, Sequences
VARIABLES vs, es, log
Round(v) == IF v = <<>> THEN 0 ELSE v[2]
LeaderVertex(r) == IF r > 0 THEN <<IF r % 2 = 1 THEN "a" ELSE "b", r>> ELSE <<>>
RECURSIVE Reach(_, _)
Reach(S, d) == IF S = {} \/ d = 0 THEN {} ELSE
    LET next == {c \in vs : \E v \in S : <<v, c>> \in es} IN next \cup Reach(next, d - 1)
RECURSIVE Order(_)
Order(S) == IF S = {} THEN <<>> ELSE
    LET e == CHOOSE e \in S : \A f \in S : Round(e) <= Round(f)
    IN Append(Order(S \ {e}), e)
Init == vs = {<<>>} /\ es = {} /\ log = <<>>
Add(n, r) ==
    /\ <<n, r>> \notin vs
    /\ \E parents \in SUBSET {v \in vs : Round(v) = r - 1} :
        /\ parents # {}
        /\ vs' = vs \cup {<<n, r>>}
        /\ es' = es \cup {<<<<n, r>>, p>> : p \in parents}
        /\ log' = IF LeaderVertex(r - 1) \in parents
                     THEN Order((parents \cup Reach(parents, 4)) \ {<<>>})
                     ELSE log
Next == \E n \in {"a", "b"}, r \in 1..3 : Add(n, r)
Inv1 == \A v \in vs \ {<<>>} : Len(v) = 2 /\ Round(v) \in Nat \ {0}
Inv2 == \A e \in es : e = <<e[1], e[2]>> /\ {e[1], e[2]} \subseteq vs
Inv3 == \A i \in DOMAIN log : log[i] # <<>>
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2 Inv3\n",
    shapes: None,
    not_native: &[],
};

#[test]
fn tuple_unions() {
    run(&TUPLE_UNIONS);
}

/// Bitsets of records with a set-valued field (ranked through the field's
/// bitset) and `SetToSeq` of a set mapped from a temp.
const SET_FIELDS: Case = Case {
    name: "SetFields",
    body: r#"EXTENDS Naturals, FiniteSets, Sequences
VARIABLES net, hold, log
Clients == {"c1", "c2"}
Res == {"r1", "r2"}
IsInjective(f) == \A a, b \in DOMAIN f : f[a] = f[b] => a = b
SetToSeq(S) == CHOOSE f \in [1..Cardinality(S) -> S] : IsInjective(f)
Init == net = {} /\ hold = [c \in Clients |-> {}] /\ log = <<>>
Send(c, S) == S # {} /\ hold[c] = {} /\ net' = net \cup {[clt |-> c, rsrc |-> S]} /\ UNCHANGED <<hold, log>>
Recv == \E m \in net : m.rsrc \subseteq Res /\ hold' = [hold EXCEPT ![m.clt] = @ \cup m.rsrc] /\ net' = net \ {m} /\ UNCHANGED log
Note == Len(log) < 2 /\ log' = log \o SetToSeq({m.clt : m \in {x \in net : x.rsrc # {}}}) /\ UNCHANGED <<net, hold>>
Free(c) == hold[c] # {} /\ hold' = [hold EXCEPT ![c] = {}] /\ UNCHANGED <<net, log>>
Next == (\E c \in Clients, S \in SUBSET Res : Send(c, S)) \/ Recv \/ Note \/ (\E c \in Clients : Free(c))
Inv1 == \A m \in net : m.rsrc # {} /\ m.clt \in Clients
Inv2 == [clt |-> "c1", rsrc |-> hold["c1"]] \in net => hold["c1"] = {}
Inv3 == \E m \in net \cup {[clt |-> "c2", rsrc |-> Res]} : m.rsrc = Res \/ m.clt = "c1"
Sent == [][\E c \in Clients, S \in SUBSET Res : net' = net \cup {[clt |-> c, rsrc |-> S]} \/ net' = net \/ net' \subseteq net]_<<net, hold, log>>
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2 Inv3\nPROPERTY Sent\n",
    shapes: None,
    // An action iterates in TLC's order, which the encoded order of such
    // records is not: boxed iteration (a host region in mixed mode).
    not_native: &["action Recv"],
};

/// A record kept up to date with `:>` and `@@` (a map over its field names
/// whose values have different kinds: integers and a tuple), read with
/// `r.f`, updated through a CASE and 0-ary definitions standing for
/// operator calls; a recursive operator with a scalar result built from a
/// set of integers of unknown bounds; `CHOOSE` over records with a
/// sequence field (encoded order is not TLC's: one witness is taken,
/// several fail over to the interpreter); a sequence of records copied
/// into a message whose record shape has other integer ranges.
const HETERO_RECORDS: Case = Case {
    name: "HeteroRecords",
    body: r#"EXTENDS Integers, Sequences, FiniteSets, TLC
VARIABLES rec, hist, inbox, acks
Minimum(S) == IF S = {} THEN -1 ELSE CHOOSE n \in S : \A m \in S : n <= m
RECURSIVE FirstIdx(_, _, _)
FirstIdx(h, v, cur) == IF cur > Len(h) THEN cur
                       ELSE IF h[cur].val = v THEN Minimum({cur, FirstIdx(h, v, cur + 1)})
                       ELSE FirstIdx(h, v, cur + 1)
Inc(k) == k :> rec[k] + 1
Get(k) == k :> rec[k]
IncN == Inc("n")
Upd(tag) == rec' = (CASE tag = "push" -> IncN @@ Get("m") [] OTHER -> Get("n") @@ Inc("m")) @@ ("pc" :> <<tag, Len(hist)>>) @@ rec
Init == /\ rec = [n |-> 0, m |-> 0, pc |-> <<"init", 0>>]
        /\ hist = <<>> /\ inbox = <<>> /\ acks = {}
Push == /\ rec.n < 3 /\ \E v \in 1..2 : hist' = Append(hist, [val |-> v, ep |-> rec.n])
        /\ Upd("push") /\ UNCHANGED <<inbox, acks>>
Send == /\ Len(inbox) < 2 /\ rec.m < 3 /\ inbox' = Append(inbox, [kind |-> "h", hist |-> hist])
        /\ Upd("send") /\ UNCHANGED <<hist, acks>>
Ack == /\ hist # <<>> /\ rec.m < 3 /\ Cardinality(acks) < 3
       /\ \E v \in 1..2 : LET i == FirstIdx(hist, v, 1)
                          IN /\ i <= Len(hist)
                             /\ acks' = acks \cup {[id |-> v, at |-> hist[i].ep, h |-> SubSeq(hist, 1, i)]}
       /\ Upd("ack") /\ UNCHANGED <<hist, inbox>>
Pick == /\ acks # {}
        /\ LET a == CHOOSE a \in acks : a.id = 1 IN rec' = ("m" :> Len(a.h)) @@ rec
        /\ UNCHANGED <<hist, inbox, acks>>
Next == Push \/ Send \/ Ack \/ Pick
Inv1 == rec.n + rec.m <= 6 /\ rec.pc[1] \in {"init", "push", "send", "ack"}
Inv2 == \A a \in acks : a.at <= 3 /\ FirstIdx(hist, a.id, 1) >= 1
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2\n",
    shapes: None,
    not_native: &[],
};

#[test]
fn hetero_records() {
    run(&HETERO_RECORDS);
}

const ALL: &[&Case] = &[
    &HETERO_RECORDS,
    &SCALARS,
    &BITSETS,
    &RECORDS,
    &FUNCTIONS,
    &SEQUENCES,
    &MAPS,
    &SORTED,
    &UNIONS,
    &RECODE,
    &QUANTIFIERS,
    &ENABLED,
    &PRODUCTS,
    &UNION_SETS,
    &RECURSION,
    &RECURSIVE_FNS,
    &BOUND_SETS,
    &TUPLE_UNIONS,
    &SET_FIELDS,
];

#[test]
fn set_fields() {
    run(&SET_FIELDS);
}

#[test]
fn products() {
    run(&PRODUCTS);
}

#[test]
fn scalars() {
    run(&SCALARS);
}

#[test]
fn bitsets() {
    run(&BITSETS);
}

#[test]
fn records() {
    run(&RECORDS);
}

#[test]
fn functions() {
    run(&FUNCTIONS);
}

#[test]
fn sequences() {
    run(&SEQUENCES);
}

#[test]
fn maps() {
    run(&MAPS);
}

#[test]
fn sorted_arrays() {
    run(&SORTED);
}

#[test]
fn unions() {
    run(&UNIONS);
}

#[test]
fn recode() {
    run(&RECODE);
}

#[test]
fn quantifiers() {
    run(&QUANTIFIERS);
}

#[test]
fn enabled() {
    run(&ENABLED);
}

/// The cases together exercise the IR node kinds of the encoded tier.
#[test]
fn ir_node_coverage() {
    let mut kinds = BTreeSet::new();
    for c in ALL {
        let src = module(c.name, c.body);
        let h = match c.shapes {
            Some(f) => Harness::with_shapes(&src, c.cfg, f()),
            None => Harness::new(&src, c.cfg),
        };
        kinds.extend(h.node_kinds());
    }
    let required = [
        "Assign",
        "Branches",
        "Emit",
        "ForEach",
        "Guard",
        "Repeat",
        "Count",
        "Error",
        "Const",
        "ConstWords",
        "Var",
        "Temp",
        "Not",
        "And",
        "Or",
        "If",
        "IntBin",
        "IntCmp",
        "Eq",
        "Exists",
        "Forall",
        "Choose",
        "Slice",
        "Index",
        "ExceptAt",
        "ExceptIndex",
        "BitMember",
        "BitSetOp",
        "BitCard",
        "Rank",
        "Concat",
        "BitSet",
        "SeqLen",
        "SeqIndex",
        "SeqTail",
        "SeqAppend",
        "SeqSub",
        "SeqFilter",
        "SeqConcat",
        "SortedOp",
        "SortedMember",
        "SortedInsert",
        "UnionField",
        "UnionFieldInt",
        "IntRange",
        "Filter",
        "MapSet",
        "RankFlat",
        "Recode",
        "RankUnion",
        "Lookup",
        "Fail",
        "NextVar",
        "Neg",
        "MapGet",
        "MapPut",
        "MapBuild",
        "MapMerge",
        "Enabled",
        "Call",
        "Collect",
    ];
    let missing: Vec<&str> = required.iter().copied().filter(|k| !kinds.contains(k)).collect();
    if verbose() {
        note(&format!("IR node kinds exercised: {kinds:?}"));
    }
    assert!(missing.is_empty(), "IR node kinds not exercised by any case: {missing:?}\nexercised: {kinds:?}");
}

/// Model-checking each case gives the same result (outcome, error message,
/// state counts, depth, trace length) in the interpreter and
/// `-compile` (`tlx_testkit::spec::assert_modes_agree`).
#[test]
fn tiers_agree() {
    for c in ALL {
        // (Fixed shapes are a harness concern; the tiers speculate their own.)
        let s = tlx_testkit::spec::assert_modes_agree(&module(c.name, c.body), c.cfg);
        if verbose() {
            note(&format!("{}: {s:?}", c.name));
        }
    }
}

// ---------------------------------------------------------------------------
// Hand-written IR: node forms the lowering does not produce today

/// `[f EXCEPT ![arg] = v]` whose index expression fails: TLC and the
/// interpreter report the error, generated C bails out (`TLX_ERR`), and the
/// IR executor must fail too rather than treat the failure as "not in the
/// domain" and return `f` unchanged (former divergence D1,
/// from the 2026-10 code-health review). The lowering currently
/// binds failing index expressions in a `Let` first, so only hand-written IR
/// reaches it.
#[test]
fn except_index_error_in_index() {
    use tlx_compile::ir::{ActionFn, Expr, ExprKind, IndexMap, IntOp, SlotLayout, Stmt, Ty};
    let src = module(
        "ExceptIndexErr",
        "EXTENDS Integers\nVARIABLE f\nInit == f = <<0, 0, 0>>\nBad == f' = [f EXCEPT ![1 \\div (f[1] - f[1])] = 1]\nNext == Bad\n",
    );
    let elem = Shape::Int { lo: 0, hi: 2 };
    let shapes = vec![Shape::Tuple(Arc::from(vec![elem.clone(), elem.clone(), elem.clone()]))];
    let h = Harness::with_ir(&src, CFG, shapes, &mut |t, actions| {
        let f = t.var_sid[0];
        let e = t.id(&elem);
        let lit = |i: i64| Expr::new(Ty::Int, ExprKind::Const(Value::Int(i)));
        let arg = Expr::new(Ty::Int, ExprKind::IntBin(IntOp::DivFloor, lit(1), lit(0)));
        let value = Expr::new(Ty::Enc(e), ExprKind::ConstWords(Arc::from(vec![1u64])));
        let except = ExprKind::ExceptIndex {
            base: Expr::new(Ty::Enc(f), ExprKind::Var(0)),
            arg,
            map: IndexMap::IntRange { lo: 1, n: 3 },
            slot: SlotLayout::Bits(2),
            value,
        };
        let body = Stmt::Assign { var: 0, value: Expr::new(Ty::Enc(f), except), body: Box::new(Stmt::Emit) };
        actions[0] = Some(ActionFn { name: "Bad".into(), temps: Vec::new(), body });
    });
    assert!(h.not_native().is_empty(), "{:?}", h.not_native());
    let rep = h.run_reachable(10);
    if verbose() {
        note(&rep.render());
    }
    rep.assert_ok("ExceptIndex with a failing index");
}

/// Empty maps decode as tuples: a non-integer EXCEPT key is a type error,
/// while absent keys in nonempty maps (and integer keys in empty maps) are ignored.
#[test]
fn empty_map_except_checks_key_type() {
    let src = module(
        "EmptyMapExcept",
        r#"EXTENDS Naturals, TLC
VARIABLE rec
Init == rec = <<>>
Bad == rec' = [rec EXCEPT !["m"] = 2]
Missing == rec' = [rec EXCEPT !["missing"] = 1 \div 0]
Next == Bad \/ Missing
"#,
    );
    let key = atoms(&["m", "missing"]);
    let h = Harness::with_shapes(&src, CFG, vec![Shape::Map { key: Box::new(key), range: Box::new(Shape::Int { lo: 0, hi: 2 }) }]);
    assert!(h.not_native().is_empty(), "{:?}", h.not_native());
    assert!(h.node_kinds().contains("MapPut"));
    let mut rep = h.run_reachable(10);
    h.run_random(&mut Rng::new(123), 100, &mut rep);
    rep.assert_ok("empty map EXCEPT key types");
}

#[test]
fn empty_map_integer_except_ignores_missing_key() {
    let src = module(
        "EmptyMapIntExcept",
        r#"EXTENDS Naturals
VARIABLE rec
Init == rec = <<>>
Next == rec' = [rec EXCEPT ![1] = 1 \div 0]
"#,
    );
    let h = Harness::with_shapes(
        &src,
        CFG,
        vec![Shape::Map { key: Box::new(Shape::Int { lo: 1, hi: 2 }), range: Box::new(Shape::Int { lo: 0, hi: 2 }) }],
    );
    assert!(h.not_native().is_empty(), "{:?}", h.not_native());
    h.run_reachable(10).assert_ok("integer EXCEPT key on an empty map");
}
