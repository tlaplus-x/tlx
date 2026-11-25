//! The set family of encoded expressions after it moved out of the three
//! per-backend `encoded.rs` dispatchers into `expr/sets.rs` (cleanup batch
//! A17, standards CODE-02 size review, CODE-03 visible dispatch, CODE-19
//! semantic coverage, CODE-23 refactor proof, HARNESS-21 acceptance
//! accounting).
//!
//! The dispatchers used to carry every family in one `match`; the family is
//! now a `sets.rs` module beside `maps.rs` and `sequences.rs`, and the
//! dispatch stays explicit (an exact arm per `ExprKind`, the `unreachable!`
//! tail catches a kind routed to the wrong family). These tests are the
//! family's own coverage, not a whole-model verdict:
//!
//! - `set_family_agrees_across_tiers` drives six specs whose union lowers all
//!   fifteen node kinds (`BitMember`, `BitSetOp`, `BitCard`, `BitSet`,
//!   `Rank`, `Concat`, `UnionField`, `UnionFieldInt`, `SortedMember`,
//!   `SortedInsert`, `SortedOp`, `Recode`, `RankUnion`, `Lookup`,
//!   `RankFlat`) through the differential harness, so the closure executor
//!   and the native tier (generated C, or the Cranelift library under
//!   `TLX_JIT=1`) agree with the interpreter on every reachable state and on
//!   random states of the layout, including empty and padded sets and the
//!   construction/range error paths;
//! - `set_family_heterogeneous_unions` covers D-31 (mixed record / function /
//!   tuple sets: union, difference in both orders and a comparison error);
//! - `set_family_c_keeps_the_guards` inspects one generated C library per
//!   case and pins the family's idioms: the inlined bit test and popcount
//!   guards, the wordwise `BitSetOp` loop, the static union/recode/lookup
//!   tables, the mixed-radix ranks and the sorted-set helpers, with no host
//!   delegation on the family's path.
//!
//! No single spec lowers every kind (a set of plain integers never reaches
//! the sorted-representation or union-field arms), so the coverage claim is
//! the union of the cases below; each case also states the kinds it must
//! carry, so a silent lowering shift is loud.

use std::sync::Arc;
use tlx_compile::cgen::CGen;
use tlx_layout::Shape;
use tlx_runtime::Model;
use tlx_testkit::diff::{DiffReport, Harness};
use tlx_testkit::{module, seed, Rng};
use tlx_value::Value;

/// The whole family: every `ExprKind` the three `expr/sets.rs` files match.
const FAMILY: [&str; 15] = [
    "BitMember",
    "BitSetOp",
    "BitCard",
    "BitSet",
    "Rank",
    "Concat",
    "UnionField",
    "UnionFieldInt",
    "SortedMember",
    "SortedInsert",
    "SortedOp",
    "Recode",
    "RankUnion",
    "Lookup",
    "RankFlat",
];

/// A bit set over `0..6` grown, shrunk, intersected, filtered and mapped; the
/// empty and the two-element initial sets are both reached.
const BITSETS: &str = r#"EXTENDS Naturals, FiniteSets
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
"#;
const BITSETS_CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2 Inv3 Inv4 Inv5\n";

/// Records in a set use the sorted representation: membership, insertion
/// (bounded by the layout's `max_card`) and the set operations.
const SORTED: &str = r#"EXTENDS Naturals, FiniteSets
VARIABLE msgs
Init == msgs = {}
Send == \E s \in 1..3, v \in {0, 50, 99} : Cardinality(msgs) < 3 /\ msgs' = msgs \cup {[src |-> s, val |-> v, seq |-> <<s, v>>]}
Recv == \E m \in msgs : msgs' = msgs \ {m}
Keep == msgs' = {m \in msgs : m.val > 0}
Both == \E m \in msgs : msgs' = msgs \cap {m, [src |-> 1, val |-> 0, seq |-> <<1, 0>>]}
Next == Send \/ Recv \/ Keep \/ Both
Inv1 == \A m \in msgs : m.src \in 1..3
Inv2 == [src |-> 1, val |-> 0, seq |-> <<1, 0>>] \notin msgs \/ Cardinality(msgs) >= 1
"#;
const SORTED_CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2\n";

/// Three arms, two of them records: union field access picks the offset from a
/// static table and reports `TLX_ERR` on the wrong arm, and the rank of a
/// union value and a boxed construction both run.
const UNIONS: &str = r#"EXTENDS Naturals
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
"#;
const UNIONS_CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2\n";

/// Atoms move between the scalar and the set field: the recode table maps the
/// atom codes and reports a code with no target as an error.
const RECODE: &str = r#"VARIABLES x, y, s
Init == x = "a" /\ y = "c" /\ s = {}
Swap == x' = y /\ y' = x /\ s' = s
Copy == y' = x /\ x' = x /\ s' = s \cup {x}
Turn == x' = (IF x = "a" THEN "b" ELSE "a") /\ y' = y /\ s' = s \cup {y}
Next == Swap \/ Copy \/ Turn
Inv1 == x \in s \/ x \notin s
Inv2 == y # "d"
"#;
const RECODE_CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2\n";

/// A set of constant products and a function over them: membership and the
/// flat mixed-radix rank of a pair, plus the atom lookup table.
const PRODUCTS: &str = r#"EXTENDS Naturals, FiniteSets
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
"#;
const PRODUCTS_CFG: &str = "INIT Init\nNEXT Next\nCONSTANTS P = {p1, p2}\nINVARIANT Inv1 Inv2\n";

/// A union-typed element set with an explicit layout (`union_field_int`'s
/// offset-plus-low word and `RankUnion`'s switch) and a padding `max_card`.
const BOUND_SETS: &str = r#"EXTENDS Naturals
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
"#;
const BOUND_SETS_CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2\n";

/// A record, a function and a tuple in one set (D-31): union, difference in
/// both orders and membership compare by domain first, and comparing a
/// non-function atom with a function stays an error.
const HETERO: &str = r#"EXTENDS Integers, Sequences, FiniteSets
VARIABLES x, n
Rec == [a |-> 1, b |-> 1]
One == [a |-> 1]
Het == {Rec, One, <<-1>>}
Init == x = Het /\ n = 0
Uni == x' = Het \cup {Rec} /\ n' = n + 1
Dif == x' = Het \ {Rec} /\ n' = n + 1
DifRev == x' = {Rec} \ Het /\ n' = n + 1
Mem == x' = x /\ n' = IF Rec \in x /\ One \notin x THEN n + 1 ELSE n
Err == x' = {"", Rec} \ {Rec} /\ n' = n + 1
Next == Uni \/ Dif \/ DifRev \/ Mem \/ Err
Inv == x = Het \/ x = {One, <<-1>>} \/ x = {} \/ x = {"", Rec}
"#;
const HETERO_CFG: &str = "INIT Init\nNEXT Next\nINVARIANT Inv\n";

/// One case of the differential run: a spec, an optional explicit element
/// layout for the union-typed sets, and the kinds the case must lower.
struct Case {
    name: &'static str,
    src: &'static str,
    cfg: &'static str,
    shapes: Option<fn() -> Vec<Shape>>,
    kinds: &'static [&'static str],
}

const CASES: [Case; 6] = [
    Case { name: "SetFamilyBitsets", src: BITSETS, cfg: BITSETS_CFG, shapes: None, kinds: &["BitMember", "BitSetOp", "BitCard", "BitSet"] },
    Case { name: "SetFamilySorted", src: SORTED, cfg: SORTED_CFG, shapes: None, kinds: &["SortedMember", "SortedInsert", "SortedOp"] },
    Case { name: "SetFamilyUnions", src: UNIONS, cfg: UNIONS_CFG, shapes: None, kinds: &["Rank", "Concat", "UnionField", "UnionFieldInt"] },
    Case { name: "SetFamilyRecode", src: RECODE, cfg: RECODE_CFG, shapes: Some(recode_shapes), kinds: &["Recode"] },
    Case { name: "SetFamilyProducts", src: PRODUCTS, cfg: PRODUCTS_CFG, shapes: None, kinds: &["Lookup", "RankFlat"] },
    Case { name: "SetFamilyBoundSets", src: BOUND_SETS, cfg: BOUND_SETS_CFG, shapes: Some(bound_set_shapes), kinds: &["RankUnion"] },
];

fn atoms(names: &[&str]) -> Shape {
    let mut v: Vec<Value> = names.iter().map(|n| Value::str(n)).collect();
    v.sort();
    Shape::Atom(Arc::from(v))
}

/// The recode case's atom universe `{a, b, c}` and a padded set over it.
fn recode_shapes() -> Vec<Shape> {
    vec![atoms(&["a", "b"]), atoms(&["a", "b", "c"]), Shape::Set { elem: Box::new(atoms(&["a", "b", "c"])), max_card: 3 }]
}

/// The union-typed element set: a `{type}` arm, a `{type, v}` arm and a set
/// with a padding `max_card` above the reachable cardinality.
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

impl Case {
    fn harness(&self) -> Harness {
        let src = module(self.name, self.src);
        match self.shapes {
            Some(mk) => Harness::with_shapes(&src, self.cfg, mk()),
            None => Harness::new(&src, self.cfg),
        }
    }
}

/// Every family member is lowered by at least one case, and each case's three
/// tiers agree on every reachable and random state (with the error paths
/// compared, not skipped).
#[test]
fn set_family_agrees_across_tiers() {
    let mut covered: std::collections::BTreeSet<&'static str> = std::collections::BTreeSet::new();
    let (mut exec_agree, mut native_agree, mut both_fail, mut wrong, mut unsupported) = (0, 0, 0, 0, 0);
    for (i, case) in CASES.iter().enumerate() {
        let h = case.harness();
        let kinds = h.node_kinds();
        for k in case.kinds {
            assert!(kinds.contains(k), "{} does not lower {k}: {kinds:?}", case.name);
        }
        covered.extend(kinds.iter().copied());
        assert!(h.notes.is_empty(), "{}: not lowered: {:?}", case.name, h.notes);
        assert!(h.not_native().is_empty(), "{}: not native: {:?} (notes: {:?})", case.name, h.not_native(), h.notes);
        let mut rep = h.run_reachable(400);
        h.run_random(&mut Rng::new(seed(0xa17 + i as u64)), 300, &mut rep);
        rep.assert_ok(case.name);
        let (exec, native) = rep.totals();
        exec_agree += exec.agree;
        native_agree += native.agree;
        both_fail += native.both_fail;
        wrong += exec.wrong + native.wrong;
        unsupported += native.unsupported;
    }
    for k in FAMILY {
        assert!(covered.contains(k), "no case lowers the family member {k}: {covered:?}");
    }
    assert!(exec_agree > 0 && native_agree > 0, "nothing compared");
    // Empty-set membership, a set past its layout, an out-of-range element, a
    // union field on the wrong arm and the recode of an unmapped code are
    // reached and both the interpreter and the compiled tiers report them.
    assert!(both_fail > 0, "no error path compared");
    assert_eq!(unsupported, 0, "a case stopped being native");
    assert_eq!(wrong, 0, "a tier disagreed with the interpreter");
}

/// D-31: a set mixing records, a record and a tuple can be unioned,
/// differenced in both orders and searched for by domain, and comparing a
/// non-function atom with a function is an error. The encoded representation
/// has no layout for such a set, so the native tier declines it
/// (`unsupported`) rather than guessing; the interpreter and the closure
/// executor own the semantics and must still agree on every reachable state.
#[test]
fn set_family_heterogeneous_unions() {
    let h = Harness::new(&module("SetFamilyHetero", HETERO), HETERO_CFG);
    let mut rep: DiffReport = h.run_reachable(200);
    h.run_random(&mut Rng::new(seed(0xd31)), 200, &mut rep);
    rep.assert_ok("heterogeneous set unions");
    let (exec, native) = rep.totals();
    assert!(exec.agree > 0, "the mixed-order union/difference was not computed\n{}", rep.render());
    assert!(exec.both_fail > 0, "the atom-versus-function comparison error was not reached\n{}", rep.render());
    assert_eq!(exec.wrong + native.wrong, 0, "{}", rep.render());
    // The mixed set has no encoded layout: the native tier must decline it,
    // and a future encoding has to come with a real differential check.
    assert!(native.unsupported > 0, "the mixed set gained an encoding; compare it explicitly\n{}", rep.render());
}

/// The generated C keeps the family's guards and stays inline: the bit test,
/// popcount and range check of the bitsets, the wordwise `BitSetOp` loop, the
/// static union/recode/lookup tables with their `TLX_ERR` arms, the
/// mixed-radix ranks, the sorted-set helpers and no host delegation.
#[test]
fn set_family_c_keeps_the_guards() {
    let bitsets = c_of(&CASES[0].harness());
    assert!(bitsets.contains("!tlx_bit("), "BitMember is not an inlined bit test");
    assert!(bitsets.contains("x_[i_] & y_[i_]"), "BitSetOp is not a wordwise loop");
    assert!(bitsets.contains("tlx_card(("), "BitCard is not an inlined popcount");
    assert!(bitsets.contains("if (r_ < 0 || r_ >= "), "BitSet has no range guard");
    assert!(bitsets.contains("[r_ >> 6] |= 1ULL << (r_ & 63);"), "BitSet does not set a bit inline");

    let sorted = c_of(&CASES[1].harness());
    assert!(sorted.contains("!tlx_sorted_member("), "SortedMember is not a bounded search");
    assert!(sorted.contains("!tlx_sorted_insert("), "SortedInsert has no max_card guard");
    assert!(sorted.contains("!tlx_sorted_op("), "SortedOp has no capacity guard");

    let unions = c_of(&CASES[2].harness());
    assert!(unions.contains("int64_t d_ = u_[0] < "), "UnionField does not select its table arm");
    assert!(
        unions.contains("if (d_ < 0) return TLX_ERR;") && unions.contains("(uint64_t)d_ >> 16"),
        "UnionField has no wrong-arm error or bitfield descriptor read"
    );
    assert!(unions.contains("(int64_t)v_ + "), "UnionFieldInt does not add its low word");
    assert!(unions.contains("static const int64_t"), "UnionFieldInt has no low-word table");
    assert!(unions.contains("(int64_t)("), "Rank is not the first word read inline");

    let recode = c_of(&CASES[3].harness());
    assert!(recode.contains("if (c_ >= "), "Recode has no code bound");
    assert!(recode.contains("== (uint64_t)-1) return TLX_ERR;"), "Recode has no unmapped-code error");
    assert!(recode.contains("static const uint64_t"), "Recode has no static code table");

    let products = c_of(&CASES[4].harness());
    assert!(products.contains("static const int32_t"), "Lookup has no static table");
    assert!(products.contains(": (int64_t)-1; })"), "Lookup has no miss value");
    assert!(products.contains("r_ = r_ * "), "RankFlat is not a mixed-radix fold");

    let bsets = c_of(&CASES[5].harness());
    assert!(bsets.contains("switch (x_[0]) {"), "RankUnion is not an arm switch");
    assert!(bsets.contains("default: return TLX_ERR; } (int64_t)r_;"), "RankUnion has no unknown-arm error");

    for c in [&bitsets, &sorted, &unions, &recode, &products, &bsets] {
        assert!(!c.contains("host->"), "the set family was sent to the host");
    }
}

/// The generated C of one case.
fn c_of(h: &Harness) -> String {
    let verified =
        tlx_compile::verify::Program::new(&h.typing, h.init.as_ref(), &h.actions, &h.invariants, &h.aprops).expect("valid lowered IR");
    let refops = tlx_compile::exec::refops::RefOpTable::of(&verified);
    let mut gen = CGen::new(&verified).with_refops(refops);
    gen.library(h.base.action_names(), h.base.invariant_names()).src
}

/// A constant table indexed by a computed index (`Tbl[i]`), the shape that
/// makes a `\A`/`\E` over such a table a host region: the table is one boxed
/// value (its rows need not share an encoding) and no loop can iterate it.
/// `Tbl[i]` is one typed loop per row instead, and a row that is not reached
/// because the index is outside the table stays an error (the interpreter
/// reports it; the compiled tiers return `TLX_ERR`).
const TABLE: &str = r#"EXTENDS Naturals, Sequences, FiniteSets
Tbl == <<1..2, 3..4, {}>>
VARIABLES i, n
Init == i = 1 /\ n = 0
Up == \E k \in 1..4 : i' = k /\ n' = n
Mark == n' = (n + 1) % 3 /\ i' = i
Next == Up \/ Mark
AllIn == \A e \in Tbl[i] : e <= 4
SomeIn == \E e \in Tbl[i] : e = 3
AllEach == \A k \in 1..3 : \A e \in Tbl[k] : e <= 4
SomeEach == \E k \in 1..3 : \E e \in Tbl[k] : e = 3
"#;
const TABLE_CFG: &str = "INIT Init\nNEXT Next\nINVARIANT AllIn SomeIn AllEach SomeEach\n";

/// An interval intersected with another one, with computed bounds
/// (`(1..a) \cap (1..b)`): the generic lowering boxes both operands and then
/// the whole quantifier. The pieces are ascending, so the elements are
/// visited in TLC's order - which decides, below, whether a body error is
/// reached before the element that would short-circuit past it.
const INTERVALS: &str = r#"EXTENDS Naturals, Sequences, FiniteSets
VARIABLES a, b, n
Init == a = 0 /\ b = 0 /\ n = 0
IncA == a < 4 /\ a' = a + 1 /\ b' = b /\ n' = (n + 1) % 2
IncB == b < 4 /\ b' = b + 1 /\ a' = a /\ n' = (n + 1) % 2
Next == IncA \/ IncB
CapAll == \A k \in (1..a) \cap (1..b) : k <= 4
CapSome == \E k \in (1..a) \cap (1..b) : k = 3
Interior == \A k \in (1..a) \cap 2..4 : k <= 4
DiffAll == \A k \in (1..a) \ (2..b) : k <= 4
DiffSome == \E k \in (1..a) \ (2..b) : k = 3
OrderE == \E k \in (1..a) \cap (1..b) : (k = 2 /\ 1 \div 0 = 1) \/ k = 4
OrderA == \A k \in (1..a) \cap (1..b) : k # 2 \/ 1 \div 0 = 1
OrderD == \E k \in (1..a) \ (2..b) : (k = 1 /\ 1 \div 0 = 1) \/ k = 4
"#;
const INTERVALS_CFG: &str = "INIT Init\nNEXT Next\nINVARIANT CapAll CapSome Interior DiffAll DiffSome OrderE OrderA OrderD\n";

/// Both domain families stay native: no host delegation in the generated C,
/// every function native, and the three tiers agree on every reachable state
/// and on random states - including the empty table row, the intersection
/// that is empty, the index outside the table, and the two bodies that error
/// at the second element (only TLC's element order reaches them).
#[test]
fn set_family_quantifier_domains_agree_across_tiers() {
    let cases = [("table", TABLE, TABLE_CFG), ("intervals", INTERVALS, INTERVALS_CFG)];
    let (mut agree, mut both_fail) = (0, 0);
    let mut broke = Vec::new();
    for (i, (name, src, cfg)) in cases.iter().enumerate() {
        let h = Harness::new(&module(&format!("SetFamilyQuant{name}"), src), cfg);
        // Both families are native end to end: a domain the code generators
        // cannot iterate makes the whole quantifier one host region, and the
        // harness builds its library without any region.
        for (what, ok) in [
            ("not lowered", h.notes.is_empty()),
            ("not native", h.not_native().is_empty()),
            ("sent to the host", !h.c_src.contains("host->")),
        ] {
            if !ok {
                broke.push(format!("{name}: {what}: {:?}", h.not_native()));
            }
        }
        let mut rep = h.run_reachable(400);
        h.run_random(&mut Rng::new(seed(0x9f3 + i as u64)), 300, &mut rep);
        let (exec, native) = rep.totals();
        agree += exec.agree + native.agree;
        both_fail += exec.both_fail + native.both_fail;
        if exec.wrong + native.wrong > 0 || !rep.failures.is_empty() {
            broke.push(format!("{name}: a tier disagreed with the interpreter\n{}", rep.render()));
        }
    }
    assert!(broke.is_empty(), "{}", broke.join("\n"));
    assert!(agree > 0, "nothing compared");
    // The index outside the table, the empty table row and the body errors
    // are reached and reported by the interpreter and both compiled tiers.
    assert!(both_fail > 0, "no error path compared");
}
