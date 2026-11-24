//! Property tests: random states of fixed layout shapes, wider than what the
//! specs reach, checked in the IR executor, native code and the interpreter
//! (`tlx_testkit::diff`). Each family pairs a shape with a spec whose
//! actions and invariants work on any value of it.
//!
//! Default: `STATES` random states per family (fast). More:
//! - `TLX_PROP_STATES=n`: states per family and seed;
//! - `cargo test --release -p tlx-compile --test exec_vs_native_random -- --ignored`
//!   runs `many_seeds` (`TLX_PROP_SEEDS` seeds, default 20);
//! - `TLX_SEED=n` replays one seed; `TLX_DIFF_VERBOSE=1` prints tallies.

use std::sync::Arc;

use tlx_layout::Shape;
use tlx_testkit::diff::{DiffReport, Harness};
use tlx_testkit::{module, note, seed, Rng};
use tlx_value::{Sym, Value};

const STATES: usize = 1000;

fn states() -> usize {
    std::env::var("TLX_PROP_STATES").ok().and_then(|s| s.parse().ok()).unwrap_or(STATES)
}

fn int(lo: i64, hi: i64) -> Shape {
    Shape::Int { lo, hi }
}

/// The shape of a record value with the given fields (field order is the
/// layout's).
fn record(fields: &[(&str, Shape)]) -> Shape {
    let probe = Value::record(fields.iter().map(|(n, _)| (Sym::new(n), Value::Int(0))).collect());
    let Shape::Record(order) = Shape::of(&probe) else { unreachable!() };
    Shape::Record(order.iter().map(|(k, _)| (*k, fields.iter().find(|(n, _)| Sym::new(n) == *k).unwrap().1.clone())).collect())
}

struct Family {
    name: &'static str,
    body: &'static str,
    cfg: &'static str,
    shapes: fn() -> Vec<Shape>,
}

/// Sets of records too large for a bitset (sorted arrays), with an integer.
fn sorted_shapes() -> Vec<Shape> {
    let rec = record(&[("k", int(0, 99)), ("v", int(0, 99))]);
    vec![Shape::Set { elem: Box::new(rec), max_card: 4 }, int(0, 99)]
}

const SORTED: Family = Family {
    name: "PropSorted",
    body: r#"EXTENDS Naturals, FiniteSets
VARIABLES S, n
Init == S = {} /\ n = 0
Ins == S' = S \cup {[k |-> n, v |-> (n * 7) % 100]} /\ n' = (n + 1) % 100
Del == \E m \in S : S' = S \ {m} /\ n' = m.k
Flt == S' = {m \in S : m.v > n} /\ n' = n
Mrg == S' = S \cup {[k |-> 1, v |-> 2], [k |-> n, v |-> n]} /\ n' = Cardinality(S)
Int == S' = S \cap {[k |-> n, v |-> n]} /\ n' = n
Next == Ins \/ Del \/ Flt \/ Mrg \/ Int
Inv1 == \A m \in S : m.k + m.v < 150
Inv2 == [k |-> n, v |-> n] \in S \/ Cardinality(S) # 3
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2\n",
    shapes: sorted_shapes,
};

/// Sequences of pairs.
fn seq_shapes() -> Vec<Shape> {
    let pair = Shape::Tuple(Arc::from(vec![int(0, 3), Shape::Bool]));
    vec![Shape::Seq { elem: Box::new(pair), max_len: 5 }]
}

const SEQS: Family = Family {
    name: "PropSeqs",
    body: r#"EXTENDS Naturals, Sequences
VARIABLE q
Init == q = <<>>
Push == \E i \in 0..3 : q' = Append(q, <<i, i > 1>>)
Pop == q' = Tail(q)
Cat == q' = q \o SubSeq(q, 2, 3)
Flt == q' = SelectSeq(q, LAMBDA e : e[2])
Upd == Len(q) > 0 /\ q' = [q EXCEPT ![1] = <<(@[1] + 1) % 4, ~@[2]>>]
Next == Push \/ Pop \/ Cat \/ Flt \/ Upd
Inv1 == \A i \in 1..Len(q) : q[i][1] <= 3
Inv2 == Len(q) = 0 \/ Head(q)[2] \/ q[Len(q)][1] # 7
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2\n",
    shapes: seq_shapes,
};

/// Functions with a varying domain (maps) to records.
fn map_shapes() -> Vec<Shape> {
    let rec = record(&[("a", int(0, 3)), ("b", Shape::Bool)]);
    vec![Shape::Map { key: Box::new(int(0, 4)), range: Box::new(rec), witness: tlx_layout::FcnWitness::Enumerated }, int(0, 4)]
}

const MAPS: Family = Family {
    name: "PropMaps",
    body: r#"EXTENDS Naturals, TLC
VARIABLES m, k
Init == m = [i \in {} |-> [a |-> 0, b |-> FALSE]] /\ k = 0
Put == k \notin DOMAIN m /\ m' = m @@ (k :> [a |-> k % 4, b |-> TRUE]) /\ k' = (k + 1) % 5
Upd == m' = [m EXCEPT ![k] = [@ EXCEPT !.a = (@ + 1) % 4]] /\ k' = k
Get == k \in DOMAIN m /\ m' = m /\ k' = m[k].a
Del == \E j \in DOMAIN m : m' = [i \in DOMAIN m \ {j} |-> m[i]] /\ k' = j
Next == Put \/ Upd \/ Get \/ Del
Inv1 == \A i \in DOMAIN m : m[i].a <= 3
Inv2 == k \in DOMAIN m => m[k].b \/ m[k].a >= 0
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2\n",
    shapes: map_shapes,
};

/// A union of record kinds and a bitset of small integers.
fn union_shapes() -> Vec<Shape> {
    let req = record(&[("type", Shape::Atom(Arc::from(vec![Value::str("ack"), Value::str("req")]))), ("src", int(0, 3))]);
    let ack =
        record(&[("type", Shape::Atom(Arc::from(vec![Value::str("ack"), Value::str("req")]))), ("src", int(2, 6)), ("ok", Shape::Bool)]);
    vec![Shape::Union(Arc::from(vec![req, ack])), Shape::Set { elem: Box::new(int(0, 6)), max_card: 7 }]
}

const UNIONS: Family = Family {
    name: "PropUnions",
    body: r#"EXTENDS Naturals
VARIABLES msg, seen
Init == msg = [type |-> "req", src |-> 0] /\ seen = {}
Req == \E s \in 0..3 : msg' = [type |-> "req", src |-> s] /\ seen' = seen
Ack == msg' = [type |-> "ack", src |-> msg.src + 2, ok |-> msg.src > 1] /\ seen' = seen \cup {msg.src}
Ok == msg.type = "ack" /\ msg.ok /\ msg' = msg /\ seen' = seen \ {msg.src}
Bad == msg' = msg /\ seen' = IF msg.ok THEN {} ELSE {0}
Next == Req \/ Ack \/ Ok \/ Bad
Inv1 == msg.src \in seen \/ msg.src \notin seen
Inv2 == msg.type = "ack" => msg.src >= 2
"#,
    cfg: "INIT Init\nNEXT Next\nINVARIANT Inv1 Inv2\n",
    shapes: union_shapes,
};

const ALL: &[&Family] = &[&SORTED, &SEQS, &MAPS, &UNIONS];

fn check(f: &Family, seeds: &[u64]) {
    let h = Harness::with_shapes(&module(f.name, f.body), f.cfg, (f.shapes)());
    assert!(h.notes.is_empty(), "{}: not lowered: {:?}", f.name, h.notes);
    let mut rep = DiffReport::default();
    h.check_init(&mut rep);
    for &s in seeds {
        h.run_random(&mut Rng::new(s), states(), &mut rep);
    }
    if std::env::var_os("TLX_DIFF_VERBOSE").is_some() {
        note(&format!("== {} (seeds {seeds:?})\nnot native: {:?}\n{}", f.name, h.not_native(), rep.render()));
    }
    rep.assert_ok(&format!("{} (seeds {seeds:?}; replay with TLX_SEED)", f.name));
    let (e, n) = rep.totals();
    assert!(e.agree > 0 && n.agree > 0, "{}: nothing compared\n{}", f.name, rep.render());
}

#[test]
fn random_states() {
    for f in ALL {
        check(f, &[seed(1)]);
    }
}

/// Slow: many seeds per family.
#[test]
#[ignore = "slow; run with --ignored (TLX_PROP_SEEDS, TLX_PROP_STATES)"]
fn many_seeds() {
    let n: u64 = std::env::var("TLX_PROP_SEEDS").ok().and_then(|s| s.parse().ok()).unwrap_or(20);
    let base = seed(1000);
    let seeds: Vec<u64> = (0..n).map(|i| base + i).collect();
    for f in ALL {
        check(f, &seeds);
    }
}
