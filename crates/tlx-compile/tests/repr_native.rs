//! The native comparison arm removes membership regions, including errors
//! hidden in broad speculative atom universes and lowered powerset filters.
use std::sync::Arc;
use tlx_layout::Shape;
use tlx_testkit::diff::{DiffReport, Harness};
use tlx_testkit::module;
use tlx_value::Value;

#[test]
fn atom_membership_truth_and_error_table_stays_native() {
    let src = module(
        "NativeAtomMembership",
        r#"CONSTANTS A, B, C, U
VARIABLE x
Init == x = A
Next == UNCHANGED x
Inv == x \in {A, B}
Other == x \in {C}
Untyped == x \in {U}
Deferred == x \in {A, TRUE}
"#,
    );
    let cfg = "CONSTANTS A = T_a B = T_b C = S_c U = plain\nINIT Init\nNEXT Next\nINVARIANTS Inv Other Untyped Deferred\n";
    let mut values: Vec<_> = ["T_a", "T_b", "S_c", "plain"].into_iter().map(Value::model_value).collect();
    values.push(Value::str("text"));
    values.sort();
    let h = Harness::with_shapes(&src, cfg, vec![Shape::Atom(Arc::from(values.clone()))]);
    assert!(h.not_native().is_empty(), "{:?}", h.not_native());
    let mut report = DiffReport::default();
    for value in values {
        h.check_state(&[value], &mut report);
    }
    report.assert_ok("native membership truth/error table");
    let (ir, native) = report.totals();
    assert!(ir.agree > 0 && native.agree > 0 && ir.both_fail > 0 && native.both_fail > 0, "{}", report.render());
    assert!(!h.dump("Inv").contains("valop \\in"), "{}", h.dump("Inv"));
}

#[test]
fn membership_in_a_lowered_powerset_filter_stays_native() {
    let src = module(
        "NativeSubsetMembership",
        r#"EXTENDS Naturals, FiniteSets
VARIABLES s, t
Init == s = {} /\ t = {1, 2}
Next == \E a, b \in SUBSET {1, 2} : s' = a /\ t' = b
Q(S) == {q \in SUBSET S : Cardinality(q) > 0}
Inv == (s \in Q(t)) <=> (s \subseteq t /\ Cardinality(s) > 0)
"#,
    );
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\n";
    let set = Shape::Set { elem: Box::new(Shape::Int { lo: 1, hi: 2 }), max_card: 2 };
    let h = Harness::with_shapes(&src, cfg, vec![set.clone(), set]);
    let mut report = h.run_reachable(30);
    h.run_random(&mut tlx_testkit::Rng::new(913), 100, &mut report);
    report.assert_ok("native powerset membership");
    assert!(h.not_native().is_empty(), "{:?}\n{}", h.not_native(), h.dump("Inv"));
    assert!(!h.dump("Inv").contains("valop \\in"), "{}", h.dump("Inv"));
}

fn atoms(names: &[&str]) -> Vec<Value> {
    let mut values: Vec<_> = names.iter().map(|s| Value::model_value(s)).collect();
    values.sort();
    values
}

fn check_native(h: &Harness, states: impl IntoIterator<Item = Vec<Value>>) -> DiffReport {
    assert!(h.not_native().is_empty(), "{:?}", h.not_native());
    let mut report = DiffReport::default();
    for state in states {
        h.check_state(&state, &mut report);
    }
    report.assert_ok("native comparisons");
    let (ir, native) = report.totals();
    assert_eq!((ir.bailout, native.bailout, ir.unsupported, native.unsupported), (0, 0, 0, 0), "{}", report.render());
    report
}

#[test]
fn comparable_atoms_prefer_masks_and_word_equality() {
    let src = module(
        "AtomCheapPaths",
        r#"CONSTANTS A, B
VARIABLES x, y
Init == x = A /\ y = B
Next == UNCHANGED <<x, y>>
Member == x \in {A, B}
Pair == x = y
Constant == x = A
"#,
    );
    // Typed model values are comparable within their type, just like strings.
    let vs = atoms(&["T_a", "T_b"]);
    let shape = Shape::Atom(vs.clone().into());
    let h = Harness::with_shapes(
        &src,
        "CONSTANTS A = T_a B = T_b\nINIT Init\nNEXT Next\nINVARIANTS Member Pair Constant\n",
        vec![shape.clone(), shape],
    );
    for name in ["Member", "Pair", "Constant"] {
        assert!(!h.dump(name).contains("Lookup"), "{}", h.dump(name));
    }
    assert!(h.dump("Member").contains("BitMember"), "{}", h.dump("Member"));
    check_native(&h, vs.iter().flat_map(|a| vs.iter().map(move |b| vec![a.clone(), b.clone()])));
}

#[test]
fn atom_pairs_preserve_short_circuit_and_operand_errors() {
    let src = module(
        "AtomPairPaths",
        r#"EXTENDS Naturals
CONSTANTS A, B, C, U
VARIABLES x, y
Init == x = A /\ y = B
Next == UNCHANGED <<x, y>>
Equal == x = y
Reverse == y = x
Unequal == x # y
First == x \in {x, y}
Last == x \in {y, x}
Guarded == (x = x) \/ (x = C)
OperandError == x = (IF 1 \div 0 = 0 THEN y ELSE x)
"#,
    );
    let cfg = "CONSTANTS A = T_a B = T_b C = S_c U = plain\nINIT Init\nNEXT Next\nINVARIANTS Equal Reverse Unequal First Last Guarded OperandError\n";
    let mut xs = atoms(&["T_a", "T_b", "S_c", "plain"]);
    xs.push(Value::str("pair-text"));
    xs.sort();
    // Exercise both identical and different encodings; ranks are not values.
    for ys in [xs.clone(), atoms(&["T_b", "S_c", "plain"])] {
        let h = Harness::with_shapes(&src, cfg, vec![Shape::Atom(xs.clone().into()), Shape::Atom(ys.clone().into())]);
        let report = check_native(&h, xs.iter().flat_map(|x| ys.iter().map(move |y| vec![x.clone(), y.clone()])));
        let (ir, native) = report.totals();
        assert!(ir.both_fail > 0 && native.both_fail > 0, "{}", report.render());
    }
}

fn subsets(values: &[Value]) -> Vec<Value> {
    (0..1usize << values.len())
        .filter_map(|mask| {
            Value::set_from(values.iter().enumerate().filter(|(i, _)| mask & (1 << i) != 0).map(|(_, v)| v.clone()).collect()).ok()
        })
        .collect()
}

#[test]
fn runtime_atom_membership_uses_the_complete_set_mask() {
    let src = module(
        "AtomRuntimeMembership",
        r#"CONSTANTS A, B
VARIABLES x, s
Init == x = A /\ s = {B}
Next == UNCHANGED <<x, s>>
Member == x \in s
NotMember == x \notin s
"#,
    );
    let xs = atoms(&["T_a", "T_b", "S_c", "plain"]);
    for ys in [xs.clone(), atoms(&["T_b", "S_c"])] {
        let shape = Shape::Set { elem: Box::new(Shape::Atom(ys.clone().into())), max_card: ys.len() };
        let h = Harness::with_shapes(
            &src,
            "CONSTANTS A = T_a B = T_b\nINIT Init\nNEXT Next\nINVARIANTS Member NotMember\n",
            vec![Shape::Atom(xs.clone().into()), shape],
        );
        let sets = subsets(&ys);
        let report = check_native(&h, xs.iter().flat_map(|x| sets.iter().map(move |s| vec![x.clone(), s.clone()])));
        assert!(report.totals().0.both_fail > 0, "{}", report.render());
    }
}

#[test]
fn subset_difference_covers_lowered_set_forms_and_different_universes() {
    let src = module(
        "LoweredSubsets",
        r#"EXTENDS Naturals, FiniteSets
VARIABLES s, t
Init == s = {} /\ t = {1, 2}
Next == UNCHANGED <<s, t>>
Direct == s \subseteq t
Constant == {1} \subseteq t
Empty == {} \subseteq t
Filter == {i \in s : i # 2} \subseteq {i \in t : i # 3}
Cup == (s \cup {1}) \subseteq (t \cup {1})
Cap == (s \cap t) \subseteq t
Diff == (s \ t) \subseteq t
Map == {i : i \in s} \subseteq t
Q(S) == {q \in SUBSET S : Cardinality(q) > 0}
Power == s \in Q(t)
"#,
    );
    let cfg = "INIT Init\nNEXT Next\nINVARIANTS Direct Constant Empty Filter Cup Cap Diff Map Power\n";
    let shape = |hi| Shape::Set { elem: Box::new(Shape::Int { lo: 1, hi }), max_card: hi as usize };
    let h = Harness::with_shapes(&src, cfg, vec![shape(3), shape(2)]);
    assert!(h.dump("Direct").contains("Diff"), "{}", h.dump("Direct"));
    let ss = subsets(&[Value::Int(1), Value::Int(2), Value::Int(3)]);
    let ts = subsets(&[Value::Int(1), Value::Int(2)]);
    check_native(&h, ss.iter().flat_map(|s| ts.iter().map(move |t| vec![s.clone(), t.clone()])));
}

#[test]
fn subset_keeps_deferred_filter_errors_and_short_circuit() {
    let src = module(
        "SubsetDeferredErrors",
        r#"EXTENDS Naturals, FiniteSets
VARIABLES s, t
Init == s = {} /\ t = {1, 2}
Next == UNCHANGED <<s, t>>
Filter == s \subseteq {i \in t : i = 1 \/ 1 \div (i - 2) = 0}
Empty == {} \subseteq {i \in t : 1 \div 0 = 0}
Q(S) == {q \in SUBSET S : Cardinality(q) = 0 \/ 1 \div 0 = 0}
Power == s \in Q(t)
Guarded == (s = {}) \/ (s \in Q(t))
"#,
    );
    let shape = Shape::Set { elem: Box::new(Shape::Int { lo: 1, hi: 2 }), max_card: 2 };
    let h = Harness::with_shapes(&src, "INIT Init\nNEXT Next\nINVARIANTS Filter Empty Power Guarded\n", vec![shape.clone(), shape]);
    let sets = subsets(&[Value::Int(1), Value::Int(2)]);
    // Fallible filters may remain boxed: demand exact values/errors in IR,
    // and exact values/errors for each predicate the native plan accepts.
    let mut report = DiffReport::default();
    for s in &sets {
        for t in &sets {
            h.check_state(&[s.clone(), t.clone()], &mut report);
        }
    }
    report.assert_ok("deferred subset errors");
    let (ir, native) = report.totals();
    assert_eq!((ir.bailout, native.bailout), (0, 0), "{}", report.render());
    assert!(ir.both_fail > 0 && native.both_fail > 0, "{}", report.render());
}

#[test]
fn incomparable_subset_uses_membership_instead_of_difference() {
    let src = module(
        "IncomparableSubsets",
        r#"CONSTANTS A, B
VARIABLES s, t
Init == s = {A} /\ t = {B}
Next == UNCHANGED <<s, t>>
Subset == s \subseteq t
Power == s \in SUBSET t
"#,
    );
    let vs = atoms(&["T_a", "T_b", "S_c", "plain"]);
    let shape = Shape::Set { elem: Box::new(Shape::Atom(vs.clone().into())), max_card: vs.len() };
    let h = Harness::with_shapes(
        &src,
        "CONSTANTS A = T_a B = T_b\nINIT Init\nNEXT Next\nINVARIANTS Subset Power\n",
        vec![shape.clone(), shape],
    );
    assert!(!h.dump("Subset").contains("bitDiff"), "{}", h.dump("Subset"));
    let sets = subsets(&vs);
    let report = check_native(&h, sets.iter().flat_map(|s| sets.iter().map(move |t| vec![s.clone(), t.clone()])));
    assert!(report.totals().0.both_fail > 0, "{}", report.render());
}

#[test]
fn atom_tables_are_bounded_before_enumerating_the_product() {
    let src = module(
        "AtomTableBudget",
        r#"CONSTANTS A, B
VARIABLES x, y, s
Init == x = A /\ y = B /\ s = {A}
Next == UNCHANGED <<x, y, s>>
Pair == x = y
Member == x \in s
"#,
    );
    let cfg = "CONSTANTS A = T_a B = S_b\nINIT Init\nNEXT Next\nINVARIANTS Pair Member\n";
    for n in [64, 65] {
        let mut vs = atoms(&["T_a", "S_b"]);
        vs.extend((2..n).map(|i| Value::model_value(&format!("T_extra{i}"))));
        vs.sort();
        let shape = Shape::Atom(vs.into());
        // Large runtime sets must not allocate a table of all 2^n masks.
        let set = Shape::Set { elem: Box::new(shape.clone()), max_card: n };
        let h = Harness::with_shapes(&src, cfg, vec![shape.clone(), shape, set]);
        assert_eq!(h.dump("Pair").contains("Lookup"), n == 64, "{}", h.dump("Pair"));
        assert!(!h.dump("Member").contains("Lookup"), "{}", h.dump("Member"));
        h.run_reachable(2).assert_ok("bounded atom tables retain fallback");
    }
}

#[test]
fn bitset_subset_compares_every_word() {
    let src = module(
        "MultiwordSubsets",
        r#"EXTENDS Naturals, FiniteSets
VARIABLES s, t
Init == s = {} /\ t = {1, 129}
Next == UNCHANGED <<s, t>>
Subset == s \subseteq t
Q(S) == {q \in SUBSET S : Cardinality(q) > 0}
Power == s \in Q(t)
"#,
    );
    let shape = Shape::Set { elem: Box::new(Shape::Int { lo: 1, hi: 129 }), max_card: 129 };
    let h = Harness::with_shapes(&src, "INIT Init\nNEXT Next\nINVARIANTS Subset Power\n", vec![shape.clone(), shape]);
    let sets = subsets(&[Value::Int(1), Value::Int(64), Value::Int(65), Value::Int(129)]);
    assert!(h.dump("Subset").contains("bitDiff"), "{}", h.dump("Subset"));
    check_native(&h, sets.iter().flat_map(|s| sets.iter().map(move |t| vec![s.clone(), t.clone()])));
}

#[test]
fn constant_intervals_keep_single_word_set_iteration() {
    let src = module(
        "IntervalSubsetCost",
        r#"EXTENDS Naturals, FiniteSets
VARIABLES s, t
Init == s = {} /\ t = {1, 2, 3}
Next == UNCHANGED <<s, t>>
Subset == s \subseteq 1..3
Power == s \in SUBSET (1..3)
Runtime == s \subseteq t
Q(S) == {q \in SUBSET S : Cardinality(q) > 0}
Lowered == s \in Q(t)
"#,
    );
    for hi in [7, 63, 64] {
        let shape = Shape::Set { elem: Box::new(Shape::Int { lo: 0, hi }), max_card: hi as usize + 1 };
        let h = Harness::with_shapes(&src, "INIT Init\nNEXT Next\nINVARIANTS Subset Power Runtime Lowered\n", vec![shape.clone(), shape]);
        for name in ["Subset", "Power"] {
            let dump = h.dump(name);
            assert_eq!(dump.contains("forall"), hi < 64, "{name}:\n{dump}");
            assert_eq!(dump.contains("bitDiff"), hi >= 64, "{name}:\n{dump}");
        }
        assert!(h.dump("Runtime").contains("bitDiff"), "{}", h.dump("Runtime"));
        assert!(h.dump("Lowered").contains("bitDiff"), "{}", h.dump("Lowered"));
        let sets = subsets(&[Value::Int(0), Value::Int(1), Value::Int(3), Value::Int(hi)]);
        check_native(&h, sets.iter().flat_map(|s| sets.iter().map(move |t| vec![s.clone(), t.clone()])));
    }
}

#[test]
fn packed_composites_and_except_preserve_neighbor_bits_across_tiers() {
    let src = module(
        "PackedCompositesDiff",
        r#"EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANTS S1, S2, S3
VARIABLES rec, fn_var, mp, seq, msgs

Nodes == {S1, S2, S3}

Init ==
    /\ rec = [a |-> S1, b |-> FALSE, lo |-> -2, hi |-> 3]
    /\ fn_var = [s \in Nodes |-> 0]
    /\ mp = (S1 :> 1) @@ (S3 :> 2)
    /\ seq = <<1, 0>>
    /\ msgs = {[type |-> "1a", bal |-> 0]}

StepRec ==
    /\ rec' = [rec EXCEPT !.b = ~@, !.lo = IF @ < 2 THEN @ + 1 ELSE -2]
    /\ fn_var' = [fn_var EXCEPT ![rec.a] = (@ + 1) % 4]
    /\ UNCHANGED <<mp, seq, msgs>>

StepSeqAndMap ==
    /\ rec' = [rec EXCEPT !.a = IF @ = S1 THEN S2 ELSE IF @ = S2 THEN S3 ELSE S1, !.hi = (@ + 1) % 5]
    /\ mp' = IF S2 \in DOMAIN mp
             THEN [mp EXCEPT ![S2] = (@ + 1) % 4]
             ELSE (S2 :> 3) @@ mp
    /\ seq' = IF Len(seq) < 4
              THEN Append(seq, (rec.hi + 1) % 4)
              ELSE SubSeq(Tail(seq), 1, 2) \o <<0>>
    /\ msgs' = msgs \cup {[type |-> "2b", acc |-> rec.a, bal |-> (rec.hi % 3), ok |-> rec.b]}
    /\ UNCHANGED fn_var

Next == StepRec \/ StepSeqAndMap

InvRec ==
    /\ rec.lo \in -2..2
    /\ rec.hi \in 0..4
    /\ fn_var[rec.a] \in 0..3

InvSeqMap ==
    /\ Len(SelectSeq(seq, LAMBDA x : x > 0)) <= Len(seq)
    /\ \A k \in DOMAIN mp : mp[k] \in 0..3

InvMsgs ==
    /\ \E m \in msgs : m.type = "1a" /\ m.bal >= 0
    /\ Cardinality({m \in msgs : m.type = "2b" /\ m.ok}) <= Cardinality(msgs)
"#,
    );
    let cfg = "CONSTANTS S1 = s1 S2 = s2 S3 = s3\nINIT Init\nNEXT Next\nINVARIANTS InvRec InvSeqMap InvMsgs\n";
    let h = Harness::new(&src, cfg);
    // Verify packed widths (22 words unpacked -> 8 words packed):
    // rec: 4 scalar fields in 1 word; fn_var: 3 * 3-bit ints in 1 word;
    // mp: 1 bitset word + 1 packed slot word = 2 words; seq: 1 len word + 1 packed elem word = 2 words;
    // msgs: bitset over 66-element union of packed message records = 2 words.
    assert_eq!(h.layout.words, 8, "unexpected unpacked layout: {:?}", h.layout.vars);
    assert!(h.not_native().is_empty(), "not native: {:?} (notes: {:?})", h.not_native(), h.notes);
    let mut rep = h.run_reachable(120);
    h.run_random(&mut tlx_testkit::Rng::new(0x715_c0de), 200, &mut rep);
    rep.assert_ok("packed composites differential check");
    let (ir, native) = rep.totals();
    assert_eq!((ir.bailout, native.bailout), (0, 0), "{}", rep.render());
    assert!(ir.agree > 0 && native.agree > 0, "{}", rep.render());
}
