//! The closure-compiled IR executor (`exec::fast`) against native code and
//! the interpreter (the differential harness, `tlx_testkit::diff`), on
//! constructs whose
//! encodings use scratch staging (sets of sequences: sorted arrays built by
//! `MapSet`, `SortedInsert`, `SortedOp`) and on the executor's own
//! shortcuts (values modified in place, `LET` temps aliasing values,
//! EXCEPT built in the next state).

use tlx_testkit::diff::{DiffReport, Harness};
use tlx_testkit::{module, seed, Rng};

const BODY: &str = r#"
EXTENDS Naturals, Sequences
VARIABLES s, n
Init == s = {<<>>} /\ n = 0
Grow == n < 3 /\ n' = n + 1 /\ s' = {Append(t, n) : t \in s} \cup s
Pick == n > 0 /\ \E t \in s : Len(t) > 0 /\ s' = (s \ {t}) \cup {Tail(t)} /\ UNCHANGED n
Keep == n > 1 /\ s' = {t \in s : Len(t) # 1} /\ n' = n - 1
Next == Grow \/ Pick \/ Keep
Inv == \A t \in s : Len(t) <= 3
"#;

#[test]
fn sets_of_sequences() {
    let h = Harness::new(&module("FastSeqSets", BODY), "INIT Init\nNEXT Next\nINVARIANT Inv\n");
    let kinds = h.node_kinds();
    assert!(kinds.contains("MapSet") || kinds.contains("SortedInsert") || kinds.contains("SortedOp"), "{kinds:?}");
    let mut rep: DiffReport = h.run_reachable(400);
    h.run_random(&mut Rng::new(seed(0xfa57)), 200, &mut rep);
    rep.assert_ok("sets of sequences");
}

const SHORTCUTS: &str = r#"
EXTENDS Naturals, Sequences
VARIABLES f, r, q
P == 1..3
Init == f = [p \in P |-> 0] /\ r = [a |-> 0, b |-> <<>>] /\ q = <<>>
\* Nested EXCEPTs, in the next state and on a LET-bound copy.
Bump(p) == /\ f[p] < 2
           /\ f' = [f EXCEPT ![p] = @ + 1, ![(p % 3) + 1] = @]
           /\ LET g == [f EXCEPT ![p] = 2] IN r' = [r EXCEPT !.a = g[p] + f[p], !.b = Append(@, p)]
           /\ UNCHANGED q
\* A LET-bound record field and sequence, then modified copies of them.
Push(p) == /\ Len(q) < 2
           /\ LET s == r.b
                   t == IF s = <<>> THEN <<p>> ELSE Append(Tail(s), p)
               IN /\ q' = Append(q, Len(t))
                  /\ r' = [r EXCEPT !.b = IF Len(t) < 3 THEN t ELSE <<>>]
           /\ UNCHANGED f
\* A CHOOSE bound by a LET, used after another quantifier.
Pick == /\ q # <<>>
        /\ LET c == CHOOSE p \in P : f[p] = 2 \/ p = 3
            IN /\ \A x \in P : f[x] <= 2
               /\ f' = [f EXCEPT ![c] = 0]
               /\ q' = Tail(q)
        /\ UNCHANGED r
Next == \E p \in P : Bump(p) \/ Push(p) \/ Pick
Inv == /\ \A p \in P : f[p] <= 2
       /\ LET g == [f EXCEPT ![1] = 5] IN g[1] = 5 /\ \A p \in 2..3 : g[p] = f[p]
       /\ Len(r.b) <= 3
"#;

#[test]
fn executor_shortcuts() {
    let h = Harness::new(&module("FastShortcuts", SHORTCUTS), "INIT Init\nNEXT Next\nINVARIANT Inv\n");
    let kinds = h.node_kinds();
    assert!(kinds.contains("ExceptIndex") || kinds.contains("ExceptAt"), "{kinds:?}");
    assert!(h.actions.iter().all(Option::is_some), "{:?}", h.notes);
    let mut rep: DiffReport = h.run_reachable(2000);
    h.run_random(&mut Rng::new(seed(0x5c07)), 300, &mut rep);
    rep.assert_ok("executor shortcuts");
    let (exec, _) = rep.totals();
    assert!(exec.agree > 1000 && exec.wrong == 0, "{}", rep.render());
}

const DYNAMIC_BITSET_CHOOSE: &str = r#"
EXTENDS Naturals
VARIABLE x
Init == x = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24}
Next == IF 24 \in x THEN x' = x \ {24} ELSE x' = x
Inv ==
    /\ (CHOOSE s \in SUBSET x : TRUE) = {}
    /\ (CHOOSE s \in SUBSET x : 2 \in s) = {2}
"#;

/// `CHOOSE` over `SUBSET x` where `x` is a 24-element bitset state variable
/// (`ExprKind::Subsets`): both the closure executor (`Src::Subsets`) and
/// native code must stream combinations on demand without allocating `2^24`
/// subsets upfront or bailing out to the interpreter.
#[test]
fn choose_over_dynamic_bitset_subsets_streams() {
    let h =
        Harness::new(&module("FastSubsetsChoose", DYNAMIC_BITSET_CHOOSE), "INIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n");
    let kinds = h.node_kinds();
    assert!(kinds.contains("Subsets") && kinds.contains("Choose"), "{kinds:?}");
    let rep: DiffReport = h.run_reachable(10);
    rep.assert_ok("dynamic bitset CHOOSE");
    let (exec, native) = rep.totals();
    assert!(
        exec.agree >= 2 && exec.bailout == 0 && exec.wrong == 0 && native.agree >= 2 && native.bailout == 0 && native.wrong == 0,
        "{}",
        rep.render()
    );
}
