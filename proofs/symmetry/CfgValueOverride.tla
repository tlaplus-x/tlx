-------------------------------- MODULE CfgValueOverride ---------------------------------
\* `.cfg` value assignments on zero-arity definitions (`Def = value`, docs/compat.md
\* D-23). The runtime binds the configured literal to the OpDefNode every copy
\* shares, so `NoVal`, `Slot`, and `Tag` never run their shadowed bodies (an
\* unbounded `CHOOSE` and `Nat`). The certified lowering splices the literals in
\* as `CfgLiteral` leaves and records one override obligation per applied site.
EXTENDS Naturals, FiniteSets
CONSTANT Proc
VARIABLES owner, store, rank

NoVal == CHOOSE v : v \notin Proc
Slot == Nat
Tag == "unset"

Init == /\ owner = NoVal
        /\ store = [p \in Proc |-> Tag]
        /\ rank = [p \in Proc |-> 0]

Fill(p) == /\ owner = NoVal
           /\ owner' = p
           /\ UNCHANGED <<store, rank>>

Write(p) == /\ owner = p
            /\ store[p] = Tag
            /\ rank[p] < 1
            /\ store' = [store EXCEPT ![p] = NoVal]
            /\ rank' = [rank EXCEPT ![p] = @ + 1]
            /\ UNCHANGED owner

Next == \E p \in Proc : Fill(p) \/ Write(p)

Inv == /\ owner \in Proc \cup {NoVal}
       /\ \A p \in Proc : store[p] = Tag \/ store[p] = NoVal
       /\ \A p \in Proc : rank[p] \in Slot
==========================================================================================
