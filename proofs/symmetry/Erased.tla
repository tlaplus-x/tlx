----------------------------- MODULE Erased -----------------------------
EXTENDS Naturals, TLC
CONSTANTS Proc, Limit
VARIABLES snapshot, previous, pc
Init == /\ snapshot = FALSE /\ previous = FALSE
        /\ pc = [p \in Proc |-> [n |-> 0, done |-> FALSE]]
Step(p) == /\ pc[p].n < Limit
           /\ pc' = [pc EXCEPT ![p].n = @ + 1, ![p].done = TRUE]
           /\ snapshot' = pc /\ previous' = snapshot
Swap == /\ snapshot' = previous /\ previous' = snapshot /\ UNCHANGED pc
Forget == /\ snapshot' = FALSE /\ previous' = TRUE /\ UNCHANGED pc
Next == (\E p \in Proc : Step(p)) \/ Swap \/ Forget
Inv == \A p \in Proc : pc[p].n <= Limit /\ pc[p].done \in BOOLEAN
=============================================================================
