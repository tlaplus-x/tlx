----------------------------- MODULE KeyedSeven -----------------------------
EXTENDS Naturals
CONSTANTS Proc, Limit
VARIABLES pc
Init == pc = [p \in Proc |-> [n |-> 0, done |-> FALSE]]
Advance(p) == /\ pc[p].n < Limit
              /\ pc' = [pc EXCEPT ![p].n = @ + 1]
Finish(p) == /\ pc[p].n = Limit
             /\ pc' = [pc EXCEPT ![p].done = TRUE]
Next == \E p \in Proc : Advance(p) \/ Finish(p)
Inv == \A p \in Proc : pc[p].n <= Limit
=============================================================================
