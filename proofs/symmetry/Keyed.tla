----------------------------- MODULE Keyed -----------------------------
EXTENDS Naturals
CONSTANTS Proc, Limit
VARIABLES pc, audit
Init == /\ pc = [p \in Proc |-> [n |-> 0, done |-> FALSE]]
        /\ audit = [p \in Proc |-> 0]
Advance(p) == /\ pc[p].n < Limit
              /\ pc' = [pc EXCEPT ![p].n = @ + 1]
              /\ UNCHANGED audit
Finish(p) == /\ pc[p].n = Limit
             /\ pc' = [pc EXCEPT ![p].done = TRUE]
             /\ audit' = [audit EXCEPT ![p] = 1]
Reset(p,q) == /\ p # q /\ pc[p].done /\ pc[q].done
              /\ pc' = [pc EXCEPT ![p] = [n |-> 0, done |-> FALSE]]
              /\ audit' = [audit EXCEPT ![p] = IF p = q THEN 2 ELSE 0]
Next == \E p \in Proc : Advance(p) \/ Finish(p) \/ (\E q \in Proc : Reset(p,q))
TypeOK == /\ pc \in [Proc -> [n : Nat, done : BOOLEAN]]
          /\ audit \in [Proc -> Nat]
Inv == /\ TypeOK
       /\ \A p \in Proc : pc[p].n <= Limit
       /\ \A p,q \in Proc : p = q => audit[p] = audit[q]
=============================================================================
