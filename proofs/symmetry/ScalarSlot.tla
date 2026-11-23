--------------------------- MODULE ScalarSlot ---------------------------
EXTENDS Naturals
CONSTANTS Proc
VARIABLES owner, pc

Init == /\ owner = "none"
        /\ pc = [p \in Proc |-> 0]

Acquire(p) == /\ owner = "none"
              /\ pc[p] < 2
              /\ owner' = p
              /\ UNCHANGED pc

Step == /\ owner # "none"
        /\ pc[owner] < 2
        /\ pc' = [pc EXCEPT ![owner] = @ + 1]
        /\ UNCHANGED owner

Release == /\ owner # "none"
           /\ owner' = "none"
           /\ UNCHANGED pc

Next == (\E p \in Proc : Acquire(p)) \/ Step \/ Release

Inv == /\ owner \in Proc \cup {"none"}
       /\ pc \in [Proc -> Nat]
       /\ \A p \in Proc : pc[p] <= 2
=========================================================================
