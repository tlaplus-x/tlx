---- MODULE Age ----
EXTENDS Naturals
VARIABLE clock, records
Empty == [status |-> "empty", payload |-> ""]
Init == /\ clock = 0 /\ records = [k \in {1} |-> Empty]
Tick == /\ clock' = clock + 1 /\ UNCHANGED records
Put == /\ records' = [records EXCEPT ![1] = [created |-> clock, payload |-> "x"]]
       /\ UNCHANGED clock
Drop == /\ records[1] # Empty /\ records[1].created + 2 <= clock
        /\ records' = [records EXCEPT ![1] = Empty]
        /\ UNCHANGED clock
Next == Tick \/ Put \/ Drop
Inv == /\ clock \in Nat
       /\ records \in [{1} -> [created: Nat, payload: {"x"}] \cup {Empty}]
====
