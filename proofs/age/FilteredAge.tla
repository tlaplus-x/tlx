---- MODULE FilteredAge ----
EXTENDS Naturals, FiniteSets
VARIABLE clock, records, selected
Empty == [status |-> "empty", payload |-> ""]
Init == selected = {} /\ /\ clock = 0 /\ records = [k \in {1} |-> Empty]
Tick == /\ clock' = clock + 1 /\ UNCHANGED <<records, selected>>
Put == /\ records' = [records EXCEPT ![1] = [created |-> clock, payload |-> "x"]]
       /\ UNCHANGED <<clock, selected>>
Drop == /\ records[1] # Empty /\ records[1].created + 2 <= clock
        /\ records' = [records EXCEPT ![1] = Empty]
        /\ UNCHANGED <<clock, selected>>
Scan == selected' = {k \in {1}: records[k] # Empty /\ records[k].created + 2 <= clock}
        /\ UNCHANGED <<clock, records>>
Next == Tick \/ Put \/ Drop \/ Scan
Inv == selected \subseteq {1} /\ /\ clock \in Nat
       /\ records \in [{1} -> [created: Nat, payload: {"x"}] \cup {Empty}]
Past == \A k \in {1}: records[k] = Empty \/ records[k].created <= clock
====
