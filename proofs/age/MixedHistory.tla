---- MODULE MixedHistory ----
EXTENDS Naturals, Sequences, FiniteSets
VARIABLE clock, records, selected, history
Keys == {1, 2}
Empty == [status |-> "empty", payload |-> ""]
Ready == \A i \in 1..Len(history): history[i] = "drop" =>
             \E j \in 1..i: history[j] = "put"
Expired == {k \in Keys: records[k] # Empty /\ records[k].created + 2 <= clock}
Chosen == IF Ready /\ history # <<>> THEN Expired ELSE {}
Init == /\ clock = 0 /\ records = [k \in Keys |-> Empty]
        /\ selected = {} /\ history = <<>>
Tick == /\ clock' = clock + 1 /\ UNCHANGED <<records, selected, history>>
Put == \E k \in Keys:
         /\ records' = [records EXCEPT ![k] = [created |-> clock, payload |-> "x"]]
         /\ history' = Append(history, "put") /\ UNCHANGED <<clock, selected>>
Drop == \E k \in Keys:
          /\ records[k] # Empty /\ records[k].created + 2 <= clock
          /\ records' = [records EXCEPT ![k] = Empty]
          /\ history' = Append(history, "drop") /\ UNCHANGED <<clock, selected>>
Scan == /\ selected' = Chosen /\ UNCHANGED <<clock, records, history>>
Next == Tick \/ Put \/ Drop \/ Scan
Inv == /\ clock \in Nat /\ selected \subseteq Keys
       /\ records \in [Keys -> [created: Nat, payload: {"x"}] \cup {Empty}]
       /\ history \in Seq({"put", "drop"})
Computed == Chosen \subseteq Keys
====
