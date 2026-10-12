---- MODULE DependentHistory ----
EXTENDS Naturals, Sequences, FiniteSets
VARIABLE clock, records, selected, history
Keys == {1, 2}
Empty == [status |-> "empty", payload |-> ""]
Ready == \A i \in 1..Len(history): history[i] = "drop" =>
             \E j \in 1..i: history[j] = "put"
Eligible == IF Ready /\ history # <<>> THEN Keys ELSE {1}
Expired == {k \in Eligible: records[k] # Empty /\ records[k].created + 2 <= clock}
Init == /\ clock = 0 /\ records = [k \in Keys |-> Empty]
        /\ selected = {} /\ history = <<>>
Tick == /\ clock' = clock + 1 /\ UNCHANGED <<records, selected, history>>
Put == \E k \in Eligible:
         /\ records' = [records EXCEPT ![k] =
              [created |-> clock, payload |-> IF history = <<>> THEN "x" ELSE "y"]]
         /\ history' = Append(history, "put") /\ UNCHANGED <<clock, selected>>
Drop == \E k \in Keys:
          /\ records[k] # Empty
          /\ records' = IF Ready /\ records[k].created + 2 <= clock
                        THEN [records EXCEPT ![k] = Empty] ELSE records
          /\ history' = Append(history,
               IF records[k].created + 2 <= clock THEN "drop" ELSE "put")
          /\ UNCHANGED <<clock, selected>>
Scan == /\ selected' = Expired /\ UNCHANGED <<clock, records, history>>
Next == Tick \/ Put \/ Drop \/ Scan
Inv == /\ clock \in Nat /\ selected \subseteq Keys
       /\ records \in [Keys -> [created: Nat, payload: {"x", "y"}] \cup {Empty}]
       /\ history \in Seq({"put", "drop"})
Computed == Expired \subseteq Keys
====
