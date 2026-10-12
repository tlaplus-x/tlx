---- MODULE HistoryFeedback ----
EXTENDS Naturals, Sequences, FiniteSets
VARIABLE clock, records, selected, history
Empty == [status |-> "empty", payload |-> ""]
Ready == \A i \in 1..Len(history): history[i] = "drop" =>
             \E j \in 1..i: history[j] = "put"

Init == /\ clock = 0 /\ records = [k \in {1} |-> Empty]
        /\ selected = {} /\ history = <<>>
Tick == /\ Ready /\ clock' = clock + 1 /\ UNCHANGED <<records, selected, history>>
Put == /\ records' = [records EXCEPT ![1] = [created |-> clock, payload |-> "x"]]
       /\ history' = (IF history = <<>> THEN <<"put">> ELSE Append(history, "put")) /\ UNCHANGED <<clock, selected>>
Drop == /\ records[1] # Empty /\ records[1].created + 2 <= clock
        /\ records' = [records EXCEPT ![1] = Empty]
        /\ history' = Append(history, IF Ready THEN "drop" ELSE "put") /\ UNCHANGED <<clock, selected>>
Scan == /\ selected' = (IF history = <<>> THEN {} ELSE {1})
        /\ UNCHANGED <<clock, records, history>>
Next == Tick \/ Put \/ Drop \/ Scan
Inv == /\ clock \in Nat /\ selected \subseteq {1}
       /\ records \in [{1} -> [created: Nat, payload: {"x"}] \cup {Empty}]
       /\ history \in Seq({"put", "drop"})
Past == \A k \in {1}: records[k] = Empty \/ records[k].created <= clock
Ordered == \A i \in 1..Len(history): history[i] = "drop" =>
             \E j \in 1..i: history[j] = "put"
====
