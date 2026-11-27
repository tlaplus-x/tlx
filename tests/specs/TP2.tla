---- MODULE TP2 ----
\* Reduced MultiCarElevator liveness shape: explicit []<> obligations over
\* the people, under the model's weak and strong fairness. The probe keeps
\* the property and weakens the fairness by dropping the strong fairness of
\* Serve, so a run may leave a person waiting forever.
EXTENDS Naturals
CONSTANTS Person
VARIABLES at, waiting
vars == <<at, waiting>>
Init == at = [p \in Person |-> 1] /\ waiting = [p \in Person |-> TRUE]
Call(p) == /\ waiting[p] /\ at[p] < 2
           /\ at' = [at EXCEPT ![p] = at[p] + 1]
           /\ UNCHANGED waiting
Serve(p) == /\ at[p] = 2 /\ waiting[p]
            /\ waiting' = [waiting EXCEPT ![p] = FALSE]
            /\ UNCHANGED at
Next == \/ \E p \in Person : Call(p)
        \/ \E p \in Person : Serve(p)
TemporalInvariant == \A p \in Person : []<>(~waiting[p])
Fair == \A p \in Person : WF_vars(Call(p)) /\ SF_vars(Serve(p))
Spec == Init /\ [][Next]_vars /\ Fair
ProbeSpec == Init /\ [][Next]_vars /\ \A p \in Person : WF_vars(Call(p))
====
