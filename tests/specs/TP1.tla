---- MODULE TP1 ----
\* Reduced MultiCarElevator liveness shape (ElevatorLivenessMedium/Large):
\* TemporalInvariant is a conjunction of leads-to obligations over the
\* people, under weak and strong fairness. The probe mutates one conjunct's
\* consequent to a floor the model never reaches; the other conjunct holds.
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
Fairness == /\ \A p \in Person : WF_vars(Call(p))
            /\ \A p \in Person : SF_vars(Serve(p))
Spec == Init /\ [][Next]_vars /\ Fairness
TemporalInvariant ==
    /\ \A p \in Person : waiting[p] ~> at[p] = 2
    /\ \E p \in Person : at[p] = 2 ~> ~waiting[p]
TemporalInvariantProbe ==
    /\ \A p \in Person : waiting[p] ~> at[p] = 3
    /\ \E p \in Person : at[p] = 2 ~> ~waiting[p]
====
