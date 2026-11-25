---- MODULE ActionChecks ----
EXTENDS Naturals
CONSTANT Actors, Rounds, Values
VARIABLE r, count
Init == r = [a \in Actors |-> [mode |-> "idle", buf |-> 0]] /\ count = 0
Start == \E a \in Actors :
           /\ r[a].mode = "idle"
           /\ count < Rounds
           /\ \E v \in Values : r' = [r EXCEPT ![a].mode = "busy", ![a].buf = v]
           /\ count' = count + 1
Finish == \E a \in Actors :
            /\ r[a].mode = "busy"
            /\ r[a].buf >= 0
            /\ r' = [r EXCEPT ![a].mode = "idle"]
            /\ count' = count
Next == Start \/ Finish
Inv == \A a \in Actors : r[a].mode \in {"idle", "busy"} /\ count <= Rounds
StateLimit == count <= Rounds
ActLimit == \A a \in Actors : r[a].mode \in {"idle", "busy"}
ActProp == [][ \A a \in Actors : r'[a].mode \in {"idle", "busy"} ]_<<count>>
====
