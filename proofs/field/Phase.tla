---- MODULE Phase ----
EXTENDS Integers
VARIABLE r
Init == r = [mode |-> "idle", data |-> 0]
Start == \E n \in {0, 1}: /\ r.mode = "idle"
                              /\ r' = [r EXCEPT !.mode = "busy", !.data = n]
Finish == /\ r.mode = "busy"
          /\ r.data >= 0
          /\ r' = [r EXCEPT !.mode = "idle"]
Next == Start \/ Finish
Inv == r \in [mode: {"idle", "busy"}, data: {0, 1}]
====
