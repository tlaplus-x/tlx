---- MODULE HiddenAnchor ----
EXTENDS Naturals, FiniteSets
VARIABLE clock, bad
Init == clock = 1 /\ bad = FALSE
Next == /\ clock' = clock + 1
        /\ bad' = IF Cardinality({clock, 1}) = 2 THEN TRUE ELSE bad
Inv == ~bad /\ clock \in Nat
====
