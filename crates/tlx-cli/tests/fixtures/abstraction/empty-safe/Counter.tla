---- MODULE Counter ----
EXTENDS Naturals
VARIABLE c
Init == c = 5
Next == c < 0 /\ c' = c + 1
Inv == c = 5
====
