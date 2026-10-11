---- MODULE Counter ----
EXTENDS Naturals
VARIABLE c
Init == c = 0
Next == c < 3 /\ c' = c + 1
Inv == c < 2
====
