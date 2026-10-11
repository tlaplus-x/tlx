---- MODULE Counter ----
EXTENDS Naturals
VARIABLE c
Init == c = 9
Next == c' = 0
Inv == c >= 0
====
