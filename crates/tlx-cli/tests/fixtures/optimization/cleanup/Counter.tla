---- MODULE Counter ----
EXTENDS Naturals
VARIABLES fixed, c
Init == fixed = 7 /\ c = 0
Next == (fixed /= 7 /\ c > 2147483647 /\ c' = c + 1 /\ UNCHANGED fixed) \/ (c < 2 /\ c' = c + 1 /\ UNCHANGED fixed)
Inv == fixed = 7 /\ c <= 2
====
