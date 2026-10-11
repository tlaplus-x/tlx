---- MODULE Abstract ----
\* Generated mathematical abstraction; this file is not a safety verdict.
EXTENDS Naturals
VARIABLES v0, v1
Init ==
    /\ v0 = 7
    /\ v1 = 0
Action0 ==
    /\ (v1 < 2)
    /\ v0' = (v0)
    /\ v1' = (IF v1 < 3 THEN v1 + 1 ELSE 3)
Next == Action0
Invariant0 == (v1 <= 2)
====
