---- MODULE Optimized ----
\* Generated mathematical abstraction; this file is not a safety verdict.
EXTENDS Naturals
VARIABLES v0
Init ==
    /\ v0 = 0
Action0 ==
    /\ (v0 < 3)
    /\ v0' = (IF v0 < 3 THEN v0 + 1 ELSE 3)
Next == Action0
Invariant0 == (v0 < 2)
====
