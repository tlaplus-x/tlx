---- MODULE Optimized ----
\* Generated mathematical abstraction; this file is not a safety verdict.
EXTENDS Naturals
VARIABLES v0
Init ==
    /\ v0 = 5
Next == (v0 /= v0) /\ UNCHANGED <<v0>>
Invariant0 == TRUE
====
