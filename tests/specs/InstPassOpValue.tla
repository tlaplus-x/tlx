---- MODULE InstPassOpValue ----
\* Using an unapplied parameterized instance prefix S!Read in a value operand
\* position (arithmetic `+`) must be rejected, matching SANY.
EXTENDS Naturals

---- MODULE Source ----
CONSTANT k
Read == k
====

S(n) == INSTANCE Source WITH k <- n
VARIABLE x
Init == x = 0
Next == x' = S!Read + 1
====
