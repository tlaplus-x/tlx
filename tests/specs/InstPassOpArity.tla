---- MODULE InstPassOpArity ----
\* Passing an inherited operator S!Twice from a parameterized INSTANCE S(p) to a
\* unary consumer must be rejected (S!Twice has public arity 2, not 1).
EXTENDS Naturals

---- MODULE Source ----
EXTENDS InstPassOpCommon
CONSTANT k
Read == k
====

---- MODULE One ----
CONSTANT F(_)
Value == F(3)
====

VARIABLE x
S(p) == INSTANCE Source WITH k <- p
C(G(_)) == INSTANCE One WITH F <- G
Init == x = 0
Next == UNCHANGED x
Inv == C(S!Twice)!Value = 6
====
