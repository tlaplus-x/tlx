---- MODULE InstOpSubLevel ----
\* Level bound on a CONSTANT operator substitution in a non-constant module
\* must be enforced at the parameterized INSTANCE call site (SANY rejects).
EXTENDS Naturals

---- MODULE M ----
CONSTANT c(_)
VARIABLE v
Test == c(0) = v
====

VARIABLE x
Ix(G(_)) == INSTANCE M WITH c <- G, v <- x
Init == x = 0
Next == UNCHANGED x
Read(a) == x + a
Inv == Ix(Read)!Test
====
