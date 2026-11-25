---- MODULE InstOpSubSelectSeq ----
\* Passing a qualified operator with a constant-level parameter bound to
\* SelectSeq with a state-level sequence must be rejected (matching SANY).
EXTENDS Naturals, Sequences

---- MODULE Bounds ----
CONSTANT candidate
VARIABLE limit
Keep == candidate <= limit
====

---- MODULE Batch ----
CONSTANT Filter(_)
Pick(s) == SelectSeq(s, Filter)
====

VARIABLE x
S(i) == INSTANCE Bounds WITH candidate <- i, limit <- x
B(P(_)) == INSTANCE Batch WITH Filter <- P
Init == x = 0
Next == x' = (x + 1) % 128
Inv == B(S!Keep)!Pick(<<x, x + 1>>) = <<x>>
====
