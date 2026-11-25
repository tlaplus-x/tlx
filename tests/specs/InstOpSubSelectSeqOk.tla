---- MODULE InstOpSubSelectSeqOk ----
\* Positive control: when the substituted declaration is a VARIABLE (allowing
\* state-level inputs), passing S!Keep to SelectSeq on a state-level sequence
\* succeeds and matches TLC.
EXTENDS Naturals, Sequences

---- MODULE Bounds ----
VARIABLE candidate, limit
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
