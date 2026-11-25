---- MODULE InstOpSubForward ----
\* Forwarding an operator argument through a LET helper must preserve its
\* constant-level operand bound (matching SANY).
EXTENDS Naturals

---- MODULE Bounds ----
CONSTANT candidate
VARIABLE limit
Keep == candidate <= limit
====

---- MODULE Batch ----
CONSTANT Filter(_)
Pick(s) == LET Apply(a) == Filter(a) IN Apply(s)
====

VARIABLE x
S(i) == INSTANCE Bounds WITH candidate <- i, limit <- x
B(P(_)) == INSTANCE Batch WITH Filter <- P
Init == x = 0
Next == x' = (x + 1) % 128
Inv == B(S!Keep)!Pick(x)
====
