---- MODULE ViewTraceSum ----
EXTENDS Naturals, Sequences, TLCExt
VARIABLES x, y
alias == [x |-> x, sum |-> x + Len(Trace)]
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ y' = y + 1
Inv == x < 2
====
