---- MODULE DiffAlias ----
EXTENDS Naturals
VARIABLES x, y
alias == [ax |-> x, k |-> 5]
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ y' = y + 1
Inv == x < 2
====
