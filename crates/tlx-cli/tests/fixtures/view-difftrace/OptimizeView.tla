---- MODULE OptimizeView ----
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ y' = x
Inv == x < 3
====
