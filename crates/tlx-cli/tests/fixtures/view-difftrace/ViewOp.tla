---- MODULE ViewOp ----
EXTENDS Naturals
VARIABLES x, y
F(a) == <<a, y>>
view == F(x)
Init == x = 0 /\ y = 5
Next == x' = x + 1 /\ y' = y
Inv == x < 2
====
