---- MODULE ViewTupleOne ----
EXTENDS Naturals
VARIABLES x, y
view == <<x>>
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ y' = y + 1
Inv == x < 2
====
