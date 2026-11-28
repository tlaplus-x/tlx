---- MODULE ViewRev ----
EXTENDS Naturals
VARIABLES x, y
view == <<y, x>>
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ y' = y + 10
Inv == x < 2
====
