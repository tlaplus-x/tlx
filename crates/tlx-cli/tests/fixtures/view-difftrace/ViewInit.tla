---- MODULE ViewInit ----
EXTENDS Naturals
VARIABLES x, y
view == <<y, x>>
Init == x = 0 /\ y = 5
Next == UNCHANGED <<x, y>>
Inv == x = 1
====
