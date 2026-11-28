---- MODULE ViewTuple ----
EXTENDS Naturals
VARIABLES x, y, z
view == <<x, y>>
Init == x = 0 /\ y = 0 /\ z = 9
Next == x' = x + 1 /\ y' = y + 1 /\ z' = z
Inv == x < 3
====
