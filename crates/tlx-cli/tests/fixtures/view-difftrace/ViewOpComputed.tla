---- MODULE ViewOpComputed ----
EXTENDS Naturals
VARIABLES x, y, z
F(a) == a + y
view == <<F(x), z>>
Init == x = 0 /\ y = 1 /\ z = 2
Next == x' = x + 1 /\ y' = y /\ z' = z
Inv == x < 2
====
