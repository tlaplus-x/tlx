---- MODULE ViewFn ----
EXTENDS Naturals
VARIABLES x, y, z
f[a \in 0..2] == a + y
view == <<f[x], z>>
Init == x = 0 /\ y = 1 /\ z = 2
Next == x' = x + 1 /\ y' = y /\ z' = z
Inv == x < 2
====
