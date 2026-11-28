---- MODULE LassoTwo ----
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y = 7
Next == x < 3 /\ x' = x + 1 /\ y' = y
Spec == Init /\ [][Next]_<<x, y>>
Reach == <>(x = 3)
====
