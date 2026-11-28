---- MODULE DiffMulti ----
EXTENDS Naturals
VARIABLES x, y
Init == x = 0 /\ y = 0
Next == x' = x + 1 /\ y' = IF x = 1 THEN y + 1 ELSE y
Inv == x < 3
====
