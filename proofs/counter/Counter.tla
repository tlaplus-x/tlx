---- MODULE Counter ----
EXTENDS Naturals
VARIABLES fixed, x, y
Init == fixed = 7 /\ x = 0 /\ y = 0
GrowX == x' = x + 1 /\ UNCHANGED <<fixed, y>>
GrowY == x >= 3 /\ y' = y + 1 /\ UNCHANGED <<fixed, x>>
ResetX == x' = 0 /\ UNCHANGED <<fixed, y>>
ResetY == y >= 5 /\ y' = 0 /\ UNCHANGED <<fixed, x>>
Dead == fixed = 8 /\ x' = x + 1 /\ UNCHANGED <<fixed, y>>
Next == GrowX \/ GrowY \/ ResetX \/ ResetY \/ Dead
Inv == fixed = 7 /\ x >= 0 /\ y >= 0
====
