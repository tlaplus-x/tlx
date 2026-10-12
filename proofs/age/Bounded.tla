---- MODULE Bounded ----
EXTENDS Age
VARIABLE budget
BoundedInit == Init /\ budget = 0
BoundedNext == budget < 120 /\ budget' = budget + 1 /\ Next
====
