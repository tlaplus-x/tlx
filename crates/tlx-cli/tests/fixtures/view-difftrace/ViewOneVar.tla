---- MODULE ViewOneVar ----
EXTENDS Naturals
VARIABLE x
view == <<x>>
Init == x = 0
Next == x' = x + 1
Inv == x < 2
====
