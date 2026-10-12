---- MODULE BoundedLedger ----
EXTENDS LedgerChaining
VARIABLE step
BoundedInit == Init /\ step = 0
BoundedNext == step < 30 /\ Next /\ step' = step + 1
====
