---- MODULE LevelLasso ----
EXTENDS Naturals, TLC
VARIABLES x, y
alias == [x |-> x, y |-> y, sum |-> x + TLCGet("level")]
Init == x = 0 /\ y = 0
Next == \/ (x = 0 /\ y = 0 /\ x' = 1 /\ y' = 0)
        \/ (x = 0 /\ y = 0 /\ x' = 5 /\ y' = 1)
        \/ (x = 1 /\ y = 0 /\ x' = 2 /\ y' = 0)
        \/ (x = 2 /\ y = 0 /\ x' = 5 /\ y' = 1)
        \/ (x = 5 /\ y = 1 /\ x' = 2 /\ y' = 1)
        \/ (x = 2 /\ y = 1 /\ x' = 1 /\ y' = 0)
Spec == Init /\ [][Next]_<<x, y>>
Prop == <>[](x = 1)
====
