---------------------------- MODULE TupleView ----------------------------
EXTENDS Naturals, TLC
CONSTANT Proc
VARIABLES pc, phase
serverVars == <<pc>>
logVars == <<phase>>
Init == pc = [p \in Proc |-> 0] /\ phase = FALSE
Next == \/ \E p \in Proc : pc[p] < 2 /\ pc' = [pc EXCEPT ![p] = @ + 1] /\ UNCHANGED phase
        \/ phase' = ~phase /\ UNCHANGED pc
Inv == \A p \in Proc : pc[p] <= 2
\* A nested, reordered exact (full-retention) tuple VIEW built from zero-arity
\* variable-group definitions.
View == <<logVars, serverVars>>
=============================================================================
