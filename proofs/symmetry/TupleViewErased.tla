------------------------- MODULE TupleViewErased -------------------------
EXTENDS Naturals, TLC
CONSTANT Proc
VARIABLES pc, phase, ghost
serverVars == <<pc>>
logVars == <<phase>>
Init == pc = [p \in Proc |-> 0] /\ phase = FALSE /\ ghost = FALSE
Next == \E p \in Proc : pc[p] < 2 /\ pc' = [pc EXCEPT ![p] = @ + 1] /\ phase' = ~phase /\ ghost' = phase
Inv == \A p \in Proc : pc[p] <= 2
\* `ghost` is omitted and certified erasable; the retained tuple is built from
\* zero-arity variable-group definitions and is not in declaration order.
View == <<logVars, serverVars>>
=============================================================================
