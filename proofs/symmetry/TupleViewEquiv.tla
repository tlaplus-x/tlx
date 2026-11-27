------------------------ MODULE TupleViewEquiv --------------------------
EXTENDS Naturals, FiniteSets, TLC
CONSTANT Proc
VARIABLES msgs, phase, ghost
serverVars == <<msgs>>
logVars == <<phase>>
Init == msgs = {} /\ phase = FALSE /\ ghost = FALSE
Next == \E p, q \in Proc : p # q /\ Cardinality(msgs) < 1
        /\ msgs' = msgs \cup {[src |-> p, dst |-> q]}
        /\ phase' = ~phase /\ ghost' = phase
Inv == Cardinality(msgs) <= 1
\* A set of two-key records is outside the keyed rule IR, so the retained
\* `VIEW` composition uses ErasedEquivCertificate. The groups are zero-arity
\* variable-group definitions.
View == <<logVars, serverVars>>
=============================================================================
