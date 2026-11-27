---- MODULE TP5 ----
\* Reduced MisraReachability Refines shape: Refines == R!RSpec for an
\* INSTANCE R of the abstract module. The probe maps the abstract initial
\* variable to a value that does not satisfy R!RInit, so the refinement's
\* initial conjunct is false while its action and fairness conjuncts hold.
EXTENDS Naturals
VARIABLES x, marked
vars == <<x, marked>>
Init == x = 0 /\ marked = {}
Step == x = 0 /\ x' = 1 /\ marked' = {1}
Next == Step
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
R == INSTANCE TPRefAbs WITH Target <- {1}, marked <- marked
Refines == R!RSpec
\* The mutation: R!RInit is checked on this expression, which is {1} in the
\* initial state instead of {}.
markedBad == IF x = 0 THEN {1} ELSE marked
RBad == INSTANCE TPRefAbs WITH Target <- {1}, marked <- markedBad
RefinesProbe == RBad!RSpec
====
