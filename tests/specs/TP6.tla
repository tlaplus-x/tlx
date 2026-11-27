---- MODULE TP6 ----
\* Reduced MisraReachability Refines shape: Refines == R!RSpec for an
\* INSTANCE R of the abstract module. The probe maps the abstract next
\* state to Target = {2} while the concrete step produces {1}, so the
\* refinement's [][R!RNext]_R!vars conjunct is false.
EXTENDS Naturals
VARIABLES x, marked
vars == <<x, marked>>
Init == x = 0 /\ marked = {}
Step == x = 0 /\ x' = 1 /\ marked' = {1}
Next == Step
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
R == INSTANCE TPRefAbs WITH Target <- {1}, marked <- marked
Refines == R!RSpec
RActionBad == INSTANCE TPRefAbs WITH Target <- {2}, marked <- marked
RefinesProbe == RActionBad!RSpec
====
