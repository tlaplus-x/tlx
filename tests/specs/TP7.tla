---- MODULE TP7 ----
\* Reduced MisraReachability Refines shape: Refines == R!RSpec for an
\* INSTANCE R of the abstract module. The probe keeps the refinement and
\* checks it against the concrete specification without its fairness, so a
\* behavior may stutter in the initial state where R!RNext is enabled and
\* the refinement's WF_R!vars(R!RNext) conjunct is false.
EXTENDS Naturals
VARIABLES x, marked
vars == <<x, marked>>
Init == x = 0 /\ marked = {}
Step == x = 0 /\ x' = 1 /\ marked' = {1}
Next == Step
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
SpecNoFair == Init /\ [][Next]_vars
R == INSTANCE TPRefAbs WITH Target <- {1}, marked <- marked
Refines == R!RSpec
====
