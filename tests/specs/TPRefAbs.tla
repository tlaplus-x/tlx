---- MODULE TPRefAbs ----
\* The abstract specification a concrete model refines in the reduced
\* MisraReachability Refines probes (TP5-TP7): one step moves the mark to
\* Target, then the abstract next-state relation keeps it there under weak
\* fairness.
EXTENDS Naturals
CONSTANT Target
VARIABLE marked
vars == <<marked>>
RInit == marked = {}
RNext == marked' = Target
RSpec == RInit /\ [][RNext]_vars /\ WF_vars(RNext)
====
