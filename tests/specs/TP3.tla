---- MODULE TP3 ----
\* Reduced MongoDB RaftMongo liveness shape: CommitPointEventuallyPropagates
\* wraps the ordered-pair leads-to obligations in [] under the model's strong
\* fairness. Two servers keep the reduced probe at four ordered pairs and
\* TLC's trace check bounded; the corpus configuration's three servers give
\* the nine branches. The probe mutates the inner <> consequent to a commit
\* point the monotone model never reaches.
EXTENDS Naturals
CONSTANTS Server
VARIABLES log, cp
vars == <<log, cp>>
Init == log = [s \in Server |-> 0] /\ cp = [s \in Server |-> 0]
Grow(s) == log[s] < 2 /\ log' = [log EXCEPT ![s] = log[s] + 1] /\ UNCHANGED cp
Learn(s) == cp' = [cp EXCEPT ![s] = log[s]] /\ UNCHANGED log
Next == \/ \E s \in Server : Grow(s)
        \/ \E s \in Server : Learn(s)
Fair == \A s \in Server : SF_vars(Grow(s)) /\ SF_vars(Learn(s))
Spec == Init /\ [][Next]_vars /\ Fair
CommitPointEventuallyPropagates ==
    \A i, j \in Server : [](cp[i] # cp[j] ~> <>(cp[i] = cp[j]))
CommitPointEventuallyPropagatesProbe ==
    \A i, j \in Server : [](cp[i] # cp[j] ~> <>(cp[i] = 3))
====
