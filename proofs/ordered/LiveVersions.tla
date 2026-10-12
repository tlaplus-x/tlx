------------------------- MODULE LiveVersions -------------------------
EXTENDS Integers, TLC
CONSTANT Actors
VARIABLES frontier, held, versions, flag, observed
Init == /\ frontier = 1
        /\ held = [a \in Actors |-> 1]
        /\ versions = [k \in {1} |-> FALSE]
        /\ flag = FALSE /\ observed = FALSE
Publish == /\ frontier' = frontier + 1
           /\ versions' = versions @@ [k \in {frontier + 1} |-> ~versions[frontier]]
           /\ flag' = ~flag
           /\ UNCHANGED <<held, observed>>
Acquire(a) == /\ held' = [held EXCEPT ![a] = frontier]
              /\ observed' = versions[held[a]]
              /\ UNCHANGED <<frontier, versions, flag>>
Share(a,b) == /\ versions[held[a]] = versions[held[b]]
             /\ held' = [held EXCEPT ![a] = held[b]]
             /\ UNCHANGED <<frontier, versions, flag, observed>>
Next == Publish \/ (\E a \in Actors : Acquire(a) \/ (\E b \in Actors : Share(a,b)))
Inv == /\ versions[frontier] = flag
       /\ observed \in BOOLEAN
       /\ \A a \in Actors : held[a] <= frontier /\ versions[held[a]] \in BOOLEAN
=============================================================================
