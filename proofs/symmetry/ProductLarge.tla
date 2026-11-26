----------------------------- MODULE ProductLarge -----------------------------
EXTENDS Naturals
CONSTANTS K, V, T
VARIABLES kmap, vmap, tmap
Init == /\ kmap = [k \in K |-> 0]
        /\ vmap = [v \in V |-> 0]
        /\ tmap = [t \in T |-> 0]
Next == \/ \E k \in K : kmap[k] < 1 /\ kmap' = [kmap EXCEPT ![k] = 1] /\ UNCHANGED <<vmap, tmap>>
        \/ \E v \in V : vmap[v] < 1 /\ vmap' = [vmap EXCEPT ![v] = 1] /\ UNCHANGED <<kmap, tmap>>
        \/ \E t \in T : tmap[t] < 1 /\ tmap' = [tmap EXCEPT ![t] = 1] /\ UNCHANGED <<kmap, vmap>>
Inv == /\ \A k \in K : kmap[k] <= 1
       /\ \A v \in V : vmap[v] <= 1
       /\ \A t \in T : tmap[t] <= 1
===============================================================================
