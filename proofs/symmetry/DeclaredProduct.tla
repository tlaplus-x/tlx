---- MODULE DeclaredProduct ----
\* A declared SYMMETRY over one constant leaves two independent symmetric
\* sets of model values unreduced. In the default mode tlx certifies the
\* product TxIdSymmetric x Permutations(Key) x Permutations(Val) with one
\* connected Lean certificate; -tlc and -noautosymmetry keep the declared
\* group alone.
EXTENDS TLC, Naturals, FiniteSets
CONSTANTS TxId, Key, Val
VARIABLES tx, key, val

Init == tx = [t \in TxId |-> 0]
     /\ key = [k \in Key |-> 0]
     /\ val = [v \in Val |-> 0]

Next == \/ \E t \in TxId : tx[t] < 1 /\ tx' = [tx EXCEPT ![t] = 1]
                                     /\ UNCHANGED <<key, val>>
        \/ \E k \in Key : key[k] < 1 /\ key' = [key EXCEPT ![k] = 1]
                                     /\ UNCHANGED <<tx, val>>
        \/ \E v \in Val : val[v] < 1 /\ val' = [val EXCEPT ![v] = 1]
                                     /\ UNCHANGED <<tx, key>>

Inv == \A t \in TxId : tx[t] <= 1
    /\ \A k \in Key : key[k] <= 1
    /\ \A v \in Val : val[v] <= 1

TxIdSymmetric == Permutations(TxId)
====
