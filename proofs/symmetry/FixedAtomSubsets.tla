----------------------------- MODULE FixedAtomSubsets -----------------------------
\* Quorum sets that mix one symmetric acceptor group with a fixed fake acceptor:
\* `ByzQuorum` and `WeakQuorum` are exact unions of k-subsets of `Acceptor` per
\* fixed-atom stratum (`{fa1}` and the empty stratum), so the equivariant
\* lowering stratifies them into `{Q \cup F : Q \in SUBSET Acceptor, |Q| \in K}`
\* unions instead of enumerating them. `NoVal` is a zero-arity definition the
\* configuration binds to a model value.
EXTENDS Naturals, FiniteSets
CONSTANTS Value, Acceptor, FakeAcceptor, ByzQuorum, WeakQuorum
VARIABLES votes, choice, decided

NoVal == CHOOSE v : v \notin Value

Init == /\ votes = [a \in Acceptor \cup FakeAcceptor |-> 0]
        /\ choice = [a \in Acceptor \cup FakeAcceptor |-> NoVal]
        /\ decided = FALSE

Vote(a, v) == /\ a \in Acceptor
              /\ votes[a] < 1
              /\ votes' = [votes EXCEPT ![a] = 1]
              /\ choice' = [choice EXCEPT ![a] = v]
              /\ UNCHANGED decided

Next == \E a \in Acceptor : \E v \in Value : Vote(a, v)

Inv == /\ \A Q \in ByzQuorum : \A a \in Q : votes[a] <= 1
       /\ \A Q \in WeakQuorum : \A a \in Q : choice[a] \in Value \cup {NoVal}
       /\ \A a \in Acceptor : votes[a] \in 0 .. 1
===================================================================================
