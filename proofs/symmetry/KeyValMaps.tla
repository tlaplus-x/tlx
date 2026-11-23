---------------------------- MODULE KeyValMaps ----------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS Proc
VARIABLES parent, followers, grants
Init ==
  /\ parent = [p \in Proc |-> p]
  /\ followers = [p \in Proc |-> {}]
  /\ grants = [p \in Proc |-> [q \in Proc |-> FALSE]]
Follow(p, q) ==
  /\ p # q
  /\ parent[p] = p
  /\ parent' = [parent EXCEPT ![p] = q]
  /\ followers' = [followers EXCEPT ![q] = @ \cup {p}]
  /\ grants' = [grants EXCEPT ![p][q] = TRUE]
Reset(p) ==
  /\ parent[p] # p
  /\ LET old == parent[p] IN
     /\ parent' = [parent EXCEPT ![p] = p]
     /\ followers' = [followers EXCEPT ![old] = @ \ {p}]
     /\ grants' = [grants EXCEPT ![p] = [q \in Proc |-> FALSE]]
Next == \E p \in Proc : Reset(p) \/ (\E q \in Proc : Follow(p, q))
TypeOK ==
  /\ parent \in [Proc -> Proc]
  /\ followers \in [Proc -> SUBSET Proc]
  /\ grants \in [Proc -> [Proc -> BOOLEAN]]
Inv ==
  /\ TypeOK
  /\ DOMAIN parent = Proc
  /\ \A p \in Proc : p \notin followers[p]
  /\ \A p, q \in Proc : (p \in followers[q]) <=> (parent[p] = q /\ p # q)
  /\ \A p, q \in Proc : grants[p][q] => (p \in followers[q])
  /\ Cardinality({p \in Proc : parent[p] # p}) <= Cardinality(Proc)
===========================================================================
