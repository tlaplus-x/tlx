---- MODULE ChooseSym ----
EXTENDS Naturals, FiniteSets

CONSTANT Proc
VARIABLES votes, leaders, msgs

TotalVotes ==
    LET sum[S \in SUBSET Proc] ==
        IF S = {} THEN 0
        ELSE LET p == CHOOSE x \in S : TRUE
             IN votes[p] + sum[S \ {p}]
    IN sum[Proc]

Init ==
    /\ votes = [p \in Proc |-> 0]
    /\ leaders = {}
    /\ msgs = {[from |-> p, tag |-> 0, val |-> 7] : p \in Proc}

Elect(p) ==
    /\ \A q \in Proc : q \notin leaders
    /\ votes[p] < 2
    /\ leaders' = leaders \cup {p}
    /\ UNCHANGED <<votes, msgs>>

StepLeader ==
    /\ \E q \in Proc : q \in leaders
    /\ LET l == CHOOSE p \in Proc : p \in leaders
       IN /\ votes' = [votes EXCEPT ![l] = @ + 1]
          /\ leaders' = leaders \ {l}
          /\ msgs' = msgs \cup {[from |-> l, tag |-> votes[l] + 1, val |-> 7]}

Next ==
    \/ (\E p \in Proc : Elect(p))
    \/ StepLeader

Inv ==
    /\ \A p \in Proc : votes[p] \in 0..2
    /\ Cardinality(leaders) <= 1
    /\ (CHOOSE m \in msgs : TRUE).val = 7
    /\ (LET m == CHOOSE m \in msgs : m.tag >= 0 IN m.val) = 7
    /\ TotalVotes <= 6
====
