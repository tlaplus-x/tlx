-------------------------- MODULE ProductSets ---------------------------
EXTENDS Naturals, FiniteSets
CONSTANTS Client, Server
VARIABLES cState, sState, acked, msgs

Msg == [type : {"req"}, c : Client]
  \cup [type : {"ack"}, s : Server]
  \cup [type : {"done"}]

Init == /\ cState = [c \in Client |-> "idle"]
        /\ sState = [s \in Server |-> "ready"]
        /\ acked = {}
        /\ msgs = {}

SendReq(c) ==
  /\ cState[c] = "idle"
  /\ cState' = [cState EXCEPT ![c] = "sent"]
  /\ msgs' = msgs \cup {[type |-> "req", c |-> c]}
  /\ UNCHANGED <<sState, acked>>

Serve(s) ==
  /\ sState[s] = "ready"
  /\ \E c \in Client : [type |-> "req", c |-> c] \in msgs
  /\ sState' = [sState EXCEPT ![s] = "served"]
  /\ msgs' = msgs \cup {[type |-> "ack", s |-> s]}
  /\ UNCHANGED <<cState, acked>>

Collect(c, s) ==
  /\ [type |-> "req", c |-> c] \in msgs
  /\ [type |-> "ack", s |-> s] \in msgs
  /\ acked' = acked \cup {c, s}
  /\ UNCHANGED <<cState, sState, msgs>>

Finish ==
  /\ acked = Client \cup Server
  /\ msgs' = msgs \cup {[type |-> "done"]}
  /\ UNCHANGED <<cState, sState, acked>>

Next == \/ \E c \in Client : SendReq(c)
        \/ \E s \in Server : Serve(s)
        \/ \E c \in Client, s \in Server : Collect(c, s)
        \/ Finish

Inv == /\ cState \in [Client -> {"idle", "sent"}]
       /\ sState \in [Server -> {"ready", "served"}]
       /\ acked \subseteq Client \cup Server
       /\ msgs \subseteq Msg
       /\ Cardinality(acked) <= 4
=========================================================================
