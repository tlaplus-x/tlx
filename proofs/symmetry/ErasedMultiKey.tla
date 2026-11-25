-------------------------- MODULE ErasedMultiKey --------------------------
EXTENDS Naturals, Sequences, FiniteSets
CONSTANTS Node
VARIABLES msgs, log, audit, lastAction, stats
Init == /\ msgs = {}
        /\ log = <<>>
        /\ audit = {}
        /\ lastAction = [kind |-> "init", actor |-> "none"]
        /\ stats = [n \in Node |-> FALSE]
Send(p, q) ==
  /\ p # q
  /\ Cardinality(msgs) < 2
  /\ [src |-> p, dst |-> q, kind |-> "req"] \notin msgs
  /\ msgs' = msgs \cup {[src |-> p, dst |-> q, kind |-> "req"]}
  /\ log' = IF Len(log) < 2 THEN Append(log, [src |-> p, dst |-> q]) ELSE log
  /\ audit' = audit \cup {[who |-> p, dst |-> q, kind |-> "req"]}
  /\ lastAction' = [kind |-> "send", actor |-> p]
  /\ stats' = [stats EXCEPT ![p] = TRUE]
Ack(m) ==
  /\ m \in msgs
  /\ m.kind = "req"
  /\ Cardinality(msgs) < 2
  /\ [src |-> m.dst, dst |-> m.src, kind |-> "ack"] \notin msgs
  /\ msgs' = msgs \cup {[src |-> m.dst, dst |-> m.src, kind |-> "ack"]}
  /\ UNCHANGED <<log, stats>>
  /\ audit' = audit \cup {[who |-> m.dst, dst |-> m.src, kind |-> "ack"]}
  /\ lastAction' = [kind |-> "ack", actor |-> m.dst]
DropHead ==
  /\ Len(log) > 0
  /\ Head(log).src # Head(log).dst
  /\ log' = Tail(log)
  /\ UNCHANGED <<msgs, audit, stats>>
  /\ lastAction' = [kind |-> "drop", actor |-> "none"]
Next == (\E p, q \in Node : Send(p, q)) \/ (\E m \in msgs : Ack(m)) \/ DropHead
TypeOK ==
  /\ msgs \subseteq [src : Node, dst : Node, kind : {"req", "ack"}]
  /\ log \in Seq([src : Node, dst : Node])
Inv ==
  /\ TypeOK
  /\ Cardinality(msgs) <= 2
  /\ Len(log) <= 2
=============================================================================
