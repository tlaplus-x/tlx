--------------------------- MODULE MultiKeyMsgs ---------------------------
EXTENDS Naturals, Sequences, FiniteSets
CONSTANTS Node
VARIABLES msgs, log
Init == /\ msgs = {}
        /\ log = <<>>
Send(p, q) ==
  /\ p # q
  /\ Cardinality(msgs) < 3
  /\ [src |-> p, dst |-> q, kind |-> "req"] \notin msgs
  /\ msgs' = msgs \cup {[src |-> p, dst |-> q, kind |-> "req"]}
  /\ log' = IF Len(log) < 2 THEN Append(log, [src |-> p, dst |-> q]) ELSE log
Ack(m) ==
  /\ m \in msgs
  /\ m.kind = "req"
  /\ Cardinality(msgs) < 3
  /\ [src |-> m.dst, dst |-> m.src, kind |-> "ack"] \notin msgs
  /\ msgs' = msgs \cup {[src |-> m.dst, dst |-> m.src, kind |-> "ack"]}
  /\ UNCHANGED log
DropHead ==
  /\ Len(log) > 0
  /\ Head(log).src # Head(log).dst
  /\ log' = Tail(log)
  /\ UNCHANGED msgs
Next == (\E p, q \in Node : Send(p, q)) \/ (\E m \in msgs : Ack(m)) \/ DropHead
TypeOK ==
  /\ msgs \subseteq [src : Node, dst : Node, kind : {"req", "ack"}]
  /\ log \in Seq([src : Node, dst : Node])
Inv ==
  /\ TypeOK
  /\ Cardinality(msgs) <= 3
  /\ Len(log) <= 2
=============================================================================
