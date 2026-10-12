---- MODULE Feedback ----
EXTENDS Naturals, Sequences
VARIABLE h, witnessed
Seen == \E i \in 1..Len(h):
          h[i] = "R" /\ \A j \in 1..i: h[j] # "W"
Init == /\ h = <<>> /\ witnessed = FALSE
Next == \E event \in {"R", "W"}:
          /\ h' = Append(h, event) /\ witnessed' = Seen
TypeOK == /\ h \in Seq({"R", "W"}) /\ witnessed \in BOOLEAN
Safe == ~(witnessed /\ \E i \in 1..Len(h): h[i] = "W")
====
