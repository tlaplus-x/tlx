---- MODULE Length ----
EXTENDS Naturals, Sequences
VARIABLE log, audit, seen
Init == /\ log = <<>> /\ audit = <<0>> /\ seen = 0
Grow == /\ Len(log) < 5
        /\ \E tx \in {0, 1}:
              /\ log' = Append(log, tx)
              /\ audit' = IF Len(log) < 2 THEN Append(audit, Len(log)) ELSE <<>>
              /\ seen' = Len(log)
Reset == /\ Len(log) = 5 /\ log' = <<>> /\ UNCHANGED <<audit, seen>>
Next == Grow \/ Reset
TypeOK == /\ log \in Seq({0, 1}) /\ audit \in Seq(Nat) /\ seen \in Nat
Safe == Len(log) < 4
====
