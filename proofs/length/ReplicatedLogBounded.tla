---- MODULE ReplicatedLogBounded ----
EXTENDS ReplicatedLog
BoundedNext == Len(log) < 22 /\ Next
====
