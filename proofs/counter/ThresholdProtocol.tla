------------------------ MODULE ThresholdProtocol ------------------------
EXTENDS Naturals

CONSTANTS Actor

VARIABLES phase, step, retries, failures

vars == <<phase, step, retries, failures>>

Init ==
  /\ phase = "idle"
  /\ step = 0
  /\ retries = 0
  /\ failures = [a \in Actor |-> 0]

TryWork ==
  /\ phase = "idle"
  /\ phase' = "busy"
  /\ UNCHANGED <<step, retries, failures>>

Retry ==
  /\ phase = "busy"
  /\ step < 30
  /\ step' = step + 1
  /\ retries' = retries + 1
  /\ phase' = IF retries >= 2 THEN "escalated" ELSE "busy"
  /\ UNCHANGED failures

EscalatedTick ==
  /\ phase = "escalated"
  /\ step < 30
  /\ step' = step + 1
  /\ retries' = retries + 1
  /\ UNCHANGED <<phase, failures>>

FailActor ==
  \E a \in Actor :
    /\ phase \in {"busy", "escalated"}
    /\ step < 30
    /\ step' = step + 1
    /\ failures' = [failures EXCEPT ![a] = @ + 1]
    /\ phase' = IF failures[a] >= 2 THEN "degraded" ELSE phase
    /\ UNCHANGED retries

DegradedTick ==
  \E a \in Actor :
    /\ phase = "degraded"
    /\ step < 30
    /\ step' = step + 1
    /\ failures' = [failures EXCEPT ![a] = @ + 1]
    /\ UNCHANGED <<phase, retries>>

Recover ==
  /\ phase' = "idle"
  /\ retries' = 0
  /\ failures' = [a \in Actor |-> 0]
  /\ UNCHANGED step

Next ==
  \/ TryWork
  \/ Retry
  \/ EscalatedTick
  \/ FailActor
  \/ DegradedTick
  \/ Recover

TypeOK ==
  /\ phase \in {"idle", "busy", "escalated", "degraded"}
  /\ step \in Nat
  /\ retries \in Nat
  /\ failures \in [Actor -> Nat]

EscalatedImpliesRetries ==
  (phase = "escalated") => (retries >= 3)

DegradedImpliesFailure ==
  (phase = "degraded") => (\E a \in Actor : failures[a] >= 3)

=============================================================================
