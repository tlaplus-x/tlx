---------------------------- MODULE MCDieHardestScale ---------------------------
(***************************************************************************)
(* A model-checking wrapper for the upstream `DieHardest.tla` in           *)
(* `third_party/Examples/specifications/DieHard` (fetch it with            *)
(* `scripts/fetch-deps.sh`). It only fixes the two jug configurations,     *)
(* like the upstream `MCDieHardest.tla`, at larger capacities so the state *)
(* search dominates the fixed run cost and the threshold-counter           *)
(* projection's effect on wall-clock time is measurable.                   *)
(***************************************************************************)
EXTENDS DieHardest

MCGoal == 4

MCCapacity1 == "j1" :> 19 @@ "j2" :> 13

MCCapacity2 == "j1" :> 19 @@ "j2" :> 13 @@ "j3" :> 11

MCCapacities == <<MCCapacity1, MCCapacity2>>

=============================================================================
