----------------------- MODULE MC_tlx_FastLeaderElection -----------------------
\* tlx corpus (ours): bounded model-checking configurations of the upstream
\* Apache ZooKeeper `FastLeaderElection` specification.
\*
\* The upstream module is unbounded: `LeaderAdvanceEpoch`, `LeaderAdvanceZxid`
\* and `ZabTimeout` keep raising `currentEpoch`, the log index and
\* `logicalClock`; `history`, the notification channels (`electionMsgs`), the
\* receive queues, and the otherwise write-only `version` counters of the
\* received-vote records grow without a finite limit. The bound constants below
\* keep the search finite; the cfg files choose their values.
\*
\* The upstream `NullPoint == CHOOSE p: p \notin Server` is an unbounded CHOOSE,
\* which the pinned TLC cannot evaluate. The cfgs bind `NullPoint` to
\* `MCNullPoint` with a constant definition (`CONSTANT NullPoint <- MCNullPoint`)
\* instead, and no server id of these configurations is negative.
EXTENDS FastLeaderElection

CONSTANTS MaxEpoch, MaxIndex, MaxClock, MaxHistory, MaxQueue, MaxVersion

MCNullPoint == -1

Bound == /\ \A i \in Server : currentEpoch[i] <= MaxEpoch
         /\ \A i \in Server : lastProcessed[i].index <= MaxIndex
         /\ \A i \in Server : logicalClock[i] <= MaxClock
         /\ \A i \in Server : Len(history[i]) <= MaxHistory
         /\ \A i \in Server : Len(recvQueue[i]) <= MaxQueue
         /\ \A i, j \in Server : Len(electionMsgs[i][j]) <= MaxQueue
         /\ \A i, j \in Server : receiveVotes[i][j].version <= MaxVersion
         /\ \A i, j \in Server : outOfElection[i][j].version <= MaxVersion
===============================================================================
