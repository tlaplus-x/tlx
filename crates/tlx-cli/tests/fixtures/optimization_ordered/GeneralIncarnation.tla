---- MODULE GeneralIncarnation ----
EXTENDS TxnsCollectionIncarnation

LiveSnapshots == {snap \in {shardTxnResources[s][t].snapshot : s \in Shards, t \in Txns} : DOMAIN snap # {}}
SnapshotTimes == {clusterTime} \cup {snap.ts : snap \in LiveSnapshots}
Requests == UNION {UNION {log[t][i].reqEntries : i \in DOMAIN log[t]} : t \in Txns}
SuccessfulResponses == UNION {{rsp \in response[t][i] : rsp.status = OK} : t \in Txns, i \in Stmts}
Times == {1, clusterTime, databaseMetadata.dbVersion, rDatabaseCache.dbVersion}
    \cup {collectionMetadata[n].collectionGen : n \in NameSpaces}
    \cup {rCollectionCache[n].collectionGen : n \in NameSpaces}
    \cup {rPlacementConflictTime[t] : t \in Txns}
    \cup {shardTxnResources[s][t].placementConflictTime : s \in Shards, t \in Txns}
    \cup SnapshotTimes
    \cup UNION {{req.dbVersion, req.collectionGen, req.txnRuntimeContext.placementConflictTime} : req \in Requests}
CatalogTimes == Times \cap DOMAIN shardNamespaceUUID
UUIDs == {nextUUID}
    \cup {shardNamespaceUUID[ts][n][s] : ts \in CatalogTimes, n \in NameSpaces, s \in Shards}
    \cup {snap.uuid[n] : snap \in LiveSnapshots, n \in NameSpaces}
    \cup {rsp.snapshot.uuid : rsp \in SuccessfulResponses}
TimeValue(v) == IF v <= 0 THEN v ELSE Cardinality({w \in Times : w > 0 /\ w <= v})
UUIDValue(v) == IF v = 0 THEN 0 ELSE Cardinality({w \in UUIDs : w > 0 /\ w <= v})
ProjectSnapshot(snap) == IF DOMAIN snap = {} THEN snap ELSE
    [snap EXCEPT !.ts = TimeValue(snap.ts), !.uuid = [n \in NameSpaces |-> UUIDValue(snap.uuid[n])]]
ProjectRequest(req) == [req EXCEPT
    !.dbVersion = TimeValue(req.dbVersion),
    !.collectionGen = TimeValue(req.collectionGen),
    !.txnRuntimeContext.placementConflictTime = TimeValue(req.txnRuntimeContext.placementConflictTime)]
ProjectResponse(rsp) == IF rsp.status # OK THEN rsp ELSE
    [rsp EXCEPT !.snapshot.uuid = UUIDValue(rsp.snapshot.uuid)]
FiniteView == <<
    [databaseMetadata EXCEPT !.dbVersion = TimeValue(databaseMetadata.dbVersion)],
    [n \in NameSpaces |-> [collectionMetadata[n] EXCEPT !.collectionGen = TimeValue(@)]],
    [t \in Txns |-> [i \in DOMAIN log[t] |->
        [log[t][i] EXCEPT !.reqEntries = {ProjectRequest(req) : req \in @}]]],
    [t \in Txns |-> [i \in Stmts |-> {ProjectResponse(rsp) : rsp \in response[t][i]}]],
    TimeValue(clusterTime), UUIDValue(nextUUID),
    [rDatabaseCache EXCEPT !.dbVersion = TimeValue(rDatabaseCache.dbVersion)],
    [n \in NameSpaces |-> [rCollectionCache[n] EXCEPT !.collectionGen = TimeValue(@)]],
    rCompletedStmt,
    [t \in Txns |-> TimeValue(rPlacementConflictTime[t])],
    [s \in Shards |-> [t \in Txns |-> [shardTxnResources[s][t] EXCEPT
        !.snapshot = ProjectSnapshot(@), !.placementConflictTime = TimeValue(@)]]],
    shardData,
    [ts \in {TimeValue(old) : old \in CatalogTimes} |->
        LET old == CHOOSE v \in CatalogTimes : TimeValue(v) = ts
        IN [n \in NameSpaces |-> [s \in Shards |-> UUIDValue(shardNamespaceUUID[old][n][s])]]]
>>
====
