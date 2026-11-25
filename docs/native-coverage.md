# Native coverage census

**M** denotes measurement; **A** denotes a proposed lowering family or an
estimated benefit. Native coverage measures executed action/predicate evaluations,
not state count, static function count or the proportion of typed IR nodes.

The driver is `scripts/coverage.py`; selection, denominator, incomplete-evidence
policy and time attribution are documented in
[testing.md](testing.md#10-compiled-tier-coverage-scriptscoveragepy).
The census behind every table below is reproduced by the commands under
"Method and reproduction": the small Examples census writes
`target/native-small.json`, the cloud census `bench/native-census.json` and its
completion pass `bench/native-census-ext.json`, and the cloud union is the
primary JSON with the completion pass's rows merged. No census artifact is part
of the released tree, so this document names the files a run writes rather than
linking them. A census JSON is lossless: it retains each model's static
histograms and rejection reasons, function paths, host regions and the original
runtime statistics, and its `models` array contains the complete per-model
views; `operations` is a ranked aggregate, not a count of source expressions.

## Method and reproduction

Each configuration runs in compiled TLC compatibility mode, synchronously built,
with one search worker and `-stats json`; the census runs at most three
configurations at once and the completion pass at most five, on a 16-vCPU
instance either way.
No TLC timing run is performed. Existing timing baselines are left untouched. Host times are instrumented elapsed time, including
memo hits; the denominator is sampled/extrapolated search thread-seconds. These
are diagnostic measurements, not benchmark speedups or an additive CPU partition.
A share above 100% on a tiny case is possible because of the sampled denominator.

The small census is reproduced by one command (M):

```sh
python3 scripts/coverage.py --dynamic --source corpus --max-runtime 1 --timeout 20 -j 3 --bin target/release/tlx --out target/native-small.json --models
```

Build `target/release/tlx` first. This snapshot is from `2d87d5f6`, on macOS arm64.
The command exits 2 for six retained unknown metrics: five zero-evaluation cases
(CarTalkPuzzle Model_1, PrintValues, SimpleMath, Stones and MC_sums_even) and
EWD998ChanTrace, whose relative ndjson input cannot be read. The nonempty metrics
reproduced the preceding measurement's exact native and total evaluation counts.

The EWD998ChanTrace gap was staging, not a tlx difference: the model names its
trace relative to the Examples root and now runs there (`cwd: root` of the corpus
models, docs/testing.md section 6.1). A rerun of the command
therefore measures it, while the snapshot above keeps the numbers it was taken
with.

The cloud census uses this command (M), on revision `5bd45c7d`:

```sh
python3 scripts/cloud_verify.py 5bd45c7d --provider tencent --rust-from upload \
  --bench 'coverage --dynamic --source all --sizes small,medium,large --max-runtime 10 --prioritize ext/ccf,ext/mongo,ext/cassandra,ext/alpha-zk,ext/etcd,ext/neon,ext/vanlightly,ext/,bench/ --timeout 120 --deadline-min 45 -j 3 --release --no-build --models --out bench/native-census.json' \
  --max-minutes 60
```

The 120 s bound is what makes the run fit one launch; a configuration that
does not finish inside it contributes no dynamic ratio, so a bounded census
leaves a tail of configurations without data. A second pass over the same
external selection with a longer per-configuration timeout completes whichever
of those can finish at all:

```sh
python3 scripts/cloud_verify.py 5bd45c7d --provider tencent --rust-from upload \
  --bench 'coverage --dynamic --source external --sizes small,medium,large --timeout 900 --deadline-min 38 -j 5 --release --no-build --models --out bench/native-census-ext.json' \
  --max-minutes 60
```

Its rows replace the primary record's entries for the configurations it
measured completely; every other row is the primary pass's. It measured 69 of
the 123 external configurations, timed 14 out against the whole 900 s bound and
never started 40 more before its deadline passed, so the completion pass is
still bounded work, not a full sweep of the external selection. Both commands
sort their queue by the `--prioritize` substrings and then by configuration id,
and the completion command above passes no `--prioritize`: the configurations
it never started are the alphabetically late ones, which is why the largest
searches in this record's gap — `ext/vanlightly-vsr/*`, `ext/paxosstore/*_n3`,
`ext/vanlightly-kafka/*`, `ext/vanlightly-bookkeeper/*` — carry `deadline
skipped` rather than `timeout` in the supplement. A completion pass that wants
the large searches measured has to name them in `--prioritize`; the ordering is
a substring list and does not change the selection. Those rows are a
completion, not a second comparable census: they were collected on the same
instance type with a longer bound and more concurrent configurations, and the
archived record keeps the supplement's command, revision, replaced model list
and status counts under `supplement`. Interpreter time is a bounded-search
total, not a per-evaluation cost, so an operation's absolute host seconds are
only comparable between runs whose searches are identical; a faster native path
explores more states inside the same bound and can therefore accumulate more
host seconds than the slower path it replaced.

The archived record is the gzip of the primary JSON with those rows merged; a
census that cannot measure every selected entry exits 2, which the cloud wrapper
reports as exit 1 — an observation about the selection, not a failure of the
run.

The instance has 16 vCPUs, 32 GiB RAM, AMD EPYC 9754, Ubuntu 24.04 and clang 18
(Tencent SA5.4XLARGE32). Native Linux release all-target Clippy and the release
build passed before collection. Selection is the manifest union: Examples with
runtime annotation at most 10 seconds, external small/medium/large configurations,
and the benchmark registry in those sizes. Duplicate IDs run once; benchmark aliases of external configurations are separate
selected entries and can therefore weight a workload more than once. The overall
share is evaluation-weighted across this selection, not a unique-spec mean. Suite
`huge` entries are excluded. Missing inputs, compiler errors, timeouts and deadline skips
remain selected. Observed outcomes are execution results, not new oracle/parity
judgments. A bounded census can exit 2 with useful but incomplete evidence;
the cloud wrapper propagates that nonzero result. A killed process that never
writes final statistics has no dynamic ratio; no timeout is treated as native.
A recorded timeout means the configuration did not finish inside the bound, not
that it cannot, and not that it is large:
`ext/vanlightly-kafka/consumer_group_protocol_kip_848_v2` was killed at the
120 s bound with its retained output stopping right after the pre-run, the same
binary, environment and flags reproduce the TLC oracle's 31,441 distinct
states, depth 12 and deadlock verdict here in about one second, and the
completion pass then measured it at a 900 s bound. The configurations without
data are therefore a mixture of search spaces no bound in this record reaches
and collection the census could not complete, and the size of the TLC oracle's
own run is the only guide to which is which.
At the time of this census the CLI exited after signal cleanup without counters.
Current builds emit best-effort interrupted statistics during TERM grace, including
active-worker and host-region snapshots. The census preserves these as partial
evidence, never as completed measurements; see [configuration.md](configuration.md)
for snapshot and adaptive-tier metadata semantics.

The tooling that produced this record labels `Call` roots with their callee and
anonymous applied operators with their source position (`Interp apply-def
@236:30`), so those rows carry a name instead of an empty argument list. The
archived JSON is this revision's own output, so its `operations` aggregate needs
no reclassification.

Every table below is computed from that one archived record by one stated rule,
because a table generated from a different record than the prose around it is a
defect and not a rounding difference — the preceding revision's "below the
thresholds" table was generated from its 120 s pass while its prose counted the
merged record, which is why it listed 33 rows while the prose said 36. The
totals row and the outcome row are summed over the record's `models`; the
"below the thresholds" table is every `ext/` row with a complete measurement
that misses the target, and its summary counts both rules; its per-model
operation column aggregates that model's `regions` by operation and argument
shape and keeps the three that spent the most host time there; the ranked table
keeps each `operations` row that spent at least 1% of the record's interpreter
time and names the model with the largest host time in it; the closure table
counts the models behind each `static.closure_functions` pair; the families
table groups the `operations` rows by family and the "gain ceiling" is the
non-native evaluations of the complete measured models in which that family
executed.

## Census totals (M)

| Run | Selected | Reported | Nonempty dynamic | Fully native / all evaluations | Native share | Static reports | Static typed/boxed/interpreted nodes | Host calls | Host time | Host time share estimate |
|---|---|---|---|---|---|---|---|---|---|---|
| Small | 88 | 88 | 82 | 8,825,220/8,859,154 | 99.61696% | 82 | 91,887/586/106 | 115,646 | 0.021611s | 1.35982% |
| Cloud | 334 | 334 | 271 | 5,110,016,207/5,205,428,023 | 98.16707% | 315 | 4,159,237/151,281/12,620 | 143,567,097 | 64.646806s | 3.21820% |

Only complete nonempty measurements contribute to the native and aggregate time
shares above, so the Cloud row covers the 271 configurations this record could
bound and changes meaning whenever a pass measures configurations the previous
one could not. 69 of them came from the completion pass, whose rows run from 48
to 792,336,575 evaluations, so the row is not comparable with the preceding
record's, which covered 277. Over the 120 s census alone the same figures are
3,576,439,424/3,627,886,797 (98.58189%), 66,360,810 host calls, 46.947825s of
interpreter time and a 3.11611% host time share; the preceding record's 120 s
census read 3,562,631,966/3,627,883,222 (98.20140%), 155,379,959 host calls and
58.025849s of interpreter time. The two 120 s passes cover the same selection and
almost the same evaluations (3,627,886,797 against 3,627,883,222), so they are
comparable: the same bounded search now enters host regions 66,360,810 times
instead of 155,379,959 and spends 46.948s in them instead of 58.026s.

Static totals include every reported layout/program version, even when its
search did not finish. Static classifications preserve the existing coverage
categories; typed-classified constants and iteration sources can still carry
boxed values. Neither a typed node nor a boxed node alone determines native
backend support. Native runtime helpers count as native; host interpreter entry,
closure IR and fallback paths do not.

| Run | Observed outcomes (M) |
|---|---|
| Small | error: 1, liveness failure: 1, safety failure: 12, success: 74 |
| Cloud | deadlock: 13, error: 6, liveness failure: 7, safety failure: 45, success: 218, timeout: 45 |

The final cloud record contains every selected entry. Its 65 unknown primary
metrics comprise 47 timeouts, six execution errors and 12 completed runs with
zero counted evaluations; the completion pass then measured some of the
timeouts and left 31 external configurations without a dynamic measurement. The six errors are
two set/function cardinality overflows, two illegal-initial-state export cases,
one missing trace input and one liveness memory-budget error. These are observed
collection gaps; this census does not diagnose their semantic correctness. The
liveness memory-budget case wrote search statistics, retained as partial evidence
but excluded from the primary aggregate. The primary pass skipped no entry
against its own deadline; the completion pass did, and the rows it never started
are the ones its `supplement` record lists as `deadline skipped`.

### Small evaluation kinds (M)

| Kind | Fully native | All | Share |
|---|---|---|---|
| actions | 6,150,494 | 6,159,721 | 99.85020% |
| invariants | 851,385 | 855,841 | 99.47934% |
| action_properties | 1,823,341 | 1,843,592 | 98.90155% |

### Representative configurations (M)

All selected configurations, including unknowns, are retained in the JSON. The
Examples rows are the lowest native shares of the small census above and carry
that run's host time share; the `bench/` and `ext/` rows are this cloud census
and cover the named large-model families and benchmark aliases. `unknown` is
missing evidence.

| Model | Native share | Host time share estimate | Evaluations | Outcome |
|---|---|---|---|---|
| N-Queens/QueensPluscal.toolbox/FourQueens/MC | 67.03704% | 32.35194% | 270 | safety failure |
| glowingRaccoon/product | 70.06110% | 52.03669% | 8,347 | success |
| YoYo/MCYoYoPruning | 81.52425% | 80.31042% | 866 | success |
| SpecifyingSystems/CachingMemory/MCWriteThroughCache | 81.54411% | 23.03926% | 116,494 | success |
| bcastByz/bcastByzNoBcast | 83.33333% | 4.19968% | 270 | success |
| locks_auxiliary_vars/Peterson | 88.51964% | 34.08667% | 662 | success |
| N-Queens/Queens.toolbox/FourQueens/MC | 88.54962% | 33.07104% | 131 | safety failure |
| echo/MCEcho | 91.42539% | 250.54419% | 898 | success |
| bench/ClockSettles | 100.00000% | 0.00000% | 180 | liveness failure |
| bench/FlexibleRaftReduced5 | 74.01320% | 15.00543% | 9,440,570 | success |
| bench/RaftMongoT4 | 97.33184% | 7.34883% | 243,913,005 | success |
| bench/ReplicatedLog4x3 | 93.48412% | 0.00000% | 8,654,553 | success |
| bench/ReprAccordChain | 91.26715% | 12.15138% | 256,789 | success |
| bench/ReprAccordKeys | 91.81540% | 12.13642% | 30,032 | success |
| bench/ReprAccordLoad | 97.96050% | 7.03268% | 98,946 | success |
| bench/ReprBakery | 100.00000% | 0.00000% | 756 | success |
| bench/ReprCCFMedium | 98.85794% | 0.00000% | 244,295 | success |
| bench/ReprCCFMulti | 99.29594% | 0.00000% | 29,969 | success |
| bench/ReprCCFReads | 99.42169% | 0.00000% | 58,619 | success |
| bench/ReprCCFSingle | 98.75940% | 0.00000% | 2,660 | success |
| bench/ReprKRaft | 71.81059% | 64.84596% | 46,968 | deadlock |
| bench/ReprKVS | 100.00000% | 0.00000% | 254,743 | success |
| bench/ReprLamportMutex | 100.00000% | 0.00000% | 375,009 | success |
| bench/ReprMongoReconfig | 100.00000% | 0.00000% | 876,413 | success |
| bench/ReprMoveRange | 98.99519% | 1.46073% | 222,928 | success |
| bench/ReprPaxosCommit | 100.00000% | 0.00000% | 9,264 | success |
| bench/ReprPullRaft | 99.02770% | 3.88719% | 60,064 | deadlock |
| bench/ReprRaft | 76.22887% | 63.27968% | 117,710 | deadlock |
| bench/ReprRaftAddRemove | 87.21716% | 32.08682% | 739,155 | deadlock |
| bench/ReprRaftFsync | 79.83577% | 57.34487% | 184,738 | deadlock |
| bench/ReprRaftJoint | unknown | unknown | unknown | deadlock |
| bench/ReprRaftMongo | 97.33909% | 11.37406% | 1,908,519 | success |
| bench/ReprZab | 99.94510% | 3.02944% | 69,214 | success |
| ext/alpha-zk/MC_tlx_Zab_new | 99.90901% | 0.33044% | 143,804,486 | success |
| ext/alpha-zk/MC_tlx_Zab_new_big | unknown | unknown | unknown | timeout |
| ext/cassandra/Accord_baseline__deep_chain | 91.67656% | 7.91509% | 4,074,351 | success |
| ext/cassandra/Accord_baseline__deep_chain_live | 89.65470% | 36.43457% | 5,539,965 | success |
| ext/cassandra/Accord_probe_bag_interleaves__keys_only | 89.36767% | 17.07294% | 99,141 | safety failure |
| ext/ccf/MCMultiNode | 99.58877% | 0.00000% | 29,378,281 | success |
| ext/ccf/MCMultiNodeReads | 99.66000% | 0.00000% | 58,662,962 | success |
| ext/ccf/MCSingleNodeOrderedSerializable | 97.63778% | 0.00000% | 317,244 | success |
| ext/ccf/MCccfraft_1C2N | 66.67882% | 21.20614% | 2,743 | safety failure |
| ext/ccf/MCccfraft_1C3N | 66.70717% | 15.12767% | 823 | safety failure |
| ext/etcd-raft/MCetcdraft_3s_t2 | unknown | unknown | unknown | timeout |
| ext/etcd-raft/Traceetcdraft_400 | 75.48638% | 78.69613% | 4,626 | success |
| ext/mongo/MCMongoReplReconfig | 100.00000% | 0.00000% | 117,072,637 | success |
| ext/mongo/MCMoveRange | 98.99821% | 0.61831% | 22,390,911 | success |
| ext/mongo/MCRaftMongo | 97.42339% | 1.36753% | 60,601,586 | success |
| ext/mongo/MCTxnsMoveRange | 75.85276% | 12.48406% | 18,516,898 | success |
| ext/neon/MCProposerAcceptorReconfig_p2_a3_t2_l2_c3 | unknown | unknown | unknown | timeout |
| ext/neon/MCProposerAcceptorStatic_p2_a3_t2_l2 | 99.58417% | 0.18749% | 6,293,228 | success |
| ext/neon/MCProposerAcceptorStatic_p2_a3_t3_l3 | unknown | unknown | unknown | timeout |
| ext/vanlightly-raft/flexible-raft-FlexibleRaft | unknown | unknown | unknown | timeout |
| ext/vanlightly-raft/standard-raft-Raft | 77.00910% | 24.38692% | 1,824,652 | deadlock |

### External configurations below the thresholds (M)

The coverage target for an external configuration is a host time share below
20% (the threshold was adjusted on 2026-10-09: the native share is reported and
was previously also required to reach 80%, but it counts each evaluation as
fully native or not, so it moves in steps and does not measure speed). Of the
92 external configurations with a complete measurement, 15 miss the `< 20%`
host-time target, while **19 miss at least one of the two thresholds** (`< 80%`
native evaluations or `>= 20%` host time: 13 below 80% native share, 15 at or
above 20% host time share, 9 missing both, and 4 missing only `< 80%` native
share while staying below 20% host time — `ext/ccf/MCccfraft_1C3N`,
`ext/mongo/MCTxnsMoveRange`, `ext/vanlightly-raft/pull-raft-KRaft` and
`ext/vanlightly-raft/raft-and-fsync-RaftFsync`). The table below lists all 19
union configurations, whose interpreter time totals 10.741s:
`ValOp >` 2.429s (22.6%); `ValOp \in` 2.074s (19.3%); `Eq` 1.546s (14.4%);
`ValOp @@` 1.367s (12.7%); `ValOp DOMAIN` 0.745s (6.9%) and `Interp Except`
0.697s (6.5%). The same union list against the preceding record held 41
configurations (36 over the 20% host-time line) totalling 1278.124s, so the
interpreter time of the below-threshold union fell by 119x, but the populations
differ: the revisions differ, one completion pass has run against each record,
and seven of the fifteen configurations over the 20% host-time line exceed it by
less than 10 ms of interpreter time — six of them under 2 ms each, on searches
of 101 to 2,743 evaluations whose whole denominator is a few milliseconds — so
the fall is a statement about the wave and not a like-for-like comparison of the
same configurations. The operations listed below are up to three per configuration,
the ones that spent the most host time there; they are one entry per region, so
a configuration can repeat an operation with different argument shapes. A
configuration without a complete measurement is absent here rather than counted
as passing: this list is what the record bounds, not the whole external
selection, and the 31 it does not bound are listed with the TLC oracle's own
run below.

| Model | Native share | Host time share | Evaluations | Top interpreter operations (host seconds) |
|---|---|---|---|---|
| ext/cassandra/Accord_baseline__consequence_non_subset | 93.14641% | 24.50386% | 1,217,435 | `ValOp \in` [Val, Val] 0.038s; `Interp Quant` [] 0.017s; `ValOp \` [Set bitset(21) of Atom(21), Val] 0.013s |
| ext/cassandra/Accord_baseline__deep_chain_live | 89.65470% | 36.43457% | 5,539,965 | `Exists` [Val, Bool] 0.617s; `ValOp \subseteq` [Set bitset(0) of Never, Val] 0.027s; `ValOp \in` [Val, Val] 0.020s |
| ext/cassandra/Accord_baseline__two_lockers_live | 89.21973% | 39.44629% | 30,092 | `Exists` [Val, Bool] 0.005s; `ValOp \in` [Val, Val] 0.000s; `ValOp \subseteq` [Set bitset(0) of Never, Val] 0.000s |
| ext/cassandra/Accord_ctl_fifo_adopt__consequence_non_subset | 91.89355% | 23.95139% | 2,066,848 | `ValOp \in` [Val, Val] 0.096s; `ValOp \` [Set bitset(21) of Atom(21), Val] 0.057s; `ValOp \subseteq` [Set bitset(0) of Never, Val] 0.015s |
| ext/ccf/MCccfraft_1C2N | 66.67882% | 21.20614% | 2,743 | `Interp builtin FoldLeft` [Val, Val] 0.000s; `Forall` [Val, Bool] 0.000s; `Temp` [] 0.000s |
| ext/ccf/MCccfraft_1C3N | 66.70717% | 15.12767% | 823 | `Forall` [Val, Bool] 0.000s; `Interp builtin FoldLeft` [Val, Val] 0.000s; `ValOp >` [Val, Val] 0.000s |
| ext/ccf/TraceMultiNodeReads_ElectionNoRollback | 18.75000% | 37.62772% | 288 | `ValOp \in` [Val, Val] 0.000s; `Eq` [Val, Val] 0.000s; `Interp Except` [Val] 0.000s |
| ext/ccf/TraceMultiNodeReads_ElectionNonContiguousView | 18.75000% | 37.73642% | 352 | `ValOp \in` [Val, Val] 0.001s; `ValOp <` [Val, Val] 0.000s; `Interp builtin SubSeq` [Seq(max 22) of Union(2 arms)] 0.000s |
| ext/ccf/TraceMultiNodeReads_RollbackSameSeqno | 18.82716% | 20.71053% | 324 | `ValOp \in` [Val, Val] 0.000s; `Eq` [Val, Val] 0.000s; `ValOp <` [Val, Val] 0.000s |
| ext/ccf/TraceMultiNodeReads_RollbackTwoTransactions | 18.75000% | 47.38201% | 416 | `ValOp \in` [Val, Val] 0.001s; `Eq` [Val, Val] 0.000s; `ValOp <` [Val, Val] 0.000s |
| ext/etcd-raft/Traceetcdraft_400 | 75.48638% | 78.69613% | 4,626 | `Eq` [Dyn, Val] 0.206s; `Interp Quant` [] 0.079s; `Eq` [Val, Val] 0.028s |
| ext/mongo/MCTxnsMoveRange | 75.85276% | 12.48406% | 18,516,898 | `Eq` [Val, Int] 0.768s |
| ext/pragmatic/specjuniorv1 | 0.00000% | 42.33319% | 101 | `Eq` [Val, Bool] 0.000s; `Interp Quant` [] 0.000s; `Exists` [Val, Bool] 0.000s |
| ext/vanlightly-raft/pull-raft-KRaft | 73.23206% | 11.54165% | 3,135,322 | `ValOp >` [Val, Int] 0.484s; `ValOp @@` [Dyn, Val] 0.203s; `ValOp \in` [Record(6 fields), Val] 0.163s |
| ext/vanlightly-raft/pull-raft-PullRaft | 71.10277% | 25.13540% | 2,682,842 | `ValOp >` [Val, Int] 0.781s; `Interp Except` [Val] 0.218s; `ValOp DOMAIN` [Dyn] 0.192s |
| ext/vanlightly-raft/raft-and-fsync-RaftFsync | 78.47850% | 16.48751% | 4,458,220 | `ValOp @@` [Dyn, Val] 0.463s; `ValOp \in` [Record(8 fields), Val] 0.361s; `ValOp \in` [Record(6 fields), Val] 0.242s |
| ext/vanlightly-raft/standard-raft-Raft | 77.00910% | 24.38692% | 1,824,652 | `ValOp >` [Val, Int] 0.507s; `ValOp \in` [Record(8 fields), Val] 0.189s; `ValOp @@` [Dyn, Val] 0.149s |
| ext/vanlightly-raft/standard-raft-RaftWithReconfigAddRemove | 87.21716% | 32.03471% | 739,155 | `ValOp >` [Val, Int] 0.042s; `Eq` [Val, Val] 0.036s; `ValOp DOMAIN` [Dyn] 0.028s |
| ext/vanlightly-raft/standard-raft-RaftWithReconfigJointConsensus | 85.42724% | 28.46370% | 3,670,258 | `ValOp @@` [Dyn, Val] 0.377s; `ValOp \in` [Record(8 fields), Val] 0.285s; `ValOp >` [Val, Int] 0.241s |

### What the host share does not decide (M)

The census reports a number whose size depends on where the interpreter boundary
sat during one bounded search, and the boundary is chosen at run time.
`TLX_MIXED_ADAPT` (on by default) makes every mixed function sample and time
both its mixed native and its fallback path and then pick the faster one, and
the sampling itself runs the function and enters its host regions. On
`ext/vanlightly-raft/standard-raft-Raft` — deadlock, 86,097 distinct states,
1,824,652 evaluations and the same static node histogram in every row below —
one binary, one spec and one layout give:

| Run | `TLX_MIXED_ADAPT` | Fully native | Host region entries | Host seconds | Host time share |
|---|---|---|---|---|---|
| this census, Linux x86_64 | default | 1,405,182 | 1,679,395 | 1.345 | 24.39% |
| the preceding record, Linux x86_64 | default | 1,404,101 | 712,233 | 0.570 | 11.67% |
| local, macOS arm64, two runs | default | 1,404,064 / 1,405,148 | 712,233 / 712,245 | 0.221 / 0.225 | 11.90% / 11.89% |
| local, macOS arm64, two runs | 0 | 1,409,431 | 6,994,465 | 1.213 / 1.277 | 66.62% / 66.69% |

The evaluation count, the search result and the fully native count (within 0.4%)
agree across all six, so this is not a lowering difference and not extra
non-native work: it is the tier decision and the platform, and it moves the same
model across the 20% line from 11.7% to 24.4%, and to 66.7% with the adaptive
tier off. Four of the fifteen configurations over the line are
`ext/vanlightly-raft/*`, and the preceding record already recorded the same
effect on `bench/FlexibleRaftReduced5`; a single configuration's host share is
therefore not by itself evidence of a regression or of a pass. Read a
configuration near the line with an uninstrumented benchmark, and treat a
census that does not record each function's chosen tier as inconclusive for it.
Current stats and dynamic census output preserve per-worker adaptive decisions and
sample timings; the historical rows above predate that metadata.

### Configurations without a dynamic measurement (M)

31 of the 123 external configurations are absent from the two tables above
because neither pass bounded their search, and they are this record's whole
external gap. Size explains most of them: the shared TLC oracle, which ran them
with 1, 8 or 16 workers, has a wall time for 23 of them, failed to collect a
result for four, and has no row at all for four. Those wall times are not tlx
measurements and do not forecast one; they show the scale a longer-bound
completion pass has to cover. The completion pass ran 14 of this list against
the whole 900 s bound and never started the other 17 before its deadline, so
where the boundary between measured and unmeasured falls here is a matter of the
bound, the queue order and the budget as well as of size — the 17 it never
started are the largest searches in the gap.

| Model | TLC oracle wall time | TLC workers | TLC outcome |
|---|---|---|---|
| ext/vanlightly-kafka/consumer_group_protocol_kip_848_v2 | 1 s | – | deadlock, 31,441 distinct |
| ext/vanlightly-kafka/kafka_replication_v3_5 | 68 s | 16 | deadlock, 2,062,129 distinct |
| ext/vanlightly-vsr/VSR | 80 s | 16 | deadlock, 1,617,552 distinct |
| ext/vanlightly-vsr/VR_INC_RESEND | 3 min | 16 | deadlock, 340,293 distinct |
| ext/vanlightly-vsr/VR_APP_STATE | 5 min | 1 | deadlock, 1,290,004 distinct |
| ext/vanlightly-vsr/VR_STATE_TRANSFER | 6 min | 1 | deadlock, 1,300,432 distinct |
| ext/vanlightly-kafka/kraft_kip_853_small | 6 min | 16 | deadlock, 5,269,758 distinct |
| ext/vanlightly-bookkeeper/BookKeeperProtocol_v4_13 | 8 min | 1 | safety failure, 1,937,518 distinct |
| ext/paxosstore/TPaxosRefVoting_p2_v2_n3 | 9 min | 16 | success, 12,107,912 distinct |
| ext/elastic/ReplicaEngine | 10 min | 8 | success, 112,881,036 distinct |
| ext/paxosstore/TPaxosAPRefEagerVoting_p2_v2_n3 | 11 min | 16 | success, 12,107,912 distinct |
| ext/paxosstore/TPaxos_p2_v2_n3 | 11 min | 16 | success, 24,206,600 distinct |
| ext/vanlightly-kafka/kafka_replication_kip_966 | 11 min | 16 | deadlock, 17,143,702 distinct |
| ext/paxosstore/TPaxosAP_p2_v2_n3 | 11 min | 16 | success, 24,206,600 distinct |
| ext/vanlightly-vsr/VR_ASSUME_NEWVIEWCHANGE | 11 min | 16 | deadlock, 1,065,555 distinct |
| ext/neon/MCProposerAcceptorStatic_p2_a3_t3_l3 | 18 min | 1 | success, 17,936,128 distinct |
| ext/elastic/replication | 36 min | 8 | success, 35,431,087 distinct |
| ext/neon/MCProposerAcceptorStatic_p2_a5_t2_l2 | 39 min | 1 | success, 6,929,902 distinct |
| ext/alpha-zk/MC_tlx_Zab_new_timeout | 39 min | 8 | success, 49,971,966 distinct |
| ext/logless-reconfig/MCMongoRaftReconfig-4Servers-L2-T2-CV3 | 43 min | 16 | success, 18,766,114 distinct |
| ext/neon/MCProposerAcceptorReconfig_p2_a2_t2_l2_c5 | 70 min | 1 | success, 46,952,052 distinct |
| ext/alpha-zk/MC_tlx_Zab_new_big | 89 min | 8 | success, 167,864,269 distinct |
| ext/neon/MCProposerAcceptorReconfig_p2_a3_t2_l2_c3 | 8.4 h | 1 | success, 33,473,811 distinct |
| ext/elastic/consensus | collection error | 8 | TLC could not collect a result |
| ext/etcd-raft/MCetcdraft_4s_t3_reconfig | collection error | 16 | TLC could not collect a result |
| ext/vanlightly-bookkeeper/BookKeeperProtocol | collection error | 8 | TLC could not collect a result |
| ext/vanlightly-kafka/kraft_kip_996_small | collection error | 8 | TLC could not collect a result |
| ext/etcd-raft/MCetcdraft_3s_t2 | no TLC oracle row | – | – |
| ext/etcd-raft/Traceetcdraft | no TLC oracle row | – | – |
| ext/mongo/MCTxnsCollectionIncarnation | no TLC oracle row | – | – |
| ext/vanlightly-raft/flexible-raft-FlexibleRaft | no TLC oracle row | – | – |

## Ranked non-native operations (M), proposed families (A)

This ranking uses all observed host-region counters, including available partial
search evidence. A model counts as affected only if that operation executed at
least once; zero-call region presence is kept separately in current JSON. Calls
are region entries, not evaluations: one evaluation can enter several regions or
the same region repeatedly. Argument shapes are representations at that boundary,
not a claim that the operation is intrinsically unsupported for all such values.
`Val` is an opaque boxed value; empty arguments on a captured HIR fallback mean
that its original argument shapes were not retained. Names in the model column
are examples; the JSON lists all affected models.

| Operation (M) | Argument shapes (M) | Executed models (M) | Calls (M) | Host time (M) | Lowering family (A) | Example model |
|---|---|---|---|---|---|---|
| `Interp Quant` | not retained | 8 | 303,187 | 11.530356s | Quantifiers and CHOOSE | bench/RaftMongoT4 |
| `ValOp >` | Val, Int | 15 | 10,814,716 | 5.385859s | Heterogeneous comparison and membership | bench/FlexibleRaftReduced5 |
| `Interp FnConstruct` | Val | 1 | 12,972,882 | 4.748705s | Strings | ext/mongo/MCRaftMongoReplTimestamp |
| `Interp Quant` | Int -10..61 | 1 | 1,693,626 | 4.525555s | Quantifiers and CHOOSE | ewd998/EWD998Chan |
| `Temp` | not retained | 48 | 22,736,785 | 3.141586s | Other operations (inspect IR root) | ext/mongo/MCRaftMongoReplTimestamp |
| `Interp apply-def @236:30` | not retained | 1 | 12,972,882 | 3.050210s | Functions and records with dynamic values | ext/mongo/MCRaftMongoReplTimestamp |
| `Interp builtin \in` | not retained | 4 | 11,750,338 | 2.096320s | Heterogeneous comparison and membership | aba-asyn-byz/aba_asyn_byz |
| `ValOp <=` | Val, Int | 2 | 937,473 | 1.771012s | Heterogeneous comparison and membership | bench/FlexibleRaftReduced5 |
| `Interp apply-def @189:42` | Record(2 fields) | 1 | 7,834,977 | 1.724274s | Functions and records with dynamic values | ext/mongo/MCRaftMongoReplTimestamp |
| `Interp apply-def @212:42` | Val, Val, Map(universe 5) of Int 1..5 to Record(1 fields) | 1 | 4,273,416 | 1.717587s | Functions and records with dynamic values | ext/mongo/MCRaftMongoReplTimestamp |
| `Interp builtin @@` | Val, Val | 8 | 251,583 | 1.709731s | Functions and records with dynamic values | bench/FlexibleRaftReduced5 |
| `ValOp \in` | Val, Val | 43 | 3,873,156 | 1.652947s | Heterogeneous comparison and membership | bench/FlexibleRaftReduced5 |
| `ValOp @@` | Dyn, Val | 11 | 355,253 | 1.579810s | Functions and records with dynamic values | ext/vanlightly-raft/raft-and-fsync-RaftFsync |
| `ValOp DOMAIN` | Dyn | 12 | 954,903 | 1.345165s | Functions and records with dynamic values | bench/FlexibleRaftReduced5 |
| `ValOp \in` | Set bitset(3) of Atom(3), Val | 1 | 1,502,594 | 1.340181s | Heterogeneous comparison and membership | dag-consensus/TLCSailfish1 |
| `Eq` | Val, Val | 44 | 6,427,751 | 1.300396s | Heterogeneous comparison and membership | bench/FlexibleRaftReduced5 |
| `Interp apply-def @207:30` | Val, Map(universe 5) of Int 1..5 to Record(1 fields) | 1 | 4,273,416 | 1.256526s | Functions and records with dynamic values | ext/mongo/MCRaftMongoReplTimestamp |
| `Interp apply-def @211:57` | Val, Map(universe 5) of Int 1..5 to Record(1 fields) | 1 | 4,273,416 | 1.190556s | Functions and records with dynamic values | ext/mongo/MCRaftMongoReplTimestamp |
| `ValOp \in` | Record(8 fields), Val | 8 | 381,587 | 1.105298s | Heterogeneous comparison and membership | ext/vanlightly-raft/raft-and-fsync-RaftFsync |
| `Interp Quant` | Int -10..14 | 1 | 328,319 | 0.956173s | Quantifiers and CHOOSE | ewd998/EWD998Chan |
| `Eq` | Val, Int | 14 | 5,880,294 | 0.850413s | Heterogeneous comparison and membership | ext/mongo/MCTxnsMoveRange |
| `Interp Record` | Map(universe 5) of Int 1..5 to Record(1 fields) | 1 | 4,273,416 | 0.827577s | Functions and records with dynamic values | ext/mongo/MCRaftMongoReplTimestamp |
| `Interp Except` | Union(2 arms), Int | 1 | 366,412 | 0.827133s | Functions and records with dynamic values | ewd998/EWD998Chan |
| `Interp Except` | Val | 16 | 790,530 | 0.807837s | Functions and records with dynamic values | bench/FlexibleRaftReduced5 |
| `Exists` | Val, Bool | 14 | 337,188 | 0.732413s | Quantifiers and CHOOSE | ext/cassandra/Accord_baseline__deep_chain_live |

### Closure functions and missing attribution

Static backend rejections are preserved independently of dynamic host counters.
Each reason is the first surfaced backend blocker; removing it can expose another.
Long reasons are abbreviated here; the JSON retains their full argument types.
Direct whole-function closure IR has evaluation path counts but no per-operation
host timer. IR/interpreter/fallback calls without a static rejection are labelled
`unattributed execution path`: startup, adaptive tier selection, generation mode
or layout/runtime fallback can cause these calls. They are not evidence of an
unsupported lowering operation and are not assigned a speculative hot operation.

| Function (M) | Native rejection reason, abbreviated (M) | Models with rejection (M) |
|---|---|---|
| invariant ? | predicate without a native prefix | 10 |
| action IsRoTxRequestAction | boxed equality | 4 |
| action IsRoTxResponseAction | boxed equality | 4 |
| action IsRwTxExecuteAction | boxed equality | 4 |
| action IsRwTxRequestAction | boxed equality | 4 |
| action IsRwTxResponseAction | boxed equality | 4 |
| action IsStatusCommittedResponseAction | boxed equality | 4 |
| action IsStatusInvalidResponseAction | boxed equality | 4 |
| action ExecuteTxAndReduction | action composition uses the compiled executor | 2 |
| action RcvAppendEntriesRequest | action composition uses the compiled executor | 2 |
| action VIEW | representation change Enc(5) -> Tuple([Union([Int { lo: 0, hi: 5 }, Atom([v1, v2, Normal, ViewChange, PrepareMsg, PrepareOkMsg, StartViewChangeMsg, DoViewChangeMsg, StartViewMsg, Nil]), Seq { elem: Un… | 2 |
| action WriteTxAndReduction | action composition uses the compiled executor | 2 |
| function SendAllFunc | boxed equality | 2 |
| function SetPacketsForChecking | representation change Enc(48) -> Set { elem: Record([("zxid", Tuple([Int { lo: 0, hi: 3 }, Int { lo: 0, hi: 3 }])), ("epoch", Int { lo: 0, hi: 3 }), ("source", Atom([s1, s2, s3, mv_NullPoint, LOOKING,… | 2 |
| action GossipAndReduction | action composition uses the compiled executor | 1 |
| action IncrementAndReduction | action composition uses the compiled executor | 1 |
| action VIEW | boxed value | 1 |
| action VIEW | call of a function that is not native | 1 |
| action VIEW | representation change Enc(5) -> Fcn { dom: [n1, n2, n3, n4, n5], range: Union([Int { lo: 0, hi: 6 }, Tuple([])]) } | 1 |
| action VIEW | representation change Enc(5) -> Tuple([Union([Int { lo: 0, hi: 5 }, Atom([v1, v2, Normal, ViewChange, StateTransfer, PrepareMsg, PrepareOkMsg, StartViewChangeMsg, DoViewChangeMsg, StartViewMsg, GetSta… | 1 |
| function ApplyOps | representation change Bool -> Atom([DocA, DocB, UPDATE, NULL, ADD, DELETE, RETRY_ADD, Lucene_deleteDocuments, Lucene_addDocuments, Lucene_updateDocuments, defaultInitValue]) | 1 |
| function F | representation change Enc(10) -> Record([("color", Atom(["white", "black", "tok", "pl"])), ("type", Atom(["white", "black", "tok", "pl"])), ("q", Int { lo: 0, hi: 6 })]) | 1 |
| function F | representation change Enc(11) -> Record([("color", Atom(["white", "black", "tok", "pl"])), ("type", Atom(["white", "black", "tok", "pl"])), ("q", Int { lo: 0, hi: 6 })]) | 1 |
| function SetPacketsForChecking | representation change Enc(47) -> Never | 1 |
| function SetPacketsForChecking | representation change Enc(48) -> Never | 1 |
| function SetPacketsForChecking | representation change Enc(54) -> Set { elem: Record([("zxid", Tuple([Int { lo: 0, hi: 4 }, Int { lo: 0, hi: 4 }])), ("epoch", Int { lo: 0, hi: 4 }), ("source", Atom([s1, s2, s3, mv_NullPoint, LOOKING,… | 1 |
| function SetPacketsForChecking | representation change Enc(56) -> Set { elem: Record([("zxid", Tuple([Int { lo: 0, hi: 4 }, Int { lo: 0, hi: 4 }])), ("epoch", Int { lo: 0, hi: 3 }), ("source", Atom([s1, s2, s3, mv_NullPoint, LOOKING,… | 1 |
| function ZxidToIndexHepler | boxed value | 1 |
| invariant InterestingBehavior | predicate without a native prefix | 1 |
| invariant Inv | predicate without a native prefix | 1 |
| invariant PostInv | predicate without a native prefix | 1 |

## Dispatch-sized lowering families (A)

Families are ranked by observed cloud host time. The gain ceiling is the number
of non-native evaluations in complete measured models where that family executed; it deliberately
includes other causes and is an upper bound, not a forecast. Ceilings overlap and
must not be added. Removing one region does not make an evaluation fully native
when another host region remains. Each implementation needs a fresh native-share
census and an uninstrumented large-model benchmark before claiming a speedup.

A host time is the elapsed time of region entries, and one evaluation can enter
a region several times, so the total moves when the interpreter boundary moves
even if the search does not. `bench/FlexibleRaftReduced5` executes the same
9,440,570 evaluations with the same fully native count on two revisions of the
archived records, yet its region entries rose from 4.27M to 12.07M and its
host time from 3.49s to 9.10s, with wall time flat (56.6s to 57.5s) and encode
time halved; and `ext/vanlightly-raft/standard-raft-Raft` reads 11.67% and
24.39% on one revision, from one binary, in the two cloud records above. Read a
per-operation host time as a statement about where the interpreter boundary sat
during one bounded search, and compare two revisions per model only after
checking that the model's evaluation counts agree. The rows of the table below
that spent at least 1% of this record's interpreter time are the ones above it;
an absolute cutoff would not survive a record whose interpreter time fell by two
orders of magnitude.

| Family / candidate worker scope (A) | Executed models (M) | Host calls (M) | Host time (M) | Gain ceiling among measured models (A) |
|---|---|---|---|---|
| Quantifiers and CHOOSE | 57 | 7,689,072 | 19.135910s | ≤ 34,069,090 |
| Heterogeneous comparison and membership | 66 | 54,405,243 | 18.792046s | ≤ 37,627,249 |
| Functions and records with dynamic values | 29 | 43,348,736 | 17.533410s | ≤ 52,535,524 |
| Strings | 1 | 12,972,882 | 4.748705s | ≤ 42,329,695 |
| Other operations (inspect IR root) | 79 | 24,426,494 | 3.815084s | ≤ 78,827,266 |
| Set algebra and construction on dynamic elements | 22 | 431,833 | 0.578545s | ≤ 57,020,758 |
| Sequence sorting and filtering | 24 | 275,139 | 0.038924s | ≤ 1,819,908 |
| FiniteSets and Bags | 2 | 14,509 | 0.002693s | ≤ 44,278 |
| Sequences with dynamic elements | 16 | 3,189 | 0.001489s | ≤ 2,371,708 |

The families above are not what is left to do. The lowerings that this record
measures the effect of were delivered against the preceding one, whose failing
union carried 1278.124s of interpreter time; this one carries 10.741s across the
19-configuration union (15 over the 20% host-time line), and most of that is not
a missing lowering. What the evidence
supports now, in order of the interpreter time it can move:

1. **Make the measurement decide, before another lowering batch is dispatched.**
   Four of the fifteen configurations over the line are
   `ext/vanlightly-raft/*`, and the table in "What the host share does not
   decide" shows their verdict is set by `TLX_MIXED_ADAPT` and by the platform,
   not by the program: one binary and one spec read 11.9% locally and 24.4% in
   this census, and 66.7% with the adaptive tier off. `coverage --dynamic`
   now preserves adaptive choices from `-stats`; each of those four still needs
   to be re-read with that metadata (or a fixed tier) on a quiet machine with
   `bench.py ab` before any of them is called a regression: their
   `ValOp > [Val, Int]`, `ValOp \in`, `@@` and `DOMAIN` rows are the rows whose
   region-entry counts move by up to 3.7x on `standard-raft-Raft` while the
   evaluation count stays at 1,824,652.
2. **The `Dyn` value store is the largest remaining real win and it is a
   representation batch, not a lowering.** The unmeasured
   `ext/vanlightly-vsr/*` configurations are the largest interpreter-time
   carriers left in the selection, their cause is the boxed message bag, and the
   `TLX_VALUE_STORE` experiment measures the fix at 56.5% to 12.0% host time on
   `VSR` with identical results. Turning it on by default needs recycling and a
   checkpoint format; until then the store stays off and the family stays
   unmeasured here.
3. **Boxed `@@`, `DOMAIN` and guarded `EXCEPT` on `Dyn` are worth resuming only
   with a per-evaluation cost fix.** They are the third family by host time
   (17.534s) and their measured cost is one host callback per operation: the
   attempt that shipped them made the cold-region raft and etcd configurations
   slower while the hot ones got faster, and the cost tracked each region's
   average evaluation count, not the shape coverage.
4. **Do not dispatch on the small-search configurations.** Six of the fifteen
   configurations over the line total under 2 ms of interpreter time on
   searches of 101 to 2,743 evaluations (`ext/ccf/TraceMultiNodeReads_*`,
   `ext/pragmatic/specjuniorv1`, `ext/ccf/MCccfraft_1C2N`), and
   `ext/cassandra/Accord_baseline__two_lockers_live` is 6 ms on 30,092. Their
   share is a statement about a tiny denominator, and a lowering that removed
   their whole top operation would move the record's interpreter time by less
   than the run-to-run variation of one larger configuration. A minimum-search
   guard, or a column that reports the interpreter seconds next to the share, is
   what they need.
5. **What is left after that.** `Interp Quant` and `Exists [Val, Bool]`
   (19.136s, the largest family) are the remaining quantifier roots; the
   `Interp apply-def @line:col` and `Interp FnConstruct` rows (4.749s, all of
   it `ext/mongo/MCRaftMongoReplTimestamp`) are closures the tooling can now
   attribute to a source position, which is the IR-root inspection the
   `Temp`/`Var` family wanted. Both are worth a fresh census before a batch is
   sized, because neither is measurable in the same shape twice.

Dynamic sequences, FiniteSets/Bags and the boxed algebra families are below 1 s
each and should be dispatched only when executed sites in the complete evidence
justify a separate worker; no speedup is estimated from zero-call static
presence. Static-only and timed-out configurations are explicit coverage gaps,
not estimates of 100% native execution.

## Tracking contract

`bench.py track` records bounded `native_coverage` summaries in each model/mode/
worker history entry. A discarded synchronous preheat supplies the exact counts;
performance samples remain uninstrumented. A native-share drop greater than one
part per million is reported as `NATIVE COVERAGE REGRESSION`, independently of
wall-time noise; missing new evidence against a known baseline is inconclusive.
Host time share is retained for attribution. Coverage changes can reflect adaptive
path selection and do not alone establish a semantic error or performance loss.
