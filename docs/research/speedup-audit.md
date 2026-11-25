# Auditing the published speedups above 100x

> [!NOTE]
> **Historical point-in-time audit record** — not an active normative specification. This document
> records an audit of the 2026-10-11 frozen initial benchmark store (`5dc582bde9`, collected on
> Tencent `SA5.4XLARGE32` x86_64 instances with local count/digest cross-checks). Current state
> reductions and certificate requirements on `main` are owned by [reductions.md](../reductions.md)
> and [optimization.md](../optimization.md) (benchmark reporting is owned by
> [benchmarking.md](../benchmarking.md) and [performance.md](../performance.md)). In particular,
> the pre-`v0.1.0` `proof: static` and `runtime guard` (`PaxosCommit`) symmetry mechanisms recorded
> in the frozen baseline were subsequently replaced on `main` by mandatory compiler-generated Lean
> certificates (`proof: "generated-lean"`).

Source identifiers below name reachable, source-equivalent commits in this history.
The original measurement and reproduction identifiers remain in the evidence files; [source-equivalents.toml](../../bench/environment/source-equivalents.toml)
maps those original identities to revisions with identical Rust/workspace inputs.
This source mapping does not claim that a historical measurement ran on a rewritten commit.

The frozen store's published table contains ratios far above the typical 5-10x
([performance.md](../performance.md)). This report audits the 13 configurations whose *paired*
tlx/TLC ratio the report publishes above 100x at the 2026-10-11 freeze, states which of them are
supported by evidence, and names the ones that are not what their number suggests. It does not
change the frozen baseline: it adds an inventory tool, a local reproduction method and this record.

## 0. Which rows are candidates

A ratio is published only for a stored tlx row that passes the report's `eligible` selection and
whose recorded TLC baseline matches it under `baselines.historical_match`
([benchmarking.md](../benchmarking.md) section 2 owns the store). Recomputing the candidates with a
different rule (pairing by model name, or taking every record) would treat excluded or incomplete
rows as claims the report never made. `benchmarking.speedup_audit` uses the same two functions:

```sh
PYTHONPATH=scripts python3 -m benchmarking.speedup_audit --threshold 100 --verify-digests
```

The command prints the table below; `--verify-digests` recomputes each candidate's input digest from
the resolved spec, configuration and module closure and compares it with both stored keys (requiring
the fetched corpus, external repositories and `third_party/community` modules from
`scripts/fetch-deps.sh` and `scripts/fetch-external.py` to match the baseline snapshot; missing
checkouts report `unresolved`, and drifted unpinned `community` modules report a digest mismatch).
At the 2026-10-11 freeze, all 13
digests recomputed **exactly** (tlx key and TLC key), so the two sides of every ratio were measured
on the same bytes. The 13 candidates reproduce the seed inventory in full; no row was added or lost.

## 1. Cross-cutting findings

**F1 - every denominator is one TLC sample.** The tlx side of all 13 rows has 3/3 complete samples
(`provenance.repetitions`), and the store keeps every raw sample and the discarded warm-up in
`raw_result`. The TLC side is one measurement per key: of the 470 TLC records in the current store,
470 are `aggregation: single-or-legacy-scalar` and only two record any repetition. A ratio built
from one sample has no noise bound: the denominator of the *ratio* is a point estimate on the
collecting instance (F6 records unexplained sample variation in the same batch).

**F2 - the timed tlx value is a warm-cache run; the TLC value is one process.** A measured tlx row is
the median of three timed runs that follow a discarded warm-up, and the warm-up runs with
`TLX_NATIVE_SYNC=1` so that it builds the native library synchronously and the timed runs find it in
the cache (`bench_suite.samples` in `scripts/benchmarking/bench_suite.py`). The store keeps that run
in `raw_result.warmups`; the report prints only the timed time. TLC's number is a single process that
includes JVM start-up, parsing and the model's compilation. The recorded warm-up is *not*, however,
a documented cold-cache measurement: the suite lane sets no `TLX_CACHE` (only the `ttfr` lane does,
and it defines `cold` as "one run with an empty TLX_CACHE", benchmarking.md section 1), so the cache
directory is whatever the batch inherited, it is shared by every configuration of that batch, and
the store records no cache state. The `Accord_baseline__deep_chain` rows show the reuse directly:
the `-compile` row's warm-up took 7.568 s (it built the library) and the default row's warm-up of the
same artifact took 1.285 s. The table below is therefore "the recorded warm-up", not a cold run, and
this audit derives no end-to-end ratio from it:

| candidate | timed tlx | recorded warm-up | warm-up / timed |
|---|---:|---:|---:|
| MultiCarElevator/ElevatorLivenessLarge | 0.712 | 3.637 | 5.1x |
| MultiCarElevator/ElevatorLivenessMedium | 0.165 | 1.045 | 6.3x |
| ext/cassandra/Accord_baseline__deep_chain (-compile) | 1.111 | 7.568 | 6.8x |
| bench/ReprRaftMongo | 0.491 | 1.898 | 3.9x |
| PaxosHowToWinATuringAward/MCPaxosSmall | 0.552 | 1.857 | 3.4x |
| ext/mongo/MCRaftMongo (all three rows) | 1.660-14.680 | 1.794-17.940 | 1.08-1.22x |
| bench/RaftMongoT4, byzpaxos/PConProof, MisraReachability/* | 0.096-9.779 | 0.207-11.811 | 1.2-2.8x |

Consequence for reading the table: the tlx side excludes the cost of a user's first run (build the
library, start the process), the TLC side includes its own start-up, and the section title "Default
mode end-to-end vs TLC" claims more than that for the fast rows, where the recorded warm-up is
3.4-6.8x the timed value. A cold-cache number for these configurations exists only in the `ttfr`
lane's protocol (a fresh `TLX_CACHE` per run); no such record is in this store. The generated report
now states these conditions in its own text - a timed tlx value is a separate process run after a
discarded warm-up whose cache may be reused, and the discarded run is not a cold-cache measurement -
without changing any published number.

**F3 - two rows compare different searches.** `MCPaxosSmall` (239x) and `PConProof` (181x) are
default-mode runs that applied tlx's automatic symmetry of sets of model values
([usage.md](../usage.md) section 6.3). Their recorded `Optimizations:` line says
`proven; safety checks only`, and the distinct counts the two sides publish differ by 10.8x and
10.6x (17,153 against TLC's 185,369 and 95,028 against 1,009,133). Re-running the *same
configurations* with `-tlc` (the tier-2 mode) reproduces TLC's distinct and generated counts
exactly, so the reduced search is a state-space reduction rather than a search that lost states:

| configuration | tlx default, distinct / generated | tlx `-tlc`, distinct / generated | TLC, distinct / generated |
|---|---:|---:|---:|
| PaxosHowToWinATuringAward/MCPaxosSmall | 17153 / 127002 | 185369 / 1361380 | 185369 / 1361380 |
| byzpaxos/PConProof | 95028 / 11676837 | 1009133 / 115774725 | 1009133 / 115774725 |

Only the counts are recorded here: the published TLC denominator was measured on the collecting
cloud instance and the `-tlc` re-runs this audit could produce ran on a different machine, so
dividing them would mix machines. A like-for-like timing ratio needs both sides measured on one
instance (section 3), and this audit does not quote one.

The reduction itself checks out. On the frozen pre-`v0.1.0` revision, `-stats json` reported `proof: static`, `scope: safety`, `preserved: [V-safe, CEX, D, L]`
for the applied group (subsequently replaced on `main` by mandatory connected Lean certificates with `proof: "generated-lean"`, see [reductions.md](../reductions.md)); the bounded cross-check finds no violation in 1000 states at depth 7 for
each candidate set; and a compatible-mode run with the equivalent declared
`SYMMETRY Perms == Permutations(Acceptor) \cup Permutations(Value)` reproduces the same 17153
distinct states, which is the documented identity ("the state counts ... equal TLC's counts with the
corresponding SYMMETRY added to the cfg"). Their properties are checked: the configured PROPERTY of
`MCPaxosSmall` is `V!Spec` (`Voting!Spec == Init /\ [][Next]_<<votes, maxBal>>`, a safety shape), which
tlx decomposes into a per-step action property exactly as TLC's `processConfigProps` does, and a
falsified copy of that property in the same configuration is reported
(`Error: Action property prop_... is violated.`) in both modes.

The policy that lets a default-mode row pair with an unreduced TLC baseline is written down (the
report header exempts "distinct count outside default mode") and the report prints the distinct
counts next to the ratio, so a reader who knows the rule can see it. The label this audit found
missing is now in the generator: `benchmarking.bench_records.render` reads the optimization line out
of each record's own samples - never out of a count difference, which the default-mode contract
permits for reasons the record does not state - and emits a `tlx optimizations` column on every
measured row: `none` only when every recorded sample states an empty list, `unknown` when the record
does not state it for every sample (the older compatible rows are exactly that shape), and a
`Models with recorded optimizations` count in the summary. 39 published rows in the store carry one,
among them
`ElevatorSafetyLarge` (published at 22.72x, below this audit's threshold) with
`symmetry Permutations(Person)`: 10,365,445 reduced distinct states against TLC's 59,007,145.
The column states the tlx side's record, not what the TLC baseline was configured with: a TLC
baseline may declare `SYMMETRY` itself, so "the two sides explored different state spaces" is a
separate claim that needs its own evidence. For the two candidates above that evidence exists in
their configurations, which declare no `SYMMETRY` (checked in `MCPaxosSmall.cfg` and
`PConProof.cfg`), together with the `-tlc` re-runs matching TLC's counts.
The same store shows why a count difference cannot stand in for that line: two published rows have
different distinct counts on the two sides and name no optimization, and both have an innocent
reason - `ext/vanlightly-raft/pull-raft-KRaft -compile` stops at a deadlock, where the count is
whatever the exploration order reached first, and `SpanningTree/SpanTreeRandom` checks a temporal
property, which TLC may stop early on a periodic check.

**F4 - the checks that must hold, hold.** For all 13 rows: input digest recomputed equal on both
sides; worker count, instance type, architecture and `cgroup_mib` equal; TLC version equal; verdict
`success` on both sides; `generated`, `distinct` and `depth` equal in 11 of 13 rows (the two
reductions above are the exceptions, and both re-check equal under `-tlc`). Mode contract: the four
`-tlc`/compatible rows (`MCRaftMongo` x2, `bench/ReprRaftMongo`, and the local `-tlc` re-runs of the
reduction cases) satisfy tier 2 exactly, including distinct counts. The local re-runs of every
candidate reproduced the stored counts, verdicts and digests, but they were run against the frozen
measurements' original Rust source, now represented by `5dc582bde98a677524032753f133dc3692cd2e15`, whose `crates/` tree is
`90c32255b973c17ea2a12c3b94feadff3f3c3d5b` - the tree [baseline provenance](../../bench/README.md#frozen-snapshot-provenance) records for the
original measurement inputs - and not against the Rust fixes main has gained since. Those runs
say nothing about how the fixes change any timing; the cloud benchmark of the fixed revision is a
separate measurement.

**F5 - no evidence of the checks being skipped wholesale; per-property correctness stays open.** The
suspicion this audit was asked to test is that a large ratio comes from tlx silently dropping
liveness. The records below show no sign of a configuration-wide skip. They do not prove that every
configured property is translated and checked with the right semantics - a phase line and a branch
count say that the liveness phase ran, not that each property in it is correct:

* The default-mode run of `ElevatorLivenessLarge` prints `Checking 8 branches of temporal
  properties for the complete state space with 405224 total distinct states` and
  `Finished checking temporal properties in 00s`; `ElevatorLivenessMedium` prints 6 branches,
  `bench/RaftMongoT4` and the two `MCRaftMongo` rows 9 branches each, `MCReachable`/`MCParReach` one
  branch each (`Termination`, `Refines`). The branch count is the tableau size and the run says when
  it checked it, which is what the printed size is evidence for.
* The store itself contains three default-mode rows whose verdict is `liveness failure`
  (`FiniteMonotonic/MCDistributedReplicatedLog`, `SpecifyingSystems/RealTime/MCRealTimeHourClock`,
  `bench/ClockSettles`), so the default mode reports temporal violations at all.
* Where a temporal property is checked, tlx refuses the automatic symmetry and says so: the `-tlc`
  runs of `MCReachable`/`MCParReach` print
  `Symmetry: ... is provable for safety checking and not declared (not for the temporal properties
  this run checks: under SYMMETRY, TLC can miss or invent their violations).`
* The tlx time is search time, not hidden compile time: for `ElevatorLivenessLarge` the recorded
  coverage census gives `search_thread_s_est` 0.785 s against a 0.712 s wall; the compile is in the
  discarded 3.637 s warm-up (F2, which also says why that run is not called cold).
* Nothing was terminated early: every candidate's verdict is `success`, `0 states left on queue`,
  and no `count_problems` entry.

What would close the remaining gap: a probe per property shape that makes each configured property
false and checks that the violation is reported (this audit ran such probes for the `[]`-shaped
`V!Spec` of `MCPaxosSmall` and, in a follow-up diagnostic, for all three conjuncts of
`MCParReach`'s `Refines == R!Spec` — `R!Init`, `[][R!Next]_R!vars`, and `WF_R!vars(R!Next)` — all
detected in both `default` and `-tlc` modes, matching TLC), or validating each liveness
counterexample against TLC. All 13 rows expect `success`, so a dropped or mistranslated property
would not show up in their verdicts.

**F6 - unexplained sample variation in the batch.** [issues.md](../issues.md) lists four
default-mode rows whose sample range over the median exceeds 25%. Their raw samples classify as
follows (`warmups` is the recorded warm-up):

| row | samples (wall s) | noise | median vs min | reading |
|---|---|---:|---:|---|
| SpecifyingSystems/AsynchronousInterface/AsynchInterface | 0.055, 0.039, 0.040 | 41% | +2.5% | 40 ms process; one delayed first sample |
| barriers/Barrier | 0.052, 0.041, 0.040 | 30% | +2.5% | same, at recorded load 1.02 |
| Prisoners_Single_Switch/PrisonerSolo | 0.053, 0.042, 0.042 | 26% | 0% | same, at recorded load 1.21 |
| MultiCarElevator/ElevatorSafetyLarge | 99.255, 129.140, 98.571 | 31% | +0.7% | 100 s run; one sample 30% slow, warm-up 114 s, recorded load 1.0 |

The three sub-100 ms rows are a measurement-floor effect (a single scheduling delay inflates the
range while the median is unaffected): their published ratios are 9.6-10.3x, not candidates here. The
fourth is different in kind - a long run with one sample 30% slower than the other two, at a recorded
load the collector did not flag. Its published ratio uses the median (99.255 s, within 0.7% of the
minimum), so its own headline is not distorted. The variation is *not* explained by the recorded
evidence, and machine contention is only one possible cause among others (a neighbouring tenant whose
load the average did not capture, CPU frequency or memory behaviour, or the process's own
variability); the load figures cannot separate them. It is a reason to want a repeat before quoting a
denominator built from one process, not proof that the machine was contended. With F1 this is the
largest unexplained uncertainty in the biggest numbers.

## 2. Per-case evidence and status

Statuses: **supported** - the ratio is a real end-to-end comparison of the same task, with the
caveats named; **policy-shaped** - the ratio is correct under the documented default-mode rule but is
not an engine-speed comparison; **pending** - the recorded evidence is consistent but one bounded
experiment is needed to name the cause. F1 (one TLC sample per denominator) applies to all 13 rows
and is not repeated in the column.

Every candidate was re-run locally with a release binary using the original baseline Rust source (now represented by `5dc582bde98a677524032753f133dc3692cd2e15`), the base revision
the frozen measurements were taken on (F4 carries the tree identity), using the suite's own argument
construction (worker count, tier flag, `-tlc`), each configuration at least twice in one sequence so
that its first run paid the compile and the later ones ran from the cache. The table's counts,
verdicts and content digests are what the *stored* rows say; the runs audit the frozen records, not
the fixes main has gained since:

| configuration (mode) | reproduced distinct / generated / depth | reproduced result | digest |
|---|---|---|---|
| ElevatorLivenessLarge (default) | 50653 / 230899 / 39 | success | verified |
| MCReachable (default, `-tlc`) | 8 / 11 / 6 | success | verified |
| RaftMongoT4 (`-compile` 16w) | 1572408 / 21924604 / 29 | success | verified |
| MCRaftMongo (default 1w, `-compile -tlc` 1w, `-compile -tlc` 16w) | 371368 / 5398516 / 21 | success | verified |
| MCPaxosSmall (default, `-tlc`) | 17153 / 127002 / 25 and 185369 / 1361380 / 25 | success | verified |
| PConProof (default, `-tlc`) | 95028 / 11676837 / 28 and 1009133 / 115774725 / 28 | success | verified |
| Accord_baseline__deep_chain (default, `-compile`) | 179712 / 214191 / 9 | success | verified |
| ReprRaftMongo (`-compile -tlc`) | 12003 / 166069 / 16 | success | verified |
| MCParReach (default, `-tlc`) | 393 / 747 / 18 | success | verified |
| ElevatorLivenessMedium (default) | 4122 / 14296 / 36 | success | verified |

The reproduction used the corpus inputs resolved by `benchmarking.models`/`corpus`, not the digest
recorded in the store, so the digests above are recomputed independently (F4) and not copied. The
local times of those runs are kept in the diagnostic artifacts but are not quoted here: they come
from a different machine than every TLC baseline in the store, and no ratio may be formed from them.

| # | configuration | ratio | tlx timed / recorded warm-up s | TLC s | distinct tlx / TLC | recorded optimizations (tlx) | status |
|---:|---|---:|---:|---:|---:|---|---|
| 1 | MultiCarElevator/ElevatorLivenessLarge default 1w | 2090.54x | 0.712 / 3.637 | 1488.466 | 50653 / 50653 | none | supported (F2) |
| 2 | MisraReachability/MCReachable default 1w | 790.16x | 0.096 / 0.207 | 75.855 | 8 / 8 | none | supported (phase attributed, 2.2) |
| 3 | bench/RaftMongoT4 -compile 16w | 310.09x | 6.603 / 8.781 | 2047.532 | 1572408 / 1572408 | none | supported |
| 4 | ext/mongo/MCRaftMongo -compile 16w -tlc | 270.96x | 1.660 / 1.794 | 449.796 | 371368 / 371368 | unknown | supported |
| 5 | ext/mongo/MCRaftMongo default 1w | 242.17x | 14.665 / 16.337 | 3551.468 | 371368 / 371368 | none | supported (shared denominator with #6) |
| 6 | ext/mongo/MCRaftMongo -compile 1w -tlc | 241.93x | 14.680 / 17.940 | 3551.468 | 371368 / 371368 | unknown | supported (duplicate of #5) |
| 7 | PaxosHowToWinATuringAward/MCPaxosSmall default 1w | 238.97x | 0.552 / 1.857 | 131.910 | 17153 / 185369 | symmetry Permutations(Acceptor) x Permutations(Value) (proven; safety checks only) | policy-shaped (F3) |
| 8 | byzpaxos/PConProof default 1w | 180.89x | 9.779 / 11.811 | 1768.963 | 95028 / 1009133 | symmetry Permutations(Value) x Permutations(Acceptor) (proven; safety checks only) | policy-shaped (F3) |
| 9 | ext/cassandra/Accord_baseline__deep_chain -compile 1w | 146.60x | 1.111 / 7.568 | 162.878 | 179712 / 179712 | none | supported (F2) |
| 10 | ext/cassandra/Accord_baseline__deep_chain default 1w | 146.21x | 1.114 / 1.285 | 162.878 | 179712 / 179712 | none | supported (duplicate of #9) |
| 11 | bench/ReprRaftMongo -compile 1w -tlc | 132.22x | 0.491 / 1.898 | 64.921 | 12003 / 12003 | unknown | supported (F2) |
| 12 | MisraReachability/MCParReach default 1w | 111.74x | 0.109 / 0.310 | 12.180 | 393 / 393 | none | supported (phase attributed, 2.2) |
| 13 | MultiCarElevator/ElevatorLivenessMedium default 1w | 109.12x | 0.165 / 1.045 | 18.005 | 4122 / 4122 | none | supported (F2) |

The `recorded optimizations (tlx)` column is the record's own statement, byte for byte the cell the
generated report shows (`docs/performance.md`), and never an inference from the counts: only rows 7
and 8 of these 13 ran with the automatic reduction (tlx's proven symmetry of sets of model values,
[usage.md](../usage.md) sections 6.2-6.3), which is what makes their ratio compare a reduced tlx
search with TLC's unreduced one. The three `unknown` rows were recorded without the per-sample
field; they are `-tlc` runs, and `-tlc` never applies the automatic reduction, so their own mode
already excludes it - the record simply does not state the optimization list. 39 of the store's 262
published rows carry a recorded optimization; the appendix lists them.

Records: the tlx row and its TLC baseline for each case are the files named in the report's Evidence
column; the inventory JSON emits both paths per row. Every row above also carries the raw samples and
the discarded warm-up in its `raw_result`, so F1/F2 are checkable from the store alone.

### 2.1 The liveness rows (1, 3-6, 13)

The candidate's own evidence says the configured property was checked (F5). The TLC side of the
ratio is dominated by TLC's own liveness machinery, not by search, and the store shows it without a
new experiment:

* `ElevatorLivenessLarge`: TLC took 1488.466 s for 50,653 distinct states (29 ms/state, 6.9 GiB RSS)
  while the sibling safety configuration `ElevatorSafetyLarge` took 2254.915 s for 59,007,145
  distinct states (38 us/state, 6.1 GiB) on the same instance type - a 770x difference in state rate
  and 1300x in bytes per state on the same spec.
* `ElevatorLivenessMedium`: 18.005 s for 4,122 states (4.4 ms/state), again against the same
  safety sibling's 38 us/state.
* `bench/RaftMongoT4` and `ext/mongo/MCRaftMongo`: nine leads-to properties under strong fairness;
  TLC's 16-worker baseline spends 26,201 CPU-seconds (12.8 cores busy) on 1.57M distinct states,
  16.7 ms of CPU per distinct state against 38 us per state on the safety sibling above.

Caveat: each comparison above is between two TLC records of the same instance type (except the
manifest line below), and the paired configurations differ in constants, so the rate difference is
an indication of which phase dominates rather than a controlled experiment. The ratio also mixes two
different liveness designs (TLC's in-search tableau against tlx's offline check after the search)
with two different parallel strategies, so it is not a per-state engine ratio, and it is a cloud
record on one instance class. The manifest's own `runtime` for `ElevatorLivenessLarge` is 11 minutes
while the baseline took 24.8 minutes; this audit does not recompute a ratio from the manifest's
number, and records only that the published size depends on the TLC machine.

### 2.2 The MisraReachability rows (2, 12)

`MCReachable` is 8 distinct states and 11 edges; `MCParReach` is 393 and 747. Their TLC times
(75.855 s and 12.180 s) are 9.5 s and 31 ms *per distinct state*. Both configurations are ordinary
safety-sized models whose cost in TLC is serial, which the store shows directly:

* The same keys at 16 workers are **slower** than at one worker: `MCReachable` takes 102.672 s
  against 75.855 s (`cpu_s / wall_s` = 1.19, about one core busy), and `MCParReach` takes
  41.972 s against 12.180 s (`cpu_s / wall_s` = 1.72), where `MCBoulanger` (243.75 s -> 29.588 s)
  and `MCRaftMongo` (3551.468 s -> 449.796 s) use 12.6-14.0 cores at the same worker count. TLC
  gains nothing from 16 workers on either model, so its time is not search parallelism.
* The tlx side of the comparison is search: the census recorded with `MCReachable` reports 84
  evaluations and 0.0145 s of estimated search-thread time over the same 8 states (recorded warm-up
  0.207 s against 0.096 s timed), and `MCParReach`'s recorded census reports 6,949 evaluations and
  0.004383 s of estimated search-thread time over the same 393 states (recorded warm-up 0.310 s
  against 0.109 s timed).
* The configurations are the unusual part: `Succ <- ConnectedToSomeButNotAll` substitutes a
  `CHOOSE succ \in [Nodes -> SUBSET Nodes] : ...` over a 65536-function space, and
  `Seq <- LimitedSeq` bounds `Seq(Nodes)` for `ExistsPath`; four of `MCReachable`'s invariants
  (`Inv2`, `Inv3`, `PartialCorrectness` through `Reachable = ReachableFrom({Root})`) consume them on
  every evaluation.

The store keeps normalized baselines, not TLC's stdout, and the collecting history file
`bench/history/tlc-1813307-SA5.4XLARGE32.json` named by their provenance is not in the published tree
(the raw runner histories live under the maintainer's `work/` archive). The phase attribution was
therefore run directly, as two serial diagnostics with TLC's stdout kept (one JVM at a time,
`-Xmx4g`, 180 s cap; approved as a diagnostic, not a measurement):

```sh
PYTHONPATH=scripts python3 scripts/tlc.py third_party/Examples/specifications/MisraReachability/MCReachable.tla -config third_party/Examples/specifications/MisraReachability/MCReachable.cfg -workers 1 --allow-local-heavy
```

The original configuration (55.876 s wall) spends its time in the search, not after it: TLC reports
`Finished computing initial states` after 6 s, then 3 s to reach 2 states, then 47 s for the
remaining 9 states, and its `Finished in 55s` timestamp is the same second as the last progress
report, so the post-search temporal-property check is under a second of the total. The reduced copy
- same spec, same constants, `INVARIANTS TypeOK` only and no `PROPERTY` - finished the same 8
distinct states and depth 6 in 3.124 s. Removing the four `ReachableFrom`-based invariants therefore
removed ~53 s of the 55.9 s, and the properties were not the cost. Together with the single-core
profile above, the record's 75.855 s is per-state evaluation of those invariants (`Reachable`,
`ExistsPath` over the configured `Seq`, and the `Succ` substitution), not search parallelism and not
the liveness tableau.

Two limits on that reading: the diagnostic ran on a local workstation, not on the collecting cloud
instance, so it attributes *phases* and does not re-measure the published `2026-10-11` number; and
the reduced `MCReachable` run drops the `PROPERTY` as well as the invariants, so it bounds the
invariants' share from below (the original log's own timestamps place the property check under a
second).

A follow-up bounded serial diagnostic on `MCParReach` (same single-JVM `-workers 1` methodology via
`scripts/tlc.py ... --allow-local-heavy` on a Linux x86_64 workstation — attributing phases only,
with no cross-machine ratio against the `2026-10-11` `SA5.4XLARGE32` cloud record) records each
configuration's phase split on the same 393 distinct / 747 generated / depth-18 state space:

| `MCParReach` diagnostic variant (workstation, TLC `-workers 1`) | wall s | startup/init | search | post-search temporal |
|---|---:|---:|---:|---:|
| Original `MCParReach.cfg` (`INVARIANT Inv`, `PROPERTY Refines`, `SPECIFICATION Spec`) | 21.884 | ~5 s | ~15 s | < 1 s (`00s`) |
| `PROPERTY Refines` only (dropping `INVARIANT Inv`) | 22.339 | ~5 s | ~16 s | < 1 s (`00s`) |
| `INVARIANT Inv` only (dropping `PROPERTY Refines`) | 7.389 | ~4 s | ~3 s | n/a |
| `INVARIANT Inv` + safety-only `R!Init /\ [][R!Next]_R!vars` (no `WF_R!vars(R!Next)`) | 11.808 | ~7 s | ~4 s | n/a |
| Pure search (`INIT Init`, `NEXT Next`, no invariant or property) | 8.521 | ~5 s | ~3 s | n/a |
| Full `Inv` + `Refines` with `Succ <- FixedSucc` control (same 2-successor outdegree) | 1.679 | ~1 s | < 1 s | < 1 s (`00s`) |

Unlike `MCReachable` (where `ReachableFrom`-based invariants dominate), `ParReach!Inv` does not
reference `Succ` or `Reachable` and adds no measurable cost (`22.339 s` without `Inv` vs.
`21.884 s` with it). `Refines == R!Spec` (`R!Init /\ [][R!Next]_R!vars /\ WF_R!vars(R!Next)`) is
the expensive part: the full property raises the run from `7.389 s` (`INVARIANT Inv` alone) to
`21.884 s`, a `14.495 s` difference between configurations. It arrives in two whole-run steps, and
the wall-time gaps do not split them into phases — the timestamp columns do:

* Adding the safety conjuncts `R!Init /\ [][R!Next]_R!vars` to `INVARIANT Inv` increases wall time
  by `4.419 s` (`7.389 s` -> `11.808 s`), of which roughly `3 s` accrues in startup/init
  (`~4 s` -> `~7 s`) and only about `1 s` in search (`~3 s` -> `~4 s`). The `4.419 s` is therefore
  not the per-step cost of the action property.
* Adding `WF_R!vars(R!Next)` on top increases wall time by a further `10.076 s`
  (`11.808 s` -> `21.884 s`), which the timestamps place almost entirely in search
  (`~4 s` -> `~15 s`). That run also enables TLC's temporal graph and evaluates the concrete
  specification's per-process fairness conditions alongside the abstract fairness obligation, so
  the `10.076 s` is an end-to-end difference, not a measurement of the abstract obligation alone.

The post-search temporal check itself finishes in `00s` (< 1 s) in both property runs. Replacing
`Succ <- ConnectedToSomeButNotAll` with a direct 2-successor constant function
(`FixedSucc == [n \in Nodes |-> {Root, SecondNode}]`, producing the same 393/747/depth-18 state
space) drops total TLC runtime from `21.884 s` to `1.679 s` (startup/init `~5 s` -> `~1 s`), so the
substitution dominates the run as a whole. Its consumers are startup `ASSUME SuccAssump`, `Next`
(`b(self)`), and in-search evaluation of `R!Next` inside `PROPERTY Refines`; the run-level
`FixedSucc` comparison establishes their combined cost, not the share of each call site.

Cross-checking `tlx` (`default` and `-tlc`) on `MCParReach` reproduces `393` distinct / `747`
generated / depth `18`, and falsifying each conjunct of `Refines == R!Spec` — `R!Init`,
`[][R!Next]_R!vars` (via `RBad!Spec` with `vrootBad == IF marked = {} THEN vrootBar ELSE {}`), and
`WF_R!vars(R!Next)` (checking unmodified `Refines` against `SpecNoFair == Init /\ [][Next]_vars`) —
is detected in both `default` and `-tlc` modes with exact TLC parity (exit 13: init property
violation, action property violation at `Reachable` line 109 with trace length 3, and
`Temporal property Refines was violated`). The *ratios* on both `MisraReachability` rows are real
end-to-end differences on the collecting instance; what is now established is that TLC spends its
time on repeated constant-heavy `Succ`/`ReachableFrom` evaluation (in `MCReachable`'s invariants
and in `MCParReach`'s `ASSUME`/`Next`/in-search `R!Spec` evaluation).

## 3. Proposed bounded repeat protocol

To replace the single-sample denominators and the unrecorded cache state with a defensible number,
for this 13-row set only (bounded by construction: the whole set costs TLC ~2.7 hours of CPU-serial
time at the recorded times, and most of it is dominated by four rows):

1. One isolated instance per run, no other measurement on it, `load` recorded before and after each
   sample (F6 shows the recorded load did not flag a 30% excursion, so it is evidence, not proof).
2. Three TLC samples per key, interleaved with three tlx samples of the same configuration, and
   report the median *and* the range/median; a ratio is quoted only with its TLC range. `bench.py ab`
   already interleaves A/B; the TLC side needs the same treatment instead of one cached process per
   key.
3. For every default-mode row, a companion `-tlc` run of the same configuration *on the same
   instance*, so each reduced row has a like-for-like twin that may be divided (F3). Numbers from
   different machines are not quotable.
4. Make the cache state part of the measurement, not an assumption: either run the reported row with
   a fresh `TLX_CACHE` (the `ttfr` lane's own definition of `cold`) or record that the warm-up found
   a filled cache, and name the table column accordingly (F2).
5. For the liveness rows, keep the branch count and the property names next to the time (F5), and
   record TLC's phase split for at least the two `MisraReachability` configurations.

## 4. What this audit does not claim

* It does not claim any of the 13 rows has a wrong verdict, a wrong state count under its mode
  contract, or a wrong input digest: those all check out, including the two reduced searches, which
  match TLC exactly under `-tlc`.
* It does not claim the reductions are unsound: in the frozen baseline their proof was static, documented, cross-checked in
  bounds and reproducible as declared `SYMMETRY` (and on `main` every applied reduction now requires a connected compiler-generated Lean certificate, `proof: "generated-lean"`).
* It does not claim the large ratios are fabricated. `ElevatorLivenessLarge`, `RaftMongoT4`,
  `MCRaftMongo` and `Accord` are genuine end-to-end differences on the same inputs and counts
  (`MCReachable` and `MCParReach` too, now that their TLC phases are attributed).
* It does claim that the six rows whose recorded warm-up is 3.4-6.8x the timed value and the two
  reduction rows are not yet evidence for the *size* of the number they publish, and that the
  missing TLC repeats (F1) and the unverified per-property correctness (F5) are the two items to
  fix first.

## Appendix: published rows whose records name an optimization

Every row the generated report publishes carries a `tlx optimizations` cell; these are the 39 rows
whose recorded samples name one in the 2026-10-11 frozen baseline (the pre-`v0.1.0` `proven` static groups, or the pre-`v0.1.0` `runtime guard` group of `transaction_commit/PaxosCommit`; both were subsequently replaced on `main` by mandatory connected Lean certificates, `proof: "generated-lean"`, per [reductions.md](../reductions.md)). The list is
produced from the store with the report's own selection, so it is the annotation the report shows,
not a second inference. Each row's record file is the one named in the report's Evidence column.

| Model | Mode | Workers | Recorded optimization |
|---|---|---:|---|
| CigaretteSmokers/CigaretteSmokers | default | 1 | symmetry Permutations(Ingredients) (proven; safety checks only) |
| Disruptor/MCDisruptor_MPMC | default | 1 | symmetry Permutations(Writers) x Permutations(Readers) (proven; safety checks only) |
| KeyValueStore/MCKVSSafetySmall | -compile | 1 | symmetry Permutations(Key) x Permutations(Val) x Permutations(TxId) (proven; safety checks only) |
| KeyValueStore/MCKVSSafetySmall | -compile | 16 | symmetry Permutations(Key) x Permutations(Val) x Permutations(TxId) (proven; safety checks only) |
| KeyValueStore/MCKVSSafetySmall | default | 1 | symmetry Permutations(Key) x Permutations(Val) x Permutations(TxId) (proven; safety checks only) |
| MissionariesAndCannibals/MissionariesAndCannibals | default | 1 | symmetry Permutations(Missionaries) x Permutations(Cannibals) (proven; safety checks only) |
| MultiCarElevator/ElevatorSafetyLarge | default | 1 | symmetry Permutations(Person) (proven; safety checks only) |
| MultiCarElevator/ElevatorSafetyMedium | default | 1 | symmetry Permutations(Person) (proven; safety checks only) |
| MultiCarElevator/ElevatorSafetySmall | default | 1 | symmetry Permutations(Person) (proven; safety checks only) |
| PaxosHowToWinATuringAward/MCConsensus | default | 1 | symmetry Permutations(Value) (proven; safety checks only) |
| PaxosHowToWinATuringAward/MCPaxosSmall | default | 1 | symmetry Permutations(Acceptor) x Permutations(Value) (proven; safety checks only) |
| PaxosHowToWinATuringAward/MCPaxosTiny | default | 1 | symmetry Permutations(Acceptor) x Permutations(Value) (proven; safety checks only) |
| PaxosHowToWinATuringAward/MCVoting | default | 1 | symmetry Permutations(Acceptor) x Permutations(Value) (proven; safety checks only) |
| SpecifyingSystems/AsynchronousInterface/AsynchInterface | default | 1 | symmetry Permutations(Data) (proven; safety checks only) |
| SpecifyingSystems/AsynchronousInterface/Channel | default | 1 | symmetry Permutations(Data) (proven; safety checks only) |
| SpecifyingSystems/CachingMemory/MCInternalMemory | default | 1 | symmetry Permutations(Adr) x Permutations(Val) (proven; safety checks only) |
| SpecifyingSystems/CachingMemory/MCWriteThroughCache | default | 1 | symmetry Permutations(Val) (proven; safety checks only) |
| SpecifyingSystems/FIFO/MCInnerFIFO | default | 1 | symmetry Permutations(Message) (proven; safety checks only) |
| SpecifyingSystems/TLC/ABCorrectness | default | 1 | symmetry Permutations(Data) (proven; safety checks only) |
| acp/ACP_NB_WRONG_TLC | default | 1 | symmetry Permutations(participants) (proven; safety checks only) |
| acp/ACP_SB_TLC | default | 1 | symmetry Permutations(participants) (proven; safety checks only) |
| btree/MCbtree | -compile | 1 | symmetry Permutations(Vals) (proven; safety checks only) |
| btree/MCbtree | -compile | 16 | symmetry Permutations(Vals) (proven; safety checks only) |
| btree/MCbtree | default | 1 | symmetry Permutations(Vals) (proven; safety checks only) |
| btree/kvstore | default | 1 | symmetry Permutations(Vals) (proven; safety checks only) |
| byihive/VoucherCancel | default | 1 | symmetry Permutations(V) x Permutations(H) x Permutations(I) (proven; safety checks only) |
| byihive/VoucherIssue | default | 1 | symmetry Permutations(V) x Permutations(H) x Permutations(I) (proven; safety checks only) |
| byihive/VoucherLifeCycle | default | 1 | symmetry Permutations(V) (proven; safety checks only) |
| byihive/VoucherRedeem | default | 1 | symmetry Permutations(V) x Permutations(H) x Permutations(C) (proven; safety checks only) |
| byihive/VoucherTransfer | default | 1 | symmetry Permutations(V) x Permutations(SH) x Permutations(DH) (proven; safety checks only) |
| byzpaxos/PConProof | default | 1 | symmetry Permutations(Value) x Permutations(Acceptor) (proven; safety checks only) |
| byzpaxos/VoteProof | default | 1 | symmetry Permutations(Value) x Permutations(Acceptor) (proven; safety checks only) |
| dijkstra-mutex/DijkstraMutex.toolbox/Safety-4-processors/MC | default | 1 | symmetry Permutations(Proc) (proven; safety checks only) |
| transaction_commit/2PCwithBTM | default | 1 | symmetry Permutations(RM) (proven; safety checks only) |
| transaction_commit/PaxosCommit | -compile | 1 | symmetry Permutations(RM) x Permutations(Acceptor) (runtime guard; safety checks only) |
| transaction_commit/PaxosCommit | -compile | 16 | symmetry Permutations(RM) x Permutations(Acceptor) (runtime guard; safety checks only) |
| transaction_commit/PaxosCommit | default | 1 | symmetry Permutations(RM) x Permutations(Acceptor) (runtime guard; safety checks only) |
| transaction_commit/TCommit | default | 1 | symmetry Permutations(RM) (proven; safety checks only) |
| transaction_commit/TwoPhase | default | 1 | symmetry Permutations(RM) (proven; safety checks only) |

The other 223 published rows are `none` (every recorded sample states an empty list) or `unknown`
(40 rows recorded without the field, mostly the older compatible samples). A row says nothing about
its TLC baseline: a TLC baseline may declare its own `SYMMETRY`, so this table labels the tlx side's
search and not the difference between the two sides.
