# Open issues

This document tracks unresolved work. Fixed defects are removed; their changes and regression
coverage remain in Git history and the relevant design and testing documentation. Documented
TLC compatibility differences are tracked in
[compat.md](compat.md#3-documented-differences).
[bench/README.md](../bench/README.md#frozen-snapshot-provenance) preserves the initial snapshot's
provenance and historical failures. Fixes and later validation do not rewrite that frozen baseline.

## Full-model validation and performance follow-up

The following checks remain open after the code fixes. Passing a regression test does not establish
completion or performance on the original benchmark configuration.

| Configuration | Remaining work |
|---|---|
| `ext/vanlightly-kafka/kafka_replication_v3_5`, compiled 16 workers and default one worker | Collect repeated same-instance before/after samples with explicit cache conditions. Investigate remaining layout migration and interpreted-region costs; compiler cancellation alone does not establish that the timeout problem is solved. |
| `bcastFolklore/bcastFolklore`, default one worker | Collect repeated cloud benchmark samples after hoisting suffix-invariant temporal conditions out of `<>`/`[]` and compacting product storage (local `-maxmem 2048 -stats` verification now completes with 5 tableau states, 655,360 product nodes, 6,483,968 product edges, 58.3 MiB CSR, 76.2 MiB largest product and 239.7 MiB peak RSS vs. the 16,845 MiB freeze failure). |

A [20-second Kafka prefix diagnostic](research/kafka-prefix.json) on Linux x86_64
(2026-11-24, `test-release`, original fetched config, `-compile -tlc -workers 1
-maxmem 512 -stats json=stats.json`, normal asynchronous native compilation,
SIGTERM with five seconds of grace) observed three layout misses, two completed
resumes and four model builds. Completed model-build timers accounted for 6.90 s;
completed re-encoding of 4,383 states accounted for 0.30 s. The signal arrived
during another restart, so that migration's unfinished work is not in these phase
totals. The partial snapshot retained 25,236 expansions and 1,802,965 host-region
calls (1.20 s of instrumented host time). The largest aggregated host rows were
`ReceiveBrokerRegResponse`'s `Var` (0.111 s), `ReceiveMetadataUpdate`'s boxed `>`
(0.107 s) and membership (0.099 s), and `SendAlterPartitionRequest`'s interpreted
record construction (0.088 s). Repeated model compilation was a substantial
observed cost, larger than all measured host-region work; no single host region
dominated. The incomplete migration timer prevents ranking total migration cost.
Adaptive metadata retained 93 worker/model/library observations: 15 last chose
mixed native, 16 fallback, and 62 were undecided. These are historical observations,
not 93 simultaneously active functions. The snapshot includes 62 optimized-slot
and 31 quick-slot rows; installed-model revisits reuse the same rows.

A preceding `coverage.py --dynamic` prefix with synchronous native compilation
spent its entire 20-second budget before search, after generating 9.1 MB of C.
Both runs now preserve `interrupted: true`; neither establishes a completed timing,
a full-run bottleneck, or a performance improvement. Timers overlap and partial
snapshots lag, so these numbers are not an additive wall-time breakdown. The machine
was shared and cache state uncontrolled (an optimized native cache hit was observed). Fetch with `scripts/fetch-external.py
--repos vanlightly-kafka`; the original module/config are under
`third_party/external/vanlightly-kafka/kafka_data_replication/kraft/v3.5/`.
Full-model repeated cloud measurements remain open.

Other long-running configurations still need completion or a documented resource bound:
`KeyValueStore/MCKVSSafetyLarge`, `TLC/TestMCReachability`, `byzpaxos/BPConProof`, `c1cs/c1cs`,
`dag-consensus/TLCSailfish2`, `detector_chan96/EnvironmentController`, `diskpaxos/MC_HDiskSynod`
and `ewd998/EWD998`. Several matching TLC runs also timed out; a timeout is not a completed timing.
The [frozen observations](../bench/README.md#timeout-observations-at-the-freeze-point) retain the
original limits and TLC results. Later successful runs, including extended retries, need review
before they become a new baseline.

## Enumeration resource limits

`SpanTreeTest5Nodes` no longer fails immediately on cardinality overflow, but reached the
600-second warm-up limit with no timed samples in the
[post-fix validation](research/post-fix-validation.md); its large `Init` enumeration still needs
optimization or a documented larger resource bound.

`CarTalkPuzzle/CarTalkPuzzle.toolbox/Model_3/MC` (`N = 121`, `P = 5`, `[1..5 -> 1..121]` =
25,937,424,601 functions) previously hit the 600-second warm-up limit in the same validation pass
(and timed out in TLC at 14,400 s / 1 worker and 1,800 s / 16 workers). After extending
`seqfilter` (bounded recursive unfolding, constant `LET`/`CHOOSE`, integer interval pruning with
binary range splitting, and small constant-domain quantifier unrolling) together with interpreter
bound caching, zero-allocation disjoint-intersection checks, and borrowed constant memo lookups,
local single-worker `test-release` verification now completes with the expected solution
`{<<1, 3, 9, 27, 81>>}` (0 states, 52.6 MiB peak RSS); repeated cloud benchmark samples remain
open.

## Measurement quality and high-speedup validation

Four frozen default-mode configurations have a sample range divided by the median above 25%:
`MultiCarElevator/ElevatorSafetyLarge`, `Prisoners_Single_Switch/PrisonerSolo`,
`SpecifyingSystems/AsynchronousInterface/AsynchInterface` and `barriers/Barrier`.
Keep their samples visible and repeat measurements before using them to establish small changes.

The [audit of ratios above 100x](research/speedup-audit.md) identifies further validation work:
repeated TLC measurements on the same instance, explicit cache conditions, comparable runs with
and without automatic reduction, and per-property correctness checks. The per-property check is now
automated: reduced probes in `tests/specs/` (`TP1`-`TP7`) make each temporal and refinement property
shape of the >100x cohort false one property at a time, and `cargo test` plus `scripts/spectest.py`
require `tlx` to report the named violation with a counterexample in default and `-tlc` modes, with
TLC confirming the property and validating the lasso. Matching counts and a log line announcing
liveness checking alone still do not prove that every configured property is correct; the probes
cover the cohort's shapes, not every configuration.
