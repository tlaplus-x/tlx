# Open issues

This document tracks unresolved work. Fixed defects are removed; their changes and regression
coverage remain in Git history and the relevant design and testing documentation. Documented
TLC compatibility differences and the open compiled-tier function-domain representation bug
(`D-13`, including empty enumerated functions in `tests/fuzz/specs/FzEmptyFcnExcept` and the
planned cutover in [value-store.md](value-store.md) section 8) are tracked in
[compat.md](compat.md#3-documented-differences).
[bench/README.md](../bench/README.md#frozen-snapshot-provenance) preserves the initial snapshot's
provenance and historical failures. Fixes and later validation do not rewrite that frozen baseline.

## Compiled function-domain representation (`D-13`)

In the compiled tier's fixed encodings (`Shape::Fcn` / `Map`), decoding does not record whether a
function's domain was built from an interval/tuple or from an enumerated set (`[k \in {0, 1} |-> e]`,
`[i \in {} |-> e]`), so an out-of-domain non-integer `EXCEPT` key raises a type error instead of
leaving the function unchanged as TLC and `-interp` do (for example
`tests/fuzz/specs/FzEmptyFcnExcept`). Store-backed `Ref` slots (`TLX_VALUE_STORE`) preserve the
construction witness; full details and reproduction cases live in [compat.md](compat.md) `D-13`
and [value-store.md](value-store.md) section 8.

## Full-model validation and performance follow-up

The following checks remain open after the code fixes. Passing a regression test does not establish
completion or performance on the original benchmark configuration.

| Configuration | Remaining work |
|---|---|
| `ext/vanlightly-kafka/kafka_replication_v3_5`, compiled 16 workers and default one worker | Collect repeated same-instance before/after samples with explicit cache conditions. Investigate remaining layout migration and interpreted-region costs; compiler cancellation alone does not establish that the timeout problem is solved. |
| `bcastFolklore/bcastFolklore`, default one worker | Collect repeated cloud benchmark samples after hoisting suffix-invariant temporal conditions out of `<>`/`[]` and compacting product storage (local `-maxmem 2048 -stats` verification now completes with 5 tableau states, 655,360 product nodes, 6,483,968 product edges, 58.3 MiB CSR, 76.2 MiB largest product and 239.7 MiB peak RSS vs. the 16,845 MiB freeze failure). |

Other long-running configurations still need completion or a documented resource bound:
`KeyValueStore/MCKVSSafetyLarge`, `TLC/TestMCReachability`, `byzpaxos/BPConProof`, `c1cs/c1cs`,
`dag-consensus/TLCSailfish2`, `detector_chan96/EnvironmentController`, `diskpaxos/MC_HDiskSynod`
and `ewd998/EWD998`. Several matching TLC runs also timed out; a timeout is not a completed timing.
The [frozen observations](../bench/README.md#timeout-observations-at-the-freeze-point) retain the
original limits and TLC results. Later successful runs, including extended retries, need review
before they become a new baseline.

## Enumeration resource limits

CarTalkPuzzle Model_3 and SpanTreeTest5Nodes no longer fail immediately on cardinality overflow,
but both reached the 600-second warm-up limit with no timed samples in the
[post-fix validation](research/post-fix-validation.md). Their large enumerations still
need optimization or a documented larger resource bound; neither is a completed timing.

## Incomplete upstream EWD998 examples

The upstream examples `ewd998/EWD998ChanID_export` and `ewd998/EWD998ChanID_shiviz` are incomplete:
`MCInit` leaves `passes` unassigned. TLC and tlx both reject them. They need corrected examples or
explicit classification as invalid inputs, rather than an engine fix.

## Measurement quality and high-speedup validation

Four frozen default-mode configurations have a sample range divided by the median above 25%:
`MultiCarElevator/ElevatorSafetyLarge`, `Prisoners_Single_Switch/PrisonerSolo`,
`SpecifyingSystems/AsynchronousInterface/AsynchInterface` and `barriers/Barrier`.
Keep their samples visible and repeat measurements before using them to establish small changes.

The [audit of ratios above 100x](research/speedup-audit.md) identifies further validation work:
repeated TLC measurements on the same instance, explicit cache conditions, comparable runs with
and without automatic reduction, and per-property correctness checks. `MCParReach` still lacks
phase attribution. Matching counts and a log line announcing liveness checking do not prove that
every temporal property was translated correctly.
