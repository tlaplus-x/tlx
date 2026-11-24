# Post-fix validation, 2026-10-11

> [!NOTE]
> **Historical point-in-time validation record** — not an active normative specification. This
> document captures the 2026-10-11 post-freeze validation runs (`e59632b1` and `d2a36005`) on
> Tencent `SA5.4XLARGE32` x86_64 spot instances (`bench/validation/2026-10-11/`). Current benchmark
> protocol and published performance numbers on `main` are owned by
> [benchmarking.md](../benchmarking.md) and [performance.md](../performance.md).

Source identifiers below name reachable, source-equivalent commits in this history.
The original measurement and reproduction identifiers remain in the evidence files; [source-equivalents.toml](../../bench/environment/source-equivalents.toml)
maps those original identities to revisions with identical Rust/workspace inputs.
This source mapping does not claim that a historical measurement ran on a rewritten commit.

These results validate subsequent fixes; they do not replace the frozen initial baseline in
`bench/records/` or the headline table in [performance.md](../performance.md).
The measurements used separate Tencent SA5.4XLARGE32 x86_64 spot instances
(AMD EPYC 9754, 16 vCPU, 32 GB), with clang. Both runs have final fetch receipts;
the instances were terminated and a subsequent provider listing found no remaining instances.

[provenance.json](../../bench/validation/2026-10-11/provenance.json) records revisions, machine class, sampling and file checksums.
The Kafka JSON files are gzip-compressed original outputs; their decompressed checksums are also
recorded. They retain per-run statistics and output rather than only the table below.

## Correctness fixes

Source-equivalent revision: `e59632b14c15f858b89ee49817f7b88f63425067`.
[Manifest](../../bench/validation/2026-10-11/core-suite.json), [original results](../../bench/validation/2026-10-11/fixes-core.json).
One discarded warm-up followed by three timed samples; native caches were not isolated per model.

| Model | Mode / workers | Timed wall seconds | Median seconds | Result | Distinct / generated / depth |
|---|---|---|---:|---|---|
| MCInnerSerial | default / 1 | 788.233, 783.666, 775.857 | 783.666 | success | 195 / 6,181 / 5 |
| MCccfraft_1C3N | compiled `-tlc` / 1 | 280.795, 279.132, 278.189 | 279.132 | success | 675,893 / 1,848,071 / 66 |
| MCccfraft_1C3N | compiled `-tlc` / 16 | 32.934, 32.798, 32.986 | 32.934 | success | 675,893 / 1,848,071 / 66 |

All three configurations completed with empty `count_problems`. The CCF checks agree with the
stored TLC verdict and counts; MCInnerSerial completed liveness checking and agrees with the
stored safety counts. These observations establish completion on the original configurations,
not a proof of all language semantics or a speedup attributable to each individual change.

## Enumeration limits

[Manifest](../../bench/validation/2026-10-11/cardinality-suite.json), [original results](../../bench/validation/2026-10-11/fixes-cardinality.json).
CarTalkPuzzle Model_3 and SpanTreeTest5Nodes each reached the 600-second warm-up limit. Neither
produced a timed sample. They no longer fail immediately on the previous cardinality overflow,
but neither completed: the collector's aggregate `skipped` row and empty timing arrays must not
be read as a zero-second result. This pass is **inconclusive**, which is why its cloud invocation
returned exit 1 even though the preceding correctness pass completed.

## Kafka cancellation diagnostic

Before source: `e59632b14c15f858b89ee49817f7b88f63425067`.
After source: `d2a360051e601f5435709dfc39df00e2d3a782d7`.
The Rust changes between these revisions are the compiler-cancellation fix.
Each binary/configuration had its own initially empty native cache, no warm-up, one sample,
statistics collection enabled and a 1,800-second limit. This is a diagnostic A/B, not a repeated
performance estimate. Both binaries ran on the same instance, sequentially.

| Mode / workers | Before wall s | After wall s | Before CPU s | After CPU s | Result |
|---|---:|---:|---:|---:|---|
| default / 1 | 1,253.168 | 1,208.692 | 4,216.917 | 1,606.852 | deadlock on both |
| compiled / 16 | 169.010 | 162.364 | 1,714.010 | 2,038.806 | deadlock on both |

[One-worker original output](../../bench/validation/2026-10-11/kafka-cold-1.json.gz),
[16-worker original output](../../bench/validation/2026-10-11/kafka-cold-16.json.gz).
At one worker both runs reached 5,200,276 distinct states, 23,148,306 generated states and depth 22.
At 16 workers both stopped at depth 21, but the early-stop counts differ: 6,023,669 versus
7,220,733 distinct states. Parallel early-stop counts depend on scheduling; the higher after-run
CPU and explored-state totals prevent treating this as identical work per second.

The single observations show lower elapsed time in both cases and lower CPU use at one worker.
They do not establish a stable percentage improvement. Repeated, comparable samples are still
needed. Both before and after finished within this run's bound, so this experiment also does not
show that cancellation alone explains the earlier 1,800-second timeout.
