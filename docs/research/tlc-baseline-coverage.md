# TLC baseline coverage

> [!NOTE]
> **Historical point-in-time campaign record** — not an active normative specification. This
> document captures the 2026-10-08 to 2026-10-10 TLC `1813307` baseline collection campaign on
> Tencent `SA5.4XLARGE32` x86_64 spot instances (1 and 16 workers). Current baseline collection,
> keying and report rules on `main` are owned by [benchmarking.md](../benchmarking.md) and
> [performance.md](../performance.md).

How much of the benchmark corpus has a usable TLC timing baseline in the store
[benchmarking.md](../benchmarking.md) section 5 defines, and the recorded cause of every key
that has none. A baseline key is TLC revision + model id + input digest + worker count +
instance type; a key with no completed measurement is a gap, and a gap is only useful if it
says *why* it has none. Timeouts and errors are outcomes of the TLC run, budget skips are
outcomes of the collector, and the two are easy to confuse: `tlcbase --missing` prints a key
that was never tried exactly like a key whose TLC run timed out. This report separates them.

TLC times for the corpus are collected once and reused: a later performance run reads the
store instead of launching TLC for a baseline, so the TLC baseline files in the measurement store
(`bench/tlc-baselines/`, one file per key) are
meant to be the last TLC measurement of this revision on this instance type.

The campaign collected the baselines for TLC revision
`1813307068bbc5759a441df820f3f548948d6b7a` on instance type `SA5.4XLARGE32`, at 1 and 16
workers, between 2026-10-08 and 2026-10-10, on cloud instances of that type (a baseline is
meaningful only on the machine type it was measured on). TLC's baseline jar (`third_party/tla2tools.jar`)
is pinned by SHA-256 and manifest revision in `scripts/dependencies.py` (`scripts/fetch-deps.sh`),
while `third_party/community/modules.jar` is fetched from `CommunityModules` `releases/latest` and
recorded by SHA-256 in each baseline header, so matching keys are reused by later
tlx benchmarks instead of re-running TLC.

## Method

List missing or stale baseline keys with the public benchmark driver:

```sh
python3 scripts/bench.py tlcbase --missing --workers 1,16 --instance-type SA5.4XLARGE32
```

One slice of the collection, on a cloud instance of the baseline's own type:

```sh
python3 scripts/bench.py tlcbase --instance-type SA5.4XLARGE32 --missing --collect \
    --models <ids> --workers <1|16> --timeout <seconds> --deadline-min <minutes> \
    --out bench/history/tlc-1813307-lane<name>.json
```

`--missing` selects only keys with no valid completed measurement, so a slice can be re-run
without repeating work. Slices are cut by expected cost, not by model count: each one is a
balanced group of keys whose estimated TLC times (read from earlier receipts) add up to a
comparable length, and the very long models get a slice of their own. Slices are joined with

```sh
python3 scripts/bench.py tlcbase-merge bench/history/<merged>.json bench/history/<slice>.json ...
python3 scripts/bench.py tlcbase-report tlc-1813307
```

Each launch runs on a cloud instance of the baseline's own type under `--max-minutes` and the
launcher's dead-man switch, so a lost instance stops itself instead of spending on. Slices run
in parallel within a fixed number of concurrent instances; a key measured on another instance
type is never reused as this key's baseline.

The measurement method is the oracle's (`scripts/tlc.py`: TLC's default heap and `-fpmem`, no
`-Xmx`; simulation models with `-seed 1`; one JVM at a time) plus
`-Dtlc2.TLC.asMilliSeconds=true`. Each run records wall time (with JVM start-up), TLC's own
"Finished in", JVM CPU time, peak RSS, counts, result and violated name.

## Coverage

Before this campaign the store held the small models and a first pass over the rest; the
campaign filled in the medium, large and huge models. By size tier and worker count, before
and after:

| tier | 1 worker | 16 workers | 1 worker | 16 workers |
|---|---|---|---|---|
| | before | before | after | after |
| small | 161/162 | 156/162 | 161/162 | 156/162 |
| medium | 44/57 | 46/57 | 47/58 | 47/58 |
| large | 10/11 | 10/11 | 10/11 | 11/11 |
| huge | 2/4 | 4/4 | 2/4 | 4/4 |
| **total** | **217/234** | **216/234** | **220/235** | **218/235** |

**Before: 433 of 468 keys (92.5%). After: 438 of 470 keys (93.2%).** The campaign covered
three keys that had no usable measurement (1 worker `NanoBlockchain/MCNanoLarge`, 1 worker
`SlushProtocol/SlushLarge`, 16 workers `bench/RaftMongoT4`), and turned 15 keys that had been
never measured, skipped by the collector's budget admission, or timed out at a shorter bound
into a recorded outcome at a longer bound. The denominator grew by one model per worker
(234 -> 235) because the corpus manifest registered the Accord deep-chain benchmark while the
campaign ran; both of its keys were measured (1 worker 163 s, 16 workers 25 s), and each total
above is shown on its own pass's denominator.

## Timeouts at the bound (19 keys)

A timeout does *not* mean the model is unmeasurable at a longer bound; it means the recorded
bound was reached. The 16-worker bound is often shorter than the 1-worker bound because the
slice budget, not the model, chose it.

| model | worker(s) | bound | note |
|---|---|---|---|
| `CarTalkPuzzle/CarTalkPuzzle.toolbox/Model_3/MC` | 1, 16 | 14400 s / 1800 s | The 1-worker run is the longest model of the campaign, in a slice of its own. |
| `KeyValueStore/MCKVSSafetyLarge` | 1, 16 | 7200 s | |
| `MultiPaxos-SMR/MultiPaxos_MC` | 1 | 3600 s | Huge tier; 16 workers completes. |
| `bench/RaftMongoT4` | 1 | 1800 s | Liveness configuration; 16 workers completes in 2047 s. |
| `bench/cf1s_folklore_N5` | 1 | 3600 s | |
| `byzpaxos/BPConProof` | 1, 16 | 3600 s / 7200 s | The 16-worker run needed a larger states disk; see below. |
| `c1cs/c1cs` | 1, 16 | 7200 s | |
| `dag-consensus/TLCSailfish2` | 1, 16 | 7200 s | Same re-run as `byzpaxos/BPConProof` at 16 workers. |
| `detector_chan96/EnvironmentController` | 1, 16 | 7200 s | |
| `diskpaxos/MC_HDiskSynod` | 1, 16 | 7200 s | |
| `ewd998/EWD998` | 1, 16 | 7200 s / 1800 s | The 16-worker run is heap-bound: peak RSS 8.3 GB against the JVM's 7.6 GiB default heap. |

None of these runs stalled: each reached its bound with its workers busy the whole time (about
1.1 CPU-seconds per wall second at 1 worker, 11-16 at 16 workers), so the state space was
still growing. Collection policy since 2026-10-09: a key that does not converge before its
deadline is left empty and not re-run - it is recorded here as a gap instead, and no longer
launch is bought for it. Keys that an earlier pass had timed out at a *shorter* bound were
re-run once at the bound above during this campaign (`c1cs/c1cs`,
`detector_chan96/EnvironmentController` and `ewd998/EWD998` went from 1800 s to 7200 s;
`diskpaxos/MC_HDiskSynod`, `byzpaxos/BPConProof` and `dag-consensus/TLCSailfish2` were measured
for the first time in this campaign), so for these keys the bound above is the strongest
evidence the campaign could record.

## TLC errors (11 keys)

These keys have a TLC run, but it exited with an error (exit code 10, or 255 after a completed
run). They are grouped by where the error comes from, because the groups need different
follow-up.

**16 workers only (5 keys).** The model runs to completion at 1 worker and the oracle
(`corpus/out/tlc.json`) records a successful 1-worker TLC run, but the same configuration at
16 workers stops within a second on a false assumption, an assertion or a postcondition:

| model | message (TLC) |
|---|---|
| `DieHard/MCDieHardest` | `Assumption line 59, col 8 to line 60, col 37 of module DieHardest is false.` |
| `KnuthYao/SimKnuthYao` | postcondition: `The first argument of Assert evaluated to FALSE; the second argument was: <<"Fewer samples than expected:", 104>>` |
| `ext/ccf/TraceMultiNodeReads_ElectionNoRollback` | false assumption in module `TraceMultiNodeReads` |
| `ext/ccf/TraceMultiNodeReads_RollbackSameSeqno` | same as above |
| `ext/etcd-raft/Traceetcdraft_400` | `Assumption line 462, col 8 to line 462, col 34 of module Traceetcdraft is false.` |

**Both workers (6 keys).** `bench/ReplicatedLog4x3` fails identically at 1 and 16 workers in
0.5 s, on a false assumption in its own configuration module `MCReplicatedLog`: TLC rejects
that configuration, so there is nothing to time.

`ewd998/EWD998ChanID_export` and `ewd998/EWD998ChanID_shiviz` are a different failure: the
model *completes* (TLC prints `Finished in ...` after about 4 s) and the JVM then exits 255
while printing the trace, with `java.lang.RuntimeException: ... Cannot apply @@ to a string
representation of a record?` from the value-printing path. That is a TLC output-formatting
limit on these two trace views, not an evaluation or search failure, so their timing is not
recoverable without changing the model's output; it is recorded here rather than retried.

## Not measurable by TLC (2 keys)

At the time of this campaign, `ewd998/EWD998ChanTrace` (1 and 16 workers) failed in TLC: TLC's own oracle
(`corpus/out/tlc.json`) recorded the same `error` with
`Error: Evaluating assumption line 11, col 23 to line 11, col 37 of module EWD998Chan failed.`
Because the spec reads `specifications/ewd998/EWD998ChanTrace.ndjson` relative to the Examples
corpus root rather than its own directory, those two keys produced no TLC timing during this
campaign. Subsequent root-relative staging (`cwd: root` in `scripts/corpus.py`, [testing.md](../testing.md)
section 6.1) resolved the upstream module/input path alongside the 2026-10-11 validation wave
documented in [post-fix-validation.md](post-fix-validation.md) and
[ewd998-chantrace-oracle.json](../../bench/validation/2026-10-11/ewd998-chantrace-oracle.json).

## Infrastructure failures and tooling changes

Two 16-worker keys (`byzpaxos/BPConProof`, `dag-consensus/TLCSailfish2`) filled the instance's
states directory and the collector stored the failure as a model-level `error` - an
infrastructure failure that looked like a model result. The states disk is now a launcher
parameter (`--disk-gb`), and both keys were re-run on a 400 GB states disk, where they reached
the 7200 s bound: the record the store keeps for that key is the re-run, so the gaps above
describe the models, not the disk.

Lane drivers lost their SSH sessions roughly every five minutes in one window because the
shared security group's rules were rewritten by other launches; the launcher now re-applies
its own owner-tagged rule and reconnects, and re-fetches the results of a streamed run instead
of failing the lane. An output-streaming cap that could terminate a healthy lane after 20
failed reads was removed for the same reason.

The collection runs under a supervisor that survives the tool shell: the fold loop that turns
finished lanes into store records, the slot gate and the lane bookkeeping keep running when
the shell that started them dies, and a granted lane's state is preserved across the restart.
The default allowance is two launches per 12 h; the long slices and the disk-full re-run ran
under owner grants, each a bounded launch with a slot share and a spend allowance.

## Reproducing and reading back

```sh
python3 scripts/bench.py migrate                        # re-derive bench/records/ and bench/tlc-baselines/ when raw sources are present
python3 scripts/bench.py tlcbase-report tlc-1813307     # totals, distribution, slowest, oracle mismatches
python3 scripts/bench.py tlcbase --missing --workers 1,16 --instance-type SA5.4XLARGE32
```

`tlcbase-report` prints the 1- and 16-worker totals, the wall-time distribution, the slowest
models and every count mismatch against the TLC oracle. The per-key TLC baselines ship in
`bench/tlc-baselines/`; raw slice files from collection runs are archived outside the published
`bench/` directory under ignored `work/`.
