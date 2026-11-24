# State representation alternatives

> [!NOTE]
> **Historical point-in-time research record** — not an active normative specification. This
> document captures the pre-`v0.1.0` 21-model state-representation prototype survey (`B+A`, `D`,
> `E`, `repr-b2`) measured on an AMD EPYC 9754 (`SA5.4XLARGE32`) cloud host prior to repository
> history consolidation at `5dc582bde9`. Current value-store representation and native coverage
> contracts on `main` are owned by [value-store.md](../value-store.md) and
> [native-coverage.md](../native-coverage.md).

**M** denotes a measurement; **A** denotes an architectural estimate.

M: direct native lowering D is the strongest measured near-term change:
5.88× / 6.04× on the original CCF models. B+A eliminates restarts and queue
re-encoding with below-1% common-path cost on four controls, but its escaped
symmetry, transcoding and interpreted predicates cause severe regressions.
A: build D first, narrow store promotion to measured profitable slots, and
continue B+A on a stable slot-access ABI with local guards and native predicate
versions. The immutable arena remains useful for escapes and selected Dyn
workloads; the current general Ref path is not a broad performance win.

The fixed attribution baseline is `17dcf775`; the batch-2 store is pinned to
`c4d2c45c`. Revisions, inputs, counters and limitations are separated below.

## Method and attribution

M: the original 21-model attribution used `-compile -workers 1 -tlc` on an
AMD EPYC 9754 cloud host with 16 vCPUs (SA5.4XLARGE32). Each model had a discarded
warmup, an uninstrumented process CPU/RSS sample with `perf stat`, a separate
`-stats` sample sampled with `perf record`. These are diagnostic single
samples, not an A/B performance claim. The complete command, raw phases,
layouts, host-region roots and hardware were recorded in the attribution artifact
(`state-representation-alternatives-attribution.json`), which is not part of the
released tree: it is one `scripts/bench.py profile` pass on the runner revision it
names, and it carries that command ([benchmarking.md](../benchmarking.md)).
No TLC timing was recollected.

M: CPU below is process user+system time without stats. Pre-run, build and
search are the elapsed phase timers from the separate instrumented run;
`-stats` does not expose per-phase CPU clocks. Host times are inclusive elapsed
times from the final layout's regions, including memo hits; they overlap search
and action time and exclude regions belonging to discarded earlier layouts.
They give an operation ranking and a lower bound, not an additive CPU partition. They also exclude boxed operations executed directly by whole-function closure IR after adaptive tier choice, which bypasses the mixed-region entry point.
Build means lowering/C generation across attempts; warm C-cache lookup/load is
separate in the raw phases. Restarts also count misses; re-encoded states are
existing queue/archive states, not newly generated successors.

| Original configuration | CPU s | Pre-run s | Build s | Search s | Host s / calls | Misses / re-encoded | Root Dyn slots |
|---|---:|---:|---:|---:|---:|---:|---|
| MCBakery | 1.45 | 0.101 | 0.003 | 1.661 | 0.000 / 0 | 0 / 0 |  |
| MCKVSSafetySmall | 11.79 | 0.031 | 0.001 | 16.914 | 0.000 / 0 | 0 / 0 |  |
| MC_tlx_Zab_new | 31.26 | 1.003 | 0.268 | 33.619 | 0.078 / 209,796 | 0 / 0 |  |
| Accord_baseline__deep_chain | 3.55 | 0.078 | 0.242 | 3.936 | 0.593 / 5,875,643 | 3 / 248,751 |  |
| Accord_baseline__keys_only | 1.23 | 0.029 | 0.139 | 1.316 | 0.373 / 2,720,103 | 2 / 30,552 |  |
| Accord_baseline_load__keys_only | 2.89 | 0.033 | 0.144 | 3.258 | 0.570 / 4,257,517 | 2 / 121,157 |  |
| MCMultiNode | 36.80 | 0.043 | 0.006 | 38.802 | 7.325 / 18,649,872 | 0 / 0 |  |
| MCMultiNodeReads | 66.90 | 0.038 | 0.006 | 69.260 | 10.852 / 27,265,180 | 0 / 0 |  |
| MCSingleNode | 1.09 | 0.051 | 0.004 | 0.986 | 0.110 / 206,470 | 0 / 0 |  |
| MCccfraft_1C3N | timeout | — | — | — | unavailable | unavailable | unavailable |
| MCMongoReplReconfig | 32.32 | 0.055 | 0.004 | 39.328 | 2.742 / 20,867,354 | 0 / 0 |  |
| MCMoveRange | 11.27 | 0.084 | 0.378 | 10.257 | 0.049 / 196,651 | 9 / 58,603 |  |
| MCRaftMongo | 14.38 | 0.065 | 0.017 | 15.092 | 0.905 / 55,328 | 0 / 0 |  |
| pull-raft-KRaft | 12.39 | 0.272 | 0.020 | 13.221 | 1.432 / 1,941,027 | 0 / 0 | messages |
| pull-raft-PullRaft | 6.38 | 0.068 | 0.105 | 7.103 | 2.157 / 4,270,528 | 5 / 3,778 | messages |
| raft-and-fsync-RaftFsync | 8.28 | 0.126 | 0.012 | 8.676 | 1.229 / 1,772,756 | 0 / 0 | messages |
| standard-raft-Raft | 4.64 | 0.097 | 0.019 | 5.258 | 1.298 / 1,679,957 | 0 / 0 | messages |
| standard-raft-RaftWithReconfigAddRemove | 1.09 | 0.076 | 0.056 | 0.978 | 0.330 / 556,821 | 0 / 0 | messages |
| standard-raft-RaftWithReconfigJointConsensus | 6.45 | 0.078 | 0.058 | 6.772 | 1.995 / 2,256,119 | 0 / 0 | messages |
| MCLamportMutex | 2.47 | 0.034 | 0.003 | 3.012 | 0.000 / 0 | 0 / 0 |  |
| PaxosCommit | 5.99 | 0.042 | 0.004 | 7.704 | 0.000 / 0 | 0 / 0 |  |

M: 20 models completed. `MCccfraft_1C3N` exceeded the 180-second bound in both
the warmup and measured run; it is censored, not a zero-cost result. The
replacement is `MCMultiNodeReadsNotLinearizable` (an existing medium
configuration), reported separately on the later fixed main revision. Across the 20 completed cases there were 21 misses, 462,841
state re-encodings and 0.642 seconds of explicit re-encoding. Instrumented search
summed to 287.153 seconds; pre-run to 2.404 seconds and model build to 1.491
seconds. Removing re-encoding alone therefore addresses about 0.22% of this
summed instrumented search, although the cost is concentrated in MoveRange,
PullRaft and Accord. The runs also report 4,623 state expansions repeated after
layout changes (3,633 in MoveRange and 983 in PullRaft). Restart bookkeeping,
partial re-expansion and rebuilding codecs can also be saved; their CPU is not
isolated, so 0.22% is only the explicit re-encoding component, not an upper bound
for A. This is a different revision/configuration/mode sample
from the older 46-miss survey in the design document.

M: explicit re-encoding is concentrated as follows; these are elapsed
components of the instrumented search, not CPU percentages or total restart
cost. A can remove this component, but any escape/tag/dispatch cost is paid
on the much larger common path.

| Original configuration | Re-encoding s | Share of search | Repeated expansions |
|---|---:|---:|---:|
| MCMoveRange | 0.452 | 4.41% | 3,633 |
| pull-raft-PullRaft | 0.078 | 1.09% | 983 |
| Accord_baseline__deep_chain | 0.070 | 1.78% | 3 |
| Accord_baseline__keys_only | 0.013 | 0.99% | 2 |
| Accord_baseline_load__keys_only | 0.029 | 0.90% | 2 |

M: CCF MultiNode's final host table contains 16,453,290 boxed membership calls
(6.391 s), 1,545,362 `SortSeq` calls (0.825 s) and 650,434 map constructions
(0.108 s). Reads has 23,329,281 membership calls (8.997 s), 2,789,827 sorts
(1.682 s), and 1,145,286 map constructions (0.172 s). Membership is usually
rooted in `UnionField(history)`. Total reported host time is 18.9% / 15.7% of
the respective instrumented search. The earlier 7.3-second MultiNode reference is not a baseline for this fixed
revision/input: this run has 1,546,226 states and 36.80 CPU seconds. Input,
revision and mode differences must not be pooled; no automatic-symmetry cause
is assumed for the difference.

M: the Raft variants retain `messages` as a root Dyn slot. Their final host
tables are 10.8–33.7% of search, dominated by boxed comparisons, membership,
DOMAIN, bag override (`@@`), lookup and field access. Accord's host share is
15.1–28.3%, principally membership and quantified predicates. Mongo Reconfig
has 20,867,354 membership calls (2.742 s, 7.0% of search). RaftMongo's remaining
quantified host expression costs 0.902 s (6.0%); MoveRange has only 0.5% in the
final region table but nine layout misses. Zab's final host table is 0.2%;
its cost is principally fingerprinting and compiled/action work. The four
controls have no reported host-region calls or layout misses.

M: this distinction is material in CCF. `UniqueTxRequestsInv` takes an
estimated 13.360 seconds in closure IR across 1,541,265 calls, but its mixed
path records only 110,461 region evaluations. `AtMostOnceObservedInv` likewise
spends 2.366 seconds in IR. These are sampled function estimates, not additional
CPU clocks, and overlap the overall phase measurements. Removing their last
host operation can make the entire nested predicate native and avoid IR
iteration, memo keys and decoding. Consequently a native-lowering effect can
substantially exceed the 18.9% reported mixed-region time; that percentage is
not an Amdahl ceiling for D. A complete operation count including closure IR
would require instrumentation beyond the existing `-stats` interface.

M: sampled CPU in the instrumented CCF MultiNode run corroborates the
host-operation ranking: memo lookup takes 13.11% of samples, layout decoding
5.50%, and membership itself 2.44%. These are flat, potentially shared symbols,
not percentages attributable solely to membership. Zab instead spends 19.84%
in encoded fingerprint hashing and 12.32% in permutation application; Mongo
Reconfig spends 18.02% in permutation application and 8.27% in encoded hashing.
Neither has root Dyn slots in this run. Promoting only non-inline slots cannot
remove that inline symmetry/fingerprint workload. Stats and sampled profiles
are perturbed diagnostics; the uninstrumented repeated A/B is the effect-size
measurement.

<!-- Host operation attribution -->

M: the three leading reported host operation roots for each nonzero case
are below (calls / inclusive elapsed seconds). These are the final layout
only; the raw artifact retains every root, including low-frequency operations.

| Original configuration | Leading host operation kinds: calls / s |
|---|---|
| MC_tlx_Zab_new | union: 135,265 / 0.055; t51: 33,252 / 0.012; t176: 27,482 / 0.008 |
| Accord_baseline__deep_chain | membership: 5,297,234 / 0.497; Eq: 316,929 / 0.032; call f3: 42,360 / 0.027 |
| Accord_baseline__keys_only | membership: 2,076,008 / 0.206; forall: 52,288 / 0.073; Eq: 428,236 / 0.044 |
| Accord_baseline_load__keys_only | membership: 3,284,139 / 0.313; forall: 105,131 / 0.106; call f3: 66,699 / 0.067 |
| MCMultiNode | membership: 16,453,290 / 6.391; SortSeq: 1,545,362 / 0.825; map construction: 650,434 / 0.108 |
| MCMultiNodeReads | membership: 23,329,281 / 8.997; SortSeq: 2,789,827 / 1.682; map construction: 1,145,286 / 0.172 |
| MCSingleNode | membership: 186,344 / 0.103; map construction: 20,126 / 0.007 |
| MCMongoReplReconfig | membership: 20,867,354 / 2.742 |
| MCMoveRange | union: 189,945 / 0.048; t5: 6,706 / 0.001 |
| MCRaftMongo | quantifier: 42,176 / 0.902; const {}: 13,152 / 0.003 |
| pull-raft-KRaft | comparison >: 840,893 / 0.444; membership: 155,671 / 0.234; bag override @@: 43,855 / 0.195 |
| pull-raft-PullRaft | comparison >: 2,339,018 / 0.874; membership: 212,598 / 0.288; EXCEPT: 180,108 / 0.258 |
| raft-and-fsync-RaftFsync | membership: 198,758 / 0.486; bag override @@: 90,748 / 0.327; comparison >: 860,622 / 0.195 |
| standard-raft-Raft | comparison >: 758,308 / 0.506; membership: 91,676 / 0.229; bag override @@: 32,934 / 0.145 |
| standard-raft-RaftWithReconfigAddRemove | comparison >: 203,061 / 0.060; membership: 49,744 / 0.057; Eq: 135,417 / 0.036 |
| standard-raft-RaftWithReconfigJointConsensus | membership: 354,338 / 0.554; bag override @@: 73,200 / 0.366; comparison >: 753,174 / 0.358 |

M: the four controls have no host-region roots in this sample; the censored
CCF configuration has no usable operation table. The replacement medium
configuration is reported separately with its own revision and input.

<!-- End host operation attribution -->

## Candidate mechanisms and removable costs

| Candidate | Cost it can remove (A unless stated M) | Remaining cost / failure mode | Implementation estimate (A) |
|---|---|---|---|
| A: inline slots with escapes | Re-encoding and global layout restart; narrow layouts survive late outliers | Tag checks, overflow memory, canonical fingerprints; no direct removal of host operations | Medium: codec, queue, symmetry/VIEW, checkpoint format and ownership |
| B+A: guarded local versions | A's costs plus interpretation caused by wrong shape speculation | Compilation work is retained; guards and versions must use the same external ABI; effect rollback and storm limits matter | High: action/expression guards, version publication, generic fallback, tier integration |
| C: canonical values for non-inline slots | Repeated structural hashing during interning and host operations, child sharing, operation memoization | Today's Dyn interner already supplies canonical root IDs and O(1) encoded equality; recursively consing every scalar does not itself remove host dispatch | Medium for a Dyn/escape replacement; high for all operators |
| D: native host-operation lowering | The targeted portion of the measured host table, without representation-wide indirection | Does not address late shapes or unlowered operations; dispatch, memoization and decoding surrounding the targeted operation also matter | Low–medium per operation; separate sorting is more complex |
| E: per-slot hybrid | The Dyn-backed Raft bag workload; known batch-1 implementation promotes slots containing Dyn and keeps the rest inline | Layout speculation remains for inline slots; store conversion, operation dispatch and memory remain on promoted slots | Already available as batch-1; medium to add escapes as its promotion trigger |

M: `dynval.rs` already interns structurally equal composite roots to a unique
handle and stores common scalars directly in tagged handles. Candidate C is
therefore useful only if it adds recursive sharing, cached semantic digests or
operations that stay on IDs. Merely replacing the hash table repeats existing
work. Dyn handles already participate directly in encoded state equality and
fingerprinting; their numeric assignment is process-local and is not a semantic
cross-codec digest. Cached semantic digests matter for inline/escape consistency
and host memo keys, rather than making an already constant-size Dyn state word
smaller. The batch-1 store provides that narrower experiment; the batch-2 full
operator path tests whether those gains exceed its dispatch/read overhead.

M/A: CCF has zero state-layout misses but tens of millions of host calls;
its B+A rows request no new shapes. Those costs are predominantly missing
native operations and whole-function IR tier choice, so wider state codecs
alone do not remove them. Likewise, Raft's `messages` is already Dyn after the
initial speculation. A/B addresses late shape changes; D and ID-resident
operations address the separate unsupported-operation problem. This is why a
single representation-wide redesign should not be credited with both budgets
without measuring its execution paths.

A: even eliminating every reported host-region nanosecond leaves most search
work. B+A and D are complementary: stable slots remove invalid speculation as a
search-wide event, while native lowering avoids boxing/host dispatch on stable
shapes. A useful refinement is a stable slot access ABI shared by all versions,
so a recompiled action loads only its touched slots and never transcodes a
whole state. That refinement is not an additional measured prototype here.

M: the prototype's implementation size gives a useful complexity comparison:
B+A adds roughly 500 production Rust lines across the codec, fingerprint,
version manager and driver, before its tests; D adds roughly 50 lowering lines
and uses existing execution backends. These line counts describe this minimal
experiment, not production effort.

A: a stable per-slot ABI, selective generic fallback, expression versions,
reclamation and persisted escapes remain
substantial work beyond B+A; D can be integrated one independently tested
operation at a time.

## B+A prototype and correctness boundaries

M: `TLX_ESCAPE=1` keeps the first inline codec immutable and appends one overflow
handle per variable in the queue codec. Inline state objects omit the zero
suffix; the overflow store is allocated only on the first outlier. The queue
still reserves one extra 64-bit word per variable even when every value is
inline; packing tags into available codec space is future work. Fingerprints
normalize forced escapes back to their inline encoding when possible, and use
semantic digests for genuine outliers, never handle IDs. Existing queued states
are not re-encoded. Native actions buffer all successors before publication.
An escaped input or failed compiled action tries a published version, otherwise
only that action is interpreted. Inline inputs first try their initial version.

M: at most two widened execution codecs and then an all-Dyn version are built
on a background thread using the existing native tier machinery. The counter
tracks requests, with a separate pending-build metric; it does not imply every
requested version became native before termination. Old region tables are
retained in stats so totals include every published version. A version converts
its input/output transiently; this is an implementation cost, not a rewrite of
existing queue states. Predicates over escaped states currently fall back
individually. Each background version lowers an entire model, although execution fallback
is confined to the current action. Only the initial and latest published
versions participate in dispatch; older versions are retained for statistics.
The prototype is action-level, not an expression-level optimizer. Its input
escape test is global rather than restricted to the current action's read-set,
so an unrelated escaped slot can reroute an otherwise unaffected action. This
is a measured-prototype limitation, not the intended final deoptimization
granularity.

M: side effects exposed a real boundary: the existing effects journal rolls
back whole searches, not individual actions. Initial testing found two duplicate
file writes and three incompatible explicit checkpoint cases. Actions with irreversible effects
now mechanically use the interpreter, and explicit checkpoints disable the
experiment. Print/PrintT alone use the existing transactional output buffer;
a later focused correction replaced an overly broad volatile-action guard
with the existing `stmt_volatile_beyond_output` classification. Those five targeted regressions pass. The overflow store has a hard
4 GiB limit and no reclamation; explicit checkpoint/recovery and speculative
irreversible side effects remain unsupported speculative paths. A regression
forces a printing action through a real native layout failure and checks that
the fallback prints exactly once; the CSV/checkpoint regressions remain green.

M: the growing-shape cycle regression agrees with the interpreter at 81
generated / 80 distinct / depth 80 in closure IR, C, JIT and JIT-only modes,
with no layout restart, no state re-encoding and at most three background
versions. Cross-form tests cover integers, tuples, sets, functions and VIEW.
All three spectest modes passed 441/441 contract judgments
(434 pass, seven expected failures) with the switch enabled. All 21 fixed small
configurations also matched the interpreter under paranoid mode and fresh TLC
correctness oracles; counts, verdicts, violated names, depth and safety-trace
lengths are retained in the correctness artifact
(`state-representation-alternatives-correctness.json`), which is not part of the
released tree: it records the switch, the revision and the command behind each
check above.
A deterministic unit test also synchronizes each version publication: three successive shape changes produce the all-Dyn version, and subsequent integer/tuple changes request no fourth build. Final acceptance reruns affected paths after integration.

## D prototype and correctness

M: the native-lowering prototype at `beea1f2b` implements two narrow lowerings found in the attribution.
CCF tests a history record's type against a small constant enumeration, but
its predicted atom universe contains other typed model values. The existing
comparability proof rejects the whole universe and boxes every legal input.
The prototype precomputes a truth/error table for every encoded atom (up to
256 atoms/elements); an error entry still falls back to the interpreter, so
unreachable incompatible atoms do not force every successful call through a
host region. This uses the existing lookup IR, closure executor, JIT and C.

M: Mongo Reconfig's quorum predicate tests membership in an already lowered
powerset/filter. The prototype recognizes that lowered powerset and computes
bitset difference, only when the element universes are provably comparable.
Other inputs retain the existing host path. No state codec, native ABI or
runtime value implementation changes are needed for these lowerings.

M: two dedicated differential tests exercise broad typed/untyped atom
universes, deferred heterogeneous enumerations, error-versus-value behavior,
and powerset filters. Both pass with C and JIT-only native backends as well
as closure IR and the interpreter. All 21 fixed reduced models agree with
the interpreter under `TLX_PARANOID=1`; the existing fresh TLC contracts have
identical spec/config digests and also agree. The native-comparison rows are
in the correctness artifact above. Timing conclusions use the cloud samples,
not these checks.

## Fixed comparison configurations

The fixed reduced configurations are in `bench/repr-models.toml` and
`bench/repr-configs/`, registered in `bench/suite.json`. The five-arm table uses
these exact configurations; the larger three-arm table retains the original
CCF MultiNode/Reads, two Raft variants, Zab and controls. The store's large cases
are capped diagnostics. Code inspection of the pinned repr-b2 is also
material: `c4d2c45c` promotes variable-length sequences, non-bitset sets,
variable-domain functions larger than eight inline words, length-changing tuple
unions and containers holding such values, in addition to Dyn. Batch-1 E only
promotes roots containing Dyn. Thus the same-revision repr-b2 toggle isolates
its combined selection policy and store execution path, not dispatch alone;
neither arm is the future all-variables-as-stable-roots design. Reduced JointConsensus uses three servers and initial
cluster size two: merely lowering the reconfiguration bound delayed its
terminal deadlock and exceeded the local correctness timeout. Reduced Accord
uses fewer tasks; Bakery must reduce N with MaxNat because its ASSUME requires
N to belong to the overridden Nat. Raw attribution above remains on the
original configurations.

The tables below separate three-round uninstrumented CPU/RSS comparisons from
single-pass diagnostics. The optional default-mode supplement is explicitly
censored. Correctness runs and single attribution samples are not used as
standalone performance conclusions.

## Five-arm fixed small configurations (M)

All five arms use the identical fixed inputs from `bench/repr-models.toml`,
one worker, TLC mode, a discarded warmup and three rotating interleaved
rounds on one AMD EPYC 9754 instance. Cells are median process CPU seconds /
median per-process peak RSS MiB. `*` marks a relative CPU range above 5%;
short-case timings include startup and compilation, so large-model evidence
takes precedence for performance conclusions. Main and the batch-1 hybrid
use `bfe7daf3`; corrected B+A uses `facd6658`, D `beea1f2b`, repr-b2
`c4d2c45c`. The repr-b2/main ratio includes branch differences; the
same-revision toggle below isolates its store effect.

| Fixed configuration | main CPU / RSS | B+A CPU / RSS | D CPU / RSS | E: batch-1 CPU / RSS | repr-b2 CPU / RSS |
|---|---:|---:|---:|---:|---:|
| ReprRaft | 0.421 / 167.1 | 0.419* / 165.0 | 0.419* / 169.0 | 0.362* / 215.3 | 0.433* / 143.2 |
| ReprRaftAddRemove | 1.219 / 201.4 | 1.217 / 205.8 | 1.221 / 203.9 | 0.931* / 259.7 | 1.210 / 203.8 |
| ReprRaftJoint | 0.284* / 173.3 | 0.284* / 171.4 | 0.284* / 175.3 | 0.328* / 229.5 | 0.287* / 175.8 |
| ReprKRaft | 0.356 / 126.9 | 0.363 / 133.1 | 0.358 / 128.8 | 0.345 / 182.7 | 0.411 / 163.3 |
| ReprPullRaft | 0.526 / 169.1 | 0.531 / 165.0 | 0.536 / 170.7 | 0.522 / 172.7 | 0.584 / 125.2 |
| ReprRaftFsync | 0.444 / 111.1 | 0.435 / 107.1 | 0.439 / 107.1 | 0.364 / 131.3 | 0.475 / 125.2 |
| ReprCCFSingle | 0.160* / 102.9 | 0.163 / 104.9 | 0.162* / 107.1 | 0.161 / 102.8 | 0.169* / 119.6 |
| ReprCCFMulti | 0.227 / 121.8 | 0.229 / 127.1 | 0.213 / 129.4 | 0.228 / 129.1 | 0.259 / 127.4 |
| ReprCCFReads | 0.262 / 131.1 | 0.261 / 127.5 | 0.228* / 129.2 | 0.260 / 127.2 | 0.312 / 131.3 |
| ReprCCFMedium | 0.285 / 107.0 | 0.280 / 105.0 | 0.255 / 107.0 | 0.284 / 109.1 | 0.517 / 93.3 |
| ReprMoveRange | 0.604 / 57.6 | 2.993 / 61.8 | 0.877 / 173.3 | 0.607 / 61.6 | 0.923* / 179.5 |
| ReprMongoReconfig | 0.416 / 106.8 | 0.413 / 106.6 | 0.384 / 108.8 | 0.421 / 106.8 | 1.520 / 119.3 |
| ReprRaftMongo | 0.608 / 141.0 | 0.613 / 145.5 | 0.611 / 142.8 | 0.612 / 145.1 | 2.744 / 78.9 |
| ReprAccordKeys | 0.221 / 149.5 | 0.225 / 153.2 | 0.224 / 155.5 | 0.224 / 153.0 | 0.481 / 89.3 |
| ReprAccordChain | 0.520 / 180.1 | 3.682 / 246.6 | 0.602 / 179.1 | 0.521 / 186.1 | 3.978 / 167.7 |
| ReprAccordLoad | 0.283 / 156.6 | 0.283 / 151.0 | 0.285 / 152.8 | 0.283 / 158.8 | 0.948 / 89.1 |
| ReprZab | 0.445 / 99.6 | 0.451 / 99.4 | 0.453 / 97.4 | 0.444 / 89.3 | 1.287 / 441.9 |
| ReprPaxosCommit | 0.125 / 122.9 | 0.126 / 129.2 | 0.126 / 125.1 | 0.125 / 125.3 | 0.126 / 127.5 |
| ReprBakery | 0.107 / 75.3 | 0.109 / 77.0 | 0.106 / 73.4 | 0.106 / 75.4 | 0.107 / 77.3 |
| ReprLamportMutex | 0.157 / 84.8 | 0.154 / 82.7 | 0.157 / 84.8 | 0.156 / 84.8 | 0.384 / 96.9 |
| ReprKVS | 0.149 / 60.6 | 0.147 / 60.7 | 0.151 / 62.5 | 0.150 / 62.5 | 0.152 / 63.1 |

The five-arm `ab` pass's own record (`small.json`, not part of the released
tree; it carries its own `measurement_command`) retains every sample,
contract comparison, input digest, revision and environment. Its instrumented
companion (`small-stats.json`) retains complete region tables and phase counters.

The next table is diagnostic, not a second timing comparison. B+A counters
are action failures / guard dispatches / background version requests;
they include existing unsupported-operation fallback. Host counts list
main / B+A / D / E / repr-b2 and exclude whole-function closure IR.

| Fixed configuration | main misses / re-encoded | B+A failures / guards / versions | Host calls main / B+A / D / E / b2 |
|---|---:|---:|---:|
| ReprRaft | 0 / 0 | 0 / 0 / 0 | 403,092 / 403,092 / 403,092 / 106,761 / 91,606 |
| ReprRaftAddRemove | 0 / 0 | 0 / 0 / 0 | 555,974 / 556,821 / 533,664 / 314,078 / 285,222 |
| ReprRaftJoint | 0 / 0 | 0 / 0 / 0 | 9,428 / 9,428 / 8,896 / 3,258 / 3,535 |
| ReprKRaft | 0 / 0 | 0 / 0 / 0 | 291,743 / 291,743 / 291,743 / 59,243 / 51,893 |
| ReprPullRaft | 0 / 0 | 0 / 0 / 0 | 30,909 / 30,909 / 30,909 / 30,909 / 23,687 |
| ReprRaftFsync | 0 / 0 | 0 / 0 / 0 | 457,939 / 457,939 / 457,939 / 143,500 / 137,447 |
| ReprCCFSingle | 0 / 0 | 33 / 33 / 0 | 2,585 / 2,585 / 45 / 2,585 / 854 |
| ReprCCFMulti | 0 / 0 | 211 / 211 / 0 | 60,527 / 60,527 / 2,055 / 60,527 / 12,403 |
| ReprCCFReads | 0 / 0 | 339 / 339 / 0 | 111,097 / 111,097 / 3,593 / 111,097 / 22,568 |
| ReprCCFMedium | 0 / 0 | 2,790 / 2,790 / 0 | 94,783 / 94,783 / 9,063 / 94,783 / 63,934 |
| ReprMoveRange | 1 / 911 | 274 / 62,038 / 1 | 1,500 / 2,895 / 1,500 / 1,500 / 6,889 |
| ReprMongoReconfig | 0 / 0 | 0 / 0 / 0 | 141,289 / 141,289 / 0 / 141,289 / 1,214,608 |
| ReprRaftMongo | 0 / 0 | 0 / 0 / 0 | 16,768 / 16,768 / 16,768 / 16,768 / 424,980 |
| ReprAccordKeys | 0 / 0 | 0 / 0 / 0 | 49,240 / 49,240 / 49,240 / 49,240 / 33,012 |
| ReprAccordChain | 2 / 11,556 | 2,516 / 115,029 / 3 | 165,581 / 254,824 / 165,581 / 165,581 / 94,251 |
| ReprAccordLoad | 0 / 0 | 0 / 0 / 0 | 130,918 / 130,918 / 130,918 / 130,918 / 83,054 |
| ReprZab | 0 / 0 | 0 / 0 / 0 | 44 / 44 / 44 / 44 / 13,498 |
| ReprPaxosCommit | 0 / 0 | 0 / 0 / 0 | 0 / 0 / 0 / 0 / 0 |
| ReprBakery | 0 / 0 | 0 / 0 / 0 | 0 / 0 / 0 / 0 / 0 |
| ReprLamportMutex | 0 / 0 | 0 / 0 / 0 | 0 / 0 / 0 / 0 / 95,638 |
| ReprKVS | 0 / 0 | 0 / 0 / 0 | 0 / 0 / 0 / 0 / 0 |

M: all 315 timing samples and 105 instrumented samples complete with zero
contract mismatches. Corrected B+A reduces restarts and queue re-encoding to
zero in all 21 cases. AccordChain requests three versions, reaches the generic
version, and has no pending compiler at termination; MoveRange requests one,
also fully published. All other cases request zero. The action-failure counts
in CCF are inherited unsupported-operation fallback, not additional shape
changes. Nonetheless B+A costs 3.682 / 0.520 = 7.08× on AccordChain and
2.993 / 0.604 = 4.96× on MoveRange. Bounding recompilation is necessary and
works here, but does not bound interpretation, transcoding or symmetry cost.

M: E's small Raft/AddRemove/Fsync CPU ratios are 0.860 / 0.764 / 0.820,
with RSS 215.3 / 259.7 / 131.3 MiB versus 167.1 / 201.4 / 111.1 on main.
JointConsensus instead has a 1.155 CPU ratio and 229.5 versus 173.3 MiB RSS.
Several Raft ranges exceed 5% (marked above), so these are descriptive small
configuration effects, not precise large-model gains. A Dyn-root policy can
help message bags but is not universally cheaper, especially when startup and
extra index memory dominate short searches.

M: pinned repr-b2 is 7.65× on AccordChain, 4.51× on RaftMongo, 3.65× on
Mongo Reconfig, 3.35× on AccordLoad, 2.89× on Zab and 2.45× on LamportMutex,
compared with main on these reduced inputs. Zab RSS is 441.9 versus 99.6 MiB,
so canonical sharing does not automatically imply lower memory. These are
cross-revision comparisons, not pure dispatch attribution. D's reduced Accord
regression is 15.8%, reinforcing the original-model 7.8% regression; reduced
MoveRange is also 45.2% slower, while its original-model ratio is 1.025.
Preserving existing cheap native paths before trying the experimental atom
table is a required next correction (A), rather than assuming every lowering
addition is a gain.

M: state-word reduction alone also predicts neither CPU nor process RSS.
The separate stats pass reports the following final codecs and store storage:

| Fixed configuration | main / b2 state words | main / b2 search elapsed s | b2 store nodes+payloads+index MiB | b2 misses / re-encoded |
|---|---:|---:|---:|---:|
| ReprCCFMedium | 174 / 2 | 0.120 / 0.361 | 1.257 | 0 / 0 |
| ReprMoveRange | 1,826 / 53 | 0.086 / 0.155 | — | 1 / 911 |
| ReprAccordChain | 24 / 17 | 0.187 / 3.558 | 0.004 | 2 / 11,556 |
| ReprZab | 1,218 / 74 | 0.015 / 0.046 | 0.173 | 0 / 0 |

M/A: Zab's 442 MiB uninstrumented process peak cannot be attributed to its
0.173 MiB of recorded store nodes/payloads/index. Compiler and temporary
allocation are plausible contributors (A), but the existing end-of-search
accounting does not isolate them. The RSS result is a process-level cost,
not a measured canonical-arena leak. Partial slot promotion also leaves layout
misses in MoveRange and Accord, so it does not implement A's no-restart property.

## Same-revision store toggle (M)

Both arms below run repr-b2 `c4d2c45c`, changing only `TLX_VALUE_STORE=0/1`;
all use `TLX_PRERUN_REUSE=0`. Three rotating interleaved rounds follow discarded
warmups. Cells are CPU seconds / peak RSS MiB; every contract matches.
CPU ranges are below 2%. This isolates the combined store selection and
execution policy from unrelated branch changes, but not those two components
from one another.

| Fixed configuration | Store off CPU / RSS | Store on CPU / RSS | CPU on / off |
|---|---:|---:|---:|
| ReprCCFMulti | 0.212 / 127.5 | 0.258 / 125.2 | 1.217 |
| ReprCCFReads | 0.227 / 131.7 | 0.309 / 131.8 | 1.361 |
| ReprCCFMedium | 0.255 / 107.1 | 0.513 / 95.6 | 2.012 |

M: these current reduced cases establish extra store-path cost, not the earlier
96/171-second large-model observation on another branch head. The same-head
records and separate operation/slot counters are retained in the `ab` pass's
`store-toggle.json` and its instrumented companion `store-toggle-stats.json`
(neither is part of the released tree).


## Common path without deoptimization (M)

This separate original-configuration pass disables retention in every arm
with `TLX_RETAIN_MB=0`, also confirmed by the absence of archive allocation
in stats. Main is `bfe7daf3`; prototype-off and B+A both use `facd6658`,
changing only `TLX_ESCAPE=1` between the latter two. All have discarded
warmups and three rotating interleaved rounds. Cells are CPU s / peak RSS MiB.

| Original control | main CPU / RSS | Prototype off CPU / RSS | B+A CPU / RSS | B+A / main | B+A / prototype off |
|---|---:|---:|---:|---:|---:|
| PaxosCommit | 5.704 / 137.2 | 5.731 / 133.4 | 5.749 / 133.2 | 1.0079 | 1.0031 |
| MCBakery | 1.475 / 165.0 | 1.456 / 165.3 | 1.468 / 155.2 | 0.9953 | 1.0082 |
| MCLamportMutex | 2.339 / 92.8 | 2.345 / 92.9 | 2.343 / 93.0 | 1.0017 | 0.9991 |
| MCKVSSafetySmall | 11.375 / 255.0 | 11.308 / 255.2 | 11.347 / 247.0 | 0.9975 | 1.0034 |

M: all 36 timing samples and 12 stats samples have matching contracts.
Every B+A control reports zero action failures, guard failures, version
requests, irreversible-action interpretation and ordinary action fallback.
CPU ranges are below 0.8%. B+A is within 0.8% of main in these four cases;
its increment against the same binary with the switch off is −0.1% to +0.8%.
The common-path obligation is supported here at the 1% level, not proven
as a literally zero-cycle guard or a bound for every model. In particular
it says nothing about escaped symmetry or predicate fallback.
The `ab` pass's `guards.json` and its instrumented companion
`guards-stats.json` (neither is part of the released tree) retain the samples and
native/fallback counters.

## Interleaved original-model comparison (M)

This pass compares main `bfe7daf3` with the initial B+A and D prototype
`beea1f2b` on one AMD EPYC 9754 instance. Each model has a discarded warmup
and three rotating interleaved rounds, `-compile -workers 1 -tlc`, with
`TLX_PRERUN_REUSE=0` for every arm. Cells give median process CPU seconds /
median per-process peak RSS MiB. Ratios use CPU medians. All completed pairs
match result, violated names, generated/distinct counts, depth and trace length;
MoveRange B+A is censored in all three rounds at the 180-second wall limit.
No whole-model compilation fallback was reported. The complete samples,
input digests, per-arm revisions and contract checks are in the `ab` pass's
`large.json` (not part of the released tree).

| Original configuration | main CPU / RSS | B+A CPU / RSS | D CPU / RSS | B+A / main | D / main |
|---|---:|---:|---:|---:|---:|
| standard-raft-Raft | 4.876 / 203.7 | 4.749 / 201.7 | 4.720 / 203.3 | 0.974 | 0.968 |
| pull-raft-PullRaft | 6.536 / 244.9 | 35.949 / 169.9 | 6.693 / 247.7 | 5.500 | 1.024 |
| MCMultiNode | 36.277 / 279.4 | 34.452 / 237.5 | 6.172 / 234.4 | 0.950 | 0.170 |
| MCMultiNodeReads | 65.847 / 387.5 | 63.828 / 297.5 | 10.903 / 355.5 | 0.969 | 0.166 |
| MCMoveRange | 11.773 / 274.1 | timeout ×3 / partial | 12.063 / 252.3 | — | 1.025 |
| MCMongoReplReconfig | 32.059 / 396.9 | 32.069 / 345.0 | 29.418 / 395.3 | 1.000 | 0.918 |
| MCRaftMongo | 14.250 / 151.2 | 14.266 / 145.4 | 14.302 / 155.4 | 1.001 | 1.004 |
| Accord_baseline__deep_chain | 3.640 / 225.5 | 131.157 / 105.6 | 3.924 / 209.9 | 36.032 | 1.078 |
| MC_tlx_Zab_new | 31.021 / 553.2 | 163.496 / 218.2 | 31.208 / 552.8 | 5.270 | 1.006 |
| PaxosCommit | 5.825 / 173.0 | 5.751 / 137.1 | 5.909 / 173.1 | 0.987 | 1.014 |
| MCBakery | 1.488 / 164.9 | 1.468 / 155.0 | 1.484 / 165.2 | 0.987 | 0.997 |
| MCLamportMutex | 2.439 / 118.6 | 2.326 / 92.7 | 2.450 / 118.8 | 0.954 | 1.005 |
| MCKVSSafetySmall | 11.501 / 305.2 | 11.420 / 247.1 | 11.566 / 305.2 | 0.993 | 1.006 |

M: D reduces MultiNode CPU 36.277 → 6.172 s (5.88×) and Reads
65.847 → 10.903 s (6.04×); every corresponding CPU range is below 1%.
Mongo Reconfig improves by 8.2%. Accord instead regresses by 7.8%, with
less than 1% range. The experimental atom-table path currently precedes
existing native enum lowering; preferring the established cheap path is a
plausible correction (A), but this experiment does not measure that correction.

M: B+A is 5.50× slower on PullRaft and 36.03× on Accord; MoveRange never
completes within the bound. Standard Raft B+A and PullRaft B+A have 6.7% /
5.9% relative CPU ranges, so their median ratios are descriptive rather than
precise small-effect conclusions. The old Zab B+A row also exposes the
overly broad Print-only interpreter guard; a corrected revision is measured
separately below rather than silently replacing this negative result.

M: B+A disables the resume archive because its external codec cannot widen.
The lower RSS in this table therefore includes a different archive policy;
it does not demonstrate that the escape slots themselves use less memory.
The isolated guard comparison disables retention in every arm.

M: the separate instrumented pass explains why eliminating restarts is not
sufficient. PullRaft's fingerprint elapsed estimate grows from 1.298 to 22.863 s,
encoding from 0.303 to 3.323 s, and search from 6.692 to 36.568 s. Escaped
symmetry currently reconstructs and permutes complete value states. Accord has
1,390,185 interpreter predicate calls and 117.768 s estimated predicate
interpreter time with B+A, compared with 0.010 s on main. Both request three
versions and stop requesting more; the dominant failure is execution cost,
not an unbounded compilation storm. These sampled elapsed estimates overlap
other timers and are not CPU percentages.

M: MultiNode D changes estimated predicate execution from 21.058 s closure IR
and 8.510 s mixed to 0.001 s closure IR and 1.147 s mixed; its native predicate
estimate grows from 0.812 to 1.448 s. This is the whole-function tier change
that the initial host-operation table could not expose as a CPU budget.
B+A's 120,813 action failures on MultiNode are also present in main, and cause
no shape recompilation; they must not be described as 120,813 newly introduced
layout failures. Full initial/child region sections and function paths are
retained in that pass's instrumented `large-stats.json` (not part of the released
tree).

## Original-model diagnostics (M)

These are separate single instrumented samples. "Failures / guards / versions"
is B+A's action-failure counter / guard-dispatch counter / version requests.
The counters include inherited unsupported compiled operations; they are not
counts of newly introduced state-shape failures. Host calls include every
published version's mixed-region table, but exclude whole-function closure IR.
Every completed B+A sample has zero layout restarts and zero queued-state
re-encodings. D retains main's restart/re-encoding behavior.

| Original configuration | main misses / re-encoded | B+A failures / guards / versions | Host calls main / B+A / D |
|---|---:|---:|---:|
| standard-raft-Raft | 0 / 0 | 0 / 0 / 0 | 1,679,957 / 2,226,595 / 1,679,969 |
| pull-raft-PullRaft | 5 / 3,778 | 16,909 / 1,255,474 / 3 | 3,322,989 / 8,741,560 / 6,605,937 |
| MCMultiNode | 0 / 0 | 120,813 / 120,813 / 0 | 18,819,866 / 18,290,508 / 2,196,582 |
| MCMultiNodeReads | 0 / 0 | 199,453 / 199,453 / 0 | 31,016,538 / 25,861,269 / 3,935,899 |
| MCMoveRange | 9 / 58,603 | censored | 196,651 / — / 196,651 |
| MCMongoReplReconfig | 0 / 0 | 0 / 0 / 0 | 20,867,354 / 20,867,354 / 0 |
| MCRaftMongo | 0 / 0 | 0 / 0 / 0 | 22,752 / 27,232 / 27,232 |
| Accord_baseline__deep_chain | 3 / 248,751 | 20,461 / 2,168,964 / 3 | 5,875,643 / 5,278,504 / 5,875,643 |
| MC_tlx_Zab_new | 0 / 0 | 0 / 0 / 0 | 209,796 / 0 / 209,796 |
| PaxosCommit | 0 / 0 | 0 / 0 / 0 | 0 / 0 / 0 |
| MCBakery | 0 / 0 | 0 / 0 / 0 | 0 / 0 / 0 |
| MCLamportMutex | 0 / 0 | 0 / 0 / 0 | 0 / 0 / 0 |
| MCKVSSafetySmall | 0 / 0 | 0 / 0 / 0 | 0 / 0 / 0 |

M: PullRaft D reports more mixed-region calls while CPU stays close to main:
adaptive tier choice moves work out of whole-function IR, where those calls
were not counted. Conversely Mongo Reconfig D removes all 20,867,354 reported
host calls but improves CPU only 8.2%, because symmetry and other native work
remain. Host-call counts alone are therefore not a performance objective.

## Corrected original Zab (M)

This new three-round comparison measures corrected B+A `facd6658` against the
same main and D pins on the final instance; the earlier negative row is retained
above with its original revision. CPU ranges are below 0.9%, all nine timing
samples and three stats samples have matching contracts. Cells are CPU seconds /
peak RSS MiB. B+A has zero deopts, guard failures, version requests and
irreversible-action interpretation, while Print-only actions remain native.

| Original configuration | main CPU / RSS | B+A CPU / RSS | D CPU / RSS | B+A / main; D / main |
|---|---:|---:|---:|---:|
| MC_tlx_Zab_new | 30.987 / 552.7 | 30.730 / 226.7 | 30.925 / 553.3 | 0.992 / 0.998 |

The corrected 0.992 B+A/main ratio removes the earlier 5.270 regression.
This is an implementation correction to Print-only fallback, not evidence that
escaped symmetry became cheap. B+A still disables the resume archive, so its
lower RSS includes that policy. The raw measurements are in the `ab` pass's
`zab-corrected.json` and its instrumented companion `zab-corrected-stats.json`
(neither is part of the released tree).

## Original Raft store comparison (M)

This pass compares main and batch-1 E in the same `bfe7daf3` binary, plus pinned
repr-b2 `c4d2c45c`, with three rotating interleaved rounds after warmups. All 18
timing samples and six diagnostic samples have matching contracts. Cells are
CPU seconds / peak RSS MiB. CPU ranges are below 3.8%.

| Original configuration | main CPU / RSS | E: batch-1 CPU / RSS | repr-b2 CPU / RSS | E / main; b2 / main |
|---|---:|---:|---:|---:|
| pull-raft-PullRaft | 6.593 / 246.4 | 4.077 / 167.0 | 6.566 / 114.1 | 0.618 / 0.996 |
| standard-raft-Raft | 4.664 / 202.9 | 2.366 / 133.0 | 4.617 / 135.7 | 0.507 / 0.990 |

E saves 49.3% / 38.2% CPU and about 34% / 32% peak RSS here. These larger
message-bag cases support selective storage even though some reduced cases pay
more startup/index memory. Current repr-b2 is essentially CPU-neutral against
main in these two cases, with lower RSS, but does not retain E's CPU gains.
The cross-revision b2 comparison is an end-to-end result, not isolation of its
operator path. Raw samples/counters are in the `ab` pass's `raft-stores.json`
and its instrumented companion `raft-stores-stats.json` (neither is part of the
released tree).

## Replacement medium attribution and current store profile (M)

`MCMultiNodeReadsNotLinearizable` replaces the censored CCF configuration.
It runs main `bfe7daf3`, not the earlier `17dcf775` attribution binary, so its
figures are separate rather than added to that earlier total. The uninstrumented
sample is 6.636 CPU seconds / 223.2 MiB peak RSS; its separate instrumented pass
reports 0.027 s pre-run, 0.004 s lowering/generation and 6.995 s search, zero
layout misses/re-encodings, and no root Dyn slots. Final host regions contain
803,698 calls / 0.190 s: map construction 602,198 / 0.085 s, membership
201,500 / 0.105 s. The sampled CPU leaders include encoded fingerprinting
(12.1%), layout decoding (3.4%) and queue XOR encoding (3.15%). These are
single-pass diagnostics with the same elapsed/whole-function-IR limits as the
initial table.

Its safety verdict `AllCommittedObservedRoInv`, 2,362,986 generated states,
1,468,921 distinct states and depth 12 match the existing TLC correctness cache.
The measured tlx trace has 12 states; the cached oracle has no trace-length
field, so that length is retained without claiming a fresh TLC trace comparison.
No TLC timing was recollected. Full profile metadata, cached-contract checks
and raw attribution are in the `profile` pass's `medium-profile.json` (it carries
its own `measurement_command`) and its instrumented `medium-stats.json`; neither
is part of the released tree.

The current repr-b2 profile uses the fixed reduced CCF medium, with the store
explicitly enabled and pre-run reuse disabled. It has 3,990,106 native-to-store
operation calls on `history` and `ledgerBranches`. The leading operations are:

| Store operation | Calls |
|---|---:|
| Apply | 1,765,220 |
| Domain | 578,086 |
| Field(tx) | 569,620 |
| Member | 281,048 |
| Len | 216,937 |
| Field(type) | 198,561 |

The separate same-head stats pass has search elapsed 0.357 s store-on versus
0.085 s store-off; Multi/Reads similarly have 0.065/0.011 and 0.112/0.019 s.
These instrumented search ratios are roughly 4.2–5.9, while startup dilutes the
three-round whole-process CPU ratios to 1.22–2.01. This is not a large-model
store timing result. The current short sampled profile identifies RefOpTable
`run` (~8%), Ref operation `run` (~6%), native Ref callback (~4%), `Fn::val`
(~2%) and intern (~2%) among flat samples. Parser and startup symbols also
appear prominently: the uninstrumented sample is only 0.494 CPU seconds, so
these percentages are coarse diagnostic clues, not precise cost budgets.
Together with the deterministic call counts and same-revision A/B, they support
prioritizing typed/direct access and dispatch before another interner rewrite;
they do not prove that dispatch alone explains the entire loss. The current
profile is retained in the `profile` pass's `store-profile.json` (it carries its
own `measurement_command`) and its instrumented `store-stats.json`; neither is
part of the released tree.

## Next B+A experiment (A)

The next version should share one external slot-access ABI across compiled
versions. An action first tests its read-set against escape metadata, then
loads inline words directly or guards/decodes only the escaped slots it uses.
Unchanged slots retain their original payload and escape handles. A wider
specialization must not decode and re-encode an entire input and every successor.
Escaped fingerprinting also needs escape-aware permutation plans: keep the
compiled word permutation for unaffected inline slots and cache transformations
of canonical escaped values by value ID and permutation ID. Reconstructing and
permuting an entire value state defeats cached per-value digests.
Predicates need the same version dispatch as actions; making every predicate
interpret an escaped state defeats native execution even when only one unrelated
slot changed.

The current three-request cap bounds compilation storms, but the final generic
choice should be per slot or expression rather than making every variable Dyn.
The initial version should remain available for the original shapes, with a
small version cache and a code-size budget. Queue metadata can also be packed:
a bitmap plus an overflow-index handle needs approximately
`ceil(variables / 64) + 1` words instead of one overflow word per variable, at the cost of an extra
lookup on escaped accesses. This is a design estimate, not a measured replacement.

Counters should distinguish actual escape-tag failures and new-shape failures
from pre-existing unsupported compiled operations. The prototype's action
failure counter includes the latter; guard counts also include dispatch into
an already published version. Predicate interpreter calls and per-function
execution paths must be inspected separately. Correct verdicts and zero state
re-encodings alone do not establish that execution remained native or became
faster.

## Recommendation and build order (A, grounded in M above)

First, productionize D's proven native gaps. Typed-atom membership and lowered
powerset membership give 5.88× / 6.04× on the original CCF cases and 8.2% less
CPU on Mongo Reconfig without a representation change. Preserve established
cheap native paths before the experimental truth table, and address the
measured Accord regression before enabling it broadly. Follow with sorting,
quantifier and bag operations only when full function-path profiles show that
they keep a whole function in IR or dominate the remaining host work. This is
the lowest-complexity route to measured CPU savings.

Second, keep the immutable value arena as a selective component and narrow
promotion to demonstrably profitable Dyn/escape slots. Batch-1 E's Raft gains
justify retaining that path, with an explicit RSS budget. A sequence, a map
larger than eight words, or a smaller encoded state is not sufficient evidence
that promotion is cheaper: current repr-b2 loses 22–101% in the same-revision
CCF toggle, and loses substantially more in several cross-revision reduced
comparisons. Promotion should consider native operations already available,
read/write frequency, sharing/reuse, symmetry and total compilation/storage
cost. The pinned branch already has a selective policy; this recommendation
narrows and measures that policy rather than describing it as an all-root store.

Third, continue the JS-style B+A direction on a stable slot-access ABI, with
read-set guards, escape-aware permutation plans, predicate/expression versions
and unchanged-slot inheritance as described above. The experiment establishes
cross-form fingerprint consistency, action-local execution fallback, bounded
three-request compilation, and below-1% common-path cost on four original
controls. Its current whole-state transcoding, global input escape guard and
interpreted predicates make it unsuitable for broad enablement: zero restarts
coexists with 5.50× / 36.03× original-model regressions and censored MoveRange.
Keep the prototype behind its switch as a correctness and performance test bed;
use those negative cases as acceptance workloads for the next implementation.
Production work also needs reclamation, explicit checkpoint/recovery support,
code-size limits and safe handling of irreversible actions.

C should support that architecture through recursively shared escaped values,
cached semantic digests, bounded pure-operation memoization and cached value
permutations. Existing Dyn root IDs already provide constant-size encoded
state equality/fingerprints; replacing their interner alone addresses little of
the observed IR/dispatch cost. Logical TLA+ operations still need compatibility
and deferred-error guards, rather than treating every unequal pair of IDs as a
safe logical inequality.

The store work should continue for canonical storage, correctness-tested pure
operators and the generic escape path. Pause expansion of general Ref operator
lowering until the current read/dispatch and promotion costs are controlled;
carry useful native operations into the guarded hybrid ABI instead of requiring
all hot inline operands to traverse it. D and B+A solve different measured
problems and should share lowering infrastructure. The present evidence supports
that staged combination, not a representation-wide rollout of either prototype.

## Reproduction and evidence

M: none of the raw measurement artifacts or pre-consolidation prototype branches
this document names is part of the released tree. The six prototype commit SHAs
(`17dcf775`, `bfe7daf3`, `beea1f2b`, `facd6658`, `bbaf9920`, `c4d2c45c`) and the
raw JSON artifacts under `bench/repr-alternatives/`, `work/notes/`, and
`bench/migration.json` came from the pre-`v0.1.0` design survey archived before
repository history was rooted at `5dc582bde9`; they are historical provenance
identifiers rather than live checkout paths or reachable commits in this
repository ([DOC-06](../development-standards.md#doc-06)). During that survey, each
artifact recorded one `scripts/bench.py ab` or `profile` pass, a correctness or
verification campaign, or the command manifest on its named prototype revision.
Current benchmark lanes, canonical store layout (`bench/records/`,
`bench/tlc-baselines/`) and reproduction rules on `main` are owned by
[benchmarking.md](../benchmarking.md) and [bench/README.md](../../bench/README.md).

M: in that pre-consolidation survey, the original attribution ran code and profile driver `17dcf775`.
The large comparison ran main `bfe7daf3`, with both prototype switches in
`beea1f2b`. The final small comparison used corrected B+A `facd6658`,
D `beea1f2b`, main `bfe7daf3` for both the baseline and batch-1 hybrid,
and repr-b2 `c4d2c45c`. The latter was a separately developed branch, so its
ratio against main included unrelated compiler changes. A same-revision
store-off/store-on diagnostic separated the store toggle from those changes.
Every arm disabled pre-run result reuse; timing used one worker and TLC mode
unless explicitly labeled as the default-mode supplement. Each timing table
used three complete interleaved rounds after discarded warmups; instrumented
counter tables used separate single passes.

M: the committed verification artifact records 937 passing Rust tests,
zero failures and seven ignored tests from
`cargo test --profile test-release -q --no-fail-fast`. Both experimental
switches pass interpreter, compiled and paranoid spectest modes: each run has
441 contract judgments, comprising 434 passes and seven expected failures.
Release build and workspace release Clippy finish without warnings. The
production prototype Rust code in `facd6658` is the same as the corrected
code tested in `bbaf9920`; intervening changes repair deadline-test readiness
and the measurement driver. The readiness regression also passes 500 runs
of three cancellation cases, 1,500 tests with zero failures, preserving the
20-millisecond post-readiness deadline. Full commands, source revisions and
logs' summaries are in the verification artifact
(`state-representation-alternatives-verification.json`, not part of the released
tree; it records the command, revision and exit status of every step above).
These correctness checks do not establish a performance effect.

M: the command manifest (`state-representation-alternatives-commands.json`, not
part of the released tree) records the
exact cloud launch argument arrays and every benchmark pass, alongside the
original attribution command. AB artifacts retain per-arm arguments and
switches, input digests, individual CPU/RSS samples and contract checks.
Canonical measurements are imported into `bench/records/`; the public report
and report policy are regenerated together rather than hand-editing results.

M: the optional default-mode supplement reached its deadline after 16 complete
samples and one censored sample; the remaining 55 samples were skipped.
No model/arm group completed all three requested rounds. The 16 complete
samples have no verdict/violated-name mismatch against the corresponding main
sample, but this is not a three-pair performance result. Its checkpoint is
retained in the `ab` pass's `default-censored.json` (not part of the released
tree).
All 24 later default stats samples and all six capped large store samples were
skipped for lack of remaining time. These provide no store timing evidence.
The old summary driver also divided by skipped zero-time rows when reusing TLC
baselines, so it failed before writing the final default files; a red-to-green
regression now requires both implicit and explicit baseline paths to preserve
incomplete evidence and suppress incomplete ratios. All 75 benchmark harness
tests pass after the fix. The final campaign includes that fix.

M: a final report audit found that the single-pass ordinary CPU sample embedded
in a diagnostic profile could enter the default public performance table.
Diagnostic profile headers are now explicitly marked; raw `-stats`/`raw_stats`
samples receive the same canonical category, and public eligibility rejects
that category while retaining every metric. The normalization regression
covers explicit diagnostic metadata, legacy profile headers, raw stats and the
stats argument; the profile writer regression also requires its diagnostic flag.
All 76 benchmark harness tests pass.
