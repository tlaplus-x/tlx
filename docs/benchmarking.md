# Benchmarking

This document owns how tlx's performance numbers are produced: the benchmark driver
`scripts/bench.py`, the suite of record and its continuous tracking, the TLC timing baselines and
their reuse, and the measurement schema behind the generated [performance.md](performance.md)
report.

Where a measurement may run at all - which machine, what stays local - is owned by
[cloud-verification.md](cloud-verification.md) section 1: benchmarks of record are a cloud job,
local reduced runs are diagnostics, and a shared machine is never loaded artificially.

## 1. Benchmarks: `scripts/bench.py`

The public performance report is [performance.md](performance.md), generated only from the
measurements in the current benchmark store (`bench/records/`, section 6.2), which ships with
the sources. Record via the suite, never ad hoc. Benchmarks of record run on the cloud; local
reduced runs are diagnostics. Use release binaries.

```sh
python3 scripts/bench.py suite-check --oracle
python3 scripts/bench.py track --dry-run
python3 scripts/bench.py track
python3 scripts/bench.py report
python3 scripts/bench.py report --check
```

The fixed report covers default end-to-end runs, compiled execution, external industrial
models, liveness, trace replay, worker scaling, memory pressure and the interpreter. It lists
missing modes and missing/stale TLC baselines. Every number is named by the record behind it:
the Evidence column carries that record's revision, instance, date and store file, as text
as a link that resolves in a fresh clone (section 6.2); unknown provenance stays unknown. The
report states its timing conditions next to the numbers - a tlx time is the median of the timed
samples, each a separate process run after the discarded warm-up of section 1, which is not a
cold-cache measurement - and its `tlx optimizations` column carries the optimization the recorded
samples name, so a row whose tlx run was reduced says so (the summary counts the rows that record
one; `none` requires every sample to record an empty list, and a sample without the field is
`unknown`). Historical markdown is retained as source material and is
not updated. `bench.py table` now regenerates the fixed report without running measurements.

The report publishes peak resident memory beside time: `## Summary` carries each cohort's
`Median TLC / tlx RSS` and `RSS range`, and every per-model table pairs the tlx row's `RSS MiB`
with the baseline's `TLC RSS MiB` and the `TLC / tlx RSS` ratio. Both sides are the stored
`metrics.rss_mib` (the median of that run's finite positive timed samples), so a ratio is
published only when both records carry a positive measurement; a missing or zero value stays
`—`, never a zero-byte footprint. The import, the report and `history-report` share that reader,
so a legacy history's timed `samples[*].maxrss_mib` and a `tlcbase` run's scalar `maxrss_mib`
name the same statistic.

A default-mode row can apply automatic symmetry, so its ratio compares a reduced search with TLC's
unreduced one. When the store also holds a same-instance unreduced twin - an eligible tlx `-tlc`
record (or an eligible `-compile` record passing `-tlc` with `configuration.compatibility` true)
with the same model, revision, instance type and architecture, worker count, input digest,
TLC version, remaining configuration (arguments without `-tlc`, environment and memory limit) and
recorded cache provenance - the per-model tables gain `-tlc twin s` and `-tlc / default` columns:
the twin's timed wall time (cited in the row's Evidence) and the factor by which the reduced run
was faster on the same machine.
The pairing fails closed: a row whose machine type, architecture, input digest or cache provenance
is unknown is not paired, because a ratio across unknown hosts, inputs or cache regimes is not
quotable. The TLC ratio beside them is unchanged: it still compares the reduced run with TLC's own
run, and neither number is inferred when the store holds no twin (`—`). A store without companions
renders the report exactly as before; section 4 owns how a run is collected.

New TLC baselines can collect repeated process runs, for example on a cloud instance:

```sh
python3 scripts/bench.py tlcbase --models DieHard/DieHard --workers 1 --tlc-repetitions 3
```

A complete set stores raw `tlc_samples`, median wall/CPU times, and
`provenance.sample_spread` (`wall_s` and `cpu_s`, each range divided by median;
null for missing or zero CPU time). Every sample must finish with a valid exit
and agree on verdict and violated property; counts must also agree for single-worker
runs and successful searches. Incomplete or inconsistent sets cannot become reusable
baselines or enter timing totals/distributions. Rejected sets keep all attempts and
use `aggregation: last-attempt`; their scalar timing preserves the terminating
attempt (including its actual timeout bound). Missing resource metrics display
as unavailable. Samples are sequential and each uses the existing deadline admission.
An existing valid key is always reused, even if it has only one sample; requesting
more repetitions alone never replaces frozen evidence. Passing `--min-repetitions N`
(default `1`) on `tlcbase` treats reusable baselines with fewer than `N` completed
samples as unsatisfied so callers (for example `--min-repetitions 3 --tlc-repetitions 3`)
can upgrade legacy 1-sample records without discarding valid evidence if collection fails.
Ingesting a history reference to
a reusable baseline preserves the canonical row and its raw samples byte for byte.
Use a new input/tool/hardware key
for new measurements. Historical scalar records remain valid.

`suite`, `track` and repeated `run` measurements support `--isolate-cache` (option
reference: [configuration.md](configuration.md)). Each configuration gets
an empty temporary `TLX_CACHE`; suite A/B binaries get separate caches. It lasts
through that configuration's samples, any `run --stats` diagnostic, and, for suite,
its discarded warm-up, then
is removed. Isolated runs use synchronous native compilation so builds finish
before cleanup. Timed suite samples therefore follow a warm-up even in this mode;
`run` has no discarded warm-up, so its first sample starts with an empty cache.

New rows from these runners carry `provenance.cache`: `mode` is `fresh-per-model`
for isolation, `inherited` for an explicit environment cache, or `shared-batch`
for the default shared cache. `initial_state` is `empty` only for isolation and
`unknown` otherwise; `warmup` states whether a discarded warm-up was scheduled.
These are collection conditions, not claims that every timed access is a cache hit.
Legacy rows omit this field. Cache provenance does not change historical keys or
rewrite the frozen 2026-10-11 snapshot.

Benchmark measurements captured with `wait4` (including suite warm-ups) own a new process group. On timeout,
cancellation or capture completion, the runner kills remaining members of that group before
starting another run; compiler descendants must not outlive their checker and contaminate the
next measurement. The capture layer never adopts a PID found by process listing or signals the
caller's group. Child `wait4` accounting and the immediate-kill timeout policy are unchanged.
The disk sampler has its separate cgroup-aware lifecycle.

Other subcommands (details in the script header):

```sh
scripts/bench.py tiers                               # tiers and chosen models
scripts/bench.py run --tlc                           # every tier with tlx, TLC measured on the same machine -> bench/history/<commit>.json
scripts/bench.py report                              # regenerate the fixed public report
scripts/bench.py history-report <commit>              # inspect one historical file on stdout (wall, CPU and RSS speedups)
scripts/bench.py compare <A> <B> --metric cpu        # regression check between two history files
scripts/bench.py ab --bin a=PATH --bin b=PATH --models X,Y --repeat 10
                                                     # interleaved A/B of two tlx binaries (min/median CPU and wall, peak RSS)
scripts/bench.py layout --bin a=PATH --models X,Y    # compiled-tier start-up decisions (pre-run, layout misses, restarts)
scripts/bench.py release v0.1.2 --report-only        # the cross-release comparison from the store (section 7)
```

`compare` has three outcomes: **PASS** (exit 0), **REGRESSION** (exit 1), and
**INCONCLUSIVE** (exit 2). It compares the minimum time with the fixed relative threshold
(`--threshold`, default 5%) and absolute slowdown (`--min-delta`, default 0.05 s). Noise never
raises that threshold. Each row reports A/B noise estimates: `(max - min) / min`, including
isolated slow samples. Noise above `--max-noise` (default 5%), fewer than three complete samples,
unequal sample counts, missing run keys or metric samples, and unfinished runs are inconclusive.
CPU comparisons require CPU samples; they do not substitute wall time for missing CPU data.
Historical one- or two-sample records, including `run --tlc`'s single TLC measurement, remain
readable but cannot establish a conclusive timing comparison.
Only conclusive timings contribute to the per-tier geometric means. Changed distinct counts
remain regressions regardless of timing noise; a proven regression takes precedence over
inconclusive timings in the overall exit status. For example, `[1,1,1]` versus `[2,10,10]` seconds
has a minimum ratio of 2 and B noise of 400%, and is inconclusive rather than passing.
Re-run inconclusive comparisons on an unloaded machine with at least three repeats, preferably
interleaving A/B (`ab`) - anything large belongs on a cloud instance, per
[cloud-verification.md](cloud-verification.md) section 1; inspect intermittent slow paths if the
noise persists. The load warning remains explicit because variation alone cannot distinguish
machine contention from program behavior.

The **stress** tier is a fixed algorithmic selection, included in the default `run` tiers and
listed by `tiers`. It always retains both configurations, regardless of TLC time or `--per-tier`:

- `bench/ClockSettles`: the pinned TLC regression suite's `LiveHourClock.tla`, with
  `bench/stress/ClockSettles.cfg` checking `ClockSettles` (12 clock values). This stresses the
  liveness tableau even though the state graph is tiny. The config excludes the suite's
  postcondition asserting a particular counterexample, since equally valid lassos may differ.
- `MultiPaxos-SMR/MultiPaxos_MC`: the full Examples configuration (about 37 million states),
  exercising late layout misses and restart/resume costs beyond the small variant.

Fetch the pinned suite with `python3 scripts/fetch-external.py --repos tlaplus-tests`
([testing.md](testing.md) section 6.4). Both cases default to compiled mode with one worker.
They are refused on the shared machine: measure them separately on a cloud instance, which is
where an algorithmic-performance investigation runs:

```sh
python3 scripts/cloud_verify.py --bench "run --tiers stress --repeat 3 --stats --tlc --timeout 1800"
```

`--stats` records the phase breakdown and layout/restart counts; for layout changes, compare
states expanded, restarts and resumed searches as well as time. These configurations can also be
selected by `--models`. Without a cached ordinary-corpus oracle, use `--tlc` to check results on
the same machine; `tiers` displays such TLC times as unmeasured rather than omitting the case.

Two more fixed liveness configurations (`bench/stress/<NAME>.cfg` on a corpus spec) are selected
only by `--models`, not by the stress tier; TLC takes hours on them, so the `liveness` lane
(above) measures the tableau instead of a whole-model TLC run:

- `bench/RaftMongoT4`: MongoDB's `MCRaftMongo` (external corpus) with four election terms, 1.57M
  states and 15M edges under nine leads-to properties and strong fairness.
- `bench/ReplicatedLog4x3`: `FiniteMonotonic/MCReplicatedLog` with four nodes and three
  transactions, whose 12 `<>[]` assumptions make a 2^13-state tableau as one formula.

External corpus ([testing.md](testing.md) section 6.3; ids `ext/<repo>/<name>`):
`run --external small,medium` selects the
manifest tiers as bench tiers `ext-<tier>` (`--models` narrows them); `--workers 1,max` and
`--tlc-workers 1,max` set the worker counts, `--tlc-timeout` TLC's timeout, and `--resume` skips
runs already in the history file, so several invocations (e.g. `--modes compile` with TLC, then
`--modes interp` with fewer repeats) fill one file. Models without a TLC oracle result are checked
against the TLC runs of the same file (result kind; distinct states of complete searches).
A model whose input is a tracked wrapper around a pinned upstream module (`bench/stress/*.tla`) is
staged by the driver beside a copy of the upstream module under `target/bench-models/`, so the shared
external checkout stays untouched; the wrapper's extra constraint must be invariant under the
model's symmetries, or the counts stop being comparable.

`history-report FILE --markdown` prints the per-model table, geometric means per tier and per TLC time
bucket, and the models where `-compile` 1w is less than 3x faster than TLC. Without `--markdown`,
it prints the geometric-mean `wall`, `cpu` and `rss` speedups per tier and mode; `rss` is TLC peak
RSS over tlx peak RSS, and `-` marks a row whose history or TLC entry records no measurement. The
cloud instances receive `third_party/external` (`cloud_verify.py --bench "run --external ..."`, see
[cloud-verification.md](cloud-verification.md) section 3).

Time to first result: `ttfr --bin base=OLD --bin new=NEW [--once base] [--external small]
--tlc-baseline FILE [--lanes N]` measures every corpus model with `tlx check` as a user runs it
(no tier flag, `-workers 1`), cold (empty `TLX_CACHE`) and warm, against TLC `-workers 1` measured on
the same machine through the canonical keyed baseline store, and
gives the models where tlx is slower or within 10% a `-stats` run for the phase breakdown; `--once`
binaries run once (a default tier without a native cache). `ttfr-report FILE` imports the raw measurements and regenerates `docs/performance.md`. Output
`bench/ttfr*.json` is rewritten after every model; cold/default and warm-cache records remain distinct.
`cold` is the first run with an empty native cache (`TLX_CACHE`) and `warm` the minimum of the runs
after it; a tlx run is cut off at `max(2.0 × TLC, 20 s)`, so an entry at the cut-off is a lower
bound, never a time.

Three further lanes have their own rules, without which their numbers are not readable:

- **`disk`** (`scripts/benchmarking/bench_disk.py`; its module doc lists the plan items). The unit is `P`, tlx's
  in-memory peak RSS of the model. `-maxmem F×P` limits tlx's own budget and leaves the page cache
  free; a control-group limit of `F×P` (`memory.max`, page cache included, no swap) models a machine
  with that much memory. Under the same limit TLC gets `-Xmx F×P/2 -XX:MaxDirectMemorySize F×P/4`
  with its disk fingerprint set and disk queue, so the comparison is at equal memory, not at equal
  flags.
- **`liveness`**. The models are scratch clock specifications (one initial state, a ring of `n`
  states, stuttering and weak fairness, `ClockSettles` over `n` atoms). A separate construction
  probe compiles each revision's tableau source verbatim with the same shared interner, so
  construction cost is compared without a whole-model run. Peak RSS comes from `wait4`, every
  model/probe run is limited to 60 s by default (`--timeout`), and the probe and the whole model get different address-space caps; a
  run stopped by its limit is an incomplete sample, not a time or a completed peak allocation.
  Compare revisions within one phase — probe against probe, release binary against release binary —
  never probe against whole model: they are different compilations.
- **`profile`**. `perf stat` gives whole-run counters and `perf record` a flat per-symbol profile;
  the comparison is between symbols whose samples per state grew, not between total percentages.
  Profiler percentages are inclusive and overlap, so they must never be added.

`ab` accepts `--env b:K=V` (a variable for one binary only; the same path may be given under two
names to compare an option) and `--hog N` (N spinning processes during the runs, to measure an
oversubscribed machine - a cloud-instance measurement; creating that load locally is prohibited,
[cloud-verification.md](cloud-verification.md) section 1). `table` is a compatibility alias for
the generated report. To
measure the cost of the `-stats` hooks, build `cargo build --release -p tlx-cli --features
no-stats` and `ab` it against the default build.

Micro-benchmarks of hot paths (value fingerprints, TLC order comparison, layout encode/decode,
`fp_words`) compare two builds on one machine; they are not records:
`cargo run --profile test-release -p tlx-testkit --features models --bin microbench [name] [batches]`.

## 2. Multi-core scaling: `scale` and `scale-report`

The table's models finish in 0.2–1.3 s at 16 workers, too fast to show scaling. `scale` runs large
models (≥ 2·10^7 distinct states) at a list of worker counts with tlx `-compile` (default tiering,
warm cache) and TLC:

```sh
scripts/bench.py scale --workers 1,16,64,128,max --tlc-1w dijkstra-mutex/DijkstraMutex.toolbox/Safety-4-processors/MC
scripts/bench.py scale --models bench/MCLamportMutex_clock14 --workers 1,16 --no-tlc   # tlx only (sizing)
scripts/bench.py scale-report bench/history/scale-<commit>.json                       # Markdown tables
```

- Models: `SCALE_DEFAULT` (large configurations already in the manifest) plus `bench/scaling/*.cfg`
  (corpus specs with larger constants, ids `bench/<name>`).
- Each model gets one warm-up run at the largest worker count (its counts are checked too), then
  timed runs from small to large worker counts (`--repeat`, default 2, minimum taken; 1 worker
  uses `--repeat-1w`, default 1), then TLC once per `--tlc-workers` count, one JVM at a time. TLC
  at 1 worker is slow and runs only for the models listed in `--tlc-1w`.
- TLC memory: `-Xmx` and `-XX:MaxDirectMemorySize` are each `--tlc-mem` of physical memory
  (default 0.4; TLC's fingerprint set is off-heap); `--tlc-mem 0` keeps the JVM defaults as
  `tlcbase` does.
- Results go to `bench/history/scale-<commit>.json` (resumable, `--force` re-measures): machine,
  `lscpu` topology (sockets, cores per socket, SMT, NUMA nodes), memory, JVM and TLC versions, and
  per run wall/CPU/peak RSS/counts; with `--stats` one extra `-stats json` run per multi-worker count.
- The report gives, per model and worker count, tlx and TLC wall time, tlx's speedup over TLC at
  the same worker count, parallel efficiency T1 / (w · Tw), the count check against TLC, and
  geometric means.

To run it on a large cloud instance ([cloud-verification.md](cloud-verification.md)):

```sh
python3 scripts/cloud_verify.py --provider tencent --instance-type <type> \
    --bench "scale --workers 1,16,64,128,max --tlc-1w <model>" --max-minutes 90
```

## 3. TLC baseline

TLC's baseline jar (`third_party/tla2tools.jar`) is pinned by version, manifest revision and
SHA-256 in `scripts/dependencies.py` (`scripts/fetch-deps.sh`), and `third_party/community/modules.jar`
is pinned by `CommunityModules` release `202609120237` and SHA-256 the same way; both are verified
on install and a mismatched existing jar is refused, so an upstream `releases/latest` move cannot
silently invalidate stored baselines. The community-modules SHA-256 is recorded in each baseline
header. TLC times therefore need measuring once per machine type and input digest; later tlx
benchmarks compare against the stored baseline instead of re-running TLC.

```sh
scripts/bench.py tlcbase --slice 1/8                 # whole corpus, TLC -workers 1 and 16
scripts/bench.py tlcbase-merge bench/history/<out>.json <slice>.json ... --set instance_type=<type>
scripts/bench.py tlcbase-report tlc-<rev>            # totals, distribution, timeouts, slowest, count mismatches vs the oracle
scripts/bench.py report                             # canonical report, no TLC collection
scripts/bench.py history-report <commit> --tlc-baseline tlc-<rev>
scripts/bench.py ab --bin a=... --bin b=... --models X,Y --tlc-baseline tlc-<rev>
```

The measurement method equals the oracle's (`scripts/tlc.py` options; no `-Xmx`/`-fpmem`, so the
JVM's default heap and TLC's default fpmem; simulation models with `-seed 1`; one JVM at a time),
plus `-Dtlc2.TLC.asMilliSeconds=true` so TLC prints "Finished in" in milliseconds. Each run
records wall time (with JVM start-up), TLC's own "Finished in", JVM CPU time and peak RSS,
counts, result and violated name; a timeout (defaulting to each suite model's manifest
`timeout_s`, or `1800` s for non-suite models, unless `--timeout` is given) is recorded as `timeout`. The file
header records machine, JVM version, TLC revision, community-modules hash, timeout and worker
counts. `--slice I/N` splits the models into slices of similar estimated cost for parallel
machines; `tlcbase-merge` joins them. A baseline is meaningful only on the machine type it was
measured on (a warning is printed for a different CPU model). Raw collector outputs write to
`bench/history/` during a run (archived under ignored `work/` outside the published tree), while
canonical per-key baselines ship in `bench/tlc-baselines/` (section 6.2). A
baseline name resolves to its merged file, not to its slices: `tlc-<rev>` still matches
`tlc-<rev>-lane<s>.json`, and the canonical file wins while two slices without one stay an error
(reporting a slice as the whole baseline would silently report a fraction of the corpus).

## 4. Continuous performance tracking: `suite`, `track`, `suite-report`

A performance regression must not be found by chance. `bench/suite.json` is the fixed benchmark
suite; `scripts/bench.py track` runs it on one cloud instance, compares it with the previous
recorded revision on the same instance, records the result and fails on a regression.

**The manifest** (`bench/suite.json`, checked by `bench.py suite-check [--oracle]` and the unit
tests): per model its size class (`small`, `medium`, `large`; `huge` runs only with `--sizes all`),
the runs (`default`, `compile`, `interp` or `tlc`, worker counts, optional arguments and cgroup limits), a
timeout and the expected counts (`result`, and for a successful search `distinct`, `generated`,
`depth`) with their source: `tlc-oracle` (TLC's 1-worker result under `corpus/out`, checked by
`suite-check --oracle`), `tlc-bench` (counts TLC confirmed in the scaling and liveness records),
`tlx-pinned` (no TLC run exists; the count was pinned from recorded runs) or `unpinned` (recorded,
not enforced yet). The suite spans small models (start-up, front end, C build), medium and large
corpus models, the industrial external specifications (Vanlightly Raft, FlexibleRaft, Neon,
MongoDB, CCF, ZooKeeper Zab and FastLeaderElection, PingCAP Percolator, Raft region merge and
distributed transaction, Cassandra Accord with liveness), the liveness stress configurations
(`bench/ClockSettles`, `bench/RaftMongoT4`, `bench/ReplicatedLog4x3`) and the scaling
configurations (`bench/MCLamportMutex_clock14`, and with `huge` `MultiPaxos_MC` and
`bench/cf1s_folklore_N5`). A model whose SYMMETRY is not equivariant (`ext/neon`) runs at 1
worker only. Legacy `tlc_1w_s` fields are retained as historical metadata; they do not supply
report ratios because they were measured on another machine.

**Reduced rows and their unreduced twin.** `bench.py suite --with-tlc-companion` (also accepted by
`track` and forwarded to its cloud launch) schedules, immediately after every `default`-mode
manifest run that does not already pass `-tlc`, one companion `tlc` run of the same model, worker
count, timeout, extra arguments, environment and memory limit on the same instance, under the same
cache policy (both rows record that policy in `provenance.cache`, which the report requires to match).
When the selection already includes a `compile` run with `"-tlc"` in `args` matching the same model,
workers, remaining arguments, environment and memory limit, `with_companions` skips the redundant
separate `tlc` run: `tlx check -compile -tlc` executes the exact same unreduced compiled search, and
`bench_records.py` pairs that eligible `-compile` (`compatibility: true`, `"-tlc"` in `args`) record
as the `default` row's unreduced twin when no dedicated `mode: "-tlc"` record is newer.
That is the like-for-like twin the speedup audit requires: the two rows can be divided without mixing
machines or cache regimes. The companion's counts are checked against the manifest's pin when
that pin came from TLC (`tlc-oracle`, `tlc-bench`); when the pin came from a reduced run
(`tlx-pinned`) only its verdict is enforced, because the companion exists to measure the unreduced
counts and checking them against a reduced pin would reject the measurement. The option is off by
default. The stored dedicated twin is mode `-tlc`, tool `tlx`, so it is not confused with a TLC
baseline row. Section 1 describes how the report pairs the two.

**Incremental sharding and shortest-first scheduling.** `bench.py suite` accepts `--missing`,
`--bin-rev REV`, `--instance-type TYPE`, `--slice I/N` and `--dry-run`:

- `--missing` filters out runs already satisfied by an eligible canonical record in `bench/records/`
  for the target `(revision, instance_type, content_digest)` (and, under `--with-tlc-companion`, checks
  whether the matching unreduced twin is already paired via `bench_records.unreduced_twin` or matches
  the exact `twin_key` attributes this run will produce). To keep incremental `--missing` passes from
  clobbering previously ingested records on `ingest`, an explicit `--out` that already exists or owns
  stored records is refused, and omitted `--out` automatically chooses a fresh `-missing-<N>.json`
  history file when the default path is already occupied. Passing `--bin` without `--bin-rev` records
  `commit: null`, `bin` and `runner_commit` on the history file so an external binary never inherits
  the runner checkout's commit; `--missing` with `--bin` requires `--bin-rev`.
- `--slice I/N` partitions the remaining models into `N` load-balanced shards using the same
  longest-processing-time (LPT) balancer as `tlcbase` (`benchmarking.bench_budget.balance_slices`),
  keeping all selected runs of each model in one slice so `--with-tlc-companion` same-instance pairing
  is preserved. `bench.py track --slice I/N` runs one shard of that suite on the cloud instance and
  copies the shard's history file (`bench/history/<rev>-sliceIofN.json`) into the checkout, and
  `bench.py suite-merge OUT IN...` joins the shards of one revision into a single history file: the
  runs, the A/B base runs and the samples are the union, and the verdict is judged again over that
  union with the thresholds the shards recorded. A duplicate A/B key keeps the `(new, base)` pair the
  one shard measured interleaved on one instance, never a new run from one shard with a base run from
  another. The inputs must agree on the revision, the A/B base,
  the machine's instance type and architecture (slices are separate spot launches, so their recorded
  machine strings name different zones and prices), the selected sizes, the repeat count, the TLC
  version and the measured binaries;
  `suite-merge` writes the merged history and `bench.py suite-report` ingests it into
  `bench/records/` like any other history. It prints the merged verdict and exits with its status
  (0 pass or baseline, 1 regression or count mismatch, 2 inconclusive); `--set K=V` adds a header
  field to the merged file. Sharding is what keeps a campaign inside a cloud lease
  instead of truncating it with `skipped (time budget)`. For example:

  ```sh
  python3 scripts/bench.py track --sizes all --slice 1/2
  python3 scripts/bench.py track --sizes all --slice 2/2
  python3 scripts/bench.py suite-merge bench/history/<rev>.json bench/history/<rev>-slice1of2.json bench/history/<rev>-slice2of2.json
  python3 scripts/bench.py suite-report
  ```
- Within every `suite` run (sliced or unsliced), models execute **shortest-estimated-first** using
  (1) stored `bench/records/` wall times, else (2) stored `bench/tlc-baselines/` wall times /
  `tlc_1w_s`, else (3) size-tier fallbacks (`small: 2 s`, `medium: 30 s`, `large: 180 s`,
  `huge: 600 s`), keeping each model's `default` and companion twin adjacent so slow or unestimated
  models cannot starve fast models before `--max-minutes` / `--deadline-min`. Use `--dry-run` (with
  `--instance-type` if planning off-host) to inspect the filtered, sliced and ordered run list without
  building or running `tlx`.

Use `bench.py suite --modes compile` to select only compiled entries when a manifest
also contains default-mode runs. The CCF and MongoDB compiled entries pass `-tlc`
so their pinned counts remain comparable when automatic symmetry changes default
mode. For matching region profiles, pass `bench.py profile --extra=-tlc`.
When profiling an existing binary with `--bin`, pass `--bin-rev REV` to record
its revision; otherwise that revision remains unknown, independently of the
checkout running the profiler. Full per-worker `.stats.json` files retain region
and layout attribution alongside the measured profile summary.
Fixed configurations use the same registry as A/B runs. Pass repeatable
`--env K=V` overrides when profiling an experimental switch: every pass receives
them, and the summary records them. Reusing an output directory with different
overrides is refused.

Profile output is diagnostic evidence: it retains the ordinary CPU sample and
instrumented counters, but is excluded from public performance headlines.
Use repeated `bench.py ab` or suite measurements for a performance comparison.
A/B stats passes are also marked diagnostic, including when stats output is absent.

**Instrumented adapters** are custom `ab` wrapper binaries or scripts that count
something the ordinary binary cannot — for example, process-wide Rust allocator calls and encoded fallback input
decodes. They are run under `--env LABEL:K=V` (such as `MEMO_PROFILE_REV`, `MEMO_PROFILE_BIN`,
`MEMO_PROFILE_IR`, `MEMO_PROFILE_TOOLS` when driving a custom adapter). A counted binary's time includes its atomic counters, so it must never be compared for
timing: run the ordinary A/B first, then the adapter, at least three interleaved rounds after a
discarded warm-up, with the worker count, `TLX_*` settings and native-cache conditions identical.
Save the ordinary binaries outside `target/release/tlx` first — an instrumented build reuses
`target/` and overwrites that path. Instruction counts come from the ordinary binary
(`perf retired user instructions`, or `Cachegrind simulated instructions` when perf is unavailable,
which changes execution speed and can change adaptive path selection); report the method, the memo
hit rates, the load and the sample ranges alongside the medians.

**One command after merges:**

```sh
python3 scripts/bench.py track            # HEAD, A/B against the previous recorded revision, Tencent spot
python3 scripts/bench.py track --dry-run  # print the cloud_verify.py command
git add bench/report-policy.json docs/performance.md
git commit -m "bench: refresh generated performance report"
```

`track` picks the newest `bench/history/*.json` whose commit is an ancestor of the revision as the
base (`--base REV|none` overrides), starts one 16-vCPU instance with `cloud_verify.py --bench` (the
base is built next to the revision, `--bench-bin base=REV`), and the instance runs `bench.py suite`:
per run one discarded warm-up (C library built synchronously, counts checked) and three
interleaved A/B repeats, the order alternating, then wall, CPU, peak RSS and (when `perf` works
on the instance) retired instructions are recorded. The history file `bench/history/<rev>.json`
(the raw compatible source, including base revision, verdict and commit range) comes back.
`track` imports it into the canonical schema and regenerates `docs/performance.md`. Commit the
current source history, canonical records, report policy and generated report together. Move
superseded evidence and packaged archives under ignored `work/` (section 6.2).
Canonical records retain the requested and completed repetition counts for suite runs;
configurations with missing repetitions remain archived but are excluded from report headlines.
The budget is one launch of at most 60 minutes
(`--max-minutes`, default 40 plus 20 for set-up); runs not started within the budget are listed as
skipped and make the verdict inconclusive.

**Verdict and exit status** (the existing comparator, `bench.py compare`'s rules): `PASS` or
`BASELINE` (no previous revision) 0; `REGRESSION` 1: a count differing from the manifest, a different
number of distinct states of a complete search than the base's, a timeout, or a slowdown of the
minimum above 5% and 0.05 s with relative sample range at most 25% (the ratio of minima is
robust: the same binary measured against itself on a cloud instance stayed within -5%..+1.3% over
41 runs; the distinct states of a run stopped at a violation vary with several workers and are not
compared);
`INCONCLUSIVE` 2: noisy or incomplete samples, or skipped runs. Runs that are regressed or
inconclusive are measured once more with two more repeats, and the retry's samples are final.
The output names every regressed model and mode, the commit range `base..rev` (and its
`git log`); bisect by running `track --rev X --base Y` on candidates. A regression is a result,
not a reason to skip recording: the history file keeps its verdict.

**Testing the detector:** `bench.py suite-judge FILE [--write]` judges a recorded run again (other thresholds, a fixed rule).
`bench.py suite --inject-slow MODEL=FACTOR` makes the new binary's runs of
models whose id contains MODEL take FACTOR times as long (the extra time is slept and added to
wall and CPU), also through `track --inject-slow`. `scripts/tests/test_bench_suite.py` covers the
manifest, comparator, verdict, report and the runner with fake binaries, including a forced
regression that must exit 1 and name the model.

Local use is limited to what is cheap: `bench.py suite --sizes small --models SimpleRegular
--base-bin OLD_TLX` on a reduced selection, or the unit tests.

## 5. Canonical records and TLC baseline reuse

`scripts/benchmarking/records.py` defines the versioned measurement schema (`VERSION`, `FIELDS`,
`validate`). Each measurement records the
model, categories, tool, execution mode and workers, revision, instance/architecture and date,
input digest, verdict and counts, wall/CPU/RSS/instructions and a matching TLC measurement ID.
Null means unknown or unmeasured. Repeated timings use medians in the report; the existing A/B
regression judge retains its minimum-based comparison. Canonical records in the published repository
(`bench/records/` and `bench/tlc-baselines/`) carry embedded per-sample data and point to their own
canonical store files, while retaining original collection pointers in `provenance` ([bench/README.md](../bench/README.md)).
When raw runner outputs or an optional maintainer archive inventory are present during a re-import,
`benchmarking.legacy` resolves retired raw sources through `<revision>:<path>` in git history and
verifies their SHA-256 digests rather than treating a broken locator as an absent source.
`suite-report` re-ingests present suite histories and regenerates the report; the historical trend
view in `bench_suite.trend_markdown` is a renderer, not a document, and no command writes one — the
report of record is `docs/performance.md`. Where a trend view is rendered, its `vs prev` column uses
the minimum wall time of the repeats, unlike the canonical report's medians.

```sh
python3 scripts/bench.py migrate             # idempotent re-import when raw sources are present
python3 scripts/bench.py report --refresh-ages
python3 scripts/bench.py report --check
python3 scripts/bench.py tlcbase --missing --workers 1,16 --no-large --instance-type SA5.4XLARGE32
# Collect only missing/stale keys on a cloud instance, within its launch budget:
python3 scripts/bench.py tlcbase --missing --collect --workers 1,16 --no-large
# List missing or stale baseline keys for the selected machine:
python3 scripts/bench.py tlcbase --missing --workers 1,16 --instance-type SA5.4XLARGE32
```

The input digest covers the spec, config, local module closure and semantic flags, and the run's
**layout**: the effective working directory when it is not the spec's own - a model the corpus
manifest marks `cwd: root` reads its declared inputs (`corpus.MODEL_INPUTS`) from the corpus root,
where upstream's Examples CI runs it - and the resolved bytes of those declared inputs. Both are
relative (a named root and relative file names), so a relocated but identical input keeps its key,
while a changed staging or a changed trace is a different key and a missing declared input has no
reusable key at all. A model that runs next to its spec and declares no input hashes exactly as
before, so the frozen report's pinned input keys stay valid.

TLC is collected once per key in `bench/tlc-baselines/` (section 6): TLC revision, model ID, digest of
spec/config/local module dependencies, semantic flags and run layout, worker count and instance type.
Memory-constrained experiments additionally key their heap/direct-memory/cgroup settings.
A valid completed key is reused even with a runner's force option. `run`, `scale`, disk
experiments, `ttfr` and `tlcbase` share this collection boundary; `ab` and `track` consult the store
without running TLC. Timeouts and other incomplete measurements never satisfy a baseline key.

An incomplete key still keeps one row, the strongest record of why it has none: a timeout
measured at a longer bound outranks a shorter one, otherwise the newer record is the current
evidence, and a completed measurement supersedes either - so re-running a key at a longer
timeout replaces the shorter bound it outgrew instead of leaving a stale row behind.
`cached_tlc` shares this strongest-evidence persistence with `seed_baselines`, so non-reusable
`timeout` and `error` runs are persisted when no stronger record exists for that key.
`tlcbase --missing` inspects the stored row for each key and skips already-bounded timeouts
(`wall_s` at least the model's target timeout) and stored TLC errors, reporting counts of
`unmeasured/stale`, `bounded-timeout`, and `tlc-error` keys unless `--retry-incomplete` is passed.
Baseline pairing (`historical_match`) requires matching hardware, worker count, verdict (`COMPLETE`,
and violated property name when recorded), and outside `default` mode exact `distinct` parity for
single-worker runs and successful searches (multi-worker early stops such as `deadlock` and
`safety failure` have interleaving-dependent counts under [compat.md](compat.md) section 0 tier 3).
When raw measurement sources are modified in a working tree, re-run `bench.py migrate`; `bench.py report --check`
re-derives every present or archived source and fails a stored row no source produces, or a stored row weaker
than the row its key derives. Migration validation compares the previous store with the migrated store: every retained row
must preserve its measurements, and every previous measurement key must remain represented.
Missing keys are listed explicitly; they are collected only by an explicitly requested TLC
measurement, with normal cloud/local resource guards still applied.

Legacy TLC timings retain their recorded version. Migration can adopt current model bytes only
when verdict, distinct count and depth exactly match the current TLC oracle; it records the
migration snapshot and matching fields as provenance. Missing TLC versions are not inferred
from the existence of today's jar. Unverifiable records stay historical/unverified and appear
in coverage gaps. Changing the model digest, TLC revision, workers or instance invalidates the
key; age alone does not. The pinned report policy stores input identities and revision ages,
so regeneration and gates need no oracle timings or cloud access. `--refresh-ages` advances
that reference; `track` does this automatically. The stale threshold defaults to the revision
count in `bench/report-policy.json`.

`scripts/doccheck.py` calls `bench_records.check(..., sources=False)`, validating every stored
record and baseline key in `bench/records/` and `bench/tlc-baselines/`, checking that
`docs/performance.md` matches a fresh render from `bench/report-policy.json` and `bench/suite.json`,
and rejecting ad hoc Markdown under `bench/` (outside `bench/README.md`). `python3 scripts/bench.py report --check`
runs `bench_records.check(..., sources=True)`, which additionally checks source locators — re-deriving
any present raw sources and verifying archived source digests when an archive inventory is present —
and fails if a stored row's source is missing or no longer produces that row. Re-importing cannot
silently re-adopt changed inputs or unfreeze old tables. Add a suite configuration and record the
resulting measurement instead of starting another report.

## 6. Record format and conventions

This section owns the shape of a stored measurement and the rules for changing it. The protocol
above says how a number is produced; this section says what a stored number is.

### 6.1 A measurement

`scripts/benchmarking/records.py` is the single validator (`VERSION`, `validate`) and every reader
goes through it. The validator is strict: a field the
schema does not name is refused, and a field that does not apply to a row is *absent* - so "carried
no census" and "carried a census of zero" cannot be confused. One measurement carries:

| Field | Meaning |
|---|---|
| `schema_version` | the schema the row was written under; a bump moves the validator, the readers and the migration together |
| `tool` | `tlx` or `tlc` |
| `model` | corpus model id (`Repo/Model`, or a `bench/` id) |
| `mode` | one of `default`, `-tlc`, `-interp`, `-compile`, `legacy-unknown` |
| `workers` | positive integer; `1` and `16` are the two the TLC baseline collects |
| `revision` | the tlx commit for a tlx row, `null` for a TLC row |
| `tlc_version` | the TLC revision measured, or the one a tlx row was compared against |
| `content_digest` | digest of the spec, config, module closure, semantic flags and run layout, so a row is reusable only for the same input |
| `instance` | `{type, arch, description}`; the machine the number is only valid on |
| `category` | free-form tags the report groups by (`corpus`, `external`, `compiled`, `liveness`, `scaling`, `beyond-memory`, `diagnostic`, ...) |
| `counts` | `{result, distinct, generated, depth}`; `result` in `COMPLETE` (`success`, `deadlock`, `safety failure`, `liveness failure`, `assumption failure`) means the run finished |
| `metrics` | `{wall_s, cpu_s, rss_mib, instructions}`, medians over the repeats |
| `configuration` | `{args, variant, env, hogs, cgroup_mib, compatibility}`; the run's own knobs. All but `compatibility` are key dimensions |
| `samples`, `aggregation` | the per-repeat values and how they were reduced |
| `baseline` | the TLC measurement a tlx row was compared against, or `null` |
| `provenance` | `{source, pointer, legacy}`: the artifact and JSON pointer (or markdown line) the row came from, plus what the reader learned there (`adoption`, `repetitions`, `sample_results`, `count_problems`, `metric_sources`, ...) |
| `raw_result` | the producer's own raw output for the row, kept because the canonical fields do not carry all of it (a TLC parse result: `finished_s`, `tlc_memory`, `exit`, ...) |
| `date`, `id` | when it ran, and the row's own identity |
| `native_share`, `host_time_share`, `host_s`, `host_calls`, `evaluations`, `fully_native`, `search_thread_s_est`, `coverage` | coverage attributes (6.4); absent when the run carried no census |

`null` means unknown or unmeasured, never zero. A row whose `counts.result` is not in `COMPLETE`
is the record of *why* a key has no measurement, not a measurement of it; it is kept, not deleted.
The optional `provenance.count_problems` preserves the producer's expectation mismatches,
including earlier samples and warm-ups. A nonempty list excludes the row from performance
evidence and TLC baseline reuse or pairing even when the result is in `COMPLETE`;
its verdict, timings and diagnostics remain
available for audit. An empty list means the recorded check matched; absence means the source
did not record that check, preserving legacy behavior. Expected safety failures and deadlocks
remain valid measurements. Re-import the raw source to repair older rows that lost this field.

### 6.2 The store

There is one store with one shape, whatever tool wrote the row:

| Container | Rows | Envelope | Granularity |
|---|---|---|---|
| `bench/records/<key id>.json` | tlx | `{schema_version, key, measurement}` | one file per key; `key` is exactly `measurement_key`'s value |
| `bench/tlc-baselines/<key id>.json` | tlc | `{schema_version, key, measurement}` | the same, in the container TLC's own lifecycle owns (sections 3 and 5) |

The two containers differ in nothing but which tool's rows they hold - a TLC baseline is collected
once per key and replaced wholesale when its TLC revision changes, which is why it keeps a container
of its own rather than a subdirectory's worth of churn. Every reader takes both.

The source repository publishes the current benchmark inputs, `bench/records/`,
`bench/tlc-baselines/`, embedded samples, environment evidence and `bench/report-policy.json`.
A fresh clone can reproduce the performance report and follow its record links without private
archives. Raw histories for a frozen baseline can be archived after their per-configuration results are
embedded and provenance is repointed to the independent canonical files. Superseded records,
migration inventories, packaged snapshots and process notes belong
under ignored `work/`, not under `bench/`.

See [benchmark inputs and evidence](../bench/README.md) for validation and optional backup commands.
Report generation still refuses to replace the report when measurements are absent, and the
documentation checker reports this limitation for deliberately stripped checkouts. A portable
backup includes the current inputs, evidence, exact Python tools and report, with per-file hashes
and an archive checksum. Verification reproduces the report without rerunning models. Historical
raw artifacts outside the current baseline remain in the maintainer archive.

A file's name is the SHA-256 of the key's **identity dimensions** - the dimensions that can tell two
measurements of that tool apart (6.3) - so a reader can check a file against its own key without
reading the store. It is `legacy-<measurement id>` for a row whose key is **not fully determined**
(a historical TLC row with no TLC revision or no input digest): those rows are still stored, because
each is the only record of why that measurement exists, so two of them must never collapse into one
file, and the file name stops being the key exactly there. `load_records` refuses a file whose
envelope, key, name and measurement disagree; `load_store` is the tolerant reader migration uses on
the store it is about to rewrite.

A keyed file holds the *record of record* for its key: measurements are grouped by key and the
strongest one wins - a completed measurement over a timeout over a run that did not finish, and
among equals the newest, except that between two timeouts the longer bound is the better evidence.
A row the store does not keep is not lost: it stays readable in its own source under `bench/`, and
`check` accepts it exactly while the store holds a row at least as strong for the same key.

A TLC baseline key has no revision dimension: the TLC revision pins it, and a key changes only when
its input digest, worker count, machine or TLC revision changes. TLC's mode, arguments, variant and
environment are that tool's constants. Tracked files under `bench/` consist of `bench/README.md`,
`bench/suite.json`, `bench/repr-models.toml`, `bench/repr-configs/`, `bench/stress/`,
`bench/scaling/`, `bench/report-policy.json`, `bench/records/`, `bench/tlc-baselines/`,
`bench/environment/` and `bench/validation/`. Raw runner outputs (such as `bench.py run`, `scale` or
`ab` JSON files) are ingested into the canonical store via `ingest` or `bench.py migrate` and
archived under ignored `work/`, so hand edits to derived rows do not survive a re-import.

### 6.3 Key dimensions

| Dimension | TLC baseline | tlx record | Unified (BENCH-01) |
|---|---|---|---|
| `tool` | yes | yes | yes |
| `model` | yes | yes | yes |
| `workers` | yes | yes | yes |
| `instance_type`, `instance_arch` | yes | yes | yes |
| `content_digest` | yes | yes | yes |
| `tlc_version` | yes | yes | yes |
| `revision` (the tlx commit) | n/a (TLC row: `null`) | yes | yes |
| `mode`, `args` | constant (`-tlc`, none) | yes | yes |
| `configuration.variant` | `null` | yes | yes |
| `configuration.env` | `null` | yes | yes |
| `configuration.cgroup_mib`, `configuration.hogs` | `null`/`0` | yes | yes |

`cgroup_mib` and `hogs` are part of the key because they change what a number means: a
memory-constrained run and an oversubscribed run are different measurements of the same model, and
the `beyond-memory` lane stores both. The dimensions a key *names a file* by are the ones that can
differ for that tool: a tlx measurement by all of them, a TLC baseline by the TLC revision, the
model, the input digest, the worker count and the instance type - TLC's mode, arguments, variant,
environment and revision are constants of how it is run and distinguish nothing, and leaving them
out of the name is what keeps a TLC key's file the one the lanes and the coverage report already
name. A tlx measurement is comparable only to one with the same
model, revision, instance, mode and arguments; the report renders that as the row's evidence
text (revision, instance, date and the store file the row lives in).

### 6.4 Coverage attributes (BENCH-01)

A tlx measurement may also carry coverage attributes - `native_share`, `host_time_share`, `host_s`,
`host_calls`, `evaluations`, `fully_native`, `search_thread_s_est` and the optional per-operation
`coverage.ops[]` - so that the native coverage census is a view over the same store instead of a
separate artifact with its own schema. `scripts/coverage.py --record` publishes a census as one row
per model (`-stats` output, the run's timing and verdict, and its coverage attributes together) and
`--view` prints that census back out of the store; a row carries `category: [..., "diagnostic"]`, so
a census never enters the report headlines.

Three rules go with them. A coverage number is comparable only when the run's adaptive tiering is
pinned (`configuration.env` records `TLX_MIXED_ADAPT`), because the same binary chooses per function
and per run and can move the interpreter share by a factor of two or three; a coverage row that
records no `TLX_MIXED_ADAPT` was measured under the adaptive default. A coverage row records the
layout and pre-run summary it was taken with, for the same reason. And the chosen tier is auditable
per function: `coverage.ops[]` keeps, for each function the census saw, how many of its calls took
each path (`calls` per `native`/`mixed`/`ir`/`interp`/`fallback`), so a share that moved can be
attributed to the functions whose tier moved rather than to the model as a whole.

A manifest run may pin the tier with a per-run `env` (`{"TLX_MIXED_ADAPT": "0"}`), and
`bench.py suite/track --pin-adapt [marked|all]` adds that pin to the compiled and default runs of the
families the manifest marks `pin_adapt` (or of every model). The pin is recorded in
`configuration.env` and therefore in the key, so the pinned configuration sits beside the adaptive
one instead of moving it, and `track` measures both binaries under the same pin in the same launch -
the comparison stays valid and the judgement is reproducible. Pinning is asked for, never implied:
a run that pins nothing records nothing new, and `track` without it reports exactly what the
adaptive chooser produced.

### 6.5 Reuse, staleness and migration

- A stored TLC row is reusable as a baseline only when its key is complete, its result is in
  `COMPLETE` and it has a wall time; nothing else may stand in for a baseline.
- Staleness is 20 revisions, relative to the pinned reference in `bench/report-policy.json`. A
  baseline expires only when its key changes, never because time passes, and an unknown revision
  age counts as stale rather than recent.
- Published canonical records in `bench/records/` and `bench/tlc-baselines/` carry embedded
  samples and point `provenance.source` at their own canonical files; when an optional maintainer
  archive inventory is used during migration, retired raw sources are verified by git revision and
  SHA-256 digest (`benchmarking.records.archived_bytes`).
- Migration is idempotent: running `bench.py migrate` twice changes nothing. A file is written only
  when its bytes would change, so a fold that re-derives the same store leaves
  `bench/report-policy.json` and `docs/performance.md` alone.
- A new field is added only together with the reader that consumes it, and a `schema_version` bump
  updates the validator (`scripts/benchmarking/records.py`), the readers and the migration in one change.

## 7. Release comparison: `bench.py release`

`bench.py release` compares two published releases - and both with TLC - on one machine class, from
the canonical measurement store. It measures nothing itself: `--report-only` renders the comparison
of what `bench/records/` and `bench/tlc-baselines/` already hold, and the campaign mode collects
what is missing (sections 4 and 5) before rendering the same report.

```sh
python3 scripts/bench.py release v0.1.2 --report-only
python3 scripts/bench.py release v0.1.2 --report-only --markdown target/release-v0.1.2.md
python3 scripts/bench.py release v0.1.2 --dry-run --slices 4 --slots 4
```

`TAG` defaults to the newest `v*.*.*` tag and `--prev-tag` (default `auto`) to the release before
it in version order; name a tag or commit to compare against another one, or `none` to report only
the TLC side. A name that resolves to no commit is refused, so an unknown tag can never enter the
report as an unknown revision. `--instance-type` (default `SA5.4XLARGE32`) is the machine class the
comparison is quotable on.

**Pairing fails closed.** A new-revision row and a previous-release row are compared only when every
dimension that decides whether they are the same measurement agrees: model, machine class and
architecture, mode, worker count, arguments, environment, memory limit, the input digest and the TLC
version the timing was taken against. A dimension either record leaves unknown is not an agreement -
two unknown input digests are two possibly different inputs - and a `-dirty` working-tree record names
bytes nobody published, so it is not a release row at all. A row measured on another machine, against
changed inputs or against another TLC version is therefore unpaired (`—`), never a ratio across
incomparable evidence; a missing counterpart is not a zero. The TLC side is the row's own stored
baseline, and it is used only when `historical_match` accepts it (section 5).

**The report** is deterministic Markdown: the same store renders byte for byte the same text. It has
three tables.

- *Cohort summary* per mode and worker count: the models measured, how many paired, the median and
  geometric-mean `previous / new` wall speedup, the median `previous / new` peak-RSS ratio, the
  median `TLC / new` wall and RSS ratios, and how many models recorded a newly applied optimization
  (a row with no previous release states no new optimization: it has nothing to differ from).
- *Regressions and notable gains*: rows whose new wall time is both more than `--threshold` (default
  5%) and more than `--min-delta` (default 0.05 s) slower than the previous release, beside the
  largest wall-time gains and the largest peak-memory reductions (`--top`, default 8 each; a ratio of
  one or below is neither a gain nor a reduction and is listed in neither). Both regression bounds
  are required: a 5% slowdown of a 0.1 s model is not a result.
- *Flagship open-source models* (`ext/*`, and the corpus models whose id names Raft, Zab or Mongo):
  `previous s / MiB` -> `new s / MiB` against `TLC s / MiB`, the same-instance unreduced `-tlc`
  twin's wall time and the optimizations the new record states.

Ratios are `previous / new` and `TLC / new`, so a value above one means the new release (or tlx) is
faster or used less peak memory on the same machine and input. `docs/performance.md` remains the
report of record for the corpus as a whole; the release report is the cross-version delta beside it.

**Campaign mode** (no `--report-only`) launches what the store is missing and then renders the same
report. Each launch is one `scripts/cloud_verify.py --bench` invocation on the provider's spot
capacity: first `tlcbase --missing --collect` for the missing TLC baselines, then `--slices` shards
of `suite --missing --slice I/N --bin target/bench-bins/rel/tlx --isolate-cache
--with-tlc-companion` with `--bench-bin rel=<TAG>`, so the harness is this checkout's and the binary
under test is the released tag (`HARNESS-19`). `--slots` is the concurrent-instance share the
launches may use, `--max-minutes` the suite's own budget per launch, and `--repeat` /
`--tlc-repetitions` the sample counts. `--models` (ids or id substrings) and `--sizes` (size classes,
or `all` for every class including `huge`) select the campaign's suite models, resolved once against
`bench/suite.json` into exact ids: both passes get the same list, so a targeted campaign collects no
TLC baseline for a model - or a size class - it will not run, and a filter that selects no suite model
is refused before anything launches. An explicit `--models` also tells the suite pass `--sizes all`,
because the suite's own default is `small,medium,large` and would otherwise drop a named `huge` model
after the instance was provisioned. A launch with nothing missing exits successfully without writing
its history file, which is a completed no-op and not a failure - the campaign goes on to the next
shard. A suite verdict of 1 (regression) or 2 (inconclusive) is a result and is recorded; any other
exit is an infrastructure refusal, and nothing it fetched is recorded, as is a verdict exit whose
receipt does not hold the history file it was told to write. Only the receipt a launch writes for
itself authorizes it: the result directory is new for every invocation, so an earlier run's receipt is
never adopted and a re-issued command never becomes ambiguous. Each returned history file is imported
into the canonical store and the published report is regenerated, so the campaign's output is
committed as the usual history files, records, report policy and report. `--dry-run` prints the
launches without running any.

A campaign runs once per release. A history file whose records are already in the store is not
overwritten: `suite --missing` refuses an occupied `--out`, so a resumed campaign takes the next
attempt number (`suite-<tag>-s1of4-2.json`) and records only what the new launch returned.

**The release webhook.** [`.github/workflows/release-benchmark.yml`](../.github/workflows/release-benchmark.yml)
runs on a `v*.*.*` tag push (and by `workflow_dispatch` with an optional tag) and POSTs
`{event, repo, tag, sha, run_id}` to the `MULTICA_RELEASE_BENCH_WEBHOOK_URL` repository secret,
which starts the post-release benchmark autopilot. The GitHub tag glob also matches prereleases, so
the tag is re-checked against `vX.Y.Z`: a tag push that is not one is skipped, an explicit dispatch
input that is not one is an error, and without the secret the workflow logs that and succeeds - a
fork, a prerelease or a repository that has not configured the autopilot stays green.
