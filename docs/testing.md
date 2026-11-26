# Testing

tlx is correct when it agrees with **TLC**. The semantic oracle ordering is TLC, then the tlx
interpreter, then the tlx compiled tier. What "agrees" means (which results must be identical and
which only have to be valid) is the compatibility contract in [compat.md](compat.md) section 0.
This document owns the test tiers, the differential tests and their oracles, and the gates that run
them, with the exact commands. Two neighbouring topics have their own owner:
[benchmarking.md](benchmarking.md) for performance measurement and the TLC timing baselines, and
[cloud-verification.md](cloud-verification.md) for what runs on a cloud instance and on the shared
workstation.

The commands below use public tools in `scripts/`. Most use the Python 3 standard library;
cloud-provider commands additionally need their SDKs, described in [cloud-verification.md](cloud-verification.md).

## Continuous integration

GitHub Actions runs on pushes to `main`, pull requests and manual dispatches. The `CI`
summary check aggregates Linux x86_64, Linux arm64 and macOS arm64 Rust/spec tests plus the Linux quality
job (formatting, Clippy, Python driver tests, documentation and benchmark-report checks).
Actions are pinned by commit and run with read-only repository permissions. The workflow does not
use cloud credentials or run performance benchmarks. Corpus-wide model-checking runs remain separate cloud jobs.
The `main` branch accepts changes only through pull requests with a linear history; squash
merging is the only enabled merge method, and direct pushes, force pushes, merge commits and
deletion are rejected. CI runs after each push; its result is not a precondition for pushing.

The Python quality job uses `bash scripts/fetch-deps.sh --tests-only`, without the Examples corpus.
Rust jobs use the full dependency fetch because their parser and resolver corpus tests require it;
these front-end checks do not exhaustively model-check the corpus. The exact TLC oracle jar and
its license are retained in `tests/deps/` and verified
against the pin in `scripts/dependencies.py`; the mutable upstream release asset is not trusted to
supply the historical oracle bytes. With Java available for trace validation, spec tests run all
seven `spectest` modes on every OS/architecture runner, matching the suites of `scripts/verify.py`:
interpreter (`-interp`), compiled with default tiering, paranoid compiled (`TLX_PARANOID=1`, C
tier), paranoid JIT compiled (`TLX_JIT=1 TLX_PARANOID=1`, Cranelift codegen), C-only without
pre-run reuse (`TLX_JIT=0 TLX_PRERUN_REUSE=0 TLX_NATIVE_SYNC=1`, run after the paranoid suite has
built the C libraries into the shared cache, which the synchronous load then reuses), multi-worker
compiled (`-compile -workers 8`), and default mode
(`--default-mode`, automatic symmetry with its Lean certificates written to an isolated
`TLX_PROOF_DIR`). Each mode writes its own report under `target/ci/`, uploaded with the run.

## What belongs in a test

Test tlx behavior and the contracts of its integrations, not basic guarantees supplied by the
operating system, standard library or an unchanged third-party dependency. For example, do not
retest that the system CPU clock excludes sleep or that a re-exported hash implementation is
deterministic. Keep coverage of tlx-owned hashing, persisted formats, resource accounting,
cleanup, cancellation and error propagation: these can fail even when the underlying APIs work.

Use controlled inputs or an injected clock to test time-dependent policy. Avoid assertions about
machine speed or elapsed time around otherwise empty work. Real-process tests and generous
deadlines are appropriate when they exercise tlx's timeout, cancellation or process-ownership
contract. Before adding a test, identify the tlx defect its failure would reveal.

## 1. Test layers

| Layer | What it checks | Needs Java/TLC | Section |
|---|---|---|---|
| `cargo test` | unit and integration tests of every crate | no | [4](#4-cargo-tests) |
| `scripts/spectest.py` | `tests/specs`: small specs, one semantic point each, against cached TLC results | no (only for new specs) | [5](#5-spec-tests-scriptsspectestpy) |
| `scripts/difftest.py` | the tlaplus/Examples corpus against the TLC oracle `corpus/out/tlc.json` | no (oracle is cached) | [6](#6-corpus-differential-tests) |
| `scripts/difftest.py --filter ext/` | external repositories (MongoDB, CCF, Neon, ...) pinned in `corpus/external.json` | no after the first TLC run | [6.3](#63-external-corpora-corpusexternaljson) |
| `scripts/tlcsuite.py` | TLC's own regression suite (test-model and its JUnit tests) against a TLC re-run | yes (oracle cached) | [6.4](#64-tlcs-regression-suite-scriptstlcsuitepy) |
| `scripts/matrix.py` | generated feature-combination specs against TLC | yes | [7](#7-feature-matrix-and-expression-fuzzing) |
| `scripts/fuzz_expr.py` | random expressions, TLC vs interpreter vs compiled | yes | [7](#7-feature-matrix-and-expression-fuzzing) |
| `scripts/fuzz_spec.py` | random whole specs, TLC vs tlx in five modes; minimized regressions in `tests/fuzz/specs` | yes | [7.1](#71-whole-spec-fuzzing-scriptsfuzz_specpy) |
| `TLX_PARANOID`, `TLX_JIT_VERIFY` | compiled tier cross-checked against the interpreter at run time | no | [8](#8-cross-checking-modes-tlx_paranoid-and-the-jit) |
| `scripts/sanydiff.py` | tlx front end against SANY | yes | [9](#9-front-end-against-sany-scriptssanydiffpy) |
| `scripts/coverage.py` | how much of the corpus compiles to native code | no | [10](#10-compiled-tier-coverage-scriptscoveragepy) |
| `scripts/verify.py` | everything above, in a clean checkout (the merge gate) | no | [12](#12-the-merge-gate-scriptsverifypy) |

Performance measurement and the cloud lanes are not test layers and have their own owner documents:
[benchmarking.md](benchmarking.md) (the benchmark driver, the suite of record, the TLC timing
baselines and their reuse) and [cloud-verification.md](cloud-verification.md) (`scripts/cloud_verify.py`,
the launch admission rules, and what may run on the shared workstation at all).

## 2. Setup

| Dependency | Purpose |
|---|---|
| Rust (the toolchain in `rust-toolchain.toml` is installed by rustup) and a C compiler (`cc`) | build and run tlx; the compiled tier builds generated C with `$CC` or `cc` |
| Python 3 | the `scripts/` drivers |
| Java 21 | run TLC and SANY (test oracles only). Not on `PATH` by default on macOS/Homebrew; point `TLX_JAVA` at the `java` binary (default `/opt/homebrew/opt/openjdk@21/bin/java`, see `scripts/tlc.py`) |
| `third_party/` | test inputs, fetched by `scripts/fetch-deps.sh` (idempotent, skips what exists) |
| `corpus/out/` | result files of the corpus scripts (git-ignored) |

```sh
scripts/fetch-deps.sh          # third_party/: tla2tools.jar (TLC), Examples/, community/, tlapm/, apalache/
```

| `third_party/` entry | Content |
|---|---|
| `tla2tools.jar` | TLC and SANY (v1.8.0) |
| `Examples/` | the tlaplus/Examples corpus, with `manifest.json` expectations; the submodules (CCF, azure-cosmos-tla, BlockingQueue, microwave) are checked out too, they have no manifest and are not corpus models |
| `external/` | the external repositories of `corpus/external.json` and TLC's regression suite, fetched by `scripts/fetch-external.py` (section 6.3) |
| `community/` | CommunityModules jar and `.tla` sources |
| `tlapm/library/`, `apalache/` | extra modules some corpus specs extend |

`corpus/out/` holds the TLC oracle `tlc.json`, tlx result files `tlx*.json`, the SANY cache
`sany.json` and the benchmark TLC cache `bench-tlc.json`. Section 6 shows how to produce `tlc.json`
(needs Java; takes a while). Rust front-end corpus tests print a note and skip when `third_party/`
is missing. Python oracle drivers (`scripts/tlc.py`, `scripts/sanydiff.py`) invoke `TLX_JAVA` with
`third_party/tla2tools.jar` and `third_party/community/modules.jar` on `-cp`: if `scripts/fetch-deps.sh`
has not installed the jars (`scripts/dependencies.py verify-jar` checks the pinned `tla2tools.jar`
SHA-256 and manifest revision, reporting `no tla2tools.jar` when absent) or `TLX_JAVA` is missing,
Java/subprocess launch fails and the driver reports a collection or `no verdict` infrastructure
error rather than silently passing.

Scripts pass `-I third_party/community -I third_party/tlapm/library -I third_party/apalache` to tlx
and put the same directories on TLC's classpath. Tests find the two directories through
`TLX_THIRD_PARTY` and `TLX_CORPUS_OUT` (see [configuration.md](configuration.md)). A fresh git
worktree has neither directory. Fetch dependencies there, or point `TLX_THIRD_PARTY` at an
existing dependency tree. Keep a private `corpus/out` because the oracle scripts write into it;
section 6.5 describes copying validated oracle evidence.

## 3. Build profiles

| Profile | Settings | Used for |
|---|---|---|
| `release` | `codegen-units = 1`, `lto = "thin"`, `debug = 1` | the warning/lint gate, all benchmarks and performance conclusions, the `verify.py` spec and corpus suites, shipped binaries |
| `test-release` | inherits `release`; `lto = false`, `codegen-units = 16`, `incremental = true`, `debug = "line-tables-only"` | the inner loop: `cargo build/test --profile test-release`, and by default every correctness script (`spectest`, `difftest`, `matrix`, `coverage`, `fuzz_expr`, `sanydiff`; through `build_tlx()` in `scripts/tlxlib.py`) |

The correctness scripts build and run `target/test-release/tlx`, the same file `cargo test
--profile test-release` builds, so running cargo tests and then spec tests needs no extra build.
`--release` selects the release binary for one run, `--profile P` any other profile (`dev` is
debug; much slower), and `TLX_BUILD_PROFILE=release` changes the default for all scripts. Results
are identical across profiles; only speed differs.

Why a second profile (build time of `cargo build -p tlx-cli`, wall seconds, median, 18-core shared
machine; "one-line edit" changes one line of the named file):

| Scenario | release | test-release without incremental | test-release |
|---|---|---|---|
| fresh build (new worktree) | 121 | 59 | 79 |
| one-line edit in `tlx-eval/src/eval.rs` | 91 | 18.5 | **3.5** |
| one-line edit in `tlx-compile/src/lower/mod.rs` | 70 | 15.3 | **8.6** |
| `cargo test --no-run` (workspace) after an `eval.rs` edit | n/a | 47-94 | **9-10** |

Incremental compilation is the only option that helped: a larger `codegen-units`, lower `debug`,
`opt-level = 2`, a different linker and `sccache` for workspace crates gave nothing measurable
(linking takes 0.1-0.2 s; sccache keys include absolute paths and skip incremental builds, so it
only caches third-party crates). The cost is run time of the binary (1 worker, instructions
relative to `release`, three interleaved runs):

| Model | Tier | `release` instructions | `test-release` |
|---|---|---|---|
| SimpleRegular | interpreter | 48.2 G | +7.2% |
| SimpleRegular | `-compile` | 6.4 G | +0.5% |
| PaxosCommit | interpreter | 1139 G | +4.3% |
| PaxosCommit | `-compile` | 47.3 G | +3.3% |
| cf1s_folklore | interpreter | 805 G | +8.0% |
| cf1s_folklore | `-compile` | 59.6 G | +1.0% |

The interpreter is 4-8% slower, the compiled tier 0-3% (its hot path is generated C or JIT code,
which Rust profiles do not affect). The `difftest` default timeout (120 s) leaves room for that, but
the slowest interpreter models can time out under load with either profile (pass `--timeout 300`
when you need their counts). Always use `release` for performance numbers.

## 4. Cargo tests

```sh
cargo test --profile test-release -q --no-fail-fast   # everything (debug builds are very slow)
cargo test --profile test-release -q -p tlx-cli        # one crate
cargo build --release                                  # must build without warnings
cargo clippy --workspace --release --all-targets       # must report 0 warnings
cargo fmt --all -- --check
```

`--no-fail-fast` is what makes the run a verdict: libtest otherwise stops at the first failing test
binary, and a failure in an early crate hides every crate after it. On the shared machine it runs with
`-j 3`; choose an explicit concurrency limit appropriate to the machine. No local Cargo
configuration or cross-checkout compiler wrapper is required.

The rule-based optimization CLI regressions run with
`cargo test --profile test-release -p tlx-cli --test optimization -j 3`.
They compare original and generated model verdicts against cached TLC output, then check
counts, depth, violated invariant names and trace lengths for each model across the interpreter,
compiled IR and native tiers with paranoid checking, including opt-in exact cleanup and
compatibility-mode bypass. Deterministic counterexamples also compare concrete values. Exact generated module/config snapshots
prevent using an oracle for different emitted input. The reset case has two original states and
one abstract state, so it also detects accidental optimization during ordinary `-tlc` checking.
The [fixture refresh recipe](../crates/tlx-cli/tests/fixtures/optimization/README.md) needs Java/TLC;
running the Rust regressions does not.

The lint set is declared once in the root `Cargo.toml` (`[workspace.lints]`, inherited with
`[lints] workspace = true`); a local `#[allow(clippy::...)]` needs a reason on the same line.

| Crate tests | Content |
|---|---|
| `tlx-value/tests` | total order, equality, normalization, arithmetic, fingerprints, formatting, serialization |
| `tlx-front/tests` | grammar (`parse.rs`), cfg parsing (`cfg.rs`, including every `.cfg` in the corpus), whole-corpus parsing (`parse_corpus.rs`) |
| `tlx-sema/tests` | name resolution and INSTANCE (`resolve.rs`); SANY's semantic checks with expected messages (`sany.rs`) |
| `tlx-eval/tests` | expression evaluation |
| `tlx-layout/tests`, `tlx-testkit/tests` | shape inference, `LayoutNode`, serialization and recovery of values and shapes; corpus encoding and serialization round trips (in `tlx-testkit`, the interpreter-fixture crate) |
| `tlx-native/tests` | C generation, build and `dlopen` (`native.rs`), concurrent and failed builds, mixed-mode host side (`mixed.rs`) |
| `tlx-compile/tests` | volatile built-ins are not folded (`volatile.rs`); closure executor against native code (`exec_vs_native*.rs`); regions, mixed mode, memo tables (`regions.rs`, `mixed_*.rs`, `jit_mixed.rs`, `exec_*.rs`) |
| `tlx-runtime/tests` | parallel BFS, traces, worker panics under `TLX_PARANOID` (`explore.rs`); safepoints; queue, spill, disk fingerprint set, checkpoints; observers, `-dump`, VIEW/SYMMETRY representatives, edge recording, liveness |
| `tlx-live/tests` | liveness: hand-written cases, random graphs against brute force, scale (`TLX_LIVE_SCALE=<states>`) |
| `tlx-cli/tests` | end-to-end CLI: output format and `-tool`, `TLX_PARANOID` + `TLX_INJECT_MISMATCH` (`paranoid.rs`), config documentation against the `KNOBS` table (`config.rs`), checkpoints, memory budget, liveness, `-coverage`, `-dumpTrace`, signals, ... |

Two slow tests are `#[ignore]` by default:

```sh
# corpus encoding round trip: decode(encode(v)) = v, equal encodings iff equal values (needs corpus/out/tlc.json)
cargo test --profile test-release -p tlx-testkit --features interpreted,values --test layout_corpus -- --ignored --nocapture
# exploration throughput of native models (a performance number: use --release)
cargo test --release -p tlx-native --test bench_native -- --ignored --nocapture
```

The JIT tier is tested as the native tier of the differential harness with
`TLX_JIT=1 TLX_JIT_VERIFY=1 cargo test --profile test-release -p tlx-compile --features tlx-testkit/jit`.

### Python driver tests

```sh
python3 -m unittest discover -s scripts -p 'test_*.py'     # discover and run all Python driver tests
```

They cover the shared policy in `scripts/tlxlib.py` (paths, environment stripping, subprocess
timeouts and reaping, atomic JSON updates), argument handling, the drivers with mocks, the
counterexample validator (`test_tracecheck.py`, one JVM per case), the cloud logic without calling
any cloud API, and `test_no_cloud_ids.py`, which fails if a tracked file contains a personal cloud
identity (account IDs, ARNs, instance IDs, e-mail addresses; documented placeholders excepted).
The `cargo-test` suite of `verify.py` runs them before the Rust tests.

Unit tests for the benchmark store and suite (`test_bench_records.py`, `test_bench_suite.py`,
`test_drivers.py`) construct temporary fixtures under scratch directories rather than mutating or
assuming the working tree's `bench/` contents, while `test_release_tree.py`,
`test_bench_report_evidence.py`, `python3 scripts/bench.py suite-check`, and
`python3 scripts/bench.py report --check` verify the tracked `bench/suite.json`, `bench/records/`,
`bench/tlc-baselines/`, and `docs/performance.md` shipped with the repository
([benchmarking.md](benchmarking.md) section 6.2).

Other driver commands: `python3 scripts/matrix.py --list`, `python3 scripts/fuzz_expr.py --show
--seed 1 --count 5`. The drivers' default parallelism is 3 jobs; TLC runs are capped at 2 JVMs at
a time in `matrix.py` (`--tlc-j`) and `fuzz_expr.py`.

### Public Python tooling

Public Python tests live in `scripts/tests/`. Run them with
`python3 -m unittest discover -s scripts -p 'test_*.py'`; discovery recurses into the test package.
The command entrypoints `scripts/bench.py` and `scripts/cloud_verify.py` delegate to
implementation modules in `scripts/benchmarking/` and `scripts/cloud/`, respectively.

`scripts/harness/` provides shared libraries for the public tools, including Git,
process management, and storage helpers. It is included in the published sources.
Local development configuration and archived process material are excluded by
`scripts/unshipped.py`. Public contributor instructions live in [AGENTS.md](../AGENTS.md).
Benchmark inputs and current measurement records are tracked; see
[bench/README.md](../bench/README.md) for their layout.

## 5. Spec tests: `scripts/spectest.py`

`tests/specs/NAME.tla` + `NAME.cfg` are small specs, each targeting one semantic point (the file
name prefix is a rough grouping: E semantics and configuration errors, EK evaluation error kinds,
G generate, L liveness, S simulation, V VIEW/SYMMETRY; most specs start with a comment saying what
they test). A `.tla` without `.cfg` is a module other specs use. The script runs tlx on every spec
and compares with TLC by the three tiers of the contract:

| Tier | Compared | How |
|---|---|---|
| 1 | result kind (an error only as "error", not its class or exit code); violated names (invariant, action property, initial-state property, POSTCONDITION) | exact |
| 2 | distinct, generated, depth; length of safety counterexamples | exact (simulation: result kind only, plus generated with `# deterministic`) |
| 3 | the counterexample itself; for liveness, which property names are reported | equal to TLC passes; otherwise validated by TLC (below) |

The parity drivers (spectest, difftest, tlcsuite, matrix, fuzz_expr; `tlxlib.parity_args`) run tlx
with `-tlc` (TLC-compatible results) and an explicit tier: `-interp` unless the arguments choose
`-compile` (the compiled tier is tlx's default, the interpreter the drivers' plain mode). Flags an
older binary does not list in its `-h` (verify.py `--baseline`'s merge-base build) are left out;
it has these semantics by default. In the Rust tests `tlx!()` adds `-tlc -interp` after `check`
the same way (a later `-compile` wins); `tlx_default!()` runs the default mode and tier.

```sh
scripts/spectest.py                                    # interpreter
scripts/spectest.py --extra=-compile                   # compiled tier
TLX_PARANOID=1 scripts/spectest.py --extra=-compile    # compiled tier + cross-check
scripts/spectest.py L1 L2                              # selected specs
scripts/spectest.py --extra="-workers 8"               # multi-worker: see below
scripts/spectest.py --refresh L1                       # re-run TLC for L1 (needs Java)
scripts/spectest.py --timeout 30 STK2                  # cap tlx wall time
```

All pass with `N/N passed`, optionally followed by `(M trace differs, valid)`; any failure exits 1.
`--timeout S` (default 120 seconds, or `TLX_SPEC_TIMEOUT`) bounds each tlx run and, when collecting
an oracle, the TLC runs for that case together. A spec's `.flags` can lower it with `# timeout S` and
set a CPU-time budget with `# cpu-timeout S` (user + system time of the child, checked when it exits).
Exceeding either budget emits a structured `timeout` failure, including for expected errors and known
differences. The STK recursion-error specs use 10 seconds of wall time and 5 seconds of CPU time.
Write the extra argument with `=`: `--extra -compile` and `--compile` are rejected by argparse (an
unknown spec name also exits 2 with a "did you mean" hint instead of running anything).

- **Cached TLC results.** TLC's normalized `-tool` output is cached in `tests/specs/tlc/NAME.out`
  (summary in `tests/specs/expected.json`; both are in git). TLC runs only for a new spec or with
  `--refresh`, so daily runs need no Java. Commit the new `.out` files with the new spec. The script
  rewrites `expected.json` on each run.
- **Per-spec options.** `NAME.flags` (optional) holds extra arguments for both checkers (for
  example `-simulate num=5 -depth 20`); a `# env K=V ...` line sets variables for the tlx run only
  (for example `TLX_PRERUN=1` to force layout misses in compiled mode); `# deterministic` makes a
  simulation/generate spec also compare the generated count; `# xfail ID` marks a known tier 1
  difference listed in [compat.md](compat.md) (the spec reports XFAIL while it differs and XPASS,
  a failure, once it is fixed so the marker can be removed). A multi-worker run compares fewer
  fields, so its marker may go unobserved: a passing case then stays a pass rather than XPASS.
  Other `#` lines are comments.
- **Multi-worker mode** (`--extra="-workers N"`, N > 1) compares only what must hold with several
  workers: result kind (an evaluation error TLC stops at may lose the race to a violation, so any
  non-success failure is accepted then) and violated names; counts and depth only for complete
  explorations; no counterexample comparison. Specs using `TLCSet`/`TLCGet` depend on scheduling
  and are not compared. TLC's expectation is always the 1-worker cache.
- tlx runs in a private copy of `tests/specs`, so specs that write files cannot race with another
  run in the same checkout.

**Counterexample validation** (`scripts/tracecheck.py`). When tlx's counterexample differs from
TLC's, the script generates a trace-check module (the original spec plus an index variable) and
lets TLC check it:

- Safety: Init is restricted to the first state of the counterexample, Next to the step to the
  next state; a step that is not a spec step makes TLC report a deadlock. An invariant is false only at the
  final state (or step) if it really violates the reported property, and TLC must report exactly
  that.
- Liveness (lasso): the module's only behavior is the lasso; TLC checks that it violates the
  conjunction of the properties tlx named. tlx must name at least one property.
- No CONSTRAINT, ACTION_CONSTRAINT, SYMMETRY or VIEW is used (the exception is the closing step of
  a lasso under VIEW/SYMMETRY, which only has to be valid modulo the VIEW, see D-10 in
  [compat.md](compat.md)).
- Outcome: `PASS NAME ... (trace differs, valid)`; or FAIL with both reports; or `(trace differs,
  unvalidated: reason)`, which passes with a soft warning (no Java, or TLC's own counterexample
  fails the check, for example under SYMMETRY or when run-time string order matters).
- Results are cached in `tests/specs/tlc/validated.json` (keyed by hashes of spec, cfg and
  trace-check module; in git), so normal runs start no JVM. Commit new entries with the change that
  produced them.

## 6. Corpus differential tests

### 6.1 TLC oracle: `scripts/corpus.py`

Models come from `third_party/Examples/specifications/*/manifest.json`. Exhaustive models run
as-is; `simulate` models add `-simulate num=<traceCount>`; `generate` models add `-generate
num=100` and run in a scratch copy (they write CSV files).

A run starts in the directory the model's inputs are relative to, and both engines use the same
one. That is the spec's own directory by default (a spec writes its CSV/JSON output next to
itself), or the corpus root for the models `scripts/corpus.py` names as `cwd: root`
(`ROOT_RELATIVE_MODELS`): upstream's Examples CI runs TLC from the Examples root with the
manifest's relative paths (`.github/scripts/check_small_models.py`, `--examples_root .`), so a spec
that names an input `specifications/<dir>/<file>` reads it there and nowhere else.
`ewd998/EWD998ChanTrace` reads its trace as `specifications/ewd998/EWD998ChanTrace.ndjson`; from the
spec's own directory TLC and tlx both stop with an IO error. A model
that writes files still runs in a scratch copy of its directory, so concurrent runs of one model do
not collide and the shared checkout stays untouched.

```sh
scripts/corpus.py list --max-runtime 60              # models whose manifest runtime is <= 60 s
scripts/corpus.py tlc --max-runtime 60 -j 4          # run TLC, write/merge corpus/out/tlc.json
scripts/corpus.py tlc --max-runtime 60 --only-failed # re-run only the models whose TLC result was an error
scripts/corpus.py tlc --ids ewd998/EWD998ChanTrace   # re-collect one model's row (see below)
# large tier (manifest 61-700 s; about an hour: a cloud job, see cloud-verification.md section 1)
scripts/corpus.py tlc --min-runtime 61 --max-runtime 700 --name tlc-large --tlc-workers 4 -j 4 --timeout 3600
# huge tier (manifest runtime above 700 s: the 6 models KVSSafetyLarge, NanoLarge, SlushLarge,
# bcastFolklore, EnvironmentController, EWD998): not in the default selection, for the cloud
scripts/corpus.py list --tier huge
scripts/corpus.py tlc --tier huge --tlc-workers 16 --timeout 90000     # corpus/out/tlc-huge.json
```

`--max-runtime` defaults to 10 seconds (run `python3 scripts/corpus.py list` or `python3 scripts/corpus.py list --max-runtime 60` for the current manifest counts). The results file is saved after every model, so an
interrupted run keeps what finished. TLC is run by `scripts/tlc.py` (also usable alone:
`scripts/tlc.py SPEC.tla -config X.cfg -workers 1` prints JSON statistics), with its state
directory under `target/tlc-states/<pid>`.

`corpus.INVALID_UPSTREAM_MODELS` explicitly excludes `ewd998/EWD998ChanID_export` and
`ewd998/EWD998ChanID_shiviz`: their upstream `MCInit` leaves `passes` unassigned, so both TLC
and tlx reject them. Listing and collection report the exclusion reason on stderr when those
configurations fall within the selected runtime bounds. They are also excluded from shared
oracle selection, even if old cached results exist; requesting either id explicitly reports
the invalid-input reason. Other EWD998 configurations remain eligible. Remove these exclusions
only after upstream initialization is corrected and revalidated; historical benchmark records
remain unchanged. The benchmark suite resolver uses the full manifest for its explicitly
declared entries, including these invalid inputs and their historical expectations; the
exclusions apply to ordinary corpus and oracle selection.

`--ids A,B` selects exact ids inside the tier's runtime bounds. It exists for a row whose
well-formed result a staging or path fix changes: such a row is not an "error" row, so
`--only-failed` leaves it in place, and the shared `corpus/out/tlc.json` copied into a worktree
keeps the old result until the row is re-collected. `ewd998/EWD998ChanTrace` is collected with
`-fp 0` (`corpus.TLC_ORACLE_ARGS`): TLC's fingerprint polynomial is random by default and decides
the order of concurrent log lines, so only `-fp 0` gives the deterministic `generated` count that
tlx reproduces (compat.md D-25). Its row, the `bench/suite.json` pin that quotes it, and the
identity of the run moved together in one baseline upgrade: `corpus.MODEL_INPUTS` declares the trace
the model reads from its run directory, and `benchmarking.baselines.content_digest` carries the
effective working directory and the resolved bytes of every declared input, so the pre-fix staging's
evidence cannot satisfy the corrected run. The corrected row is success with 659 distinct states,
11,169 generated states and depth 655; the frozen pre-fix `error` records stay historical. The
durable receipt, including the corrected identity and the TLC/tlx counts, is
[bench/validation/2026-10-11/ewd998-chantrace-oracle.json](../bench/validation/2026-10-11/ewd998-chantrace-oracle.json).

### 6.2 Differential run: `scripts/difftest.py`

```sh
scripts/difftest.py -j 3 --timeout 120                         # interpreter -> corpus/out/tlx.json
scripts/difftest.py -j 3 --extra=-compile --tag=-compile       # compiled tier -> tlx-compile.json
scripts/difftest.py --workers 8 --extra=-compile               # 8 workers -> tlx-w8.json
scripts/difftest.py --filter DieHard -v                        # subset; -v prints failing output
scripts/difftest.py --failed --extra=-compile --tag=-compile   # re-run only the previous failures
TLX_PARANOID=1 scripts/difftest.py --extra=-compile --tag=-paranoid --timeout 600
scripts/difftest.py --extra=-compile --recover 1               # end each run after its first checkpoint, then -recover it
```

- Only models whose TLC result is not an error are tested. Compared: result kind; for complete
  exhaustive runs with TLC success also distinct, generated and depth (multi-worker runs search
  level-synchronously, so depth is exact too); simulation only the result kind; violated names
  for safety and property violations (a liveness failure only needs tlx to name one property). Exit
  codes and counterexamples are not compared.
- tlx runs in the same directory as the TLC oracle (section 6.1): its own spec directory, the
  corpus root for a `cwd: root` model, or a scratch copy for a model that writes files. The
  benchmark stages a `cwd: root` model in that same corpus root (`benchmarking.measurement`); every
  other model keeps its documented run semantics (the driver's directory, an absolute spec path).
- One line per model, `PASS/FAIL id tlc=result/distinct/generated/depth tlx=... (TLC s vs tlx s)`,
  then this run's and the cumulative pass counts. Results merge into `corpus/out/tlx<tag>.json`
  (`--tag` defaults to empty for 1 worker, `-w<N>` otherwise).
- The script copies the binary to `target/tlx-difftest-<pid>` first, so you can keep editing and
  rebuilding while it runs.
- In the default Examples selection, `SpanningTree/SpanTreeRandom` is an expected nondeterministic
  failure in `tests/expected_failures.json` (TLC's default seed is random, see compat.md D-4). The
  interpreter times out on a few large models at 120 s.

**Pitfalls**

- Do not run TLC jobs (for example `corpus.py tlc`) while `difftest` runs: CPU contention causes
  timeouts. The same applies to several concurrent test runs; keep `-j` at 3 or lower.
- TLC may leave `*_TTrace_*` files next to specs (`third_party/Examples/...`, `tests/specs/`).
  Delete them and do not commit them (the parse test and `sanydiff.py` skip or trip over them).
- `difftest` times are wall-clock under concurrent load; use `bench.py` for performance
  ([benchmarking.md](benchmarking.md)).

### 6.3 External corpora: `corpus/external.json`

Models of other projects (industrial specifications, parametric benchmarks) are corpus entries too,
with ids `ext/<repo>/<model>`. Nothing is vendored: the manifest pins each repository at a commit and
`scripts/fetch-external.py` downloads it into `third_party/external/<repo>/` (git-ignored; one
tarball, or, for repositories whose tarball is huge, the listed directories through the GitHub
contents API; `GITHUB_TOKEN` raises the API rate limit). Repositories without a license may only
be fetched like this, never copied into this tree. Our own files (a cfg for a repository that
lacks one or has a broken one, a wrapper module) live under `corpus/external/<repo>/` at the path
they should have in the fetched tree and are copied over it on every fetch.

```sh
scripts/fetch-external.py                              # every repository of the manifest (--repos a,b; --force; --list)
scripts/corpus.py list --source external               # tiers small and medium (--tier large,huge for the others)
scripts/corpus.py tlc --source external --tier small -j 2 --timeout 900 --only-failed   # TLC oracle -> corpus/out/tlc-ext.json
scripts/difftest.py -j 3 --filter ext/ --timeout 300 --tag=-ext           # difftest finds the external oracle when
                                                                          # the filter or --ids names ext/ models
scripts/difftest.py -j 1 --filter ext/ --oracle tlc-ext-large --workers 8 --extra=-compile --tag=-ext-large
                                                                          # also the large tier (its own oracle file)
```

Manifest entries: `repos.<name>` (`repo`, `commit`, optional `root` = the directory that becomes the
top of the tree, `fetch` = `tarball` (default; with `include` only those paths are unpacked) or
`files` with `include`, `sha256` for a tarball, `license`, `attribution`, `redistributable`) and
`models[]` (`name`, `repo`, `tla` and `cfg` relative to the fetched tree, `tier`, informational
`runtime` = TLC time with one worker on a busy machine, optional `features` (e.g. `action
composition`: TLC runs with `-Dtlc2.tool.impl.Tool.cdot=true`), `scratch`, simulation `flags`,
`oracle_workers`). The tier is by TLC's expected time with one worker: `small` up to a few
minutes, `medium` up to about half an hour, `large` hours, `huge` days; the default selection is
small and medium (oracle `corpus/out/tlc-ext.json`), so an oracle run of the others is a
deliberate cloud job with its own oracle file (`tlc-ext-large.json`, read by `difftest.py
--oracle tlc-ext-large`). The large oracle runs TLC with several workers (`--tlc-workers`):
TLC's counts and depth of a complete run do not depend on the workers (compat.md D-3), but those
of a violation do, so a model that can end in a violation has `"oracle_workers": 1` and gets one
worker anyway. difftest compares counts and depth only for complete runs (and verdict and
violated name for every run). The external oracle is kept apart from `corpus/out/tlc.json`:
`difftest.py` and the other scripts that use `load_oracle` only see the `ext/` models when
`--filter` starts with `ext/` or `--ids` names one, so the default corpus runs are unchanged.
Flags other than simulation flags are not possible (the scripts take a model with flags for a
simulation); use a cfg of ours instead (`CHECK_DEADLOCK FALSE`). Models that read environment
variables get a wrapper module of ours whose cfg overrides the definitions that read them
(`ccf/consensus/MCccfraft_tlx.tla`).

`verify.py`'s full tier covers the external corpora (section 12): `corpus-ext` (`-compile`),
`corpus-ext-interp` and `corpus-ext-w8` on the small tier; `corpus-ext-paranoid` (small tier),
`corpus-ext-large` (medium and large tiers, `-compile -workers 16` only),
`corpus-ext-medium` (only the medium tier in that mode), and
`corpus-ext-medium-paranoid` (medium tier, `-workers 16`) when named with `--suites`. The medium
and large tiers run with 16 workers only, never with one worker or in the interpreter (user
decision 2026-10-06); `difftest.py --tiers` selects the tiers. Under SYMMETRY or VIEW, TLC's
counts with several workers vary between runs (seen: `ext/neon/MCProposerAcceptorStatic_p2_a3_t3_l3`
17,936,089 and 17,936,128 distinct states with 12 workers), so a count difference on such a model
is inconclusive; verdict and violated name still must agree. The
cloud run uploads `third_party/external` (fetch it first). The oracles of the medium and large
tiers come from a cloud run of TLC: `cloud_verify.py --oracle "tlc --source external --tier
medium ..." --oracle "tlc --source external --tier large --tlc-workers 8 ..."`
([cloud-verification.md](cloud-verification.md) section 3), which brings the `tlc*.json` files
back; copy them into `corpus/out/`. A linked worktree refreshes its private oracle copy first
([section 6.5](testing.md#65-the-worktree-oracle-snapshot)).

| Repository | Upstream, pinned commit | License | Attribution |
|---|---|---|---|
| `mongo` | mongodb/mongo `1c1e012583df`, `src/mongo/tla_plus` | CC-BY-3.0-US (the specifications) | Copyright MongoDB, Inc. |
| `ccf` | microsoft/CCF `a5d04970798a`, `tla` (our wrapper `MCccfraft_tlx` and its cfg files) | Apache-2.0 | Copyright Microsoft Corporation |
| `neon` | neondatabase/neon `fa504217c61b`, `safekeeper/spec` | Apache-2.0 | Copyright Neon Inc. |
| `vanlightly-raft` | Vanlightly/raft-tlaplus `69ad9d6092f1` | MIT | Copyright Jack Vanlightly |
| `vanlightly-kafka` | Vanlightly/kafka-tlaplus `823615e8a096` (our cfg files with smaller bounds for KRaft) | MIT | Copyright Jack Vanlightly |
| `vanlightly-vsr` | Vanlightly/vsr-tlaplus `7566e8af7bb4`, `vsr-revisited/paper` | MIT | Copyright Jack Vanlightly |
| `vanlightly-bookkeeper` | Vanlightly/bookkeeper-tlaplus `fe199dc717b5` (our cfg files without deadlock checking) | MIT | Copyright Jack Vanlightly |
| `alpha-zk` | AlphaCanisMajoris/zookeeper-tla-spec `c633af379dbe` (our wrapper `MC_tlx_Zab_new`) | Apache-2.0 | the upstream authors |
| `pragmatic` | ElliotSwart/pragmaticformalmodeling `ea86b1b5852d` | MIT | Copyright Elliot Swart |
| `tezedge` | tezedge/tezedge-specification `bd4538407bd5` | MIT | Copyright the TezEdge authors |
| `apalache-tests` | apalache-mc/apalache-tests `1b76b8e70549`, `parametric` | Apache-2.0 | the Apalache authors |
| `cassandra` | apache/cassandra `b15526b48165`, `formalise/accord/execution/tla` (cells of its `matrix.py`, generated with its `gen()`) | Apache-2.0 | Copyright the Apache Software Foundation |
| `etcd-raft` | etcd-io/raft `1c0011d2c6b7`, `tla` (our cfg files with smaller bounds) | Apache-2.0 | Copyright the etcd authors |
| `elastic` | elastic/elasticsearch-formal-models `ca30663506a7` (our wrappers and cfg files from the Toolbox models) | Apache-2.0 | Copyright Elasticsearch B.V. |
| `logless-reconfig` | will62794/logless-reconfig `05178a700a05` | none: fetched only, never vendored | William Schultz |
| `snapshot-isolation` | will62794/snapshot-isolation-spec `99ff1fd5ba64` | none: fetched only | William Schultz |
| `mongo-repl-models` | will62794/mongo-repl-tla-models `48ef5d7e7d13` | none: fetched only | William Schultz |
| `paxosstore` | Disalg-ICS-NJU/PaxosStore-TLA `0188955e7023`, `experiment/TPaxos` (our wrappers and cfg files from its `.ini` models) | none: fetched only | Disalg-ICS-NJU |

Integrated models: query the live inventory across the 18 repositories above with
`python3 scripts/corpus.py list --source external --tier small,medium,large,huge` (or pass a single
`--tier` to inspect each tier). Industrial protocol models: MongoDB
replication and sharding, CCF consensus and consistency, Neon safekeeper, Kafka KRaft and data
replication, Viewstamped Replication, BookKeeper, Raft variants (Vanlightly, MongoDB's logless
reconfiguration, etcd), ZooKeeper Zab, Cassandra Accord, Elasticsearch, Tencent PaxosStore,
snapshot isolation. The huge tier (days of TLC, or no finite state space: `ext/pragmatic/
storagecleaner`'s constraint does not bound its failure counter) has no oracle.

Models left out (the reason, for later): Vanlightly's `BookKeeperProtocolWithLimbo` (upstream
does not parse: operators called with the wrong number of arguments); the KRaft and VSR
configurations as published (10^8 states and more: our smaller cfg files instead); CommunityModules
tests (`TLCExt!AssertError`); SwarmKit (nested modules); the NJU ZooKeeper and PingCAP
specifications (cfg files to be written from `.ini`/Toolbox models).

### 6.4 TLC's regression suite: `scripts/tlcsuite.py`

TLC's own tests are the densest source of language and configuration corner cases. The suite
(tlaplus/tlaplus at the commit pinned under `suites` in `corpus/external.json`: `test-model` and
the JUnit sources of the model-checker tests) is fetched into `third_party/external/tlaplus-tests`.
`tlcsuite.py` turns every model-checker test (a `ModelCheckerTestCase`, `PCalModelCheckerTestCase`,
`SuiteTestCase` or `SuiteETestCase` class) into a case: spec, command-line arguments, whether the
test checks deadlock. The oracle is TLC itself, re-run on the case (`-workers 1`, cached in
`corpus/out/tlcsuite.json`); the JUnit expectations (exit status, state counts) are only
cross-checked. tlx is run with the same arguments and compared by contract tiers 1 and 2 as
`difftest.py` does (result kind, violated names, and counts and depth for a successful run;
simulations only the result kind).

```sh
scripts/tlcsuite.py -j 3                      # fetch, TLC oracle (2 JVMs; 10-20 minutes the first time), tlx, report
scripts/tlcsuite.py --filter Github71 -v      # a subset; -v prints skipped cases and the tail of failures
scripts/tlcsuite.py --list                    # the cases
scripts/tlcsuite.py --update-expected         # regenerate tests/tlcsuite_expected_failures.json (see below)
scripts/tlcsuite.py --extra=-compile          # the compiled tier
```

As the JUnit harness does, cases get `-deadlock` unless the test checks deadlock, PlusCal tests
are translated with `pcal.trans` and the test's own options first (in a private copy of the
directory; this prepares the input for both checkers), `-lncheck` is dropped, and a `-config
X.tla` (the config is a `---- CONFIG ----` section of the module) becomes a cfg file. Tests with
`@Ignore` or non-literal arguments are skipped; a case whose TLC run does not finish in 120 s
has missing oracle evidence and fails the gate. In the pre-`v0.1.0` baseline run against TLC
`rev 1813307` (before the structured gate; run `python3 scripts/tlcsuite.py --list` for the current
case inventory): 538 test
classes, 483 cases run, 52 skipped, 3 without a TLC result; **382 pass, 101 are expected
failures, 0 unexpected**; the JUnit expectations agree with TLC on 459 of the 483 cases.

The selected test list is independent of the oracle cache. Cache entries record input and
module dependency digests, the TLC jar and Java identity, arguments, collection budget and
completion state. A timeout or collection failure is missing evidence, never a semantic
oracle: the case remains selected and fails verification. Increasing `--oracle-timeout`
retries cached timeouts; collection errors and stale entries are retried automatically.
The coverage summary reports `to_test`, `verified`, `missing`, `stale` and `skipped` counts
(and how many stale entries were refreshed). Legacy entries without this metadata are stale.
`verified` counts completed semantic comparisons, excluding even expected tlx timeouts.

`tests/tlcsuite_expected_failures.json` classifies the differences: an entry has the case name
(a glob is allowed), a short `reason`, optionally the `result` kind tlx reported and `flaky`
(a timeout under load). The reasons name out-of-contract options (`-continue`, `-dfid`,
`-maxSetSize`, `-invlevel`, `-view`, `-dumpTrace` state files) and the known gaps (TLCGet
`"all"`/`"all:named"`, `\cdot` with context, a SPECIFICATION or PROPERTY wrapped in an operator
or LET, lazily evaluated ASSUME bounds, `_POSSIBLE` cfg items, Java overrides). A listed case that
now passes is reported as FIXED and fails the gate: remove the entry. After a fix lands,
`--update-expected` re-runs the cases and rewrites the file: entries that still fail are kept with
their reasons, entries that no longer match are dropped, new failures get a reason derived from the
difference (known gaps by a pattern table in the script; edit the text if it is not right).
`verify.py --full` runs the suite (`tlcsuite`, release binary, `-j N`) and classifies failures with
this file; without a cached oracle in `corpus/out/tlcsuite.json` the suite first runs TLC on every
case.

### 6.5 The worktree oracle snapshot

Every oracle above (`tlc.json`, `tlc-ext.json`, `tlcsuite.json`, `sany.json`) lives in `corpus/out/`,
which is git-ignored. A worktree starts with a private copy of the main checkout's `corpus/out`; it is
not a live view. From the destination worktree, refresh it before collecting missing oracles:

```sh
python3 scripts/oracles.py sync --source /path/to/main/corpus/out --destination corpus/out
```

This merges shared TLC caches by entry key and provenance date, prints added and updated counts, and
preserves newer local evidence. A matching branch-specific config digest takes precedence over stale
main evidence; records of unknown age never overwrite local records. The command writes only the
destination worktree's private cache. Missing or incomplete oracle entries fail `difftest.py` and
`verify.py` as coverage errors (`scripts/oracle.py` prints `missing or incomplete TLC oracle` with a
legacy local-setup hint; in a public checkout, sync from the main worktree with `scripts/oracles.py sync`
above or collect the missing cache entries with `scripts/corpus.py tlc`).

## 7. Feature matrix and expression fuzzing

`scripts/matrix.py` generates small combination specs (templates crossed with search mode,
symmetry/view reduction, constraints, property kind, outcome, ALIAS, ...) and compares TLC with
tlx across execution tiers and worker counts, by the same tiers as spectest (validation through
`tracecheck.py`; cache in `tests/matrix/expected.json`).

```sh
python3 scripts/matrix.py --list                  # list generated combinations and current count
python3 scripts/matrix.py --list --filter mutex   # subset by substring
python3 scripts/matrix.py --filter M003 -v        # run a subset
```

A TLC timeout is recorded as a timeout; it does not abort the batch.

`scripts/fuzz_expr.py` generates random expressions with a fixed seed and compares TLC, the tlx
interpreter and the compiled tier (state-level evaluation with `TLX_PARANOID=1`), then shrinks each
discrepancy. `--show` only prints expressions, `--replay FILE.jsonl` replays saved findings (for
example `tests/fuzz/findings.jsonl`), `--no-build` reuses an existing build.

```sh
python3 scripts/fuzz_expr.py --show --seed 1 --count 5
python3 scripts/fuzz_expr.py --seed 1 --count 200 --modes tlc,interp   # needs Java
```

Both generators reserve every fourth case (25%) for heterogeneous collections,
independently of the typed generator's random choices. These probes cycle through
all 21 pairs of records, tuples/sequences, sets, functions, strings, integers and
model values, and through union, intersection, difference, subset, membership,
SUBSET, UNION, Cardinality, CHOOSE, function application, DOMAIN, set-builder,
set-map and EXCEPT. Literals and operand order vary with the seed. Comparable
pairs and comparison errors both go through `contract.compare`: an error versus
a value fails; differing error wording is informational (tier 3). Structured
expression nodes preserve lifting and shrinking. Whole-spec probes evaluate the selected operator in Next. Every fourth
heterogeneous probe stores the collections, functions with mixed domains and
functions with mixed ranges as state variables; the others store their elements
separately so an initial fingerprinting error cannot mask the selected operation.
A program counter bounds these probes to two states without a shape predicate
that could itself compare incomparable values.

A small local campaign exercises both generators and all execution modes:

```sh
python3 scripts/fuzz_expr.py --seed 1 --count 200 -j 3 --save
python3 scripts/fuzz_spec.py --seed 1 --count 100 -j 3 --save --replay
```

Use the cloud `build,fuzz` verification suites for the final campaign. Retain
minimized saved repros for every new discrepancy and report checker bugs separately
from generator changes. Registered open heterogeneous bugs are reported as expected
discrepancies; their predicates require the recorded comparison diagnostics and
result shapes. The comparator still reports every difference, and unknown errors,
crashes, timeouts and paranoid failures remain fatal. Remove the corresponding
root classifier and exact replay expectations when a semantic fix lands. `FzHeterogeneousUnion` replays the record/tuple union
comparison regression using TLC's cached one-worker error oracle.

### 7.1 Whole-spec fuzzing: `scripts/fuzz_spec.py`

`fuzz_spec.py` generates random small specs and compares TLC (one worker, the oracle) with tlx.
Spec I of seed S (`F<S>_<I>`) comes from its own random stream. It has 1-4 variables of mixed bounded
shapes (integers, booleans, strings, model values, sets, sequences, functions over enumerated,
interval and run-time domains, records with set-valued fields, tuples, bags) and 1-4 actions with
guards, parameters over constant or state-dependent sets, inner `\E`, IF branches, EXCEPT / `@@` /
`:>` updates, `x' \in S`, reads of earlier primed variables and UNCHANGED. The cfg adds random
invariants (often violated at some depth), action properties, CONSTRAINT / ACTION_CONSTRAINT, VIEW,
SYMMETRY (kept only if `tlx -checksymmetry` finds no witness against it), liveness properties with
WF/SF fairness and `CHECK_DEADLOCK FALSE`. Expressions come from `fuzz_expr.py`'s typed generator
with the state in scope. Every update is guarded by `OkV(v')`, a membership predicate of the
variable's shape, so every state space is finite; specs whose interpreter run takes longer than a few
seconds, or whose TLC run times out, are skipped.

Every spec runs in five modes, each compared with TLC by the contract tiers (a differing
counterexample must pass `tracecheck.py`): `interp`; `compile` (`-compile`, `TLX_PRERUN_REUSE=0`);
`paranoid` (`TLX_PARANOID=1`, per spec the C tier, the JIT or `TLX_PRERUN=1`); `w4` (`-workers 4`,
compiled or interpreted); `recover` (ended after its first checkpoint and continued with
`-recover`). A mismatch, crash, paranoid failure or tlx timeout fails the run. A multi-worker verdict
that differs from TLC's single-worker one is checked against TLC with as many workers: when two
different violations are found at the same BFS level, TLC with several workers can report the other
one too (D-3), and then tlx's verdict is accepted if it is TLC's. The first `--shrink`
findings (one per spec and signature) are minimized: cfg features, actions, variables, parameters,
guards and updates are dropped and expressions shrunk while the same kind of mismatch remains (a
compiled-tier mismatch whose interpreter run agrees with TLC is shrunk against the interpreter,
without TLC). Results go to `target/fuzz-spec/seed-S/` (`report.md`, `report.json`, failing specs,
`findings/NAME/` with the minimized spec, TLC's output and `finding.json`).

```sh
python3 scripts/fuzz_spec.py --show --seed 1 --count 2         # print generated specs
python3 scripts/fuzz_spec.py --seed 1 --count 100 -j 3         # needs Java; about a minute
python3 scripts/fuzz_spec.py --seed rev --minutes 10 --expr 2000 --replay   # a short campaign
python3 scripts/fuzz_spec.py --replay-only                     # saved regressions, cached TLC oracle
python3 scripts/fuzz_spec.py --replay-only FzViewAPropTrace     # one saved regression
python3 scripts/fuzz_spec.py --record NAME                     # store TLC's output of a regression
```

`--save` copies minimized findings to `tests/fuzz/specs/` (NAME.tla, NAME.cfg, NAME.json with the
finding, `tlc/NAME.out` with TLC's output); `--replay` replays them in every mode against the saved
output (ids `replay/NAME/MODE`; an open bug is an entry of `tests/expected_failures.json` with suite
`fuzz*`). Replays and generated specs share the same comparator: differing traces are validated
with TLC for every worker count. Multi-worker runs may report another safety violation from the
same BFS level only when TLC validates the concrete trace and its reported property (D-3).
Known open differences that would otherwise recur in every campaign are classified by the
`KNOWN` list in the script (reported as known failures, not findings; `KNOWN_EXPR` likewise for the
expressions of `--expr`, see `tests/fuzz/expr-open.jsonl`); remove an entry when its bug is fixed. `--expr N` also runs `fuzz_expr.py` with the same seed, `--seed rev` derives the seed from
the checked-out commit, `--minutes M` generates until M minutes have passed, `--shrink-known` also
minimizes known differences. `--results-json` writes the case report of section 12 (ids
`gen/NAME`, `replay/NAME/MODE`, `expr/seed-S`). The verify.py suites `fuzz` (full tier: 100 specs,
1000 expressions, the regressions) and `fuzz-campaign` (by name; `--fuzz-minutes`, default 30) run
it; large campaigns run on the cloud:

```sh
python3 scripts/cloud_verify.py HEAD --provider tencent --suites build,fuzz-campaign \
    --fuzz-minutes 40 --max-minutes 60
```

## 8. Cross-checking modes: `TLX_PARANOID` and the JIT

With `TLX_PARANOID=1`, the compiled tier (`-compile`) recomputes every Init, the successor set of
every state and every native invariant verdict with the interpreter and compares. On a mismatch it
prints both state lists ("missing in compiled / extra in compiled") and panics (exit code 101),
also with several workers. It implies `TLX_NATIVE_SYNC` (generated C is built before the search)
and is much slower than a normal run.

```sh
TLX_PARANOID=1 tlx check Spec.tla -compile
TLX_PARANOID=1 scripts/spectest.py --extra=-compile
TLX_JIT=1 TLX_PARANOID=1 scripts/spectest.py --extra=-compile   # the Cranelift JIT as the only native tier
TLX_JIT=0 scripts/spectest.py --extra=-compile                  # generated C only
```

`TLX_INJECT_MISMATCH=drop|dup|stale|init|inv[:n]` makes the n-th injectable compiled result wrong
on purpose, to prove that PARANOID reports it (`tlx-cli/tests/paranoid.rs` does this);
`miss[:n]` forces a layout miss in the n-th compiled action or liveness atom evaluation after the
search, to prove the interpreter redoes that stage (`tlx-cli/tests/live_miss.rs`):

```sh
TLX_PARANOID=1 TLX_INJECT_MISMATCH=drop tlx check tests/specs/C7.tla -compile   # expected: panic, exit 101
```

All knobs are documented in [configuration.md](configuration.md).

### Automatic symmetry

A symmetry tlx applies without a `SYMMETRY` declaration ([usage.md](usage.md) sections 6.2 and 6.3)
is tested in four ways besides the unit tests (`tlx-eval/tests/autosym.rs`: one spec per breaker
class and per allowed class of operations; `tlx-cli/tests/autosym.rs`):

- `tlx check Spec.tla -checksymmetry -suggest` cross-checks every proven set with the bounded
  diagnostic; a witness is an internal error (exit 101). Run it over the corpus after changes to
  the analysis (`model/autosym`), also with `-symmetrystates 20000`.
- `TLX_SYMMETRY_PARANOID=N` checks the applied group at one expanded state in N (1: every state)
  in both tiers and fails with exit 101 on a mismatch. `TLX_AUTOSYM_FORCE=Set,...` marks candidate
  sets despite static-analysis rejection while still requiring a connected Lean certificate before
  application:

  ```sh
  python3 scripts/verify.py HEAD --quick --suites corpus-default --env TLX_SYMMETRY_PARANOID=1000
  ```

- `scripts/autosym_mutants.py` derives, for each corpus model where the default mode applies a
  symmetry and the state space has at most 10^5 states, 20 invariant mutants (`~P` with P an
  orbit-closed predicate of a reachable state) and 5 deadlock mutants (`Next /\ ~Q`), runs each in
  the TLC-compatible mode and in the default mode, and fails unless the default mode reports every
  violation with the same violated name, trace length and (invariants) depth. Mutants are seeded
  (`--seed`); the reference results are cached in `corpus/out/autosym-mutants.json`.

  ```sh
  python3 scripts/autosym_mutants.py -j 3              # Examples corpus
  python3 scripts/autosym_mutants.py -j 3 --filter ext/
  ```

- Runs in the default mode are compared with TLC by verdict only: `scripts/tlc.py` records the
  `Optimizations:` line and `contract.compare` refuses to compare the counts of such a run with a
  TLC oracle unless the caller asks for a verdict comparison (`optimized=True`), which checks the
  result, the violated names and the fields the optimizations preserve.

## 9. Front end against SANY: `scripts/sanydiff.py`

Runs SANY (`tla2sany.SANY`) and the tlx front end (the `tlx-sema` example `check`, which performs
`Program::load`'s checks) on each `.tla` file and lists files that one accepts and the other
rejects.

```sh
scripts/sanydiff.py -j 4                 # default: every .tla under third_party/Examples/specifications
scripts/sanydiff.py -j 4 tests/specs     # a directory or files
scripts/sanydiff.py --refresh            # ignore the SANY cache
```

SANY results are cached in `corpus/out/sany.json` by (path, mtime). Exit code 1 means differences.
On `tests/specs` (run `python3 scripts/sanydiff.py -j 4 tests/specs` for the current file and
rejection counts) the run reports 2 differences: `BG1.tla`
and `SM5.tla` (`Unknown operator CopiesIn`). This is a known artifact of the harness: the `check`
example searches the `-I` directories before the bundled standard modules, and
`third_party/tlapm/library/Bags.tla` is an older `Bags` without `CopiesIn`. `tlx check` itself
accepts both specs (they pass `spectest`).

## 10. Compiled-tier coverage: `scripts/coverage.py`

`coverage.py` selects models from the Examples manifests (`--source corpus`),
`corpus/external.json` (`external`), `bench/suite.json` (`suite`), or their union
(`all`). Missing inputs, unsupported models and timeouts stay in the denominator;
selection never depends on a successful TLC oracle. No TLC process is launched.

```sh
python3 scripts/coverage.py --filter transaction_commit --models
python3 scripts/coverage.py --dynamic --source corpus --max-runtime 1 --timeout 20 -j 3 --out target/native-small.json
python3 scripts/coverage.py --dynamic --source all --sizes all --timeout 120 --deadline-min 45 -j 3 --out bench/native-census.json
```

Use small configurations locally; the last command is a cloud workload. The
cloud launcher accepts the same command through its forwarding entry:
`--bench "coverage --dynamic --source all --sizes all --timeout 120 --deadline-min 45 -j 3 --out bench/native-census.json"`.
`--prioritize A,B` measures matching model IDs first. `--bin` selects an existing
binary; otherwise the driver builds the test-release profile (`--release` selects
release). Every subprocess has a timeout and JSON checkpoints after each model. Dynamic
runs allow five additional seconds after TERM for spill cleanup. The current CLI
then exits without final statistics: this does not recover partial counters.
The primary tracked ratio stays unknown for every timeout. Truncated statistics are
an explicit gap, not a successful measurement. The cloud
prelaunch path runs local release all-target Clippy before reserving a launch,
then requires a measured native-share field from all three tiny smoke fixtures.
A dynamic census exits 2 when any selected model has no complete nonempty
measurement, while keeping all evidence. Static mode stops after the lowering
report and exits 2 for missing reports. `--dump DIR` preserves full text output.

Static JSON includes expression-node histograms by typed/boxed/interpreted
representation, operation and argument shape, plus native rejection reasons and
functions that stayed in closure IR. Counts include compiled helper functions;
with layout restarts each reported program version contributes its own nodes.
A typed node is not a promise of backend support, and a boxed node need not use
the interpreter: native runtime helpers can handle boxed values.

Dynamic `native_share` is **fully native action and predicate evaluations / all
such evaluations**, combining actions, invariants, state constraints, action properties and action
constraints and evaluated liveness atoms within
search units. Init, quiet pre-runs and liveness graph reconstruction are outside
this denominator. Counters are exact across all workers and layout versions,
including repeated work; a mixed function counts as native when that particular
call short-circuits before entering any host region. Closure IR, interpreted and
fallback calls never count as fully native. Empty/missing statistics are unknown,
not 100%. Timeouts are incomplete; any available partial ratio is retained
separately and never promoted to the tracked metric.

`host_time_share` divides inclusive elapsed host-region seconds by sampled,
extrapolated search-unit thread-seconds. It is diagnostic attribution, not a CPU
fraction or additive partition; sampling and nesting can produce values above
one. Region JSON retains search-unit-only calls, nanosecond-resolution time, operation,
argument shapes and enclosing function from every layout/escape version.
Ranked rows distinguish models where a region exists from `executed_models`
with at least one observed call; zero-call presence is not a dynamic gap.
Host tables do not time operations performed directly in whole-function closure
IR; `closure_evaluations` exposes those path counts and their static blockers.
When no static rejection exists, the report labels the path unattributed: startup,
adaptive tier selection and a runtime fallback can also execute closure IR.
See [native-coverage.md](native-coverage.md) for measured rankings and
estimated lowering families.

`bench.py track` stores `native_coverage` per model/mode/worker configuration in
its history record (shares and aggregate counts/time, without unbounded region
tables). It reuses the discarded preheat run for statistics, leaving
measured performance samples uninstrumented. A native-share drop greater than
one part per million is a regression, independently of timing noise; a missing
new metric when the baseline has one is inconclusive. Old baselines without the
counter establish a new coverage baseline. Host time share is retained for
attribution but does not independently fail the timing gate. Adaptive tier
selection can change the measured native share between runs; a coverage alert
identifies a change in execution paths, not a semantic error or a proven slowdown.

## 11. Sanitizer and Miri runs

These are not part of `verify.py`.

- **Generated C under ASan + UBSan**: `TLX_CC_SANITIZE=1` builds the generated C with sanitizers
  (`-O1 -g`; part of the build cache key, so sanitized and normal builds never mix). On macOS the
  host must preload the runtime:

  ```sh
  TLX_CC_SANITIZE=1 TLX_NATIVE_SYNC=1 TLX_CACHE=/tmp/tlx-asan \
  DYLD_INSERT_LIBRARIES=$(cc -print-file-name=libclang_rt.asan_osx_dynamic.dylib) \
  ASAN_OPTIONS=detect_leaks=0 tlx check Spec.tla -compile
  ```

  Do not also preload the standalone UBSan runtime, and do not go through a SIP-protected wrapper
  (it strips `DYLD_*`).
- **Miri** over the pure-Rust crates with `unsafe` (`cargo +nightly miri test -p tlx-value`, `-p
  tlx-live`, and `-p tlx-runtime --lib` with skips for tests that use files, `mmap`, FFI or stack
  switching): see [unsafe-audit.md](unsafe-audit.md) for the recorded results and the skip list.

## Helper drivers: exit codes

`scripts/autosym_mutants.py`, `scripts/matrix.py`, `scripts/sanydiff.py`, `scripts/verify_compare.py`
and `scripts/ir_receipt.py` each report one comparison instead of running a whole suite. They follow
the harness exit convention — `0` consistent, `1` a difference or a failed run, `2` no verdict (the
invocation or the engines decided nothing) — and count their cases with the shared acceptance
vocabulary of `scripts/contract.py` ([HARNESS-05](development-standards.md#harness-05)):
`selected`, `eligible`, `executed`, `observed`, `skipped`, `inconclusive`, `infra_failed`. Every
driver prints an `observations: <counts>` line (a field with count 0 is omitted) and, when it
refuses to report success, a `<driver>: <reason>` line before exiting `2`; a driver that scheduled
zero cases (an empty selection) exits `2`, never `0`.

`scripts/ir_receipt.py` is the receipt for a behavior-preserving refactor of the compiled tier: it
builds (or reuses, from `target/ir-receipt/bin/<sha>/`) the release binary of two revisions, runs a
fixed list of small specs through `-compile` with a fresh native-code cache and the knobs that force
compilation and dump the generated code (`TLX_PRERUN_REUSE=0`, so a spec that finishes inside the
shape pre-run is still compiled, `TLX_IR_DUMP=*`, `TLX_IR_DUMP_RAW=1`, `TLX_JIT=0`,
`TLX_NATIVE_SYNC=1`, `TLX_IR_VERIFY_HARD=1`), normalizes its volatile fields (paths, timestamps) and
compares the typed IR dump, the generated `model.c`, the search output and the exit code per spec; a
spec that dumps no IR or leaves an empty `model.c` is a failed run, never an identical receipt (a
JIT-backed run writes no C source, and two empty files would agree byte for byte). This receipt covers the
generated-C path only: the run pins `TLX_JIT=0`, so a refactor of the JIT tier is not covered and
needs its own comparison.

| Driver | `0` | `1` | `2` |
|---|---|---|---|
| `scripts/autosym_mutants.py` | every mutant the domain could judge is detected | a mutant failed (a missed violation, a differing trace or depth, an unreduced run) or a run produced no verdict | no eligible model, or not one mutant the domain could judge |
| `scripts/matrix.py` | every selected run was judged and matched TLC | a run mismatched or produced no usable output | no spec selected, or no run selected |
| `scripts/sanydiff.py` | SANY and tlx agree on every file | a file one accepts and the other rejects | nothing selected, or a file where SANY or tlx produced no verdict |
| `scripts/verify_compare.py` | every compared result agreed | a result differed | fewer than two directories, a missing directory, no suite log, or not one comparable (suite, id) pair |
| `scripts/ir_receipt.py` | every selected spec ran and its IR, `model.c`, output and exit code match byte for byte | a spec's IR, `model.c`, output or exit code differed | a revision that does not resolve or build, a missing spec, a run that times out, exits `2`/`101`, dumps no IR or leaves an empty `model.c`, or a cache without exactly one generated `model.c` |

What each prints:

- `autosym_mutants.py`: `PASS`/`FAIL`/`NONE <model>: <n> invariant and <m> deadlock mutants detected,
  <k> invalid; trace lengths [...]` per model (`NONE` when not one mutant of that model could be
  judged), `SKIP <model>: <why>` for a skipped model, one
  `<status>: <model> <mutant> ref=... got=...` block with the engine output per failing mutant, and
  the summary `<models> models (<skipped> skipped), <mutants> mutants, <failures> failures`.
- `matrix.py`: `running TLC on <n> specs` and `  TLC <name>: <result> <violated>` for the specs
  whose oracle was refreshed, `FAIL <name>/<tier>/w<workers>` plus the differing fields (with `-v`,
  the tail of tlx's output), `NOTE ...: counterexample differs, unchecked` (with `-v`), and the
  summary `<passed>/<total> runs passed, 0 known issues, <failed> failed (<specs> specs);
  counterexamples differing from TLC's: ...`. `--list` prints `<name> <features>` per row and
  `<n> specs`, and always exits `0`.
- `sanydiff.py`: the path plus `  SANY: ...` and `  tlx: ...` for every disagreement, the path plus
  `  no verdict: <why>` for a file SANY or tlx could not decide, and the summary
  `<files> files (<n> rejected by SANY), <diffs> differences`.
- `verify_compare.py`: `MISSING` (a result only one side recorded), `timeout`, `FLAKY` or `DIFF`
  per differing (suite, id) with a `<dir>: <value>` line per directory, the summary
  `<compared> results compared, <diffs> differences, <timeouts> timeout-only differences,
  <flakies> flaky (not compared)`, and `<lonely> suite log(s) present in one directory only: not
  comparable` when a suite log exists in only one directory.
- `ir_receipt.py`: `<spec>: identical (exit <n>, IR <n> lines, model.c <n> B, stdout <n> lines)` per
  spec, `<spec>: DIFFERS (<field> line <n>, ...)` with the first differing lines (`- base` then
  `+ candidate`) for a differing spec, `<spec>: NO VERDICT (<why>)` for a spec that produced no
  receipt, the summary `<n> specs compared, <n> identical, <n> different`, and a first line naming
  each resolved revision and its binary sha256.

## 12. The merge gate: `scripts/verify.py`

```sh
python3 scripts/verify.py                 # HEAD, quick tier (a few minutes)
python3 scripts/verify.py HEAD --full     # about half an hour
python3 scripts/verify.py --here          # the current working tree instead of a revision
python3 scripts/verify.py HEAD --quick --suites build,spectest-compile --env TLX_PARANOID=1
python3 scripts/verify.py HEAD --full --filter DieHard    # try the full tier cheaply
```

`verify.py` checks out the revision into a temporary detached worktree (symlinking `third_party`,
copying `corpus/out`), runs the suites of the tier and exits nonzero on an unexpected failure, a
compiler warning, or a suite that did not finish. Logs and `summary.json` go to
`target/verify/<time>-<rev>/`. Other options: `--suites NAME,...`, `--filter SUBSTR` (corpus model
ids), `--strict` (also fail on a FIXED cargo test; case drivers always reject XPASS), `--cold-cache` (fresh `TLX_CACHE`),
`--keep`, `-j N` (default 3), `-v`.

| Suite | Tier | What |
|---|---|---|
| `build` | quick, full | `cargo build --release` without warnings; `cargo fmt --all --check`; `cargo clippy --workspace --release --all-targets` (each warning fails) |
| `cargo-test` | quick, full | Python driver tests, then `cargo test --profile test-release` |
| `cargo-test-jit` | quick, full | `TLX_JIT=1` tests of `tlx-compile` with `--features tlx-testkit/jit` |
| `spectest`, `spectest-compile` | quick, full | spectest (`-tlc`): interpreter; compiled (default tiering: JIT, then C) |
| `spectest-paranoid`, `spectest-jit-paranoid` | quick, full | with `TLX_PARANOID=1`: C tier; JIT only |
| `corpus-compile`, `corpus-interp` | quick (curated subset in `tests/quick_corpus.json`), full (whole corpus) | difftest (`-tlc`): compiled; interpreter |
| `spectest-default`, `corpus-default` | quick (`corpus-default` uses `tests/quick_corpus.json`), full | default mode (no `-tlc`), compared with TLC by verdict and optimization-preserved fields |
| `spectest-c`, `spectest-compile-w8`, `corpus-compile-w8` | full | C tier only without reusing the pre-run's result; 8 workers |
| `tlcsuite` | full | TLC's regression suite against tlx (section 6.4; failures are classified with `tests/tlcsuite_expected_failures.json`) |
| `corpus-paranoid`, `corpus-recover`, `corpus-interp-recover`, `corpus-recover-w8` | only with `--suites` | paranoid corpus run; checkpoint then recover |
| `corpus-ext`, `corpus-ext-interp`, `corpus-ext-w8` | full | the small tier of the external corpora (section 6.3): `-compile`; interpreter; `-compile -workers 8` |
| `fuzz` | full | `fuzz_spec.py --seed rev`: the regressions of `tests/fuzz/specs`, 100 generated specs and 1000 expressions against TLC (section 7.1; needs Java) |
| `fuzz-campaign` | only with `--suites` | the same for `--fuzz-minutes` (default 30) minutes, 6000 expressions; for the cloud |
| `corpus-ext-paranoid`, `corpus-ext-large`, `corpus-ext-medium`, `corpus-ext-medium-paranoid` | only with `--suites` | the small tier with `TLX_PARANOID=1`; the medium and large tiers (oracle `tlc-ext-large.json` too) with `-compile -workers 16`, for the cloud; the medium tier alone, with and without `TLX_PARANOID=1`, at 16 workers |

The spec and corpus suites run the **release** binary (`--profile release`; the `build` suite has
built it already and it is faster); `--profile test-release` uses the `cargo-test` binary instead.
All `TLX_*` variables of the calling shell are stripped except `TLX_CACHE` and `TLX_JAVA`; use the
repeatable `--env K=V` to pass a variable to the spectest, difftest and cargo test suites (a
suite's own settings win; it is recorded in `summary.json`).

### Expected failures

Spec, corpus and TLC-suite drivers share a structured `CaseResult` protocol: an id, a status
(`pass`, `fail`, `xfail`, `xpass`, `error`, `skip`, `timeout`) and details. `--results-json PATH`
writes the selected-case manifest, per-case results, status counts and exit judgment, and the
driver's suite name (the `--suite` identifier), so a downloaded report identifies its run mode
without relying on the file name. The same
judgment is used for standalone exits and by `verify.py`; readable PASS/FAIL/XFAIL/XPASS lines
are only a rendering. A zero selection, missing case results, execution errors, unacknowledged
XPASS or a failed driver process fails the gate. A model's expected evaluation error is a
semantic verdict and can pass its comparison; it is different from an execution error.

`tests/expected_failures.json` lists the failures `verify.py` tolerates (each with a reason); every
other failure is a regression. Entries match by suite glob, model or spec id, and optionally the
result kind. A non-`flaky` entry must fail: if the model passes, `verify.py` reports XPASS/FIXED (always an error for case drivers) and the entry should be removed. Current groups:

| Group | Entries |
|---|---|
| nondeterministic TLC reference | `SpanningTree/SpanTreeRandom` (random seed changes TLC's graph); `KnuthYao/SimKnuthYao` (statistical POSTCONDITION, flaky in TLC too) |
| specs that assume one TLC worker | `DieHard/MCDieHardest`, `KnuthYao/SimKnuthYao` in `*-w8` suites; `LZT1` in `spectest*-w8` |
| multi-worker same-level choices (D-3), unnamed simulator lassos (D-1/D-2) | `FzWorkersAPropFirst` (invariant vs action property at the same level), `SN21` (D-31 error/violation race) and `LZS2` in `spectest*-w8` |
| interpreter timeouts under load | a few slow models in `corpus-interp*` and `corpus-paranoid` (flaky) |
| open bugs found by fuzzing | `replay/Fz*/MODE` in `fuzz*` (minimized regressions in `tests/fuzz/specs`) |

### Recommended local workflow

After changing semantics, the compiled tier or the runtime:

1. `cargo test --profile test-release -q --no-fail-fast -j 3`, `cargo build --release` (no warnings),
   `cargo clippy --workspace --release --all-targets` (0 warnings), `cargo fmt --all -- --check`
2. `scripts/spectest.py` and `scripts/spectest.py --extra=-compile`, each also with `TLX_PARANOID=1`
3. `scripts/difftest.py -j 3 --timeout 120` and `--extra=-compile --tag=-compile`
4. a front-end change: `scripts/sanydiff.py -j 4`
5. a performance-relevant change: a release-binary A/B, `scripts/bench.py ab`; a large or
   record-setting measurement is a cloud job ([benchmarking.md](benchmarking.md),
   [cloud-verification.md](cloud-verification.md) section 1)

For a merge, `python3 scripts/verify.py` covers all of this in a clean checkout.

## Public checks

The released sources do not require Git hooks or local automation. Run the relevant checks
explicitly and retain their exit status and output:

```sh
python3 scripts/check_imports.py
python3 scripts/knobs_check.py
python3 scripts/doccheck.py --require-examples
python3 scripts/bench.py report --check
```

Build the test-release binary before requiring documentation example parsing. The full verification
entrypoint is `python3 scripts/verify.py`; its suites and prerequisites are described in section 12.
A missing dependency, skipped test, or incomplete oracle is not evidence that the omitted checks
passed. Record the tested revision, selected cases, results and any limitations.

### Oracle evidence and comparison coverage

Corpus differential selection comes from the Examples manifests (the default
runtime tier is 0–60 seconds) and `corpus/external.json`, independently of cached
TLC results. Explicit IDs absent from the selected manifest, missing results,
collection errors and stale configuration digests are coverage errors and cause
a nonzero exit. `--tiers` selects external tiers; `--oracle` supplies additional
cache files and selects their named standard tiers, never defines the model list.

New `corpus.py tlc` records include `provenance`: TLC version, worker count,
machine OS/architecture/CPU count, UTC date and SHA-256 configuration digest.
`--only-failed` also retries stale/incomplete records and legacy records without
provenance. Old records can still be compared, but the report explicitly says
`partial=True` and counts `legacy_provenance`; their freshness is unverified.
Configuration changes invalidate records with provenance. Collection failures
are separate from TLC's semantic `error` verdicts, which are testable outcomes.

Models marked `asymmetric_symmetry` require a proven `-workers 1` oracle, even
when testing multiple tlx workers. Both difftest and bench prefer records from
`corpus/out/tlc-ext-1w.json` for these models; collect them with
`corpus.py tlc --source external --repos neon --name tlc-ext-1w` and appropriate
`--tier`/cloud placement. The manifest overrides `--tlc-workers` to one for these
models. Benchmark measurements may use several workers, but never promote such
a TLC measurement to the authoritative reference, and multi-worker counts are
explicitly marked non-comparable (compatibility D-22).

Spectest, difftest and tlcsuite share `scripts/contract.py`. Reports attach
`checked` fields and `skipped` reasons to each comparison. Deterministic failing
model checks compare recorded counts and depth, as do completed searches.
State-level random choices (the TLC RandomSubsetNext regression specs, D-4),
simulation, multi-worker early stops and periodic liveness failures use the
exceptions in `compat.md`. Fields absent from a legacy oracle are reported as
unchecked. New parsed safety results also record trace length; it is compared wherever the
oracle records it. Spectest additionally checks shortest safety-trace length and uses
its existing TLC trace validation; corpus and tlcsuite scalar reports explicitly
do not claim trace/lasso validity. Documented TLC defects retain their existing
expected-failure judgments; the comparator does not require defect parity.

Documentation checks parse complete fenced `tla` modules with `tlx parse`, check links and
registered environment names, and report skipped checks explicitly. Use `--require-examples`
when example parsing is required. The published tree includes AGENTS.md and the benchmark inputs
and current records; all public documentation links must resolve without local process archives.
