# tlx

[![CI](https://github.com/tlaplus-x/tlx/actions/workflows/ci.yml/badge.svg)](https://github.com/tlaplus-x/tlx/actions/workflows/ci.yml)
[![License: MIT](https://img.shields.io/badge/license-MIT-blue.svg)](LICENSE)

**Native-code model checking for TLA+, written in Rust.**

tlx reads TLA+ specifications (`.tla`) and TLC configuration files (`.cfg`), explores their
reachable states, and checks safety and liveness properties. It compiles models to native code
(using an interpreter for expressions or actions it cannot compile) and supports
Lean-certified [state reductions](#state-reduction-and-lean-certificates) — automatic symmetry
in default mode and opt-in state projections under `-optimize` — for safety checking. Java is
not needed to run it.

Core design and architecture:

- **Compilation specialized to each specification.** Once configuration constants are fixed,
  tlx folds constant expressions and compiles supported actions and expressions using
  model-specific value representations, reducing interpretation and dynamic dispatch while
  retaining guarded interpreter fallbacks.
- **Modular typed-IR optimization passes.** Before targeting the closure, Cranelift JIT and C
  backends, compiled-tier passes share repeated element ranks, hoist loop invariants, shape
  mixed-mode host regions, materialize shared state predicates and plan alias-checked in-place
  updates, checked by a compile-time IR verifier.
- **Compact state representations.** Where value shapes permit, flat word arrays, bitsets and
  specialized collection layouts reduce allocation and make equality and fingerprinting cheaper.
- **Parallel state-space exploration.** Level-synchronous workers share an atomic fingerprint
  table, supporting concurrent successor generation and duplicate detection.
- **Lean-certified state reduction.** Safety runs apply automatic symmetry over interchangeable
  model-value orbits in default mode and opt-in state projections under `-optimize`, each
  gated on a compiler-generated Lean certificate while preserving concrete counterexamples.

[docs/design.md](docs/design.md), [docs/optimization.md](docs/optimization.md) and
[docs/reductions.md](docs/reductions.md) explain these mechanisms and the guarded interpreter
fallback.

The initial benchmark snapshot shows a **9.27× median speedup and a 6.98× median peak-memory
reduction over TLC in single-worker default mode**, across 168 completed configurations with
matching TLC baselines.

| Execution mode | Workers | Matched configurations | Median TLC / tlx wall time | Median TLC / tlx peak RSS |
|---|---:|---:|---:|---:|
| Default | 1 | 168 | **9.27×** | **6.98×** |
| Compiled | 1 | 51 | **7.30×** | **8.32×** |
| Compiled | 16 | 22 | **11.36×** | **6.57×** |

These measurements use Tencent SA5.4XLARGE32 instances (AMD EPYC 9754, 16 vCPU, 32 GB),
one warm-up and three timed tlx repetitions. Times exclude the warm-up: the timed samples are
separate process runs that follow a discarded warm-up whose native cache may be reused across
the batch, rather than isolated per configuration, so the discarded run is not a cold-cache
measurement. Each ratio uses the same input, machine class and worker count as its TLC baseline,
and the memory ratio pairs the same two records' stored median peak RSS (`metrics.rss_mib`), so a
value above one means tlx used less peak memory; a record without a measurement is excluded
rather than read as a zero-byte footprint. The report names, per row, the optimization the tlx
record states - a row that states one
ran with it, so its counts are those of that reduced search; the row does not assert what the
TLC side was configured with. The mode cohorts differ, and the measurements compare complete
implementations (separate from later Lean gating and `-optimize` projections) rather than
isolating each mechanism's contribution. Incomplete runs and expectation mismatches are excluded;
see the [full performance report](docs/performance.md) and [open issues](docs/issues.md).

TLC is the semantic oracle: `-tlc` enforces TLC-identical verdicts and state-space statistics,
while the default mode preserves verdicts and counterexample validity ([Compatibility with TLC](#compatibility-with-tlc),
[docs/compat.md](docs/compat.md) section 0).

## Quick start

Supported platforms are macOS arm64 (Apple Silicon) and Linux x86_64 / arm64; Windows is not
supported. [docs/usage.md](docs/usage.md#1-installation) owns the installation requirements:

- Rust through [rustup](https://rustup.rs); [rust-toolchain.toml](rust-toolchain.toml) pins 1.93.0.
- A C compiler available as `cc` (clang or gcc; override with `CC`). It builds the tree-sitter
  dependency and, at run time, generated C code. If the C compiler is unavailable at run time,
  the default build can keep using the JIT.
- Java is **not** needed to build or run tlx. Running TLC or SANY for comparison requires Java.

Download or clone these sources, then run from the repository root:

```sh
cargo build --release                  # binary: target/release/tlx
export PATH="$PWD/target/release:$PATH" # use this build in the current shell
# Optional: cargo install --path crates/tlx-cli
```

The repository includes a three-state cyclic model and its configuration. Check it without
fetching any test dependencies:

```sh
tlx check tests/specs/A1.tla
```

Selected output (startup and timing lines omitted):

```text
Model checking completed. No error has been found.
4 states generated, 3 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 3.
```

To write your own first model, follow the [Counter walkthrough](docs/usage.md#2-first-run):
a complete module and configuration, a passing run, and then a violated invariant.

### A counterexample

For a larger example, fetch the test dependencies from the repository root:

```sh
scripts/fetch-deps.sh
```

This downloads the tlaplus/Examples corpus into `third_party/Examples`, together with TLC and
module dependencies used by the test scripts. DieHard asks whether the jug puzzle can be solved;
finding a solution violates its `NotSolved` invariant. These are output excerpts from runs on
macOS arm64; startup, timing and other progress lines are omitted.

```
$ cd third_party/Examples/specifications/DieHard
$ tlx check DieHard.tla
tlx version 0.1.1
compile: native code: 6/6 actions, 2/2 invariants, Init
Error: Invariant NotSolved is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
/\ big = 0
/\ small = 0

State 2: <FillBigJug line 68, col 18 to line 69, col 34 of module DieHard>
/\ big = 5
/\ small = 0

State 3: <BigToSmall line 97, col 15 to line 98, col 48 of module DieHard>
/\ big = 2
/\ small = 3

State 4: <EmptySmallJug line 71, col 18 to line 72, col 30 of module DieHard>
/\ big = 2
/\ small = 0

State 5: <BigToSmall line 97, col 15 to line 98, col 48 of module DieHard>
/\ big = 0
/\ small = 2

State 6: <FillBigJug line 68, col 18 to line 69, col 34 of module DieHard>
/\ big = 5
/\ small = 2

State 7: <BigToSmall line 97, col 15 to line 98, col 48 of module DieHard>
/\ big = 4
/\ small = 3

73 states generated, 14 distinct states found, 1 states left on queue.
The depth of the complete state graph search is 7.
```

This run exits with code 12 (invariant violation). A passing run exits with 0. From the DieHard
directory, check DiningPhilosophers with 5 philosophers, safety and liveness, on all available cores:

```
$ cd ../DiningPhilosophers
$ tlx check DiningPhilosophers.tla -workers auto
Model checking completed. No error has been found.
336 states generated, 67 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 29.
$ cd ../../../..
```

The last command returns to the repository root.

## Usage essentials

For your own model (`Spec.tla` with `Spec.cfg`), or the user guide's Counter example:

```sh
tlx check Spec.tla                             # uses Spec.cfg next to Spec.tla (compiled tier)
tlx check Counter.tla -config Counter-spec.cfg # another configuration file (user guide, section 2)
tlx check Spec.tla -workers auto               # level-synchronous parallel BFS on all cores
tlx check Spec.tla -interp                     # the interpreter only (tlx's semantic reference)
tlx check Spec.tla -tlc                        # TLC-compatible results (counts, depth, traces)
tlx check Spec.tla -noautosymmetry             # disable default-mode automatic symmetry
tlx check Spec.tla -optimize                   # opt-in state projection and Lean output
tlx optimize Spec.tla -output DIR              # export a reduced scalar model + Lean proof
tlx check Spec.tla -simulate num=100 -depth 50 -seed 1   # random simulation
tlx check Spec.tla -checkpoint 10 -metadir DIR           # checkpoint every 10 minutes
tlx check Spec.tla -recover DIR                          # continue an interrupted run
tlx check Spec.tla -I path/to/modules       # extra module search path
tlx check -h                                # every option
```

The supported options generally follow TLC's spelling and meaning (single dash; `-deadlock`
*disables* deadlock checking, as in TLC). Also available: `-tool` (TLC's `@!@!@STARTMSG` message format),
`-dump` / `-dumpTrace` (state graph and counterexample export), `-coverage`, `-stats`
(where the time went), `-generate`, `-maxmem` and disk spilling for large state spaces.
Builds of generated code are cached in `~/.cache/tlx`.

Full references: [docs/usage.md](docs/usage.md) (user guide: a self-contained first-run
tutorial, compiled mode, output and exit codes, troubleshooting) and
[docs/configuration.md](docs/configuration.md) (every command-line option and `TLX_*`
environment variable).

## State reduction and Lean certificates

Automatic state reductions require a compiler-generated Lean certificate connected to
that application:

1. **[Automatic symmetry](proofs/symmetry/README.md) (default mode).** Applies disjoint
   products of full permutation groups (two to seven model values each, total order at most
   5,040) when backed by a connected Lean certificate across keyed state (`KeyedCertificate`:
   fixed/mixed maps, scalar or optional key slots, sets of keys, single-key tagged record
   sets, and fixed records), recursive equivariant finite values (`EquivSymCertificate`:
   key-valued and nested maps, multi-key
   records, bounded sequences/tuples, set comprehensions, `KSubset`, `IsInjective`), or
   choice-irrelevant `CHOOSE` (`ChooseSymCertificate`: unique-witness `CHOOSE`, projected
   uniform/constant-value `CHOOSE`, and commutative-associative recursive `CHOOSE` integer
   set-sum folds).
2. **Opt-in state projections (`-optimize`).** Installs a certified `VIEW` key while keeping
   concrete states and transitions intact for counterexample replay; each certificate proves
   initialization, successor correspondence, observations, counterexample lifting and deadlock
   preservation:
   - *Unobserved variables:* erases dead variables with literal/copy/frame updates (and can
     [compose with keyed symmetry](proofs/symmetry/README.md) through one shared source model).
   - *Phase-dependent fields:* [erases record or map fields](proofs/field/README.md) in phases
     where they are overwritten before their next use, with Lean-checked finite liveness tables.
   - *Sequence lengths:* merges sequences when every consumer depends only on current lengths.
   - *Ordered allocation and live versions:* reduces scalar or fixed nested allocation frontiers
     ([nested allocation example](proofs/ordered/README.md), 13 states across two families) and
     immutable version tables ([LiveVersions.tla](proofs/ordered/LiveVersions.tla), 89 states).
   - *Finite history summaries and relative ages:* summarizes append-only event histories over
     finite domains including prefix-predicate feedback ([history example](proofs/history/README.md),
     6 states), caps relative timestamp ages ([age example](proofs/age/README.md), 4 states),
     and combines supported age and history reductions (15 states; 113 states with two slots and
     age-filtered sets; 135 states in [DependentHistory.tla](proofs/age/DependentHistory.tla)
     with dynamic filter domains and dependent transfers).
   - *Threshold counters:* [saturates scalar or fixed-domain](proofs/counter/README.md) monotone and
     resettable natural counters at `min(c, K)` in the `VIEW` when every read is a threshold
     comparison, keeping concrete un-capped counter values in traces (and forgetting a monotone
     counter no accepted predicate reads, `K = 0`).
3. **[Counter export](proofs/counter/README.md) (`tlx optimize`).** Emits closed Lean proofs
   for each actual cleanup and threshold-saturation pass plus their composition. The generated
   finite model can be checked separately; export does not itself check safety.

Every implemented reduction family has connected rule-IR certificates for its enabled subset.
Broader age/history combinations, dynamic allocation containers, identifier-containing version
payloads and other symmetry combinations remain unavailable without connected certificates.
Unsupported candidates stay unapplied; another certified rule may still apply. Explicit user
`VIEW` and `SYMMETRY` declarations retain their TLC behavior.
See [the coverage inventory](docs/optimization.md#proof-coverage).

Optimized checking and certified automatic symmetry always write standalone Lean
(cached under `~/.cache/tlx/proofs` or `-proofdir`) and print its path; they never
invoke Lean. If `-optimize` finds no certified rule, the file records that no
reduction was applied.
Development of a new or changed reduction requires explicit Lean verification, an axiom
audit and negative tests. Verification is optional during ordinary checking.

The certificates prove preservation of a parametric rule model. TLA+/HIR lowering,
domain and totality analysis, the emitted runtime key and backend execution remain
trusted; these are not proofs of the input model's safety or state count. Accepted
allocation and relative-age reductions use [mathematical integer semantics](docs/compat.md#0-the-three-tiers);
runtime arithmetic stays checked. Concrete values remain available in counterexamples.
The [Lean coverage description](docs/optimization.md#lean-output-for-checking) explains
verification; the [blob case study](proofs/blob/README.md) supplies a manual protocol proof.

These features are separate from the frozen performance snapshot above. Generation of
a certificate does not imply Lean acceptance or a measured speedup. Output locations,
failure behavior and option interactions are specified in [configuration.md](docs/configuration.md).

## Compatibility with TLC

The contract has three tiers ([docs/compat.md](docs/compat.md) section 0):

1. **Verdicts**: the kind of result, the names of violated invariants, properties and
   postconditions, whether a spec or config is accepted. Must match exactly.
2. **State space**: generated and distinct counts, search depth, length of the shortest safety
   counterexample, and the semantics of the language and modules. Must match exactly.
3. **Incidental choices**: which of several equally short counterexamples, the shape of a liveness
   lasso, error class and exit code, print order. Counterexamples must be valid; other differences
   must not affect tiers 1 and 2.

Tiers 1 and 2 are promised in `-tlc` mode at `-workers 1`, subject to the documented differences
in [docs/compat.md](docs/compat.md). The default mode preserves verdicts and counterexample validity;
explicit optimization permits the mathematical-arithmetic exception described above.
With several workers, the choice of a valid safety violation at the same BFS level and the
counts, depth and trace length at an early stop are tier 3. Liveness-failure counts and depth
are timing-dependent even with one worker. Section 0 of that document owns these boundaries.

Supported: the `.cfg` keywords `CONSTANT(S)`, `INIT`/`NEXT`, `SPECIFICATION`, `INVARIANT(S)`,
`PROPERTY`, `CONSTRAINT(S)`, `ACTION_CONSTRAINT(S)`, `SYMMETRY`, `VIEW`, `ALIAS`, `POSTCONDITION`,
`CHECK_DEADLOCK`; temporal properties with `WF`/`SF` fairness; the standard modules (Naturals,
Integers, Sequences, FiniteSets, Bags, TLC, TLCExt, Randomization, Json, ...) and the
CommunityModules. Support and limitations for individual operators, including native counterparts
of TLC's Java operators, are listed in [docs/features.md](docs/features.md).

Known limitations ([docs/compat.md](docs/compat.md) section 5): real numbers and temporal
quantifiers (`\EE`, `\AA`) are not supported (as in TLC); PlusCal is not translated (check the
generated TLA+); some TLC options (`-continue`, `-difftrace`, `-fp`, ...) are not implemented;
liveness checking needs memory for the behavior graph; `-coverage` reports per action only.

## Performance

[docs/performance.md](docs/performance.md) is the shipped performance report. It gives median
TLC/tlx wall-time ratios and ranges by model cohort, machine, mode and worker count, with the
record identities and measurement conditions. Results vary by workload; some reported ratios
are below 1, meaning tlx was slower than TLC.

The current configurations, measurement records and report policy are tracked in
[bench/](bench/README.md), so a fresh clone can reproduce the report and inspect its evidence.
Raw run histories, superseded data and backup snapshots are archived outside the published tree. The
[open issues](docs/issues.md) document exclusions and unfinished work;
[docs/benchmarking.md](docs/benchmarking.md) owns the protocol and tooling.

## How it works

```
 .tla ─► tree-sitter-tlaplus ─► surface AST ─► semantic analysis ─► HIR      (tlx-front, tlx-sema)
 .cfg ─► cfg parser (tlx-front) ───► constant binding & model ◄──────┘       (tlx-value, tlx-eval)
                                                ▼
        state reduction: certified symmetry / -optimize VIEW ─► Lean proof   (tlx-sema, tlx-eval; safety, non -tlc)
                                                │
              ┌─────────────────────────────────┴──────────────────────────┐
              ▼                                                            ▼
   interpreter (tlx-eval), -interp                     compiled tier (default): pre-run infers value shapes
   reference semantics over Value (tlx-value)          ─► fixed-size layout ─► typed IR (tlx-layout, tlx-compile)
              │                                        ─► closure executor │ Cranelift JIT │ C + dlopen (tlx-native)
              │                                        ─► mixed-mode host regions & per-(state, action) fallback
              └─────────────────────────────────┬──────────────────────────┘
                                                ▼
          tlx-runtime: BFS / parallel workers / fingerprint set / traces / checkpoints / simulation
                       liveness (tlx-live) ─► POSTCONDITION, ALIAS & TLC-style report (tlx-cli)
```

- The front end uses [tree-sitter-tlaplus](https://github.com/tlaplus-community/tree-sitter-tlaplus);
  a semantic layer re-implements SANY's name resolution, scoping and level checking.
- Before safety exploration (unless `-tlc` is given), semantic state reduction (`tlx-sema`,
  `tlx-eval`) applies certified automatic symmetry in default mode and certified `-optimize`
  projections via `VIEW`, writing standalone Lean certificates while keeping concrete transitions
  for counterexample reconstruction ([State reduction and Lean certificates](#state-reduction-and-lean-certificates)).
- The interpreter (`-interp`) is the reference implementation of TLC's semantics.
- The compiled tier is the default (`-compile` selects it explicitly): a short interpreted pre-run
  infers variable shapes; the spec is lowered to a typed IR over fixed-size encoded states,
  optimized and checked by a compile-time IR verifier. A layout miss widens the layout and resumes
  or restarts the search; anything that cannot be lowered runs in the interpreter.
- Three executors share one IR and one ABI: a closure executor, a Cranelift JIT, and generated C built by
  `cc` in the background and loaded with `dlopen`. The generated library can replace JIT code
  during the search and is cached for later runs.
- In *mixed mode*, a subtree that C cannot express becomes a host region evaluated by the closure
  executor, so one unsupported expression does not force the whole action back to the interpreter.
- The search runtime is generic over a `Model` trait, so the interpreter and the compiled model
  share the same parallel BFS, counterexample reconstruction and liveness checker.

Details: [docs/design.md](docs/design.md) (executor tiering in section 6.6),
[docs/optimization.md](docs/optimization.md), [docs/reductions.md](docs/reductions.md),
[docs/mixed-mode.md](docs/mixed-mode.md), [docs/scale.md](docs/scale.md) (memory and disk).

## Project status

Version 0.1.1 ([Cargo.toml](Cargo.toml)). Results are tested against TLC on the `tests/specs`
suite (small specs, each targeting one semantic point) and on the tlaplus/Examples corpus (see
[Testing](#testing)). Expect rough edges: some error messages are worded differently from TLC's
and some TLC options are missing.

## Testing

```sh
cargo test --profile test-release -q --no-fail-fast  # unit and integration tests
scripts/fetch-deps.sh                                # test dependencies: Examples corpus, TLC jar, modules
python3 scripts/spectest.py --extra=-compile         # tests/specs against TLC results, compiled tier
python3 scripts/spectest.py                          # the same in the interpreter (-interp)
```

The Rust tests need no Java. `spectest.py` compares against the TLC output shipped in
`tests/specs/tlc`; refreshing that output or validating an uncached, differing counterexample
needs Java 21 and the TLC jar. Without Java, a trace that needs validation is reported as
unvalidated. The parity tests select `-tlc` and default to `-interp`; `--extra=-compile` selects
the compiled tier. `TLX_PARANOID=1` checks compiled execution against the interpreter.

The broader tlaplus/Examples differential tests also need a generated TLC oracle; fetching the
models alone does not provide it. [docs/testing.md](docs/testing.md) owns the test tiers and
corpus-oracle setup. Known differences are documented in [docs/compat.md](docs/compat.md) and
tracked in [tests/expected_failures.json](tests/expected_failures.json).

## Contributing

Contributions are welcome; see [CONTRIBUTING.md](CONTRIBUTING.md). In short: keep
`cargo fmt --all` and `cargo clippy --workspace --release --all-targets` clean, and run the tests
above. Changes must not alter results (tiers 1 and 2) or performance without saying so.

## License

[MIT](LICENSE).

## Acknowledgments

- TLA+ and TLC by Leslie Lamport and the [tlaplus](https://github.com/tlaplus) project: the
  language, the reference model checker that tlx is compared against, and the
  [tlaplus/Examples](https://github.com/tlaplus/Examples) corpus used for testing.
- [tree-sitter-tlaplus](https://github.com/tlaplus-community/tree-sitter-tlaplus) for the grammar.
- [TLA+ CommunityModules](https://github.com/tlaplus/CommunityModules): vendored under
  `crates/tlx-sema/modules/community`; the standard modules are under `crates/tlx-sema/modules/stdlib`.
- The Apalache modules (`Apalache.tla`, `Variants.tla`, `Option.tla`), used in tests.
- [Cranelift](https://cranelift.dev/) for the JIT backend.
- [Lean 4](https://lean-lang.org/) for verifying generated state-reduction certificates.

## Security

See [SECURITY.md](SECURITY.md) for private vulnerability reporting and guidance on running untrusted models.
