# tlx configuration reference

This document is the single source for command-line options and environment variables; other
documents link here. Configuration comes in three kinds:

- **Command-line options**: for users. Options with the same name as TLC's keep TLC's semantics (so
  tlx can replace TLC and `scripts/difftest.py` can run both with the same arguments); tlx-only
  options are marked. `tlx check -h` prints the same list.
- **Environment variables `TLX_*`**: except for `TLX_PATH` / `TLX_CLASSPATH` / `TLX_CACHE` / `TLX_CACHE_MB` (and a few
  memory and disk variables that mirror options) they are development and debugging switches and are
  not guaranteed to be stable. All variables are declared once, in the `KNOBS` table of
  `crates/tlx-base/src/knobs.rs` (name, type, default, description, audience, the crate that reads it).
  Parsing and the environment section of `-h` are generated from that table, and
  `crates/tlx-cli/tests/config.rs` checks this document against it: the variables listed in the
  table below must be exactly the ones declared in `KNOBS` (internal ones excepted), and every
  `"TLX_..."` literal in the sources must be declared. To add a variable, change `KNOBS` and the
  table below. Crates read values through the typed accessors of `tlx_base::knobs::Env`, validated
  once at process start by the front end; an invalid value makes `tlx` report an error and exit with
  code 2 before the check starts (for example `tlx: invalid value of TLX_PRERUN_MS: "1s" (expected a number of milliseconds)`).
- **Script options**: the arguments of `scripts/*.py`; each script's module docstring (`--help`)
  describes them in full.

Boolean environment variables: unset, the empty string, `0`, `false`, `no` and `off` mean off, any
other value means on (for variables that default to on: unset means on, and the values above turn
them off). `TLX_JIT_VERIFY`, `TLX_JIT_DISASM` and `TLX_CC_SANITIZE` used to look only at whether the
variable was set, so `=0` also turned them on; they now behave like the other boolean variables.

## Command-line options (`tlx check Spec.tla [options]`)

`tlx parse Spec.tla` checks only front-end syntax, without resolving imports, reading a
configuration or exploring states. It exits with 0 on success, 1 for syntax errors, and 2
for argument or file errors. Documentation checks use this command for complete TLA+ modules.

| Option | Default | Effect | Relation to TLC | Audience |
|---|---|---|---|---|
| `-optimize` | off | Apply only state reductions with connected generated Lean certificates: supported unobserved-variable, relative-age, finite-history, phase-field, sequence-length and scalar/fixed-nested ordered allocation with supported immutable-version collection. Unsupported candidates retain the original graph; see [proof coverage](optimization.md#proof-coverage). Safety invariants and deadlocks only; constraints, action/initial properties, aliases, temporal checking and declared VIEW/SYMMETRY exclude projection. Pure, non-recursive, arity-preserving `.cfg` definition overrides (including builtin definitions and parameterized operator constants) are applied by the certified lowering and recorded in the certificate's `certificate_with_overrides` theorem; value (`Def = value`), module-scoped, cyclic, impure, doubly-bound and arity-changing overrides are refused. Certified unobserved-variable erasure can compose with automatic keyed symmetry (including disjoint products of keyed groups); other combinations stay uncomposed. Concrete values remain in traces. Accepted allocation and relative-age reductions may eliminate eventual overflow under [mathematical integer semantics](compat.md#0-the-three-tiers); runtime arithmetic remains checked. Excludes simulation, symmetry diagnostics, coverage and checkpoint/recovery. Always writes standalone `Optimization.lean` under `-proofdir` (default `$TLX_CACHE/proofs` or `~/.cache/tlx/proofs`, content-addressed by `<hash>/Optimization.lean`), including a no-pass record when no certified rule applies. Prints its path and never invokes Lean. Identical certificates reuse their slot and distinct outputs are never overwritten; write failure exits with 2 before exploration. Lowering and runtime remain trusted; see [Lean coverage](optimization.md#lean-output-for-checking). | Disabled by `-tlc`, regardless of argument order | User |
| `-checksymmetry` | off | tlx only: bounded diagnostic of the declared `SYMMETRY`, on one interpreter worker: init membership, successor sets, each invariant, VIEW equivariance and each state/action constraint, under generator permutations; no ordinary model checking. Exit 0 = no violation within bounds, 1 = witness, 2 = incomplete or error. Incompatible with simulation, recovery and dumps; details in [usage.md](usage.md) section 6.1 | tlx only | User |
| `-suggest` | off | With `-checksymmetry`: check every set of model values the cfg binds to a constant, proving tlx's symmetry analysis statically and bounded-checking the proven group (a witness is an internal error, exit 101) or all permutations of a set it does not prove, then print a `SYMMETRY` definition to paste ([usage.md](usage.md) section 6.2). Requires `-checksymmetry` | tlx only | User |
| `-symmetrystates N` | 1000 | Maximum stored/checked BFS states in symmetry checking; positive. Initial enumeration stops when an additional distinct initial state is found | tlx only | User |
| `-symmetrydepth D` | 10 | Maximum transitions from Init to a checked BFS state (initial depth 0). At the boundary, still checks that state's outgoing edges and their state predicates, but does not enqueue successors | tlx only | User |
| `-symmetryperms N` | 100 | Maximum selected generators, or enumerated elements for an arbitrary declaration; positive. Exceeding it makes the check incomplete. Recognized `Permutations(S)` and unions use adjacent transpositions without constructing the group; other finite sets are evaluated and enumerated up to this limit, without group closure | tlx only | User |
| `-symmetryedges N` | 10000 | Maximum generated successors of each original/permuted state; positive. Exceeding it stops with an incomplete result, never compares truncated successor sets | tlx only | User |
| `-config FILE` | `Spec.cfg` | Configuration file; a relative path that does not exist is taken relative to the spec directory; without `.cfg`/`.tla`, `.cfg` is added if needed; of a `.tla` file its `---- CONFIG Name ----` section is read | as TLC | User |
| `-workers N\|auto` | 1 | Number of worker threads; `auto` = the number of logical CPUs available to the process (`available_parallelism`: on Linux it honors CPU affinity and cgroup quotas). Parallel BFS semantics, what stays nondeterministic with several workers and the measured scaling: [usage.md](usage.md) section 6 | as TLC | User |
| `-deadlock` | check deadlock | **Disables** deadlock checking (overrides the cfg's `CHECK_DEADLOCK`) | as TLC | User |
| `-simulate [num=N]` | unbounded | Random simulation instead of exhaustive search; the argument is a comma-separated list of `key=value`, tlx supports only `num` (number of behaviors, multiplied by the worker count as in TLC); `file=` is an error | as TLC (no `file=`, `stats=`) | User |
| `-generate [num=N]` | unbounded | Simulation that also makes random choices inside actions | as TLC | User |
| `-depth N` | 100 | Maximum behavior length in simulation; `-1` unbounded | as TLC | User |
| `-seed N` | simulation: random; otherwise 0 | Random seed: for the behavior choices of simulation and for the values of `RandomElement` / Randomization (also without `-simulate`) | as TLC (TLC always picks a random seed when none is given; simulated behaviors differ from TLC's, compat.md D-2, D-4) | User |
| `-dump [dot[,actionlabels][,colorize]] FILE` | none | Write the reachable states to `FILE.dump`, or the state graph to `FILE.dot` | as TLC (no `constrained`) | User |
| `-dumpTrace json\|tla FILE` | none | On a violation (invariant, action property, deadlock or temporal property) write the counterexample (TLC's `CounterExample`; a lasso for temporal properties) to `FILE`; repeatable; byte-for-byte TLC's format. The lowercase alias `-dumptrace` is accepted; formats and file contents in [usage.md](usage.md) section 9.2 | the `json` and `tla` formats of TLC; the `tlc`/`tlcplain`/`dot` formats are not supported | User |
| `-coverage N` | off | Every N minutes (`0` = with every progress report) and at the end, print TLC's action-level coverage statistics `<name location>: distinct:generated` (Init as `generated:evaluated`); no cost when off ([usage.md](usage.md) section 9.3) | as TLC's action-level lines (no sub-expression, variable, invariant, constraint or property lines; compat.md D-12); has no effect under `-simulate` | User |
| `-fpmem X` | not given: starts at 8 MiB and grows within the `-maxmem` budget | Fingerprint set memory: `0 < X < 1` is a fraction of physical memory (TLC semantics; TLC's default is 0.25), an integer `X >= 1` is MiB (tlx extension). When given the table has this fixed size and never grows or spills; when full the run is a capacity error. TLC's "NMB fingerprint memory" start-up line prints the limit; without it the table grows in place and, over budget, spills ([scale.md](scale.md) sections 2.1 and 4.1) | TLC only has the fraction, default 0.25 | User |
| `-maxmem X` | 0.5 (half of physical memory) | Soft limit for all of tlx's memory: `0 < X < 1` is a fraction of physical memory; otherwise MiB, or a `K`/`M`/`G`/`T` suffix (1024-based); at least 1 MiB. Default: half of physical memory (on Linux the process's cgroup limit when lower; not the memory free at start-up). Counted components, the pressure stages they spill in and the liveness limit: [scale.md](scale.md) section 2 | tlx only (TLC is limited by the JVM's `-Xmx` and `-fpmem` separately) | User |
| `-fpbits N` | 0 | TLC-compatible (MultiFPSet): divide the fingerprint set into 2^N contiguous shards by the high bits (`0 <= N <= 30`), which only decides the granularity of work sharing during growth and does not affect results ([scale.md](scale.md) section 4.1) | TLC-compatible (MultiFPSet) | User |
| `-maxSetSize N` | 1000000 | The most elements a set that tlx *materializes* may have (`N >= 1`; TLC's `setBound`). A `[S -> T]`, `S \X T`, a record set, a set former, a set filter over an enumerable set, and a union or difference of those — and a quantifier bound over one — with more elements is an error, "Attempted to construct a set with too many elements (>N)." (exit 75), as in TLC. TLC's `ValueVec` starts with ten slots and checks the bound only when it grows, so a set built by appending may hold up to `max(10, N)` elements (`N < 10` binds from the eleventh); a set former appends once per iteration of its domain, a set filter once per kept element, and a set literal or an interval — both preallocated to their exact size in TLC — is never limited. Sets that are enumerated element by element are not limited either: `x' \in S`, `x \in S`, a `SUBSET S` or `kSubset(k, S)` bound, printing, `\subseteq`, `Cardinality` (which reports its int overflow instead) and `RandomSubset`/`RandomElement`. Part of a checkpoint's identity (`-recover`) ([compat.md](compat.md) section 5) | as TLC (same option, default, error and initial ten slots) | User |
| `-tool` | off | Wrap output in the message delimiters of TLC's `-tool` | as TLC | User / tools |
| `-nowarning` | off | Do not print warnings | as TLC | User |
| `-spill auto\|off\|always` | `auto` | When to use disk: `auto` (default) spills archive segments, full trace/edge-log blocks, queue segments and fingerprint runs only when `-maxmem` is exceeded; `off` never writes (over budget the archive is dropped and a full fingerprint set is a capacity error); `always` (testing) uses the disk paths from the start, so counterexamples, the liveness graph and the archive are read back from disk. Results are identical with and without disk; `TLX_SPILL` is a synonym (the command line wins) ([scale.md](scale.md) sections 10 and 4.2) | tlx only | User |
| `-maxdisk X` | unlimited | The most disk the spill files may use: MiB, or a `K`/`M`/`G`/`T` suffix; min(1 GiB, 2%) of the file system is always kept free. Exceeding it, a full disk or a checksum mismatch on read-back stops the search with `The search stopped: ...` and exit 255. `TLX_MAXDISK` is a synonym ([scale.md](scale.md) section 10). Default: unlimited | tlx only | User |
| `-checkpoint MIN` | 30 | Every MIN minutes (integer; `0` = never) write a checkpoint at a level boundary into the metadir: fingerprint set, queue, trace/edge logs, counters, TLCSet registers, archive and `Dyn` interner, committed atomically (`fsync` + rename) and keeping only the newest. Deleted when the run ends normally, kept after SIGKILL or SIGINT/SIGTERM for `-recover`; prints TLC's "Checkpointing of run DIR" lines ([scale.md](scale.md) sections 9.1-9.2). Default: 30 minutes | as TLC (same default and unit; tlx works at level boundaries while TLC pauses its workers immediately; TLC's checkpoint does not contain the generated count, so the counts after recovery are approximate, tlx's are exact) | User |
| `-recover DIR` | none | Continue from the checkpoint in metadir `DIR` (or its `checkpoint/`), which becomes this run's metadir: verdict, generated/distinct counts, depth and counterexample length equal those of an uninterrupted run (`-workers` may differ). It must be the same binary, spec, cfg, tier, mode, deadlock setting, `-seed` and undeclared symmetry, otherwise tlx refuses and says which one differs (exit 255); the pre-run is skipped, and a later layout miss still widens and resumes. Incompatible with `-simulate`/`-generate`/`-dump` ([scale.md](scale.md) section 9.3) | as TLC (TLC also takes a metadir and continues in it) | User |
| `-cleanup` | none | Accepted, no effect (the spill directory is already deleted at the end of the run) | TLC compatibility | User |
| `-noGenerateSpecTE` | none | Accepted, no effect (tlx does not generate trace-exploration specs) | TLC compatibility | User |
| `-metadir DIR` | `<spec directory>/states/<yy-MM-dd-HH-mm-ss>` | Directory of the spill files and of the checkpoint (`checkpoint/`), guarded by a `LOCK`; created lazily on the first spill or checkpoint and removed when the run ends (for a given existing directory only tlx's own files). On SIGINT/SIGTERM it is removed unless it holds a committed checkpoint; SIGKILL leaves it behind, recoverable with `-recover`. `TLX_METADIR` is a synonym ([scale.md](scale.md) section 10) | same name; TLC's default is the same | User |
| `-proofdir DIR` | `$TLX_CACHE/proofs` or `~/.cache/tlx/proofs` | Directory for generated Lean certificates (`<hash>/Optimization.lean`); identical certificates reuse their slot and distinct outputs are never overwritten. When neither `-proofdir`, `TLX_PROOF_DIR` nor `TLX_CACHE` is set and `~/.cache/tlx/proofs` is unwritable, falls back to a private per-user directory (`$TMPDIR/tlx-proofs-<uid>` with mode `0700` on Unix, or `$TMPDIR/tlx-proofs` elsewhere). Explicit destinations fail closed (exit 2) before exploration if unwritable. `TLX_PROOF_DIR` is a synonym (the command line wins) | tlx only | User |
| `-I DIR` | none | Module search directory, repeatable; searched after the spec directory and before the built-in standard modules and CommunityModules ([usage.md](usage.md) section 11) | tlx only (TLC uses Java `-DTLA-Library`) | User |
| `-progress` | once a minute | Report progress every 10 seconds | tlx only | User |
| `-compile` | on (the default tier) | Compiled execution tier: a short interpreted pre-run infers the state layout, then encoded states and native code (an in-process Cranelift JIT first; after the search has run for 1.5 s a C library built by `cc -O2` in the background replaces it and is cached, see `TLX_CACHE`); results equal the interpreter's. It is the default: without a tier option tlx uses it, except when there can be no native code at all (no JIT in the build or `TLX_JIT=0`, and no C compiler, see `CC`): then the default is the interpreter and one line `compile: no JIT and no C compiler (...): checking with the interpreter` says so (`-compile` still runs the compiled tier, on the IR). The last of `-compile` and `-interp` wins | tlx only | User |
| `-interp` | off | Interpreter: evaluate on dynamic values (tlx's semantic reference) instead of the compiled tier; no pre-run, no compilation, no native-code cache | tlx only | User |
| `-noautosymmetry` | off | Disable automatic symmetry application. By default, a disjoint product of full groups (two to seven model values each, total order at most 5,040) can reduce safety runs when a connected certificate is generated by the keyed emitter (`KeyedCertificate`: fixed/mixed maps, scalar/optional key slots, sets of keys, sets of single-key tagged records, and fixed records of those shapes), the generic equivariant fallback (`EquivSymCertificate`: key-valued and nested finite maps, multi-key records, bounded sequences/tuples, set comprehensions, `KSubset`, fixed-atom stratified `k`-subset constants, zero-arity `Def = value` literal assignments, `IsInjective`), or the choice-irrelevant fallback (`ChooseSymCertificate`: unique-witness `CHOOSE`, projected uniform/constant-value `CHOOSE`, and commutative-associative recursive `CHOOSE` integer set-sum folds). Always emits standalone Lean before exploration, without invoking Lean; proof-output failure exits 2. Uncertified shapes and partial/overflowing operations stay unreduced. A declared `VIEW` that is a (possibly nested) tuple of distinct state variables composes with the certified group (plain certificate when it retains every variable, certified erasure+symmetry when it omits certified-erasable variables), including zero-arity variable-group definitions such as `View == <<serverVars, logVars>>`; computed or guard-live views keep their declared search and report the refusal under `-stats`. See [certified automatic symmetry](optimization.md#certified-keyed-symmetry). A declared `.cfg` `SYMMETRY` is used verbatim under this flag; without it the default mode may enlarge a factorized declaration by disjoint proven groups when one connected certificate covers the combined product ([usage.md](usage.md) section 6.3). Separately enabled state projections retain their own behavior. | tlx only | User |
| `-tlc` | off | TLC-compatible results: verdicts, violated names, state counts, depth and shortest-trace length as TLC's ([compat.md](compat.md) section 0). Without it the default mode may use optimizations TLC does not have, which keep the verdicts sound (a violation is reported exactly when one exists, with a genuine counterexample) but may change counts, depth or the counterexample: currently certified automatic symmetry (`KeyedCertificate`, `EquivSymCertificate`, `ChooseSymCertificate`, including certified enlargements of a declared `SYMMETRY` and certified declared tuple `VIEW`s) and explicitly enabled certified projections ([usage.md](usage.md) section 6.3). A declared `.cfg` `SYMMETRY` is used verbatim under `-tlc`. The parity tests (spectest, difftest, tlcsuite and the matrix and fuzz drivers) run with `-tlc`. Part of a checkpoint's identity (`-recover`) | tlx only | User |
| `-stats [json[=FILE]]` | off | On exit (including best-effort partial reports on SIGINT/SIGTERM) report where time and work went: phases (front end, pre-run, lowering and C generation/build/load, search, liveness, restart/resume), search work (expanded states, generated successors, fingerprint set inserts and probes, encode/decode/fingerprint), worker utilization (busy / waiting for work / level barrier), per action / invariant / action property the native / IR / interpreter / fallback call counts and estimated time, in the compiled tier every evaluated host region (time, evaluations, failures, the state variables it reads) and the region evaluations per state variable read, the final layout slot by slot (shape, words and how it was chosen: rejected encodings and why a slot is `Dyn`, type-invariant bounds, misses and widenings, fallbacks), the states expanded again after layout restarts and resumes, and memory by component (fingerprint set reserved and actually touched, frontier, trace log, state retained for resuming, liveness behavior graph, `Dyn` interner tables and the value heap they retain, peak RSS). Text goes to stderr; each JSON report is one object, written to stderr or FILE (see interruption semantics below). When absent nothing is collected and the output is unchanged | tlx only | Developer |
| `-h`, `-help`, `--help` | none | Print help | `-h` in TLC | User |

Other TLC options (`-continue`, `-dfid`, `-difftrace`, `-fp`, `-view`, `-terse`,
`-userFile`, `-postCondition`, `-inv`, `-debugger`, ...) are not implemented in tlx and are reported as
unknown options (`tlx: unknown option ...`, exit code 2); see [features.md](features.md) section 1.

Argument errors (a missing or invalid value, an unknown option, several specs) print the reason and
the usage line and exit with 2.

### Statistics on interruption and adaptive tiering

With `-stats`, SIGINT/SIGTERM writes a best-effort report before spill cleanup and
exit status `128 + signal`. JSON adds `interrupted: true` (`false` on normal
completion); text labels the report partial. Active worker counters are snapshots
of completed search units: the first unit and then at most every 250 ms, checked
every 256 units. JSON reads host-region atomic counters on demand; immutable region
metadata is prepared once, and retiring layouts freeze their final rows. In-flight
host calls are excluded until their counters are drained. Long-running units/calls
can leave older snapshots; unfinished phases and end-of-search-only metrics can
be absent. These are diagnostic prefixes,
not completed measurements. SIGKILL cannot produce a report. A signal claimed before
normal exit commits owns reporting, cleanup and exit. If normal stderr reporting
has already started, an additional interrupted report follows it when output can
complete; the last complete report is authoritative. File output is replaced by
the interrupted report. Shutdown allows one second for report generation, writer
contention and output, then proceeds to spill cleanup even if reporting is blocked.
A blocked or slow destination can therefore receive a truncated report or none.
Checkpoint-preservation notices have a separate one-second output allowance after
cleanup. Failed writes (including full destinations and closed stderr pipes) do
not prevent cleanup or the signal exit status. Normal stats writers block SIGPIPE
on their exiting threads. A claimed signal shutdown ignores SIGPIPE process-wide,
also protecting platforms that deliver a failed pipe write's signal to the process.

When adaptive mixed tiering is active, `adaptive_tiers_*` JSON fields contain one
observation per model/layout identity, worker, library slot, function kind
and index. The `library` field identifies the write-once `quick` or `optimized` slot
(the slot can contain JIT or C code). Each row includes `name`, `phase` (`warming`, `sampling`, `running`),
`chosen` (`undecided`, `mixed_native`, `fallback`), cumulative `sample_calls` and
`sample_ns` for both paths, decision counts in `decisions`, and the last completed
sampling phase's `last_trimmed_mean_ns` (null before a decision). Sample totals use
unclipped measured nanoseconds; the decision means use the tierer's existing clipped,
trimmed samples. Library replacement starts a new row; earlier observations remain.
Revisiting an installed model reuses its row and accumulates samples and decisions,
while the tierer's existing reset behavior is preserved. `chosen` and the means
retain the last completed decision across revisits, even while the tierer warms
or samples again. Workers may choose different paths. The phase is the
latest published observation, not a synchronized view of all threads. Text reports
include the same identities, choices, sample totals and decision counts. No adaptive
rows are produced for functions that never enter adaptive tiering or when it is disabled.
The dynamic coverage census preserves rows under `dynamic.adaptive_tiers` and keeps
interrupted shares separate from complete measurements.

## Optimization command

`tlx optimize Spec.tla -output DIR [-config FILE] [-I DIR]...` generates a finite
mathematical abstraction using the rule-based verification optimizer. It is separate from
`tlx check`; generation is not a safety verdict. The supported fragment, pass extension
interface, artifacts and trust boundary are described in [optimization.md](optimization.md).

| Option | Meaning |
|---|---|
| `-output DIR` | Required new destination; existing paths are never overwritten. Emits `Optimized.tla`, `Optimized.cfg`, `Optimization.lean` and `optimization.txt`. Every committed pass has a connected certificate. Lean is not invoked; verification is a separate explicit action. |
| `-config FILE` | Configuration file, defaulting to the specification path with `.cfg` extension. An explicit path is resolved against the working directory; embedded `.tla` configuration sections are not supported by this command. |
| `-I DIR` | Additional module search directory, repeatable. The normal `TLX_PATH` and `TLX_CLASSPATH` search paths also apply. |
| `-h`, `--help` | Print optimization-command help. |

The input configuration must explicitly name INIT, NEXT and at least one INVARIANT, and
set CHECK_DEADLOCK FALSE. Unsupported constructs or options return exit 2 without a safety
claim. Successful generation returns exit 0, which means only that artifacts were emitted.
I/O failures also return exit 2 and can leave an incomplete destination.

For example, after generation, `tlx check DIR/Optimized.tla -interp` checks the generated model.
Its verdict, counts and trace describe that model. The command does not automatically transfer
results or validate a concrete trace for the original specification.

## Environment variables

| Name | Type | Default | Effect | Audience | Read in |
|---|---|---|---|---|---|
| `TLX_PATH` | path list (separator as `PATH`) | empty | More module search directories, after `-I` | User | `tlx-cli/src/settings.rs` |
| `TLX_CLASSPATH` | path list (separator as `PATH`) | empty | More module search directories, after all built-in modules (standard modules and CommunityModules); corresponds to TLC's Java classpath | User | `tlx-cli/src/settings.rs` |
| `CC` | program | `cc` | The C compiler of the compiled tier (a path, or a program looked up in `PATH`). When it cannot be found no C build is attempted: the JIT code stays, or without a JIT the default tier is the interpreter. A failing compilation is reported in one line (the compiler's first error line) ([usage.md](usage.md) sections 5.3-5.4) | User | `tlx-native/src/build.rs` |
| `TLX_CACHE` | directory | `~/.cache/tlx` | Directory of the compiled tier's cache: one *slot* per hash of the C source, compiler and flags, holding the library, its C source and `tlx_abi.h`; it can be deleted at any time, is safe to share between processes, and its size is bounded by `TLX_CACHE_MB`. The background build is done by a separate `sh` child holding the slot's `build.lock`; a build still running when tlx exits lands in the cache ([usage.md](usage.md) section 5.3, [design.md](design.md) section 6.7) | User | `tlx-native/src/build.rs` |
| `TLX_CACHE_MB` | integer (MiB) | 1024 | Size limit of the native-code cache (`TLX_CACHE`): above it the least recently used slots are removed, never the one being built or those used in the last 10 minutes; `0` = no limit ([usage.md](usage.md) section 5.3) | User | `tlx-native/src/build.rs` |
| `TLX_PARANOID` | boolean | off | Compiled tier: every compiled result is cross-checked against the interpreter and the first mismatch fails (implies `TLX_NATIVE_SYNC`) | Developer | `tlx-compile/src/settings.rs` |
| `TLX_NO_NATIVE` | boolean | off | Compiled tier: do not generate C, only run the lowered IR | Developer | same |
| `TLX_NATIVE_SYNC` | boolean | off | Compiled tier: build the native code synchronously before exploring (by default it is built in the background) | Developer | same |
| `TLX_NO_MATERIALIZE` | boolean | off | Compiled tier: do not materialize state-level definitions | Developer | same |
| `TLX_ESCAPE` | boolean | off | Compiled tier experiment: keep the first inline layout stable, escape outliers to a side store and deoptimize only the current action. Background compilation publishes at most two widened execution layouts followed by an all-Dyn layout; queued states are never re-encoded. Turns the value store off for the run (logged): the escape slots replace the layout its slots would sit in. Explicit checkpoint/recovery disables the experiment; the default checkpoint interval is disabled instead. Actions with irreversible effects stay interpreted because the effects journal has no action transaction; Print/PrintT use the existing transactional output buffer. No reclamation in the experimental side store (4 GiB limit). | Developer | `tlx-compile/src/settings.rs` |
| `TLX_VALUE_STORE` | `0`\|`off`\|`1`\|`on`\|`all` | `0` | Compiled tier, experimental: with `1` (or `on`), the slots whose shape would be `Dyn` (values of unbounded or unordered shape, e.g. message bags keyed by records with sequence fields) hold handles into a value store owned by the run instead of the process-wide `Dyn` interner; `all` (testing) does so for every slot; `0` and `off` disable it (ASCII case-insensitive). The store keeps every finite value with its exact representation (including how a function was built: compat.md D-13 does not apply to these slots) and a semantic digest that fingerprints use; `DOMAIN`, application, `\in` and `\in DOMAIN`, EXCEPT, `:>`, `@@`, `=`, field access, record and tuple construction, `Cardinality`, `Len`/`Append`/`Head`/`Tail` and iteration over such values run natively in the closure executor, the JIT and C (ABI v5 `ref_op`/`ref_elems` callbacks), everything else through the existing host regions. The store has no reclamation yet: it is limited to the run's `-maxmem` (never a fraction of it, so a run that fits its budget is not ended earlier) and exceeding that ends the run with an error naming this switch. Default 30-minute checkpoints and explicit `-checkpoint` / `-recover` persist the store in `model-store` and validate the store mode on recovery (mismatched `TLX_VALUE_STORE` modes or `TLX_ESCAPE=1` are refused). `TLX_ESCAPE` turns the store off for fresh runs (logged). Results do not change ([value-store.md](value-store.md)) | Developer | `tlx-compile/src/settings.rs` |
| `TLX_MIXED` | boolean | on | Compiled tier: mixed-mode native code ([mixed-mode.md](mixed-mode.md)): sub-expressions that C cannot compile become host regions evaluated by the IR executor, instead of the whole action / predicate falling back; impure functions (containing `Print`, `Random*`, ...) are not mixed, with one exception: output (`Print`/`PrintT`) in an action is mixed (the host holds the lines its regions print and drops them if the interpreter redoes the run), see [mixed-mode.md](mixed-mode.md) sections 4 and 5. On by default (with adaptive tiering and region memoization no model was measured slower); `0` turns it off and returns to whole-function fallback | Developer | same |
| `TLX_MIXED_FORCE` | integer k | 0 | Compiled tier, for testing: also turn every k-th expression that C could compile into a host region, to exercise the region ABI on specs that are fully native; implies `TLX_MIXED`; 0 = no forcing; adaptive tiering is off then (mixed functions always run natively) ([mixed-mode.md](mixed-mode.md) section 7) | Developer | same |
| `TLX_MIXED_ADAPT` | boolean | on | With `TLX_MIXED`: adaptive tiering ([mixed-mode.md](mixed-mode.md) section 7): each worker alternately samples and times, for every mixed function, the "mixed native" and the "fallback" (IR executor or interpreter) path and picks the faster one (native must be more than 5% faster), re-sampling periodically; results do not change. `0` = mixed functions always run natively | Developer | same |
| `TLX_PRERUN` | integer (states) | 20000 | Compiled tier: state budget of the shape pre-run | Developer | same |
| `TLX_PRERUN_MS` | integer (milliseconds) | 1000 | Compiled tier: time budget of the shape pre-run | Developer | same |
| `TLX_PRERUN_SETTLE` | integer (states) | 2000 | Compiled tier: stop the pre-run BFS once the layout has settled, that is, after the last state that did not fit the then-chosen layout (`n` states observed before it) a further `max(this value, 2n)` states were observed and all fit, or 1/4 of this value of states were observed, with CPU-time floors (at least 50 ms, and twice the CPU time before that state); `0` = stop only on the state/time budget ([design.md](design.md) section 6.5.1) | Developer | same |
| `TLX_PRERUN_REUSE` | boolean | on | Compiled tier: when the faithful pre-run (a single-worker interpreter search if the search may create strings) ends within its budget (the state space is exhausted, or it stops at a violation/deadlock/error), its result is the result of the run and nothing is compiled or searched again; only under the conditions listed in [design.md](design.md) section 6.5.1. `0` = off; off under `TLX_PARANOID` | Developer | same |
| `TLX_RETAIN_MB` | integer (MiB) | `-maxmem / 4` (1024 without a budget) | Compiled tier: memory limit for the archive of expanded states kept while a layout miss may still happen, so a restart can resume at the failing level; beyond it encoded archive segments go to disk when spilling is allowed; `0` = keep nothing, always restart from scratch. `-stats` reports the lost archive and the states repeated ([scale.md](scale.md) section 6) | Developer | same |
| `TLX_MAX_RESTARTS` | integer | 16 | Compiled tier: the number of widen-and-restart steps after layout misses; a further miss makes the rest of the run use dynamic values (all variables `Dyn`, definitions not materialized, so no more misses), noted in the log ([design.md](design.md) section 6.5.3) | Developer | same |
| `TLX_COVERAGE` | boolean | off | Compiled tier: print the variable layout, widening records and the histogram of boxed / interpreter IR nodes | Developer | `tlx-base/src/diag.rs` |
| `TLX_CGEN_DEBUG` | boolean | off | Compiled tier: print why a function got no native code | Developer | same |
| `TLX_EQ_DEBUG` | boolean | off | Compiled tier: print the type / shape of boxed equality comparisons | Developer | same |
| `TLX_IR_DUMP` | name | none | Compiled tier: print the IR of the action / predicate of that name (`*`: all) | Developer | same |
| `TLX_IR_DUMP_RAW` | boolean | off | With `TLX_IR_DUMP`: print in `Debug` form | Developer | `tlx-base/src/diag.rs`, `tlx-compile/src/enc/diag.rs` |
| `TLX_MEMO_SLOTS` | integer (slots) | 65536 | Mixed-mode region memo table: the maximum number of slots of each thread's direct-mapped table (rounded to a power of two; a collision replaces the entry; it starts at 1024 and doubles when more than half is used) ([mixed-mode.md](mixed-mode.md) section 8) | Developer | `tlx-compile/src/settings.rs` |
| `TLX_MEMO_MB` | integer (MiB) | 128 | Mixed-mode region memo table: the byte budget of the memo tables of all threads (keys plus estimated result size); each search worker gets 1/N, also limited by the memory budget (at most 1/N of `-maxmem`/8, halved under pressure, at least 1 MiB), and the table is cleared when exceeded. Usage counts against `-maxmem` and appears in `-stats` ([mixed-mode.md](mixed-mode.md) section 8, [scale.md](scale.md) section 2.2) | Developer | same |
| `TLX_MEMO_STATS` | boolean | off | With `-stats`: add a "memo tables" section to the `-stats` report, listing per interpreter node the lookups / hits, the average time of a miss and the estimated time saved (timing has a cost, for analysis only; without `-stats` there is no output) ([mixed-mode.md](mixed-mode.md) section 8) | Developer | same |
| `TLX_JIT` | `tier`\|`1`\|`only`\|`0`\|`off` | `tier` | Compiled tier: tiering of native code ([design.md](design.md) section 6.6). `tier`: compile in-process with Cranelift first (milliseconds, ready before exploration starts), and only after the search has run for `TLX_CC_DELAY_MS` build the C library with `cc -O2` in the background; once loaded it replaces the JIT code; if the C library is already in the cache it is loaded synchronously (a few milliseconds) and the JIT is not used; if `cc` is missing or fails the JIT code stays. `1`/`only`: JIT only, never call `cc`. `0`/`off`: C only (the behavior before the JIT: background build, large sources start with `-O0`). The set of native functions and the host-region calls of JIT and C must be the same, otherwise the JIT is not enabled (log `JIT disabled: ...`) and C is used. Under `TLX_NATIVE_SYNC`/`TLX_PARANOID`, `tier` builds C synchronously (the JIT is used if C fails). Results do not change. Needs the cargo feature `jit` (on by default) | Developer | `tlx-compile/src/settings.rs` |
| `TLX_CC_DELAY_MS` | integer (milliseconds) | 1500 | With `TLX_JIT=tier`: how long to search with JIT code before starting the background C build (short runs do not pay for `cc` nor compete with the search for CPU); 0 = immediately | Developer | same |
| `TLX_CC_AT_EXIT_MS` | number (milliseconds, may be fractional) | 200 | With `TLX_JIT=tier`: when the run ends before `TLX_CC_DELAY_MS`, so the delayed C build never started, and this run's JIT compilation took at least this many milliseconds, start the C build in the background right at the end of the run (without waiting: the build finishes by itself after tlx exits and lands in the cache), so the next run hits the cache and does not JIT again (an attempt after a layout-miss restart counts the whole run so far instead of its own JIT time: its layout had no cached library and the restarts cancelled the delayed builds); 0 = off (it does not start anyway when `cc` is missing, the library is already cached, or under `TLX_JIT=0`, `TLX_NATIVE_SYNC`, `TLX_PARANOID`) | Developer | same |
| `TLX_JIT_OPT` | `none`\|`speed` | `speed` | JIT: Cranelift optimization level | Developer | `tlx-compile/src/jit/mod.rs` |
| `TLX_IR_VERIFY_HARD` | boolean | off | Make typed IR verifier failures hard compiler errors in release builds; also implied by paranoid mode and always hard in debug/unit-test builds. Verification itself is always enabled. Normal release rejects the compilation and uses the interpreter. The parity test drivers (spectest, difftest, tlcsuite) set it for their compiled-tier runs (`tlxlib.parity_env`), so that a verifier rejection, which would otherwise silently run the model in the interpreter, fails the test | Developer | `tlx-compile/src/verify.rs` |
| `TLX_JIT_VERIFY` | boolean | off | JIT: turn on the Cranelift IR verifier (for debugging, compiles slower) | Developer | `tlx-compile/src/jit/mod.rs` |
| `TLX_JIT_DISASM` | boolean | off | JIT: print the machine code of every JIT function to stderr | Developer | `tlx-base/src/diag.rs` |
| `TLX_SYMMETRY_PARANOID` | positive integer | unset (off) | Check a symmetry tlx applies on its own — an automatic group without a `SYMMETRY` declaration ([usage.md](usage.md) section 6.2) or the extra factors added to a declared `SYMMETRY` — at one expanded state in N (1: every state), in both tiers: for every generator p of the applied group, the image p(s) must agree with s on Init membership, invariants and constraints, the images of the successors of s must be the successors of p(s), and action constraints and action properties must agree on each edge. A mismatch is an internal error (exit 101) that prints s, p(s) and the differing edge | Developer | `tlx-eval/src/model/mod.rs` |
| `TLX_AUTOSYM_FORCE` | constant names, comma-separated | none | For testing: mark these candidate sets as symmetric candidates despite static-analysis rejection. Cannot bypass the connected-certificate gate; uncertifiable groups stay unreduced | Test | `tlx-cli/src/autosym.rs` |
| `TLX_STATS_SAMPLE` | positive integer | 8 | `-stats`: time every N-th state expansion (or simulation step) in detail and only count the others; total times are extrapolated proportionally | Developer | `tlx-cli/src/stats.rs` |
| `TLX_MAX_DEPTH` | positive integer | 100000 | Interpreter: the maximum nesting depth of operator / function application; beyond it a TLC-style stack overflow error is reported (TLC's limit is the JVM stack size, and the scripts run it with `-Xss16m`, which is the same order of magnitude) | Developer | `tlx-eval/src/depth.rs` |
| `TLX_BAILOUT_DEBUG` | integer | 0 | Compiled tier: print the first N errors of the IR executor | Developer | `tlx-compile/src/enc/model.rs` |
| `TLX_CC_SANITIZE` | boolean | off | Compiled tier: build the generated C with AddressSanitizer and UndefinedBehaviorSanitizer (`-O1 -g -fsanitize=address,undefined`, part of the build cache key). `tlx` is not instrumented, so the host must preload the runtime (`LD_PRELOAD` on Linux, `DYLD_INSERT_LIBRARIES` on macOS) and set `ASAN_OPTIONS`/`UBSAN_OPTIONS`; [testing.md](testing.md) section 11 has the commands | Developer | `tlx-native/src/build.rs` |
| `TLX_INJECT_MISMATCH` | `drop\|dup\|stale\|init\|inv\|miss[:N]` | none | For testing: deliberately corrupt the N-th (from 0) eligible compiled result, to check that `TLX_PARANOID` detects it; `miss`: report one layout miss after the search ends, to check that the interpreter redoes that phase | Test | `tlx-compile/src/settings.rs` |
| `TLX_QUEUE_COMPRESS_MB` | integer (MiB) | the smaller of 64 and 1/16 of `-maxmem` | For testing: the size at which the queue starts writing compressed blocks (it returns to object blocks below half of it); over the memory budget it compresses regardless of size ([scale.md](scale.md) section 5.1) | Test | `tlx-cli/src/settings.rs` |
| `TLX_MAXMEM` | fraction or size | 0.5 | Same as `-maxmem` (the command line wins); see [scale.md](scale.md) section 2 | User | same |
| `TLX_THP` | `auto\|on\|off` | `auto` | Linux only: whether the process uses transparent huge pages. mimalloc asks for them for its arenas, which costs tens of MiB of extra resident memory (about 15-30 MiB with 1 worker, 25-55 MiB with 8) in exchange for 1-10% speed. `auto`: switched off (`prctl(PR_SET_THP_DISABLE)`) when `-maxmem`/`TLX_MAXMEM` is given and below 512 MiB + 64 MiB x the number of workers, otherwise on; `MIMALLOC_ALLOW_THP` decides instead when set. Results do not change ([scale.md](scale.md) section 2.2) | User | same |
| `MIMALLOC_PURGE_DELAY` | integer (milliseconds) | 100000 | mimalloc's own option: how long freed memory is retained before it is returned to the system (the mimalloc v3 default is 1000). When unset tlx sets it to 100 s, because the interpreter repeatedly frees and re-requests the same memory ([scale.md](scale.md) section 2.2). The memory budget's pressure stages still force a return (`mi_collect(true)` is not subject to the delay); `-1` (never return) also disables that forced return, so it is not the default; not a `KNOBS` entry | User | `tlx-cli/src/process.rs` |
| `TLX_SPILL` | `auto\|off\|always` | `auto` | Same as `-spill` (the command line wins); the regression tests use `TLX_SPILL=always TLX_SEG_BYTES=4096 TLX_FP_SPILL_SLOTS=1024` so that very small models also write to disk and read counterexamples and fingerprints back from it ([scale.md](scale.md) sections 10 and 4.2) | User / Test | `tlx-cli/src/settings.rs` |
| `TLX_METADIR` | directory | see `-metadir` | Same as `-metadir` (the command line wins) | User | same |
| `TLX_PROOF_DIR` | directory | see `-proofdir` | Same as `-proofdir` (the command line wins) | User | `tlx-cli/src/settings.rs` |
| `TLX_MAXDISK` | size | unlimited | Same as `-maxdisk` (the command line wins) | User | same |
| `TLX_CHECKPOINT_SECS` | integer (seconds) | none | For testing: the checkpoint interval is N seconds (instead of the minutes of `-checkpoint`; has no effect with `-checkpoint 0`) ([scale.md](scale.md) section 9.3) | Test | `tlx-cli/src/settings.rs` |
| `TLX_CHECKPOINT_STATES` | integer (states) | none | For testing: take a checkpoint at the next level boundary after every further N distinct states found (in addition to the time interval; has no effect with `-checkpoint 0`) ([scale.md](scale.md) section 9.3) | Test | same |
| `TLX_CHECKPOINT_ABORT` | integer n | none | For testing: end the process right after the n-th checkpoint is committed (`_exit(134)`, no cleanup, as if killed), to test `-recover` ([scale.md](scale.md) section 9.3) | Test | same |
| `TLX_SEG_BYTES` | integer (bytes, >= 64) | 1048576 | For testing: the size of the segments that hold encoded blocks (the unit of the queue, the archive and, with VIEW/SYMMETRY and several workers, the on-disk representative candidates) and of the trace-log and liveness-edge-log blocks (the unit of spilling); use a small value to exercise segment boundaries ([scale.md](scale.md) sections 5 and 10) | Test | same |
| `TLX_FP_TABLE_MIN` | integer (slots, >= 1024) | 1048576 (8 MiB) | For testing: the initial number of slots of the fingerprint table when `-fpmem` is not given; a very small value (such as 1024) makes growth frequent, to check that growth does not change results ([scale.md](scale.md) section 4.1) | Test | `tlx-cli/src/settings.rs` |
| `TLX_FP_SPILL_SLOTS` | integer (slots, >= 1024) | 262144 (2 MiB) | For testing: with `-spill always` the fingerprint table has at most this many slots and spills as a run at the high-water mark (0.75); 1024 spills every 768 new states, so small models also exercise disk lookups and run merging ([scale.md](scale.md) section 4.2) | Test | same |
| `TLX_TLC_XMX` | Java heap size | `4g` | Default maximum heap for every TLC launch; an explicit JVM `-Xmx` option takes precedence | Developer | `scripts/tlxlib.py` |
| `TLX_CLOUD_HOST` | boolean | off | Set by `cloud_verify.py` on the remote host; permits heavy TLC models, concurrent cloud JVMs and cloud benchmark load | Developer | `scripts/tlxlib.py`, `scripts/bench.py` |
| `TLX_JAVA` | program | `/opt/homebrew/opt/openjdk@21/bin/java` | The java the scripts use to run TLC / SANY | Developer | `scripts/tlc.py` |
| `TLX_BENCH_MACHINE` | text | none | Appended to the machine description recorded by `bench.py` (after the architecture, CPU model and core count), for example the cloud instance type and price | Developer | `scripts/bench.py` |
| `TLX_LIVE_CHECK_FIRST` | positive integer (expanded states) | 250000 | First level boundary for periodic recorded-graph liveness checking. Subsequent checks require twice as many expanded states. | Test | `crates/tlx-runtime/src/explore/periodic.rs` |
| `TLX_LIVE_SCALE` | integer (states) | 200000 | Number of states of the `tlx-live` scale test | Test | `crates/tlx-live/tests/scale.rs` |
| `TLX_TRACE` | boolean (on when set) | off | The `tlx-sema` resolve test prints the model being processed | Test | `crates/tlx-sema/tests/resolve.rs` |
| `TLX_RUSTC_SLOTS` | positive integer | optional | Reserved for local build integrations; public build commands use their explicit `-j` limit | Developer | `crates/tlx-base/src/knobs.rs` |
| `TLX_HOOKS` | text | unset | Reserved for local development integrations; not required by the released sources | Developer | `crates/tlx-base/src/knobs.rs` |
| `TLX_MAIN` | directory | detected automatically | Location of the main checkout when public tools run from a linked worktree | Developer | `scripts/tlxlib.py` |
| `TLX_SEED` | integer | chosen by each test | Seed of the property tests (printed on failure), to replay a seed | Test | `crates/tlx-testkit/src/lib.rs` |
| `TLX_PROP_STATES` | integer | chosen by each test | `exec_vs_native_random`: number of states per family and seed | Test | `crates/tlx-compile/tests/exec_vs_native_random.rs` |
| `TLX_PROP_SEEDS` | integer | 20 | Number of seeds of the `--ignored` multi-seed test of `exec_vs_native_random` | Test | same |
| `TLX_DIFF_VERBOSE` | boolean (on when set) | off | `exec_vs_native*` tests: print statistics of every case | Test | `crates/tlx-compile/tests/exec_vs_native*.rs` |
| `TLX_DIFF_STRICT` | boolean (on when set) | off | `exec_vs_native`: a difference between IR executor and native code on erroring cases also counts as a failure | Test | `crates/tlx-testkit/src/diff.rs` |
| `TLX_DIFF_DUMP` | name | none | `exec_vs_native`: print the IR of the function of that name | Test | `crates/tlx-compile/tests/exec_vs_native.rs` |
| `TLX_THIRD_PARTY` | directory | `third_party/` | Where tests find `third_party/` (tla2tools.jar, Examples, community) | Test | `crates/tlx-testkit/src/lib.rs` |
| `TLX_CORPUS_OUT` | directory | `corpus/out/` | Where tests find `corpus/out/` (the TLC oracle results) | Test | same |
| `TLX_REQUIRE_THIRD_PARTY` | boolean (on unless `0`) | off | Tests that need `third_party/` panic instead of skipping when it is missing (also when `CI` is set) | Test | same |
| `TLX_KEEP_TMP` | boolean (on when set) | off | Do not delete the testkit's temporary directories after use | Test | same |
| `TLX_SER_RECOVER_MODE` | text | none | The mode `tlx-layout/tests/ser_recover.rs` passes to its own child process; not a configuration option | Test | that test |
| `TLX_SER_RECOVER_FILE` | path | none | As above: the file the child process works on | Test | that test |
| `TLX_BUILD_PROFILE` | cargo profile name | `test-release` | The profile of the tlx binary that the test scripts (spectest, difftest, matrix, coverage, fuzz_expr, sanydiff) build and run (`target/<profile>/tlx`); `release` adds `--release` on every run. tlx itself does not read it; `verify.py` strips it (use `verify.py --profile`) | Developer | `scripts/tlxlib.py` |
| `TLX_SPEC_TIMEOUT` | seconds | 120 | The default `spectest.py --timeout` budget for each tlx case and for collecting its TLC oracle; the option overrides it. tlx itself does not read it; pass `verify.py --env TLX_SPEC_TIMEOUT=S` to override it in a gate run | Developer | `scripts/spectest.py` |
| `TLX_CLOUD_CONFIG` | path | `~/.config/tlx/cloud.json` | Local configuration of the cloud identities (account/ARN, CLI profile) that the cloud scripts (`cloud_verify.py` and its providers) may use; the scripts refuse to run when the file or the provider's entry is missing (format in [cloud-verification.md](cloud-verification.md) section 2). tlx itself does not read it | Developer | `scripts/cloud/cloud_common.py` |

Notes:

- `tlx-runtime` reads no configuration environment variable (its parameters come from the CLI through
  structs such as `Options` / `SimOptions`); `tlx-eval` reads only `TLX_MAX_DEPTH` and `TLX_SYMMETRY_PARANOID`. `IOEnv`
  (IOUtils) in `tlx-eval` exposes the whole process environment to the spec, as TLA+ semantics
  require; it is not configuration.
- At build time `tlx-native/src/build.rs` also passes `TLX_TMP`, `TLX_LIB`, `TLX_SRC`, `TLX_KEEP`
  and `TLX_LOG` to the child process; these are implementation details, not configuration.
- Diagnostic output (`tlx-base::diag`): `TLX_COVERAGE`, `TLX_CGEN_DEBUG`, `TLX_EQ_DEBUG`,
  `TLX_IR_DUMP`, `TLX_JIT_DISASM` and `TLX_BAILOUT_DEBUG` each enable one diagnostic topic and the
  output lines are uniformly `topic: text` (`compile:`, `cgen:`, `eq:`, `ir:`, `jit:`, `bailout:`).
  The lines of `compile:` (always on) and of `TLX_COVERAGE` belong to the compile progress stream
  and go to stdout (stderr under `-tool`); the other topics go to stderr. TLC messages do not use
  this channel.
- `TLX_OK` / `TLX_ERR` / `TLX_STOP` / `TLX_UNSUPPORTED` and similar names in the generated C code are
  ABI constants and unrelated to the environment.

## Script options

Conventions shared by the scripts (`scripts/tlxlib.py` and `scripts/tlc.py`):

| Option | Meaning | Scripts |
|---|---|---|
| `-j N` | number of parallel jobs, default 3 (`tlxlib.DEFAULT_JOBS`) | `difftest.py`, `corpus.py`, `coverage.py`, `sanydiff.py`, `matrix.py` |
| `--filter S` | run only the corpus models whose id contains `S` | `difftest.py`, `coverage.py`, `matrix.py`, some subcommands of `bench.py` |
| `--timeout S` | timeout of a single run (seconds) | `difftest.py` (120), `matrix.py` (120), `corpus.py` (600), `coverage.py` (60), `bench.py` (600; `tlcbase` 1800) |
| `--extra=ARGS` | extra arguments for tlx; a value that starts with `-` must be written as `--extra=-compile` | `difftest.py`, `spectest.py` |
| `--default-mode` | run tlx in its default mode and tier (without `-tlc`) and compare verdicts with TLC | `difftest.py`, `spectest.py` |
| `--workers N` | tlx's `-workers` | `difftest.py` (1), `bench.py` (all cores) |
| `--refresh` | run TLC / SANY again instead of using the cache | `spectest.py`, `sanydiff.py` |
| `--release` / `--profile P` | build and run the release binary (or cargo profile `P`); the default is the fast profile `test-release` (`target/test-release/tlx`) and the environment variable `TLX_BUILD_PROFILE` changes the default (see [testing.md](testing.md) section 3) | `spectest.py`, `difftest.py`, `matrix.py`, `coverage.py`, `fuzz_expr.py`, `fuzz_spec.py`, `sanydiff.py`; `bench.py` always uses release; `verify.py --profile` defaults to release |

Options specific to a script:

| Script | Options |
|---|---|
| `spectest.py` | `-j N` (parallel spec jobs, default 1), `--default-mode`, `NAME...` (default: all specs with a cfg under tests/specs) |
| `difftest.py` | `--default-mode`, `--tag TAG` (result file `corpus/out/tlx<TAG>.json`), `--ids A,B` (select models by exact id), `--failed` (rerun only the previous failures), `--recover N` (end each run after the N-th checkpoint and recover it), `-v` (print the error output of failing models) |
| `corpus.py` | `list\|tlc`, `--max-runtime S`, `--min-runtime S`, `--name NAME`, `--tlc-workers N`, `--only-failed`, `--ids A,B` (exact ids; re-collects a row whose result a staging fix changed, which `--only-failed` does not flag) |
| `coverage.py` | `--hist N`, `--models`, `--dump DIR` (write each model's output into DIR); sets `TLX_COVERAGE`, `TLX_CGEN_DEBUG` and `TLX_NATIVE_SYNC` automatically |
| `bench.py` | subcommands `tiers`/`run`/`compare`/`report`/`ab`/`layout`/`table`/`tlcbase`/`tlcbase-merge`/`tlcbase-report` (see the script header and [benchmarking.md](benchmarking.md) section 1); `table`: `--models a,b,...`, `--no-tlc`, `--measure-tlc`, `--repeat R`; `run`: `--tlc`; `tlcbase`: `--tlc-repetitions N` (positive integer, default 1; collect N samples only for a missing baseline key); `run`/`suite`/`track`: `--isolate-cache` (off by default; fresh cache per configuration and binary, synchronous compilation); `suite`/`track`: `--with-tlc-companion` (off by default; also measure a same-instance `-tlc` twin of every default-mode run, same model, workers, arguments and cache policy); `ab`: `--bin NAME=PATH`, `--args` |
| `sanydiff.py` | `FILE_OR_DIR...` |
| `fuzz_spec.py` | `--seed N\|rev`, `--count N`, `--start I`, `--minutes M`, `--modes interp,compile,paranoid,w4,recover`, `--shrink N`, `--shrink-minutes M`, `--shrink-known`, `--save`, `--expr N`, `--replay`, `--replay-only [NAME...]`, `--record NAME...`, `--show`, `--keep`, `--out DIR`, `--results-json F --suite S` ([testing.md](testing.md) section 7.1) |
| `verify.py` | `--fuzz-minutes M` (duration of the `fuzz-campaign` suite); `cloud_verify.py --fuzz-minutes M` forwards it |
| `tlc.py` | `SPEC.tla [TLC arguments...]` |
| `cloud_verify.py` | see [cloud-verification.md](cloud-verification.md); launch admission: `--wait-quota MINUTES\|auto`, `--slots N`, `--max-account-slots N`, `--cancel`, coordinator `--grant OWNER --minutes M --slots N --budget-cny X [--reason TEXT]` (`--reason` required above 180 minutes, which name a heavy job), `--coordinator-hub` (authorizes `--grant`/`--budget-override`/`--prune-sg` in a bare-repository worktree pool); the optional `spot_instance_quota` and `default_share` fields of the cloud config |

Scripts that run tlx pass the current environment to tlx unchanged, so developer environment
variables can be put in front of the command, for example `TLX_PARANOID=1 python3 scripts/spectest.py --extra=-compile`.
