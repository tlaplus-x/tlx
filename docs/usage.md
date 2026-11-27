# tlx user guide

tlx is an explicit-state model checker for TLA+. It reads the same `.tla` and `.cfg` files as TLC,
prints results in TLC's format with TLC's exit codes, and by default specializes the whole model
to native code (the compiled tier), which is typically several times faster than TLC. This guide is for people
who already know TLA+ and TLC.

Related documents: [configuration.md](configuration.md) lists every command-line option and
`TLX_*` environment variable with its default (the only place where they are specified);
[compat.md](compat.md) defines what "same results as TLC" means and lists the differences and
limitations; [features.md](features.md) is the support matrix for options, `.cfg` keywords and
modules; [design.md](design.md) describes the architecture.

Contents: [1 Installation](#1-installation) · [2 First run](#2-first-run) ·
[3 Command line overview](#3-command-line-overview) · [4 Execution tiers](#4-execution-tiers) ·
[5 Compiled mode](#5-compiled-mode--compile) · [6 Multiple workers, symmetry and state reductions](#6-multiple-workers-symmetry-and-state-reductions) ([6.1](#61-checking-a-symmetry-declaration)–[6.4](#64-certified-state-projections--optimize-and-tlx-optimize)) ·
[7 Simulation and generation](#7-simulation-and-generation) ·
[8 Checkpoint and recovery](#8-checkpoint-and-recovery) ·
[9 Dumping states and traces, coverage](#9-dumping-states-and-traces-coverage) ·
[10 Output and exit codes](#10-output-and-exit-codes) · [11 Module search path](#11-module-search-path-and-community-modules) ·
[12 TLC compatibility of options](#12-tlc-compatibility-of-options) · [13 Troubleshooting](#13-troubleshooting)

---

## 1. Installation

| Requirement | Used for |
|---|---|
| Rust toolchain through [rustup](https://rustup.rs) (`rust-toolchain.toml` pins 1.93.0 and rustup installs it on the first `cargo` command) | building tlx |
| A C compiler named `cc` (clang on macOS, gcc or clang on Linux; override with the environment variable `CC`) | building tlx itself (the tree-sitter grammar) and, at run time, compiling the generated C code of the compiled tier (without it the JIT code stays; with no JIT either, the default tier is the interpreter) |
| Java (optional) | **not needed to run tlx**; only the test scripts that compare tlx with TLC or SANY use it, see [testing.md](testing.md) |

```sh
cargo install tlx                     # install from crates.io into ~/.cargo/bin/tlx
```

Or build from a source checkout:

```sh
cargo build --release                 # binary: target/release/tlx
cargo install --path crates/tlx-cli   # optional: install into ~/.cargo/bin/tlx
```

**Platforms.** macOS arm64 (Apple Silicon) is the primary development platform; Linux x86_64 and
arm64 are tested (the generated library is a `.so` there). Windows is not supported.

`tlx check -h` (also `-help`, `--help`) prints the complete option help to stdout and exits with 0.
There is no `--version`: the version is the first line of every run (`tlx version 0.1.2`), and an
invalid command line prints a one-line usage to stderr and exits with 2.

---

## 2. First run

This walkthrough needs no external files. It uses one four-state module, `Counter`, and a few
configuration files; put them in an empty directory and write `Counter.tla`:

```tla
---- MODULE Counter ----
EXTENDS Naturals

CONSTANT Limit

VARIABLE n

Init == n = 0

Next ==
    \/ n < Limit /\ n' = n + 1
    \/ n = Limit /\ n' = 0

Spec == Init /\ [][Next]_n

AtMostLimit == n <= Limit
Bounded == n < Limit
Three == 3
View == n % 2
====
```

`Next` increments `n` and wraps it back to 0 when it reaches `Limit`; `Spec` wraps the initial
predicate and the next-state relation into the one temporal formula that the `SPECIFICATION`
recipe below needs. `AtMostLimit`, `Bounded`, `Three` and `View` are the operators used by the
recipes and by the diagnostics further down.

### 2.1 Two configuration recipes

A run reads a configuration file: `tlx check Counter.tla` uses `Counter.cfg`, next to the module.
The two recipes below give identical results; which one you use is a matter of taste (they are
TLC's `INIT`/`NEXT` form and its `SPECIFICATION` form).

```text
\* Counter.cfg
CONSTANT Limit = 3
INIT Init
NEXT Next
INVARIANT AtMostLimit
```

```text
\* Counter-spec.cfg
CONSTANT Limit = 3
SPECIFICATION Spec
INVARIANT AtMostLimit
```

```sh
tlx check Counter.tla                        # reads Counter.cfg next to Counter.tla
tlx check Counter -config Counter-spec.cfg   # the .tla suffix may be omitted; another cfg file
tlx check Counter.tla -workers auto          # all cores
tlx check Counter.tla -interp                # the interpreter instead of the compiled tier
tlx check Counter.tla -tlc                   # TLC-compatible results (see section 4)
```

`INIT` and `NEXT` name the initial-state predicate and the next-state relation; `SPECIFICATION`
names one temporal formula. A configuration file may use one or the other, never both (exit code
151, section 2.8).

### 2.2 A passing run

`AtMostLimit` holds in every reachable state, so the run passes. The default compiled tier adds its
`compile:` progress lines ([section 5.2](#52-the-compile-log)) to the TLC-style output:

```
tlx version 0.1.2
Running breadth-first search Model-Checking with fp 0 and seed 0 with 1 worker on 18 cores with 32768MB fingerprint memory [pid: 83926] (macos aarch64, tlx 0.1.2).
Optimizations: none applicable.
Starting... (2026-10-08 16:58:42)
Computing initial states...
compile: pre-run: 0.00s, 4 states
compile: lowering and code generation: 0.00s
compile: layout: 1 words; 2/2 actions lowered, 2 fully typed; IR nodes 13 (0 boxed, 0 interpreter)
compile: IR invariants: 1 lowered; IR nodes 4 (0 boxed, 0 interpreter)
compile: IR action properties: 0 lowered; IR nodes 0 (0 boxed, 0 interpreter)
compile: native code: 2/2 actions, 1/1 invariants, Init
Finished computing initial states: 1 distinct state generated at 2026-10-08 16:58:42.
Model checking completed. No error has been found.
  Estimates of the probability that TLC did not check all reachable states
  because two distinct states had the same fingerprint:
  calculated (optimistic):  val = 2.2E-19
5 states generated, 4 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 4.
The average outdegree of the complete state graph is 1 (minimum is 0, the maximum 1 and the 95th percentile is 1).
Finished in 00s at (2026-10-08 16:58:42)
```

`-interp` prints the same lines without the `compile:` ones. The exit code is 0, as in TLC; see
[section 10.3](#103-exit-codes).

The `32768MB` in the start-up line is not a fixed fingerprint-set size. Without `-fpmem` it is the
`-maxmem` budget (by default half of the physical memory; the machine in the example has 64 GiB);
the fingerprint set starts at 8 MiB and grows on demand within that budget. With `-fpmem` the line
prints the fixed size (see `-fpmem` in [configuration.md](configuration.md)).

### 2.3 A violated invariant

`Counter-violation.cfg` keeps `INIT` and `NEXT` but checks `Bounded` (`n < Limit`), which the
generated state `n = 3` violates:

```text
\* Counter-violation.cfg
CONSTANT Limit = 3
INIT Init
NEXT Next
INVARIANT Bounded
```

```
tlx version 0.1.2
... (the start-up and compile: lines of section 2.2) ...
Error: Invariant Bounded is violated.
Error: The behavior up to this point is:
State 1: <Initial predicate>
n = 0

State 2: <Next line 11, col 8 to line 11, col 30 of module Counter>
n = 1

State 3: <Next line 11, col 8 to line 11, col 30 of module Counter>
n = 2

State 4: <Next line 11, col 8 to line 11, col 30 of module Counter>
n = 3

4 states generated, 4 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 4.
Finished in 00s at (2026-10-08 16:58:42)
```

The exit code is 12. Every `State` line names the source span of the action instance that produced
the state; here all three successors come from the first disjunct of `Next`, `Counter` line 11
column 8 to column 30.

### 2.4 The other recipes at a glance

Further configuration files for the same module exercise the remaining `.cfg` concepts:
`CONSTRAINT`, `VIEW` and a `CONSTANT ... <- ...` replacement. All of them were run with
`-workers 1`; generated/distinct counts, the search depth and the exit code are the same in the
default, `-interp`, `-compile`, `TLX_PARANOID=1 -compile`, `-tlc` and `-tlc -interp` modes, and
they agree with TLC's for the same files:

| Configuration file | Change | generated / distinct / depth | Exit |
|---|---|---|---|
| `Counter.cfg` | `INIT`/`NEXT`, invariant `AtMostLimit` | 5 / 4 / 4 | 0 |
| `Counter-spec.cfg` | `SPECIFICATION Spec` | 5 / 4 / 4 | 0 |
| `Counter-violation.cfg` | invariant `Bounded` | 4 / 4 / 4 | 12 |
| `Counter-constraint.cfg` | `CONSTRAINT Bounded` | 4 / 3 / 3 | 0 |
| `Counter-con-vs-inv.cfg` | `CONSTRAINT Bounded` *and* invariant `Bounded` | 4 / 3 / 3 | 12 |
| `Counter-view.cfg` | invariant `AtMostLimit`, `VIEW View` | 3 / 2 / 2 | 0 |
| `Counter-viewviol.cfg` | invariant `Bounded`, `VIEW View` | 3 / 2 / 2 | 0 |
| `Counter-repl.cfg` | `CONSTANT Limit <- Three` | 5 / 4 / 4 | 0 |

Sections 2.5 to 2.8 explain the rows that do more than restate the first recipe.

### 2.5 Constants, model values and `<-` replacements

`Limit` gets its value in one of three ways:

| In the configuration file | Value of `Limit` |
|---|---|
| `CONSTANT Limit = 3` | the integer 3 |
| `CONSTANT Limit <- Three` | the value of the operator `Three` of the module (3 here) |
| `CONSTANT Limit = p` | the model value `p`, because the module does not define `p` |

A replacement (`<-`) deserves its own file; everything else stays as in the first recipe:

```text
\* Counter-repl.cfg
CONSTANT Limit <- Three
INIT Init
NEXT Next
INVARIANT AtMostLimit
```

Model values are atoms that are equal only to themselves; a spec uses them where a constant stands
for an arbitrary element (a process, a server). They are not numbers, so using one where `Next`
expects an integer fails during the initial state: `Error: The argument of <= should be an integer,
but instead it is: p` (exit code 75, an evaluation error). A string (`CONSTANT Limit = "3"`) fails
the same way. Omitting the line while the module declares the constant is reported before the
search starts (exit code 151). `<-` needs an operator name, not a formula: `CONSTANT Limit <- 2 + 1`
is a configuration syntax error (exit code 150).

### 2.6 `CONSTRAINT` versus `INVARIANT`

Both name an operator of the module, and neither accepts a formula in the configuration file
(`INVARIANT n <= Limit` is a syntax error, exit code 150). They differ in what they do with a
state that does not satisfy them:

- `INVARIANT Bounded` reports the generated state `n = 3` and stops: 4 generated, 4 distinct,
depth 4, exit code 12. The trace names the violation, and the run covers the whole state space.
- `CONSTRAINT Bounded` *prunes*. The state `n = 3` is generated but dropped, so it is counted as
generated and not explored (4 generated, 3 distinct, depth 3), and the run passes with exit code 0.
Here "no error" means "no error among the states the constraint keeps", not that the property holds
of the spec: turning a property into a constraint is only meaningful if the pruned states are
outside the question you asked.
- With both, the invariant still fires (a generated state is checked even when the constraint would
drop it): exit code 12, 4 generated, 3 distinct, depth 3.

The last two rows are these two files (the first is [section 2.3](#23-a-violated-invariant)):

```text
\* Counter-constraint.cfg
CONSTANT Limit = 3
INIT Init
NEXT Next
CONSTRAINT Bounded
```

```text
\* Counter-con-vs-inv.cfg
CONSTANT Limit = 3
INIT Init
NEXT Next
CONSTRAINT Bounded
INVARIANT Bounded
```

### 2.7 `VIEW`: smaller state graphs, weaker guarantees

`VIEW View` replaces the fingerprint of a state with the value of `View` (here `n % 2`), so the
states `n = 0` and `n = 2` count as one. The state space shrinks to 3 generated / 2 distinct states
and depth 2, and `Counter-viewviol.cfg` — the same `INVARIANT Bounded` that failed in section 2.3 —
now passes: `n = 3` is never reached, because `n = 2` is not expanded. TLC reports the same counts
and the same exit code for the same files.

```text
\* Counter-view.cfg
CONSTANT Limit = 3
INIT Init
NEXT Next
INVARIANT AtMostLimit
VIEW View
```

```text
\* Counter-viewviol.cfg
CONSTANT Limit = 3
INIT Init
NEXT Next
INVARIANT Bounded
VIEW View
```

`Counter-viewviol.cfg` is the first file with the invariant changed to `Bounded`; it is the same
recipe as `Counter-violation.cfg` plus the `VIEW` line.

`VIEW` (like `SYMMETRY`) is a fingerprinting optimization, not a way to state a requirement. Two
states with the same view value must be interchangeable for every property you check, or the run
can miss a violation. When the compiled tier can evaluate the view natively, its log says so:

```
compile: materialized definitions: View
compile: view: fingerprints of the encoded VIEW (native)
```

Two documented differences in [compat.md](compat.md) bound what a run with `VIEW` or `SYMMETRY`
promises:

- **D-10**: a liveness lasso is valid only *modulo* the view. The reported back edge may return to
a state with the same view value as the state it leaves, while the variables differ.
- **D-30**: rebuilding a counterexample under `VIEW` or `SYMMETRY` is counter-dependent. tlx keeps
the violated name and the verdict, and prints only the prefix it can genuinely reconstruct, naming
the reason (run-time counters such as `TLCGet`/`TLCSet`, for example) in place of the states it
cannot. Such a prefix shows that the property fails; it is not a complete execution path
([DOC-08](development-standards.md)). For the whole behavior, check the spec again without `VIEW`
and without `SYMMETRY`, where the same violation is reported with a complete trace.

TLC's `-view` command-line option is not implemented; the `VIEW` configuration keyword is
([features.md](features.md) section 1). In the default mode a `VIEW` that is a tuple of state
variables may additionally compose with automatic symmetry
([section 6.3](#63-automatic-symmetry-in-the-default-mode)); `-tlc` and `-noautosymmetry` keep the
plain `VIEW` search.

### 2.8 Diagnosed before or during the run

The messages below are what a mistake in the module or the configuration file produces. The
configuration messages carry the file name and the position first, and a long message is wrapped
over two lines; the prefix is omitted here and the wrap is joined.

| You wrote or ran | Message | Exit |
|---|---|---|
| `INVARIANT n <= Limit` | ``expected a name in INVARIANT list, found operator `<=` ``, then `Error: Parsing the configuration failed.` | 150 |
| `CONSTRAINT n < Limit` | ``expected a name in CONSTRAINT list, found operator `<` ``, then the same `Error:` line | 150 |
| `CONSTANT Limit <- 2 + 1` | ``expected an operator name after `Limit <-`, found number `2` ``, then the same `Error:` line | 150 |
| no `CONSTANT Limit` line | `Error: The constant parameter Limit is not assigned a value by the configuration file.` | 151 |
| `SPECIFICATION Spec` together with `INIT`/`NEXT` | `Error: The configuration file specifies both a SPECIFICATION and an INIT or NEXT.` | 151 |
| `INVARIANT NotDefined` | `Error: The invariant NotDefined specified in the configuration file is not defined in the specification.` | 151 |
| `INVARIANT Three` (not a state predicate) | `Error: The invariant of Three is equal to 3.` | 150 |
| `CONSTANT Limit = "3"` or `= p` | `Error: The argument of <= should be an integer, but instead it is: "3"`, then the position in the module and `While working on the initial state:` | 75 |
| `-config nope.cfg` | `Error: cannot read nope.cfg: No such file or directory (os error 2)` | 150 |
| `EXTENDS Nope` instead of `EXTENDS Naturals` | `Counter.tla:2:9: cannot find module Nope`, then `Error: Parsing or semantic analysis failed.` | 150 |
| `Next` without its second disjunct (so it disables at `n = 3`), without `-deadlock` | `Error: Deadlock reached.`, then the behavior | 11 |
| `Limit = 200000` with `-fpmem 1` | `Error: The fingerprint set is full; rerun with a larger -fpmem.`, then `-fpmem 1 MiB holds 117965 states.` and `Suggested -fpmem: 2 MiB or more.` | 255 |
| a failing or missing C compiler | synchronous build (`TLX_NATIVE_SYNC=1`): `compile: C build failed, using the JIT code: no C compiler (/nonexistent/cc not found)`; the default background build, once it starts: `compile: C build failed, keeping the JIT code: ...`; with `TLX_JIT=0`: `compile: native code disabled: ...`; with neither JIT nor compiler: `compile: no JIT and no C compiler (... not found): checking with the interpreter` | 0 (or 12), unchanged |

A failed C build never changes the result: the compiled tier falls back to the JIT code, or, with
neither, to the interpreter. The background build starts only after `TLX_CC_DELAY_MS` (1.5 s by
default), so a run that ends sooner prints no build line at all. The exact lines and the fallbacks
are in [section 5.4](#54-fallbacks);
[section 13](#13-troubleshooting) has the same problems with more background. Exit code groups are
in [section 10.3](#103-exit-codes).

---

## 3. Command line overview

```
tlx check Spec.tla [options]
tlx optimize Spec.tla -output DIR [-config FILE] [-I DIR]...
tlx parse Spec.tla
```

`tlx check` runs model checking, simulation, or bounded symmetry diagnostics; options keep TLC's
spelling and meaning (single dash; `-deadlock` *disables* deadlock checking). `tlx optimize` emits a
certified finite abstraction and its standalone Lean proof into `DIR` without exploring states
([section 6.4](#64-certified-state-projections--optimize-and-tlx-optimize)). `tlx parse Spec.tla`
parses the modules in `Spec.tla` without resolving imports, reading a configuration, or running
model checking (exits 0 on success, 1 on syntax errors, and 2 on argument or file errors). All
options and defaults are listed in [configuration.md](configuration.md); `tlx check -h` and
`tlx optimize -h` print the same lists. An unknown option (including TLC options tlx does not
implement, such as `-continue`) prints a usage line and exits with 2.

| You want to | Use |
|---|---|
| choose the configuration file | `-config F` |
| run on several cores | `-workers N` or `-workers auto` ([section 6](#6-multiple-workers-symmetry-and-state-reductions)) |
| apply certified state projections | `-optimize`, `-proofdir DIR`, or `tlx optimize` ([section 6.4](#64-certified-state-projections--optimize-and-tlx-optimize)) |
| run the interpreter instead of the compiled tier (the default) | `-interp` ([section 4](#4-execution-tiers)) |
| TLC-identical counts, depth and traces | `-tlc` ([section 4](#4-execution-tiers)) |
| random simulation instead of exhaustive search | `-simulate`, `-generate`, `-depth`, `-seed` ([section 7](#7-simulation-and-generation)) |
| survive interruptions | `-checkpoint`, `-recover`, `-metadir` ([section 8](#8-checkpoint-and-recovery)) |
| export states or the counterexample | `-dump`, `-dumpTrace` ([section 9](#9-dumping-states-and-traces-coverage)) |
| see which actions fire | `-coverage N` ([section 9.3](#93--coverage)) |
| limit memory or disk, handle huge state spaces | `-maxmem`, `-fpmem`, `-spill`, `-maxdisk` (see [configuration.md](configuration.md) and [scale.md](scale.md)) |
| add module directories | `-I dir`, `TLX_PATH`, `TLX_CLASSPATH` ([section 11](#11-module-search-path-and-community-modules)) |
| machine-readable output | `-tool` ([section 10.2](#102--tool-output)) |
| find out where the time went | `-stats` |

---

## 4. Execution tiers

| Tier | Switch | Description |
|---|---|---|
| Compiled | default (`-compile`) | Infers the state layout, lowers the model to a typed IR and then to native code: first an in-process Cranelift JIT (milliseconds), then, after the search has run for 1.5 s, a background `cc -O2` build that is loaded with `dlopen` and replaces the JIT code (`TLX_JIT` in [configuration.md](configuration.md)). Typically an order of magnitude faster than the interpreter on medium and large models; on tiny models the pre-run usually explores everything and the extra cost is a few milliseconds. |
| Interpreter | `-interp` | Evaluates and enumerates over dynamic values with TLC's semantics; it is tlx's semantic reference. No pre-run, no compilation; useful for debugging and for comparing with the compiled tier. |

Both tiers must give identical results (counts, depth, counterexamples, errors); a difference is a
bug. `TLX_PARANOID=1` cross-checks the compiled tier against the interpreter ([section 13](#13-troubleshooting)).
The last of `-compile` and `-interp` on the command line wins. If there can be no native code at
all (a build without the JIT, or `TLX_JIT=0`, and no C compiler) the default is the interpreter, and
one line `compile: no JIT and no C compiler (cc not found): checking with the interpreter` says so.

**Modes.** `-tlc` asks for TLC-compatible results: verdicts, violated names, state counts, depth and
shortest-trace length as TLC's ([compat.md](compat.md) section 0). Without it, the default mode may
use optimizations TLC does not have; they keep the verdicts sound (a violation is reported exactly
when one exists, with a genuine counterexample) but may change counts, depth or the counterexample.
Automatic symmetry applies only within its connected certificate coverage
([section 6.3](#63-automatic-symmetry-in-the-default-mode)). Every run in the default mode names
the optimizations it used in an `Optimizations:` line.

---

## 5. Compiled mode (`-compile`)

The compiled tier is the default; `-compile` names it explicitly.

### 5.1 How it works

1. **Pre-run.** A short interpreted BFS (by default at most 20,000 states or 1 second; the initial
   states are not subject to the time limit) observes the values of every variable and infers
   their shape (integer interval, enumeration, set, function, record, sequence, ...). Together with
   the constants of the cfg file and constant sets in the spec this gives a fixed-size state layout.
2. **Lowering and code generation.** Every action instance, invariant, action property and
   liveness atom is lowered to a typed IR and C code is generated. Sub-expressions that cannot be
   typed statically stay "boxed" values or call back into the interpreter (slower but correct).
3. **Search.** By default the Cranelift JIT compiles the code in-process (ready before exploration
   starts); after the search has run for 1.5 s a **background thread** builds the C code with
   `cc -O2` and swaps it in, so short runs do not pay for `cc`. With `TLX_JIT=0` only C is used and
   the search runs on the IR until the C library is ready (same results). A very small model may
   finish before the native code is ready (`native build still running at the end of the search`;
   normal). The tiers are described in [design.md](design.md) section 6.6.
4. **Layout miss.** Before storing a state, generated code checks that every value fits the
   inferred shape. If one does not, a *layout miss* occurs: the shape is widened with the
   offending value, code is regenerated, and the search **continues from the beginning of the
   level that failed**. Visited states are kept in a compressed archive and re-encoded for the new
   layout; the trace log is only rewritten with new fingerprints. The archive goes to disk when
   the memory budget is exceeded. The search starts over from scratch if re-encoding is expected to
   be slower than searching again, if the in-memory part of the archive exceeds `TLX_RETAIN_MB`, or
   if it exceeds the memory budget under `-spill off`. At most 16 restarts happen; at the last one
   the variable becomes dynamic (`Dyn`, which holds any value). Counts, depth and counterexamples
   equal those of an uninterrupted search.

### 5.2 The `compile:` log

Compiled mode interleaves lines that start with `compile:` with the TLC-style output (stdout; they
are not wrapped under `-tool`):

```
compile: pre-run: 0.00s, 100 states
compile: lowering and code generation: 0.00s
compile: layout: 1 words; 2/2 actions lowered, 1 fully typed; IR nodes 24 (3 boxed, 0 interpreter)
compile: native code: 1/2 actions, 1/1 invariants, Init
compile: layout miss on n (value 149); widening and restarting
compile: resuming the search at depth 149: 149 states re-encoded in 0.00s
compile: native code (-O2) ready after 0.60s
```

| Line | Meaning |
|---|---|
| `pre-run: T, N states` | Pre-run time and state count; `(time budget)` means it was cut off by the time budget. |
| `pre-run reused as the search` | The pre-run exhausted the state space (or stopped at a violation) within its budget, so its result is the result of the run (`TLX_PRERUN_REUSE`). |
| `layout: W words; a/n actions lowered, t fully typed; IR nodes X (b boxed, i interpreter)` | Every state takes W 64-bit words; a of n action instances were lowered, t of them fully typed. Fewer boxed / interpreter nodes is faster. |
| `native code: a/n actions, i/m invariants, Init` | How many actions and invariants (and Init, action properties) got native code; the rest run in the IR or the interpreter. |
| `native code (JIT) ready after T (compile C)` | The JIT code is ready (before exploration starts). |
| `native code (-O2) ready after T` | The C library is ready and replaced the JIT code (close to 0 on a cache hit; absent when the run ended before the C build started). |
| `C build failed, keeping the JIT code: ...` | The C build failed (for example no `cc`), in the default asynchronous build: the JIT code stays; results and speed are essentially unaffected. The same failure with a synchronous build (`TLX_NATIVE_SYNC`) prints `C build failed, using the JIT code: ...`. |
| `native code disabled: ...` | There is no JIT code (`TLX_JIT=0`, or `JIT disabled: ...`) and the C build failed: the run completes on the IR, correct but slow. |
| `layout miss on VAR (value V); widening and restarting` | See 5.1. A few are normal; many mean the pre-run was too short (raise `TLX_PRERUN` / `TLX_PRERUN_MS`). |
| `resuming the search at depth D ...` / `starting over ...` | After a miss: continue from the failed level / start from scratch. |
| `N action evaluations fell back to the interpreter` | Some action evaluations fell back to the interpreter. |
| `pre-run failed (...); using Dyn layout` | The pre-run failed (for example the model has an error early on): all variables are dynamic; the error is still reported correctly. |

### 5.3 Build cache

- The generated C and the built library are cached in `~/.cache/tlx/<hash>/` (`model.c`,
  `model.dylib` / `model.so`, `tlx_abi.h`); change the directory with `TLX_CACHE`. The hash covers the
  C source, the ABI header, the compiler name and its flags, so running the same model again reuses it.
- The cache can be deleted at any time; several tlx processes can share it safely.
- Its size is bounded: `TLX_CACHE_MB` (default 1024 MiB). Whenever a new library is built, the
  least recently used entries beyond the limit are removed (not the ones used in the last 10
  minutes or being built). Editing a spec usually changes the C source, so each edit adds an entry.
- The first run of a model (or of an edited spec) has a cold cache: it runs on JIT code, and when
  the search lasts more than 1.5 s it builds the C library in the background (a build still running
  when tlx exits finishes into the cache). Later runs load the library at once.
- A failed build leaves no files behind; the `compile:` line shows the compiler's first error.

### 5.4 Fallbacks

| Situation | Behavior |
|---|---|
| No C compiler / C compilation fails | Keeps the JIT code (`C build failed, keeping the JIT code`, or `using the JIT code` when the build ran synchronously with `TLX_NATIVE_SYNC`); with no JIT code, `native code disabled` and the whole search runs on the IR. |
| An action or invariant cannot get native code | Only that one runs in the IR (`cgen: ... not native: reason`, shown with `TLX_CGEN_DEBUG`). |
| A sub-expression cannot be typed | Boxed value, or a call back into the interpreter. |
| A value exceeds the inferred shape | Layout miss: widen and resume / restart (at most 16 times, then `Dyn`). |
| The pre-run fails | All variables are `Dyn`. |
| `VIEW` together with `SYMMETRY`, or a `SYMMETRY` whose shape cannot be permuted | Fingerprints are computed on values (decoded and evaluated by the interpreter): slower but correct. |

### 5.5 Environment variables

Tuning and debugging variables (pre-run budget `TLX_PRERUN` / `TLX_PRERUN_MS`, resumption
`TLX_RETAIN_MB`, native-code tiering `TLX_JIT`, cross-checking `TLX_PARANOID`, diagnostics
`TLX_COVERAGE` / `TLX_CGEN_DEBUG` / `TLX_IR_DUMP`, ...) are not needed for normal use. Defaults and
meanings are in the environment variable table of [configuration.md](configuration.md).

---

## 6. Multiple workers, symmetry and state reductions

`-workers N` (or `-workers auto`, one worker per logical CPU available to the process) runs a
**level-synchronous parallel BFS**: all workers expand the states of one BFS level, wait at a
barrier, and continue with the next level. As a result the search depth, the length of the shortest
counterexample and, for a run that finishes without error, the generated and distinct state counts
equal TLC's. `-workers 0` is rejected. Sections [6.1](#61-checking-a-symmetry-declaration)–[6.4](#64-certified-state-projections--optimize-and-tlx-optimize) cover symmetry verification, automatic symmetry, and certified state projections.

What is not deterministic with several workers (all tier 3 of the [compatibility contract](compat.md)):

- which of several equally short counterexamples is reported, and, when a run stops at a violation,
  the exact counts at that point (as in TLC; [compat.md](compat.md) D-3);
- the order of `Print` output, and the order of sets containing run-time strings
  ([compat.md](compat.md) D-9);
- the order in which simulation behaviors are produced.

For reproducible results use `-workers 1` (all comparisons with TLC are defined at one worker).
A narrow, deep state graph gains little from more workers. `auto` counts SMT threads and ignores the
current load; on an x86 SMT machine 16 threads were measured 20-35% faster than 8 physical cores.

### 6.1. Checking a symmetry declaration

When tlx applies a declared symmetry as a product of full permutation groups, it supports up to
65,536 factors with up to 65,535 model values per factor. Overlapping permutation sets count
as one factor per connected component. A declaration that exceeds either limit produces an error
before exploration.

TLC trusts `SYMMETRY`. A definition that selects a particular model value, for example
`CHOOSE a \in Acceptors : TRUE`, can make transitions depend on the representative of an orbit.
Reduced searches can then miss behavior; parallel searches may give different counts.
Use tlx's bounded diagnostic before relying on that reduction:

```sh
tlx check Spec.tla -checksymmetry
tlx check Spec.tla -checksymmetry -symmetrystates 5000 -symmetrydepth 8
```

The diagnostic explores concrete states without SYMMETRY or VIEW reduction. For each selected
permutation it compares initial-state membership, complete successor sets across all actions,
each invariant, VIEW equivariance, and each state/action constraint. Constraints restrict the BFS,
but the comparisons include rejected successors and edges. A violation prints the permutation,
the differing component (and action for an edge), the BFS trace, and the permuted values.

For VIEW the condition is `V(p(s)) = p(V(s))`: evaluating the permuted state must give the
permutation of the original view. Comparing `V(p(s))` directly with `V(s)` would falsely reject
views containing model values (such as a server-keyed function). For Boolean views and
predicates, permutation leaves the result unchanged, so this reduces to equal truth values.
This checks consistent relabelling of views, not whether VIEW is itself a valid abstraction.

`Permutations(S)` and unions of such sets use adjacent swaps as generators, including through
zero-argument aliases. Other declarations use their finite set of permutations. No full group
closure is needed. The diagnostic always uses the interpreter, including when `-compile` is
present; it does not check temporal properties or the compiled implementation.

“No symmetry violation found within bounds” is not a proof. A generator check at a sampled
state does not cover all images or all reachable states. State/depth limits restrict the sample;
permutation or successor limits make the check explicitly incomplete. Evaluating an arbitrary
symmetry expression or a single predicate can itself be expensive; these limits are not a time
or byte limit. Side-effectful or random predicates are unsuitable for this diagnostic because
it evaluates them repeatedly. The diagnostic exits with 0 for no violation within bounds, 1
for a witness, and 2 when it cannot finish; errors while loading the model or checking assumptions
retain the normal exit codes. See [configuration.md](configuration.md) for limits.

### 6.2. Undeclared symmetry

Many models bind a constant to a set of interchangeable model values (`RM = {r1, r2, r3}`) and
do not declare the symmetry. Before the search, tlx looks for such sets (a CONSTANT whose cfg
value is a set of at least two model values, also through a `<-` substitution of a constant
definition) that the cfg's SYMMETRY does not cover, and tries to prove statically that every
permutation of them is an automorphism of the checked state graph. A candidate group is applied
automatically only when it also receives a connected Lean certificate
([section 6.3](#63-automatic-symmetry-in-the-default-mode)). Under `-tlc`, tlx prints a
suggestion: when the proven group also receives a Lean certificate for default-mode automatic
symmetry, it notes both options:

```
Symmetry: Permutations(RM) is provable for safety checking and not declared; to use it, run without -tlc, or define Perms == Permutations(RM) and add "SYMMETRY Perms" to the cfg.
```

(When default mode certifies a proper subset `G` of the proven group, it prints `run without -tlc to use G, or define Perms == ... and add "SYMMETRY Perms" to the cfg for the full group.`) When the proven group lacks a Lean certificate for automatic application, it omits `run without -tlc`:

```
Symmetry: Permutations(RM) is provable for safety checking and not declared; to use it, define Perms == Permutations(RM) and add "SYMMETRY Perms" to the cfg.
```

For a run that checks temporal properties the line warns instead that a reduction does not apply to
them.

The proof is a scalarset analysis of everything the safety checks evaluate (the initial
predicate, the next-state relation, invariants, constraints, action constraints, action
properties, initial-state `PROPERTY` predicates, `_POSSIBLE` predicates, and `POSTCONDITION`s).
It tracks which values may contain elements of the set, and accepts the set only
when those values are used through operations that treat all elements alike: equality and
membership, set, function, record, tuple, sequence and bag operators, quantifiers, IF/CASE,
`Permutations`, and folds with `+`, `*`, `\cup` or `\cap`. These break the symmetry when applied
to such values and reject the set, naming the location: `CHOOSE` (TLC chooses by value order, so
the choice depends on the elements' names, unless the predicate fixes the element by an
equality `x = e` or a connected `ChooseSymCertificate` proves the `CHOOSE` idiom choice-irrelevant —
unique witness, uniform/constant projected value, or commutative-associative recursive `CHOOSE`
integer set-sum fold — in which case the candidate is promoted rather than rejected), `SetToSeq`,
`ToString`, `Max`/`Min` of FiniteSetsExt, JSON conversion, `TLCModelValue`, `RandomElement`, folds
over a set or a function's domain with another operator, and order-dependent CommunityModules
operators. A constant whose value singles out elements (`Leader = r1` in the cfg, or a constant
definition `Leader == CHOOSE r \in RM : TRUE`) restricts the group to the permutations that fix it,
for example `Permutations(RM \ {r1})`. The analysis is conservative: it can reject a symmetric
spec, but a proven group maps initial states to initial states, successors to successors, and
preserves every invariant, constraint, action property, initial-state property, `_POSSIBLE`
predicate and `POSTCONDITION`. It does not cover temporal properties: under SYMMETRY, TLC's
liveness checking can both miss violations and report spurious ones.

With `-stats`, the report's `auto symmetry` section lists every candidate set with the proven
group or the reason it is not proven; specs that print, use TLCGet/TLCSet registers, randomness
or IO in the checked parts are reported too, since their output depends on which states are
explored.

`-checksymmetry -suggest` runs the analysis and then the bounded diagnostic of section 6.1 on
each candidate set: on the proven group as a cross-check of the proof (a proven group with a
witness is an internal error of tlx and exits with 101), and on all permutations of a set the
analysis does not prove (evidence, not a proof). It ends with the definition to paste:

```sh
tlx check MCKVS.tla -config MCKVSSafetySmall.cfg -checksymmetry -suggest
```

```
Symmetry: Key = {k1, k2}: proven: Permutations(Key); bounded check: no violation in 1000 states, depth 6.
...
Proven symmetry: define Perms == Permutations(Key) \cup Permutations(Val) \cup Permutations(TxId) and add "SYMMETRY Perms" to the cfg.
```

### 6.3. Automatic symmetry in the default mode

Automatic symmetry applies a disjoint product of full groups (two to seven model
values each, total order at most 5,040) when backed by a connected Lean certificate
(`KeyedCertificate`, `EquivSymCertificate`, or `ChooseSymCertificate`). Each
application emits standalone Lean before search, without invoking Lean. The
[certificate coverage](optimization.md#certified-keyed-symmetry) describes
supported shapes, expressions, and trusted layers. The Rust candidate analysis and
bounded checks cannot substitute for this certificate; the development force
setting cannot bypass the gate.

Before installing a certified group, tlx also runs a bounded 20 ms generator
cross-check (`symcheck::check_perms`) on concrete initial states and transitions:
a symmetry witness there is an internal error (exit 101), while an evaluation error
or incomplete check refuses automatic symmetry (`not applied: cross-check failed (...)`)
rather than applying it.

Other candidates remain available through analysis and `-checksymmetry -suggest`.
Their refusal is recorded in the `auto symmetry` section of `-stats`.

A declared `.cfg` `SYMMETRY` is used verbatim under `-tlc` and `-noautosymmetry`. In the
default mode, when it factors as a disjoint product of full permutation groups over model
values, tlx may add proven candidates the declaration does not move (for example
`Key = {k1, k2, k3}` next to a declared `Permutations(TxId)`) and certifies the whole
combined product with one connected Lean certificate; the `Optimizations:` line then names
the enlarged group. A non-factorized declaration (a cyclic or custom subgroup), a product
above the certificate bounds, a candidate overlapping the declaration, a specification
outside the certificate subset (`ALIAS`, `_POSSIBLE`, `POSTCONDITION`, unsupported
operations), or a failed certificate keeps the declared group unchanged; the reason is
recorded under `-stats`. `-noautosymmetry` disables the enlargement. See
[reductions.md](reductions.md) section 2.6.

A declared `VIEW` does not by itself disable the group when it is a (possibly nested) tuple of
distinct state variables, including zero-arity variable-group definitions such as
`View == <<serverVars, logVars>>` (a group assigned a `.cfg` value is refused). In the default mode
a full-retention tuple is a bijection on states, so
the plain symmetry certificate covers it and the fingerprint stays TLC's `VIEW` of the least orbit
state; a tuple that omits variables composes certified unobserved-variable erasure with the orbit
quotient over the exact retained tuple, keyed by the orbit of the projected value. Computed or
duplicated views, views whose omitted variables a guard, update, bound, or check reads, and views
under a declared `SYMMETRY` keep their declared search; the refusal reason is recorded under
`-stats`. Certified state projections under `-optimize` still decline a declared `VIEW`.

Every default-mode run names applied optimizations (message code 9100 under `-tool`)
and records an `optimizations` array in JSON statistics. A certified symmetry is
labelled `certificate generated`, with `proof: "generated-lean"`, and its counts
are marked `symmetry-reduced`. With no certified automatic reduction, it reports
`Optimizations: none applicable.` and explores the full graph.

### 6.4. Certified state projections (`-optimize` and `tlx optimize`)

`tlx check Spec.tla -optimize [-proofdir DIR]` enables rule-based certified state projections for
safety and deadlock checking:

```sh
tlx check Spec.tla -optimize
tlx check Spec.tla -optimize -proofdir proofs/
```

- **Rules applied when certified**: unobserved-variable erasure, relative ages, finite histories,
  phase-dependent fields, sequence lengths, and scalar or fixed-nested ordered allocation with
  supported immutable-version collection. Concrete state values are retained for execution and
  counterexample traces; certified unobserved-variable erasure can compose with automatic keyed
  symmetry (including disjoint products of keyed groups).
- **Lean certificate output**: every `-optimize` run writes standalone `Optimization.lean` under
  `-proofdir` (default `$TLX_CACHE/proofs/<hash>/Optimization.lean` or
  `~/.cache/tlx/proofs/<hash>/Optimization.lean`, including a no-pass record when no rule applies)
  and prints its path without invoking Lean.
- **Scope and exclusions**: disabled by `-tlc` (regardless of argument order); skipped when the
  configuration uses constraints, action or initial properties, `ALIAS`, `_POSSIBLE`,
  `POSTCONDITION`, temporal properties, or declared `VIEW`/`SYMMETRY`; incompatible with simulation
  (`-simulate`, `-generate`), `-checksymmetry`, `-coverage`, and checkpoints or `-recover` (exit 2).

To export a standalone finite TLA+ abstraction without running model checking, use `tlx optimize`:

```sh
tlx optimize Spec.tla -output DIR [-config FILE] [-I DIR]...
```

This writes `Optimized.tla`, `Optimized.cfg`, `Optimization.lean`, and `optimization.txt` into a new
directory `DIR` (requiring `INIT`, `NEXT`, at least one `INVARIANT`, and `CHECK_DEADLOCK FALSE`);
supported fragments, rules, and trust boundaries are in [optimization.md](optimization.md).

---

## 7. Simulation and generation

```sh
tlx check Spec.tla -simulate num=100 -depth 50 -seed 42
tlx check Spec.tla -generate num=20 -depth 10
tlx check Spec.tla -simulate num=100 -workers 4
```

- `-simulate`: starting from a random initial state, each step picks one of all successors at
  random and the behavior is at most `-depth` (default 100) long. Invariants are checked in every
  state, temporal properties after every behavior.
- `-generate`: TLC's generate mode. Disjunctions, `\E`, `x' \in S` and similar inside an action
  are also tried in random order and the first feasible choice is taken, instead of enumerating
  all successors first.
- As in TLC, `num=N` is the number of behaviors **per worker** (4 workers and `num=2` give 8).
  Without `num=` the simulation runs until an error is found or it is interrupted.
- Without `-seed` a random seed is chosen and printed (`Running Random Simulation with seed ...`);
  with one worker the same seed reproduces a tlx run. The behavior selection uses tlx's own random
  number generator, so **the same seed does not give TLC's behaviors**
  ([compat.md](compat.md) D-2). `RandomElement` and friends are covered by D-4.
- In the compiled tier (the default) the simulation runs on the encoded model: the pre-run does a short BFS and then
  some random behaviors to see deeper states; after a layout miss the shape is widened and the
  whole simulation restarts from scratch with the same seed. `-generate -compile` uses compiled code
  for state encoding and invariants, while the interpreter still produces the random successors.
- The run ends with `The number of states generated: N` and `Simulation using seed S and aril 0`, as
  in TLC.
- `-dump` is silently ignored in simulation.

For reproducible simulations fix `-seed` and use `-workers 1`: behaviors, counterexamples and
statistics are then identical across runs. With several workers thread scheduling influences which
counterexample is reported first and the statistics (three runs with the same seed and 4 workers
gave three different generated counts).

### 7.1 Trace validation

Trace validation checks an implementation's log against a spec: the spec reads the log
(`JsonDeserialize`, `ndJsonDeserialize`), lets each step match the next log line, and accepts the
log if some behavior matches all of it. tlx runs the idioms of tlaplus/Examples' EWD998ChanTrace,
etcd's `Traceetcdraft` and CCF's traces with TLC's results:

```sh
JSON=trace.ndjson tlx check Traceetcdraft.tla
```

- The log is read once, when the constant definitions are evaluated at startup (as TLC), so
  `TLCEval(...)`, `SelectSeq`, folds and `VectorClocks!CausalOrder` over it cost nothing per state.
  `CausalOrder` orders concurrent log lines as TLC does with `-fp 0` ([compat.md](compat.md)
  D-25).
- The log position can be a variable or `TLCGet("level")` (in the VIEW, an ACTION_CONSTRAINT and
  temporal properties it is the level of the state they are evaluated on, the predecessor's in an
  action). `TLCGet("queue")` and the other statistics in a temporal property such as the usual
  `TraceMatched` have TLC's values: the liveness predicates are evaluated as TLC evaluates them
  during its search. `TLCExt!Trace` gives the path to the current state.
- In the compiled tier (the default; not `-interp`) the actions and the properties run natively with the log as a host value
  (a log of thousands of lines does not slow down compilation); expect a few layout restarts while
  the log position grows past what the pre-run saw. The specs `ASSUME` one worker.
- A cfg override of a definition (`InitServerVars <- TraceInitServerVars`) also applies inside the
  INSTANCEs of its module, but a direct reference `etcd!InitServerVars` still calls the original,
  as in TLC (D-23).

---

## 8. Checkpoint and recovery

As in TLC, once a run has lasted longer than `-checkpoint` minutes (default 30; `0` disables), tlx
writes the search state at the next BFS level boundary into the `checkpoint/` directory of the
metadir (`-metadir`; default `<spec directory>/states/<time>`) and prints

```
Checkpointing of run /path/to/states/26-10-05-12-00-00
Checkpointing completed at (2026-10-05 12:30:01)
```

Only the most recent checkpoint is kept (it is written to `checkpoint.tmp`, and replaces the old
one only after everything is written and flushed). It is deleted when the run ends normally and
kept when the process is killed (SIGKILL, power loss, crash) or interrupted by Ctrl-C / SIGTERM (the
latter prints `continue the run with -recover DIR` on stderr). Continue with the same command plus
`-recover DIR`:

```sh
tlx check Spec.tla -workers 8 -recover states/26-10-05-12-00-00
```

The continued run starts at the level of the checkpoint; verdict, generated and distinct counts,
depth and counterexample length equal those of an uninterrupted run (with one worker the
counterexample is identical too). `-workers` may differ from the original run. The tlx binary, the
spec and cfg (contents), the execution tier (interpreter or compiled), the mode (`-tlc` or not),
`-deadlock`, `-seed` and any automatic symmetry applied to the run must be the same, otherwise tlx
refuses and says which one differs (exit code 255).

Things to know:

- `Print` output and file writes such as `CSVWrite` after the checkpoint's level happen again in
  the continued run (including those the interrupted process had already done). TLCSet registers are
  restored from the checkpoint ([compat.md](compat.md) D-16).
- Checkpoints are taken only at level boundaries: if a level takes longer than the interval, the
  checkpoint waits for the end of the level.
- Size: about 24 bytes per distinct state (fingerprint plus trace log), plus the states of the
  current level (compressed in compiled mode), plus the edges of the liveness graph when liveness
  is checked.
- `-recover` cannot be combined with `-simulate`, `-generate` or `-dump`. `-optimize` (without
  `-tlc`) disables the default checkpoint interval and rejects explicit `-checkpoint` (`> 0`) and
  `-recover` (exit code 2).

---

## 9. Dumping states and traces, coverage

### 9.1 `-dump`

- `-dump states`: text format into `states.dump` (the extension is added automatically, as in
  TLC), one `State n:` paragraph per state.
- `-dump dot,actionlabels,colorize graph`: GraphViz format into `graph.dot`; `actionlabels`
  labels edges with action names, `colorize` colors by action. Node ids are tlx fingerprints
  (their values differ from TLC's).
- In the compiled tier the whole search is **run a second time** after the check to write the file (the
  compiled search may restart midway), which roughly doubles the time.
- `-dump` is silently ignored in simulation (`-simulate`, `-generate`).

### 9.2 `-dumpTrace`

As in TLC: when an invariant (including in an initial state), an action property, deadlock or a
temporal property is violated, the counterexample is written as TLC's `CounterExample` value
`[action |-> {...}, state |-> {...}]` (`state` is the set of `<<i, state record>>`; `action` is the
set of `<<<<i, s>>, action record, <<i+1, t>>>>`; an action record has `name`, `location`, and for
parameterized actions also `context` and `parameters`), and `"CounterExample written: file"` is
printed:

- `-dumpTrace json t.json`: `JsonSerialize(file, [counterexample |-> CounterExample, vars |-> set of variable names])`,
  byte-for-byte identical to TLC; missing parent directories are created.
- `-dumpTrace tla tt.tla`: a module `---- MODULE tt ----` (the file name up to the first `.tla`)
  defining `CounterExample == ...`, byte-for-byte identical to TLC.
- Nothing is written for evaluation errors or when nothing is violated (as in TLC); file names are
  relative to the current directory. The option can be repeated.
- The counterexample of a temporal property (a lasso) has one extra closing edge from the last
  state back to the first state of the cycle (`<<<<n, s>>, action, <<k, t>>>>`). If the cycle is
  a stuttering step the edge goes from the last state to itself with the action that led into the
  last state (`UnnamedAction` for an initial state), as in TLC. The file holds the lasso that tlx
  printed (which of several lassos is chosen is tier 3 and may differ from TLC's, see
  [compat.md](compat.md) D-1); the format is byte-for-byte TLC's.
- With `ALIAS`, the original states are written.

### 9.3 `-coverage`

The action-level statistics of TLC's `-coverage N`: every N minutes during the search (`0`: with
every progress report) and at the end (before the `N states generated` line) tlx prints

```
The coverage statistics at 2026-10-05 10:57:29 (see https://explain.tlapl.us/module-coverage-statistics for how to interpret the following statistics).
<Init line 6, col 1 to line 6, col 4 of module C1>: 2:2
<Inc line 7, col 1 to line 7, col 6 of module C1>: 6:24
<Both line 9, col 1 to line 9, col 4 of module C1 (12 12 14 20)>: 0:24
End of statistics.
```

- One line per action, `<name location>: distinct:generated`. `distinct` is the number of new
  states the action found **first** (constraint-satisfying; a state found by several actions
  counts for the first one in BFS order), `generated` is the number of successors it produced
  (including already seen ones and ones violating a constraint). When a definition is split into
  several disjuncts the location is followed by `(start-line start-col end-line end-col)`; the
  same action with different parameters (`\E i \in S : A(i)`) is merged into one line, sorted by
  location. Actions are split as TLC does ([tlc-semantics.md](tlc-semantics.md) section 5.1):
  definitions inside an `INSTANCE` with substitution are not split and the location is the
  `INSTANCE` statement (of several actions at the same location TLC reports only the first); an
  `\E` over the empty set is one `0:0` line; operators applied to actions (the argument is not
  a constant) are named after the operator; an action name that does not come from a definition
  is `Action`. The sum of `distinct` plus the number of initial states is the distinct total, and
  likewise for `generated`.
- The Init line is `generated:evaluated`: the number of generated initial states, and the
  assignments that were completed but then rejected by a later conjunct (TLC's way of counting). An
  initial predicate with several conjuncts gets several lines, the states are counted in the last.
- For a run without error the numbers equal TLC's (`-workers 1`) and do not depend on the execution
  tier or the number of workers (with several workers tlx picks representatives in BFS order;
  liveness is checked as usual on the behavior graph recorded during the search). When a violation
  stops the run the counts are those up to that point (TLC additionally counts evaluations made
  while reconstructing the trace).
- Only action lines: the number of values per variable and the lines for invariants, constraints
  and properties and the per-subexpression evaluation counts that TLC prints are not printed. With
  temporal properties TLC's liveness check generates the successors of some states a second time and
  counts them in `generated`; tlx counts only the search. See [compat.md](compat.md) D-12.
- Without `-coverage` there is no counting code in the search (it is a separate instantiation), so
  the cost is zero. With it each successor is counted twice (about +0.3% instructions for
  SimpleRegular with `-compile`; with several workers representatives are chosen in BFS order,
  about +4% at `-workers 4`). To count the `evaluated` of Init, every tier enumerates the initial
  states with the interpreter, so models with very many initial states become noticeably slower
  in the compiled tier (MCBakery has 655,200 initial states: CPU 1.0 s to 4.1 s; for comparison TLC's
  `-coverage` costs about 20-30% CPU on MCBakery).

---

## 10. Output and exit codes

### 10.1 Normal output

The output imitates TLC: the mode line, `Starting...`, the initial-state statistics, progress lines
`Progress(d) at ...`, errors starting with `Error:`, counterexamples as `State n: <action name location>`
followed by the state (or the `ALIAS` value), the final statistics (generated / distinct / left on
queue, search depth, average out-degree) and `Finished in ...`. Scripts that parse TLC's output
line by line usually work unchanged. Differences:

- The version line is `tlx version 0.1.2`; `fp 0` in the mode line is only a placeholder, `seed` is
  the seed actually used (0 for BFS without `-seed`).
- Compiled mode adds `compile:` lines ([section 5.2](#52-the-compile-log)).
- Parse and semantic errors carry the file name, as `file:line:col: message` (on stderr): a path
  relative to the current directory if the file is below it, otherwise the path where it was found
  (a `-I` directory, `<stdlib>/...` for standard modules); then `Error: Parsing or semantic analysis failed.`
- The fingerprint collision probability on success uses TLC's optimistic formula (tlx's fingerprint
  function differs from TLC's, so the number is informational only).
- The compatibility contract does not cover message texts, order and layout ([compat.md](compat.md)
  section 2).

### 10.2 `-tool` output

As in TLC's `-tool`, every message is wrapped in

```
@!@!@STARTMSG 2193:0 @!@!@
Model checking completed. No error has been found.
...
@!@!@ENDMSG 2193 @!@!@
```

The number is TLC's message number (`tlc2.output.EC`, e.g. 2110 invariant violated, 2114 deadlock,
2217 counterexample state); the class is 0 normal / 1 error / 3 warning / 4 state. Under `-tool`
durations are printed in milliseconds and messages such as `Starting SANY...` are added. The
output has not been verified with the TLA+ Toolbox or the VS Code extension.

### 10.3 Exit codes

Same as TLC (`EC.ExitStatus`):

| Exit code | Meaning |
|---|---|
| 0 | Success (also a successful simulation) |
| 1 | `-checksymmetry` found a symmetry witness, or `tlx parse` found syntax errors |
| 2 | Command-line error (tlx specific) |
| 10 | An `ASSUME` is false; the `POSTCONDITION` is false |
| 11 | Deadlock |
| 12 | An invariant is violated |
| 13 | A temporal property is violated (liveness), an action property is violated, a `PROPERTY` is violated by an initial state |
| 14 | `Assert` failed |
| 75 | Evaluation error (division by zero, overflow, out of domain, ...) |
| 76 | An invariant failed to evaluate, or is not a state predicate |
| 77 | A temporal `PROPERTY` is a tautology (or quantified over an empty set) |
| 150 | Parse or semantic error, spec or cfg file unreadable, cfg syntax error |
| 151 | Configuration error (for example an action-level formula used as a `PROPERTY`) |
| 255 | Other errors: system or resource limits (integer literal beyond 32 bits, no initial state satisfies Init and the constraints, fingerprint set full, disk budget exceeded, some errors during simulation, differing checkpoint on `-recover`) |
| 101 | Internal panic or invariant failure of tlx (including a mismatch found by `TLX_PARANOID`, or an internal symmetry proof/witness mismatch under `-checksymmetry -suggest`, the startup cross-check of automatic symmetry, or `TLX_SYMMETRY_PARANOID`): please report a bug |

The error class (and therefore the exit code) of a failing run is tier 3 of the compatibility
contract: tlx and TLC agree that it fails, not always on the code ([compat.md](compat.md) section 0).

---

## 11. Module search path and community modules

The modules of `EXTENDS` / `INSTANCE` are looked up in this order (the same order as TLC's
`SimpleFilenameToStream`: user directory, `-DTLA-Library`, the standard modules in the jar, then
the CommunityModules jar on the classpath):

1. the directory of the root module (the `.tla` given on the command line);
2. the directories given with `-I` (in the order given);
3. the directories in the environment variable `TLX_PATH` (`:`-separated);
4. tlx's built-in standard modules: Naturals, Integers, Reals, Sequences, FiniteSets, Bags, TLC,
   TLCExt, Randomization, Json, Toolbox, RealTime;
5. tlx's built-in CommunityModules (SequencesExt, FiniteSetsExt, Functions, Folds, Relation,
   Graphs, UndirectedGraphs, IOUtils, CSV, BagsExt, Bitwise, SVG, ... 34 files, taken from
   CommunityModules-deps.jar of 2026-09-12, MIT license, see `crates/tlx-sema/modules/community/LICENSE`);
6. the directories in `TLX_CLASSPATH` (`:`-separated), after all built-in modules, corresponding
   to TLC's Java classpath (which `SimpleFilenameToStream` consults last).

So, as in TLC, `EXTENDS SequencesExt` needs no option. To use another version of the community
modules (or to override a standard module) add its directory with `-I` or `TLX_PATH`; they come
before the built-in modules:

```sh
tlx check Spec.tla -I ~/src/CommunityModules/modules
export TLX_PATH=~/src/CommunityModules/modules:~/src/tlapm/library
```

Conversely, to add modules the built-ins lack without letting same-named files in that directory
shadow the built-ins (for example `third_party/tlapm/library` ships a `Bags.tla` without
`CopiesIn`), use `TLX_CLASSPATH`, which comes after the built-ins, like putting a directory on
TLC's classpath:

```sh
export TLX_CLASSPATH=~/src/tlapm/library:~/src/apalache
```

Whichever way a module is loaded, the operators TLC implements in Java are evaluated natively by
module name (parts of CSV, IOUtils, Json, Folds, FiniteSetsExt, Functions, SequencesExt, Graphs,
UndirectedGraphs, BagsExt, DyadicRationals, Statistics); the other operators are evaluated from
their TLA+ source, with the same semantics but possibly slower than TLC's Java implementation.
[features.md](features.md) has the operator-by-operator matrix.

---

## 12. TLC compatibility of options

TLC is the semantic oracle. The following agree with TLC and are covered by differential tests
(semantic details in [tlc-semantics.md](tlc-semantics.md)): the total order of values
and `CHOOSE`, 32-bit integers and overflow errors, type errors of equality, the enumeration
semantics and order of Init/Next, generated/distinct counts (including constraints and duplicate
successors), the deadlock decision, BFS depth and shortest counterexamples, `SYMMETRY`/`VIEW`,
`ALIAS`, `POSTCONDITION`, `TLCGet`/`TLCSet`, `Print`, `Assert`, and the verdict of liveness
checking (WF/SF).

Command-line options are not part of the compatibility contract, but tlx follows TLC's names:

| TLC option | In tlx |
|---|---|
| `-config`, `-workers`, `-deadlock`, `-depth`, `-seed`, `-simulate`, `-generate`, `-dump`, `-dumpTrace`, `-coverage`, `-tool`, `-nowarning`, `-fpmem`, `-fpbits`, `-maxSetSize`, `-checkpoint`, `-recover`, `-metadir`, `-h` | implemented with TLC's meaning (restrictions: `-simulate` has no `file=`; `-dump` has no `constrained`; `-dumpTrace` has only `json` and `tla`; `-coverage` is action-level only) |
| `-cleanup`, `-noGenerateSpecTE` | accepted, no effect |
| `-continue`, `-difftrace`, `-fp`, `-terse`, `-view`, `-userFile`, `-inv`, `-postCondition`, `-dfid`, `-lncheck`, `-debugger`, ... | not implemented; usage error, exit code 2 |
| `-DTLA-Library` | `-I dir` or `TLX_PATH` |

tlx-only options: `-I`, `-progress`, `-compile`, `-interp`, `-tlc`, `-optimize`, `-proofdir`,
`-noautosymmetry`, `-checksymmetry`, `-suggest`, `-symmetrystates`, `-symmetrydepth`,
`-symmetryperms`, `-symmetryedges`, `-maxmem`, `-spill`, `-maxdisk`, `-stats`. The
full matrix is [features.md](features.md) section 1; the contract, the intentional differences
(random numbers D-4, several workers D-3, liveness counterexamples under VIEW D-10, `-coverage`
D-12, checkpoints D-16, ...) and the known limitations (unimplemented options, real numbers and
temporal quantifiers, memory, wording of messages) are in [compat.md](compat.md).

---

## 13. Troubleshooting

**Should I use `-interp`?**
Rarely: the compiled tier (the default) is faster on all but tiny models, and on those it costs a
few milliseconds more (the pre-run, lowering and the JIT; the C build only starts after 1.5 s of
search, in the background, and later runs load it from the cache). `-interp` is useful to compare
results with the semantic reference, or when the compiled tier runs into layout misses on a model
whose state space is too small to be worth it.

**Many `layout miss` lines in compiled mode.**
The pre-run did not reach states deep enough, and the value range of a variable (a counter, a
sequence length, a set size) grew later. A few misses only cost a little time (usually the search
resumes without starting over). With many misses enlarge the pre-run:
`TLX_PRERUN=200000 TLX_PRERUN_MS=5000`; with enough memory also raise `TLX_RETAIN_MB` so large
models can resume instead of restarting. `TLX_COVERAGE=1` shows the shape before and after each
widening.

**Compiled mode is not much faster than the interpreter.**
Look at the `compile: layout ...` and `native code: a/n actions` lines: if not all actions are
native, or many nodes are boxed / interpreter nodes, part of the model still runs interpreted. Use

```sh
TLX_COVERAGE=1 TLX_CGEN_DEBUG=1 TLX_NATIVE_SYNC=1 tlx check Spec.tla -compile
```

to see which expressions are boxed and which actions are not native, and why. A narrow, deep state
graph also gains little from several workers.

**I suspect a compiled-mode result is wrong.**
First run the interpreter (`-interp`) and compare the counts. Then run
`TLX_PARANOID=1 tlx check Spec.tla -compile`, which cross-checks every successor against the
interpreter; on a mismatch it prints both results immediately and exits with 101. Please report the
output together with the spec.

**`native code disabled: ...` / `C build failed, keeping the JIT code: ...` (or `using the JIT code` with `TLX_NATIVE_SYNC=1`).**
Check that `cc --version` works, or set `CC=clang` (`no C compiler (cc not found)`: none was found
in `PATH`). The line shows the compiler's first error. Correctness is not affected; without C the
JIT code runs (slightly slower on long runs).

**`cannot find module Xxx`.**
The CommunityModules are built in ([section 11](#11-module-search-path-and-community-modules));
for other modules pass the directory with `-I` or `TLX_PATH`. A relative `-I` path is relative to
the current directory, not to the spec directory.

**`The fingerprint set is full; rerun with a larger -fpmem.` / `... cannot grow within the memory budget; rerun with a larger -maxmem.`**
The number of states exceeds the capacity of the fingerprint set (about 118,000 states per MiB).
With `-fpmem` the table has a fixed size and is full; the message gives the number of distinct
states reached and a suggested `-fpmem`. Without `-fpmem` (the default) this happens only with
`-spill off` (a larger table does not fit the budget and writing to disk is forbidden); the message
suggests a larger `-maxmem`. The default `-spill auto` writes the fingerprint set to disk instead.
Both are resource limits, not counterexamples of the spec, so no behavior is printed and the exit
code is 255 (not 75, the evaluation-error code).

**A broken pipe when output is piped into `head`.**
When standard output is closed early (broken pipe, `tlx check Spec.tla | head -3`), on Unix tlx
restores the default `SIGPIPE` disposition, so the process is killed by the signal and the shell
reports status 141 (128+13). On a platform without `SIGPIPE` the failed write panics and tlx exits
with 101. Either way this can be ignored; redirect to a file first if you need to truncate the
output.

**How do I get a reproducible simulation?**
Fix `-seed` and use `-workers 1` ([section 7](#7-simulation-and-generation)).
