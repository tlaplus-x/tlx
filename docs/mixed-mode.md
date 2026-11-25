# Mixed mode: native code with host regions

Mixed mode is the part of the compiled tier (`-compile`, see [design.md §6](design.md)) that lets a
native function (C or Cranelift JIT) call back into the host for the sub-expressions it cannot
compile. It is on by default (`TLX_MIXED`; the variables are documented in
[configuration.md](configuration.md)). Where it sits among the executors is described in
[design.md §6.6](design.md), the full native ABI in [design.md §6.7.](design.md)

Code: `tlx-compile` (`lower/regions.rs`, `cgen/region.rs`, `native_plan.rs`, `jit/`, `exec/fast/`,
`exec/memo.rs`, `enc/{mixed,adapt,region_eq}.rs`) and `tlx-native` (`tlx_abi.h`, `mixed.rs`,
`native.rs`).

## 1. Overview

Without mixed mode, one expression that the C generator cannot handle (a lazy function set, a
recursive set construction, a `Value`-level operator) sends the whole function back to the
interpreter. With it, only that sub-tree, a **region**, is evaluated by the host through the
callback `host->eval`; the rest of the function stays native. Boxed values (`Ty::Val`, see
[design.md §6.3](design.md)) cross into C as per-call arena handles.

Properties that make this safe and cheap:

- **Errors stay exact.** A region that fails makes the whole call return `TLX_ERR`; the host drops
  the buffered successors and the interpreter redoes that (state, action) or predicate. Which
  error is reported, and the evaluation order, therefore do not depend on mixed mode (§6).
- **Regions are small and never inside loops** (§4): the root is the smallest sub-tree C cannot
  compile, all-boxed sub-trees are merged into one interpreter call to keep its laziness, and a
  region inside an expression-level binding construct is hoisted out or the whole construct
  becomes one region.
- **Each state is decoded at most once**, and pure regions are **memoized** by their exact inputs
  (§8); memoization is where most of the gain comes from.
- **Adaptive tiering** (§7) compares each mixed function with the whole-function fallback at run
  time and drops it when it is slower.

### Replacing a host operation with native lowering

Add the specialization at the operation's lowering boundary, before region extraction.
Try the existing cheaper native representations first (word equality, rank masks,
structural membership); a more general specialization must not displace them. Reuse
the same helper at every matching expression site, including already lowered operands.
The native planner should accept the resulting ordinary IR without a model-specific
exception.

An integer set that fits in one bitset word retains its existing short-circuit
iteration against a constant interval. This is already fully native; replacing it
with a difference does not improve coverage, and a shorter generated instruction
sequence alone does not prove that the whole predicate or model runs faster.
Runtime right-hand sets, multiword sets and already lowered powersets without that
structural path still use comparable bitset difference.

The proof covers every value admitted by the operand shapes, not only values observed
in a pre-run. For example, comparable bitset sets satisfy `s \subseteq t` exactly when
`s \ t` is empty, after both sets use the same element encoding. This also handles
membership in a lowered powerset, including its enclosing filter. If the universes
cannot be proved comparable, retain semantic membership rather than silently comparing
bits. Construct operands at their original evaluation point: a finite filter may fail
even when the left set is empty, whereas a lazy powerset filter must retain its deferred
predicate and short circuit.

Finite atom universes offer another proof: tabulate the interpreter's exact result for
each encoded input. Entries are false, true, or failure; failure emits `Fail` so the
interpreter re-evaluates the original expression under the normal fallback contract
(§6). Membership tables use the original enumeration, including its deferred errors;
runtime bitset membership uses the whole normalized set mask, not an OR of element
equalities. Check the original atom universe before narrowing its encoding. Table
construction is bounded: constant membership/equality admits 256 atoms, constant
membership also admits at most 256 elements, and atom pairs or runtime set masks admit
at most 4096 entries. Larger products retain the host path.

Require differential tests against the interpreter for closure IR, generated C, and
JIT, with evidence that the intended native nodes execute. Cover successful values,
error-versus-value outcomes, deferred errors, skipped branches, different encodings,
table bounds and the retained cheap path. Successful interpreter cases must not merely
pass through a compiled bailout. Add a small TLC regression when a semantics defect is
found, then run the compiled paranoid suite and the affected fixed configurations.
Measure native evaluation share with `scripts/coverage.py` before and after; a zero
evaluation denominator stays unknown. Measure performance on the cloud with the
[benchmark protocol](benchmarking.md): identical models/modes/workers, an interleaved
baseline and candidate, discarded warmup and at least three complete repetitions,
including unaffected controls. Report coverage separately from time and preserve
incomplete runs as incomplete evidence.

Current corpus-wide native evaluation share and remaining host-region families are tracked in
[native-coverage.md](native-coverage.md) (reproduced with `scripts/coverage.py --dynamic`, see
[testing.md §10](testing.md#10-compiled-tier-coverage-scriptscoveragepy)). Accepted A/B timing
campaigns live in the canonical benchmark store and [generated report](performance.md).

## 2. ABI

The mixed-mode part of the ABI (v3 onward, now v5: `TLX_ABI_VERSION` in
`crates/tlx-native/src/tlx_abi.h`) consists of four `tlx_host` callbacks and two `tlx_spec_info`
fields (v5's value store callbacks are described in design.md §6.7):

| Item | Meaning |
|---|---|
| `eval(cx, rid, s0, s1, args, out)` | Evaluate region `rid` with current state `s0`, partial next state `s1` and arguments `args` (a `tlx_arg` union: scalar `i`, encoding pointer `w`, value handle `h`); write the result to `out`; returns `TLX_OK` or `TLX_ERR`. |
| `elems(cx, set, sorted, &first, &n)` | The elements of a boxed set handle as `n` consecutive handles starting at `first` (normalized order if `sorted`). |
| `mark(cx)` / `release(cx, mark)` | Handle watermark and release of the handles made after it. |
| `tlx_spec_info.n_regions`, `.regions_hash` | Number of host regions and a hash of the region table (0 when there are none). |

`tlx_info().regions_hash` must equal the hash of the region table the host rebuilt, otherwise the
library is not used (this protects a cached library against a region table from a different
lowering). The canonical printout of the region table is also written into the C source as a
comment, so the source hash, which is the build-cache key (§10), changes with the region contents.

Shape of a region call in generated C (a statement expression, like the rest of the generated code):

```c
/* Bool/Int result */
({ tlx_arg a_[2] = {{.w = t3}, {.h = t7}}; int64_t r_;
   if (h->eval(cx, 17, s0, s1, a_, (uint64_t *)&r_)) return TLX_ERR; r_; })
/* Enc result: written to a function-level buffer */
({ tlx_arg a_[1] = {{.i = t2}}; if (h->eval(cx, 18, s0, s1, a_, b5)) return TLX_ERR; (const uint64_t *)b5; })
/* iteration over a boxed set (ForEach / Repeat / quantifier) */
{ uint64_t f_, n_; if (h->elems(cx, S, sorted, &f_, &n_)) return TLX_ERR;
  for (uint64_t k_ = 0; k_ < n_; k_++) { uint64_t m_ = h->mark(cx); uint64_t t9 = f_ + k_;
    ...body...  h->release(cx, m_); } }
```

## 3. Value handles and memory

Each worker thread owns one `MixedCx` (`tlx-native/src/mixed.rs`): the value arena, the decoded
current state (`StateCache`), a panic caught inside a callback, and region-evaluation counters.

- **Lifetime.** A handle is valid only within one top-level call (`tlx_init`, `tlx_next`,
  `tlx_invariant`, `tlx_action_property`); the arena is emptied on return. A handle is
  `epoch << 32 | (index + 1)`; the epoch advances after every call and every `release`, and a
  handle whose epoch does not match its slot panics (a bug in generated code, not a TLA+ error).
  Handles never escape into the next state: an `Assign` of a region result has the variable's
  `Enc` result type, and `Emit` copies encoded words.
- **Idle capacity.** At call end, an oversized arena buffer is shrunk toward 2,048 slots.
  Explicitly clearing the state decode cache similarly shrinks its word buffer toward 2,048
  words. Smaller buffers retain their capacity for reuse; active calls and cached states may
  still grow beyond these retention targets.
- **Release in loops.** IR scopes are lexical, so a boxed value bound in a loop body does not
  outlive the iteration. C brackets loop bodies that contain region calls with `mark`/`release`,
  which bounds the arena by nesting depth times temporaries per level. The element handles of
  `elems` are allocated outside the loop.
- **No interning.** Arena values may be non-canonical or lazy (`LazyFcn`, `LazySet`, `Interval`),
  exactly as inside the interpreter; nothing is normalized unless the result is encoded. Only
  `Dyn` slots in states use the global, sharded `dynval` interner.
- **Threads.** A `MixedCx` is exclusive to its worker; callbacks only read the shared `Arc<Interp>`,
  typing and region table. No new locks.
- **State decode cache.** The explorer calls every action on a state and then checks invariants on
  its successors, so `StateCache` keeps the decoded most recent state (`Arc<[Value]>`). A hit is
  decided by comparing all encoded words of the state (not pointers or fingerprints: buffers are
  reused and fingerprints can collide). `s1` is decoded only for the assigned variables in the
  region's read set.
- **Panics.** A Rust panic inside a callback is caught (`guarded` in `tlx-native/src/native.rs`;
  it must not unwind through C frames), kept in the `MixedCx`, makes the callback return
  `TLX_ERR`, and is resumed by the host after the C call returns.

## 4. Region boundaries

Two steps decide where regions are.

**Lowering** (`lower/regions.rs`) applies two structural transformations on the IR: R3 (merge
all-boxed sub-trees) and R9 (no region in a loop). "Boxed" means `Ty::Val` and operators on it, the
same definition as the coverage report.

**Code generation** decides the final region roots (`cgen/region.rs`). It is the single source of
truth for "what C can compile", which also includes a few typed nodes C does not support (sorted
enumeration, bitsets of composite elements), instead of a separate analysis guessing at it:

```
expr_or_region(e, want):          // pseudocode; want = the C representation the call site needs
  match expr_native(e):           // cgen's expression generator, recursing through expr_or_region
    Ok(code) => code
    Err(_)   => region call for e (the whole sub-tree becomes a region)
```

`expr_native` fails on a node kind it does not support (`ValOp`, `Apply`, `Interp`, conversions
from/to `Val`, equality on `Val`, boxed `Choose`, ...) before looking at the children. A supported
parent therefore stays in C and its unsupported children become separate regions, and a
conversion (`Convert(Val -> Bool/Int/Enc)`) is always in the same region as the boxed sub-tree under
it, so the region returns the target representation directly.

| Rule | Content |
|---|---|
| Inputs | Free IR temporaries (`lower::free_temps`) in order of first occurrence become `args`, typed from the function's `temps` (Bool/Int in `.i`, Enc in `.w`, Val in `.h`). State reads (`Var`, `NextVar`, `Interp`) go through `s0`/`s1`, resolved on the host. |
| Context | The region table records the call-site context: Init (`s0 = NULL`), action (plus the statically known set of assigned variables, tracked by cgen along the statements; cleared on entering `ENABLED`), state predicate (`s0` only), transition predicate (`s0` and fully assigned `s1`). A region inside `ENABLED` sees `ENABLED`'s local `s1`. |
| R3: do not split lazy structure | If all nodes of a boxed sub-tree are boxed and it contains an interpreter fallback, one `Interp` of the HIR sub-expression replaces the IR composition (`Apply(Interp(f), x)` becomes `Interp(f[x])`), so the interpreter evaluates and memoizes recursive functions lazily as TLC does (`regions_post`). |
| Purity | A region and the definitions it uses must not contain volatile or side-effecting builtins (`Print`, `TLCSet`, `TLCGet` except `"level"`, `Random*`, `IOExec`, `CSVWrite`, ...; `ir_volatile`). Otherwise the function is not mixed and falls back as a whole, because a fallback re-runs and would repeat the effect. Exception: output (`Print`/`PrintT`, `Builtin::is_output`) in an action (not Init or a predicate): the action is mixed (`RegionOracle::mixes_next`), the host holds the lines its regions print back until the native run succeeds (`Interp::hold_begin`/`hold_end` in `EncModel::compiled_successors_printing`) and drops them when the interpreter redoes the run, and a printing region is never memoized (`RegionInfo::pure`). `TLX_PARANOID` compares the lines with the interpreter's. |
| Statements | `Guard` (condition region giving Bool), `Let` (Val temp from a handle), `Assign` (value region with the variable's `Enc` result type; the host normalizes and encodes into the `s1` slot, a value outside the shape is `TLX_ERR` and the interpreter path records the layout miss). Quantifiers, `CHOOSE`, filters and maps over a boxed set are one region as a whole. `ForEach`/`Repeat` are statements (their body has `Emit`), loop in C and fetch element handles with `elems`. |
| LET temps, by-name arguments | LET values, by-name argument thunks, LAMBDAs and operator references are IR temps or `Interp.deferred` by lowering; the HIR closures in `deferred` only reference `binds` (IR expressions) and the constant environment and travel with the region. |
| Predicates | With regions a predicate is always native as long as lowering succeeded. |
| Table | No limit on region ids. Regions are stored per function; structurally identical regions (one HIR sub-tree duplicated by CPS expansion) share one `Arc<Expr>`. |
| R9: no callback in a loop | If a binding construct at expression level (`\E`, `\A`, `CHOOSE`, filter, set map, function constructor, fold) contains a region in its body: (1) a region that does not depend on the bound variables (no body-bound temps, no body-assigned `s1`) is hoisted before the construct (`hoist_stmt`, `hoist_pred`; regions are pure, so hoisting can at most evaluate once too often, and only when the source is non-empty); (2) otherwise the whole construct becomes one `Interp`. Exception: in a construct that reads the next state, a pure iteration source that reads only the current state is first bound as its own region (memoized by its inputs) and the construct is not widened (`split_memoizable`). A region that is itself a whole iteration — an `Interp` an inner widening produced from a loop, or the loop's own `Interp` under its conversion (`iteration`) — is not the element's work of an enclosing construct: widening it too would fold a tower of native loops into one host call and discard the enclosing iteration (`lower/regions.rs`; hoisting treats a nested loop the same way). Statement-level `ForEach`/`Repeat` (also inside `ENABLED`) cannot be widened because their body has `Emit`; element-dependent regions stay in the body and adaptive tiering (§7) decides whether the function pays off. Init is the exception: it runs once, so there is nothing to adapt to and such an Init is not mixed (`loop_region` in `cgen`). |

## 5. Host callbacks in the closure executor

`eval` is implemented by `HostRegions` (`enc/mixed.rs`, implementing `tlx_native::mixed::Regions`):

1. Look up `rid` in the region table. A region is compiled to a closure program
   (`exec::fast::ExprProg`) on first use (one `OnceLock` per region) and reused.
2. Write `args` into the program frame by the region's input types: `Int`/`Bool` directly, `Enc`
   by reading the encoded words, `Val` from the arena.
3. `s0` comes from the state decode cache; `s1` borrows the caller's buffer and only the assigned
   variables of the read set are decoded.
4. Evaluate (`exec::fast::eval_region`) and write `out` by result type: `Val` becomes an arena
   handle, `Enc` is normalized and encoded, scalars go to `out[0]`. Pure regions first consult the
   memo table (§8).
5. An evaluation error is counted and returns `TLX_ERR` (no message is needed, the interpreter
   reports it again); a panic is caught and also returns `TLX_ERR`. A region the closure compiler
   does not cover returns an error too and the interpreter redoes the call.

## 6. Errors and fallback

- **Invariant.** For one (state, action), mixed native code either produces the same multiset of
  successors as the interpreter or returns `TLX_ERR`/`TLX_MISS` so that the interpreter redoes it.
  A failing region returns `TLX_ERR`, the host discards the buffer, and the interpreter reports
  TLC's exact error (kind, message, location, `-tool` code, and the count of states generated
  before the error). The evaluation order and which error is reported need not be reproduced in C
  or in the callbacks.
- **Must not succeed where the interpreter fails.** C may not skip a sub-expression TLC would
  evaluate and fail on. Mixed mode adds no short-circuiting or laziness (region internals are
  interpreter semantics and R3 moves laziness closer to the interpreter), so the risk equals that
  of typed code and is covered by `TLX_PARANOID` ("interpreter fails but compiled code has a
  result" counts as a mismatch).
- `Assert(FALSE, msg)` in a region is an error and therefore a fallback; the interpreter prints
  TLC's Assert message once (callbacks never print).
- A region result that must be encoded into an intermediate `Enc` shape (not a state variable)
  and does not fit is also `TLX_ERR` and does not trigger widening; if this happens often, the
  cost of the failed calls is part of the mixed path's time in adaptive tiering.
- Init: a failing region in `tlx_init` makes the interpreter redo Init as a whole. Liveness atoms,
  ACTION_CONSTRAINT and VIEW behave like predicates: a negative return falls back.

### Relation to the other tiers

| Tier | Used when |
|---|---|
| Native (incl. mixed) | the function is lowered, the native library is loaded and the function is native; mixed functions are additionally selected by adaptive tiering |
| Closure IR executor | the native library is not ready yet (background C build under `TLX_JIT=0`), `TLX_NO_NATIVE`, or the function is not native; an action runs on IR only if it contains no interpreter-fallback node (`EncModel::exec_ok`: going in and out of the interpreter per node is slower than interpreting the whole action), Init only if it evaluates no side-effecting builtin |
| Interpreter | not lowered, impure, native or IR run failed, or adaptive tiering found the fallback faster |

## 7. Adaptive tiering (`enc/adapt.rs`)

A mixed function (native and calling regions; `NativeSet::mixed_init`, `mixed_actions`,
`mixed_invariants`, `mixed_action_properties`) is not always faster than the fallback: a region may
convert a large value on every call or do almost all of the work. Each worker thread alternates the
two paths per mixed function: in the sampling phase consecutive calls take the mixed native path
and the fallback (IR executor or interpreter), `SAMPLES` = 32 each. The timing excludes the
explorer's successor processing (`out` callback); an interpreter redo after a failure is charged
to the mixed path.

- **Decision.** Drop the largest eighth of each path's samples (calls preempted under load), take
  the means, and choose native only if mixed <= `MARGIN` (0.95) x fallback. The chosen path then
  runs `RUN_FIRST` = 1024 calls before re-sampling; if the choice is unchanged the period grows
  x4 up to `RUN_MAX` = 65536, if it changes it returns to 1024.
- **Warm-up.** With region memoization, every function first runs native `WARM` = 4096 calls
  before sampling: the memo table is cold at start, so early sampling would pick the fallback, and
  on the fallback the table never warms up.
- State is per worker thread and per function (`thread_local`, reset per model and library), with
  no shared counters. When the native library is replaced (C library replaces the JIT library) all
  functions are sampled again; nothing is sampled while the library is still loading.
- Purely native functions pay one bit-vector lookup. Tiering is off under `TLX_MIXED_FORCE` (test
  mode needs the region path to run always) and with `TLX_MIXED_ADAPT=0`.
- It only affects performance, never results, so workers need not agree. `-stats` shows a `mixed`
  column, per mixed function the region evaluations/failures and per-call time of each path, and a
  list of regions sorted by cumulative time (memo hits included).

## 8. Region memoization (`exec/memo.rs`)

The result of a pure region depends only on its inputs (`args` plus the state variables it
reads). The key is the region plus the **exact encoding** of its inputs (encoded inputs: the
words; scalars: tag and value; boxed inputs: a structural encoding; a lazy value as input is not
memoized), plus the encoded words of the current-state variables the region may read. There are
no fingerprints, hence no collisions, and a hit needs no decoding.

- **Read set.** `Var`/`NextVar` in the region plus state variables reachable from the HIR of
  `Interp` nodes through definitions, constant substitution, by-name arguments and operator
  parameters, and from the bodies of the compiled functions it calls (`Call`, e.g. a RECURSIVE
  operator whose function is not native: the call's arguments need not mention the state it
  reads; a function still being compiled makes the read set unknown).
  `Lowerer::expression_summary` (`tlx-compile/src/lower/summary.rs`, with HIR fallback walking in
  `tlx-compile/src/lower/summary_hir.rs`) computes fixed-point summaries across `Call` edges, and
  `summary::scan` matches every `ir::ExprKind` variant explicitly so a new kind that evaluates code
  kept elsewhere must be handled. Purity is as in §4 (primed variables, `UNCHANGED`, `ENABLED`,
  temporal operators and cfg-overridden builtins are also excluded).
- **Table.** One direct-mapped table per thread (a collision replaces the older entry), starting
  at 1024 slots and doubling when over half full up to `TLX_MEMO_SLOTS`. The byte budget is the
  thread's share of `TLX_MEMO_MB`, further capped by the memory budget's cache allowance
  (`tlx_runtime::cache_mem`); exceeding it clears the table.
- **Per-node switch.** After a probation of `PROBATION` = 4096 lookups a node stops memoizing if its
  hit rate is below 20% or its misses average under 3 µs. The decision is per thread, and a later
  probation can reverse it: after 65536 skipped calls (4 times as many after each further
  probation). With several workers a thread's first lookups come from its share of the small early
  levels on a cold table, which disabled 99%-hit regions on some workers of MCMongoReplReconfig.
- **Errors are not memoized** (a failing region falls back as usual). TLC does not memoize, but a
  pure expression's value does not depend on how often it is evaluated.
- Memoization is on whenever mixed mode is. The IR executor's own non-region runs do not memoize
  `Interp` nodes. `TLX_MEMO_STATS` with `-stats` reports lookups, hits and estimated savings per node.
- **Sharing across regions** (`enc/region_eq.rs`). Memo nodes are allocated per computation, not
  per region. Two memoizable regions share the first one's node if their key layouts agree (input
  representation, read set, whether they read the current state, whether they are inside `ENABLED`;
  for next-state readers also the same context and assigned variables), their expressions are
  equal under a type-preserving renaming of temps, and their `Interp` is the same HIR node with
  equal environment bindings (`Env::same_bindings`). A pure region yields the same value for the
  same key at every call site and errors are not memoized, so sharing never changes results. The
  classification runs once, at the first memo lookup; `-stats` marks shared nodes `memo of region N`.
  It matters when the same expensive pure call occurs in an action and in a liveness transition
  predicate (about 20% fewer instructions on such a model); elsewhere the shared regions were cheap.

## 9. PARANOID and tests

- Mixed native code is "native": the `TLX_PARANOID` comparison of successor multisets, of invariant
  and action-property verdicts, and the Init cross-check cover it automatically.
- **Forced regions.** `TLX_MIXED_FORCE=k` (testing) makes every k-th otherwise compilable
  expression a region too, so the ABI, argument marshalling, arena and contexts (Init, `ENABLED`,
  primed, predicates) are exercised on specs that are fully native. Run it with the existing
  difftests/spectests plus `TLX_PARANOID`; it is the main ABI correctness test.
- `TLX_MIXED=0` switches mixed mode off (whole-function fallback), for comparison and bisection.
- Tests: region partitioning and R3/R9 (`tlx-compile/tests/regions.rs`, `mixed_regions.rs`), mixed C
  generation (`mixed_cgen.rs`), region evaluation (`exec_region.rs`), memo table (`exec_memo.rs`),
  mixed mode in the JIT (`jit_mixed.rs`); host-side handles and epochs (unit tests in
  `tlx-native/src/mixed.rs`), rejection of a library on ABI-version or region-table-hash mismatch
  (`tlx-native/tests/mixed.rs`).
- Sanitizers: `TLX_CC_SANITIZE=1` (ASan + UBSan, see [unsafe-audit.md](unsafe-audit.md)) on
  spectests with regions. The expression fuzzer (`scripts/fuzz_expr.py`) covers the region path
  under `-compile`.

## 10. Code generation and cache

- Region ids are assigned in a deterministic order during the cgen traversal. The region table is
  returned with the `cgen::Library` and held by the native handle; the JIT library uses the same
  table (`native_plan.rs`: the C generator is the reference backend and the JIT consumes its plan,
  `RegionCursor` checks that each region is called exactly once; see [design.md §6.6](design.md)).
- The cache key (source hash) covers the C side. The canonical region-table printout in the source
  comment makes host-side region changes change the key, and `regions_hash` is checked again at
  load time.
- With an `-O0` first / `-O2` replacement build (large sources under `TLX_JIT=0`), both libraries
  share one region table (one cgen run).
- A layout-miss widening restart lowers again and regenerates region table and library.

## 11. Performance model

The cost of one (state, action) in the mixed version is about

```
T_native(typed part) + sum over region calls [ ~5 ns call + argument marshalling
                     + region evaluation (or memo hit) + result encoding ]
                     + one decode of s0 per state (shared across actions)
```

The whole-function fallback costs: decode of the whole state, interpreting the whole action,
encoding every successor. Mixed mode loses when a region is called repeatedly in a loop or is
almost the whole function; R9 and adaptive tiering cover those cases. The remaining boxed nodes
and their causes are listed in [design.md §6.8.](design.md)
