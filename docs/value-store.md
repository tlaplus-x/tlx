# The value store (`Ref` slots)

This page is the contract of the compiled tier's **value store**: the representation a `Ref` slot
holds, the identity of its handles, the operation set the executors share, what owns a handle, and
the limits of the experiment. [configuration.md](configuration.md) owns the
`TLX_VALUE_STORE` switch and its default, [compat.md](compat.md) owns what a run promises a user, and
[design.md](design.md) puts the store next to the four other value representations (sections 2.3
and 6.7). The store is **experimental**: with `TLX_VALUE_STORE=1` the slots whose shape has a `Dyn`
part hold handles into it, and with the switch off nothing on this page applies to a run.

The design record of where the store is going — stable state root slots, complete collection
lowering, reclamation, spill and a checkpoint format, with the measurements that ranked those steps —
is not current documentation. [README.md](README.md) names the pinned revision that holds it.

## 1. What the store is

One **run** owns one store (`tlx_layout::store::Store`). A node holds the exact representation of a
finite value: its kind and, for a function, how TLC built it — tuple, record, function over an
enumerated domain, or function over an interval (a *witness*, `tlx_value::plan::Witness`) — with its
children as handles. The kinds are `Body::Int`, `Set`, `Interval`, `Tuple`, `Record` and
`Fcn(_, FcnDom)`, and the interval/enumerated distinction is part of the kind, not a side table
(`crates/tlx-layout/src/store/mod.rs`). A set's elements and a function's keys are in TLC order and a
sequence is a tuple node; every node is flat, of any size, and an operation that grows a value
(`Append`) publishes a new node instead of changing one.

`freeze` normalizes a lazy set or lazy function first and refuses a value that is not finite
(`StoreError::NotFinite`); `thaw` returns exactly the value that was frozen, and `thaw_slot` maps the
all-zero word of an unassigned slot to `FALSE`.

A slot holds a `Ref` **handle**: a `u64` that is either an immediate scalar — strings and model
values by `Sym` id, Booleans, and integers of at most 61 bits — or a reference to a node of the run's
store. The immediate schema is declared once in `crates/tlx-layout/src/scalar.rs` and re-exported by the
store, so the store, the `Dyn` interner and the C and JIT backends derive their tags from one owner
(ARCH-07). A node handle carries the store's 16-bit id and the node's index; store ids are allocated
from a process-global counter and are never reused, so a handle of another store is refused by the
checked lookups rather than read as this store's node. Nodes live in a two-level radix page table
(256 nodes per page, 4,096 pages per directory with an inline first directory covering the first
1,048,576 nodes, and 16,384 directories — up to 2^34 handles) behind a readers-writer lock
(`StorePin<'_>` via re-entrant read locks during normal execution, exclusive write lock only during
safepoint reclamation). Sealed pages with at most half their slots live compact to sparse sorted
arrays (`Page::Sparse`), and sealed overflow directories with at most 1/8 of their pages live
compact to `Dir::Sparse`, keeping retained backing storage proportional to survivors and charged
against the byte budget.

## 2. Identity: interning, witnesses and the digest

### 2.1 Interning by exact representation

Two handles are equal iff they denote the same representation: kind, witness and child handles.
Equal values with different witnesses therefore get different handles — the interval `2..4` and the
set `{2, 3, 4}` are one value to TLC's equality and two handles here — and `<<1, 2>>` and
`[i \in {1, 2} |-> i]` likewise. This is what makes compat.md's D-13 inapplicable to `Ref` slots: how
a function was built survives in the handle, so EXCEPT at a model-value key behaves as the
interpreter does, not as the fixed encodings do.

`freeze` computes an exact hash of the representation, looks in one of the store's 64 index shards,
and returns the existing handle when a structurally equal body is there; only if not does it append a
node and publish it. Hash collisions are settled by the structural comparison, never by the hash.

Interning takes a short lock on one shard under a shared `StorePin<'_>`. Published nodes never
change or move while live, so concurrent readers share the pin with no per-node locking; a node
slot written twice is an assertion failure rather than a silent replacement. Only safepoint
reclamation (section 6) takes the exclusive write lock to sweep dead slots and drop empty pages.

### 2.2 The semantic digest

Every node caches a 64-bit **semantic digest** computed from its children's digests. The digest is
the same for all values TLC considers equal — the tuple / record / function aliases of
`tlx_value::Value`'s equality — and it does not depend on handle numbers, allocation order, the
interning thread or the store instance. State fingerprints substitute digests for handle words, and
the symmetry orbit comparison does the same, so a state's fingerprint is independent of the store's
internal numbering.

A digest is a **filter**, never a decision: equality is settled structurally, by thawing and
comparing. A digest collision is not evidence of equality.

## 3. Slots

With `TLX_VALUE_STORE=1`, a variable whose speculated shape would have a `Dyn` part holds a `Ref`
slot, and so does such a component of a tuple VIEW. `TLX_VALUE_STORE=all` makes every slot a `Ref`
slot; it exists for tests, not as a configuration to run a model with. A run whose slots all have
fixed shapes has no `Ref` slot and stores nothing. Both are
`Shape::Ref(store id)`: the shape compares and hashes by the store's identity and prints without it,
so generated code never depends on a store's contents.

One run has exactly one store: all `Ref` shapes of a run compare equal, and `tlx_layout::layout::store_of`
reports the one store of a layout. A `Ref` also has to sit at a fixed position — a handle inside a
set, sequence, map or union arm is refused, so the layouts never build such a shape.

## 4. Operations

### 4.1 One table, three executors

`ir::ExprKind::RefOp` names every store operation of a verified program.
`crates/tlx-compile/src/exec/refops.rs` is their single implementation: the closure executor calls it
directly, and native code reaches it through the ABI v5 callbacks `ref_op` and `ref_elems`
(design.md section 6.7), which come back to the same function. Each operation is the store method of the same
name, so all executors compute the same handles and fail in the same cases.

The table numbers every distinct (operation, arity) of the program in a fixed traversal, so C, the
JIT and the host agree on the ids. Its canonical text is written into the generated C source (so it is
part of the native cache key) and its hash into `tlx_spec_info`, which the host compares on load
against its own table; a mismatch refuses the library. A failing operation — a TLC error, a case the
store leaves to the interpreter (`RefOpError::Eval`), or a full store — fails the whole call and the
interpreter redoes it. It never yields a handle that would change a result.

C inlines the scalar conversions and part of equality; every other operation is a `ref_op` call.
An operation inside a *compiled function*, an operation with a boxed argument and a boxed operation
result are all refused by the code generator, and such a subtree keeps the boxed path.

### 4.2 The operation set

| Operation (`ir::RefOp`) | What it computes |
|---|---|
| `Domain` | the domain of a stored function, in TLC's normalized order |
| `Apply` | application of a stored function to a key |
| `Select` | the position of a key in a stored function's domain (the lookup schedule of `tlx_value::plan`), or `-1` when it is absent |
| `ValueAt`, `SetAt` | the read and the write step of EXCEPT, in the interpreter's order: all keys are evaluated first, and an absent key leaves the function unchanged without evaluating the replacement |
| `Single`, `Merge` | `:>` and `@@` (left-biased on duplicate domains) |
| `Member`, `InDomain` | `\in` and `\in DOMAIN` |
| `Eq` | TLA+ equality between two stored values |
| `Field`, `Tuple`, `Record` | field access, and tuple and record construction |
| `Cardinality`, `Len`, `Append`, `Head`, `Tail` | the collection operations of FiniteSets and Sequences |
| `FromInt`, `FromBool`, `ToInt`, `ToBool` | immediate scalar conversion |
| `FromEnc`, `ToEnc` | conversion between a fixed encoding and a handle — the boundary between the two representations |

Iteration over a stored collection is `ref_elems` (the elements of a stored value, as borrowed words)
rather than a `RefOp` variant.

### 4.3 What still goes through the host

An operation the store does not have, or an operand that is boxed, converts to the boxed value and
runs in the existing host regions; `Dyn` remains exactly as that boundary. The store is a
representation, not a replacement for the evaluator: a value leaves it, is computed on, and is frozen
again.

## 5. Fingerprints, VIEW, SYMMETRY and the paranoid check

State fingerprints, VIEW fingerprints and the symmetry orbit comparison use digests in place of
handles, so a stored run keeps TLC's semantics under a reduction. A SYMMETRY permutation has a plan
for stored values: it thaws the value, permutes it and freezes the image, memoized per handle; a full
store keeps the old handle and the run stops on it.

Under `TLX_PARANOID` the compiled tier also checks that every `Ref` slot holds exactly the
interpreter's value, representation included (design.md section 6.5.5). `-stats` reports the store's nodes,
payload bytes, index estimate, budget and the operation counts per executor.

## 6. Ownership, lifetime and memory

The store belongs to a run. It is created when the encoding is built, with the run's full memory
budget (`-maxmem`, or `mem::default_budget()` when `-maxmem` is not set; unlimited when the run has
no memory budget, `Settings::value_store_bytes` in `crates/tlx-compile/src/settings.rs`).

The store is not a process-wide interner, so two runs in one process have two stores even when they
share one cached native library: the library calls back into the store of its per-call context, not
into one of its own (`tlx-compile/tests/value_store_runs.rs`).

### 6.1 Safepoint live-root reclamation

The store reclaims unreachable nodes via **stop-the-world safepoint mark-and-sweep**
(`Store::collect_with` in `crates/tlx-layout/src/store/mod.rs`, `StoreGc` in
`crates/tlx-runtime/src/model.rs`, and `SP_STORE_GC` in `crates/tlx-runtime/src/explore/`):

- **Budget & triggers.** Insertion charges the node struct plus payload bytes (and retained page and
  overflow directory backing storage after sweep/restore) against the budget (the index is counted
  separately for reporting). Crossing the **soft limit** (75% of budget) sets `gc_requested`, which
  the pressure monitor (`relieve`) and level boundaries observe to request a proactive `SP_STORE_GC`
  safepoint. Hitting the hard budget returns `StoreError::Full` (`ErrorKind::StoreFull`), which
  parks workers at a mid-level `SP_STORE_GC` safepoint and retries cleanly. Successors are finished
  and delivered one at a time in order via `Model::action_successors_gc` / `Model::init_states_gc`,
  holding captured `PrintT` output until fingerprinting succeeds so GC retries never duplicate
  printed lines or interpreter effects (`Print`, `TLCSet`, files) and never change first-failure
  order. If a single compiled action, predicate, or `VIEW` expression still overflows an
  archive-free store due to discarded transient intermediates, the retry falls back to the
  interpreter (which evaluates intermediates without interning discarded values).
- **Root enumeration.** At `SP_STORE_GC`, all active workers are parked with their local queue
  readers/writers, archives, VIEW/SYMMETRY candidate stores, in-flight states, and pending emit
  handles deposited into `Shared::gc_roots`. The safepoint executor enumerates every live root:
  current and next frontier queues (in-memory and spilled segments), worker local buffers,
  VIEW/SYMMETRY candidate stores, the layout-miss resume archive (phase 1), in-flight/pending
  states, and compile-time constant `Ref` handles pinned in `EncModel::pinned_handles`.
- **Two-phase archive policy.** Both initialization and worker safepoints share one archive-drop
  decision: proactive collections keep the layout-miss resume archive rooted up to 3/4 of budget so
  layout-miss resume remains available whenever live frontier + archive fit; persistent hard
  allocation retries force an archive-free collection before latching exhaustion, even when
  post-sweep occupancy fell below 3/4.
- **Sweep, page compaction & caches.** Mark traversal runs an iterative DFS over child handles using
  per-page bitmaps. Sweep removes unmarked entries from the 64 intern shards (shrinking excess
  shard capacity), clears dead slots, frees empty pages and overflow directories, compacts sealed
  sparse pages/directories, charges exact retained backing storage against the budget, resets
  derived `domain`/`elems` caches on surviving nodes, and increments `Store::gc_gen`. Thread-local
  memo tables (`exec/memo.rs`), decoded/mixed value caches (`enc/model.rs`), and symmetry
  permutation memos (`permute.rs`) key on `gc_gen` and drop stale entries automatically.
- **Liveness edges, concrete liveness & counterexample replay.** Recoverable `StoreFull` errors
  during liveness atom evaluation (`EdgeRec`) return to a unified worker retry path without clearing
  the recorded graph; only exhausted retries fail the recorder and stop the search. Multi-predicate
  checks (`check_invariants_gc`, `constraint_gc`, `action_constraint_gc`, `check_transition_gc`)
  retry only the failing predicate so earlier predicates' committed side effects (`TLCSet`, `PrintT`)
  are preserved. Pre-resume edge reconstruction (`resume.rs::record_archived`), liveness lasso
  counterexample replay (`liveness/recorded.rs`), concrete liveness BFS and counterexample rebuilding
  under `VIEW`/`SYMMETRY` (`liveness/concrete.rs`), early temporal checking inside `find_error`
  (`liveness/search.rs`), and safety/terminal-error trace reconstruction (`tracelog.rs`, whenever
  `Effects::resumes` declines a `ResumePoint`) all run with `StoreGc` reclamation so deep traces and
  temporal checks stay within `-maxmem`. Constraint-rejected candidates release their store handles
  immediately (staging store-free `Arc<[Value]>` snapshots via `AtomBits::stage_state` only when the
  spec has action atoms), and `Early` reuses the worker's filtered successor batch and safepoint GC
  hook rather than re-expanding actions outside GC. Before running a secondary liveness-error search
  (`find_error`) or `-dump` search on the same model, the CLI decodes any retained safety/error trace
  into owned values so collections in the secondary search cannot sweep handles still needed for
  rendering.
  Optional layout-miss archive migration (`enc/driver.rs::migrate`) runs inside a GC scope so a
  transient budget hit falls back to a fresh restart after sweeping dead nodes instead of latching
  permanent store exhaustion.
- **Hard stop when live roots exceed `-maxmem`.** If live reachable roots genuinely exceed the
  budget even after collection (and archive drop), the search stops cleanly with an error naming
  the budget and the way out (`raise -maxmem or turn the store off (TLX_VALUE_STORE=0)`,
  `enc/driver.rs::check_store`), and `Checkpointed::keep_checkpoint` preserves the last committed
  checkpoint on disk for `-recover` with a larger `-maxmem`. `-stats` reports `gc_cycles`,
  `reclaimed_nodes`, and `reclaimed_bytes` alongside live node counts and payload bytes.

## 7. Checkpoint and recovery

Stored runs support both TLC's default 30-minute checkpoint interval and explicit `-checkpoint` /
`-recover` (`crates/tlx-layout/src/store/ser.rs`, `crates/tlx-compile/src/enc/driver.rs`).

- **`model-store` (format v2, sparse ascending delta):** `Checkpointed::files` writes a framed
  `model-store` file alongside `model-strings`, `model-shapes`, and `model-dyn`. Because safepoint
  reclamation leaves swept holes in the monotonic handle space, format v2 persists the store's
  `next` high-water mark, `live_count`, and only live nodes as `(delta, kind, body)` records in
  ascending index order, preserving every `Body` kind and `FcnDom` witness while encoding node
  references as 0-based indices (`< idx`, acyclic by construction) and symbols by `Sym` id
  (resolved after `model-strings` restore).
- **Store-id-neutral queue and archive words:** on checkpoint write, `StateCodec::checkpoint_words`
  strips the 16-bit `store_id` bits (`-> 0`) of `TAG_NODE` handles in `Ref` slots without adding
  overhead to in-run `StateCodec::encode`. Keeping on-disk state words store-id-neutral preserves
  incremental `archive-*` segment hard-linking across repeated recoveries.
- **Process-safe recovery:** `model-shapes` (`SPECULATION_VERSION = 4`) records the run's store mode
  (`TLX_VALUE_STORE=0` / `1` / `all`), and recovery refuses mode mismatches (including recovering a
  stored checkpoint under `TLX_VALUE_STORE=0` or `TLX_ESCAPE=1`, or vice versa) before loading
  tables. `Store::read_snapshot` always allocates a fresh process-unique `uid` from `NEXT_UID`,
  recomputes semantic digests, rebuilds the shard intern index at the exact original sparse indices
  (compacting finished sealed pages and overflow directories as restore progresses), restores
  `next`, enforces `-maxmem` against retained backing storage, and rejects corrupt/truncated
  payloads, forward/cyclic/out-of-range/swept-hole node references, malformed or duplicate bodies,
  and unpublished `Sym` ids (`Sym::try_from_id`). `StateCodec::recover_words` then rewrites `store_id = 0 -> store.id` in
  recovered `queue` and `archive` state words and validates every slot canonically (including
  rejecting swept holes) before any words enter trusted execution paths. If live roots exhaust
  `-maxmem` during a run (including after a recovery), `Checkpointed::keep_checkpoint` preserves
  the last committed checkpoint on disk so the user can retry `-recover` with a larger `-maxmem`.

## 8. Limits and known deviations

- **One experiment at a time.** `TLX_VALUE_STORE` is experimental and off by default. It cannot be
  combined with `TLX_ESCAPE`: when both are set, the driver logs
  `value store (TLX_VALUE_STORE) disabled: the escape slots replace its layout` and runs the escape
  layout rather than refusing the environment (`crates/tlx-compile/src/enc/driver.rs`). Recovering a
  `TLX_VALUE_STORE` checkpoint under `TLX_ESCAPE=1` is refused cleanly.
- **Still boxed.** Applying a fixed-domain function to a key that comes from a stored value (the
  `currentTerm[m.dest]` shape), and EXCEPT of a fixed-domain function at such a key, convert to boxed
  values. `Merge` rebuilds the merged node, which costs O(n log n) in the size of the function.
- **No spill.** Store nodes are never written to disk, so the budget is a resident-memory limit and
  the store takes part in no part of the memory and disk protocol of [scale.md](scale.md).
- **Function witnesses (`D-13`, resolved).** Both `Ref` slots and the compiled tier's fixed
  encodings (`Shape::Fcn` / `Shape::Map` via `FcnWitness`) now preserve how a function's domain was
  built in state and `VIEW` slots — including empty enumerated functions (`[i \in {} |-> e]`,
  `tests/fuzz/specs/FzEmptyFcnExcept`) and mixed-witness slots (`[i \in {1, 2} |-> i]` alongside
  `<<1, 2>>`) — while canonicalizing dynamic witness words for equality and fingerprints
  ([compat.md](compat.md) `D-13`).

## 9. Tests

- `crates/tlx-layout/src/store/tests.rs` — differential tests of the store against `tlx_value` on random
  finite values with aliases and witnesses (`operations_match_the_interpreter` requires zero
  fallbacks), digests against value equality, comparisons against the interpreter, tiny-hash
  collisions, growth across 31/32/33 and 255/256/257 keys, failed operations that publish nothing,
  the byte budget as a hard limit, handles of another store, store ids that never wrap, store
  identity, concurrent interning, safepoint mark-and-sweep reclamation (page freeing, sparse
  page/directory compaction, backing-storage accounting, and derived cache reset), and sparse v2
  `model-store` snapshot round-trip and corruption/hole rejection.
- `crates/tlx-layout/src/store/order.rs` — comparison and equality of mixed stored function kinds against
  their boxed consumers; `crates/tlx-layout/src/permute.rs` — permutation of stored handles.
- `crates/tlx-compile/src/exec/refops.rs` — the native callbacks accept an uninitialized output and
  leave it untouched on failure.
- `crates/tlx-compile/tests/value_store_runs.rs` — one cached native library serving runs of one model
  and of two models in one process, sequential and concurrent.
- `crates/tlx-compile/tests/value_store_switch.rs` — the switch on: a `Dyn` slot is a `Ref` slot and
  the run's counts equal the interpreter's; a run whose shapes are all fixed takes no store path; the
  store's budget is the run's `-maxmem`; safepoint reclamation completes `>= 5x` single-worker and
  multi-worker churn (both multi-level frontier churn and mid-level transient churn) inside a tight
  budget while genuine live-frontier exhaustion stops cleanly with the error naming the way out;
  default and explicit checkpoints persist sparse v2 `model-store` across multiple GC cycles and
  recover repeatedly in-process with fresh store ids; budget overflow and corrupt `model-store` are
  rejected cleanly. The switch's own values (`0`, `1`, `all`, unset, and its coexistence with
  `TLX_ESCAPE`) are parsed in `tlx-compile/src/settings.rs`, tested there: one test binary runs one
  environment.
- `crates/tlx-native/tests/native.rs` — an operation-table count or hash mismatch is refused, and the
  ABI header matches the Rust descriptor field by field.
- `crates/tlx-cli/tests/value_store.rs` — `>= 5x` churn reclamation across closure, C, and JIT
  backends (single- and multi-worker, mid-level and multi-level, including `TLX_PARANOID=1`),
  retry-boundary regressions (first-failure `VIEW` ordering, GC-backed counterexample replay,
  recoverable liveness atom `StoreFull`, hard-retry archive drop below 75%, single-action transient
  overflow fallback, and once-only `PrintT` across forced `VIEW` `StoreFull` retries),
  genuine live-frontier budget errors preserving the last checkpoint for larger-budget recovery,
  checkpoint and `-recover` across multiple GC cycles and workers (`VIEW`, `SYMMETRY`, `DOMAIN` /
  interval iteration caches, incremental `archive-*` hard-linking), `TLX_VALUE_STORE=all`,
  counterexample traces, layout-miss restarts after recovery, store-mode mismatch refusals
  (`TLX_VALUE_STORE=0`/`all`, `TLX_ESCAPE=1`), and corrupt `model-store` rejection.
- `crates/tlx-cli/tests/repr_litmus.rs` — the value-contract litmus specs
  (`tests/specs/Repr*.tla`: aliases, empty function, missing EXCEPT path, CHOOSE order, lazy union,
  EXCEPT side effects and errors) on the interpreter and the closure, C and JIT executors, with the
  store off, on and `all`, under `TLX_PARANOID`; `crates/tlx-cli/tests/set_comparison.rs` — fallible
  set comparisons across the same three settings.

## 10. Gaps of the experiment

`TLX_VALUE_STORE=1` is what a run sets to use the store (both gaps 1 and 2 below are now resolved;
the switch remains opt-in while gaps 4 and 5 are evaluated). This section is the record of what
turning it on costs a user today, what the way out is, and what closing each gap takes; a gap here
is not a defect of the store's operation set (section 4) but a property of the experiment it still is.

| # | Gap | What a run with the store on sees | Way out today | Fix | Cost |
|---|---|---|---|---|---|
| 1 | **No reclamation** *(resolved, section 6)* | Safepoint live-root mark-and-sweep reclamation (`SP_STORE_GC`) frees unreachable nodes, empty pages, and stale generation-keyed caches at level boundaries and mid-level budget pressure, with two-phase archive drop when live bytes exceed 3/4 of budget. Only workloads whose live reachable frontier genuinely exceeds `-maxmem` stop with the budget error (preserving the last checkpoint) | raise `-maxmem`, or `TLX_VALUE_STORE=0` if live roots exceed `-maxmem` | implemented (`crates/tlx-layout/src/store/mod.rs`, `crates/tlx-runtime/src/explore/`, `crates/tlx-compile/src/enc/model.rs`) | done |
| 2 | **Checkpoint format** *(resolved, section 7)* | Default 30-minute checkpoints and explicit `-checkpoint` / `-recover` work with `TLX_VALUE_STORE=1` and `all` via framed `model-store` snapshots, fresh `NEXT_UID` allocation on restore, store-id-neutral checkpoint handles, and mode-mismatch validation | none needed | implemented (`crates/tlx-layout/src/store/ser.rs`, `crates/tlx-compile/src/enc/driver.rs`) | done |
| 3 | **Not combined with `TLX_ESCAPE`** | With both `TLX_ESCAPE=1` and `TLX_VALUE_STORE=1`, the driver runs with the store off (logged) rather than refusing the pair | none needed | escape wins when both switches are set | none |
| 4 | **Crude slot selection** | A slot that merely *contains* a `Dyn` part becomes one handle, so its other, already-encoded components (a bitset field of a tuple, say) stop using their encodings; and a materialized definition with a `Dyn` part stays unmaterialized (`enc/driver.rs`). Only models with a `Dyn` slot are affected. | `TLX_VALUE_STORE=0` | promote per component, or choose per slot by measured benefit | half a batch: it needs a per-slot read/write and representation analysis, and the recorded regressions of the earlier broader promotion policy are the evidence that guessing is worse than not promoting |
| 5 | **Still boxed** (section 8) | Operations whose operands arrive as boxed values (a fixed-domain function applied to a key from a handle, `@@`/`:>` on a handle in the boxed expression path, a higher-order operator call over a handle) keep an interpreter boundary; native share stays below 100% on the analysis configurations. Results are unaffected | none | separate lowering batches (the operations themselves, not the representation) | a batch per operation family |

Results do not change with the switch (section 5, section 9): every gap above is about lifetime,
recovery or speed, never about a verdict, a count or a trace.

## 11. Evidence

The store's recorded A/B (interleaved off/on pairs of `scripts/bench.py ab` on one 16-vCPU spot
instance; [benchmarking.md](benchmarking.md) owns the method) found 22–49% less search time and
19–63% less peak memory on the affected raft models, unchanged results and unchanged or slightly
higher memory on the controls, and 2.8× search time for `TLX_VALUE_STORE=all` on a model with padded
fixed layouts — which is why `all` is a test mode. The raw arms and the full table are recoverable
from the pinned revision named in [README.md](README.md); nothing here is a current performance
promise.

A run with the store on against the same run with it off was measured on one 16-vCPU spot instance (Tencent
SA5.4XLARGE32 in `ap-shanghai-5`, 2026-10-09): one binary, both arms the same build with
`TLX_VALUE_STORE=0` and `TLX_VALUE_STORE=1`, `TLX_MIXED_ADAPT=0` (adaptive tiering moves work between
the mixed and the fallback path inside one run, so a comparison pins it), one search worker,
TLC-compatibility mode, `-stats` for the evaluation counts and the region times.

| Configuration | Native share | Host time share | Host seconds | Peak RSS |
|---|---|---|---|---|
| `ext/vanlightly-vsr/VSR` | 38.1% → 90.2% | 56.5% → 12.0% | 251.9 → 30.9 | 2875 → 1534 MiB |
| `VR_APP_STATE` | 55.1% → 93.8% | 61.5% → 28.6% | 83.2 → 25.2 | 1583 → 860 MiB |
| `VR_STATE_TRANSFER` | 46.4% → 88.9% | 70.7% → 49.1% | 85.6 → 40.6 | 1557 → 858 MiB |

Both arms of every pair report the same verdict (deadlock) and the same distinct states (2,692,588,
1,290,004 and 1,300,432; the `VSR` count is the one the census row has). These are single interleaved
pairs, so the seconds are a pair of samples rather than a noise-qualified comparison; the native
share and the host time share are the reproducible numbers. `VSR` is the configuration that reaches the gated threshold (interpreter
time below 20% of the search, 12.0%); the two analysis configurations stay above it and keep a
residual that is not the store's:
`Quantify` and the boxed `@@`/`:>` of `SendFunc`/`BroadcastFunc` (section 8).

The targets themselves had a discarded warm-up and one rotating interleaved round per arm on a
second launch of the same instance type, without `-stats` (a `VSR` arm is 4-8 minutes, so a warm-up
and three rounds of four targets in both modes do not fit one launch; this launch's deadline cut the
round of `VSR` and `VR_STATE_TRANSFER` after their warm-up pair and skipped `VR_INC_RESEND`):

| Configuration | Mode | Off → on (CPU seconds) | Ratio |
|---|---|---|---|
| `ext/vanlightly-vsr/VSR` | `-tlc` | 367.7 → 252.6 (the round's off arm: 365.4) | 0.687 |
| `VR_APP_STATE` | `-tlc` | 113.7 → 88.0 (warm-up), 112.1 → 86.2 (round) | 0.774, 0.769 |
| `VR_STATE_TRANSFER` | `-tlc` | 104.0 → 81.8 | 0.787 |
| `VR_APP_STATE` | default | 112.2 → 86.3 | 0.769 |

Every pair is the same search (deadlock, the same distinct states as above, peak RSS 2793 → 1535 MiB
on `VSR`), so the store lowers the whole search to about three quarters of its CPU, not only the
interpreter's share of it. The instrumented run above shows a larger ratio for the same reason the
interpreter time does: `-stats` charges the host regions, and the store-off arm enters them about a
thousand times more often (`VSR` 446 CPU seconds instrumented against 366-368 uninstrumented, while
the store-on arm is 256 against 253).

On the same instance the controls and the reduced message-bag configurations had a discarded warm-up
and three rotating interleaved rounds per arm, in TLC-compatibility mode and in the default mode
(CPU seconds, the ratio of the medians, and the range of one arm's own three samples as the run's
noise):

| Configuration | `-tlc` off → on | ratio | Default mode off → on | ratio |
|---|---|---|---|---|
| `transaction_commit/PaxosCommit` | 5.944 → 5.950 | 1.001 | 1.658 → 1.660 | 1.001 |
| `Bakery-Boulangerie/MCBakery` | 1.431 → 1.434 | 1.002 | 1.431 → 1.435 | 1.003 |
| `lamport_mutex/MCLamportMutex` | 2.476 → 2.461 | 0.994 | 2.465 → 2.466 | 1.000 |
| `KeyValueStore/MCKVSSafetySmall` | 11.988 → 11.992 | 1.000 | 3.400 → 3.413 | 1.004 |
| `bench/FlexibleRaftMsg3` | 1.588 → 1.278 | 0.805 | 1.592 → 1.270 | 0.798 |
| `bench/RaftMsg3` | 0.585 → 0.497 | 0.850 | 0.586 → 0.499 | 0.852 |
| `bench/PullRaftMsg3` | 0.239 → 0.245 | 1.025 | 0.243 → 0.247 | 1.016 |
| `bench/ReprRaftAddRemove` | 1.145 → 0.991 | 0.866 | 1.152 → 0.991 | 0.860 |
| `bench/ReprRaftFsync` | 0.438 → 0.395 | 0.902 | 0.437 → 0.395 | 0.904 |
| `bench/ReprRaft` | 0.425 → 0.389 | 0.915 | 0.425 → 0.391 | 0.920 |

The three samples of one arm spread by up to 1.9% on these runs (3.8% on the 0.24 s
`bench/PullRaftMsg3`), and every non-bag control ratio is 0.994–1.004 while the message-bag
configurations are 8–20% faster (`bench/PullRaftMsg3` moves by +0.006 s, inside its own spread).
Promoting only `Dyn`-bearing slots keeps fixed-layout configurations on their compact sequence, set
and map encodings rather than replacing them with handle indirection (section 3, section 10 gap 4).

Correctness with `TLX_VALUE_STORE` enabled — including `TLX_PARANOID` cross-checking against the
interpreter and multi-worker store sharing — is enforced by the test targets listed in section 9.
