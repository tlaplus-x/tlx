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
checked lookups rather than read as this store's node. Nodes live in a page table of `OnceLock`s
(16384 nodes per page, 65536 pages).

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

Interning takes a short lock on one shard. Nodes are published once and never change or move, so
readers take no lock at all; a node slot written twice is an assertion failure rather than a silent
replacement.

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
no memory budget, `Settings::value_store_bytes` in `crates/tlx-compile/src/settings.rs`). A handle
stays valid for as long as that run's store lives — nothing else keeps it alive, and nothing
reclaims it.

The store is not a process-wide interner, so two runs in one process have two stores even when they
share one cached native library: the library calls back into the store of its per-call context, not
into one of its own (`tlx-compile/tests/value_store_runs.rs`).

There is **no reclamation**. The budget is the run's own memory budget
(`Settings::value_store_bytes`), never a fraction of it: the store replaces the process-wide `Dyn`
interner for its slots, and that interner had no limit of its own, so a budget below the run's would
end a run the run's memory guard lets finish. Insertion charges the node word plus its payload bytes
against the budget (the index is counted separately, for the report). Exceeding the budget — or
exhausting the page table — marks the store full and ends the run with an error naming the budget
and the way out (`raise -maxmem or turn the store off (TLX_VALUE_STORE=0)`,
`enc/driver.rs::check_store`); values the store refused were neither stored nor fingerprinted, so
this is a hard stop and not a degraded mode. When a run has no memory budget (`usize::MAX`, such as
simulation or unbudgeted library `Options`), the page table is the store's only limit, as the
interner's growth was (section 10, gap 1).

## 7. Checkpoint and recovery

There is no checkpoint format for the store. A run that recovers, or that asks for checkpoints, turns
the store off and logs `value store (TLX_VALUE_STORE) disabled: checkpoints keep Dyn values`; a run
whose only checkpoint setting is the default interval takes no checkpoints and logs
`value store (TLX_VALUE_STORE): this run takes no checkpoints (TLX_VALUE_STORE=0 keeps them)`
(`crates/tlx-compile/src/enc/driver.rs`). This is the largest gap of the experiment: a stored run
cannot be resumed, and a stored run takes none of TLC's default interval checkpoints either
(section 10, gap 2).

## 8. Limits and known deviations

- **One experiment at a time.** `TLX_VALUE_STORE` is experimental and off by default. It cannot be
  combined with `TLX_ESCAPE`: when both are set, the driver logs
  `value store (TLX_VALUE_STORE) disabled: the escape slots replace its layout` and runs the escape
  layout rather than refusing the environment (`crates/tlx-compile/src/enc/driver.rs`). When
  `TLX_VALUE_STORE` is enabled without `-recover` or an explicit `-checkpoint`, it suppresses the
  default 30-minute checkpoint timer (section 7).
- **Still boxed.** Applying a fixed-domain function to a key that comes from a stored value (the
  `currentTerm[m.dest]` shape), and EXCEPT of a fixed-domain function at such a key, convert to boxed
  values. `Merge` rebuilds the merged node, which costs O(n log n) in the size of the function.
- **No spill.** Store nodes are never written to disk, so the budget is a resident-memory limit and
  the store takes part in no part of the memory and disk protocol of [scale.md](scale.md).
- **D-13 remains for the fixed encodings.** Because the store keeps a function's construction, D-13
  does not apply to `Ref` slots; it still applies to every slot with a fixed encoding. In particular
  an empty function over an enumerated domain (`[i \in {} |-> e]`) must keep its witness in state and
  VIEW slots, where decoding it as the tuple `<<>>` currently makes a string-key EXCEPT fail. That is
  the open tlx bug pinned by `tests/fuzz/specs/FzEmptyFcnExcept` (TLC and the interpreter end at
  3 generated / 2 distinct / depth 2), and it is a deviation of the fixed encodings, not of the store.

## 9. Tests

- `crates/tlx-layout/src/store/tests.rs` — differential tests of the store against `tlx_value` on random
  finite values with aliases and witnesses (`operations_match_the_interpreter` requires zero
  fallbacks), digests against value equality, comparisons against the interpreter, tiny-hash
  collisions, growth across 31/32/33 and 255/256/257 keys, failed operations that publish nothing,
  the byte budget as a hard limit, handles of another store, store ids that never wrap, store
  identity, and concurrent interning.
- `crates/tlx-layout/src/store/order.rs` — comparison and equality of mixed stored function kinds against
  their boxed consumers; `crates/tlx-layout/src/permute.rs` — permutation of stored handles.
- `crates/tlx-compile/src/exec/refops.rs` — the native callbacks accept an uninitialized output and
  leave it untouched on failure.
- `crates/tlx-compile/tests/value_store_runs.rs` — one cached native library serving runs of one model
  and of two models in one process, sequential and concurrent.
- `crates/tlx-compile/tests/value_store_switch.rs` — the switch on: a `Dyn` slot is a `Ref` slot and
  the run's counts equal the interpreter's; a run whose shapes are all fixed takes no store path; the
  store's budget is the run's `-maxmem` (a value set that fits it finishes, half of what it needs ends
  the run with the error that names the way out); an explicit checkpointer keeps `Dyn` values and
  turns the store off, and the default interval keeps the store and takes no checkpoint. The switch's
  own values (`0`, `1`, `all`, unset, and its coexistence with `TLX_ESCAPE`) are parsed in
  `tlx-compile/src/settings.rs`, tested there: one test binary runs one environment.
- `crates/tlx-native/tests/native.rs` — an operation-table count or hash mismatch is refused, and the
  ABI header matches the Rust descriptor field by field.
- `crates/tlx-cli/tests/value_store.rs` — the budget error, and the checkpoint policy.
- `crates/tlx-cli/tests/repr_litmus.rs` — the value-contract litmus specs
  (`tests/specs/Repr*.tla`: aliases, empty function, missing EXCEPT path, CHOOSE order, lazy union,
  EXCEPT side effects and errors) on the interpreter and the closure, C and JIT executors, with the
  store off, on and `all`, under `TLX_PARANOID`; `crates/tlx-cli/tests/set_comparison.rs` — fallible
  set comparisons across the same three settings.

## 10. Gaps of the experiment

`TLX_VALUE_STORE=1` is what a run sets to use the store, and the switch stays off by default until
the first two gaps below are closed. This section is the record of what turning it on costs a user
today, what the way out is, and what closing each gap would take; a gap here is not a defect of
the store's operation set (section 4) but a property of the experiment it still is.

| # | Gap | What a run with the store on sees | Way out today | Fix | Cost |
|---|---|---|---|---|---|
| 1 | **No reclamation** (section 6) | A `Dyn` variable's values accumulate for the whole run; past the run's `-maxmem` the run *stops with an error*, where the `Dyn` interner it replaced grew until the machine ran out of memory. Long runs on bag-like state are the ones that reach it. The budget is the run's own `-maxmem`, not a fraction of it | raise `-maxmem`, or `TLX_VALUE_STORE=0` | reclamation (reference counting, or mark-and-sweep rooted in the live states) plus a budget policy that matches the other representations — the "stable state root slots" step of the design record | a full batch: it needs the set of live state roots (queue, archive, spill, memo) to be enumerable, which is a change to the search, not to the store |
| 2 | **No checkpoint format** (section 7) | (a) `-recover` or an explicit `-checkpoint N`: the store is off (logged) — as before. (b) With only TLC's default interval, the run takes **no checkpoints at all** (logged): a crash costs the whole search, where the same run without the store would leave a resumable checkpoint. This is what a run with the store on does today. | `TLX_VALUE_STORE=0` restores the checkpoint | a checkpoint format for the store (serialize its nodes, remap handles on recovery), which belongs with the stable-root work: an encoding is only stable across a recovery if the slots are | a full batch |
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
