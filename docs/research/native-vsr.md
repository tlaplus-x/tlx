# The `messages` bag in the vanlightly-vsr configurations

> [!NOTE]
> **Historical point-in-time diagnostic record** — not an active normative specification. This
> document captures pre-`v0.1.0` profiling of `ext/vanlightly-vsr/*` on a shared macOS arm64
> development workstation. All wall and search times reported here are local workstation
> diagnostics under shared load, **not** isolated cloud benchmarks of record
> ([DOC-05](../development-standards.md#doc-05)). Current value-store representation and native
> coverage contracts on `main` are owned by [value-store.md](../value-store.md) and
> [native-coverage.md](../native-coverage.md).

**M** denotes a measurement (a command was run and its numbers are reported here);
**A** denotes analysis, an estimate or a proposal. This analysis explains why
`ext/vanlightly-vsr/*` spends most of its time in the interpreter, measures the
representation change that removes it, and ranks the remaining costs.
[native-coverage.md](../native-coverage.md) owns the census method, the meaning of *native share* and *host time share*, and the operations
of the whole corpus; this analysis covers these five configurations only.

## 1. Summary

All five configurations have exactly one variable whose encoding is `Dyn`: the
message bag `messages`. That single slot costs **1.21 billion host-region
entries** on `VSR`, which is where nearly all of its 170 s of interpreter time
goes.

Store-backed slots — the `Ref` representation behind `TLX_VALUE_STORE`
([value-store.md](../value-store.md)) — already remove almost all of it: native
share 38.14 % → 90.19 %, host-region entries 1,207,663,985 → 6,388,591, host
time 170.07 s → 13.13 s, with identical generated / distinct / depth counts.
What stays behind is not a second shape problem: it is the **boxed expression
path in the lowering**, which turns `@@` / `:>` on a handle into `ValOp`
whenever the enclosing node is not a store coerce target, plus — in the four
analysis configurations — calls to the CommunityModules higher-order operator
`Quantify(S, LAMBDA)`, which the compiler does not inline.

Making individual boxed operations native (the recorded plans for `DOMAIN` /
`@@` / EXCEPT on `Dyn`) cannot fix this model: those three operations are
**16.7 %** of the host time, while boxed *values* (`Eq` and the comparison after
a boxed application) are **76.5 %**.

## 2. What the model is

`messages` is a **bag**: `SendFunc`/`DiscardFunc` maintain
`messages : [Message -> Nat]` as `msgs @@ (m :> 1)` and `[msgs EXCEPT ![m] = @ - 1]`,
and every action begins with `\E m \in DOMAIN messages : ReceivableMsg(m, Type, r)`,
where `ReceivableMsg(m, t, r) == m.type = t /\ m.dest = r /\ messages[m] > 0`
(`third_party/external/vanlightly-vsr/VSR.tla`, lines 236-272 and 425-720).

`Message` is a *heterogeneous* set of records: `PrepareMsgType` (7 fields),
`PrepareOkMsgType` (5), `StartViewChangeMsgType` (4), `DoViewChangeMsgType` (8,
including `log : [Nat -> LogEntryType]`), `StartViewMsgType` (7),
`GetStateMsgType` (5), `NewStateMsgType` (8), and the recovery messages — a
`Union` of record arms of different arity, several with an unbounded or
sequence-valued field.

## 3. Root cause: the slot decision

`TLX_COVERAGE=1` prints the final layout slot by slot and, for a `Dyn` slot, why
it was refused (M, unmodified `VSR.cfg`):

```
compile: var messages : Dyn
    Dyn: function keys Union(2 arms) have no finite universe of at most 4096 values (2 times)
    Dyn: function keys Union(3 arms) have no finite universe of at most 4096 values (2 times)
    Dyn: function keys Union(4 arms) have no finite universe of at most 4096 values (3 times)
    Dyn: function keys Union(4 arms) have no encoding in TLC order (universe 34)
```

Both `Shape::Map` refusals in `shape.rs::map_shape` fire, for two different
reasons (A, read from the source):

- `bitset_universe` needs the key shape to have a cardinality of at most 4096.
  A record's cardinality is the product of its fields'
  (`shape.rs::cardinality`), and `log : [Nat -> LogEntryType]` is unbounded, so
  the union has no finite universe.
- The last line is the other branch: that union *does* have a finite universe of
  34 values, but `map_key_ok` rejects it — a record field that is neither scalar
  nor a nested record/tuple/union-of-records (the `Seq` of log entries) is not
  a legal map key.

`messages` is the only `Dyn` variable in all five configurations (M, one
`TLX_COVERAGE` layout per configuration); every other slot has a fixed encoding,
including `rep_svc_recv` and `rep_dvc_recv`, which are already
`Set bitset(...) of Record(4 fields)`. The merged lowering changes of the last
day (native EXCEPT on a union's function-like arm, quantifier domains over
constant tables, interval difference) leave this file's static profile
byte-identical: 2,396 IR nodes (344 boxed, 48 interpreted), 153 host regions,
the same 24-row boxed histogram (M, before and after merging the current main).

## 4. What the cost actually is

**It is not one expensive operation; it is a large number of cheap interpreter
callbacks.** On the full `VSR.cfg` (M, `-tlc -workers 1`, host times summed over
all regions):

| Operation | Argument shapes | Region entries | Host seconds | Share |
|---|---|---|---|---|
| `Eq` | Val, Val | 930,978,952 | 87.75 | 51.6% |
| `ValOp >` | Val, Int | 59,089,377 | 24.85 | 14.6% |
| `Eq` | Val, Int 0..5 | 155,824,891 | 17.57 | 10.3% |
| `Interp Except` | Dyn, Val | 5,357,589 | 14.41 | 8.5% |
| `ValOp DOMAIN` | Dyn | 40,743,846 | 9.13 | 5.4% |
| `Interp builtin @@` | Val, Val, Int 0..5, Val | 620,645 | 5.34 | 3.1% |
| `ValOp @@` | Dyn, Val | 1,211,925 | 4.82 | 2.8% |
| `ValOp \in` | Record(8 fields), Val | 1,211,925 | 1.69 | 1.0% |
| `Interp SetEnum` | Val | 4,117,259 | 0.72 | 0.4% |
| other 110 regions | | | 3.80 | 2.2% |
| **total** | | **1,207,663,985** | **170.07** | |

A region is charged to its root node, so the row name is not the cost (an
earlier correction of this census); the generated C is where the subtree and its
inputs are visible. `act_2` is `ReceiveMatchingSVC`, region ids as `-stats`
reports them (M, `model.c` from the native cache):

```c
for each r in replicas:                     /* native bitset loop */
  h->elems(cx, h->eval(cx, 20, ...), ...)   /* region 20: ValOp DOMAIN   [Dyn]        */
  for each message handle t0 in that set:
    h->eval(cx, 14, [t0])                   /* region 14: Eq             [Val, Val]   */
    h->eval(cx, 15, [t0, r])                /* region 15: Eq             [Val, 0..5]  */
    h->eval(cx, 16, [t0])                   /* region 16: ValOp >        [Val, Int]   */
    h->eval(cx, 17, [t0, r])                /* region 17: Eq             [Val, 0..5]  */
    ... native bitset compare and copy
```

Region 14 is `m.type = StartViewChangeMsg`, 15 is `m.dest = r`, 16 is
`messages[m] > 0`, 17 is `m.view_number = View(r)`: **four interpreter callbacks
per (message, replica) pair**, each handing the opaque message handle over the
ABI and back. An `Eq` entry costs 94 ns and a `ValOp >` entry 420 ns on average
(M, from the table above). Neither is large on its own; 1.2 billion of them is.

Every action in the specification iterates `DOMAIN messages` this way, which is
why the same `Eq [Val, Val]` row reappears once per action with 75-98 million
entries (`SendGetState`, `ReceivesRecoveryMsg`, `ReceiveSV`, the whole
`Receive*` family).

## 5. The representation that removes it, measured (M)

The store-backed slot (`TLX_VALUE_STORE=1`, one `Ref` slot per variable whose
speculated shape would have a `Dyn` part — exactly `messages` here) is already
implemented and off by default; [value-store.md](../value-store.md) is its
contract. `TLX_MIXED_ADAPT=0` pins the mixed-mode tier so that adaptive tiering
cannot flip the chosen path between arms (section 8.2).

Read the tables below as two kinds of number. The **native share and the
host-region entry count are exactly reproducible** — identical on the branch
point and on the current main, and independent of machine load. The **seconds
are instrumented elapsed times on a shared machine** and vary with the load of
the other workers: the same 1.21 billion entries were measured at 154.66 s and
at 170.07 s in two runs. Times are indicative; counts are the evidence.

### 5.1 `VSR.cfg`, the target configuration

Two independent off/on pairs, one on the branch point and one after merging the
current main into this branch:

| Pair | Arm | generated / distinct / depth | Native share | Host entries | Host s | Search s |
|---|---|---|---|---|---|---|
| 1 | store off | 7,672,618 / 2,692,588 / 17 | 38.14% | 1,207,663,985 | 154.66 | 257.0 |
| 1 | store on | identical | 90.19% | 6,388,591 | 20.78 | 158.2 |
| 2 | store off | identical | 38.14% | 1,207,663,985 | 170.07 | 282.2 |
| 2 | store on | identical | 90.19% | 6,388,591 | 13.13 | 108.4 |

Both pairs report deadlock with the same generated, distinct and depth counts as
the census row for this configuration, and both leave the same
1,125,517 states on the queue at the end. The census row itself (adaptive
tiering on, cloud x86_64, earlier revision) reads 38.11 % native / 42.73 % host
with the same counts.

### 5.2 Three interleaved pairs on a reduced configuration

`Values = {v1}` (everything else unchanged) reproduces the full model's profile
at roughly a twelfth of the wall time; the store-off arm reports 38.79 % native
against the full configuration's 38.14 %. Three interleaved off/on pairs, each
pair adjacent in time so that load affects both arms alike (M):

| Arm | Search s (3 pairs) | Native share | Host s (3 pairs) | Host share (3 pairs) | Host entries |
|---|---|---|---|---|---|
| store off | 22.7 / 14.4 / 12.7 | 38.79% | 13.96 / 8.80 / 7.72 | 60.84 / 60.74 / 60.56% | 77,987,278 |
| store on | 8.8 / 9.2 / 9.2 | 89.92% | 1.30 / 1.39 / 1.41 | 14.59 / 14.89 / 15.07% | 577,128 |

Median search 14.4 s → 9.2 s (1.56×). The host time *share* is the stable
statistic here — 60.6-60.8 % against 14.6-15.1 % across the three pairs — and an
earlier three-pair set on the branch point gave 23.5 / 21.5 / 21.5 s against
13.1 / 12.4 / 11.6 s (1.73×) with the same native shares and the same 98 → 12
regions carrying entries. Every pair reports
636,243 generated / 235,765 distinct / depth 13 / deadlock, and
`TLX_PARANOID=1` with the store on reports the same counts, so the compiled tier
equals the interpreter for this model (compat.md §0).

### 5.3 The other configurations (M)

One off/on pair each on the current main:

| Configuration | Arm | Native | Host share | Host s | Search s | Host entries | generated / distinct / depth |
|---|---|---|---|---|---|---|---|
| `VR_APP_STATE` | off | 55.07% | 64.11% | 38.15 | 58.9 | 340,606,205 | 2,916,653 / 1,290,004 / 14 |
| `VR_APP_STATE` | on | 93.82% | 28.31% | 14.02 | 48.6 | 2,642,589 | identical |
| `VR_STATE_TRANSFER` | off | 46.44% | 72.04% | 45.27 | 61.9 | 255,223,162 | 3,260,239 / 1,300,432 / 14 |
| `VR_STATE_TRANSFER` | on | 88.95% | 47.57% | 28.46 | 58.9 | 4,427,784 | identical |

Native shares and entry counts here are identical to a measurement taken before
the merge, so the merged lowerings do not touch these configurations either.
The store clears the native-share threshold on all three measured
configurations. It clears the host-share threshold on `VSR` only: the two
analysis configurations are left with a residual that section 6 ranks.
`VR_INC_RESEND` and `VR_ASSUME_NEWVIEWCHANGE` were checked statically (both
`messages : Dyn`, same action set) but not measured — no claim is made for them
here.

### 5.4 The generated C after the change (M)

The same loop of section 4 becomes (operation ids from the ABI table the C
source carries):

```c
h->ref_op(cx, 0, [messages], ...)             /* Domain            */
h->ref_elems(cx, domain_handle, &F, &N)       /* iterate the store */
for each element handle t0:
  h->ref_op(cx, 2, [Field(type)(t0)], ...)    /* Eq, part inlined  */
  h->ref_op(cx, 3, [Field(dest)(t0)], ...)    /* Eq                */
  h->ref_op(cx, 6, [messages, t0], ...)       /* Apply             */
  h->ref_op(cx, 7, [Field(view_number)(t0)])  /* Eq                */
```

`ref_op` is still an ABI call, but it re-enters `exec/refops.rs` directly —
no interpreter, no `Val` conversion, no IR executor — which is the difference
between 1.21 billion region entries and 6.4 million.

## 6. What is left after the store

### 6.1 `VSR`, store on (M)

| Region root | Action | Entries | Host s | Cause |
|---|---|---|---|---|
| `If` [Bool, Ref, Val] | `SendDVC` | 1,211,925 | 5.98 | `SendFunc`'s `msgs @@ (m :> 1)` |
| `Interp Let` [Ref, 0..5, Record(4)] | `ReceiveHigherSVC` | 590,932 | 5.30 | `BroadcastFunc`'s `[...] @@ [...]` |
| `If` [Bool, Ref, Val] | `ReceiveSV` | 128,798 | 0.87 | `SendFunc` |
| `If` [Bool, Ref, Val] | `ReceivePrepareMsg` | 53,956 | 0.35 | `SendFunc` |
| `Interp Let` [Ref, 0..5, Record(4)] | `ReceiveHigherDVC` | 29,713 | 0.26 | `BroadcastFunc` |
| `Interp SetEnum` [Ref] | `ReceiveMatchingSVC` | 3,526,327 | 0.21 | `{m}` |
| `Interp builtin @@` [Ref, Set, ...] | `ReceiveClientRequest` | 149,473 | 0.06 | `BroadcastFunc` |
| other 6 regions | | | 0.10 | |
| **total** | | **6,388,591** | **13.13** | |

With 153 host regions reduced to 14, what is left is the expensive part: an
entry in the store arm costs about 2 µs against 141 ns in the other.

`SendFunc(m, msgs) == IF m \in DOMAIN msgs THEN [msgs EXCEPT ![m] = @ + 1] ELSE msgs @@ (m :> 1)`
is lowered with a *native* condition and a *native* THEN branch — `typed_except`
in `lower/select.rs` checks `is_ref(cur.ty)` and produces `RefOp`s — while the
ELSE branch falls to `ValOp` (`valop @@`, `valop :>`) because the generic
expression path has no such check. The `If` node is then `val`-typed and the
whole action tail becomes one host region. The same shape appears in
`BroadcastFunc`'s
`[m \in DOMAIN msgs |-> IF m \in bcast_msgs THEN msgs[m] + 1 ELSE msgs[m]] @@ [r \in new_msgs |-> 1]`,
where neither operand is a store coerce target either.

`refs.rs::ref_expr` already handles `Record`, `Tuple`, `:>` and `@@` at a store
coerce boundary; the gap is that it only runs at that boundary, so an operator
whose *result* is stored but whose body is lowered by `expr()` never reaches it.

### 6.2 The four analysis configurations: `Quantify`

`VR_APP_STATE`, `VR_INC_RESEND`, `VR_STATE_TRANSFER` and
`VR_ASSUME_NEWVIEWCHANGE` additionally call the CommunityModules operator

```tla
Quantify(DOMAIN messages, LAMBDA m : m.type = StartViewChangeMsg /\ ... ) >= ReplicaCount \div 2
```

With the store on, that is the *largest* remaining region in
`VR_STATE_TRANSFER` (`SendSV` 9.16 s + `SendDVC` 5.90 s = 15.06 s of its 28.46 s)
and the second largest in `VR_APP_STATE` (4.39 s of 14.02 s). The IR shows the
root as `interp Builtin { op: Ge, args: [Apply { op: Def(...) } @625:12] }` with
the operand converted to `val` (M, `TLX_IR_DUMP=SendDVC`): the `Quantify` call
is a non-inlined operator (FiniteSetsExt line 94) whose higher-order parameter
the compiler cannot reach, and even with the store the argument `DOMAIN
messages` is boxed at that boundary. This is *not* the `Forall`/`Exists`
family; no generic quantifier lowering covers an opaque operator call.

It is also the clearest case of the root-node attribution trap in the census:
the operation table lists it as `Interp builtin >=` with the argument shape
`Int 0..5` and the family "Heterogeneous comparison and membership", which reads
as a comparison problem. Nothing about `>=` is expensive here; the region is the
whole quantifier.

### 6.3 Ranked batches (A)

Ceilings, not forecasts: a row's host time is what the region costs today, and
replacing the region with native code removes the boundary plus whatever the
native implementation is cheaper at, not necessarily all of it. The batches are
independent; the ceilings overlap in that removing one region can expose another
(a second representation change may be needed before a region disappears
entirely).

| Rank | Batch | Files | Mechanism | Ceiling (measured host seconds, current main) |
|---|---|---|---|---|
| 1 | Store-backed slots for `Dyn` variables (implemented; enable, complete, productionize) | `crates/tlx-layout/src/store/`, `crates/tlx-compile/src/exec/refops.rs`, `crates/tlx-compile/src/lower/refs.rs`, `crates/tlx-cli/src/settings.rs` | A variable whose speculated shape has a `Dyn` part holds a `Ref`; DOMAIN, apply, EXCEPT, `:>`, `@@`, `=` and iteration become `RefOp`s in all three executors | **VSR 156.9** (170.07 → 13.13), **VR_APP_STATE 24.1** (38.15 → 14.02), **VR_STATE_TRANSFER 16.8** (45.27 → 28.46); native +52.1 / +38.8 / +42.5 points; host-region entries divided by 189 / 129 / 58 |
| 2 | `@@` and `:>` on a handle in the boxed expression path | `crates/tlx-compile/src/lower/refs.rs`, `crates/tlx-compile/src/lower/expr.rs`, `crates/tlx-compile/src/lower/construct.rs` | Whatever `typed_except` does for EXCEPT, do for `@@`/`:>`: if an operand is a handle, produce `RefOp::Merge` / `RefOp::Single` and keep the node handle-typed, and let `ref_expr` lower `IF`/`LET` bodies so an operator whose result is stored is built in the store | **VSR 12.85** (98% of its residual; `VSR` would then be ≈99% native), **VR_STATE_TRANSFER 13.30**, **VR_APP_STATE 9.62** |
| 3 | Opaque higher-order operator calls over a boxed domain | `crates/tlx-compile/src/lower/calls.rs`, `crates/tlx-compile/src/lower/expr.rs` | Inline or recognize `Quantify(S, LAMBDA)` (CommunityModules `FiniteSetsExt`) so the lambda body is compiled and `S` stays a handle | **VR_STATE_TRANSFER 15.06**, **VR_APP_STATE 4.39**, VSR 0 |
| 4 | Singleton set construction over a handle (`{m}`) | `crates/tlx-compile/src/lower/sets.rs`, `crates/tlx-layout/src/store/` | `RefOp` has no set constructor and a handle may not sit inside a set arm ([value-store.md](../value-store.md) §3), so this needs a store-side set node rather than a lowering tweak | VSR 0.26, VR_APP_STATE ≈0, VR_STATE_TRANSFER ≈0 |

Batches 2 and 3 together are what the two analysis configurations need: they are
still above the host-share threshold with the store on, and those two families
are 98 % of what remains in `VR_STATE_TRANSFER`.

## 7. What the recorded lowering plans would and would not do here

Measured against the store-off `VSR` table of section 4 (M):

| Plan | Rows it covers on `VSR` | Host s | Share | Verdict |
|---|---|---|---|---|
| Native boxed-op ABI helper (`DOMAIN`, `@@`, `:>`, guarded EXCEPT on `Dyn`) | `Interp Except [Dyn,Val]` 14.41, `ValOp DOMAIN [Dyn]` 9.13, `ValOp @@ [Dyn,Val]` 4.82 | 28.36 | 16.7% | Real but not the fix |
| Heterogeneous atom membership (`Atom(n) \in Val`) | every `ValOp \in` row | 2.72 | 1.6% | Not the problem here |
| Quantifiers `Forall`/`Exists` over boxed domains | none — the analysis configurations use `Quantify`, not `Forall`/`Exists` | 0 | 0% | Does not apply |
| Integer comparison out of encoded fields (`select.rs` order) | `ValOp > [Val,Int]` here is `messages[m] > 0`, a boxed *application*, not a boxed field | 0 | 0% | Does not apply |
| Field-level comparability (`shapes_comparable`) | `messages` is a function, not a set of records; VSR's record sets are already encoded bitsets | 0 | 0% | Does not apply |

The first row is the important one. **76.5 %** of the host time is
`Eq [Val,Val]` (87.75 s), `Eq [Val,Int 0..5]` (17.57 s) and `ValOp > [Val,Int]`
(24.85 s) — boxed *values* consumed by operations that are already as native as
they can be. No operation-level lowering reaches them, because the problem is
the representation of the value, not the operation:
`m.type = StartViewChangeMsg` is 94 ns of work behind an interpreter boundary
crossed 1.2 billion times. The same reasoning bounds the boxed-op helper: its
28.36 s ceiling is the region entry plus the operation, and the `@@` and EXCEPT
operations themselves rebuild their result (`Merge` is O(n log n) in the size of
the merged function, [value-store.md](../value-store.md) §8), so the boundary is
the smaller part of that ceiling.

## 8. Method, reproduction and limits

### 8.1 Commands

Measured on macOS arm64 (`tlx` release build, one search worker) on the shared
workstation; every run is bounded by `timeout`. All comparisons hold the
configuration, tier, worker count and tier pinning fixed between arms and check
that generated / distinct / depth agree.

```sh
cargo build --release
cd third_party/external/vanlightly-vsr

# the slot decision and the boxed-node histogram
TLX_COVERAGE=1 TLX_CGEN_DEBUG=1 timeout 200 ../../../target/release/tlx check VSR.tla \
  -config VSR.cfg -tlc -workers 1 -stats json=/tmp/vsr-stats.json

# the region subtree behind a region root
TLX_IR_DUMP=ReceiveMatchingSVC timeout 60 ../../../target/release/tlx check VSR.tla \
  -config VSR.cfg -tlc -workers 1

# one arm of the A/B; the other is TLX_VALUE_STORE=0
TLX_MIXED_ADAPT=0 TLX_VALUE_STORE=1 timeout 600 ../../../target/release/tlx check VSR.tla \
  -config VSR.cfg -tlc -workers 1 -stats json=/tmp/vsr-store.json
```

The native share and host time share of a `-stats json` file are computed with
the census driver's own function (`scripts/coverage.py`, `dynamic_report`), so
they mean what [native-coverage.md](../native-coverage.md) says they mean. The
corpus-level equivalent is
`python3 scripts/coverage.py --source external --sizes medium,large --filter vanlightly-vsr --dynamic --timeout 600 -j 3 --out …`
with the same two variables in the environment.

### 8.2 Adaptive tiering is a confounder, and so is the machine

A first measurement of the reduced configuration without pinning the tier gave,
for two runs of the same arm, 23.4 s and 33.0 s of search time and host times of
5.47 s and 14.98 s (M). The `-stats` per-action call counts show why: with
adaptive tiering on, this model's mixed functions sometimes take the native path
and sometimes the fallback path, decided by timing inside the run. The native
share did not move, because the same host regions are entered either way, but
the times did. Any before/after measurement of these configurations must pin
`TLX_MIXED_ADAPT=0`, and any time-based claim needs interleaved pairs or a
count-based check.

Host seconds are elapsed times measured on a machine shared with other workers;
the same work measured 154.66 s and 170.07 s in two runs, and the store arm
13.13 s and 20.78 s. That is the "noise" of this document's central comparison and
it is why the native share, the host-region entry count and the host time
*share* are the numbers to read.

### 8.3 Limits

`VR_INC_RESEND` and `VR_ASSUME_NEWVIEWCHANGE` are diagnosed statically only. The
full configuration and the two analysis configurations have one pair per arm;
only the reduced configuration has three interleaved pairs. The batch ceilings
in section 6.3 are region times, not measured savings of an implementation. Host
time share is instrumented region elapsed time over a sampled estimate of search
thread-seconds, so it moves when the run gets faster for reasons unrelated to
the interpreter; the threshold is met on `VSR` on the numerator (`host s`) and
on the ratio, but not on either for the two analysis configurations.
