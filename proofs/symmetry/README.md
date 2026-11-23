# Connected keyed-symmetry certificates

The automatic symmetry emitter supports disjoint products of full permutation
groups (2–6 model values per group, total group order at most 720) across:

- Fixed-domain maps (`[K -> V]`) and mixed fixed-domain maps (`[K \cup Fixed -> V]`)
  with key-free, mutually comparable payloads.
- Scalar and optional key variables (`K` or `K \cup Fixed`), including slot-indexed
  map lookups and writes.
- Sets of keys (`SUBSET K` or `SUBSET (K \cup Fixed)`), set equalities/subsets,
  and finite key cardinalities.
- Sets of single-key and key-free tagged records (each record shape has at most
  one pure-key field).
- Fixed-shape records whose fields are core values, fixed-domain maps, or
  scalar/optional key slots.

## Examples

- [Keyed.tla](Keyed.tla) ([Keyed.cfg](Keyed.cfg), [KeyedLarge.cfg](KeyedLarge.cfg)):
  two maps over the same process set, record-field writes, whole-payload resets,
  conditional values and nested key quantification. With `Keyed.cfg`, 64 concrete
  states become 20 permutation classes. With `KeyedLarge.cfg` (four processes,
  limit 30), 1,048,576 concrete states become 52,360 classes.
- [ScalarSlot.tla](ScalarSlot.tla) ([ScalarSlot.cfg](ScalarSlot.cfg)):
  optional key slot `owner \in Proc \cup {"none"}` paired with a keyed map `pc`
  read and updated at `pc[owner]`. 108 concrete states become 28 classes.
- [ProductSets.tla](ProductSets.tla) ([ProductSets.cfg](ProductSets.cfg)):
  product group `Permutations(Client) x Permutations(Server)` over two keyed
  maps, a set of keys (`acked \subseteq Client \cup Server`) with `Cardinality`
  observation, and a set of single-key/key-free tagged records (`msgs`).
  39 concrete states become 17 classes.

From the repository root:

```sh
cargo build --release
./target/release/tlx check proofs/symmetry/Keyed.tla -interp
./target/release/tlx check proofs/symmetry/ScalarSlot.tla -compile
./target/release/tlx check proofs/symmetry/ProductSets.tla -compile
python3 proofs/check_generated.py --lean lean --negative \
  /path/to/Optimization.lean
```

Use the actual Lean path printed by the check. Automatic symmetry emits it even
without `-optimize`. Normal checking never invokes Lean.

Six theorem audits cover initialization/successor/observation correspondence,
safety, stuttering specifications, concrete counterexamples, deadlocks and
formal orbit-key equivalence. Eight mutation checks reject missing bound-key
renaming, missing map permutation, missing scalar-slot permutation, missing
key-value renaming, order-dependent cardinality replacement, deleted
initial/successor classes and changed reduced observations. No custom
correctness axiom is permitted.

## Trusted computing base and refusals

The theorem quantifies over key-independent core (`C`), fixed-atom (`A`),
branch-local (`W`), and payload (`V`) interpretations; key operations, group
masks, finite cardinalities and slot transfers are explicit. Source lowering,
inferred domains and shape splitting, leaf interpretation, totality, runtime
group closure and minimum-key representative selection remain trusted. Formal
orbit equality is not a proof of the Rust minimum-key implementation.

Unsupported shapes refuse cleanly: overlapping or unused groups, partial/pinned
subsets, multi-key record shapes, key-bearing map payloads, multi-actor partial
field patches that could alias, primed non-core reads, `CHOOSE` over keys, and
unknown domains. Other projection/symmetry combinations remain disabled;
variable erasure is covered below.

## External corpus coverage

Unchanged specifications in the TLA+ Examples corpus are covered automatically
in the default mode:

- `transaction_commit/TCommit.tla` (`-config proofs/symmetry/TCommit.cfg`, 6 RMs):
  792 concrete → 34 reduced (`Permutations(RM)`).
- `transaction_commit/TwoPhase.tla`: 288 → 80 (`Permutations(RM)`).
- `transaction_commit/2PCwithBTM.tla`: 1,245 → 309 (`Permutations(RM)`).
- `byihive/VoucherLifeCycle.tla`: 64 → 20 (`Permutations(V)`).
- `byihive/VoucherCancel.tla`: 4,199 → 401 (`Permutations(V) x Permutations(H) x Permutations(I)`).
- `byihive/VoucherRedeem.tla`: 4,199 → 401 (`Permutations(V) x Permutations(H) x Permutations(C)`).
- `byihive/VoucherTransfer.tla`: 4,197 → 401 (`Permutations(V) x Permutations(SH) x Permutations(DH)`).
- `SpecifyingSystems/AsynchronousInterface/AsynchInterface.tla`: 12 → 4 (`Permutations(Data)`).
- `SpecifyingSystems/AsynchronousInterface/Channel.tla`: 12 → 4 (`Permutations(Data)`).
- `SpecifyingSystems/TLC/ABCorrectness.tla`: 20 → 10 (`Permutations(Data)`).
- `acp/ACP_SB_TLC.tla`: 54,944 → 10,100 (`Permutations(participants)`).

These are correctness coverage counts, not timing claims for small models.

## Erasure followed by symmetry

[Erased.tla](Erased.tla) keeps two unobserved snapshots of a keyed map. Snapshots can
copy each other, save the old map or reset to literals. They can contain moved keys,
so they must be erased before the retained map chooses its orbit representative.
With [Erased.cfg](Erased.cfg), TLC and compatibility-mode tlx find 2,796 generated /
811 distinct states. Erasure alone gives 109 / 27; composition gives 41 / 10:

```sh
./target/release/tlx check proofs/symmetry/Erased.tla -tlc -interp
./target/release/tlx check proofs/symmetry/Erased.tla -optimize -noautosymmetry -interp
TLX_PARANOID=1 TLX_SYMMETRY_PARANOID=1 ./target/release/tlx check proofs/symmetry/Erased.tla -optimize -compile
```

The combined generated certificate includes the full source initialization, the
actual hidden transfers, keyed guards, map writes and slot writes with one common
branch choice. Its intermediate erasure and final orbit certificates describe the
same model. Seven audits cover both certificates, safety, stuttering, concrete
counterexamples, deadlocks and formal orbit-key equivalence. Nine mutations reject
broken key/map/slot/cardinality renaming, missing quotient initialization/successors,
removed concrete hidden successors and changed reduced observations. Runtime tests
retain concrete snapshot values in failing and deadlocking traces across execution tiers.

The installed projection must be the exact retained-variable tuple. Unknown or
partial hidden updates, reads of omitted variables, unsupported keyed shapes and
other projection kinds refuse composition. Existing user VIEW/SYMMETRY declarations
retain the TLC path. Source lowering, domain/totality inference, independent semantic
leaves, group closure and runtime projection/canonicalization remain trusted.
