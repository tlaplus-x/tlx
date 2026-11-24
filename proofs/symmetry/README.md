# Connected symmetry certificates

The automatic symmetry pipeline supports disjoint products of full permutation
groups (2–6 model values per group, total group order at most 720) through three
connected Lean certificate emitters:

1. **`KeyedCertificate.lean` (`phase/keyed/`):**
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
2. **`EquivSymCertificate.lean` (`phase/equiv_sym/`):** closed recursive finite
   values and formulas when `KeyedCertificate` declines (key-valued and nested
   maps, multi-key records, bounded sequences/tuples, set comprehensions,
   `KSubset`, `IsInjective`).
3. **`ChooseSymCertificate.lean` (`phase/choose_sym/`):** choice-irrelevant
   `CHOOSE` specifications (unique-witness key `CHOOSE` including `ChooseOne` and
   inductively proved at-most-one active key, projected uniform/constant-value
   `CHOOSE`, and commutative-associative recursive `CHOOSE` integer set-sum folds).

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
- [MultiKeyMsgs.tla](MultiKeyMsgs.tla) ([MultiKeyMsgs.cfg](MultiKeyMsgs.cfg)):
  set and bounded sequence of two-key `[src, dst, ...]` records certified by
  `EquivSymCertificate`. 450 concrete states become 78 classes.
- [KeyValMaps.tla](KeyValMaps.tla) ([KeyValMaps.cfg](KeyValMaps.cfg)):
  key-valued map `[Proc -> Proc]`, set-valued map `[Proc -> SUBSET Proc]`, and
  nested matrix `[Proc -> [Proc -> BOOLEAN]]` certified by `EquivSymCertificate`.
  27 concrete states become 7 classes.
- [ChooseSym.tla](ChooseSym.tla) ([ChooseSym.cfg](ChooseSym.cfg)):
  inductively unique leader `CHOOSE`, projected uniform-value message `CHOOSE`
  (direct and `LET`-bound), and recursive `CHOOSE` integer set-sum fold
  (`TotalVotes`) certified by `ChooseSymCertificate`. 81 concrete states become
  22 classes.

From the repository root:

```sh
cargo build --release
./target/release/tlx check proofs/symmetry/Keyed.tla -interp
./target/release/tlx check proofs/symmetry/ScalarSlot.tla -compile
./target/release/tlx check proofs/symmetry/ProductSets.tla -compile
./target/release/tlx check proofs/symmetry/MultiKeyMsgs.tla -compile
./target/release/tlx check proofs/symmetry/KeyValMaps.tla -compile
./target/release/tlx check proofs/symmetry/ChooseSym.tla -compile
python3 proofs/check_generated.py --lean lean --negative \
  /path/to/Optimization.lean
```

Use the actual Lean path printed by the check. Automatic symmetry emits it even
without `-optimize`. Normal checking never invokes Lean.

Six theorem audits (seven when inductive `ChooseSymCertificate` obligations are
present) cover initialization/successor/observation correspondence, safety,
stuttering specifications, concrete counterexamples, deadlocks and formal
orbit-key equivalence. Negative mutation checks in `proofs/check_generated.py`
verify that Lean rejects broken key/map/slot/value renaming, order-dependent
cardinality replacement, broken `CHOOSE` uniqueness/projection/fold premises,
deleted initial/successor classes and changed reduced observations. No custom
correctness axiom is permitted.

## Trusted computing base and refusals

For `KeyedCertificate`, the theorem quantifies over key-independent core (`C`),
fixed-atom (`A`), branch-local (`W`), and payload (`V`) interpretations; for
`EquivSymCertificate` and `ChooseSymCertificate`, normalized `Init`, `Next`, and
`INVARIANT` formulas are lowered into closed finite value and formula IRs.
Across all three, source parsing and HIR lowering, forward domain and totality
checking (`sym_totality`), shape bijections, runtime group closure and
minimum-key representative selection remain trusted. Formal orbit equality is
not a proof of the Rust minimum-key implementation.

Unsupported shapes refuse cleanly: overlapping or unused groups, partial/pinned
subsets, unproved order-dependent `CHOOSE` or `SetToSeq` uses, partial/overflowing
operations rejected by `sym_totality`, and unknown or unbounded domains. Other
projection/symmetry combinations remain disabled; variable erasure is covered below.

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
