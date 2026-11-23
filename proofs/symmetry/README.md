# Connected keyed-symmetry certificates

`Keyed.tla` contains two maps over the same process set, record-field writes,
whole-payload resets, conditional values and nested key quantification. The
compiler emits the actual guards, ordered payload reads, key equalities and
writes in the keyed-state rule IR. All moved identifiers are map keys; payloads
and retained state contain none.

From the repository root:

```sh
cargo build --release
./target/release/tlx check proofs/symmetry/Keyed.tla -interp
./target/release/tlx check proofs/symmetry/Keyed.tla -compile
./target/release/tlx check proofs/symmetry/Keyed.tla -tlc -interp
python3 proofs/check_generated.py --lean lean --negative \
  /path/to/Optimization.lean
```

Use the actual Lean path printed by the check. Automatic symmetry emits it even
without the projection option. Normal checking never invokes Lean. The example
has 64 concrete states and 20 permutation classes.

Six theorem audits cover initialization/successor/observation correspondence,
safety, stuttering specifications, concrete counterexamples, deadlocks and
formal orbit-key equivalence. Mutation checks must reject missing key renaming,
missing map permutation, deleted initial/successor classes and changed reduced
observations. No custom correctness axiom is permitted.

The theorem quantifies over key-independent core and payload interpretations;
key operations themselves are explicit. Source normalization, inferred domains,
leaf interpretation, totality, group closure and runtime representative selection
remain trusted. Formal orbit equality is not a proof of the Rust minimum-key
implementation. Unsupported shapes, including identifiers stored in payloads,
primed map inputs and multiple potentially aliasing writers to one map, refuse.
Other projection/symmetry combinations remain disabled; variable erasure is covered below.

The unchanged external transaction-commit specification in the TLA+ Examples
corpus is also covered:

```sh
./target/release/tlx check \
  third_party/Examples/specifications/transaction_commit/TCommit.tla \
  -config proofs/symmetry/TCommit.cfg
```

With six resource managers, TLC and unreduced tlx find 792 distinct states;
certified symmetry finds 34. Both upstream invariants remain selected. This is
correctness coverage, not a timing claim for this small model.

`KeyedLarge.cfg` uses four processes and a limit of 30: 1,048,576 concrete
states become 52,360 permutation classes. To compare the same release binary,
run with this configuration both normally and with `-noautosymmetry`; use
repeated, interleaved runs after warming both configurations.

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
actual hidden transfers, keyed guards and map writes with one common branch choice.
Its intermediate erasure and final orbit certificates describe the same model.
Seven audits cover both certificates, safety, stuttering, concrete counterexamples,
deadlocks and formal orbit-key equivalence. Six mutations reject broken key/map
renaming, missing quotient initialization/successors, removed concrete hidden
successors and changed reduced observations. Runtime tests retain concrete snapshot
values in failing and deadlocking traces across execution tiers.

The installed projection must be the exact retained-variable tuple. Unknown or
partial hidden updates, reads of omitted variables, unsupported keyed shapes and
other projection kinds refuse composition. Existing user VIEW/SYMMETRY declarations
retain the TLC path. Source lowering, domain/totality inference, independent semantic
leaves, group closure and runtime projection/canonicalization remain trusted.
