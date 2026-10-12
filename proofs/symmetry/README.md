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
  .tlx-proofs/run-PID-N/Optimization.lean
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
Projection composition still requires its own connected certificate.

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
