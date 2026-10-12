# Connected sequence-length certificates

The compiler emits a `GeneratedLength` model with the actual initial sequences,
append/reset/frame transfers, guards, retained updates and observations. Semantic
leaves receive retained state and current lengths, never forgotten sequence contents.
Multiple sequences can be reduced together, including transfers that depend on their
current lengths. The shared proof establishes initialization, successor correspondence
from every representative, safety equivalence, concrete counterexample lifting and
deadlock preservation. Next-state length inputs currently refuse the certificate.

```sh
./target/release/tlx check proofs/length/Length.tla -interp -optimize -noautosymmetry
python3 proofs/check_generated.py --negative .tlx-proofs/run-PID-0/Optimization.lean
```

`Length.tla` includes two sequences, a conditional append/reset, and a retained update
that reads a length. Its ordinary graph is finite because growth is bounded. A separate
unbounded log remains unbounded after this rule: exact length is retained. The rule
reduces different contents of the same length, not the number of possible lengths.

Source lowering, totality/domain inference, semantic-leaf interpretation and runtime
VIEW execution remain trusted. Ordinary checking writes Lean without invoking it.

The optional `ReplicatedLogBounded.tla` wrapper imports the unchanged external
`Examples/specifications/FiniteMonotonic/ReplicatedLog.tla` and limits writes to
length 22. It selects `TypeOK` and `Safety`, with one node and two transaction
values. This bounded safety diagnostic is distinct from the upstream configuration
that selects liveness and a handwritten reduction. The original model remains
unbounded after exact-length projection.

```sh
./target/release/tlx check proofs/length/ReplicatedLogBounded.tla -I third_party/Examples/specifications/FiniteMonotonic -compile -optimize -noautosymmetry
```
