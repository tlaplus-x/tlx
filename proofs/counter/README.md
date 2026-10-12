# Certified counter export

`Counter.tla` has two unbounded natural counters. Their exact magnitudes are only
used by the guards `x >= 3` and `y >= 5`. `GrowX` alone gives infinitely many
mathematical source states. Export retains 0, 1, 2 and a saturated 3 for `x`, and
0 through a saturated 5 for `y`, giving 24 reachable states. It also proves
`fixed = 7`, simplifies its uses and deletes an impossible action.

```sh
target/release/tlx optimize proofs/counter/Counter.tla -output /tmp/tlx-counter-proof
target/release/tlx check /tmp/tlx-counter-proof/Optimized.tla -compile -tlc
python3 proofs/check_generated.py --lean /path/to/lean --negative /tmp/tlx-counter-proof/Optimization.lean
```

The destination must be new. Export always writes Lean but never invokes it.
The finite model generates 59 states and finds 24 distinct states in interpreter
and paranoid compiled checking. There is no completed full-graph timing of the
unbounded source, so this example does not claim a measured speedup ratio.

The emitted file contains the actual IR before and after every committed pass,
its rule name, its projection and a connected certificate. Constant propagation
first proves the required singleton domain inductive from Init and every source
action. Lean arithmetic proves the guard, update and observation correspondence;
no caller supplies a preservation hypothesis. Dead actions are removed through
explicit source-to-result action indices. The certificates then compose.

The final safety theorem relates the unrestricted source and result IR. It also
covers stuttering safety, concrete counterexample existence and reachable
plain-Next deadlocks. Each pass's stronger forward/backward lemmas apply to every
state in its proved domain. Restricting the composed certificate to reachable
systems accommodates inductive constant propagation without assuming invariants
selected for checking. The command still requires deadlock checking disabled.

Source/HIR lowering, TLA+ emission and execution remain trusted. Generated traces
contain quotient representatives; the exporter does not reconstruct concrete
traces automatically. The existence proof does not certify a model-checker
verdict or prove the input safe. Arithmetic is mathematical natural arithmetic;
eventual machine overflow is outside the export contract.
