# Ordered-allocation proof checks

Accepted ordered-allocation applications generate a connected parametric rule-model
certificate. The compiler lowers the actual initial relation, branch increments,
guards and observations; independent HIR leaves cannot access the frontier.
[OrderedCertificate.lean](../../crates/tlx-sema/src/optimize/OrderedCertificate.lean)
constructs initialization, successor and observation correspondence, then derives
safety, counterexample lifting and deadlock preservation. A further theorem connects
the formal projection to the rank key's equivalence classes.

The certified subset currently has one scalar frontier, one retained initial anchor,
literal nonnegative increments and independent remaining state. It does not cover
nested identifier copies, multiple allocation families or version collection. Those
ordered-allocation applications are refused, including the MongoDB incarnation model.
Source lowering, totality, runtime execution and symmetry composition remain trusted.
See [the rule's scope](../../docs/optimization.md#ordered-allocation-and-live-versions).

Run verification explicitly after a check emits `Optimization.lean`:

```sh
python3 proofs/check_generated.py --lean /path/to/lean --negative /path/to/Optimization.lean
```

This checks the exact generated artifact at trust level zero, treats warnings as
errors and audits six theorems. Negative checks require rejection of removing the
anchor, failing to advance the reduced phase and changing the reduced observation.
Ordinary model checking does not invoke Lean. Lean 4.34.1 is the tested version;
no Mathlib, Lake project, network or cloud machine is required.

## Why the broader rule was restricted

Proof review found that the earlier analysis lost the fixed literal inside
`Cardinality({clock, 1})`. The [regression specification](../../crates/tlx-cli/tests/fixtures/optimization_ordered/HiddenAnchor.tla)
initializes `clock = 1, bad = FALSE`, increments the clock, and sets `bad` when the
old set has cardinality two. TLC finds a violation at `clock = 3`; the former key
merged the first two states and incorrectly reported success. The analysis now
retains anchors through intermediate consumers. The accepted regression generates
a connected certificate and finds the TLC counterexample across execution tiers.

[HiddenAnchor.lean](HiddenAnchor.lean) is a standalone, manually written disproof
of the former key. It proves that the first successor is merged, that the concrete
second successor violates safety, and that **no reduced relation** can meet the
successor-correspondence obligation for that key. All three theorems use no axioms.
It is separate from the compiler-generated certificate for the repaired projection.
Run it explicitly from the repository root:

```sh
lean -t0 -DwarningAsError=true -R proofs/ordered proofs/ordered/HiddenAnchor.lean
```
