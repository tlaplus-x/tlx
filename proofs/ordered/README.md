# Ordered-allocation proof checks

Accepted ordered-allocation applications generate a connected parametric rule-model
certificate. The compiler lowers the actual initial relation, branch increments,
guards and observations; independent HIR leaves cannot access the frontier.
[OrderedCertificate.lean](../../crates/tlx-sema/src/optimize/OrderedCertificate.lean)
constructs initialization, successor and observation correspondence, then derives
safety, counterexample lifting and deadlock preservation. A further theorem connects
the formal projection to the rank key's equivalence classes.

The scalar subset has one frontier, one initial anchor, literal nonnegative increments
and independent remaining state. The nested subset supports several independent families,
fixed records/tuples/maps, conditional transfers, copying old identifiers and fresh offsets
within a branch's increment. Positive values use relative ranks; nonpositive sentinels remain
exact. One immutable table can be collected when its payloads contain no allocation
identifiers and all reads use current live roots. Dynamic shapes, colored keys/sets,
cross-family comparisons and broader version uses are refused, including the MongoDB
incarnation model. Symmetry composition is excluded.
Source lowering, fixed representations, inferred domains, independent leaf semantics,
totality and runtime execution remain trusted.
See [the rule's scope](../../docs/optimization.md#ordered-allocation-and-live-versions).

Run verification explicitly after a check emits `Optimization.lean`:

```sh
python3 proofs/check_generated.py --lean /path/to/lean --negative /path/to/Optimization.lean
```

This checks the exact generated artifact at trust level zero, treats warnings as
errors and audits six theorems. Negative checks require rejection of removing the
anchor, failing to advance the reduced phase and changing the reduced observation.
Nested certificates additionally reject losing slot transfers or exact nonpositive sentinels,
and removing initialization or successor edges. Ordinary model checking does not invoke Lean. Lean 4.34.1 is the tested version;
no Mathlib, Lake project, network or cloud machine is required.

## Nested allocation example

[Nested.tla](Nested.tla) stores two independently allocated identifiers in records inside
one-element tuples inside an actor map. Actions allocate, copy and reset records. One stored
identifier starts at `-1`; another starts at `0` and is assigned only on its first reservation.
Both frontiers grow without bound. With [Nested.cfg](Nested.cfg), the certified key completes
with 63 generated / 13 distinct states in interpreted and paranoid compiled checking:

```sh
target/release/tlx check proofs/ordered/Nested.tla -optimize -noautosymmetry -interp
TLX_PARANOID=1 target/release/tlx check proofs/ordered/Nested.tla -optimize -noautosymmetry -compile
```

The generated certificate exposes both families, every numeric path, the actual conditional
transfers and all selected observations. Its six theorem audits include equality of formal
rank vectors iff quotient keys agree. It does not prove the Rust structural walk itself.
A diagnostic variant that retains a reservation counter and stops allocating after three
reservations has 187 generated / 54 distinct states in TLC and unreduced tlx, versus 111 / 29
with optimization. This bounded variant is oracle evidence, not the unbounded source model.
Runtime regressions also check concrete safety failures and deadlocks across execution tiers.

## Immutable version collection

[LiveVersions.tla](LiveVersions.tla) publishes an unbounded sequence of immutable versions.
Two actors hold old version identifiers. Their reads affect guards, retained state and the
next published payload. The compiler keeps the entries reachable through those identifiers,
the current frontier and fixed anchors, then ranks their keys. With
[LiveVersions.cfg](LiveVersions.cfg), interpreted and paranoid compiled checks complete
with 552 generated / 89 distinct states:

```sh
target/release/tlx check proofs/ordered/LiveVersions.tla -optimize -noautosymmetry -interp
TLX_PARANOID=1 target/release/tlx check proofs/ordered/LiveVersions.tla -optimize -noautosymmetry -compile
```

The generated `LiveRule.Model` contains actual initial payloads, branch deltas, numeric
transfers, lookup feedback, appended payloads and observations. The source table grows;
the fingerprint keeps only its live graph. Future actions can copy current roots or allocate
a fresh key, so they cannot resurrect an unretained entry. The shared proof establishes this
property rather than assuming that garbage collection preserves transitions. Its six theorem
audits include equality of the retained-table/rank key iff the quotient agrees. Six mutations
reject losing live old values, inserting at the wrong key, omitting payloads from the key,
dropping initialization or successors, and changing observations.

Table initialization is a singleton at the positive frontier. Its frontier changes by zero
or one, and entries are immutable. Payloads are allocation-identifier-free and can depend on
retained state and explicit current-root reads; source lowering and lookup totality remain
trusted. Raw table escapes, enumeration, primed reads, arbitrary computed old keys, dynamic
colored shapes and identifier-containing payloads refuse. The Rust table filter and structural
key implementation also remain trusted. The theorem covers state observations and deadlocks,
not temporal properties or composition with symmetry.

A bounded diagnostic retaining a publication counter with limit four matches TLC and plain
tlx at 603 generated / 108 distinct states; optimized interpreted/paranoid execution uses
559 / 98. This is a bounded oracle check, separate from the unbounded source above.

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
