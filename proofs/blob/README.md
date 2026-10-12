# Blob history optimization proof

[Blob.lean](Blob.lean) constructs a Lean certificate for the history reduction of
the external `database-blob/working/working.tla` model. It proves preservation of
the selected safety observation, successor correspondence in both directions,
lifting of reduced counterexamples to concrete reachable states, and deadlock
preservation. The certificate is constructed from the model definitions; it is
not an assumed premise of the final theorem.

## Run explicitly

Install Lean **4.34.1** and obtain the external corpus using the setup in
[testing.md](../../docs/testing.md#6-corpus-differential-tests). From the repository
root, run:

```sh
python3 proofs/blob/check.py
```

Use `--lean /path/to/lean` to select an executable and `--report FILE` to retain
a JSON receipt. The script does not install Lean, access the network, or use
cloud machines. It checks input hashes, builds the shared rules in a fresh
temporary directory, checks the model with Lean's trust level zero, treats
warnings as errors, and audits the final theorems' axiom dependencies.

The negative test deliberately removes the previous consistency bit from the
summary update. Lean must reject the resulting preservation proof. A successful
check reports only the standard logical axioms `propext`, `Classical.choice`,
and `Quot.sound`; no placeholder proof, custom correctness axiom or native
decision procedure is used. Judge a run by its exit status and matching receipt
hashes, not by the presence of a receipt from an earlier run.

This is an explicitly invoked proof check. Ordinary opt-in model checking still
emits Lean without running it, as specified in
[configuration.md](../../docs/configuration.md).

## Inputs and source correspondence

[inputs.json](inputs.json) pins the source and configuration bytes. The source is
Elliot Swart's MIT-licensed
[working blob model at the pinned upstream revision](https://github.com/ElliotSwart/pragmaticformalmodeling/blob/ea86b1b5852d49d60d82d944e4807774392e1414/database-blob/working/working.tla).
[Unbounded.cfg](Unbounded.cfg) is our configuration: two servers, one user, two
metadata values, two images and two UUIDs, selecting `TypeOk` and `ConsistentReads`.
It has no operation-count constraint and no selected temporal property. It is
not the upstream benchmark configuration.

The Lean model uses separate finite inductive types with the configured model
value names. `none` represents the string `"UNSET"`; `some` represents a member
of the corresponding configured set. Records and total functions over the exact
finite domains encode the source's structural `TypeOk` conditions. Those types
are closed under the explicitly formalized initial state and all eight actions.
`ConsistentReads` is never assumed.

`Core` retains the database, blob store and every server field. `CoreStep`
formalizes each source action, including its guards, nondeterministic choices,
record updates and unchanged fields:

| Source action | Core effect | History effect |
|---|---|---|
| `StartWrite` | Set the server's user, metadata, image and phase | Append the chosen WRITE |
| `WriteBlob` | Fill an unused UUID slot and record its ID at the server | Unchanged |
| `WriteMetadataAndReturn` | Update the user's database record and reset the server | Unchanged |
| `FailWrite` | Reset a writing server | Unchanged |
| `StartRead` | Set the server's user and phase | Unchanged |
| `ReadMetadata` | Read a present database record into the server | Unchanged |
| `ReadMetadataAndReturnEmpty` | Reset the reading server | Append READ with unset metadata/image |
| `ReadBlobAndReturn` | Reset the reading server | Append READ with the looked-up blob image |

None of those action guards reads the history. The optional event in `CoreStep`
is its complete effect on the history. The additional `some` witnesses make
partial TLA+ function lookups explicit. `reachable_core_wf`,
`user_lookup_defined` and `image_lookup_defined` prove these witnesses exist
whenever the corresponding source action can read a function on a reachable
state, so these witnesses do not silently disable a reachable action.

`At` models sequence positions using zero-based indices. `at_exists`, `at_unique`
and `at_bound` establish its index semantics. `seenPrefix` includes precisely
the positions up to the current index, corresponding to TLA+'s `1..i`.
`eventOK` preserves the source's WRITE matching by user, metadata and image,
its empty-read exception, and its treatment of WRITE entries.

## What is proved

The projection retains `Core` and replaces the history with:

1. The set of all operation values seen so far.
2. The truth value of the indexed prefix consistency predicate.

This is the same key as the generated history VIEW, up to record/tuple grouping
and set extensionality. The explicit empty-history disjunct in the source is
handled by `consistent_iff_valid`.

Appending an event leaves every old prefix obligation unchanged. Its new
obligation depends on the appended event and the old seen set plus that event.
`indexed_append` proves this from the indexed observation; `append_commutes`
and `advance_commutes` connect it to the summary update. A previous failure
remains false even if a matching WRITE arrives later.

`certificate` supplies initialization correspondence, successor lifting for
every concrete representative, and observation equivalence. The shared rule
library then yields:

- `optimization_correct`: concrete and reduced reachable states agree on
  whether every state satisfies `ConsistentReads`.
- `specification_correct`: the same result with the stuttering steps allowed
  by the source's `[][Next]_vars`.
- `counterexample_lifts`: every reduced reachable failure has a concrete
  reachable failure with the same projection.
- `deadlock_preserved`: a concrete representative has no `Next` successor
  exactly when its projection has no reduced successor.

There are 36 values in the typed operation alphabet. Thus the seen-set/bit
representation has at most `2^37` different values, independently of history
length; this is a mathematical upper bound, not the reachable-state count.
The retained core is also finite. The proof of preservation does not impose
a bound on the number of source operations.

## Trust boundary

The correspondence between the TLA+ source and `Blob.lean` is **manually
reviewed**, not established by a verified parser or generated semantic
translation. Hash checks prevent accidental reuse after input changes; hashes
do not prove that correspondence. This is a model-specific formalization and
certificate, separate from the automatically generated parametric rule-IR certificate.

The proof does not verify the Rust rule recognizer, native compiler, runtime
fingerprinting, trace reconstruction implementation or symmetry composition.
It proves preservation, not the blob protocol's safety from first principles,
and it does not cover configurations that observe exact history length, select
liveness properties, or change the configured domains. Automatic verification of
the TLA+-to-rule-IR translation remains future work.

## Automatic compiler certificates

The compiler now generates a separate parametric history rule-IR certificate for this
configuration. It derives the prefix predicate and history transfers from normalized
HIR; history-free protocol expressions remain universal semantic parameters. This
manual proof additionally spells out all eight concrete actions and reachable lookup
definedness. See [automatic coverage](../../docs/optimization.md#lean-output-for-checking)
for the distinction and the explicit generated-proof verification command. Neither
form of verification runs during ordinary model checking.
