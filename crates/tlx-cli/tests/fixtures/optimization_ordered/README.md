# MongoDB ordered-allocation oracle

The source is MongoDB's `src/mongo/tla_plus/Sharding/TxnsCollectionIncarnation/TxnsCollectionIncarnation.tla`
at commit `1c1e012583df064096c951d5932008ea23333aac`:

- Source SHA256: `da02eb16aea2db0de9f7e8529678f86cd5a24baeeb63100dbd67bbb3fd8ef286`.
- TLC jar SHA256: `b490f45c1de08e4ff9753259a00338981b9cf464f01ca9e9cd5f19f33cf0bb92`.
- Oracle collected locally on 2026-10-11. The output retains the version, verdict,
  final counts and depth; machine paths, progress and timings are omitted.

`Unbounded.cfg` uses the unchanged upstream `Spec` with two shards, one namespace,
one key, one transaction and two statements. It retains the two selected upstream
invariants and the action safety property. There is no DDL, time, history-length
or transaction-completion constraint, no symmetry, and no liveness check.
Before any transaction starts, moving the primary between shards can continue
indefinitely, increasing `clusterTime` and adding a catalog entry every time.
The original graph is therefore infinite under mathematical integer semantics.

`GeneralIncarnation.tla` is an independently authored oracle VIEW. It retains the
catalog at every timestamp appearing outside the catalog, plus the fixed anchor 1,
and ranks positive times and UUIDs after collection. It is intentionally more
conservative than a hand-tuned VIEW that keeps only current/snapshot versions.
The configuration differs from `Unbounded.cfg` only by `VIEW FiniteView`.

TLC completed with 69,456 generated / 19,048 distinct states, depth 16, and no
safety errors. This independent VIEW remains a future certificate coverage target.
The automatic ordered-allocation rule currently refuses this configuration: its
connected certificate does not yet cover nested identifiers, multiple families,
version collection or the selected action property. The ignored Rust test
`external_mongodb_is_refused_until_its_reduction_has_a_certificate` checks this
refusal without starting an unbounded search. State counts from the independent
VIEW do not establish the soundness of the automatic reduction.

To refresh the oracle, copy the pinned source beside these fixtures in a scratch
directory, then run Java 21 with the pinned jar:

```sh
java -Xmx1g -cp /absolute/path/to/tla2tools.jar tlc2.TLC -workers 1 -config GeneralIncarnation.cfg GeneralIncarnation
```

Run the automatic check from the repository root:

```sh
cargo test -p tlx-cli --profile test-release --test optimization_ordered external_mongodb -- --ignored
```

The accepted scalar-allocation subset generates a connected rule-model certificate.
`HiddenAnchor.tla` is a small regression from proof review: forgetting `1` inside
`Cardinality({clock, 1})` merged states with different successor behavior. TLC
finds the violation at `clock = 3, bad = TRUE` (3 generated / 3 distinct states).
The CLI test requires that same concrete failure with optimization in every tier.
The broader MongoDB reduction remains refused until its proof is implemented.
