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
safety errors. Automatic `-optimize` checking of the original source must match
these counts in both interpreter and compiled execution. The ignored Rust test
`external_mongodb_incarnations_match_independent_tlc_view` enforces this when the
pinned local external corpus is installed, with a 600-second deadline per run.
These are correctness/count checks, not repeated performance measurements.
TLC agreement checks execution of the quotient, not its semantic proof.

To refresh the oracle, copy the pinned source beside these fixtures in a scratch
directory, then run Java 21 with the pinned jar:

```sh
java -Xmx1g -cp /absolute/path/to/tla2tools.jar tlc2.TLC -workers 1 -config GeneralIncarnation.cfg GeneralIncarnation
```

Run the automatic check from the repository root:

```sh
cargo test -p tlx-cli --profile test-release --test optimization_ordered external_mongodb -- --ignored
```

The generated Lean contains shared algebra and the actual structural projection
plan. It is not a model certificate. Lean verification is not part of these tests.

On 2026-10-11, freshly generated output passed Lean 4.34.1 with trust level zero
and warnings treated as errors. An axiom audit of all 19 embedded theorems found
only standard logical axioms. Two deliberate changes were rejected: dropping a
retained lookup and allowing a zero offset in strict fresh allocation. This
checks the shared algebra; source lowering, provenance analysis and the runtime
projection remain trusted. To check a freshly emitted artifact explicitly:

```sh
lean -t0 -DwarningAsError=true -R /path/to/proof-directory /path/to/proof-directory/Optimization.lean
```
