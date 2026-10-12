# Phase-dependent record fields

`Phase.tla` overwrites `data` when starting work. Its old value is irrelevant while
idle, but the busy phase reads it. The certified projection merges the two idle
states: four concrete states become three projected states. Fixed maps apply the
same mask independently to each actor; two actors reduce 16 states to nine.

```sh
target/release/tlx check proofs/field/Phase.tla -interp -optimize -noautosymmetry
```

The command prints its generated `Optimization.lean` path. Verify it explicitly:

```sh
python3 proofs/check_generated.py --lean /path/to/lean --negative /printed/path/Optimization.lean
```

The rule IR retains phases, other variables, actor choices, field writes and all
recorded reads. Generated finite liveness tables are checked by Lean: actor reads
must be live in the source phase, other-actor and observation reads must always
be live, and newly live fields must be overwritten or already live before the
transition. The resulting certificate proves initialization and successor
correspondence from every representative, observation preservation, concrete
counterexample lifting and plain-Next deadlock preservation. Ordinary optimized
checking generates the proof without invoking Lean.

HIR lowering, inferred domains/totality, independent leaf interpretation and
runtime VIEW execution remain trusted. The certificate currently requires
constant initial phases and excludes primed projected reads and symmetry
composition. Exact lengths and keys remain retained. Field erasure alone does
not guarantee a finite state space.

`BoundedLedger.tla` imports the unchanged external BookKeeper `LedgerChaining`
model and adds a 30-transition limit. Its default configuration uses two clients
and only the upstream `TypeOK` invariant, so it can enumerate the complete graph:

```sh
target/release/tlx check proofs/field/BoundedLedger.tla -I third_party/external/vanlightly-bookkeeper -compile -optimize -noautosymmetry
```

This diagnostic reduces 1,260,159 states to 632,121. A local release comparison
with one warmup and three interleaved pairs measured medians of 8.36s and 7.91s
(1.06x). A smaller 24-transition comparison reduced states but was slower, so
state reduction alone is not a speedup guarantee. These local measurements include
startup, proof emission and projection evaluation.

`BoundedLedgerSafety.cfg` instead selects all four upstream invariants. Both
baseline and optimized checking find the existing `OnlyOneLedgerOpenAtATime`
failure at transition 17. The type-only timing configuration does not establish
those safety properties. Neither configuration proves the original unbounded
model finite. The wrapper also differs from the upstream `LedgerLimit` constraint.
