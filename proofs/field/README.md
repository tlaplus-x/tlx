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

`LedgerActionChecks.cfg` is the qualifying **unchanged external module** measurement: the
BookKeeper `LedgerChaining.tla` at the corpus-pinned `fe199dc717b5723f5308aca74eda6ab3b03917e5`,
with the upstream three clients and all four upstream invariants, and the upstream `LedgerLimit`
predicate selected as an `ACTION_CONSTRAINT` (upstream uses it as a state `CONSTRAINT`). The
configuration is held fixed across both arms; only `-optimize` differs.

```sh
scripts/fetch-external.py --repos vanlightly-bookkeeper
target/release/tlx check third_party/external/vanlightly-bookkeeper/LedgerChaining.tla \
  -config proofs/field/LedgerActionChecks.cfg -compile -workers 1 -noautosymmetry [-optimize]
```

The state reduction and the wall clock both improve at this size: 3,031,030 generated / 507,471
distinct states become 511,795 / 78,534 with
`phase-field-projection (c_state[*].ledger, c_state[*].llist, c_state[*].llist_version; ...)`. One
discarded warmup per arm and three interleaved pairs measured 11.358 s median baseline against
3.285 s median optimized (3.46x; a second independent run measured 11.098 s against 3.343 s, 3.32x),
with every run passing all four invariants.

`LedgerActionChecks2.cfg` is the two-client companion, keeping only the upstream `TypeOK`
invariant, so the same diagnostic also carries the small-graph result where the state reduction does
not pay for itself:

```sh
target/release/tlx check third_party/external/vanlightly-bookkeeper/LedgerChaining.tla \
  -config proofs/field/LedgerActionChecks2.cfg -workers 1 -noautosymmetry [-interp|-compile] [-optimize]
```

It reduces 45,545 generated / 13,058 distinct states to 16,137 / 4,350, but the wall clock rises
from 0.482 s to 0.613 s in the interpreter and from 0.511 s to 0.682 s compiled. Both results are
kept here so the trade-off is visible: state reduction alone is not a speedup guarantee.

`ActionChecks.tla` exercises the constrained action-check coverage: `ActLimit` reads the retained
control field on the source endpoint and `ActProp` reads it on the target endpoint, both through the
per-actor key. `buf` is written on entry to the busy phase and read while busy (`r[a].buf >= 0`), so
the field is dead in `idle` and live in `busy` — a dead-to-live transition, which is the frame
obligation's sharpest case and the one the negative audit's mutation must break. The projection
therefore erases `buf` in `idle` and keeps it while busy, and the action checks keep their bound
keys:

```sh
target/release/tlx check proofs/field/ActionChecks.tla -interp -workers 1 -noautosymmetry -optimize
```

It reports `phase-field-projection (r[*].buf; ...)`. With the shipped four actors, five rounds and
four buffer values it reduces 116,577 generated / 16,033 distinct states to 10,401 / 1,750. A local
comparison with the release binary, one warmup and three interleaved single-worker pairs
(`-interp -workers 1 -noautosymmetry`, only `-optimize` differing between arms, unchanged inputs
otherwise) measured 0.684 s (0.661/0.684/0.937, median) unreduced and 0.199 s
(0.196/0.199/0.201, median) reduced, a 3.44x median speedup including startup, proof emission and
projection evaluation. Both arms end with no error, and the optimized arm emits a constrained
`GeneratedField` certificate.

That certificate is also part of the required negative audit, both in the regression (the ignored
`verify_all_constrained_certificate_families_with_lean_negative` test) and directly:

```sh
proofdir=$(mktemp -d)
target/release/tlx check proofs/field/ActionChecks.tla -interp -workers 1 -noautosymmetry \
  -optimize -proofdir "$proofdir"
python3 proofs/check_generated.py --lean lean --negative "$proofdir"/*/Optimization.lean
```

The audit's field mutations include abandoning the branch transfer (forcing
`FieldRule.Model.advance`'s write branch false), which breaks `advance_commutes` on this
dead-to-live instance, alongside the read-table and frame-table mutations.

The bounded merge probe also stays bounded on initial-state fan-out: with four setup choices over
`1..N`, a state `CONSTRAINT` admitting one setup and a reachable graph of four states, the optimized
run's peak RSS at `-maxmem 32 -interp -workers 1` was 23,528 KiB against 21,732 KiB baseline at
`N = 20` (160,000 rejected initial candidates), and at `N = 3` the projection is installed and
reduces four concrete states to three. `crates/tlx-cli/tests/constrained_reductions.rs` pins both
the bounded decline and the accepting case.

A projection can be certified yet merge nothing when a `CONSTRAINT` or `ACTION_CONSTRAINT` prunes
exactly the transitions that would identify two states. For the projections this rule newly enables
with action checks, a bounded merge probe declines such a case instead of claiming a reduction:
`crates/tlx-cli/tests/constrained_reductions.rs` pins both the refusal (identical unreduced counts)
and the profitable case above.
