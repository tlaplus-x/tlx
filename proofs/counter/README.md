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

## In-place threshold-counter checking (`ThresholdProtocol.tla`)

`ThresholdProtocol.tla` combines retained protocol state (`phase`, and the
bounded step variable `step`) with a scalar monotone/resettable counter
(`retries`) and a fixed-domain per-actor counter map
(`failures \in [Actor -> Nat]`) observed only through threshold comparisons
(`>= 2`, `>= 3`). Under `tlx check -optimize`, `tlx` installs an in-place
threshold-counter saturation `VIEW` (`min(retries, 3)` and
`[a \in DOMAIN failures |-> min(failures[a], 3)]`) backed by
`ThresholdCounterCertificate.lean` (`GeneratedThresholdCounter`), while keeping
concrete transitions, deadlock checks, and un-capped counterexample traces intact:

```sh
target/release/tlx check proofs/counter/ThresholdProtocol.tla -optimize -noautosymmetry -proofdir /tmp/tlx-threshold-proof
python3 proofs/check_generated.py --lean /path/to/lean --negative /tmp/tlx-threshold-proof/Optimization.lean
```

The un-reduced search reaches 46,407 distinct states; the projected search reaches
1,727 (`-workers 1`, interpreter and compiled tiers agree). `step` is a candidate
counter too, but its own `step < 30` guard already bounds it, so the profitability
gate keeps it in the retained state and only `retries` and `failures` are
saturated. The bounded merge probe additionally requires a merged admitted state,
so a saturation whose caps no reachable value exceeds is declined instead of
installing a `VIEW` that never merges.

`python3 proofs/check_generated.py` runs this specification by default and checks
the generated `GeneratedThresholdCounter` file against the standard axioms,
rejecting the off-by-one-cap, dropped-increment, discarded-guard-feedback and
changed-observation mutations.

### Composition with automatic symmetry (`ThresholdSymCertificate.lean`)

When `Actor` is configured as a set of model values (for example
`Actor = {a1, a2, a3}`) and `-optimize` runs with automatic symmetry enabled,
`threshold-counter-projection` composes directly with certified equivariant
symmetry via `ThresholdSymCertificate.lean` (`GeneratedThresholdSymmetry`,
unconstrained and constrained, reusing `OrbitQuotient.lean`) over one shared
concrete source model. Symmetric-group counter slots carry kernel-checked
uniform caps (`capUniform : by decide`) so `saturate` commutes with `GroupPerm`,
and `tlx` projects before orbit canonicalization while reconstructing un-capped
concrete counterexample traces. Both unconstrained and constrained
`GeneratedThresholdSymmetry` certificates are audited by
`python3 proofs/check_generated.py --lean lean --negative`, rejecting asymmetric
per-key counter caps, weakened `Cmp.reqCap`, dropped `Transfer.add`, broken slot
renamings, and disconnected intermediate models.

### External evidence

`scripts/fetch-deps.sh` installs the upstream tlaplus/Examples corpus. The
upstream `DieHard/MCDieHardest.cfg` is the upstream configuration of the
unchanged upstream `DieHardest.tla`: its monotone step counters `s1` and `s2`
are incremented on every interleaved instance step and are read by no accepted
predicate, so both saturate at `0`. `NotSolved` is still violated and the
reconstructed trace keeps the concrete step counts:

```sh
target/release/tlx check third_party/Examples/specifications/DieHard/MCDieHardest.tla -workers 1
target/release/tlx check third_party/Examples/specifications/DieHard/MCDieHardest.tla -optimize -workers 1
```

The un-reduced search generates 140,897 states and 11,566 distinct states; the
projected search generates 12,071 and 813 (14.2x fewer distinct states). The
whole run takes under half a second, so the fixed loading, compilation,
merge-probe and certificate-emission cost exceeds the search savings at that
size (median 0.44 s unreduced vs 0.54 s projected over five interleaved pairs).

`MCDieHardestScale.tla` fixes the same unchanged `DieHardest.tla` at larger jug
capacities (as an own wrapper module, like the upstream model-checking wrapper)
so the search dominates the fixed cost:

```sh
target/release/tlx check proofs/counter/MCDieHardestScale.tla -I third_party/Examples/specifications/DieHard -workers 1
target/release/tlx check proofs/counter/MCDieHardestScale.tla -I third_party/Examples/specifications/DieHard -optimize -workers 1
```

Interleaved pairs of one worker of a release build on a shared 32-core Linux
machine, one discarded warm-up per mode and five measured pairs:

| Configuration | Distinct (unreduced) | Distinct (projected) | Median wall (unreduced) | Median wall (projected) | Ratio |
| --- | ---: | ---: | ---: | ---: | ---: |
| upstream `MCDieHardest.cfg` | 11,566 | 813 | 0.44 s | 0.54 s | 0.8x |
| `MCDieHardestScale.cfg` | 3,722,654 | 45,574 | 19.95 s | 2.28 s | 8.75x |

A survey of the fetched `third_party/Examples` and `external` corpora found no
model whose counters are both read only through threshold comparisons and
unbounded above their caps: the monotone counters there are either bounded
directly by a comparison (so the profitability gate refuses them) or read through
cross-counter comparisons and decrements (which the certificate refuses). The
non-zero cap path is covered by `ThresholdProtocol.tla`, the cross-tier tests and
the negative mutations above.
