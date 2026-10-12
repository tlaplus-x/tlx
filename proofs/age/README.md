# Relative-age certificate example

`Age.tla` has an unbounded logical clock and a map containing either an empty
record or a creation timestamp. Deletion requires age at least two. Optimized
checking finishes with four states: empty, age zero, age one, and age two-or-more.
The original clock remains in concrete execution and counterexample traces.

From the repository root:

```sh
cargo build -p tlx-cli --release
./target/release/tlx check proofs/age/Age.tla -interp -optimize -noautosymmetry
```

The command prints a fresh `.tlx-proofs/run-PID-N/Optimization.lean` path. Verify
that actual output explicitly:

```sh
python3 proofs/check_generated.py --lean /path/to/lean --negative /path/to/Optimization.lean
```

The generated `GeneratedAge` namespace instantiates `AgeCertificate.lean` with
actual map slots, caps, seeds, ticks, reset/delete updates, deadline guards and
observations. Five preservation theorems cover the certificate, safety, safety
with stuttering, counterexample lifting and deadlocks. Two selection lemmas
connect finite filtering to its exact selected keys; two binding lemmas connect
Boolean predicates to the exact decisions received by dependent consumers. No
preservation premises or custom correctness axioms are supplied. Negative checks break ticks, resets,
deletion, deadline strictness, filter decisions, selected keys, Boolean arguments
and the reduced safety predicate; Lean must reject them.

The proof concerns the lowered rule model. Source/HIR translation, domain and
partial-read analysis, runtime VIEW construction and execution remain trusted.
Payloads and timestamp presence stay exact. Semantic leaves cannot access absolute
time or uncapped ages. Finite age-filtered sets and constant-domain quantified
deadline checks are supported. Dynamic filter domains and next-state age
consumers remain outside the certified subset.

`Bounded.tla` adds a retained budget of 120 transitions so both modes terminate.
It is a finite diagnostic wrapper, not the unbounded model's configuration. Its
302,264 concrete states (also checked by TLC) reduce to 478 states:

```sh
./target/release/tlx check proofs/age/Bounded.tla -interp -noautosymmetry
./target/release/tlx check proofs/age/Bounded.tla -interp -optimize -noautosymmetry
```

TLC independently checks the finite baseline:

```sh
java -cp third_party/tla2tools.jar tlc2.TLC -workers 1 proofs/age/Bounded.tla
```

Use release binaries and repeated interleaved runs for timing. Include proof
emission in optimized timing, keep warm-ups separate, and retain raw logs. A
finite-wrapper speedup does not establish completion of an external model.

`FilteredAge.tla` additionally stores the set of expired entries and checks a
quantified deadline observation. Its clock is unbounded; optimized checking
completes with eight states. Generated `Test.select` terms explicitly construct
the selected key positions before the retained update consumes them. The
additional selection lemmas and negative tests cover this filter boundary.

```sh
./target/release/tlx check proofs/age/FilteredAge.tla -interp -optimize -noautosymmetry
```

`AgeHistory.tla` combines an unbounded clock, an append-only log, a finite
age-filtered set and a prefix-order invariant. Its combined certificate uses
the same branch witness for age and history updates. Optimized checking finishes
with 15 states; both unbounded components are reduced:

```sh
./target/release/tlx check proofs/age/AgeHistory.tla -interp -optimize -noautosymmetry
```

The generated `GeneratedAgeHistory` certificate proves initialization, successor
correspondence, selected observations, counterexample lifting and deadlocks.
The verifier audits nine theorems and rejects thirteen broken variants, including
forgetting prior prefix failures and dropping the history transfer. Source
lowering, leaf interpretation, domain/totality analysis and runtime execution
remain trusted. History events and transfer conditions cannot depend on forgotten
ages. Supported summary predicates can control guards, retained updates and history
transfers. `HistoryFeedback.tla` exercises all three with an unbounded clock and log:

```sh
./target/release/tlx check proofs/age/HistoryFeedback.tla -interp -optimize -noautosymmetry
```

`MixedHistory.tla` has two timestamp slots and computes a retained set with a
history-dependent conditional:

```tla
Chosen == IF Ready /\ history # <<>> THEN Expired ELSE {}
```

`Expired` filters the slots by age. Both its selected set and the history
predicates' Boolean values are explicit arguments to the emitted consumer.
The original clock and history are unbounded; combined reduction finishes with
113 states. The same lowering handles observations, multiple filtered sets,
and fixed-domain filters whose predicates inspect history summaries.

```sh
./target/release/tlx check proofs/age/MixedHistory.tla -interp -optimize -noautosymmetry
```

History-dependent timestamp-map transfers, dynamic filter domains, next-state
inputs and multiple-history composition remain unsupported. Source/HIR lowering,
leaf interpretation and runtime execution are still trusted.

For the separately fetched external cleaner, `Cleaner.cfg` selects singleton
constants and `TypeOk`. The original specification completes without a transition
budget at 820 distinct / 3,083 generated states:

```sh
./target/release/tlx check third_party/external/pragmatic/database-blob/storage-cleaner-improved/storagecleanerimproved.tla -config proofs/age/Cleaner.cfg -interp -optimize -noautosymmetry
```

Adding `ConsistentReads` still reports the model's genuine invariant violation.
The successful `TypeOk` check does not establish that property.
