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
observations. Five theorems cover the certificate, safety, safety with stuttering,
counterexample lifting and deadlocks. No preservation premises or custom
correctness axioms are supplied. Negative checks break ticks, resets, deletion,
deadline strictness and the reduced safety predicate; Lean must reject them.

The proof concerns the lowered rule model. Source/HIR translation, domain and
partial-read analysis, runtime VIEW construction and execution remain trusted.
Payloads and timestamp presence stay exact. Semantic leaves cannot access absolute
time or uncapped ages. Age/history composition and retained updates containing
age-filtered sets remain outside the certified subset.

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
