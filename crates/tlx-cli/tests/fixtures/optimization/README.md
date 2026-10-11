# Optimization TLC fixtures

These bounded models cover constant propagation plus dead-action cleanup, empty next relations
with safe and failing initial invariants, a successor violation, and a reset whose abstraction
reduces two states to one. Original and generated models must have matching safety verdicts;
counts and depths are compared only against TLC on the **same** model. This is regression
evidence for these examples, not a general proof of verdict transfer or trace reconstruction.

Each directory holds original input, exact generated input, and normalized TLC `-tool` output
including the exit code and TLC version. Refresh from the repository root after building the
binary to test (Java and `third_party/tla2tools.jar` must be installed):

```sh
cargo build --profile test-release -p tlx-cli -j 3
python3 crates/tlx-cli/tests/fixtures/optimization/refresh.py target/test-release/tlx
cargo test --profile test-release -p tlx-cli --test optimization -j 3
```

The refresher uses the shared guarded process runner and output normalizer, runs TLC with one
worker and fixed seed/fingerprint selection, and refuses to write evidence unless all ten TLC
runs finish with the expected verdict. Review generated input and oracle changes together.
The Rust tests fail if current emission differs from the cached model or configuration.
