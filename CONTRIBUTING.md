# Contributing to tlx

Thanks for your interest. This file lists what a change needs before it is merged.
Use [the development standards](docs/development-standards.md) as the shared review checklist.

## Setup

```sh
cargo build --release          # Rust 1.93.0 is installed automatically (rust-toolchain.toml)
scripts/fetch-deps.sh          # test dependencies: Examples corpus, TLC jar, module sources
```

Java 21 is only needed to refresh TLC oracle results (tests compare against cached TLC output);
point `TLX_JAVA` at its `java` binary if it is not at the default path. See
[docs/testing.md](docs/testing.md#2-setup) for the details.

## Checklist

1. `cargo fmt --all` (a check runs `cargo fmt --all -- --check`).
2. `cargo clippy --workspace --release --all-targets` reports 0 warnings, and
   `cargo build --release` has no warnings. The lint set lives once in the root `Cargo.toml`
   (`[workspace.lints]`); add a local `#[allow(clippy::...)]` only with a reason on the same line.
3. Tests pass:
   ```sh
   cargo test --profile test-release -q --no-fail-fast -j 3
   python3 scripts/spectest.py                      # interpreter
   python3 scripts/spectest.py --extra=-compile     # compiled mode (note the `=`)
   ```
   `--no-fail-fast` keeps a failure in an early crate from hiding every crate after it, and `-j 3`
   is the parallelism of the shared machine ([section 4](docs/testing.md#4-cargo-tests)).
   A change to the compiled tier also runs `TLX_PARANOID=1 python3 scripts/spectest.py --extra=-compile`,
   which cross-checks the compiled tier against the interpreter
   ([section 8](docs/testing.md#8-cross-checking-modes-tlx_paranoid-and-the-jit)). The corpus
   differential tests (`scripts/difftest.py`, [section 6](docs/testing.md#6-corpus-differential-tests))
   and the other layers are described in [docs/testing.md](docs/testing.md); `python3 scripts/verify.py`
   runs the whole gate in a clean checkout ([section 12](docs/testing.md#12-the-merge-gate-scriptsverifypy)).
4. A behavior change comes with a test: a small spec in `tests/specs` (`NAME.tla` + `NAME.cfg`; the
   TLC result is cached with `scripts/spectest.py --refresh NAME`) or a Rust test next to the code.
5. Performance claims come with measurements: an interleaved A/B of two release binaries
   (`scripts/bench.py ab`, [docs/benchmarking.md](docs/benchmarking.md)), not a single timing. Large
   models, corpus-wide runs and numbers of record run on a cloud instance
   ([docs/cloud-verification.md](docs/cloud-verification.md)).

## Compatibility rules

TLC is the semantic oracle ([docs/compat.md](docs/compat.md) section 0): the contract below is the
one of `-tlc` mode, which is where the parity tests run; the default mode keeps only tier 1 and the
validity of counterexamples, with the explicit opt-in mathematical-arithmetic exception
documented in [compat.md section 0](docs/compat.md#0-the-three-tiers).

- In `-tlc` mode, verdicts, violated names, state counts, depth, shortest safety-trace length and
  language semantics must match TLC exactly, at `-workers 1` (model checking is defined there).
- With several workers, counts, search depth and safety-trace length at an early stop, and which
  valid violation is reported at the same BFS level, only have to be valid (D-3).
- Which of several equally short counterexamples, liveness lasso shape, error class and exit code,
  and print order only have to be valid.
- Clear defects in TLC or SANY are not copied: implement the correct semantics and record a `D-n`
  entry in `docs/compat.md` with evidence.
- Compiled mode must agree with the interpreter (`TLX_PARANOID=1`).

## Code and commits

- Code, comments, commit messages and all public documentation (README, this file, `docs/`) are in English. Keep commits focused, with a message that
  says what changed and why. Follow [Conventional Commits](https://www.conventionalcommits.org/en/v1.0.0/) for commit subjects.
- Command-line options and `TLX_*` environment variables are documented only in
  [docs/configuration.md](docs/configuration.md); update it when you add or change one
  (a test checks that it matches the code).
- `unsafe` code needs a `// SAFETY:` comment and a row in [docs/unsafe-audit.md](docs/unsafe-audit.md).
- Crate layout and design: [docs/design.md](docs/design.md).
