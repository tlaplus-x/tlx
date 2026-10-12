# Working on tlx

tlx is a compiled TLA+ model checker written in Rust. It generates per-spec C,
builds it with a C compiler, and loads the result for execution. The front end uses
tree-sitter; SANY and TLC are test oracles, not runtime dependencies.

## Project map

- `crates/`: Rust workspace. Front-end analysis lives in `front` and `sema`;
  execution spans `eval`, `compile`, `native`, `runtime`, and `live`.
  `base` provides shared infrastructure and `testkit` provides test helpers.
- `scripts/`: public development and verification tools; Python tests live in
  `scripts/tests/`. Benchmark implementations live in `scripts/benchmarking/`
  and cloud implementations in `scripts/cloud/`.
- `tests/specs/`: small TLA+ regression specifications and configurations.
- `bench/`: benchmark inputs and the published baseline evidence.
- `docs/`: user documentation and design references.

Read [CONTRIBUTING.md](CONTRIBUTING.md) for setup and the contribution checklist,
and [docs/design.md](docs/design.md) for architecture and topic ownership.

## Correctness contract

[docs/compat.md section 0](docs/compat.md#0-the-three-tiers) owns the compatibility
contract. In compatibility mode (`-tlc`), tiers 1 and 2 match TLC under the
conditions documented there. The default mode must remain sound: preserve
verdicts and produce genuine counterexamples.

TLC is the semantic oracle, followed by the tlx interpreter, then compiled
execution. Compiled execution must agree with the interpreter; use
`TLX_PARANOID=1` to cross-check it. Do not reproduce a demonstrated TLC or SANY
defect: document the evidence and the intentional difference in `docs/compat.md`.

## Making changes

- Keep changes focused. Preserve unrelated edits in the working tree.
- Avoid overengineering. Use the simplest design that meets current requirements;
  add abstractions, metadata, or extension points only when concrete use cases need them.
- After every implementation, review your own changes before reporting completion. Check
  correctness, architecture, failure paths, and test coverage; fix issues found, rerun the
  affected checks, and report any unresolved findings.
- Every state-reducing optimization needs a compiler-generated Lean certificate connected
  to the actual reduction. Do not apply uncertified reductions, including legacy rules,
  automatic symmetry and export passes. Prove initialization correspondence, successor correspondence
  from every equivalent representative, preservation of selected observations, and
  concrete counterexample lifting. Include deadlock or temporal preservation when the
  supported checking mode requires it. Shared lemmas, serialized plans, tests and matching
  state counts do not satisfy this requirement. Do not assume the preservation obligations
  as certificate premises or introduce placeholder proofs or custom correctness axioms.
- For new or changed reductions, explicitly verify the generated certificate with Lean
  before declaring the implementation complete; audit its axioms and test that relevant
  broken transformations are rejected. State the theorem's scope and every trusted layer,
  including source lowering and runtime execution. Existing reductions without connected
  certificates are unfinished proof work, not exceptions to this requirement. Ordinary
  `tlx check -optimize` still emits Lean without invoking a verifier unless requested.
- Write code, comments, commit messages, and public documentation in English. Follow the
  [commit convention](CONTRIBUTING.md#code-and-commits). Limit commit subjects to 75
  characters and wrap commit bodies at 75 columns; keep URLs and structured trailers
  intact when wrapping would break them.
- Add a focused regression test for a behavior change. Prefer a small specification
  or a Rust unit test that exercises the observable behavior.
- Document CLI options and `TLX_*` environment variables in
  [docs/configuration.md](docs/configuration.md), their authoritative reference.
- Every `unsafe` block needs a `// SAFETY:` explanation and coverage in
  [docs/unsafe-audit.md](docs/unsafe-audit.md).
- Follow [docs/development-standards.md](docs/development-standards.md).

## Verification

Run checks appropriate to the changed code. Common commands, from the repository root:

```sh
cargo fmt --all -- --check
cargo clippy --workspace --release --all-targets
cargo test --profile test-release -q --no-fail-fast -j 3
python3 scripts/spectest.py
python3 scripts/spectest.py --extra=-compile
python3 scripts/doccheck.py
```

For a compiled-execution change, also run:

```sh
TLX_PARANOID=1 python3 scripts/spectest.py --extra=-compile
```

Python tooling tests live in `scripts/tests/`; select the affected modules or run
`python3 -m unittest discover -s scripts -p 'test_*.py'`.
[docs/testing.md](docs/testing.md) describes prerequisites, test layers, and the
full verification command, `python3 scripts/verify.py`.
Report the commands actually run and their results; identify skipped checks and
unresolved failures explicitly.

## Performance and evidence

Follow [docs/benchmarking.md](docs/benchmarking.md) for measurements. Compare
release binaries with repeated, interleaved A/B runs. Use isolated cloud machines
for large models, corpus-wide runs, and published performance numbers, as described
in [docs/cloud-verification.md](docs/cloud-verification.md).

Do not treat timeouts, errors, or incomplete samples as completed timings. Keep
published claims tied to reproducible evidence and matching configurations.
[bench/README.md](bench/README.md) describes the baseline layout;
`python3 scripts/bench.py report --check` verifies its generated report.
