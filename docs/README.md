# tlx documentation

tlx is a compiled, TLC-compatible model checker for TLA+. The [project README](../README.md) is
the landing page (what tlx is, quick start, performance). This directory holds everything else.

## User guide

| Document | What it covers |
|---|---|
| [usage.md](usage.md) | Installing, a self-contained first-run tutorial (the four-state `Counter` module, its configuration recipes and the common diagnostics), command line overview, compiled mode, parallel workers, symmetry and certified state reductions (`-optimize`, `tlx optimize`), simulation, checkpoint and recovery, output and exit codes, module search path, troubleshooting. |

## Reference

| Document | What it covers |
|---|---|
| [configuration.md](configuration.md) | Every command-line option and every `TLX_*` environment variable, with defaults; the options of the helper scripts. |
| [compat.md](compat.md) | The compatibility contract with TLC (three tiers), the documented differences (D-n) and the known limitations. |
| [tlc-semantics.md](tlc-semantics.md) | Reference for TLC's exact behavior (values, comparison, enumeration order, counting, fingerprints, standard modules), derived from TLC's source. |
| [features.md](features.md) | Support matrix: TLC command-line options, `.cfg` keywords, standard modules, CommunityModules and Apalache modules, operator by operator. |
| [issues.md](issues.md) | Active engineering follow-ups, resource limits, benchmark input migration and pending validation (documented TLC differences live in [compat.md](compat.md)). |

## Internals

| Document | What it covers |
|---|---|
| [design.md](design.md) | Architecture, and the entry point for contributors: the crate map with the production and dev-only dependency edges, a phase walk (source → AST → HIR → cfg binding → model → search → liveness → postcondition/output) that names the owning symbol and the tests of each phase, the five value representations and the three contracts that bind them, the executors and the coverage each is meant to have, the front end, semantic analysis, the interpreter, the compiled tier (layout, IR, executor tiers), the runtime, liveness, and the compatibility contract. |
| [value-store.md](value-store.md) | The value store of the compiled tier's `Ref` slots (experimental, `TLX_VALUE_STORE`, default off): what a handle is, interning and the semantic digest, the slotted shapes, the shared operation set and its native ABI boundary, ownership, the memory budget, and the missing checkpoint format. |
| [reductions.md](reductions.md) | The default-mode guarantee vocabulary, symmetry candidate analysis, connected keyed certificates, bounded cross-checks, reduction labels, and unsupported candidates. |
| [mixed-mode.md](mixed-mode.md) | Mixed-mode native code: host regions for sub-expressions the C backend cannot express, adaptive tiering, region memoization. |
| [optimization.md](optimization.md) | Rule-based optimizer for opt-in checking and finite-model export: typed verification IR, analyses, extensible passes, rule validation, supported counter fragment and trust boundary. |
| [scale.md](scale.md) | Memory and disk: the memory budget, fingerprint set growth and spilling, queue, trace log and liveness graph on disk, checkpoints. |
| [development-standards.md](development-standards.md) | The review criteria every change is held to: the rule index by area (code, documentation, harness, architecture), each rule with its rationale, how it is checked and an example. |
| [native-coverage.md](native-coverage.md) | Measurement: how much of each corpus model executes natively, the histograms of what stays boxed and the rejection reasons. |

## Research

Version-specific measurements and analyses are collected in `research/`.

| Document | What it covers |
|---|---|
| [native-vsr.md](research/native-vsr.md) | Measurement and analysis of the message-bag representation in five vanlightly-vsr configurations: interpreter costs, store-backed slots and the remaining native-lowering gaps. |
| [tlc-baseline-coverage.md](research/tlc-baseline-coverage.md) | Measurement: how much of the corpus has a usable TLC timing baseline, and the recorded cause (timeout, TLC error, budget skip) of every missing key. |
| [state-representation-alternatives.md](research/state-representation-alternatives.md) | Measurement and analytical comparison of the alternative state representations [value-store.md](value-store.md) builds on, each entry marked as a measurement or an estimate. |
| [speedup-audit.md](research/speedup-audit.md) | Audit of the 13 frozen configurations with published tlx/TLC speedups above 100x: input-digest verification, warm-up versus single-sample denominators, automatic reductions and remaining validation. |
| [post-fix-validation.md](research/post-fix-validation.md) | Original-model checks and diagnostic cloud measurements recorded after the initial baseline freeze (correctness fixes, enumeration limits and Kafka cancellation). |

## Archived material

Earlier exploratory notes on unimplemented search reductions (partial-order reduction, sleep sets,
bitstate hashing, 128-bit fingerprints) and superseded state-representation roadmaps were
intentionally left out of the active design documentation. Current contracts and architecture live
in [reductions.md](reductions.md), [optimization.md](optimization.md), and
[value-store.md](value-store.md).

## Development

| Document | What it covers |
|---|---|
| [../CONTRIBUTING.md](../CONTRIBUTING.md) | What a change needs before it is merged. |
| [testing.md](testing.md) | Test tiers, differential tests against TLC and SANY, the corpus, expected failures, and the gates that run them. |
| [benchmarking.md](benchmarking.md) | Performance measurement: `scripts/bench.py`, the benchmark suite of record and its continuous tracking, the TLC timing baselines and their reuse, the measurement schema. |
| [cloud-verification.md](cloud-verification.md) | Where work runs (cloud instances against the shared workstation), `scripts/cloud_verify.py`, launch admission and budgets, provider identity, the operator's ssh allowlist. |
| [unsafe-audit.md](unsafe-audit.md) | Inventory and justification of every `unsafe` block and the FFI boundary to generated C. |
| [performance.md](performance.md) | Generated: the canonical TLC/tlx performance report (median wall time per cohort, instance, mode and worker count), naming the record behind every measurement and, per row, the optimization the tlx record states, so a row whose tlx run was reduced says so. |
