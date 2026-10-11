# tlx documentation

tlx is a compiled, TLC-compatible model checker for TLA+. The [project README](../README.md) is
the landing page (what tlx is, quick start, performance). This directory holds everything else.

## User guide

| Document | What it covers |
|---|---|
| [usage.md](usage.md) | Installing, a self-contained first-run tutorial (the four-state `Counter` module, its configuration recipes and the common diagnostics), command line overview, compiled mode, parallel workers, simulation, checkpoint and recovery, output and exit codes, module search path, troubleshooting. |

## Reference

| Document | What it covers |
|---|---|
| [configuration.md](configuration.md) | Every command-line option and every `TLX_*` environment variable, with defaults; the options of the helper scripts. |
| [compat.md](compat.md) | The compatibility contract with TLC (three tiers), the documented differences (D-n) and the known limitations. |
| [tlc-semantics.md](tlc-semantics.md) | Reference for TLC's exact behavior (values, comparison, enumeration order, counting, fingerprints, standard modules), derived from TLC's source. |
| [features.md](features.md) | Support matrix: TLC command-line options, `.cfg` keywords, standard modules, CommunityModules and Apalache modules, operator by operator. |
| [issues.md](issues.md) | Unresolved defects, resource limits, benchmark input migration and pending validation. |

## Internals

| Document | What it covers |
|---|---|
| [design.md](design.md) | Architecture, and the entry point for contributors: the crate map with the production and dev-only dependency edges, a phase walk (source → AST → HIR → cfg binding → model → search → liveness → postcondition/output) that names the owning symbol and the tests of each phase, the five value representations and the three contracts that bind them, the executors and the coverage each is meant to have, the front end, semantic analysis, the interpreter, the compiled tier (layout, IR, executor tiers), the runtime, liveness, and the compatibility contract. |
| [value-store.md](value-store.md) | The value store of the compiled tier's `Ref` slots (experimental, `TLX_VALUE_STORE`, default off): what a handle is, interning and the semantic digest, the slotted shapes, the shared operation set and its native ABI boundary, ownership, the memory budget, and the missing checkpoint format. |
| [reductions.md](reductions.md) | The guarantee contract of the default mode and the one reduction it has: the V-safe/CEX/D/L vocabulary, the static symmetry proof, its runtime guards and restart, the bounded cross-check, the labelling contract, and what is not implemented. |
| [mixed-mode.md](mixed-mode.md) | Mixed-mode native code: host regions for sub-expressions the C backend cannot express, adaptive tiering, region memoization. |
| [abstraction.md](abstraction.md) | Experimental finite-abstraction frontend: typed verification IR, analyses, extensible passes, rule validation, supported counter fragment and trust boundary. |
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

## Archived material

The design records behind [value-store.md](value-store.md) and [reductions.md](reductions.md) are no
longer tracked: the store's roadmap (stable state root slots, complete collection lowering,
reclamation, spill, a checkpoint format, and the measurements that ranked those steps), the survey of
alternative state representations those measurements came from, and the reductions that are not
implemented (sleep sets, partial-order reduction, bounded and swarm search, bitstate storage,
incremental re-checking, 128-bit fingerprints, `-symmetry trust` and the incomplete-search exit
code 4). Each is recoverable from the revision that held it, and the hash below pins what was
archived:

| Archived document | SHA-256 |
|---|---|
| Beyond TLC: reductions and search modes TLC does not have | `d842300668a5f09080f3002be9d3342f578165a33d3285ba9c5df8763673e720` |
| State representation without shape cliffs | `4d06ad466e3bed4212df943f38a05236cee913c1ca197257e716a94e2ebfe09d` |
| State-representation survey (the measurements behind the two) | `f2ea7749ef0fe694602fb6e3293bb4e8fd076827c2f7a64924376b5de9587b5a` |

A locator is `<revision>:<path>`, read with `git show <revision>:<path>`; the SHA-256 is of that
file's bytes, so a citation can be checked without trusting this page:

```text
git show af7011f530a61750ef5c770a37f570b91a6db1e0:docs/design-beyond-tlc.md
git show af7011f530a61750ef5c770a37f570b91a6db1e0:docs/design-state-representation.md
git show af7011f530a61750ef5c770a37f570b91a6db1e0:docs/notes/state-representation-survey.json
```

## Development

| Document | What it covers |
|---|---|
| [../CONTRIBUTING.md](../CONTRIBUTING.md) | What a change needs before it is merged. |
| [testing.md](testing.md) | Test tiers, differential tests against TLC and SANY, the corpus, expected failures, and the gates that run them. |
| [benchmarking.md](benchmarking.md) | Performance measurement: `scripts/bench.py`, the benchmark suite of record and its continuous tracking, the TLC timing baselines and their reuse, the measurement schema. |
| [cloud-verification.md](cloud-verification.md) | Where work runs (cloud instances against the shared workstation), `scripts/cloud_verify.py`, launch admission and budgets, provider identity, the operator's ssh allowlist. |
| [unsafe-audit.md](unsafe-audit.md) | Inventory and justification of every `unsafe` block and the FFI boundary to generated C. |
| [performance.md](performance.md) | Generated: the canonical TLC/tlx performance report (median wall time per cohort, instance, mode and worker count), naming the record behind every measurement and, per row, the optimization the tlx record states, so a row whose tlx run was reduced says so. |

[Post-fix validation](research/post-fix-validation.md) records original-model checks and diagnostic
measurements separately from the frozen initial baseline.
