# Development standards

This is the shared checklist for development reviews and every tlx audit. Rules apply
to changed code and identify existing debt; adoption does not claim that all existing
code already complies. Each rule has a stable ID, a one-sentence requirement, its
evidence class, a check and a small example. “Manual” means reviewer judgment is still
required; named tests prove only their implemented scope, not every suggested fixture.
Unnamed test matrices describe review/acceptance criteria, not existing automated guards.

## Authority and scope

Explicit user instructions take precedence. [AGENTS.md](../AGENTS.md) provides the public contribution instructions;
[compat.md](compat.md) section 0 owns semantics and the
compatibility tiers. This standard owns review criteria, [design.md](design.md) owns
architecture descriptions, [configuration.md](configuration.md) owns option/variable
syntax and defaults, and [testing.md](testing.md), [benchmarking.md](benchmarking.md),
[cloud-verification.md](cloud-verification.md) own runnable recipes. [CONTRIBUTING.md](../CONTRIBUTING.md) is the contributor entrypoint.
Link these owners instead of duplicating their tables here.

Execution tier (interpreter/compiled) and compatibility mode are independent axes.
In compatibility mode, tier 1 and tier 2 obey compat.md, including its stated worker
and nondeterminism qualifications; tier 3 requires validity, not identical choices.
Default optimizations must preserve verdict soundness and genuine counterexamples;
counts and depth may differ. Compiled execution must agree with the interpreter.
Clear TLC/SANY defects require evidence and a documented compatibility exception.
Older unqualified parity/default-tier summaries do not override this contract.

Current AGENTS.md resource restrictions take precedence over old “idle machine” or
artificial-load recipes in older documentation. A stale recipe is a documentation finding,
not permission to bypass a guard. If executable behavior disagrees with the owning
contract, report the discrepancy and a corrective change; do not silently weaken
the rule or claim that a proposed mechanism already exists.

## Rule index

| ID | Review criterion | Area |
|---|---|---|
| [CODE-01](#code-01) | Style and names | CODE |
| [CODE-02](#code-02) | Size review | CODE |
| [CODE-03](#code-03) | Visible phases and dispatch | CODE |
| [CODE-04](#code-04) | Honest result types | CODE |
| [CODE-05](#code-05) | Required resource failures | CODE |
| [CODE-06](#code-06) | Safe raw-input boundaries | CODE |
| [CODE-07](#code-07) | Unsafe contracts and register | CODE |
| [CODE-08](#code-08) | Semantic duplication | CODE |
| [CODE-09](#code-09) | Operational cache equivalence | CODE |
| [CODE-10](#code-10) | Exact replay keys | CODE |
| [CODE-11](#code-11) | Cache owner identity | CODE |
| [CODE-12](#code-12) | Scoped mutable state | CODE |
| [CODE-13](#code-13) | Structural keys | CODE |
| [CODE-14](#code-14) | Seeded behavior | CODE |
| [CODE-15](#code-15) | Resource bounds | CODE |
| [CODE-16](#code-16) | Numeric conversions | CODE |
| [CODE-17](#code-17) | Unicode diagnostics | CODE |
| [CODE-18](#code-18) | Complete traversal | CODE |
| [CODE-19](#code-19) | Semantic coverage matrix | CODE |
| [CODE-20](#code-20) | Explicit assertion policy | CODE |
| [CODE-21](#code-21) | Independent stability fixtures | CODE |
| [CODE-22](#code-22) | Owned test resources | CODE |
| [CODE-23](#code-23) | Refactor proof | CODE |
| [CODE-24](#code-24) | Fallback causes | CODE |
| [DOC-01](#doc-01) | Topic ownership | DOC |
| [DOC-02](#doc-02) | Current executable claims | DOC |
| [DOC-03](#doc-03) | Contracts versus proposals | DOC |
| [DOC-04](#doc-04) | Generated and mutable facts | DOC |
| [DOC-05](#doc-05) | Performance evidence | DOC |
| [DOC-06](#doc-06) | Artifact retention and provenance | DOC |
| [DOC-07](#doc-07) | Runnable examples | DOC |
| [DOC-08](#doc-08) | Diagnostic completeness | DOC |
| [DOC-09](#doc-09) | Oracle identity | DOC |
| [DOC-10](#doc-10) | Configuration metadata | DOC |
| [DOC-11](#doc-11) | Validation coverage | DOC |
| [DOC-12](#doc-12) | Public artifact hygiene | DOC |
| [HARNESS-01](#harness-01) | One policy definition | HARNESS |
| [HARNESS-02](#harness-02) | CLI contract | HARNESS |
| [HARNESS-03](#harness-03) | Library direction | HARNESS |
| [HARNESS-04](#harness-04) | Transactional state | HARNESS |
| [HARNESS-05](#harness-05) | Complete verification | HARNESS |
| [HARNESS-06](#harness-06) | Outcome and receipt | HARNESS |
| [HARNESS-07](#harness-07) | Per-sample semantics | HARNESS |
| [HARNESS-08](#harness-08) | Shared deadlines | HARNESS |
| [HARNESS-09](#harness-09) | Owned subprocesses | HARNESS |
| [HARNESS-10](#harness-10) | Destructive authority | HARNESS |
| [HARNESS-11](#harness-11) | Guard and repair tests | HARNESS |
| [HARNESS-12](#harness-12) | Authorization validation | HARNESS |
| [HARNESS-13](#harness-13) | Discovery after moves | HARNESS |
| [HARNESS-14](#harness-14) | Completion and audit evidence | HARNESS |
| [HARNESS-15](#harness-15) | Shared installations | HARNESS |
| [HARNESS-16](#harness-16) | Oracle promotion | HARNESS |
| [HARNESS-17](#harness-17) | Supervised identity | HARNESS |
| [HARNESS-18](#harness-18) | Source replacement | HARNESS |
| [HARNESS-19](#harness-19) | Executable provenance | HARNESS |
| [HARNESS-20](#harness-20) | Resource and baseline policy | HARNESS |
| [HARNESS-21](#harness-21) | Acceptance accounting | HARNESS |
| [HARNESS-22](#harness-22) | Faithful command doubles | HARNESS |
| [ARCH-01](#arch-01) | Production layering | ARCH |
| [ARCH-02](#arch-02) | Lowest appropriate owner | ARCH |
| [ARCH-03](#arch-03) | Public surface and dead code | ARCH |
| [ARCH-04](#arch-04) | Supported feature closure | ARCH |
| [ARCH-05](#arch-05) | Focused test dependencies | ARCH |
| [ARCH-06](#arch-06) | Live semantic tables | ARCH |
| [ARCH-07](#arch-07) | Representation and ABI schema | ARCH |
| [ARCH-08](#arch-08) | Backend planning | ARCH |
| [ARCH-09](#arch-09) | Embedded resources | ARCH |
| [ARCH-10](#arch-10) | Model capabilities | ARCH |

## Rust code and tests

### CODE-01

- **Rule:** Use rustfmt, the workspace lint set and descriptive English names, documenting each local lint allowance at its site.
- **Rationale:** Uniform formatting and meaningful names expose real changes and ownership instead of review noise.
- **Checked by:** `cargo fmt --all --check`, release workspace Clippy and manual naming review; lint allowances follow CONTRIBUTING.
- **Example:** Good: `restore_frame` and a justified narrow allowance; bad: numbered helpers or blanket warning suppression.

### CODE-02

- **Rule:** Review the responsibilities of every Rust file over 1,500 physical lines or named function over 150 lines and record an extraction plan or a reason to keep it together. A change may not create a file or function over either limit or grow one across it: the same thresholds apply to what a change creates, so a batch that splits an oversized unit must not end with another one. A unit that is already over a limit may grow (for example one more arm in an exhaustive family dispatcher); it stays on the review list.
- **Rationale:** Large dispatchers and search coordinators mix responsibilities, but size alone does not prove poor structure. Size that merely moves from one function to another is not progress, and nothing else in the pipeline sees it.
- **Checked by:** Manual size and responsibility review of changed functions and modules. Identify inherited large units separately from new growth; moving lines alone does not establish better structure.
- **Example:** Good: a coherent exhaustive match retained with a reason; bad: splitting into `part1` and `part2` only to meet a threshold, or a split whose extracted function is itself over the limit.

### CODE-03

- **Rule:** Separate construction, execution, persistence and reporting at responsibility boundaries while keeping exhaustive semantic dispatch and error order visible.
- **Rationale:** Mixed coordination and backend-family dispatch make ownership and omitted cases hard to inspect.
- **Checked by:** Manual phase/dispatch review and affected CLI, backend and lifecycle tests.
- **Example:** Good: named prepare/run/finish phases; bad: a wildcard fallback hiding a new operation family.

### CODE-04

- **Rule:** Represent possible outcomes directly and retain only used bookkeeping with one authority per measure.
- **Rationale:** Impossible nested outcomes and redundant bookkeeping obscure the true error owner.
- **Checked by:** Manual constructor/caller inventory and focused failure-path tests.
- **Example:** Good: `Option<BlockRef>` when lookup cannot fail; bad: every nonempty arm returns `Some(Ok(reference))`.

### CODE-05

- **Rule:** Handle failures of required ownership transfers and persistence barriers explicitly, reserving ignored results for documented best-effort work.
- **Rationale:** Child reaping and durable commits cannot inherit cache-pruning failure policy without losing guarantees.
- **Checked by:** Manual review of discarded results; fault-injection tests for transfer, flush, rename and cleanup failures.
- **Example:** Good: retain a child for fallback reaping after spawn failure; bad: discard spawn failure while promising completion.

### CODE-06

- **Rule:** Validate every invariant needed by trusted consumers before a safe raw-input API enters unchecked code, or require a validated type or explicit unsafe contract.
- **Rationale:** Forged handles and incomplete recursive-plan verification can reach trusted indexing or invalid symbols.
- **Checked by:** Manual safe-to-unsafe call-path review; [raw_handles.rs](../crates/tlx-layout/tests/raw_handles.rs) drives invalid, foreign-store and noncanonical-value inputs through the checked store API (and its publication round trip) instead of the unchecked one; Miri where supported.
- **Example:** Good: checked decoding returns `InvalidHandle`; bad: safe `decode(u64)` relies only on caller prose.

### CODE-07

- **Rule:** Give each unsafe block or implementation a relevant local safety argument and mechanically reconcile unsafe-containing source files, including tests, against the register with explicit reviewed exclusions.
- **Rationale:** Local comments and the register have independent coverage gaps, especially at callbacks and OS boundaries.
- **Checked by:** [unsafe_inventory.py](../scripts/unsafe_inventory.py), integrated into [doccheck.py](../scripts/doccheck.py), reconciles source files with [unsafe-audit.md](unsafe-audit.md); [test_unsafe_inventory.py](../scripts/tests/test_unsafe_inventory.py) exercises refusal and valid controls, alongside manual safety/exclusion review.
- **Example:** Good: state pointer span, alignment, initialization, lifetime, aliasing, synchronization and panic obligations as applicable; bad: an unrelated “see above” or “tested”.

### CODE-08

- **Rule:** Share repeated semantic decisions at their owner while retaining deliberate evaluation order, representation-specific loops and independent reference oracles.
- **Rationale:** Similar boxed, stored and native operations differ in allocation, laziness and heterogeneous errors.
- **Checked by:** Manual copy/difference inventory; common ordered/error vectors and before/after consumer tests.
- **Example:** Good: one search schedule with specialized loops; bad: thaw every stored value merely to remove similar code.

### CODE-09

- **Rule:** Make cache keys, optimization identities and region equivalence preserve every observation the cached computation can make, including representation witnesses and errors.
- **Rationale:** Extensionally equal payloads can have different domain witnesses and operational behavior.
- **Checked by:** Manual key/equivalence review; equal-payload/different-witness tests at each optimization consumer.
- **Example:** Good: retain a domain witness when lookup observes it; bad: compare only the shared pair allocation.

### CODE-10

- **Rule:** Retain exact replay keys or verify equality within a hash bucket before reusing a journaled effect or result.
- **Rationale:** Hash-only journals can suppress a different effect or replay the wrong result on collision.
- **Checked by:** Manual hash-key inventory; deterministic collision-injection tests without collision searches.
- **Example:** Good: compare stored arguments after hashing; bad: consume a command result solely by a `u64` digest.

### CODE-11

- **Rule:** Use an explicit generation or proven lifetime-bound identity for caches that can outlive or observe replacement of their owner.
- **Rationale:** Reusable addresses can incorrectly identify a replacement spec or compiler object.
- **Checked by:** Manual pointer-key/lifetime review; same-thread replacement and invalidation regressions.
- **Example:** Good: `(generation, key)`; bad: an owner address alone in a surviving thread-local cache.

### CODE-12

- **Rule:** Own temporary interpreter/compiler state as a scoped unit that restores on every supported exit, keeping persistent registries outside the frame.
- **Rationale:** Manual reset lists omit new fields and set/call/reset sequences fail during unwinding.
- **Checked by:** Manual frame-field inventory; nested-frame, error and `catch_unwind` restoration tests where unwinding is supported.
- **Example:** Good: a saved-state guard; bad: reset temporary bindings in only some entry points.

### CODE-13

- **Rule:** Use structural semantic keys with explicit order and multiplicity policy rather than incidental Debug or Display output.
- **Rationale:** Formatting changes must not alter internal formula identity or metadata lookup.
- **Checked by:** Manual key-construction review and before/after metadata fixtures.
- **Example:** Good: an ordered `Vec<Ltl>` key; bad: `format!("{formula:?}")` without a canonical encoding contract.

### CODE-14

- **Rule:** Preserve seed progression and each sampling transformation during a seeded-algorithm refactor unless separately changing behavior.
- **Rationale:** Generators with the same name can use modulo versus multiply-high sampling.
- **Checked by:** Manual consumer inventory and comparison of fixed vectors for raw outputs, bounded sampling and restart/resume.
- **Example:** Good: reuse the PRNG core and keep the old sampling policy; bad: replace an entire RNG API because both use SplitMix.

### CODE-15

- **Rule:** Apply stated resource bounds to preparation, admission, execution and cleanup, including actual concurrency, and identify any non-interruptible portion.
- **Rationale:** Pre-budget materialization, excessive pools and pipe-reader joins can bypass a nominal limit.
- **Checked by:** Manual allocation/lifecycle map; small capped preparation, peak-concurrency, timeout and descendant-pipe fixtures.
- **Example:** Good: stream initial states under the cap and honor the requested pool size; bad: materialize all states before checking a limit.

### CODE-16

- **Rule:** Validate numeric inputs with fallible conversion into their actual duration, size or index representation before accepting them.
- **Rationale:** Finite nonnegative values may still overflow a duration constructor or multiplication.
- **Checked by:** Manual conversion review; require boundary tests for zero, maximum, one beyond, huge finite values, NaN/infinity and rounding in relevant profiles.
- **Example:** Good: checked multiplication and `Duration::try_from_secs_f64`; bad: validate finiteness then call a panicking constructor.

### CODE-17

- **Rule:** Truncate or slice human-readable diagnostic strings only at character boundaries.
- **Rationale:** A byte limit inside a multibyte literal can turn an error report into a panic.
- **Checked by:** Manual slicing review; require non-ASCII diagnostics crossing each truncation boundary.
- **Example:** Good: choose a valid UTF-8 prefix; bad: `&debug[..60]` for arbitrary text.

### CODE-18

- **Rule:** Make an all-children traversal visit every child-bearing field exactly once in documented order.
- **Rationale:** Wildcard destructuring can silently omit selector arguments or new expression fields.
- **Checked by:** Manual review when adding fields; require variant/sentinel traversal tests independent of consumers.
- **Example:** Good: test base and selector children separately; bad: match only `base` in an all-subexpressions walker.

### CODE-19

- **Rule:** Test semantic changes through the interpreter including fast paths, closure executor, C, JIT and supported fallbacks, separating compatibility identity from default-mode verdict soundness.
- **Rationale:** A successful model run can delegate all operations and conceal an untested backend or fast path.
- **Checked by:** [Testing procedures](testing.md) and [verify.py](../scripts/verify.py); [operation_matrix.rs](../crates/tlx-compile/tests/operation_matrix.rs) builds the per-family consumer matrix (`ran`, `delegated`, `gap`, plus a negative control that must report a gap) from the lowered IR, the generated C and the native plan and refuses a silent zero; [coverage.py](../scripts/coverage.py) is the measured native census; the families it does not reach and every compatibility-mode claim stay a review judgment.
- **Example:** Good: a lookup regression reaches `code.rs` and native callbacks; bad: one EncModel verdict claimed as C/JIT coverage.

### CODE-20

- **Rule:** Use named comparison fields and policies and preserve every original assertion when sharing cross-mode or runtime test helpers.
- **Rationale:** Positional summaries differ intentionally in counts, depth, endpoints, trace length and graph data.
- **Checked by:** Manual before/after field matrix, affected test targets and deliberately different report fixtures.
- **Example:** Good: a named trace-length-and-endpoint policy; bad: reduce all checks to `(verdict, distinct)`.

### CODE-21

- **Rule:** Assert persisted bytes, fingerprints and other stability promises against fixed external or cross-version fixtures, not self-comparison.
- **Rationale:** A deterministic algorithm can change while a tautological assertion continues to pass.
- **Checked by:** Manual review of golden byte/bit comparisons and assertions, including checks that both sides are independently computed.
- **Example:** Good: compare a fingerprint with fixed expected bits; bad: `assert_eq!(fp(x), fp(x))`.

### CODE-22

- **Rule:** Allocate integration-test temporary resources through the shared ownership-aware helpers while preserving each test's filesystem preconditions.
- **Rationale:** Manual trailing cleanup leaks on panic and a precreated directory can invalidate an I/O test.
- **Checked by:** `tlx-testkit` helpers, `scripts/tempdirs.py` and completion checks; manual review of ad hoc paths and justified exceptions.
- **Example:** Good: scoped `TempDir` with a nonexistent child path when required; bad: PID path with cleanup only after the assertion.

### CODE-23

- **Rule:** Keep behavior-preserving extraction separate from corrective changes and prove the applicable semantic, output, seeded, lifecycle and performance contracts before removing old copies.
- **Rationale:** A move mixed with a changed decision hides regressions and leaving old copies preserves drift.
- **Checked by:** [ir_receipt.py](../scripts/ir_receipt.py) compares generated IR and C on its selected specs. Review the complete old-name inventory and affected tests; use a cloud A/B when behavior or performance changes.
- **Example:** Good: extract intact, then fix with a regression in a separate commit; bad: change pruning refusal policy in a file move.

### CODE-24

- **Rule:** Retain structured fallback or rejection causes until a diagnostic boundary without adding repeated hot-path logging.
- **Rationale:** Erasing errors with `.ok()` loses the root cause of transitive compiler coverage failures.
- **Checked by:** Manual cause propagation review and direct/transitive rejection tests.
- **Example:** Good: store a cold not-covered reason chain; bad: replace every failure with “IR closure not covered”.


## Documentation and artifacts

### DOC-01

- **Rule:** Give each normative topic one document owner and link summaries to it rather than copying its rules or algorithms.
- **Rationale:** Repeated configuration, architecture and workflow prose drifts independently.
- **Checked by:** Manual review against the topic map in [design.md](design.md); `scripts/doccheck.py` checks supported links.
- **Example:** Good: an option row links to the checkpoint protocol; bad: repeat the protocol in three tables.

### DOC-02

- **Rule:** Update comments and documentation with the attached item's current ownership, inputs, strategy and guarantees when behavior or location changes.
- **Rationale:** Recently moved comments can describe another method, old defaults or nonexistent memoization.
- **Checked by:** Manual code/claim review, doctests where available and relevant behavior tests; [cli_contract.py](../scripts/cli_contract.py) mechanically refutes one class of stale claim - a documented command or option its owning parser does not accept - and a static link does not prove the rest.
- **Example:** Good: “formatted when requested”; bad: “built on first use” for an uncached closure.

### DOC-03

- **Rule:** Clearly separate current contracts from unimplemented proposals and keep migration diaries and one-off acceptance narratives in ignored process artifacts.
- **Rationale:** Mixed current/design/history pages conceal which behavior is implemented.
- **Checked by:** Manual status/consumer inventory; public docs describe lasting contracts and explicitly label retained design proposals.
- **Example:** Good: a labeled design proposal separate from the current store contract; bad: old migration phases presented as current architecture.

### DOC-04

- **Rule:** Regenerate generated artifacts through their owning tool and derive mutable inventories from metadata or label their counting method and pinned snapshot.
- **Rationale:** Hand-edited reports and timeless case/module totals become misleading.
- **Checked by:** `scripts/bench.py report --check` via doccheck for performance artifacts; manual ownership/snapshot review for other counts.
- **Example:** Good: regenerate the report or link to the suite inventory; bad: hand-edit a generated table or undated case total.

### DOC-05

- **Rule:** Publish performance claims only from canonical measurements identifying statistic, cohort, revision, machine, mode and relevant cache conditions.
- **Rationale:** Different cohorts and summary statistics produce incompatible headlines.
- **Checked by:** Canonical record/report checks via [bench.py](../scripts/bench.py) (`report --check`) and [doccheck.py](../scripts/doccheck.py), with measurement procedures in [benchmarking.md](benchmarking.md); manual claim-to-record review outside the generated report.
- **Example:** Good: a linked scoped median from the report; bad: an unqualified speedup copied from another cohort.

### DOC-06

- **Rule:** Classify tracked artifacts by purpose and actual consumers before deletion or archival and preserve verifiable public provenance for retained evidence.
- **Rationale:** Suite histories, raw inputs and canonical rows may still drive baseline selection or contain unique evidence.
- **Checked by:** Manual tracked census and generic-reader inspection; source/hash or pinned-Git locator verification and before/after record/report fixtures.
- **Example:** Good: preserve active history and a recoverable public source hash; bad: delete all generated JSON or point only to a private archive.

### DOC-07

- **Rule:** Make first-run tutorials complete finite model/config pairs and copy runnable examples from verified source with valid source-language syntax.
- **Rationale:** Missing configs, assumed installation paths and Markdown pipe escaping break tutorials.
- **Checked by:** Doccheck parses supported complete TLA fences when the binary exists; manually execute exact bounded examples in affected modes.
- **Example:** Good: a supplied Counter module and cfg with checked results; bad: an unspecified model or table-escaped TLA source in a code fence.

### DOC-08

- **Rule:** State the completeness boundary and platform scope of user-visible traces, diagnostics and durability promises without claiming more than the implementation guarantees.
- **Rationale:** A partial trace prefix is not itself a violation witness, and best-effort flush or Unix signal behavior is not universal.
- **Checked by:** Manual claim review and targeted trace, closed-stdout and failure-path tests.
- **Example:** Good: name why trace replay is partial and which verdict remains established; bad: call the prefix a complete counterexample.

### DOC-09

- **Rule:** Pin and verify the oracle version, matching sources and configuration identity rather than letting an arbitrary installed jar define compatibility.
- **Rationale:** Bootstrap and historical evidence can disagree with the documented baseline.
- **Checked by:** [dependencies.py](../scripts/dependencies.py) declares the TLC oracle baseline once (jar bytes, manifest revision and version) and its `verify_tla2tools` refuses a jar that exists but is not that baseline, so the download URL cannot define compatibility; [test_dependencies.py](../scripts/tests/test_dependencies.py) covers the refusals, including the pinned source checkout; bootstrap provenance stays a manual verification.
- **Example:** Good: verify the jar against the declared baseline; bad: infer yesterday's TLC revision from today's jar.

### DOC-10

- **Rule:** Keep accepted aliases, documented types, defaults and effects comparable with the owning code metadata, with dynamic formulas reviewed explicitly.
- **Rationale:** Names-only checks do not establish defaults, aliases or behavioral effects.
- **Checked by:** `scripts/knobs_check.py`, CLI config tests and manual exact alias/default/effect review where not covered.
- **Example:** Good: a registered variable and documented alias; bad: claim complete accuracy from a names-only scan.

### DOC-11

- **Rule:** Check every public Markdown entry point and report missing prerequisites, skipped checks and validation limits explicitly.
- **Rationale:** A link-only pass or omitted contributor page cannot establish all examples or prose are correct.
- **Checked by:** [doccheck.py](../scripts/doccheck.py) checks public links, references, documented paths and environment names, and `--require-examples` requires parsing complete TLA+ examples. [cli_contract.py](../scripts/cli_contract.py) checks its declared command coverage and reports missing inputs. A link check alone does not verify examples.
- **Example:** Good: report “links checked; module parsing skipped”; bad: “all examples verified” without a binary.


### DOC-12

- **Rule:** Keep public documentation in English and private identities, local execution state and one-off reports out of tracked public artifacts while versioning the shared harness.
- **Rationale:** Public developer contracts must survive across machines without exposing private process history or losing the procedures that enforce them.
- **Checked by:** Staged private-identity checks, `.gitignore` and manual tracked-artifact/language review; [benchmarking/policy.py](../scripts/benchmarking/policy.py) is the single owner of the private-identifier pattern, read by [test_no_task_ids.py](../scripts/tests/test_no_task_ids.py) and by the history redaction instead of kept in two copies; [test_no_cloud_ids.py](../scripts/tests/test_no_cloud_ids.py) covers the account-identifier pattern.
- **Example:** Good: tracked standards and contributor documentation plus an ignored audit report; bad: commit private account IDs or local execution notes as user documentation.

## Scripts, gates and operations

### HARNESS-01

- **Rule:** Give each repeated operational policy one documented owner and one executable implementation, with other entry instructions linking or deriving their content.
- **Rationale:** Resource, marker and workflow copies already disagree across tools and documentation.
- **Checked by:** Manual owner/caller map; [doccheck.py](../scripts/doccheck.py) resolves every documented link, § reference, path and command example to an existing owner, so a summary that points at a renamed or moved policy fails, but whether two files state the same policy differently is a review judgment.
- **Example:** Good: adapters call the common policy; bad: copy a weaker policy into a hook.

### HARNESS-02

- **Rule:** Use the execution parser for help and preflight, and give every accepted option a documented effect or explicit deprecation/no-op outcome.
- **Rationale:** Secondary parsers omit supported flags while obsolete flags silently do nothing.
- **Checked by:** [cli_contract.py](../scripts/cli_contract.py), run by doccheck, compares the command examples of the tracked documents and the option tables of configuration.md with the parser that executes them (reporting what it could not read instead of passing it); [test_driver_options.py](../scripts/tests/test_driver_options.py) refuses an option whose `dest` nothing reads; [test_bench_cli.py](../scripts/tests/test_bench_cli.py) runs every bench subcommand's help through the entry point; aliases and preflight are still tested with actual argv by hand.
- **Example:** Good: reuse the benchmark parser and warn for a legacy no-op; bad: advertise `--out` while ignoring it.

### HARNESS-03

- **Rule:** Keep reusable domain libraries independent of command entrypoints and test modules, separating parsing, policy, execution and rendering by responsibility.
- **Rationale:** Imports back into an executed CLI create cycles, duplicate module identities and hidden global state.
- **Checked by:** [check_imports.py](../scripts/check_imports.py) reads the whole AST of `scripts/`, function bodies included, and refuses a production module importing a test module and a cycle outside a declared cluster (a cluster that gains a member or stops cycling fails as stale); [test_release_tree.py](../scripts/tests/test_release_tree.py) and the public checks in [testing.md](testing.md) run it, and import-time side effects stay a manual review.
- **Example:** Good: CLI imports a measurement library; bad: the record library imports the CLI or a test helper module.

### HARNESS-04

- **Rule:** Update concurrent persistent state in locked transactions with atomic replacement and durable stable event identities.
- **Rationale:** Separate read/overwrite and append/rewrite paths lose interleaved updates or receipts.
- **Checked by:** [scripts/harness/storage.py](../scripts/harness/storage.py) (`file_lock`, `atomic_json_replace`, `locked_json_update`) serializes read-modify-replace JSON updates and fsyncs unique temporaries before replacement, and [test_storage.py](../scripts/tests/test_storage.py) exercises concurrent cross-process updates, interrupted publication and callback failures; non-JSON or append-log state stays a manual review.
- **Example:** Good: resolve a message ID under the same lock as append; bad: overwrite a live JSONL log from an old snapshot.

### HARNESS-05

- **Rule:** Require an explicit nonempty selection and complete per-case execution evidence, keeping missing, stale, crashed and skipped cases visible in coverage; a driver that scheduled zero cases (empty selection) exits 2, never 0.
- **Rationale:** Zero-case runs and absent output can otherwise masquerade as successful semantic checking.
- **Checked by:** [contract.py](../scripts/contract.py) and the driver tests, plus [coverage.py](../scripts/coverage.py), which keeps missing inputs and unsupported models in the denominator instead of dropping them; a driver that selects no case fails through the shared judgment (`zero selected cases`) rather than passing, and zero/all-invalid/partial output fixtures cover the remaining drivers.
- **Example:** Good: infrastructure failure for missing output; bad: treat a missing engine result as expected semantic rejection.

### HARNESS-06

- **Rule:** Require successful execution and a validated artifact receipt before reporting success, retaining full logs and checking the producing command's exit status independently or through a pipefail-protected pipeline.
- **Rationale:** Stale PASS files and successful trailing log commands can conceal subprocess or transfer failure.
- **Checked by:** [cloud/session.py](../scripts/cloud/session.py) owns the run's single cleanup and the receipt its results are bound to, [cloud/remote.py](../scripts/cloud/remote.py) is the only transport, and [test_cloud_verify.py](../scripts/tests/test_cloud_verify.py) covers the failure, missing-receipt and stale-artifact paths; an artifact produced outside the cloud lanes stays a manual validation.
- **Example:** Good: retain full output and check the producer exit plus required fetch receipt; bad: infer success from truncated output or return PASS because a stale file exists after exit 3.

### HARNESS-07

- **Rule:** Validate every completed measurement and warmup against its mode contract before aggregation, preserving mismatches and unknown metadata.
- **Rationale:** The final successful sample can hide an earlier wrong verdict or dropped compatibility-mode field.
- **Checked by:** [benchmarking/records.py](../scripts/benchmarking/records.py) normalizes and validates every sample against the schema and mode vocabulary before a row enters the store, and [test_bench_budget.py](../scripts/tests/test_bench_budget.py) keeps every sample-level mismatch, censors a failed warmup, and holds the scale and ttfr aggregates to that mode contract; a sample that never reaches the store stays a manual audit.
- **Example:** Good: retain each sample verdict and mode; bad: compare only the last of three results.

### HARNESS-08

- **Rule:** Admit every expensive pass through one remaining-time budget, refuse admission after expiry and reserve time for required result retrieval and cleanup.
- **Rationale:** A minimum-runtime floor or bypassing runner can start work after the shutdown cutoff.
- **Checked by:** `scripts/tests/test_bench_budget.py` and cloud deadline tests cover existing paths; manual full-runner inventory and expired-clock/no-child-start fixtures.
- **Example:** Good: cap a sample by remaining time; bad: `max(60, remaining)` when remaining is negative.

### HARNESS-09

- **Rule:** Give each child an explicit owner, bounded wait/reap policy and per-child result/accounting record, propagating observation failures.
- **Rationale:** Process-wide CPU deltas and incomplete cleanup lose attribution across concurrent children.
- **Checked by:** [benchmarking/measurement.py](../scripts/benchmarking/measurement.py) accounts children with `wait4`; [test_driver_io.py](../scripts/tests/test_driver_io.py) covers timeout, reap, error and overlap. Review ownership and cleanup from actual process observations.
- **Example:** Good: use the owned child's usage and explicit timeout result; bad: infer its CPU from all children combined.

### HARNESS-10

- **Rule:** Require positive ownership and authoritative predecessor success before destructive actions, treating unavailable observations as unknown and signaling only owned PIDs.
- **Rationale:** Failed inspection or refused removal must not fall through to a signal, deletion or state loss.
- **Checked by:** Manual review of process ownership and cleanup receipts, including injected observation failures. Unknown ownership must not authorize termination.
- **Example:** Good: stop after removal refusal; bad: print the refusal then delete, or kill by a generic process pattern.

### HARNESS-11

- **Rule:** Prove each new guard or gate fails on a known bad state before relying on it, retaining a refusal trigger, passing control and executable fail–repair–pass remediation fixture where applicable.
- **Rationale:** Happy-path or text-presence tests do not prove refusal or that repair actually repairs the failure.
- **Checked by:** Tests of the public command entrypoints, with a known failing input and a passing control; review the boundary-to-test inventory.
- **Example:** Good: run the emitted oracle refresh and recheck unrelated entries; bad: only assert that help mentions refresh.

### HARNESS-12

- **Rule:** Reuse one validator for authorization markers and receipts in every consumer, validating all identity and scope fields.
- **Rationale:** A hook checking only tree identity is weaker than the full tree/HEAD/scope/version contract.
- **Checked by:** Manual validation of revision, tree, scope, producer and format in any reused verification receipt; test malformed receipts and mismatched identities.
- **Example:** Good: delegate marker validation; bad: independently read one JSON field and authorize.

### HARNESS-13

- **Rule:** Preserve lint, test, hook and deployment discovery before moving modules or tests into new paths.
- **Rationale:** Flat globs silently omit nested code after an otherwise correct extraction.
- **Checked by:** [test_driver_options.py](../scripts/tests/test_driver_options.py) follows options through implementation modules; [test_release_tree.py](../scripts/tests/test_release_tree.py) exercises published-tree commands. Compare test and upload discovery before and after a move.
- **Example:** Good: upload packages recursively before moving them; bad: leave the old top-level Python upload glob.

### HARNESS-14

- **Rule:** Match completion checks to the named checkout and artifact type, and make read-only audits deliver an ignored report with unchanged tracked files and no new commits.
- **Rationale:** An implementation-only gate encourages empty commits while an absent report can pass hygiene alone.
- **Checked by:** Manual review of the named checkout, revision, clean status and report evidence. A read-only audit must not require a code commit.
- **Example:** Good: record revision, coverage, severity, file:line, commands and limits in `target/audit/`; bad: commit only to satisfy audit completion.

### HARNESS-15

- **Rule:** Write shared dependencies only through their authorized checkout owner and publish completed installations atomically with a verifiable receipt.
- **Rationale:** A symlinked dependency tree is shared and a partial final filename is not an installation proof.
- **Checked by:** [dependencies.py](../scripts/dependencies.py) owns the shared `third_party/` store: it refuses a write through a linked worktree's symlink before downloading a byte, stages an install beside the final path and publishes it with one rename under a receipt; [test_dependencies.py](../scripts/tests/test_dependencies.py) covers the refusal, interruption, overlay and concurrent-installer paths on synthetic trees and never mutates the shared one.
- **Example:** Good: test an overlay on a private scratch copy; bad: write through a linked worktree's shared dependency symlink.

### HARNESS-16

- **Rule:** Promote only compatible validated oracle evidence, preserve newer evidence and conflicts for review, and confirm preservation before cleanup.
- **Rationale:** Missing-key-only copies discard newer same-key results and provenance mismatches.
- **Checked by:** `scripts/oracles.py`, `scripts/tests/test_oracles.py` and manual promotion-direction review; old/new/conflicting/corrupt fixtures.
- **Example:** Good: compare provenance and config before promotion; bad: delete worker evidence because the destination already has the key.

### HARNESS-17

- **Rule:** Bind supervised messages and receipts to the authoritative task/dispatch identity and create a fresh dispatch for work after settlement.
- **Rationale:** Terminal text and stale IDs do not establish authority for a new worker attempt.
- **Checked by:** Version-matched orchestration contract and manual receipt review; local adapters need active/settled/stale-completion fixtures.
- **Example:** Good: acknowledge a handled delivery and retain the new dispatch receipt; bad: reuse settled lifecycle IDs for a follow-up.

### HARNESS-18

- **Rule:** Replace a source's canonical measurements atomically, including an empty replacement, while preserving independent evidence and checking both directions for orphans.
- **Rationale:** Writing only nonempty groups leaves stale live records after their source is cleared.
- **Checked by:** [benchmarking/records.py](../scripts/benchmarking/records.py) replaces a source's container as a unit under the store lock, including an empty replacement, so a source that stopped producing rows cannot leave stale live ones, and [test_bench_records.py](../scripts/tests/test_bench_records.py) covers the empty and partial replacement directions and the reverse-orphan check.
- **Example:** Good: replace the owned container with an empty one; bad: skip the write and retain old rows.

### HARNESS-19

- **Rule:** Describe the executable actually measured and keep its revision unknown unless independently established.
- **Rationale:** Runner checkout revisions and labels such as “new” do not identify an external binary.
- **Checked by:** [benchmarking/records.py](../scripts/benchmarking/records.py) reads an artifact's own bytes for its revision and keeps it unknown rather than inferring one from a label, and [benchmarking/baselines.py](../scripts/benchmarking/baselines.py) attaches a stored TLC timing only when hardware, verdict and input digest match, leaving it unattached otherwise; the A/B artifact review itself stays manual.
- **Example:** Good: record a proven binary revision or null; bad: infer HEAD from the variant label.

### HARNESS-20

- **Rule:** Follow the current shared-machine/cloud resource policy and reuse valid keyed TLC timings instead of recollecting them for comparisons.
- **Rationale:** Local heavy runs, artificial load and duplicate oracle timing consume shared capacity and distort evidence.
- **Checked by:** [cloud-verification.md](cloud-verification.md) section 1 owns what may run locally (AGENTS.md keeps the pointer), [test_cloud_admission.py](../scripts/tests/test_cloud_admission.py) exercises the admission refusals, a local `bench.py --hog` run is refused, [benchmarking.md](benchmarking.md) and [bench.py](../scripts/bench.py) own the measurement recipe, and [benchmarking/baselines.py](../scripts/benchmarking/baselines.py) is the keyed TLC baseline cache that makes a recollection unnecessary.
- **Example:** Good: reduced bounded local correctness checks and cloud large-model A/B; bad: large local TLC because the machine looks idle.

### HARNESS-21

- **Rule:** Report audit and acceptance counts with their definitions, rerunnable commands and final revision, separating selected/executed/pass/fail/skip and infrastructure failures without treating hygiene as task-specific proof.
- **Rationale:** A zero exit, flaky isolated retry or completion gate alone can overstate coverage.
- **Checked by:** Existing gate summaries and `scripts/verify.py --baseline`; manual final-revision and command/result review.
- **Example:** Good: define physical source/test lines and give the inventory command, then report case judgments separately; bad: quote an unexplained total or the last “ok” line without the process exit.


### HARNESS-22

- **Rule:** Make fake commands used in harness tests record the complete invoked argv, including the executable, so assertions exercise the same command contract as production.
- **Rationale:** A fake that omits the program name can shift arguments and let an assertion test a different invocation than the real process receives.
- **Checked by:** Manual review and tests of the affected public entrypoints, including failing inputs and passing controls. Record the exact commands and observed results; do not assume local-only checks are available.
- **Example:** Good: capture `argv[0]` and every argument in order; bad: log only selected flags and assume the fake's argument positions match the real command.

## Architecture and ownership

### ARCH-01

- **Rule:** Keep normal dependency edges explicit and acyclic, with semantics-free base infrastructure, evaluation-independent representation, runtime-independent liveness algorithms and model-generic search.
- **Rationale:** Lower layers importing concrete evaluation/compiler implementations destroy reusable boundaries.
- **Checked by:** `scripts/dependency_check.py`, which holds the workspace-internal normal, optional and dev edges as an explicit list over `cargo metadata` and refuses an unlisted edge, a stale entry and a cycle without a dev edge; manual metadata review where the list has to change.
- **Example:** Good: runtime accepts `Model`; bad: representation imports interpreter environments to absorb executable IR.

### ARCH-02

- **Rule:** Place shared mechanisms at the lowest semantically appropriate existing layer and keep domain policy with its semantic owner.
- **Rationale:** An available import path does not make value serialization the owner of generic framing or base the owner of TLA+ ordering.
- **Checked by:** Manual import/caller/domain-term inventory and metadata review; preserve bytes and event behavior for moves.
- **Example:** Good: base framing, value serialization and compiler event meaning; bad: a broad utils module holding unrelated semantics.

### ARCH-03

- **Rule:** Export only an identified production API or deliberate test/diagnostic seam, removing obsolete aliases and unused helpers after checking nontextual and supported-feature consumers.
- **Rationale:** Broad exports hide supported seams, but reference counts miss traits, macros, ABI and downstream obligations.
- **Checked by:** Manual public-surface/reachability classification, all-target supported-feature compilation and retired-name search.
- **Example:** Good: a documented backend test facade; bad: export all internals or delete a trait callback for having no direct caller.

### ARCH-04

- **Rule:** Compile declared supported feature configurations and verify intended dependency absence as well as presence with explicit feature forwarding.
- **Rationale:** Default workspace feature unification conceals stale feature-off signatures and ineffective optional dependencies.
- **Checked by:** `scripts/dependency_check.py` (per-package `cargo tree` closure assertions naming what must be absent *and* present, plus a known-bad compile-error probe proving the intended cfg branch is reached), the merge gate's JIT-less workspace build, and `crates/tlx-testkit/tests/feature_policy.rs` for the tier prerequisites.
- **Example:** Good: isolate the CLI no-JIT dependency closure; bad: claim a no-JIT build merely from a runtime switch.

### ARCH-05

- **Rule:** Keep basic, representation, interpreter and compiled differential fixtures separately selectable so lower-layer tests acquire only the tiers they require.
- **Rationale:** Catch-all test features pull the full pipeline into leaf-package iteration.
- **Checked by:** `scripts/dependency_check.py`'s closure assertions on the leaf packages (a representation-only fixture reaching neither Cranelift nor the compiler) and nonzero explicit runs of the moved targets; relocate full-pipeline tests when package-level unification prevents isolation.
- **Example:** Good: shape fixtures without compiler dependencies; bad: enable every model tier for a random-value helper.

### ARCH-06

- **Rule:** Keep builtin metadata and shared value-operation policy at one owner and prove that each claimed execution consumer uses it rather than maintaining an unused authoritative-looking plan.
- **Rationale:** Inert plan objects and independently maintained operation/effect tables let semantic fixes miss executors.
- **Checked by:** [operation_matrix.rs](../crates/tlx-compile/tests/operation_matrix.rs) builds the operation-to-consumer matrix (`ran`, `delegated`, `gap`) from the lowered IR, the generated C and the native plan, so a family that ran nowhere reports a gap instead of an assumed pass; builtin registration and the consumers the matrix does not reach stay a manual review.
- **Example:** Good: both boxed and stored lookup consume the shared schedule; bad: unit-test a policy object that execution never reads.

### ARCH-07

- **Rule:** Define shared tags, widths, offsets, ranges, opcodes and ABI facts once and derive or check all backend consumers against that owned schema.
- **Rationale:** Handwritten Rust/C/JIT layouts drift even when each implementation compiles.
- **Checked by:** Existing encoding/ABI fixtures plus manual consumer inventory; common valid/invalid vectors and Rust/C offset/size/alignment comparisons.
- **Example:** Good: emit constants from the schema and pin wire bytes; bad: update independent numeric literals in three backends.

### ARCH-08

- **Rule:** Share backend decisions through an explicit validated plan independent of emission strategy, with documented identity and lifetime invariants.
- **Rationale:** Emitter-owned mutable discovery couples region IDs and backend ordering to accidental execution sequence.
- **Checked by:** Manual plan/consumer review; native mask, region order/signature, fallback and reference-lifetime tests.
- **Example:** Good: both emitters consume the same immutable verified plan; bad: rediscover regions independently and assume matching IDs.

### ARCH-09

- **Rule:** Co-locate embedded resources with their actual owner or expose an explicit resource API rather than reaching through a sibling crate's private filesystem layout.
- **Rationale:** Cross-crate include paths turn unrelated package moves into compile failures.
- **Checked by:** Manual include-path inventory; resource digest, lookup/shadowing, license and update-instruction checks.
- **Example:** Good: owner-relative unchanged module bytes; bad: include another crate's private asset directory.

### ARCH-10

- **Rule:** Preserve every model capability when changing adapters and observe searches through the existing observer interface rather than incomplete forwarding wrappers.
- **Rationale:** Successor-only wrappers silently drop effects, codecs, checkpointing or liveness hooks.
- **Checked by:** Manual capability/source-to-verdict map; persistence, effects, liveness, restart and diagnostic tests.
- **Example:** Good: use `SearchObserver` and explicit capabilities; bad: forward successors while omitting live atoms.

## Maintaining this standard

Every audit uses the rule index as its checklist and records the reviewed revision, coverage,
findings, commands and limits. State proposed changes to this standard separately from findings
about the code. An audit is not permission to change the audited code.

Maintainers record the decision and reason for each proposal. Accepted changes update this document
and the affected public documentation together, in a focused commit explaining the change and its
evidence. Keep private execution notes outside the published sources.

A mechanically checkable rule gets a lint, test or gate at its existing owner, with a
refusal-trigger test and a passing control; then update **Checked by** to the actual
mechanism and its scope. Until implemented, keep the check explicitly manual. A
repeated violation requires a mechanism rather than another reminder. When a gate
emits a repair command, test the full fail–repair–pass sequence. Avoid a second
validator for the same policy.

Keep IDs stable: add the next unused ID in an area, never renumber or recycle an old
ID. Remove obsolete rule bodies and index entries, update incoming references, and
record retirement/replacement in the change commit; do not leave obsolete requirements
as active checklist items. When rules merge, keep the surviving ID and update all
references. Each update verifies index/body agreement, all four fields, links and
anchors, and runs [doccheck.py](../scripts/doccheck.py), [dependency_check.py](../scripts/dependency_check.py) and [verify.py](../scripts/verify.py). Reviewers
record justified exceptions with scope, evidence and an expiry or removal condition;
exceptions do not silently create a competing standard.
