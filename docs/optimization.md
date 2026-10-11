# Rule-based optimization

The optimizer uses a typed transition IR, cached analyses, transformation passes, and an
independent checker for each rule. Optimization is the umbrella: constant propagation,
predicate simplification and dead-action elimination preserve concrete states; counter
saturation is an abstraction optimization that merges values into representatives.
Commands and options are documented in [configuration.md](configuration.md#optimization-command).

There are two consumers of the same verified pass framework:

- Opt-in checking runs the exact cleanup stage and writes validated IR back into the configured
  HIR roots before interpreter or compiler caches exist. It retains concrete variable values,
  original invariant names and source locations. Existing execution and reporting paths produce
  verdicts and genuine traces directly; no abstract-to-concrete trace transfer is needed.
- Artifact generation also runs saturation, then emits a finite mathematical model. Generation
  does not run the checker or transfer its verdict. Check the generated model separately; counts
  and traces describe its graph. Saturation is not enabled in ordinary checking, because its
  mathematical contract does not preserve eventual machine overflow and trace lifting is absent.

TLC compatibility mode bypasses the opt-in pipeline, including its fragment restrictions. This
policy applies to this new pipeline, not to all existing semantics-preserving compiler work.
Unsupported opt-in inputs are diagnosed rather than silently checked without optimization.

## Overlap with execution optimization

[design.md](design.md#21-crate-map-and-dependency-edges) owns the division between semantic
optimization and execution compilation. The semantic pipeline is deliberately restricted; it is
not a general-purpose HIR optimizer. There is nevertheless some general-purpose work inside it:

| Current mechanism | Overlap and reason for keeping it here |
|---|---|
| `lower.rs`: configured constant substitution, first-order call and LET expansion, constant comparison evaluation | Overlaps compiler constant folding and inlining (`tlx-compile/src/lower/expr.rs`, `typed.rs`). Here it normalizes the complete configured roots into the closed IR so that proof rules can inspect them; it is not an inlining profitability policy. |
| `simplify.rs`: Boolean identities, constant negation, empty/singleton conjunction and disjunction cleanup | Local simplification also occurs during execution lowering and native compilation. This small cleanup consumes facts exposed by semantic rules and makes FALSE guards visible to subsequent passes. The implementations are not identical Boolean optimizers. |
| `simplify.rs`: domain-implied comparisons | Uses the IR's natural, proved-singleton or saturation domain. Those facts are not merely compile-time literal values. The current pipeline does not infer general inductive counter intervals from guards. |
| `constant.rs`: inductively constant state | Proves a value from initialization and every remaining update. Backend constant folding alone does not establish that a state variable stays constant across the transition system. |
| `dead.rs`: removal of FALSE-guard actions | Analogous to local dead-branch cleanup, but removes whole actions from the semantic model. This can expose another inductively constant variable before saturation chooses its thresholds. It is not a general reachability solver. |

For example, a proved constant `fixed = 7` makes `fixed /= 7` false. Boolean cleanup then makes
an enclosing action guard false, and action removal can reveal another constant. Waiting until
native compilation to perform that cleanup would miss its role in the semantic fixed point and
would not benefit interpreter execution or exported models.

The independent checks in `verify_cleanup.rs` intentionally validate the transformation without
calling its candidate-generation logic. This is a correctness boundary, not redundant backend
optimization to deduplicate. Keep effect/error behavior, integer semantics and enumeration
requirements in mind before sharing simplification code across these IRs: semantic predicates
are a closed, pure fragment; arbitrary execution expressions are not.

There is no measured claim that this frontend cleanup speeds up work already handled by the
compiler. Further generic rewrites belong here only when a concrete semantic consumer needs
them; otherwise extend the existing execution optimizer.

## Exact checking boundary

The exact path accepts the fragment below and requires distinct configured INIT, NEXT and
INVARIANT definitions when applying rewrites. It supports exhaustive checking, not simulation,
symmetry diagnostics, coverage or checkpoint/recovery. Graph and counterexample dumps still
contain concrete states. See the option reference for the supported combinations.

The cleanup rules preserve initialization, reachable state values and transitions, and invariant
truth on reachable states. They never replace increment with saturation. Constant-state
propagation retains the original value in the state vector, including in failing initial states.
The HIR writer keeps invariant predicates at state level even when simplified to TRUE or FALSE,
and keeps an empty Next relation at action level. It invalidates level summaries and rebuilds
expression IDs before execution creates caches. Rule remarks identify applied transforms;
optimized-run statistics are labeled rather than presented as TLC compatibility evidence.

## Supported fragment

The optimizer supports one or more scalar natural-number state variables:

- Initialization is a conjunction assigning each variable one configured natural literal.
- Next is a disjunction of actions. Each action is a conjunction of state guards and exactly one
  update per variable: unchanged, reset to zero, or increment itself by one.
- Guards and named state invariants are Boolean combinations of comparisons between a counter
  and a configured natural literal. The supported comparisons are `=`, `/=`, `<`, `<=`, `>`, `>=`;
  Boolean combinations use conjunction, disjunction, negation and implication.
- First-order operator calls and LET bodies are expanded with resolved local identities. INSTANCE
  substitutions already resolved by the semantic frontend are analyzed in their substituted form.
- Global scalar integer constant assignments are bound before analysis. Observed literals and
  initial values must be natural numbers representable by the generated backend.
- ASSUME expressions must reduce to literal TRUE or a true comparison of supported constants.

Every state variable, action and configured invariant must translate. Missing updates, cross-counter
comparisons and copies, decrement, indexing, structured values, quantifiers, recursive or
higher-order calls and unsupported observations are refused. Normalization has a shared budget of
100,000 visited expression nodes and a maximum nesting depth of 128; exceeding it is inconclusive
and emits no model. It does not claim that the source has no finite optimization.

Temporal specifications/properties, exploration constraints, views, symmetry, aliases,
postconditions, possible predicates and configuration overrides are rejected. Deadlock checking
must be explicitly disabled in the input configuration. These restrictions prevent an observation
or assumption outside the rule's contract from silently disappearing.

## Pipeline and ownership

The implementation lives in `crates/tlx-sema/src/optimize/`, above execution-specific lowering:

| Module | Responsibility |
|---|---|
| `lower.rs` | Bind the supported configuration and normalize resolved HIR into the closed verification IR; refuse unknown effects/uses |
| `ir.rs` | Natural/finite domains, complete action updates, state predicates and source locations |
| `analysis.rs` | Lazily compute thresholds from all guards and properties; own cached analysis results |
| `passes.rs` | Schedule passes; validate proposals before commit; invalidate analyses after every committed rewrite |
| `counter.rs` | Propose threshold-counter saturation and its rule parameters |
| `constant.rs` | Propagate state values proved constant by initialization and every remaining update |
| `simplify.rs` | Fold domain-implied comparisons and Boolean identities |
| `dead.rs` | Remove actions with a proved FALSE guard, retaining source order |
| `verify.rs` | Check IR structure, the actual before/after correspondence, rule obligations and whole-model finite-domain closure |
| `verify_cleanup.rs` | Independently check constant propagation, predicate equivalence and dead-action evidence |
| `check.rs` | Write exact cleanup results into configured HIR roots, preserving concrete states and original names |
| `emit.rs` | Emit standalone TLA+, configuration and explanatory mappings from validated finite IR |

The pass interface receives immutable IR and the analysis manager and returns either no change,
a diagnostic, or a proposal containing replacement IR and rule-specific evidence. Passes cannot
mutate the current model. The manager checks each proposal against the actual preceding model
before committing it. All analyses are invalidated on mutation; no pass-provided preservation
claim can keep stale results alive. Analysis lifetime is one pipeline invocation, with no shared
cache across models or requests. Cached analyses include both observation thresholds and
inductively constant state candidates.

The artifact pipeline has two stages. The exact-check pipeline runs only the first stage. First, constant propagation, predicate simplification and dead-action
elimination repeat until the IR stops changing. Saturation then runs with predicate simplification
and dead-action elimination, again to a fixed point. This ordering removes irrelevant thresholds
before choosing caps. Each stage has a limit of 64 rounds; failure to converge emits a diagnostic
and no artifact. The manager validates even a proposal that claims to make no effective change.

To add a rule:

1. Implement `Pass` in a new module, reusing or extending the shared analyses. Keep heuristic
   candidate selection in this module.
2. Add its evidence variant and an exhaustive checker dispatch in `verify.rs`. Check actual IR
   correspondence as well as applicability; a rule name alone never authorizes a rewrite.
3. Register the pass in `Pipeline::default`. Register it in `Pipeline::exact` only if its checked
   contract preserves concrete reachable states and valid counterexamples without lifting. Add acceptance, refusal, corrupted-evidence and
   composition tests. If the rule extends the input language, extend typed IR, lowering,
   verification and emission together, retaining whole-model finite-domain closure.

The four passes compose through checked intermediate models. They handle independent scalar
counter families and pure state predicates, not arbitrary relational abstractions. Running the
pipeline on its optimized IR is a no-op. New preservation contracts, such as overapproximation or
temporal properties, require explicit verification obligations.

## Cleanup rules and their arguments

**Constant-state propagation** uses the initial value and every remaining action to prove a
singleton domain. An unchanged update preserves any initial value; reset preserves it only when
that initial value is zero. A genuine increment prevents this proof. Guards and target properties
are never assumed to prove constancy. The pass retains the variable with its exact value, replaces
its comparisons by truth values, and normalizes its updates to unchanged. The checker independently
checks the induction conditions, all substitutions, source metadata and unchanged parts of the IR.

Exact singleton domains and saturation domains are distinct. The constant pass never relabels a
saturated representative as an exact original value: a saturated zero may represent an unbounded
concrete counter. Saturation preserves singleton domains established by earlier passes.

**Predicate simplification** folds comparisons whose truth is determined by the variable's
domain, negations of constants, and Boolean identity/absorbing elements. For example, a natural
counter always satisfies `c >= 0`, and `FALSE /\ P` is false in this pure, total IR. The generator
uses interval comparisons. The independent checker partitions a scalar comparison's domain at
its literal and the literal plus one, where its truth can change, and recursively checks the
Boolean rewrite. This partition check covers the entire domain; it is not bounded state sampling.
In particular, equal truth at an interval's endpoints is insufficient to fold an equality whose
matching value lies inside the interval.

**Dead-action elimination** removes only actions whose guard has become literal FALSE. Its
certificate lists the retained source indices. The checker requires every omitted guard to be
FALSE and every retained action to be identical and in source order; it also preserves all
properties and initialization. If all actions disappear, emission produces an impossible action:
a false state guard conjoined with an explicit UNCHANGED tuple. This has the empty transition
relation while retaining action level; TLC rejects a constant-level `Next == FALSE`.
Initial invariants are still checked, including ones simplified to FALSE. The emitter expresses
a false invariant as the state-level predicate `v0 /= v0`, because TLC rejects an invariant defined
as constant FALSE during configuration instead of checking it on the initial state.

These passes can make previously unusable threshold partitions finite within the backend range.
For example, an impossible action guarded by `FALSE /\ c > 2147483647` no longer forces an
unrepresentable saturation cap. Unsupported source expressions are still rejected during lowering,
even when they occur in a syntactically dead branch; cleanup never bypasses the language contract.

## Counter rule and its argument

For each counter, select a cap K from every guard and target invariant. Comparisons `< T` and
`>= T` require K at least T. Comparisons `= T`, `/= T`, `<= T` and `> T` require K greater than T.
Take the largest required cap; a counter with no observations has cap zero.

The map is `alpha(c) = min(c, K)`. Abstract values below K are exact; K denotes every concrete
value at least K. Initialization is mapped through alpha. Reset and unchanged retain their form.
Increment becomes a conditional that increments below K and stays at K otherwise. In particular,
the increment at K is retained as a self-loop; exploration is not truncated.

Over mathematical naturals:

```text
alpha(c + 1) = min(alpha(c) + 1, K)
alpha(0) = 0
alpha(c) = alpha(c)
```

Each allowed comparison is constant on the interval from K upward. Consequently its truth value,
and every Boolean combination of such comparisons, is unchanged by alpha. The checker verifies
those conditions directly against source observations, without trusting the pass's threshold
analysis. It also checks initialization, every update, every action guard, the property set and
source metadata against the proposed model. The complete update vectors prevent missing actions
or unassigned variables from passing validation.

Thus a concrete action maps to its abstract action, and the abstract action can be lifted from
each concrete representative. Every variable has a checked finite interval or singleton afterward, so the
whole state domain is a finite product. This does not promise a practically small search.

## Artifacts and trust boundary

The output consists of `Optimized.tla`, `Optimized.cfg`, and `optimization.txt`. Generated variables,
actions and invariants have collision-free synthetic names; the report maps them to source names
and locations and explains every counter cap. The destination must be new. Semantic refusal
creates no destination; an I/O failure returns an error and may leave incomplete files. The report
is written last.

The correspondence argument concerns mathematical natural-number semantics. It does not preserve
the concrete checker's eventual integer-overflow error on an unbounded counter. Generated
saturating increments test the cap before adding, so they do not overflow at the maximum supported
cap. Counts, depth and trace values describe the generated graph, not the original graph.

The trusted components are the existing semantic frontend, restricted lowering, Rust rule checker
and emitter. The rule argument above is not a Lean or other proof-kernel certificate. Checking
the generated artifact additionally trusts the selected model checker and its execution settings.
The text report is not a reusable proof authorization: there is no evidence cache, automatic
verdict transfer or persisted-certificate acceptance API. Regenerate after any source,
configuration, property or tool change. Treat generated violation traces as abstract until
concrete reconstruction and validation are implemented.

## Validation

`tlx-sema` integration tests cover thresholds, source normalization, constants, substitutions,
independent counters and unsupported uses. Internal optimizer tests deliberately corrupt evidence,
updates, guards, properties and initialization; test stale proposals and analysis invalidation;
and exercise arithmetic and predicate rewrites at boundary and interior values. Cleanup tests
cover false guards, empty Next, mixed singleton/saturation domains, cascaded constants, and
preservation of failing initial invariants. These finite test vectors detect defects;
they are not the general proof.

`tlx-cli` integration tests generate models and execute them through the interpreter, compiled IR
and native tier with paranoid checking. They also check abstract violations, refusal without
artifacts, preservation of existing outputs, and isolation from compatibility-mode checking.
