# Finite abstraction optimization

The experimental abstraction frontend compiles a restricted mathematical TLA+ transition system
into a finite TLA+ model. It uses a typed verification IR, cached analyses, transformation passes,
and a separate checker for each rule. The command and its options are documented in
[configuration.md](configuration.md#finite-abstraction-command).

This workflow emits artifacts only. It does not run the model checker, transfer a success verdict,
validate concrete counterexamples, or prove a result for a configuration family. Ordinary checking
does not invoke these passes. The generated model can be checked by TLC or by any tlx execution
tier; compare those backends on the same generated model.

## Supported fragment

The first rule supports one or more scalar natural-number state variables:

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
and emits no model. It does not claim that the source has no finite abstraction.

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
| `verify.rs` | Check IR structure, the actual before/after correspondence, rule obligations and whole-model finite-domain closure |
| `emit.rs` | Emit standalone TLA+, configuration and explanatory mappings from validated finite IR |

The pass interface receives immutable IR and the analysis manager and returns either no change,
a diagnostic, or a proposal containing replacement IR and rule-specific evidence. Passes cannot
mutate the current model. The manager checks each proposal against the actual preceding model
before committing it. All analyses are invalidated on mutation; no pass-provided preservation
claim can keep stale results alive. Analysis lifetime is one pipeline invocation, with no shared
cache across models or requests.

To add a rule:

1. Implement `Pass` in a new module, reusing or extending the shared analyses. Keep heuristic
   candidate selection in this module.
2. Add its evidence variant and an exhaustive checker dispatch in `verify.rs`. Check actual IR
   correspondence as well as applicability; a rule name alone never authorizes a rewrite.
3. Register the pass in `Pipeline::default`. Add acceptance, refusal, corrupted-evidence and
   composition tests. If the rule extends the input language, extend typed IR, lowering,
   verification and emission together, retaining whole-model finite-domain closure.

The current pipeline contains one pass. It handles independent scalar counter families together;
it does not implement arbitrary relational rule composition. A second invocation on its finite
IR output is a no-op within the pipeline. New preservation contracts, such as overapproximation or temporal properties,
require explicit verification obligations rather than borrowing the counter rule's contract.

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
each concrete representative. Every variable has a checked finite interval afterward, so the
whole state domain is a finite product. This does not promise a practically small search.

## Artifacts and trust boundary

The output consists of `Abstract.tla`, `Abstract.cfg`, and `abstraction.txt`. Generated variables,
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
and exercise the rule's arithmetic at boundary values. These finite test vectors detect defects;
they are not the general proof.

`tlx-cli` integration tests generate models and execute them through the interpreter, compiled IR
and native tier with paranoid checking. They also check abstract violations, refusal without
artifacts, preservation of existing outputs, and isolation from compatibility-mode checking.
