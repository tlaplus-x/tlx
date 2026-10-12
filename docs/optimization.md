# Rule-based optimization

The goal is to reduce the explored state graph while preserving checked verdicts and genuine
counterexamples. A faster expression evaluation is not a state reduction. New reduction rules
need evidence on real specifications, including distinct-state counts and measured runtime.
Commands and options are documented in [configuration.md](configuration.md#optimization-command).

There are two consumers:

- Opt-in checking proves a projection of concrete state through resolved HIR. The existing VIEW
  machinery fingerprints the retained components; actions still produce full concrete states.
  Counterexamples are reconstructed by following actual initial states and successor edges.
- Artifact generation uses a typed transition IR, cached analyses, transformation passes and
  independent rule checkers. Cleanup exposes opportunities for threshold-counter saturation,
  which merges values into representatives. Generation does not transfer a verdict or trace to
  the source. Saturation remains export-only: its mathematical contract does not preserve eventual
  machine overflow, and counter-specific trace lifting is absent.

TLC compatibility mode bypasses opt-in reductions. Unknown expressions retain their referenced
variables; an inapplicable rule leaves ordinary checking unchanged. Artifact generation still
requires its complete input to fit the restricted fragment below. Standalone constant propagation,
predicate simplification and dead-action cleanup no longer run in ordinary checking; they remain
in the artifact pipeline as preparation for state reduction.

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

## Deriving reductions from compiler analysis and mathematics

Use compiler analyses to discover a candidate equivalence, then prove it against the configured
transition system. The relevant compiler mechanism is a monotone dataflow problem with joins,
transfer functions and a fixed point, as in [LLVM's dataflow introduction](https://clang.llvm.org/docs/DataFlowAnalysisIntro.html).
For projection, the implemented equation is `Live = Roots union Dependencies(Live)`. Its solution
identifies which components must remain in the state key; it does not delete executable assignments.

For a proposed state map `P`, related reachable states must satisfy both:

- All checked observations agree whenever `P(s) = P(t)`.
- The projected successor sets agree: `{P(u) : Next(s,u)} = {P(v) : Next(t,v)}`.

Together with coverage of projected initial states, these conditions justify an exact quotient.
Fewer reachable equivalence classes, rather than simpler expressions, deliver the reduction.
An overapproximation has a different contract: it can admit spurious violations and needs concrete
validation and refinement before returning a counterexample.

[Abstract interpretation](https://www.di.ens.fr/~cousot/COUSOTpapers/POPL77.shtml) provides a basis
for extending the analyses: inductive intervals, finite value sets and relational facts can prove
which transfer functions and partitions are safe. Range information alone does not reduce states;
it must justify a projection, a value partition, or another reduction. General interval analysis
and partition refinement are future extensions, not current checking capabilities. For example,
merging all counter values above a threshold additionally requires proving that every update and
observation respects that partition; a later decrement or exact-value test can invalidate it.

The desired domain describes distinguishable values, not just the numeric values that can occur.
If no observation or future transition distinguishes values at or above 10, the partition can be
`{0}, ..., {9}, {10, 11, ...}`. If `N > 10` is observed, 10 must remain separate from the class
above 10. Derive reachable domains from initialization and transitions; a property being checked
is an observation to preserve, not an assumption that can justify the reduction.

The same criterion applies recursively to structured values. A candidate map must respect every
observed operation and transfer, including definedness and errors:

| Value | Candidate partition | Obligations |
|---|---|---|
| Array or list | Partition each element | Preserve observed indices, order and length; reads, writes and sequence operations must respect the element partition. |
| Map or record | Partition selected values or fields | Preserve observed keys and domains; value updates and lookups must agree after projection. Merging keys requires a separate proof. |
| Set | Map each element to its class | Prove that membership, equality, removal and other used operations respect the classes. Cardinality generally forbids collapsing distinct elements into one. |

For example, a list `<<11, 20>>` may have the key `<<Above10, Above10>>` when the two exact values
are unobservable. Mapping the set `{11, 20}` to `{Above10}` loses its cardinality and cannot
preserve a cardinality check. Retaining multiplicities can preserve cardinality, but does not by
itself preserve exact membership or removal. Finite element domains also do not bound list length
or map domains: those dimensions need their own bounds or proved partitions for a finite state
space. These are requirements for future structured partitions, not implemented checking rules.

One concrete extension is field liveness conditioned on a finite control state. In the external
`pragmatic/database-blob/naive` and `improved` specifications, `serverStates` maps servers to
records. A record's `state` field determines which of `userId`, `metadata` and `image` can still
affect execution. Completed requests leave old field values behind; new requests overwrite them
before use. A candidate projection forgets these fields during every phase where they are dead.
It must propagate liveness backward through phase transitions: clearing a field only in `waiting`
is not sufficient to establish the successor-class equation if the next phase exposes its old
value again. Type predicates also need a preservation proof from Init and Next; they cannot simply
be assumed true. The phase-field rule below derives this projection automatically from the
configured source. It does not require a user-written VIEW or changes to the specification.

The checking implementation applies this reasoning through conservative projection rules. Their
dataflow analyses are deliberately bounded. Add richer transfer summaries when an external
specification demonstrates a useful reduction, with explicit definedness, overflow and trace
obligations; do not build a general framework merely to imitate LLVM's class hierarchy.

## Unobserved state projection

`projection.rs` computes a conservative cone of influence using backward dataflow analysis.
Guards, observations and unknown uses seed the live set. A recognized copy `v' = u` adds a
read-dependency edge from `v` to `u`; literals have no inputs. A worklist propagates liveness
to a least fixed point. A cycle of copies without a path to an observation stays dead; observing
one member retains the needed cycle. The current transfer vocabulary is scalar literals,
whole-variable copies and UNCHANGED. Initialization of omitted variables must use literals.
Other expressions conservatively retain their referenced variables.

This is a structural rule; it does not inspect variable, action or module names. For example:

```tla
Init == x = 0 /\ tag = "init"
Next == (x' = 1 - x /\ tag' = "flip")
     \/ (UNCHANGED x /\ tag' = "idle")
Inv == x \in {0, 1}
```

There are five reachable concrete states. Matching states by `<<x>>` leaves two classes.
Each stored representative still contains its real `tag`; the rule does not assign a canonical
replacement to the variable or alter `Next`.

The proof obligations are:

1. Init assigns an integer, Boolean or string literal to the omitted variable. Integer literals
   must fit the evaluator's integer range. Every recognized next-state binding is a literal
   assignment, copy of a fully specified current-state value, or UNCHANGED. Unknown transfers
   retain their target and referenced inputs.
2. At most one binding can occur on any syntactic alternative of Init or Next. Conjunction adds
   binding counts; disjunction, IF and CASE take their maximum. This rules out implicit guards
   such as `UNCHANGED tag /\ tag' = "idle"`, which test the old value even without a read.
3. The live set contains all guard, bound, selected invariant, initial or action property, state
   or action constraint, and alias dependencies. It is closed under the inputs of every retained
   update. Primed references outside recognized assignments count as reads too.
   Calls and LET helpers are followed by resolved definition identity. Operator actuals are
   scanned conservatively, including by-name arguments and captured reads.
4. Referenced expressions have no observable builtin effects. Unknown operator constants,
   unresolved bodies, recursive action expansion or exhausted analysis budgets disable the rule.
   Read-dependency scanning handles recursive definitions with a visited set. Traversal is bounded
   by 100,000 nodes and depth 128; exhaustion yields no projection.
5. The execution boundary excludes temporal checking, configuration overrides, possible predicates,
   postconditions and existing VIEW. Symmetry composition additionally requires the equivariance
   check described below.

**Correctness argument.** Let `P(s)` retain every non-omitted component. Related reachable states
have equal retained values; every stored component is fully specified. A guard or
other observed expression therefore evaluates identically in related states. On each action
alternative, a forgotten variable receives a literal, copies a defined value, or remains unchanged,
without constraining that alternative: the single-binding condition prevents an assignment from becoming an equality
test against an already-bound value. All retained updates have identical inputs. Consequently,
every concrete step has a corresponding step with the same projection from every related state,
and vice versa. Invalid or incomplete alternatives remain invalid independently of omitted values.
Every projected initial class has an actual initial representative. This gives a bisimulation on
the reachable graph with identical observations and enabledness, preserving safety and deadlock.

Counts and maximum search depth need not be preserved. The implementation stores concrete
representatives and reuses class-aware replay, so a reported finite counterexample consists of
actual source steps, including actual omitted values. Temporal
properties remain outside the applied contract; a finite quotient lasso alone would not establish
a genuine concrete liveness counterexample. The HIR analyzer is trusted implementation code with
this source-level argument and regression tests, not an independently checked proof certificate.

CCF's external `consistency/Consistency.tla` has this pattern: `action` is initialized to `"Init"`
and assigned labels by the actions, but guards and `TypeOK` do not read it. A bounded local wrapper
around the unchanged source demonstrates an actual reduction; it is not the upstream unbounded
configuration. Bounds and measurements belong with reproducible benchmark evidence.

## Length-only sequence projection

`phase/sequence.rs` shares the bounded normalizer, branch analysis and forward structural
value domains with field projection. It replaces a top-level sequence by its exact length in
the state key when its contents cannot affect any selected observation or successor class.
Concrete sequences and executable actions remain unchanged. Existing whole-variable and field
projections retain priority; this rule runs when they do not apply.

The rule requires a proved sequence domain from Init and every Next alternative, exactly one
binding per alternative, and transfers made from tuples, self-copies, Append and IF expressions.
Every tuple element, appended expression and IF condition is checked for content reads; errors
in those expressions remain observable. Other uses must read the sequence through Len, or a
structural membership predicate that the inferred domain proves always true. A checked type
invariant is never assumed. Head, indexing, sequence equality, unknown transfers, effects,
duplicate bindings and unresolved normalization decline the affected projection.

For related states, the retained variables and sequence lengths agree. Each accepted transfer
has the same resulting length, each guard and remaining expression has the same inputs, and
proved membership predicates have the same truth value without type errors. Thus successor
classes, safety observations and deadlocks agree. Primed reads receive the same checks.
Initialization supplies actual concrete representatives, and existing replay reconstructs
concrete counterexamples. Exact lengths retain length-dependent arithmetic and overflow
behavior; the rule does not saturate counters. The existing safety-only boundary and symmetry
composition requirements apply.

The external `Examples/specifications/FiniteMonotonic/ReplicatedLog.tla` motivates this rule.
Its actions and `Safety` use `Len(log)`; `TypeOK` additionally checks `log \in Seq(Transaction)`.
With two transaction values there are `2^k` concrete log contents of length `k`, but only one
length class for each retained `executed` map. The mathematical model remains unbounded after
projection: log length and execution counters can still increase. Measurements of a finite
length prefix are diagnostics of this reduction, not a completed check of the unbounded model.
The upstream `MCReplicatedLog` configuration also selects liveness and a handwritten reduction;
that separate configuration does not establish applicability of this safety-only rule.

## Phase-dependent field projection

`phase.rs` derives a finite control field and field liveness for a record, or a fixed-domain map
of records. Names have no special meaning. The motivating inputs are the unchanged external
database-blob specifications described above; request data becomes irrelevant in different phases.
BookKeeper's `LedgerChaining` has the same pattern in client records: cached ledger metadata,
ledger lists and list versions cease to matter in phases that refresh them before use. The rule
also handles its configured model-value phases and sequence-valued fields.

The analysis first expands resolved first-order calls and LET helpers into an analysis-only tree,
renaming bound locals to preserve scope. A forward fixed point over Init and every Next alternative
infers possible scalar values and structural shapes. Unknown expressions widen to an unknown
domain. Function key sets must be exact, rather than upper bounds on possible elements. Properties
being checked never narrow these inferred domains. A structural type membership observation can
be discharged only when the inferred domain proves it always true without hiding type errors.
The domains include integer lower bounds, sequence elements, record fields and function ranges.
Integer addition and function override can establish the types of cached data copied from growing
collections. Unknown function domains can supply range facts, but only exact fixed domains qualify
as projected maps. These facts prove observations such as membership in `Seq(Nat)`; they do not
truncate counters or bound sequence length.

For each candidate control field, backward analysis computes `Live[phase, field]`:

1. Reads in guards, update expressions and configured observations seed liveness. Every explicit
   update expression is scanned, even when its result is otherwise dead, to retain error behavior.
   A recognized control guard restricts subsequent reads only after the guard has been evaluated.
   Bound expressions, whole-record uses and cross-actor reads are conservative. First-order
   by-name substitution keeps actual reads in the callee's control context; effectful actuals
   still decline expansion even when unused.
2. A recognized EXCEPT update changes fields of one record, or one bound actor's record in a
   fixed-domain map. The actor's inferred key domain must be contained in the map domain. Duplicate
   writes, unknown transfers and multiple bindings of the candidate variable decline the rule.
   Analysis expands EXCEPT's `@` into a read of the updated point only when preceding writes
   provably cannot overlap it. Uncertain aliasing declines expansion, including uses through LET.
3. For a transition from phase `p` to `q`, every field live in `q` that is not overwritten becomes
   live in `p`. Propagate until no liveness fact changes. The control field always remains live.

The generated VIEW retains every other variable and replaces each dead field by one sentinel in
the state key. It preserves record fields, map keys and control values. Executable HIR and concrete
stored states are unchanged. The current implementation applies one projection rule per run:
whole-variable projection takes precedence, then the proved phase candidate projecting the most
fields (ties retain source traversal order). This heuristic does not predict reachable state counts. It does
not combine several candidate records or compose with user VIEW. Equivariant projections can
compose with symmetry as described below.

**Correctness argument.** Forward inference establishes an inductive overapproximation of reachable
values: it contains Init and is closed under all recognized Next alternatives. Within this domain,
states with equal projected keys agree on every field live in their common control phase. Ordered
read roots therefore preserve branch guards, definedness, errors and checked observations. Explicit
update expressions have equal inputs in related states. A field carried into a live successor
position is live in the predecessor by backward closure; an overwritten field receives an equal
value. Other map entries retain their control and live fields. Thus corresponding branches produce
the same projected successor classes in both directions, with the same enabledness. Together with
concrete initial representatives this proves an observation-preserving bisimulation, supporting
safety, deadlock checking and concrete counterexample replay under the shared checking boundary.

This is a trusted static analysis with a correctness argument and regression tests, not an
independently checked proof certificate. Recursive expansion, higher-order calls, unknown operator
constants, effects and exhausted analysis budgets decline the rule. Control domains are limited to
32 mutually comparable literal or configured model values, candidate records to 32 fields, and expanded actions to 512
alternatives. It does not infer numeric threshold partitions or remove sequence lengths or map keys.

## Composing projection with symmetry

An automatic projection can compose with declared symmetry or statically proved automatic
symmetry. Forced and runtime-guarded automatic groups retain their existing path. A declared
group remains a user assertion; composing a proved projection does not prove that declaration.

Let `P` be the proved projection and `G` the applied group. Require
`P(g(s)) = g(P(s))` for every `g` in `G`. Whole-variable projection satisfies this directly.
Phase projection is built from record updates, map construction, fixed field names and phase
comparisons. Those operations commute with permutation when each introduced phase constant is
fixed by every group element. The interpreter checks that condition against the evaluated
configuration values and declines composition if it cannot establish it.

State identity is the orbit of `P(s)`: project first, then canonicalize. Canonicalizing the full
state first would let forgotten fields choose the representative, losing potential merges.
Equivariance makes the group action well-defined on projected classes. Since both the projection
and the valid symmetry preserve observations and matching successors, their composed quotient
preserves safety verdicts, enabledness and concrete replay. Existing user VIEW semantics, including
TLC's order of combining VIEW with SYMMETRY, remain unchanged.

The interpreter uses a total structural order for projected keys, since a dead-field Boolean
sentinel and a live integer can coexist under different actor permutations. The compiled tier
reuses permutation plans and orbit fingerprinting on the projected tuple's encoding. Unsupported
projected shapes, value-store shapes and escape mode use the interpreter's by-value key; actions
can still execute as compiled code. This keeps one canonicalization policy per execution path
without treating store handles as semantic values.

## Checking boundary

Opt-in reductions support exhaustive checking without simulation, symmetry diagnostics, coverage
or checkpoint/recovery. Dumps contain concrete representatives of reduced classes. Rule remarks
name the omitted variables or projected fields; reduced statistics are labeled. Unknown source constructs do not
reject an otherwise valid model. Interpreter and compiled tiers share the same projection and
replay contract through the existing model capabilities.
Compiled execution infers result shapes for structural anonymous VIEW expressions from the current
state layout, then uses the existing VIEW compiler. Rebuilding a state layout rebuilds these shapes;
unknown shapes retain interpreted state-key evaluation. This execution-layer analysis is separate
from the state-reduction proof. Measure the complete check: fewer explored states can still cost
more runtime when projection overhead dominates.

## Artifact input fragment

Artifact generation supports one or more scalar natural-number state variables:

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
| `projection.rs` | Prove unobserved state projection from resolved HIR for ordinary checking |
| `phase.rs`, `phase/` | Infer structural domains and phase-dependent field liveness for checking |
| `emit.rs` | Emit standalone TLA+, configuration and explanatory mappings from validated finite IR |

The pass interface receives immutable IR and the analysis manager and returns either no change,
a diagnostic, or a proposal containing replacement IR and rule-specific evidence. Passes cannot
mutate the current model. The manager checks each proposal against the actual preceding model
before committing it. All analyses are invalidated on mutation; no pass-provided preservation
claim can keep stale results alive. Analysis lifetime is one pipeline invocation, with no shared
cache across models or requests. Cached analyses include both observation thresholds and
inductively constant state candidates.

The artifact pipeline has two stages. First, constant propagation, predicate simplification and dead-action
elimination repeat until the IR stops changing. Saturation then runs with predicate simplification
and dead-action elimination, again to a fixed point. This ordering removes irrelevant thresholds
before choosing caps. Each stage has a limit of 64 rounds; failure to converge emits a diagnostic
and no artifact. The manager validates even a proposal that claims to make no effective change.

To add an artifact rule:

1. Implement `Pass` in a new module, reusing or extending the shared analyses. Keep heuristic
   candidate selection in this module.
2. Add its evidence variant and an exhaustive checker dispatch in `verify.rs`. Check actual IR
   correspondence as well as applicability; a rule name alone never authorizes a rewrite.
3. Register the pass in `Pipeline::default`. Add acceptance, refusal, corrupted-evidence and
   composition tests. If the rule extends the input language, extend typed IR, lowering,
   verification and emission together, retaining whole-model finite-domain closure.

For a checking reduction, analyze resolved HIR and return a proved reduction plan without
rewriting executable actions. Extend the existing state-identity mechanism only when needed.
Specify the equivalence relation, all observations it preserves and the concrete replay contract;
add positive and refusal tests, and demonstrate fewer states on an external model. Add a shared
pass abstraction only when multiple implemented reductions need it.

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

Projection tests separately cover action alternatives, recursive read dependencies, higher-order
actuals, duplicate bindings, primed reads and effects. CLI tests exercise state-count reduction,
concrete safety/deadlock traces, configuration observations, temporal refusal and TLC bypass in
all execution tiers with paranoid cross-checking.
