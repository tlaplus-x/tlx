# Rule-based optimization

The goal is to reduce the explored state graph while preserving checked verdicts and genuine
counterexamples. A faster expression evaluation is not a state reduction. New reduction rules
need evidence on real specifications, including distinct-state counts and measured runtime.
Commands and options are documented in [configuration.md](configuration.md#optimization-command).

There are two consumers:

- Opt-in checking proves a projection of concrete state through resolved HIR. The existing VIEW
  machinery fingerprints the retained components; actions still produce full concrete states.
  Counterexamples are reconstructed by following actual initial states and successor edges.
- The internal artifact candidate pipeline uses a typed transition IR, cached analyses,
  transformation passes and independent rule checkers. Public export is disabled until connected
  certificates cover its passes. Cleanup exposes opportunities for threshold-counter saturation,
  which merges values into representatives. Generation does not transfer a verdict or trace to
  the source. Saturation remains export-only because counter-specific trace lifting and integration into
  ordinary checking are absent.

Opt-in checking permits proved reductions over mathematical integers to eliminate eventual
machine overflow, as specified in [compat.md section 0](compat.md#0-the-three-tiers).
Concrete expressions still use checked arithmetic; this does not suppress encountered errors
or enable arbitrary-precision evaluation. Safety verdicts and counterexamples must remain valid
under the rule's mathematical semantics.

TLC compatibility mode bypasses opt-in reductions. Unknown expressions retain their referenced
variables; an inapplicable rule leaves ordinary checking unchanged. Artifact generation still
requires its complete input to fit the restricted fragment below. Standalone constant propagation,
predicate simplification and dead-action cleanup no longer run in ordinary checking; they remain
in the artifact pipeline as preparation for state reduction.

## Proof coverage

Every automatic state reduction must have a compiler-generated certificate for its actual
application. This is enforced before installing a projection or publishing an export.
Shared algebra, Rust applicability checks and bounded tests do not satisfy the requirement.
Ordinary checking emits Lean without invoking Lean; development verification is explicit.

| Reduction | Connected certificate | Current behavior |
|---|---|---|
| Unobserved variables | Literal initializations, literal/copy/frame updates; independent retained state | Enabled within this subset |
| Finite history summary | Summary-dependent guards, retained updates and event values; independent bounds and initialization | Enabled within this subset |
| Ordered allocation | One scalar frontier, retained initial anchor, literal nonnegative increments | Enabled within this subset |
| Phase-dependent fields | Missing | Candidate analysis only |
| Sequence length | Missing | Candidate analysis only |
| Relative ages | Fixed-domain timestamp maps, keep/reset/erase transfers, threshold tests, finite filters and quantifiers | Enabled within this subset |
| Combined age/history | One age projection and one finite history; shared branch choices and retained core | Enabled within this subset |
| Nested ordered allocation and live versions | Missing | Candidate analysis only |
| Automatic symmetry, including forced/guarded paths | Missing | Suggestions/diagnostics only; never applied |
| Counter export and its cleanup pipeline | Missing | Internal proposal only; CLI refuses without creating artifacts |
| Projection composed with symmetry | Missing | Automatic projection refused |

All enabled projection certificates prove initialization, successor correspondence from
every representative, preservation of state observations, concrete counterexample lifting,
and deadlock preservation. Liveness, constraints, action/initial properties and aliases
remain outside this certified checking subset. Explicit user VIEW/SYMMETRY declarations
retain the TLC contract; they are not compiler-certified automatic reductions.

The sections describing unsupported rules below document candidate algorithms and prior
evidence, not enabled reductions or current performance claims. Disabling a candidate is
not a proof of it: completing these certificates remains work.

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
be assumed true. The phase-field candidate below derives this projection from the configured source;
application awaits a connected certificate. It does not require a user-written VIEW or changes to the specification.

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
a generated erasure certificate for literal/copy/frame transfers. Source lowering and runtime remain trusted.

CCF's external `consistency/Consistency.tla` has this pattern: `action` is initialized to `"Init"`
and assigned labels by the actions, but guards and `TypeOK` do not read it. A bounded local wrapper
around the unchanged source demonstrates an actual reduction; it is not the upstream unbounded
configuration. Bounds and measurements belong with reproducible benchmark evidence.

## Finite history projection

`phase/history.rs` recognizes append-only histories whose observations admit finite summaries.
The element domain must be proved finite from Init and Next. Each action alternative must bind
the history exactly once using Append, self-copy, a tuple reset, or an IF of these transfers.
Appended values and conditions are scanned for history dependencies; their errors remain
observable. Concrete histories and actions are unchanged.

Supported observations include emptiness, independently proved structural type membership, and
predicates of this form:

```tla
\A i \in 1..Len(history):
    history[i].kind = "WRITE" \/
    \E j \in 1..i:
        history[j].kind = "WRITE" /\ history[j].value = history[i].value
```

The outer quantifier may also be existential. For example, `\E i \in 1..Len(history):
history[i] = "READ" /\ \A j \in 1..i: history[j] # "WRITE"` asks whether a read ever
occurred before any write. Once found, that witness survives later writes.

The key retains the set of history elements and one Boolean per recognized outer predicate.
Universal predicates retain their truth value; existential predicates retain its complement,
using `~(\E i: Q(i)) = (\A i: ~Q(i))` to reuse the same conjunction fold and certificate.
The inner predicate can use total scalar equality/inequality, Boolean
connectives and prefix quantification. Indices may only select history elements: their numeric
values, counts and order are not observable. Prefix predicates cannot depend on other state
variables or free locals, and the structural domain must justify every field access and scalar
comparison. Unknown operations, future-looking bounds, missing fields, heterogeneous comparisons,
raw length observations, Tail and duplicate bindings refuse the candidate.

For a history `h`, let `S(h)` be its element set and let `P(h)` be one recognized predicate.
Appending `x` leaves all previous prefix obligations unchanged. Its new obligation depends only
on `x` and `S(h) \cup {x}`; quantification over that set is equivalent to prefix quantification
because indices and multiplicities are unobserved. Thus `S(h)` and `P(h)` determine `S(Append(h,x))`
and `P(Append(h,x))`. Copy preserves this summary; a reset derives it from the retained inputs.
Accepted guards, observations and successor summaries therefore agree for equal keys. Keeping
`P(h)` is essential: `<<"WRITE", "READ">>` and `<<"READ", "WRITE">>` have equal element sets,
but may disagree on whether every read has an earlier write.
For an existential predicate `E`, the dual recurrence is
`E(Append(h,x)) = E(h) \/ Q(x, S(h) \cup {x})`. Re-evaluating old events against the
final element set would be unsound for predicates containing negation.

For an alphabet of size `A` and `k` Boolean monitors, this history component has at most
`2^(A+k)` summary values, regardless of concrete history length. The complete quotient is finite
when every other retained component is finite too. This does not impose an operation limit,
saturate arithmetic, assume a checked invariant, or establish a liveness result. Concrete
representatives and replay preserve genuine safety counterexamples and deadlocks under the
shared checking boundary. Element sets and scalar equality commute with valid symmetry
permutations; the existing equivariance check also requires referenced constants to be fixed.

The external database/blob specifications motivate this rule: their `ConsistentReads` predicate
checks earlier matching writes in `operations`. Their operation-count constraints observe exact
length, so those bounded configurations deliberately decline this history reduction. A separate
configuration without that constraint can exercise the unbounded history while retaining the
original safety invariants. This distinction must accompany measurements.

### External unbounded-model opportunities

Source inspection identifies the following opportunities and limits. Relative ages are
implemented below; the remaining rows are candidates, not completed model-checking results:

| Candidate | External motivation | Required proof and remaining blockers |
|---|---|---|
| Capped relative ages | Pragmatic Formal Modeling's `storage-cleaner-improved/storagecleanerimproved.tla` stores creation times, increments a global clock, and tests `created + 2 <= time`. | Capped ages and finite age-filtered retained sets have connected certificates. A connected combined certificate also summarizes the operation history when its event values and transfer conditions are age-independent. |
| Finite tables of history witnesses | The business-logic models ask whether a particular user has a prior subscription or trial event. | Summarize existential queries for every value in a proved finite parameter domain. Current prefix monitors reject free state and local parameters. These models additionally observe exact event counts, month numbers and billing indices, so this rule alone would not bound them. |
| Relative ticket order | The Bakery/Boulangerie models use unbounded tickets in mutual-exclusion comparisons. | Order ranks suffice for resets, copies and a globally fresh maximum ticket, but arbitrary choices from `Nat`, local `max + 1`, and successor-equality observations need more information. A rank-only key is not justified for these full models. |

The replicated-log model illustrates another limit: forgetting log contents still retains
unbounded execution lag. Merging all positive lags would lose how many catch-up steps are
needed to enable the next write. A sound reduction here needs a stronger simulation argument
and possibly refinement, rather than independently capping the counters.

### Relative-age projection

**Enabled when a connected relative-age certificate can be generated.**

`phase/age.rs` analyzes one logical clock initialized to zero, advanced by one, or left
unchanged. It recognizes fixed-domain maps of records with one timestamp field per map.
A timestamp starts at zero or is reset to the current clock on a non-ticking transition.
These transfer checks establish `0 <= timestamp <= clock`; type invariants are not assumptions.

Comparisons between `timestamp + delay` and the clock determine each map's cutoff. Delays
must resolve to nonnegative constants no larger than 1,000,000. For
`timestamp + 2 <= clock`, ages 0, 1 and 2+ suffice. Strict and exact tests can require an
additional class. The key retains the capped age, other record fields and record domains;
an unstamped sentinel remains unchanged. Distinct record shapes are tracked separately in
forward analysis. Whole-record comparisons are accepted only against literals lacking the
timestamp field, so a stamped value has a different domain from that literal.

Clock decrements, future timestamps, observed absolute times, timestamp-to-timestamp comparisons,
unknown transfers and ambiguous bindings refuse the candidate. Resets to a fixed timestamp
after initialization are currently unsupported. Certificate generation additionally requires
age-independent map indices, payload updates and conditional map-transfer tests. Retained
Boolean guards and invariant observations can combine deadline tests with independent predicates.
Finite filters over configured constant sets can feed retained-state assignments, record
updates, set operations, and invariant observations. Single-variable universal and existential
quantifiers over such domains are also supported, including nested constant-domain binders.
The emitter instantiates each filter predicate with its bound source atom and proves that
`Test.select` supplies exactly the selected positions. The consumer receives exact sets;
it cannot inspect forgotten timestamps. Multiple filters use distinct placeholders.

Dynamic filter domains, dependent binders that have not been expanded, and age-dependent
updates to timestamp-map payloads still refuse the certificate. The current emitter expands
at most 256 fixed map slots and 256 filter positions per consumer, with a shared generation
budget. Unknown uses and budget exhaustion leave checking unreduced.

`phase/age/lean.rs` emits the map slots and caps, zero-time initialization, tick amounts,
per-slot keep/reset/erase changes, deadline predicates, retained payload equations and
observations. `AgeCertificate.lean` models a timestamp as an optional natural no greater
than the clock. Projection retains its presence and caps `clock - timestamp`. It proves
initialization, successor correspondence from every representative, observations, safety
with stuttering, counterexample lifting and deadlocks. Independent HIR leaves range over
retained payloads, timestamp presence and local choices; they cannot inspect forgotten
absolute time or age magnitudes. Source lowering, domain inference, partial-read totality
and the actual runtime VIEW remain trusted.

This rule runs after whole-variable elimination and before standalone history projection.
It uses mathematical natural numbers and may eliminate eventual machine overflow of
`clock + 1` or `timestamp + delay`, as permitted by the optimization contract. Runtime
arithmetic remains checked. Compatibility mode bypasses the rule. Concrete actions and
values remain available for execution and counterexample replay.

Age/history composition has a connected certificate for one clock and one history. An age-only
model with an empty record or a timestamp tested at delay two has four reduced states:
empty, age zero, age one, and age two-or-more. Its concrete clock is unbounded. Retaining
an independently unbounded history can still make the full graph infinite when composition
is inapplicable.
The [relative-age example](../proofs/age/README.md) includes reproducible unbounded and
finite-budget configurations and explicit Lean verification commands.

`AgeHistoryCertificate.lean` connects both transfers through the same retained core and
branch witness. The compiler emits their actual seeds, tick/reset/delete changes, history
append/reset transfers, deadline tests and prefix observations into one `GeneratedAgeHistory`
model. The combined theorem constructs initialization and successor correspondence from
every representative, preserves observations, lifts counterexamples and preserves deadlocks.
It reuses the proved age and history transfer lemmas, rather than assuming preservation of
either generated transformation.

History event values and transfer conditions must be independent of forgotten time and ages.
History-dependent guards or retained updates still refuse composition. Next-state reads of
age-map fields, domains or age-filtered sets also refuse the age certificate: semantic leaves currently receive
old timestamp presence only. One history is summarized; other components remain concrete.
Inapplicable composition falls back to a certified standalone reduction when available.
Source/HIR lowering, leaf interpretation, totality/domain analysis and runtime VIEW evaluation
remain trusted, as for standalone reductions.

The original cleaner, with singleton constants and only `TypeOk` selected, now completes
without a transition budget: 820 distinct states and 3,083 generated states. This checks
`TypeOk`, not all safety properties. Selecting `ConsistentReads` still produces its genuine
counterexample. The configuration and reproduction command are in the
[relative-age example](../proofs/age/README.md). A bounded diagnostic is still required for
completed A/B timings against the unreduced model.

## Ordered allocation and live versions

`ordered-allocation-projection` now requires a compiler-generated, connected rule-model
certificate before it can be applied. The current certified subset is intentionally narrow:

- One scalar frontier initialized to a positive literal, retained or advanced by a
  nonnegative literal on each branch.
- Its initial value is the sole fixed anchor; other state contains no copies of the frontier.
- Supported frontier observations are comparisons with literals at or below the initial
  value, natural/integer membership, Boolean combinations and conditionals, and equality
  tests of `Cardinality({frontier, initialValue})` against a literal.
- Other guards, updates, observations and branch domains are independent of the frontier.
  They are universally interpreted over exactly retained state and branch-local choices.
- Constraints, action/initial properties, trace aliases and liveness exclude application.

The compiler lowers the actual normalized branches into `OrderedRule.Model`: the initial
relation, each branch's increment and guard, and the selected state observations. Its
concrete state has an unbounded natural frontier at or above its initial value; initialization
and nonnegative updates establish this domain without assuming an invariant. The reduced
state retains whether the frontier still equals its initial value, plus all independent state.
The two live numeric values are the frontier and anchor. Their ranks encode exactly this
phase; `runtime_key_equivalent` proves equality of rank keys iff the formal projections agree.
The predicate semantics include the duplicate-sensitive cardinality of the two-element set.

`OrderedCertificate.lean` constructs the certificate and proves initialization correspondence,
successor correspondence from every representative, observation preservation, safety with
stuttering, concrete counterexample lifting and plain-Next deadlock preservation. No
preservation premise or correctness axiom is assumed. Source lowering, totality, runtime
execution and symmetry composition remain trusted. Generation still does not run Lean.

The wider provenance analysis can follow families through records, maps, sets and sequences,
and recognize immutable version histories. These candidates are **not applied** without a
connected certificate. This currently excludes the MongoDB collection-incarnation model,
multiple allocation families, copies of identifiers, and history garbage collection. The
[MongoDB oracle fixture](../crates/tlx-cli/tests/fixtures/optimization_ordered/README.md)
retains an independent TLC VIEW with 19,048 distinct states as a future coverage target;
that count is not a current automatic optimization claim.

Proof review exposed a concrete failure in the earlier analysis: an intermediate consumer
such as `Cardinality({clock, 1})` discarded numeric provenance and lost the anchor `1`.
Then `clock = 1` and `clock = 2` could receive the same key although their future transitions
differed. The regression initializes `clock = 1, bad = FALSE`, increments the clock and sets
`bad` when the old set has cardinality two. TLC finds `bad = TRUE` at `clock = 3`; the former
optimization incorrectly reported success. Anchors are now retained at every intermediate
colored value, not just stored values and direct comparisons. The regression generates a
connected certificate and checks the genuine failure across execution tiers.
The [ordered proof case study](../proofs/ordered/README.md) includes a standalone Lean
disproof showing that no reduced relation can satisfy successor correspondence for the
former key, and commands for auditing newly generated certificates.

Mathematical integer semantics permit eliminating eventual allocation overflow; ordinary
runtime arithmetic remains checked. A user VIEW takes precedence and `-tlc` bypasses the pass.

## Length-only sequence projection

**Candidate only: no connected certificate; this reduction is not enabled.**

`phase/sequence.rs` shares the bounded normalizer, branch analysis and forward structural
value domains with field projection. It replaces a top-level sequence by its exact length in
the state key when its contents cannot affect any selected observation or successor class.
Concrete sequences and executable actions remain unchanged. Existing whole-variable and field
projections originally retained priority; this candidate is now gated off pending proof.

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

**Candidate only: no connected certificate; this reduction is not enabled.**

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
stored states would remain unchanged. The candidate selects the record with the most
projected fields (ties retain source traversal order). This heuristic does not predict
reachable state counts. Applying it awaits a connected certificate. Currently checking
selects at most one certified erasure, history or scalar allocation projection, in that
order, and declines user VIEW and symmetry composition.

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

**Candidate only: no connected certificate; this reduction is not enabled.**

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

**Internal candidate only: the export command currently refuses without emitting artifacts.**

The candidate pipeline supports one or more scalar natural-number state variables:

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
| `phase.rs`, `phase/` | Infer structural domains and prove field, length and finite-history projections for checking |
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

The internal proposal consists of `Optimized.tla`, `Optimized.cfg`, and `optimization.txt`.
The CLI currently refuses it because no connected certificate is available. A future
certified export must also persist `Optimization.lean`. Generated variables,
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

### Lean output for checking

Opt-in checking emits standalone Lean 4 source before exploring states. The output location
and failure behavior are specified in [configuration.md](configuration.md#command-line-options-tlx-check-spectla-options).
No verifier is run during emission. Verification is an explicit, separate user action:
`lean /path/to/Optimization.lean`. No Lake project or external Lean package is required.

The compiler embeds shared `Rules.lean`, `ErasureCertificate.lean` for unobserved variables, and, for supported history applications,
`HistoryCertificate.lean`; accepted ordered-allocation applications embed
`OrderedCertificate.lean`; relative-age applications embed `AgeCertificate.lean`. The generated section also records the actual source files,
parsed configuration, definition HIR and selected VIEW as escaped Lean strings.

**Supported history applications now generate a parametric rule-IR certificate.**
The generator consumes the same normalized branches and prefix predicates as the rule.
It emits the model's initial history seeds, append/copy/reset transfers, conditional
transfers, prefix predicates and observations. The concrete system uses indexed prefix
observations; the reduced system uses seen sets and accumulated predicate results.
Shared proofs establish their equivalence and construct all certificate fields:
initialization, successor correspondence from every representative, and observations.
Generated theorems cover safety (also with stuttering), counterexample lifting and
plain-Next deadlock preservation. No certificate premise, placeholder proof or custom
correctness axiom is introduced.

Unchanged, history-free expressions are recorded as HIR leaves and interpreted by
universal semantic parameters over retained state and branch-local bindings. For
example, the blob model's database lookup remains such a leaf, while its READ/WRITE
prefix predicate is emitted as a Lean expression. These parameters cannot read the
forgotten history. The theorem holds for every interpretation of those parameters;
this avoids duplicating the entire TLA+ evaluator just to prove a history quotient.

**The trust boundary is still the lowering.** Lean checks preservation of the generated
rule model, not that Rust translated TLA+/HIR faithfully. Domain inference and totality
of reads, set/index predicate lowering, source bindings, the actual VIEW implementation,
symmetry composition, backend execution and model-checking results remain outside the
certificate. The proof does not establish the input model's safety or its state count.

History predicates can feed back into branch guards, retained-state updates, appended
values and conditional append/reset transfers. The emitter replaces each supported
predicate with a Boolean hole and records its exact HIR mapping. Semantic consumers
receive these explicit predicate results, never the raw history. The concrete system
computes them from indexed prefixes; the reduced system reads the summary. Their
proved equality preserves both decisions and resulting transfers.

Branch bounds and initialization must remain history-independent; initial histories
use finite resets. Supported predicates include prefix monitors, emptiness, sequence
type membership and their Boolean combinations. Standalone history lowering still
refuses dependent binders, next-state history reads, exact lengths and unsupported
index patterns. Combined
age/history certificates also require history-independent timestamp-map transfers and
age-independent history events. A single retained expression may mix age-filtered
sets with history predicates.
Its emitted consumer receives exact selected source positions and explicit Boolean
results, with both mappings recorded in HIR metadata. Fixed-domain filters can also
contain history predicates. Dynamic domains, next-state inputs and non-enumerated
binders remain unsupported. Constraints, action/initial properties and trace aliases exclude automatic reduction. Unsupported history cases and
all other uncertified rules are refused. A no-pass run emits shared algebra and a record
explicitly saying no reduction was applied. The export command likewise refuses its
uncertified proposal. Generation does not imply Lean acceptance.

**Unobserved-variable removal also emits a connected certificate.** `ErasureCertificate.lean`
models concrete state as retained and hidden components. Generated hidden updates are literal
assignments, copies (including cycles) or frames, so they are total. Retained guards and
observations cannot access hidden variables. The reduced relation drops only the total hidden
update, and the certificate reconstructs a successor for every concrete representative.
Missing or conflicting bindings and unknown transfers refuse certificate generation.

To audit a generated certificate explicitly, including its standard-axiom dependencies:

```sh
python3 proofs/check_generated.py --lean /path/to/lean --negative /path/to/Optimization.lean
```

The optional negative checks require Lean to reject both forgetting prior failed prefix
obligations and changing the reduced safety observation. For erasure it rejects removing reduced successors. For ordered allocation it also
rejects forgetting the initial anchor and failing to advance the reduced phase. Relative-age
checks reject incorrect ticks, resets, deletion, deadline strictness, reduced observations,
inverted filter decisions and incorrect selected-key membership. Filter certificates also
audit the concrete and reduced selection and Boolean-binding lemmas, and reject
passing the wrong Boolean to a dependent consumer. Combined age/history checks additionally
reject forgetting prior prefix failures, dropping the shared branch’s history transfer and
discarding observed history. History and combined certificates also reject discarding
summary feedback in guards and transfers.
This script is never invoked
by checking or by the ordinary Rust tests. It needs only Lean 4 (tested with 4.34.1),
not Mathlib or a network connection.

The [blob proof case study](../proofs/blob/README.md) constructs and checks a
model-specific certificate for the unbounded database/blob history configuration.
It formalizes all eight actions and the indexed consistency observation, proves
successor correspondence and deadlock preservation, and checks that partial
lookups are defined on reachable states. Its negative test rejects a summary
that forgets old consistency failures. This is a manually reviewed TLA+-to-Lean
formalization that separately checks concrete protocol actions and reachable lookup
definedness. The automatic certificate uses the general parametric rule model instead.

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
