# Rule-based optimization

The goal of `tlx-sema::optimize` is to reduce the explored state graph while preserving checked
verdicts and genuine counterexamples. Faster expression evaluation is not a state reduction; new
reduction rules require evidence on real specifications, including distinct-state counts and
measured runtime. Commands and options are documented in
[configuration.md](configuration.md#optimization-command); candidate screening and the default-mode
search contract live in [reductions.md](reductions.md).

There are two consumers:

- **Checking reductions (`tlx check -optimize` and default-mode automatic symmetry).** Opt-in
  state projections prove a quotient over resolved HIR and install an internal `VIEW` that
  fingerprints only retained state summaries (`crates/tlx-eval/src/model/optimization.rs`);
  default-mode symmetry canonicalizes orbits over proven model-value groups
  (`crates/tlx-cli/src/autosym.rs`). Executable actions and stored representatives remain full
  concrete states, and counterexamples are reconstructed along actual `Init` and `Next` transitions.
- **Finite counter export (`tlx optimize`).** Lowers a restricted scalar counter fragment into a
  typed transition IR, runs cached inductive cleanup and threshold-counter saturation passes,
  validates every step independently, and emits a standalone `Optimized.tla` / `Optimized.cfg` pair
  with a composed Lean certificate. Export does not model-check or transfer verdicts or traces back
  to the source specification; saturation remains export-only because counter-specific trace lifting
  is not integrated into ordinary checking.

Opt-in checking permits proved reductions over mathematical integers to eliminate eventual 32-bit
machine overflow on proved clock or allocation frontiers, as specified in
[compat.md section 0](compat.md#0-the-three-tiers). Concrete expressions still use checked 32-bit
arithmetic; encountered runtime errors are never suppressed and arbitrary-precision evaluation is
not enabled. TLC compatibility mode (`-tlc`) bypasses all automatic projections and automatic
symmetry. Unknown or unsupported constructs fail closed, leaving ordinary checking unreduced.

## Proof coverage

Every automatic state reduction — opt-in projection, default-mode symmetry, or finite counter
export — must carry a compiler-generated Lean 4 certificate connected to the actual lowered
instance. `InterpModel::project_state`, `tlx_cli::autosym`, and `tlx_cli::optimization` enforce
this gate before installing a reduction or writing exported files. Shared algebra alone, Rust
applicability checks, serialized plans, and bounded state-space tests do not authorize reduction,
and no unproved or runtime-guarded reduction algorithm is kept in the tree. Ordinary checking writes
mandatory Lean before exploration without invoking a Lean verifier; development verification and
negative mutation checks are explicit.

| Reduction | Connected certificate | Current behavior |
|---|---|---|
| Unobserved variables | `ErasureCertificate.lean`: literal initializations, literal/copy/frame updates (including copy cycles); independent retained state | Enabled (`-optimize`) |
| Finite history summary | `HistoryCertificate.lean`: seen-set + prefix-monitor summaries; Boolean hole feedback into guards, retained updates, event values and conditional transfers | Enabled (`-optimize`) |
| Relative ages | `AgeCertificate.lean`: single logical clock, fixed-domain timestamp maps, keep/reset/erase transfers, capped deadlines, `Decision` trees, and `Test.select` finite/dynamic-bound filters and quantifiers | Enabled (`-optimize`) |
| Combined age/history | `AgeHistoryCertificate.lean`: one relative-age clock and one finite history over a shared retained core, with `Decision` and `Test.select`/`Test.bind` continuations | Enabled (`-optimize`); falls back to standalone age or history when composition declines |
| Ordered allocation | `OrderedCertificate.lean`: one scalar frontier, retained initial anchor, literal nonnegative increments, and rank-key equivalence | Enabled (`-optimize`) |
| Nested ordered allocation | `NestedCertificate.lean` + `NestedRank.lean`: multiple independent frontier families across fixed records, tuples and finite-domain maps | Enabled (`-optimize`) |
| Immutable live versions | `LiveCertificate.lean`: singleton-seeded append-only version table with explicit live-root payload feedback and ranked-table key equivalence | Enabled (`-optimize`) |
| Sequence length | `LengthCertificate.lean`: multiple sequences, tuple/copy/append/conditional transfers, and current-length feedback | Enabled (`-optimize`) |
| Phase-dependent fields | `FieldCertificate.lean`: finite control phases over records or fixed-domain maps, masked reads, and kernel-checked (`decide`) liveness tables | Enabled (`-optimize`) |
| Automatic keyed symmetry | `KeyedCertificate.lean`: disjoint products of full groups (2–6 model values each, product order `<= 720`) over fixed/mixed maps, scalar/optional key slots, key sets, single-key tagged record sets, fixed records, cardinalities, and point/whole-map writes | Enabled in default mode; delegates unsupported shapes to the fallback symmetry certificates below |
| Automatic equivariant symmetry | `EquivSymCertificate.lean`: disjoint products of full groups over closed recursive finite values (key-valued/nested maps, multi-key records, bounded sequences/tuples, sets, comprehensions, `KSubset`, `IsInjective`) | Enabled in default mode when `KeyedCertificate` declines and no `CHOOSE` over keys is used |
| Automatic choice-irrelevant symmetry | `ChooseSymCertificate.lean`: disjoint products of full groups with unique-witness key `CHOOSE`, uniform/constant projected-value `CHOOSE`, and recursive `CHOOSE` integer set-sum folds (`chooseFoldAdd`) | Enabled in default mode when `CHOOSE` is used within this certified subset |
| Projection composed with symmetry | `ErasedKeyedCertificate.lean`: unobserved-variable erasure composed with certified keyed symmetry (including disjoint products of full keyed groups) over one shared source IR | Enabled when `-optimize` selects unobserved-variable erasure and keyed symmetry certifies the retained tuple |
| Counter export and cleanup pipeline | `PipelineCertificate.lean`: closed natural-number transition IR, inductive singleton/interval domains, and multi-pass composition | Enabled in `tlx optimize` |

State `CONSTRAINT` predicates, implied-init `PROPERTY` conjuncts, and pure zero-arity
`CONSTANT C <- Def` substitutions are covered across all certified checking projections and
automatic symmetry families via connected `ConstrainedCertificate` proofs. `ACTION_CONSTRAINT`
predicates and `[][A]_sub` action `PROPERTY` conjuncts are additionally covered by
`ErasureCertificate`, `KeyedCertificate`, `EquivSymCertificate`, `ChooseSymCertificate`, and
`ErasedKeyedCertificate`; state-only projections (`Field`, `Length`, `History`, `Age`, `AgeHistory`,
`Ordered`, `Nested`, `Live`) fail closed when action constraints or action properties are present.
Temporal/liveness properties, `ALIAS`, `POSTCONDITION`, `_POSSIBLE`, and configuration operator or
builtin overrides (e.g., `Nat <- NatOverride`) remain outside the certified checking subset.
Explicit user `VIEW` and `SYMMETRY` declarations retain TLC's contract and decline automatic
projection.

When `-optimize` runs, `InterpModel::project_state` tries projection families in priority order —
unobserved variables, relative ages (including combined age/history), standalone finite history,
phase-dependent fields, sequence lengths, and ordered allocation — and installs the first candidate
that produces a connected certificate; an uncertified candidate never preempts a certified later
rule.

### Certificate goal and soundness boundary

Lean does not prove that the user's TLA+ specification satisfies its invariants — exhaustive search
in `tlx` still checks the reduced state graph. Instead, each generated file combines embedded Lean 4
rule libraries (`crates/tlx-sema/src/optimize/Rules.lean` and the active `*Certificate.lean`
modules) with compiler-emitted definitions lowered from the configured `.tla` and `.cfg` HIR to
prove **exact safety-quotient equivalence** (`Certificate before after project`):

```lean
structure Certificate {S A : Type}
    (before : System S) (after : System A) (project : S → A) : Prop where
  initial : ∀ a, after.initial a ↔ ∃ s, before.initial s ∧ project s = a
  next    : ∀ s a, after.next (project s) a ↔ ∃ t, before.next s t ∧ project t = a
  observe : ∀ s, before.safe s ↔ after.safe (project s)
```

- **Representative-independent lifting (`∀ s`):** during explicit-state BFS with an internal `VIEW`
  or symmetry quotient, `tlx` retains whichever concrete state `s` arrives first and deduplicates
  later states `s'` with `project s' = project s`. Quantifying `next` over **every** concrete
  representative `s` (rather than `∃ s`) guarantees that expanding from any retained representative
  produces the exact same projected successors, neither dropping reachable paths nor inventing
  spurious transitions.
- **No circular premises or custom axioms:** when a reduction relies on reachability facts (for
  example in `PipelineCertificate.lean` or `ChooseSymCertificate.lean`), Lean proves an inductive
  invariant strictly from `Init` and `Next` — never assuming checked `INVARIANT`s — before
  discharging the shared theorem goals: `certificate`, `optimization_correct` (reachable safety
  `↔`), `specification_correct` (`[Next]_vars` stuttering safety `↔`), `counterexample_lifts`
  (every reduced violation lifts to a reachable concrete violation), and `deadlock_preserved`
  (plain-`Next` deadlock `↔`), plus formal key/orbit equivalence (`runtime_key_equivalent` or
  `orbit_key_equivalent`) where applicable.
- **Constrained safety and action properties (`ConstrainedCertificate`):** when a model declares
  `CONSTRAINT`, `ACTION_CONSTRAINT`, implied-init `PROPERTY`, or `[][A]_sub` action `PROPERTY`
  conjuncts, `Rules.lean` defines `ConstrainedSystem`, `AdmittedReachable`, `ConstrainedSafe`, and
  `ConstrainedCertificate` matching `tlx-runtime`'s exact checking boundary: `INVARIANT` and
  implied-init `PROPERTY` are checked on every `Init` state (even when `!constraint(s)`), `INVARIANT`
  and `[][A]_sub` are checked on every `Next(s, t)` successor of an admitted state `s` (even when
  `!constraint(t)` or `!action_constraint(s, t)`), deadlocks are plain-`Next` deadlocks on admitted
  states, and only admitted states are expanded further. Generated constrained certificates
  additionally discharge `constrained_certificate`, `constrained_optimization_correct`,
  `constrained_init_counterexample_lifts`, `constrained_step_counterexample_lifts`, and
  `admitted_deadlock_preserved` (plus `erasure_constrained_certificate` for composed erasure+symmetry),
  without ever assuming `CONSTRAINT` or `INVARIANT` as an inductive reachability premise.
- **Kernel and non-vacuity audit:** [proofs/check_generated.py](../proofs/check_generated.py) runs
  `lean -t0 -DwarningAsError=true`, restricts `#print axioms` to Lean 4's three standard logical
  axioms (`propext`, `Classical.choice`, `Quot.sound`), and under `--negative` requires Lean to
  reject targeted soundness mutations across every certificate family (including constrained
  `constraint`, `initSafe`, `actionSafe`, and `actionConstraint` obligations when active).

Because Lean verifies the lowered mathematical transition system rather than the Rust binary,
end-to-end soundness relies on five cross-cutting boundaries (alongside each rule's specific
`Refusals & Trusted Computing Base (TCB)` section below):

1. **Rust `.tla`-to-Lean lowering:** parsing (`tlx-front`), name/level resolution (`tlx-sema`),
   operator/`LET` branch normalization, and variable-read / single-binding checks emit the Lean
   `Model`.
2. **Total semantic leaves vs. TLC evaluation errors:** except in `ChooseSymCertificate.lean` (which
   models `EvalOutcome.error` for empty `CHOOSE`), untouched TLA+ subexpressions are parameterized
   as total Lean functions and predicates (`sem.value`, `sem.test`). Preserving TLC runtime errors
   (such as out-of-domain lookups, incomparable comparisons, or 32-bit overflow in concrete
   expressions) relies on Rust's static domain, totality, and read-scanning gates
   (`phase/domain.rs`, `phase/sym_totality/`).
3. **Mathematical `Nat`/`Int` vs. 32-bit machine overflow (`-optimize` and `tlx optimize`):** clock,
   frontier, and counter reductions (`AgeCertificate`, `OrderedCertificate`, `NestedCertificate`,
   `LiveCertificate`, `PipelineCertificate`) prove correspondence over mathematical integers; an
   unbounded counter that would eventually hit 32-bit overflow in an unreduced run may collapse to a
   finite quotient under `-optimize` (disabled in `-tlc`).
4. **Runtime projection and orbit canonicalization:** Lean proves soundness of the formal `project`
   map (including `Quotient (orbits ...)` and rank keys), while Rust executes `VIEW` evaluation,
   structural rank-key construction (`crates/tlx-eval/src/model/ordered.rs`), and minimum-key
   selection across permutations generated from adjacent transpositions (symmetry generators are
   cross-checked against the unreduced graph within `autosym`'s bounded `symcheck` budget, and
   compiled key evaluation is cross-checked against the interpreter under `TLX_PARANOID=1`).
5. **Offline Lean execution:** `tlx check` and `tlx optimize` write the mandatory `.lean` file
   before state exploration or export without invoking a `lean` process at run time; kernel checking
   is run explicitly via `proofs/check_generated.py` and `crates/tlx-cli/tests/optimization_lean.rs`.

## Overlap with execution optimization

[design.md](design.md#21-crate-map-and-dependency-edges) defines the boundary between the semantic
middle-end (`tlx-sema::optimize`) and the execution compiler (`tlx-compile`). The semantic pipeline
is not a general-purpose algebraic, CSE, or loop optimizer; the small rewrites it keeps exist only
to expose or consume transition-system proofs:

| Current mechanism | Overlap and reason for keeping it here |
|---|---|
| `lower.rs` / `phase/normalize.rs`: configured constant substitution, first-order call and `LET` expansion, constant comparison folding | Overlaps `tlx-compile/src/lower/expr.rs` and `tlx-compile/src/lower/typed.rs`. Normalizes configured roots into a closed, pure IR that proof emitters can inspect; it is not an inlining profitability policy. |
| `simplify.rs`: Boolean identities, constant negation, empty/singleton conjunction and disjunction cleanup | Consumes facts exposed by semantic rules so `FALSE` guards become syntactically explicit to subsequent passes in `tlx optimize`. |
| `simplify.rs`: domain-implied comparisons | Folds comparisons determined by natural, proved-singleton, or saturated counter domains across the whole transition system rather than local literal constants. |
| `constant.rs`: inductively constant state | Proves constancy from `Init` and every remaining `Next` action, which per-action backend folding cannot establish. |
| `dead.rs`: removal of `FALSE`-guard actions | Removes whole unreachable actions from the export transition IR, potentially exposing further inductive constants before counter saturation selects thresholds. |

For example, proving `fixed = 7` inductively turns `fixed /= 7` into `FALSE`, which collapses an
enclosing action guard and lets `dead.rs` drop that action before `counter.rs` computes saturation
caps. Waiting until per-action C or JIT compilation would miss that semantic fixed point and would
not benefit interpreter runs or exported models.

In `verify_cleanup.rs`, independent checkers validate each transformation without calling the pass's
candidate-generation logic. Keep effect/error behavior, integer overflow semantics, and enumeration
obligations separate across these IRs: semantic verification predicates inhabit a closed, pure
fragment, whereas general execution IR expressions do not. Further generic rewrites belong in
`tlx-sema` only when a concrete state reduction requires them; otherwise extend `tlx-compile`.

## Deriving reductions from compiler analysis and mathematics

Each checking reduction pairs a conservative static analysis over HIR — such as monotone backward
liveness `Live = Roots \cup Dependencies(Live)` ([LLVM dataflow](https://clang.llvm.org/docs/DataFlowAnalysisIntro.html))
or forward structural domain inference ([abstract interpretation](https://www.di.ens.fr/~cousot/COUSOTpapers/POPL77.shtml)) —
with a per-model equivalence proof. A state map `P` defines an exact safety quotient when reachable
states satisfy:

- **Observation agreement:** every checked invariant agrees whenever `P(s) = P(t)`.
- **Successor correspondence:** `{P(u) : Next(s, u)} = {P(v) : Next(t, v)}`, lifted from every
  concrete representative `s, t` in the same class, together with coverage of initial states.

Fewer reachable equivalence classes, rather than simpler expressions, deliver the reduction. (An
overapproximation has a different contract: it can admit spurious violations and would require
concrete counterexample validation and refinement.) Reachable domains must be derived inductively
from `Init` and `Next`; checked invariants are observations to preserve, never assumptions that can
justify a reduction. If no guard, transition, or invariant distinguishes numeric values at or above
`10`, `{0}, ..., {9}, {10, 11, ...}` is observationally sufficient, whereas observing `N > 10`
requires keeping `10` distinct from `{11, 12, ...}`.

The same observational criterion extends to structured values, where any candidate partition must
respect definedness, cardinality, key lookups, and evaluation errors:

| Value | Candidate partition | Obligations |
|---|---|---|
| Sequence or tuple | Partition elements or project to length | Preserve observed indices, order, and length; reads, writes, and `Len` must commute with the projection (`LengthCertificate.lean` certifies content-oblivious length projection). |
| Map or record | Mask dead fields or permute symmetric keys | Preserve observed keys, domains, and definedness; backward phase liveness must propagate across phase transitions (`FieldCertificate.lean` certifies phase-masked fields from the configured source without user `VIEW` edits; `KeyedCertificate.lean` certifies key-permuted maps and records). |
| Set | Map elements to classes | Membership, equality, removal, and `Cardinality` must respect classes; collapsing `{11, 20}` to `{Above10}` is unsound whenever cardinality or exact element removal is observed. |

General numeric interval synthesis and arbitrary element-partition refinement inside live
collections remain future design directions rather than enabled passes. Source inspection of
external unbounded specifications also highlights structural limits where standalone local
projections are insufficient:

| Pattern | External motivation | Certified coverage and remaining limits |
|---|---|---|
| Capped relative ages + history | Pragmatic Formal Modeling's `storage-cleaner-improved` stores creation times, advances `time`, tests `created + 2 <= time`, and logs `operations`. | Certified by `AgeCertificate.lean` and `AgeHistoryCertificate.lean`, including dynamic-bound age filters and quotient-observable `Decision` trees. |
| Parameterized history witness tables | Business-logic subscription and billing specifications query whether a specific user has a prior trial or subscription event. | Prefix monitors currently reject free state and local parameters; those models also observe exact event counts, month numbers, and billing indices. |
| Arbitrary ticket allocation and lag | Bakery/Boulangerie mutual exclusion (`Nat` choices, `max + 1`) and replicated-log follower catch-up lag. | Rank-only keys (`OrderedCertificate` / `NestedCertificate`) cover monotone frontier allocation, copies, and anchors, not arbitrary `Nat` choices or `max + 1` arithmetic; follower lag determines catch-up step counts and requires simulation/refinement rather than independent counter caps. |

<a id="certified-keyed-symmetry"></a>
## Certified automatic symmetry

Default-mode automatic symmetry (`crates/tlx-cli/src/autosym.rs`) certifies a **disjoint product of
one or more full permutation groups** (`GroupPerm sizes` acting on the tagged disjoint union
`Key sizes := \Sigma g, Fin (sizes g)`), where each factor permutes 2 to 6 model values of one
compatibility class and the product order is at most 720 (`MAX_ORDER`). After `autosym` screens
candidate sets, `phase::symmetry_certificate` attempts three connected certificate generators in
order (`KeyedCertificate.lean`, then fallback `EquivSymCertificate.lean`, or
`ChooseSymCertificate.lean` when `CHOOSE` is used). See
[proofs/symmetry/README.md](../proofs/symmetry/README.md) for reproduction commands.

### Scope

- **`KeyedCertificate.lean` (`phase/keyed/`):** handles state variables in any combination of:
  - Fixed-domain maps `[K -> V]` and mixed fixed-domain maps `[K \cup Fixed -> V]` with key-free,
    mutually comparable payloads `V` (fixed entries remain in core state `C`).
  - Scalar or optional key variables (`K` or `K \cup Fixed`), represented as sum slots (`KeyVal`).
  - Sets of keys (`SUBSET K` or `SUBSET (K \cup Fixed)`), represented by indicator maps over moved
    keys plus a key-free fixed-element subset in `C`.
  - Sets of tagged records where each record shape has at most one pure-key field and mutually
    comparable key-free payload fields (key-free shapes stay in `C`; each keyed shape maps keys to
    sets of key-free payload records).
  - Fixed-shape records whose fields are independently core values, fixed maps, or scalar/optional
    key slots.
  Exposes key/slot/fixed equality, group-mask membership, Boolean connectives, quantifiers over
  group unions or key-set variables, finite key cardinalities (`bindCount`), ordered map and
  slot-indexed reads, conditional payload/slot decision trees, point and whole-map writes
  (`Write.point` / `Write.all`, including multi-writer `EXCEPT` and tagged-record insertions), and
  slot writes (`SlotExpr`), without `CHOOSE` over keys.
- **`EquivSymCertificate.lean` (`phase/equiv_sym/`):** fallback when `KeyedCertificate` declines
  (for example on key-valued maps `[K1 -> K2]`, nested maps, multi-key message records, bounded
  sequences or tuples of keys, general finite sets, set comprehensions, `KSubset`, or
  `IsInjective`) and no `CHOOSE` over keys is present.
- **`ChooseSymCertificate.lean` (`phase/choose_sym/`):** certifies `CHOOSE`-bearing models whose
  selections are (1) unique-witness key choices (`x = target`, `ChooseOne`, or inductively proved
  at-most-one active key in a key set or Boolean flag map), (2) projected uniform/constant-value
  choices (key-free-value record comprehensions, predicate-pinned `.val`, or inductively proved
  uniform-value message sets), or (3) commutative-associative recursive `CHOOSE` integer set-sum
  folds (`chooseFoldAdd`), while preserving empty-witness `CHOOSE` errors (`EvalOutcome.error`).

### Lowered Rule & Lean Certificate

- **`KeyedCertificate.lean`** lowers `Next` into up to 512 explicit branch cases over `State C MapId
  SlotId (Key groupSizes) V A`, proves equivariance of guards, reads, cardinalities
  (`countFin_rename`), slot transfers, and map writes under `GroupPerm`, and constructs the
  permutation-quotient certificate using actual `Init` witnesses (requiring no symmetric-`Init`
  assumption). Six theorem audits verify the certificate, safety with and without stuttering,
  counterexample lifting, deadlock preservation, and formal orbit-key equality.
- **`EquivSymCertificate.lean`** lowers normalized `Init`, `Next`, and `INVARIANT` formulas into a
  closed recursive finite value and formula IR (`Val`, `Expr`, `SetPred`, `Form`), proves
  equivariance under `GroupPerm`, and discharges the same six quotient theorems.
- **`ChooseSymCertificate.lean`** pairs an inductive reachability invariant (`InvPlan` for
  at-most-one active flags and uniform message payloads) with outcome-preserving `CHOOSE`
  equivariance lemmas over the reachable sub-transition system before lifting to the unrestricted
  safety, counterexample, deadlock, and orbit-key theorems.

### Refusals & Trusted Computing Base (TCB)

- **Refusals:** overlapping or unused groups in a requested product, partial/pinned subgroups,
  product order above 720, unproved `CHOOSE` dependencies, multi-actor partial record patches that
  may alias in `KeyedCertificate`, primed non-core reads where unsupported, incomparable slot
  payloads, temporal properties, declared `VIEW`/`SYMMETRY`, constraints, action/init properties,
  aliases, and state-dependent effects. Even forced candidates (`TLX_AUTOSYM_FORCE`) require a
  connected certificate. When a product subset fails certification within `autosym`'s search budget,
  `autosym` falls back to the largest-order certifiable disjoint product or singleton subgroup.
- **TCB:** parsing and HIR normalization (`SymNormalizer`), forward structural domain inference and
  shape bijection (`phase/domain.rs`), the shared `phase/sym_totality/` gate (which proves totality,
  TLC comparability including typed vs. untyped model values, 32-bit checked-arithmetic bounds, and
  finite enumerability strictly from `Init` and `Next` without assuming invariants), semantic leaf
  interpretation in `KeyedCertificate`, runtime permutation closure from adjacent transpositions,
  and runtime minimum-key orbit canonicalization (the Lean orbit theorem characterizes the formal
  quotient, not the Rust minimum-selection procedure).

## Unobserved state projection

Unobserved-variable erasure (`projection.rs`, `phase/erasure.rs`) computes a backward cone of
influence over state variables and omits variables that cannot affect any guard, retained state
update, or checked invariant (such as action-label variables in CCF's `Consistency.tla`). This rule
is purely structural and never inspects variable, action, or module names:

```tla
Init == x = 0 /\ tag = "init"
Next == (x' = 1 - x /\ tag' = "flip")
     \/ (UNCHANGED x /\ tag' = "idle")
Inv == x \in {0, 1}
```

Five reachable concrete states collapse to two projected classes over `<<x>>`, while stored
representatives retain their real `tag` values for trace replay.

### Scope

1. **Literal initialization and total transfers:** omitted variables must initialize to integer
   (fitting TLC's 32-bit range), Boolean, or string literals, and every next-state binding on each
   syntactic alternative must be a scalar literal, a whole-variable copy `v' = u` of a defined
   current-state variable (dead copy cycles stay dead; observing one member retains the cycle), or
   `UNCHANGED`.
2. **Single-binding discipline:** conjunction sums binding counts per variable while disjunction,
   `IF`, and `CASE` take the maximum, requiring at most one binding on every syntactic alternative.
   This rules out implicit equality guards such as `UNCHANGED tag /\ tag' = "idle"` that test old
   values without reading them syntactically.
3. **Closed live cone:** guards, quantifier bounds, invariants, and retained updates seed and close
   the live set across resolved calls, `LET` helpers, and conservatively scanned higher-order
   operator actuals (including by-name and captured reads). Primed occurrences outside recognized
   assignments count as reads.

### Lowered Rule & Lean Certificate

`phase/erasure.rs` splits concrete state into retained core `C` and hidden tuple `Hidden H`, emitting
every hidden variable's literal, retained-copy, or hidden-copy/frame transfer per normalized branch.
Retained guards, updates, and observations are parameterized solely over `C` and branch-local
witnesses. `ErasureCertificate.lean` proves hidden updates are total and unconstrained, constructs
initialization and successor correspondence from every hidden representative, and discharges safety,
stuttering safety, counterexample lifting, and deadlock preservation.

### Refusals & Trusted Computing Base (TCB)

- **Refusals:** non-literal hidden initializations, unknown or multi-binding hidden updates,
  observable builtin effects, unresolved operator constants, recursive action expansion, read-scan
  traversal above 100,000 nodes or depth 128, and observations outside invariants/deadlock.
- **TCB:** HIR dependency and single-binding analysis, branch normalization, universal leaf
  interpretation of retained HIR, and runtime `VIEW` fingerprinting.

## Finite history projection

`phase/history.rs` summarizes append-only event sequences whose concrete length is unbounded (as in
the `operations` log of the external `pragmatic/database-blob` specifications when bounded
step-count constraints are removed; see [proofs/history/README.md](../proofs/history/README.md) and
[proofs/blob/README.md](../proofs/blob/README.md)).

### Scope

- One append-only sequence variable whose element domain is proved finite from `Init` and `Next`,
  initialized to a finite tuple and bound once per branch via `Append`, self-copy, finite tuple
  reset, or `IF` combinations thereof (scanning appended values and conditions so evaluation errors
  remain observable).
- Observations and feedback predicates built from emptiness, proved structural membership
  (`history \in Seq(Op)`), and universal or existential prefix monitors over `1..Len(history)` and
  `1..i` using total scalar equality/inequality and Boolean connectives:

```tla
\A i \in 1..Len(history):
    history[i].kind = "WRITE" \/
    \E j \in 1..i:
        history[j].kind = "WRITE" /\ history[j].value = history[i].value
```

  Existential monitors (such as `\E i \in 1..Len(history): history[i] = "READ" /\ \A j \in 1..i:
  history[j] # "WRITE"`) are also supported.
- **Summary feedback (`phase/history/lean/feedback.rs`):** supported history predicates may feed
  into branch guards, retained-state updates, appended event values, and conditional append/reset
  tests, provided branch quantifier bounds and `Init` remain history-independent.

### Lowered Rule & Lean Certificate

For history `h`, let `S(h)` be its seen element set and `P(h)` a universal prefix monitor. Appending
`x` leaves earlier prefix obligations intact and adds an obligation depending only on `x` and
`S(h) \cup {x}` (because numeric indices and multiplicities are unobserved), so `S(h)` and `P(h)`
determine `S(Append(h, x))` and `P(Append(h, x))`. Retaining `P(h)` alongside `S(h)` is essential:
`<<"WRITE", "READ">>` and `<<"READ", "WRITE">>` have equal element sets, and re-evaluating old
events against the final seen set would be unsound under negation. Existential monitors follow the
dual recurrence `E(Append(h, x)) = E(h) \/ Q(x, S(h) \cup {x})` and store `~(\E i : Q(i)) = (\A i :
~Q(i))` so both quantifiers share one conjunction fold. Over an alphabet of size `A` and `k`
monitors, the summary has at most `2^(A + k)` values regardless of concrete history length.

`phase/history/lean.rs` emits initial seeds, append/copy/reset transfers, prefix predicates, and
explicit Boolean feedback holes (recorded with exact HIR mappings so consumers receive summary bits
rather than raw `history`) into `HistoryCertificate.lean`, which proves concrete indexed-prefix
evaluation equals the reduced summary and discharges initialization, successor correspondence from
every representative, invariant preservation, counterexample lifting, and deadlock preservation.

### Refusals & Trusted Computing Base (TCB)

- **Refusals:** raw `Len(history)` observations, `Head` / `Tail` / arbitrary numeric indexing,
  future-looking bounds (`j \in i..Len(h)`), free state or local parameters inside prefix monitors,
  dependent branch binders, next-state history reads, heterogeneous comparisons, duplicate bindings,
  and symmetry composition.
- **TCB:** HIR normalization, forward finite-alphabet and structural field/comparison totality
  inference, Boolean hole substitution in consumer HIR leaves, and runtime `VIEW` evaluation.

## Relative-age projection

`phase/age.rs` caps unbounded logical-clock ages in fixed-domain record maps and optionally composes
that reduction with a finite history summary. On Pragmatic Formal Modeling's
`storage-cleaner-improved/storagecleanerimproved.tla`, singleton `TypeOk` completes without a
transition budget in 820 distinct / 3,083 generated states, while selecting `ConsistentReads`
produces its genuine concrete counterexample (completed A/B runtime comparisons against the
unreduced model still require a bounded configuration; see
[proofs/age/README.md](../proofs/age/README.md)).

### Scope

- **Clock and timestamp maps (`phase/age/lean.rs`):** one logical clock initialized to `0` and
  updated by `+ 1` or `UNCHANGED`, paired with fixed-domain maps (at most 256 slots) of records
  carrying one timestamp field initialized to `0`, reset to the current clock on non-ticking steps,
  kept, or erased to a timestamp-free sentinel literal (establishing `0 <= timestamp <= clock` from
  transfers alone). Whole-record equality is allowed only against literals lacking the timestamp
  field so stamped and unstamped domains stay disjoint. Comparisons `timestamp + delay` against
  `clock` (`0 <= delay <= 1,000,000`) determine each map's cutoff (e.g. `timestamp + 2 <= clock`
  keeps unstamped, `0`, `1`, and `2+`; strict or exact tests add one class when required).
- **Finite and dynamic-bound filters and quantifiers (`phase/age/lean/filters.rs`):** set filters
  `{k \in D : P(k)}` (up to 256 positions per consumer) and single or nested universal/existential
  quantifiers over constant sets or **dynamic domains enumerated from inferred finite upper bounds**
  (emitted with explicit membership tests: implication for `\A`, conjunction for `\E` and filters,
  preserving empty domains and nested binder scopes). Consumers receive exact selected sets for
  retained assignments, record updates, set unions, and invariants.
- **Single-history composition and quotient-observable decisions (`phase/age/lean/history.rs`,
  `phase/age/lean/decisions.rs`):** composes one relative-age clock with one finite history over a
  shared retained core. Quotient-observable age deadlines and history-summary predicates may drive
  history-dependent timestamp choices, age-dependent history event values and transfer conditions,
  dependent retained payload updates, and mixed age/history filter consumers.

### Lowered Rule & Lean Certificate

- **Standalone age (`AgeCertificate.lean`):** models timestamps as `Option Nat` bounded by `clock`,
  projects them to presence plus `min (clock - timestamp) cap`, and proves tick/reset/erase
  transfers and all strict/non-strict deadline comparisons commute with capping.
- **Filters and Boolean bindings:** `Test.select` passes exact selected source positions to consumer
  set placeholders, and `Test.bind` passes exact history-summary Booleans alongside selected sets
  with separate ordered argument mappings; concrete/reduced selection and binding lemmas connect
  those placeholders to the source predicates without exposing raw `clock`, uncapped age magnitudes,
  or raw history sequences to semantic leaves.
- **Decisions and combined model (`AgeHistoryCertificate.lean`):** lifts quotient-observable
  conditions and nested event/payload builders into `Decision` trees with proved concrete/reduced
  evaluation equality and continuation lemmas, then proves product initialization, successor lifting
  from every representative, invariant preservation, counterexample lifting, and deadlock
  preservation in `GeneratedAgeHistory` by reusing proved age and history transfer lemmas rather
  than assuming standalone preservation premises.
- Mathematical natural-number clock semantics may eliminate eventual 32-bit overflow of `clock + 1`
  or `timestamp + delay`; concrete runtime arithmetic remains checked.

### Refusals & Trusted Computing Base (TCB)

- **Refusals:** clock decrements or increments other than `1`, future timestamps, post-`Init` resets
  to a fixed constant timestamp, timestamp-to-timestamp or raw absolute-time observations,
  **next-state (primed) reads** of age-map fields, domains, or age-filtered sets (leaves receive old
  timestamp presence only), **unenumerable dependent binders** lacking an inferred finite upper
  bound, **multiple histories**, symmetry composition, and slot/filter/generation budget exhaustion.
  When combined age/history certification declines, `project_state` falls back to standalone
  `AgeCertificate.lean` or `HistoryCertificate.lean` when available.
- **TCB:** HIR branch normalization, forward domain and finite-upper-bound inference (tracking
  distinct record shapes and never assuming invariants), partial-read totality, placeholder/leaf
  interpretation, and runtime `VIEW` evaluation.

## Ordered allocation and live versions

`phase/ordered.rs` and `phase/ordered/` collapse unbounded monotonically allocated identifiers to
their relative order or anchor phase, with dedicated runtime projection in
`crates/tlx-eval/src/model/ordered.rs`. See [proofs/ordered/README.md](../proofs/ordered/README.md).

### Scope

Three connected emitters cover progressively richer allocation shapes:

1. **Scalar frontier (`phase/ordered/lean.rs`):** one frontier variable initialized to a positive
   literal and retained or incremented by nonnegative literals, with no copies in other state
   variables. Observations may compare the frontier against literals `<= initialValue`, test `Nat` /
   `Int` membership, or compare `Cardinality({frontier, initialValue})` against a literal.
2. **Nested families (`phase/ordered/nested/`):** multiple independent frontier families and copied
   identifiers stored at fixed paths inside records, tuples, and finite-domain maps (completing
   [proofs/ordered/Nested.tla](../proofs/ordered/Nested.tla) in 13 states). Initialization bounds
   every numeric occurrence by its family's frontier; branches may copy live identifiers, write
   retained nonpositive/anchor literals, branch on inter-identifier or anchor comparisons, or
   allocate fresh offsets within a branch's frontier increment across expanded finite actor bounds.
3. **Immutable live version table (`phase/ordered/nested/live.rs`):** adds one append-only version
   table initialized at the singleton initial frontier and extended by one entry when the frontier
   increments by `1` (completing
   [proofs/ordered/LiveVersions.tla](../proofs/ordered/LiveVersions.tla) in 89 states). Payloads are
   identifier-free and may be read in guards, retained updates, conditional identifier transfers,
   and new payload construction exclusively through current live references, allowing obsolete
   table entries to be collected in the quotient key.

### Lowered Rule & Lean Certificate

- **`OrderedCertificate.lean`** lowers branches into `OrderedRule.Model`, projects the frontier to
  whether `frontier = initialValue` (preserving duplicate-sensitive `Cardinality({frontier,
  initialValue})`), and proves `runtime_key_equivalent` between formal projections and runtime rank
  keys. Proof review of an earlier uncertified analysis exposed a concrete soundness defect: an
  intermediate expression `Cardinality({clock, 1})` dropped numeric provenance of the anchor `1`,
  collapsing `clock = 1` and `clock = 2` despite different future transitions and missing a `bad =
  TRUE` violation at `clock = 3` ([HiddenAnchor.lean](../proofs/ordered/HiddenAnchor.lean) disproves
  any reduced relation for that former key). Anchors are now retained at every colored intermediate
  value, and the regression checks the genuine failure with a connected certificate across all tiers.
- **`NestedCertificate.lean` and `NestedRank.lean`** verify completeness of the generated path and
  anchor reference vector, prove order-pattern quotient correspondence, and prove canonical positive
  ranks plus exact `<= 0` sentinels match that quotient.
- **`LiveCertificate.lean`** replaces `table[ref]` lookups with typed root-payload inputs (never
  passing the raw table to semantic leaves), proves old live reads survive append and fresh reads
  yield the appended payload, and connects the retained ranked-table graph to the quotient key.
  Mathematical integer allocation may eliminate eventual 32-bit frontier overflow.

### Refusals & Trusted Computing Base (TCB)

- **Refusals:** dynamic container domains or shapes, identifier-valued map keys or sets (which still
  exclude the general MongoDB collection-incarnation model in
  [crates/tlx-cli/tests/fixtures/optimization_ordered/README.md](../crates/tlx-cli/tests/fixtures/optimization_ordered/README.md),
  whose handwritten 19,048-state TLC `VIEW` remains a future target rather than an automatic claim),
  cross-family comparisons, general arithmetic on identifiers, full version-table enumeration,
  arbitrary historical-version lookups, primed table reads, allocation identifiers inside history
  payloads, numeric-dependent payload construction, and symmetry composition.
- **TCB:** HIR normalization, fixed-shape and forward domain inference, independent leaf
  interpretation, and the runtime structural rank-key walker (`ordered.rs`).

## Length-only sequence projection

`phase/sequence.rs` projects one or more top-level sequence variables to their exact `Len(seq)` in
the state key when sequence elements cannot influence guards, successor lengths, or invariants
(motivated by `Examples/specifications/FiniteMonotonic/ReplicatedLog.tla`, where `2^k` concrete
transaction logs of length `k` collapse to one length class per `executed` map, though unbounded
lengths and execution counters still leave the full mathematical graph infinite; see
[proofs/length/README.md](../proofs/length/README.md)).

### Scope

- One or more sequence variables with a proved `Seq(D)` domain from `Init` and `Next`, bound once
  per branch via tuple literals, self-copy, `Append`, or `IF` combinations whose element and
  condition expressions do not read projected sequence contents (preserving observable element
  evaluation errors).
- Remaining reads restricted to `Len(seq)` and structural membership predicates (`seq \in Seq(T)`)
  proved identically true by forward domain inference without hiding type errors. Exact lengths are
  kept, preserving length arithmetic and 32-bit overflow behavior without saturating counters.

### Lowered Rule & Lean Certificate

`phase/sequence/lean.rs` lowers all projected sequences' initial lengths and tuple/copy/append/`IF`
length transfers into `GeneratedLength`. Semantic leaves receive retained variables and current
lengths only. `LengthCertificate.lean` proves transfer commutation and constructs initialization,
successor correspondence from every representative, invariant preservation, counterexample lifting,
and deadlock preservation.

### Refusals & Trusted Computing Base (TCB)

- **Refusals:** `Head`, `Tail`, `SubSeq`, element indexing `seq[i]`, sequence equality, primed
  length reads (`Len(seq')`), duplicate bindings, observable effects, liveness/handwritten-view
  configurations (such as upstream `MCReplicatedLog`), and symmetry composition.
- **TCB:** HIR normalization, forward structural domain/totality inference, semantic leaf
  interpretation, and runtime `VIEW` evaluation.

## Phase-dependent field projection

`phase.rs` derives a finite control-phase field and backward per-phase field liveness `Live[phase,
field]` for a record variable or a fixed-domain map of records, replacing dead fields with a single
sentinel in the state key while preserving record field sets, map keys, and control values
(motivated by `serverStates` in `pragmatic/database-blob` and client records with model-value phases
and sequence fields in BookKeeper's `LedgerChaining`; see
[proofs/field/README.md](../proofs/field/README.md)).

### Scope

- Record variables or exact fixed-domain maps (up to 256 keys) of records (up to 32 fields) with a
  control field ranging over at most 32 mutually comparable scalar literals or model values and
  initialized to constant phases.
- Forward structural domain inference over `Init` and `Next` (tracking integer lower bounds,
  sequence elements, record fields, and function overrides) to verify exact map key sets and
  discharge always-true structural membership invariants (such as `Seq(Nat)`).
- Single-binding `EXCEPT` updates on the record or on one bound actor's map entry (up to 512
  normalized alternatives and 128 phase-expanded certificate cases), expanding `@` only when prior
  writes provably cannot alias the updated point. When multiple records qualify, selection prefers
  certified candidates and then the record with the most projected fields.

### Lowered Rule & Lean Certificate

For each candidate control field, backward dataflow computes `Live[phase, field]` to a least fixed
point:

1. Seed liveness from guards, update expressions (scanned even for dead targets so evaluation errors
   are preserved), and invariants, restricting reads to a phase only after a recognized control
   guard has been evaluated (keeping by-name operator actuals in the callee's control context).
2. Summarize recognized single-record or single-actor `EXCEPT` writes whose actor domain lies inside
   the fixed map domain.
3. Across every transition from phase `p` to `q`, propagate every field live in `q` that is not
   overwritten back into `p`; the control field stays live in every phase.

`phase/liveness/lean.rs` emits the explicit phase, masked-read, write, and observation tables into
`GeneratedField`, and `FieldCertificate.lean` discharges read, frame, and observation liveness
obligations via kernel-checked `decide` (never assuming liveness preservation) to prove
initialization, successor lifting, invariant preservation, counterexample lifting, and deadlock
correspondence.

### Refusals & Trusted Computing Base (TCB)

- **Refusals:** nonconstant initial phases, primed projected reads, cross-actor or whole-record
  uses, uncertain `EXCEPT` / `LET` aliasing, duplicate writes, unknown map domains, higher-order or
  recursive action expansion, effectful actuals (even if unused), budget exhaustion, and symmetry
  composition.
- **TCB:** HIR call/`LET` expansion and alias checking, forward structural domain/totality
  inference, leaf interpretation over retained state and recorded field reads, and runtime `VIEW`
  evaluation.

## Composing projection with symmetry

Unobserved-variable erasure is the one checking projection certified to compose with automatic
keyed symmetry (`phase/keyed/erasure.rs` + `ErasedKeyedCertificate.lean`), supporting **both single
groups and disjoint products of full keyed permutation groups** (total order `<= 720`). On the
[symmetry composition example](../proofs/symmetry/README.md), 811 concrete states drop to 27 with
erasure alone and 10 with erasure composed with keyed symmetry across both execution tiers,
preserving concrete safety violations and deadlocks.

### Scope

- `-optimize` selects `unobserved-state-projection`, installing a retained-variable tuple `VIEW` in
  source variable order, and the retained variables plus `Init`, `Next`, and `INVARIANT` satisfy
  `KeyedCertificate`'s shapes and operations for a disjoint product of full model-value groups while
  every omitted variable uses scalar literal, retained-variable copy, hidden-variable copy, or frame
  updates.

### Lowered Rule & Lean Certificate

`symmetry_projection_certificate` verifies the installed `VIEW` is the exact source-ordered tuple of
retained variables and lowers hidden updates alongside the keyed branch guards, slot writes, and map
writes in one shared `ErasedKeyedRule.Model GroupCount groupSizes` (whose intermediate initial
relation is the projected image of the full source `Init`). `ErasedKeyedCertificate.lean` proves the
erasure certificate from every hidden representative and composes it (via the shared composition
lemma in `Rules.lean`) with `KeyedCertificate`'s orbit quotient on that exact intermediate model;
two independently generated certificates for unrelated models cannot authorize application. At run
time, `tlx` projects first and canonicalizes the projected tuple under the total structural order
(`InterpModel::projected_orbit`), so forgotten variables containing moved keys cannot split or bias
orbits. Seven theorem audits cover the intermediate erasure certificate, the composed certificate,
safety with and without stuttering, counterexample lifting, deadlocks, and formal orbit-key
equality.

### Refusals & Trusted Computing Base (TCB)

- **Refusals:** any projection family other than unobserved-variable erasure (age, history, field,
  sequence-length, and ordered-allocation projections keep priority and run standalone without
  automatic symmetry), fallback symmetry engines (`EquivSymCertificate` / `ChooseSymCertificate`),
  unsupported hidden transfers, and user-declared `VIEW` or `SYMMETRY`. Passing `-noautosymmetry`
  retains standalone `ErasureCertificate.lean`.
- **TCB:** same union of TCB boundaries as `ErasureCertificate` and `KeyedCertificate`, plus runtime
  tuple projection prior to orbit canonicalization.

## Checking boundary

Certified checking reductions apply to exhaustive BFS safety runs without `-simulate`, `-generate`,
`-checksymmetry`, `-coverage`, or `-checkpoint`/`-recover`. State dumps (`-dump`) write concrete
representatives with a reduced-search header; `-dumpTrace` counterexamples are genuine concrete
behaviors. Reduced statistics and remarks name the active rule and omitted variables or projected
fields. Both `InterpModel` and `EncModel` share the projection and replay contract (`EncModel`
infers result shapes for anonymous structural `VIEW` expressions from the current state layout,
rebuilds them on layout widening, and falls back to interpreted key evaluation for unknown shapes).
Measure the complete check: fewer explored states can still cost more wall time when projection or
orbit canonicalization overhead dominates.

## Finite counter export

`tlx optimize Spec.tla -output DIR` (`crates/tlx-cli/src/optimization.rs`) transforms an unbounded
natural-number counter specification into a finite standalone model (`Optimized.tla`,
`Optimized.cfg`, `Optimization.lean`, and `optimization.txt`) without invoking Lean or a model
checker or claiming source safety. See [proofs/counter/README.md](../proofs/counter/README.md).

### Scope

- One or more scalar natural-number variables initialized to configured natural literals (`Init`
  conjunction), `Next` as a disjunction of guarded actions with exactly one update per variable
  (`UNCHANGED`, reset to `0`, or `c' = c + 1`), guards and state invariants formed from Boolean
  combinations (`/\`, `\/`, `~`, `=>`) of `c op literal` (`=`, `/=`, `<`, `<=`, `>`, `>=`), true
  constant `ASSUME`s, global scalar integer constants, and `CHECK_DEADLOCK FALSE`. Normalization
  expands first-order calls, `INSTANCE` substitutions, and `LET`s within a 100,000-node / depth-128
  budget.

### Pipeline, Lowered Rules & Lean Certificate

The implementation in `crates/tlx-sema/src/optimize/` separates checking projections from the
two-stage immutable-pass export pipeline:

| Module | Responsibility |
|---|---|
| `lower.rs`, `ir.rs`, `analysis.rs` | Normalize configured HIR into closed natural/finite counter IR; lazily compute observation thresholds and constant candidates (invalidated on every committed mutation) |
| `passes.rs`, `constant.rs`, `simplify.rs`, `dead.rs`, `counter.rs` | Stage 1 fixed-point cleanup (`constant`, `simplify`, `dead`) followed by Stage 2 threshold saturation (`counter`, `simplify`, `dead`), up to 64 rounds per stage |
| `verify.rs`, `verify_cleanup.rs` | Independently check IR structure, before/after correspondence, full-domain comparison partitions, complete update vectors, and whole-model finite-domain closure |
| `certify.rs`, `certify/`, `PipelineCertificate.lean` | Emit closed natural-valued before/after state predicates for every committed pass, prove inductive singleton/interval domains and `alpha` correspondence in Lean arithmetic, and compose passes |
| `emit.rs` | Emit collision-free `Optimized.tla`, `Optimized.cfg`, and `optimization.txt` (written last after all checks succeed) |
| `projection.rs`, `phase.rs`, `phase/`, `lean.rs` | Checking projections (`erasure.rs`, `history/`, `age/`, `ordered/`, `sequence/`, `liveness/`) and symmetry certificates (`keyed/`, `equiv_sym/`, `choose_sym/`, `sym_totality/`) |

Each export pass has an independent validator and closed Lean proof obligation:

- **Constant-state propagation (`constant.rs`):** proves a singleton domain solely from `Init` and
  all remaining actions (`reset` preserves constancy only when `Init` is `0`), folds its comparisons,
  and rewrites updates to `UNCHANGED`, never relabeling a saturated representative (where `0` may
  represent an unbounded counter) as an exact singleton.
- **Predicate simplification (`simplify.rs`):** folds domain-determined comparisons and Boolean
  identities; `verify_cleanup.rs` partitions each comparison's full domain at `literal` and `literal
  + 1` (never relying on interval endpoints, which would miss interior `=` matches).
- **Dead-action elimination (`dead.rs`):** drops actions whose guard is literal `FALSE` in source
  order. If all actions disappear, `emit.rs` outputs a false state guard conjoined with an explicit
  `UNCHANGED` tuple to preserve action level (TLC rejects constant `Next == FALSE`), and expresses
  any `FALSE` invariant as `v0 /= v0` so TLC checks it on initial states instead of rejecting the
  `.cfg`.
- **Counter saturation (`counter.rs`):** selects cap `K` from remaining guards and invariants (`K >=
  T` for `< T` / `>= T`; `K > T` for `= T`, `/= T`, `<= T`, `> T`; `0` if unobserved) and applies
  `alpha(c) = min(c, K)` (`alpha(c + 1) = min(alpha(c) + 1, K)`, `alpha(0) = 0`), rewriting `c' = c
  + 1` to `IF c < K THEN c + 1 ELSE K` (retaining a self-loop at `K` and testing `< K` before adding
  so maximum caps never overflow).
- **`PipelineCertificate.lean`** lifts each committed pass's Lean-arithmetic proof to reachable
  systems and composes them into a final unrestricted source-to-target safety theorem, stuttering
  safety, counterexample existence, and reachable plain-`Next` deadlock correspondence.

To add an export pass, implement `Pass` in a dedicated module, add exhaustive independent validation
in `verify.rs`, emit and prove its actual before/after IR in `certify.rs` (never reusing an
unrelated certificate), and register it in `Pipeline::default` with positive, refusal, and
corrupted-evidence tests. For a new checking reduction, analyze resolved HIR without rewriting
executable actions, prove a connected `*Certificate.lean` module, and demonstrate state reduction on
an external specification before adding shared abstractions.

### Refusals & Trusted Computing Base (TCB)

- **Refusals:** cross-counter comparisons or copies, decrements, structured values, quantifiers,
  recursive/higher-order calls, unsupported expressions even inside syntactically dead branches,
  enabled deadlock checking, temporal properties, constraints, `VIEW`/`SYMMETRY`, `ALIAS`,
  `POSTCONDITION`, `_POSSIBLE`, existing output directories, and non-convergence. Semantic refusal
  creates no destination directory.
- **TCB:** frontend parsing/HIR resolution, restricted IR lowering (`lower.rs`), TLA+ emission
  (`emit.rs`), and whichever model checker later runs `Optimized.tla`. Mathematical natural
  saturation eliminates concrete 32-bit counter overflow, and exported traces describe the abstract
  graph (`optimization.txt` is explanatory documentation, never a reusable authorization token).

## Lean output for checking

Opt-in checking (`-optimize`) and default-mode certified automatic symmetry write standalone Lean 4
source (`crates/tlx-cli/src/proofs.rs`) before state exploration begins. Output paths (`-proofdir`
or `$TLX_CACHE/proofs` / `~/.cache/tlx/proofs`, with private per-user fallback) and write-failure
exit behavior are documented in
[configuration.md](configuration.md#command-line-options-tlx-check-spectla-options). When `-optimize`
selects no applicable projection and no symmetry applies, `tlx` still writes a valid Lean file
containing `Rules.lean` and an explicit record that no reduction was applied.

Each generated file is self-contained (requiring only core Lean 4, tested with Lean 4.34.1, with no
Lake project, Mathlib, or network access): it embeds `Rules.lean`, the active `*Certificate.lean`
module(s), escaped audit strings of the source `.tla`/`.cfg` and normalized HIR, and the generated
model instance with its theorem checks. Independent HIR subexpressions that do not touch projected
or permuted state are represented as universally quantified semantic parameters over retained state
and branch-local bindings, proving the quotient for every total interpretation of those leaves
without re-encoding the entire TLA+ evaluator in Lean.

To verify a generated certificate with Lean and run its negative mutation checks (which confirm Lean
rejects broken reductions such as forgetting failed history prefixes or summary feedback, dropping
reduced successors, losing ordered-allocation anchors or phase transitions, inverting age ticks,
resets, deletions, deadlines, or `Test.select`/`Test.bind` bindings, or corrupting observations):

```sh
python3 proofs/check_generated.py --lean /path/to/lean --negative /path/to/Optimization.lean
```

Complementing the parametric compiler-generated certificates, the
[blob proof case study](../proofs/blob/README.md) provides a manually reviewed TLA+-to-Lean
formalization of all eight concrete database-blob actions, reachable map-lookup definedness, and
consistency-history reduction (with negative checks rejecting summaries that forget prior
consistency failures).

## Validation

- **`tlx-sema` unit and corruption tests (`crates/tlx-sema/src/optimize/tests.rs`,
  `crates/tlx-sema/src/optimize/cleanup_tests.rs`):** exercise source normalization, inductive
  constants, boundary/interior domain partitions, cascaded dead-action cleanup, failing initial
  invariants, projection and symmetry certificate emitters, and deliberate evidence/guard/update/
  invariant corruptions that the Rust verifiers and negative Lean checks reject.
- **`tlx-cli` and `tlx-eval` integration tests:** execute reduced and unreduced models across
  `-interp`, closure IR, JIT, and C backends with `TLX_PARANOID=1`, checking state-count reductions,
  concrete safety and deadlock trace reconstruction, `-tlc` bypass, temporal/configuration refusals,
  refusal without partial export artifacts, `choose_verdict` promotion, multi-group symmetry product
  selection, and mandatory Lean output persistence.
