# TLC semantics reference

Exact TLC behavior for **values, comparison, enumeration, counting, fingerprints and standard
modules**, with TLC source references. tlx keeps `states generated` and `distinct states found`
identical to TLC, so every rule here is something the interpreter (`tlx-eval`, `tlx-value`) must
reproduce. The summary lives in [design.md](design.md) §4; the compatibility contract and the
deliberate differences (D-n) are in [compat.md](compat.md).

- Source: `github.com/tlaplus/tlaplus`, checked out under `third_party/tlaplus` at the baseline
  revision `1813307068bbc5759a441df820f3f548948d6b7a` — the revision `third_party/tla2tools.jar`
  reports and `scripts/dependencies.py` pins (see [compat.md](compat.md)). The line numbers
  below refer to that checkout; when only the jar is available, read the same class with
  `javap -p -classpath third_party/tla2tools.jar <fully.qualified.Name>`.
- Path abbreviations, relative to `tlatools/org.lamport.tlatools/src/`: `V/` = `tlc2/value/impl/`,
  `T/` = `tlc2/tool/`, `TI/` = `tlc2/tool/impl/`, `M/` = `tlc2/module/`, `U/` = `util/`,
  `S/` = `tla2sany/`.
- "TLC does X" describes TLC; "tlx" sentences say what tlx does and where.

---

## 1. Values, order and canonical form

### 1.1 Kinds

`tlc2/value/ValueConstants.java:11-36` defines the kind bytes used in fingerprints:
`BOOLVALUE=0, INTVALUE=1, STRINGVALUE=3, RECORDVALUE=4, SETENUMVALUE=5, TUPLEVALUE=7,
FCNRCDVALUE=9, MODELVALUE=21, ...`. Sets have several representations (`SetEnumValue`,
`IntervalValue`, lazy sets) and so do functions (`FcnRcdValue`, `TupleValue`, `RecordValue`,
`FcnLambdaValue`). Comparison and fingerprinting first convert to a common form.

### 1.2 Total order (`compareTo`)

| Type | Order | Source |
|---|---|---|
| Bool | `FALSE < TRUE` | `V/BoolValue.java:38-55` |
| Int | `Integer.compare`, 32-bit signed | `V/IntValue.java:74-89` |
| String | compares `UniqueString.tok`, the **intern number** (§1.3) | `V/StringValue.java:47-62`, `U/UniqueString.java:227-232` |
| ModelValue | compares the name's `UniqueString.tok`, not the creation index | `V/ModelValue.java:155-180` |
| Set (any representation) | both sides `toSetEnum()` + `normalize()`; **size first**, then elements pairwise | `V/SetEnumValue.java:90-115` |
| Interval vs Interval | size, then `low`; empty intervals are equal | `V/IntervalValue.java:35-53` |
| Function | both `toFcnRcd()` + `normalize()`; domain size, then the whole domain element by element, then the values (only if the domains are equal) | `V/FcnRcdValue.java:148-257` |
| Tuple | if the other side `toTuple()`s: length, then elements; else via `FcnRcd` | `V/TupleValue.java:67-91` |
| Record | other side `toRcd()`; field count, then field names (by tok), then values | `V/RecordValue.java:302-334` |

Cross-kind comparison fails with `Assert.fail` ("Attempted to compare integer 1 with non-integer:
..."), except for model values:

- An **untyped** model value is smaller than every non-model value
  (`V/ModelValue.java:158-163, 213-226`). The order is consistent.
- A **typed** model value (name `x_...`: length > 2 and second character `_`; the type is the
  first character, `V/ModelValue.java:84-92`) raises an error when compared with a non-model value
  or a model value of another type.

Errors are lazy: they happen only when two incomparable elements are actually compared.

- `{1} = {"a","b"}` is FALSE (sizes differ); `{1} = {"a"}` is an error (`V/SetEnumValue.java:117-140`).
- `{[a|->1,b|->2], <<1>>}` normalizes (different domain sizes); reversing the
  source order fails in the record receiver, and equal-size domains can fail
  too (`V/FcnRcdValue.java:236-241`; D-31).
- Membership in a normalized `SetEnumValue` is a binary search with `compareTo`
  (`V/ValueVec.java:144-169`): `"a" \in {1,2}` is an error, `"a" \in {}` is FALSE.

tlx: `tlx_value::order::cmp_tlc` (order) and `eq_tlc` (equality). Function
representations compare symmetrically by domain and values (D-18/D-31).

### Comparisons in heterogeneous sets

Checked against the bundled TLC bytecode (`javap -c -p` on `SetEnumValue`,
`SetEnumValue$Enumerator`, `ValueVec`, `RecordValue` and `TupleValue`), and
the cached `FzHeterogeneous*` oracles:

- A set literal stores evaluated elements without comparing them. `member`
  calls `ValueVec.search`: a non-normalized set scans source order, calling
  the **element's** `equals(query)` and stopping at the first match. A
  normalized set uses binary search with `query.compareTo(element)`.
- `SetEnumValue.normalize` calls `ValueVec.sort(true)`, a binary insertion
  sort with the inserted value as receiver, and removes equal elements.
  `size`, equality, comparison, `fingerPrint`, printing and the ordinary
  `Enumerator` constructor require normalization. `SUBSET S` is lazy;
  enumerating or fingerprinting it normalizes S.
- `cap` and `diff` scan the stored left elements directly, calling membership
  on the right. They preserve the left normalization flag. `cup` copies the
  left stored elements, enumerates the right, and appends only elements that
  are not members of the left; its result is non-normalized. Thus these
  operations need not compare every pair of source elements. `UNION` of an
  explicit set of explicit sets scans both stored levels and tests membership
  in its growing result; those membership errors occur during evaluation. A
  filter over an explicit set obtains its normalized enumeration immediately.
  `FzHeterogeneousBigUnionErrorCounts` and `FzHeterogeneousFilterErrorCounts`
  therefore fail with generated=1, distinct=1, depth=1.
- A successfully assigned successor is counted before normalization and
  fingerprinting. For the mixed set/function and tuple/set successors in
  `FzHeterogeneousUnionErrorCounts`, `FzHeterogeneousIntersectionParanoid`,
  `FzHeterogeneousSubsetErrorCounts` and `FzHeterogeneousSubsetCompiled`, both
  checkers report an error with generated=2, distinct=1, depth=1. Construction
  must not move that error before the successor is assigned.
- Untyped model values compare unequal to non-model values and sort before
  them. Typed model values reject non-model values and differently typed
  model values; they compare by interned symbol with untyped model values.
  This rule applies when the comparison actually occurs, so a successful
  linear membership test can avoid a later incompatible element.

TLC's function-representation asymmetry is a defect, not a rule to reproduce:
`record.compareTo(tuple)` can fail while the reverse succeeds; same-size
integer/string domains can also fail despite being unequal. D-31 extends
D-18 to normalization, membership and fingerprints. tlx compares functions
by domain and then pointwise values, retaining errors for incomparable values
at the same argument. Genuine non-function incompatibilities still fail at
the consuming operation, not when the set literal is built.

Implementation: potentially incomparable explicit sets use `LazySet::Enum`;
homogeneous sets keep `Value::Set`. The interpreter's syntax and closure
paths use `Value::set_enum`. Encoded constructors require a statically
comparable element shape; otherwise closure IR, C and JIT use the shared
value operation. In particular, reflexive set-map equality must still
normalize the set, and cannot become word equality over an unchecked shape.
Stored-value comparisons apply the same domain rule as boxed values; their
cross-product comparison tests check both results and errors against the
interpreter.

### 1.3 Strings and model values are ordered by intern order

`UniqueString.compareTo` returns `this.tok - other.tok` (`U/UniqueString.java:227-232`); `tok` is
`++tokenCnt` at first interning (`U/InternTable.java:118-121`). So `{"b","a"}` may normalize to
`"b" < "a"`. Within one TLC run strings are interned in this order:

1. Static strings of TLC and SANY classes (`"level"`, `"diameter"`, `"action"`, `"state"`, ...;
   depends on class-loading time and cannot be listed exactly).
2. **The `.cfg`**, parsed before SANY runs (`TI/Spec.java:99-100`; SANY at `:111`). Model value
   names (`TI/ModelConfig.java:571`, `V/ModelValue.java:84-86`) and string literals
   (`TI/ModelConfig.java:540`) are interned in cfg order: `Proc = {p3, p1, p2}` orders
   `p3 < p1 < p2`.
3. **SANY parsing**: the root module (`S/modanalyzer/SpecObj.java:909`), then EXTENDS/INSTANCE
   modules in discovery order. Every token image is interned
   (`S/parser/SyntaxTreeNode.java:227,245`), including identifiers and field names; string-literal
   tokens are interned *with* quotes, so they differ from the content. A string `"a"` takes its
   parse-time number if `a` also occurs as an identifier anywhere.
4. **Semantic analysis**, dependency order, standard modules first (`S/drivers/SANY.java:421`);
   string literal contents are interned when the `StringNode` is created
   (`S/semantic/StringNode.java:35-39`).
5. **Run time**: strings created by `\o`, `Tail`/`SubSeq` on strings, `ToString`, `TLCModelValue`,
   JSON, ... (`new StringValue(String)` always interns). The first batch is the constant
   definitions TLC evaluates at startup (`SpecProcessor.processConstantDefns`, before ASSUME and
   Init): modules in `ExternalModuleTable` order (dependencies first, root last), skipping
   modules that are INSTANCEd with CONSTANT/VARIABLE (`ModuleNode.processConstantDefns`); per
   module first the `C <- Def` replacements of 0-ary constants, then the constant-level 0-ary
   definitions in declaration order (`getOpDefs`, LOCAL included; a named 0-ary INSTANCE
   contributes `I!D` at its position); evaluation errors are ignored. Then ASSUME, Init, and
   during the search (one worker) for each generated successor: constraints, invariants (of new
   states), action properties, then the next successor. With several workers this order is a race
   (compat.md D-9).

The order matters for `CHOOSE` over sets of strings or model values, SYMMETRY representatives,
printing and `ToString`.

tlx: `intern_cfg` / `intern_sources` (`tlx-eval/src/interp/cfg.rs`) register cfg values, then
identifier tokens in SANY's file order (`Program::sany_file_orders`), then string literals; the
table is `tlx-value/src/intern.rs`. Startup constant evaluation follows
`Program::tlc_constant_defn_order` and `Interp::eval_constant_defns`. The compiled tier must not
create strings earlier than the interpreter would: `makes_strings` (`tlx-eval/src/strings.rs`)
decides, and constant folding (`closed_const` in `tlx-compile/src/lower/analysis.rs`, `fold_op`
in `lower/typed.rs`) skips operations that may create strings (design.md §6.5).

### 1.4 Set normalization

- `SetEnumValue.normalize()` sorts by binary insertion with duplicate removal
  (`V/SetEnumValue.java:269-275`, `V/ValueVec.java:172`).
- `{a,b}` and `{e : x \in S}` produce **un-normalized** sets (`TI/Tool.java:2428-2449`). Enumeration
  (`Enumerator` constructor, `V/SetEnumValue.java:447-449`), `size()`, fingerprints,
  `compareTo`/`equals` and printing normalize first, so enumerating a `SetEnumValue` always yields
  canonical order without duplicates. `ToString`/`Print` also print normalized sets
  (`V/SetEnumValue.java:405-407`, `M/TLC.java:63-70`).

### 1.5 Enumeration order of lazy sets (`elements()`)

| Expression | TLC representation | Order | Source |
|---|---|---|---|
| `a..b` | `IntervalValue` | ascending; empty if `b<a` (equal to `{}`) | `V/IntervalValue.java:108-122` |
| `SUBSET S` | `SubsetValue` | **canonical**: by cardinality, then lexicographic over the normalized S; `SUBSET {}` = `{{}}` | `V/SubsetValue.java:518-560, 743-760` |
| `[S -> T]` | `SetOfFcnsValue` | domain in S's canonical order; **last domain element varies fastest**; `[{} -> T]` = `{<<>>}` | `V/SetOfFcnsValue.java:555-636` |
| `S1 \X ... \X Sn` | `SetOfTuplesValue` | **last component fastest** | `V/SetOfTuplesValue.java:491-545` |
| `[f1: S1, ...]` | `SetOfRcdsValue` | fields sorted by tok (`sortByNames`), **last field fastest** | `V/SetOfRcdsValue.java:32-40, 504-524` |
| `{x \in S : P}` | evaluated immediately to a `SetEnumValue` if S is `SetEnumValue`/Interval (Reducible), else lazy `SetPredValue` | filter of S's order | `TI/Tool.java:2469-2518` |
| `S \cup T` | merged immediately (with `member` dedup) if either side is Reducible; **otherwise `SetCupValue`: S then T, no dedup** | | `V/SetEnumValue.java:198-216`, `V/SetCupValue.java:279-310` |
| `UNION S` | merged and deduplicated if S and all its elements are `SetEnumValue`; **otherwise `UnionValue`, nested, no dedup** | | `V/UnionValue.java:217-241, 334-380` |
| `S \cap T`, `S \ T` | immediate if Reducible; else lazy, filtering with the other side | | `TI/Tool.java:2682-2702` |
| `Seq(S)`, `Nat`, `Int`, `STRING` | `UserValue`, **not enumerable** | | `M/Sequences.java:53-57` |

Multi-variable quantifiers `\E x \in S, y \in T` are enumerated by `ContextEnumerator` with the
**first variable fastest** (`T/impl/ContextEnumerator.java:40-73`), the opposite of `\X`.

Counting pitfall: `SetCupValue` and `UnionValue` enumerate **duplicates**, so
`x' \in (SUBSET A) \cup (SUBSET B)` or `\E s \in UNION {1..2, 2..3}` generate duplicate successors,
each counted in `generated` (not in `distinct`). tlx keeps these sets lazy and un-deduplicated
(`tlx-value/src/ops/mod.rs` mirrors TLC's Reducible decision; `tlx-value/src/lazy.rs`,
`ops/enumerate.rs`).

---

## 2. Equality (`=`, `#`, `\in`)

`=` calls `Value.equals` (`TI/Tool.java:2585-2590`), `#` negates it (`:2654-2659`), `\in` calls
`member` (`:2670-2681`).

| Case | Result | Source |
|---|---|---|
| `1 = "a"`, `1 = {1}`, `TRUE = 1`, `{} = 0` | **error** | each class's `equals` |
| untyped MV `= ` non-MV | FALSE | `V/ModelValue.java:183-188, 234-249` |
| typed MV vs non-MV or other type | **error** | same |
| `<<>> = {}`, `{} = <<>>` | **error** (`SetEnumValue` has no `toTuple`/`toFcnRcd`) | `V/TupleValue.java:93-99`, `V/SetEnumValue.java:117-122` |
| `[i \in {} |-> 1] = <<>>` | TRUE | `V/FcnRcdValue.java:299-317` |
| `<<a,b>> = [i \in 1..2 |-> ...]` | compared by value | same |
| `[a|->1] = [x \in {"a"} |-> 1]` (both directions) | TRUE | `V/RecordValue.java:336-367`, `V/FcnRcdValue.java:259-331` |
| `<<1>> = [a|->1]` | **error** | `V/FcnRcdValue.java:280-287` |
| `<<1>> = [a|->1,b|->2]` | FALSE (length differs, early return) | `V/FcnRcdValue.java:281` |
| `[a|->1] = <<1>>` (any length) | **error** (`TupleValue.toRcd()` succeeds only at length 0) | `V/RecordValue.java:338-344`, `V/TupleValue.java:260` |
| `"abc" = <<"a","b","c">>` | **error** (strings are not sequences) | `V/StringValue.java:64-75` |
| `1..0 = {}`, `2..1 = 5..3` | TRUE | `V/IntervalValue.java:58-66` |
| `x \in 1..3`, x a string | error; FALSE if the interval is empty or x is an untyped MV | `V/IntervalValue.java:69-84` |
| `1 \in STRING`, `"a" \in Nat` | **error** | `M/Strings.java:41-48`, `M/Naturals.java` |

Equality is "convert, then compare structurally": if one side converts to the other's
representation (`toTuple`, `toRcd`, `toFcnRcd`) the values are compared semantically; otherwise the
result is usually an error, not FALSE. The result can depend on operand order.

---

## 3. CHOOSE

- **Bounded** `CHOOSE x \in S : P` (`TI/Tool.java:2115-2201`) normalizes S (`:2154`) and returns the
  first element in `elements(Ordering.NORMALIZED)` order (`:2156`) that satisfies P: the minimum
  under `compareTo`. `EnumerableValue.elements(NORMALIZED)` normalizes the whole set
  (`V/EnumerableValue.java:83-101`); `SubsetValue` enumerates in canonical order directly
  (`V/SubsetValue.java:743-750`). No satisfying element: error "CHOOSE x \in S: P, but no element
  of S satisfied P." (`:2198-2199`). Tuple patterns `CHOOSE <<a,b>> \in S` call `toTuple` per
  element (`:2160-2173`). S must be enumerable (`:2120-2123`).
- **Unbounded** `CHOOSE x : P` **always errors**: "TLC attempted to evaluate an unbounded CHOOSE."
  (`TI/Tool.java:2529-2535`); unbounded `\E`/`\A` too (`:2536-2549`). Definitions such as `NoVal`
  must be overridden with a model value in the cfg.
- CHOOSE is deterministic, so the canonical order, including the intern order of §1.3, must match.

tlx: `tlx-eval/src/eval.rs` (`QuantUnbounded` and unbounded CHOOSE produce the same errors).

---

## 4. Integers

- `IntValue.val` is a Java `int` (`V/IntValue.java:48`). A literal outside the int range fails in
  preprocessing: "TLC can't handle a number this big." (`TI/SpecProcessor.java:2045-2056`).
- `+`, `-`: overflow error (`M/Naturals.java:54-76`); `*` computed in `long`, overflow error
  (`:78-94`); `^`: `y<0` error, `0^0` error ("0^0 is undefined."), `x^0 = 1`, repeated
  multiplication with an overflow check each step (`:194-221`); unary minus: `-(-2147483648)`
  overflows (`M/Integers.java:144-152`).
- `%`: divisor `<= 0` is an error; the result is in `[0, y)` (`M/Naturals.java:181-192`).
- `\div`: divisor 0 is an error. **Two implementations exist:**
  - `Integers.Divide` (`M/Integers.java:154-172`): correct floor division; `MIN \div -1` overflows.
  - `Naturals.Divide` (`M/Naturals.java:167-179`): `q = n1/n2; if (q<0 && q*n2 != n1) q--`. A
    truncated result of 0 is **not** corrected, so `(0-1) \div 2 = 0`; no overflow check.
  - Which one runs is per module: `processModuleOverrides` walks modules in dependency order and
    sets the Java method on the same-named definitions in each module's `getOpDefs()`, which
    includes EXTENDS-imported definitions as the same node objects
    (`TI/SpecProcessor.java:2114-2186`, `S/semantic/Context.java:385-400`). A spec that
    (transitively) EXTENDS `Integers` gets the correct `\div`; EXTENDS `Naturals` alone gets the
    flawed one. Differences only show for negative dividends.
- `< <= > >=` on non-integers error (`M/Naturals.java:96-160`). `a..b` builds an interval without
  checks; only `size()` over 2^31-1 elements errors (`V/IntervalValue.java:113-118`).
- `Nat` and `Int` are `UserValue`s: membership only, not enumerable.
- Size overflow errors: `SUBSET S` with `|S| >= 31` (`V/SubsetValue.java:182-190`); `[S->T]` and `\X`
  size products over int (`V/SetOfFcnsValue.java:244-265`, `V/SetOfTuplesValue.java:232-246`).
  These are errors of `size()` (= `Cardinality`); **enumeration does not ask for the size**, but the
  *order* asked for decides whether anything is built: `Enumerable.elements()` (the default order,
  used by `x' \in S` `TI/Tool.java:836,1455`, by `{x \in S : P}` `V/SetPredValue.java:350-372` and by
  printing `:317-322`) streams (`V/SubsetValue.java:753-767`, and the enumerators of
  `SetOfFcnsValue`/`SetOfTuplesValue`/`SetOfRcdsValue` at `:458`/`:473`/`:449`), while
  `elements(Ordering.NORMALIZED)` (a bound: `TI/Tool.java:4083-4117`; `CHOOSE`: `:2156`) is
  implemented by materializing `toSetEnum()` for every set type except `SetEnumValue`, `SubsetValue`
  (`V/SubsetValue.java:743-751`) and `KSubsetValue` (`V/EnumerableValue.java:83-101`); materializing
  more than `-maxSetSize` elements (default 10^6, `V/ValueVec.java:88-92`) is TLC's "too many
  elements" error. What raises the *overflow* is `size()`/`Cardinality`, materializing
  (`SubsetValue.toSetEnum` asks `size()`, `:304`; the tuple and record enumerators convert every
  constituent with `toSetEnum`) and the paths that still hold a whole set (`CHOOSE` normalizes it).

  tlx: `tlx-value/src/ops/enumerate.rs` (`for_each_enumerated` streams such a set in the default
  order; `enumerate` refuses it and `materialization_error` reports the overflow),
  `ops::bound_kind` (the single decision both the interpreter's `bound_elems` and the compiled
  tier's boxed-domain iteration follow: share an enumerated set or an interval, stream a
  `SUBSET S`/`kSubset(k, S)`, materialize every other lazy set, and report the bound for a size
  over the int) and `tlx-value/src/limits.rs`. Materializing enforces `-maxSetSize` exactly where
  TLC's growing `ValueVec` does, including its ten initial slots (`V/ValueVec.java`: the check runs
  only when the vector grows, so `max(10, N)` elements fit) and the eager cup that copies an
  interval (`(1..n) \cup {}` reports the bound), while enforcing `-maxSetSize` on canonical
  distinct elements of homogeneous explicit sets in `\cup`, `\cap` and `\` rather than imitating
  TLC's mutable in-place normalization aliasing ([compat.md](compat.md) D-35). `x' \subseteq S`
  (and `x \subseteq S` in `Init`, outside `-generate`) streams `SUBSET S` in normalized order; a
  `CHOOSE` and a bound of several variables still keep the overflow (see [compat.md](compat.md) section 5).

tlx: `tlx_value::arith` (`add`, `sub`, `mul`, `pow`, `neg`, `modulo`, `div_floor`, `div_naturals`;
values are `i64` with an i32 range check per operation; generated C uses `tlx_add` etc. from
`runtime.h`). `Interp` picks `div_floor` when the program has the `Integers` module
(`tlx-eval/src/interp/mod.rs`, field `div_floor`). tlx has no int64 mode.

---

## 5. Init / Next enumeration

### 5.1 Action splitting (`getActions`, `TI/Tool.java:225-430`)

`[][N]_v` in a `SPECIFICATION` contributes only N, **with no stuttering branch**; the subscript is
used only for a warning (`TI/SpecProcessor.java:1176-1200`). N is split along `\/`, bounded `\E`,
user operators with zero or all-constant-level arguments, LET and labels into `Action`s
(`:332-428`):

- The range of `\E i \in S` is evaluated at startup (no state). If that throws, the whole `\E`
  stays one action (`:375-402`). An empty range makes the `\E` an **action without successors**
  that still appears in the action list, `-coverage` (`0:0`), `TLCGet("spec").actions` and
  `-simulate` selection.
- Operators with arguments are expanded only if **all arguments are constant level** (`:340-362`).
  Otherwise (and for definitions that TLC evaluates to a value: constant 0-ary definitions, cfg
  assignments, Java overrides) the whole application is one action **named after the operator**,
  located at the application, without argument values.
- **INSTANCE with substitutions** (also implicit same-name substitutions): the body appears as a
  `SubstInNode`; `getActions` does not split it: one action, located at the INSTANCE statement,
  named with the instance prefix (`I!Next`; arguments shown, `I!B(1)`). If the spec's `[][N]_v` was
  found through an instance, `SpecProcessor` wraps N in the substitution and N is a single unnamed
  action; the initial predicate is likewise seen under the substitution (`-coverage` Init line).
- Actions that come from no definition (`Spec == x = 0 /\ [][x' = x + 1]_x`) are unnamed: trace
  label `<Action location>`, `TLCGet` name `UnnamedAction`.
- Splitting does not change the successor set or counts; it affects statistics granularity and
  BFS order.

tlx: `Interp::split_actions` (`tlx-eval/src/enumerate.rs`).

### 5.2 Init (`getInitStates`, `TI/Tool.java:435-871`)

Top-level conjuncts are processed **left to right** (`:438-450`). For a partially assigned state
and a pending list:

| Form | Behavior |
|---|---|
| `A /\ B` | A first, B pushed on the pending list (`:649-656`) |
| `A \/ B` | each branch in turn, each continuing with the rest of the list (`:641-648`) |
| `\E x \in S : P` | P for each element of S (`:658-667`) |
| `\A x \in S : P` | **expanded to a conjunction** P[x1] /\ P[x2] /\ ... (`:668-685`), so it can assign |
| `IF c THEN A ELSE B` | evaluate c, process the chosen branch (`:686-697`) |
| `CASE` | the **first** true guard in written order, else OTHER; none: error (`:698-726`) |
| `x = e` (x a variable) | assigns if x is unassigned, else tests `lval.equals(rval)` (`:756-783`) |
| `x \in S` | unassigned: **enumerates** `S.elements()` (error if not enumerable); assigned: membership (`:818-852`) |
| `x \subseteq S` | unassigned: enumerates `SUBSET S` in canonical order (`:784-817`) |
| `P => Q` | Q if P is true, else continue (`:853-868`) |
| user operator, LET name | substitute the body and continue (`:583-594`); arguments are lazy, so `x = ...` inside `F(x)` can assign |
| anything else | evaluated as a boolean; FALSE prunes the branch (`:870-880`) |

- Only a **variable on the left** assigns; `e = x` is plain evaluation. Evaluating an unassigned
  variable errors: "In evaluation, the identifier x is either undefined or not an operator."
  (`TI/Tool.java:2106-2107`).
- Once all variables are assigned the remaining conjuncts are only evaluated as predicates
  (`:534-567`; an optimization with the same semantics).
- At the end of the list `ps.copy()` goes to the functor without a completeness check; the check is
  in `DoInitFunctor` ("current state is not a legal state", `T/ModelChecker.java:1169-1175`).

### 5.3 Next (`getNextStates`, `TI/Tool.java:900-1690`)

Same structure as Init, with these differences:

| Form | Behavior |
|---|---|
| `x' = e` | if `getPrimedVar` recognizes `x'` (through LET, 0-ary definitions and lazy parameters, `TI/Spec.java:138-204`): assigns if unassigned, else tests equality; otherwise plain evaluation (`:1353-1377`) |
| `x' \in S` | unassigned: enumerates `S.elements()`; assigned: membership (`:1422-1468`) |
| `x' \subseteq S` | enumerates `SUBSET S` (`:1379-1421`) |
| `UNCHANGED e` | variable: unassigned gets `s0[x]`; assigned and different: **prints "variable x was changed while it is specified as UNCHANGED" and prunes the branch** (`:1650-1680`); tuple: item by item; 0-ary definition: expands the body; otherwise evaluates on s1 and compares (`:1560-1608`) |
| `[A]_e` | **both branches**: A and `UNCHANGED e` (`:1295-1305`), so a nested `[A]_e` yields stuttering successors counted in generated |
| `<A>_e` | A, plus a trailing "e must change" check (`:1290-1294`, `:1037-1046`) |
| `\E`, `\/`, `\A`, IF, CASE, `=>` | as in Init (`:1189-1352`, `:1470-1483`); CASE takes the first true guard |
| `f[x]` as an action | expands the body of a lazy function (`:1263-1289`) |
| empty list | `nss.addElement(s0, action, s1)` (`:1003-1005`), no completeness check here |

- Referring to an unassigned `y'` (`y' > 0` before `y' = ...`) is an evaluation error (same message
  as in §5.2). Re-assigning a differently typed value (`x' = 1 /\ x' = "a"`) is an **error**, not FALSE.
- Completeness is checked when the `Worker` receives the successor: "Successor state is not
  completely specified by action ... The following variable(s) not defined: ..."
  (`T/Worker.java:423-429`, `tlc2/output/MP.java:611-614`).

tlx: `tlx-eval/src/enumerate.rs` (the compiled tier lowers the same semantics:
design.md §6.3).

### 5.4 Counting, constraints and deadlock (`T/Worker.java:92-160, 418-497`, `T/ModelChecker.java:1151-1229, 1027-1035`)

```
generated = initial states generated (duplicates and out-of-constraint ones included)
          + sum over expanded states of successors handed to addElement
            (stuttering, duplicates and out-of-constraint ones included)
distinct  = size of the FPSet (in-constraint states only, initial states included)
```

Processing of a successor `t` of `s` (`T/Worker.java:418-472`):

1. `statesGenerated++`.
2. Check that all variables are assigned, else error.
3. `inModel = all CONSTRAINT(t) && all ACTION_CONSTRAINT(s,t)`; t's predecessor is set before the
   constraints, so `TLCGet("level")` is t's level.
4. If `inModel`, insert the fingerprint into the FPSet and get `seen`. **If not `inModel` the FPSet is
   not touched and `unseen` stays true.**
5. If `unseen`, check INVARIANT: **an out-of-constraint state is checked on every generation** and a
   violation is reported.
6. Check action properties whether or not `seen`.
7. If `inModel && unseen`, enqueue.

Initial states (`T/ModelChecker.java:1151-1210`) are handled alike: CONSTRAINT only (no
ACTION_CONSTRAINT); out-of-constraint initial states are neither in the FPSet nor queued, but their
invariants are checked.

**Deadlock**: after expanding a state, if `statesGenerated` did not increase, it is a deadlock
(`T/Worker.java:125-130`). Any generated successor (`s'=s`, already seen, out of constraint)
prevents it. Only enqueued states are checked. Enabled unless `-deadlock` is given or the cfg says
`CHECK_DEADLOCK FALSE` (`tlc2/TLC.java:1437`).

Report format (`tlc2/output/MP.java:1206-1211, 1261-1264`): "Finished computing initial states: N
distinct state(s) generated" (when generated equals the FPSet size) or "N states generated, with M
of them distinct"; at the end "X states generated, Y distinct states found, Z states left on
queue."; the depth is the largest BFS level, initial states being level 1 (`T/TLCTrace.java:119-125`).
`ModelChecker.doNext` (`T/ModelChecker.java:414-470`) is used only when replaying errors.

tlx: `tlx-runtime/src/explore/worker.rs` (the per-successor hot path), `tlx_runtime::admits`
(CONSTRAINT then ACTION_CONSTRAINT, `tlx-runtime/src/model.rs`), `Model::extra_generated` for
`\cdot` intermediate states. design.md §7.3.

### 5.5 BFS order

TLC's queue is FIFO; actions are processed in `getActions` order, successors within an action depth
first (§5.2/§5.3), `\E`/`\in` in §1.5 order. Counts **depend on exploration order** (tlx reproduces
it exactly; multi-worker TLC is itself nondeterministic here) with:

- **VIEW**: only the first discovered state of each view class is expanded;
- **SYMMETRY** on a spec that is not actually symmetric;
- `TLCSet`/`TLCGet(i)`, `RandomElement`, `Randomization`, `JavaTime`, `TLCGet("distinct"|"generated"|"queue"|"duration")`;
- **early stop** on an invariant violation, deadlock or evaluation error.

**Search depth with several workers (D-3).** `ConcurrentTLCTrace.getLevel()` takes the
maximum of every `Worker.getMaxLevel()`; `Worker.writeState(curState, ..., sucState)`
updates that maximum to `curState.getLevel() + 1`. `ModelChecker.printSummary()` uses
`getLevelForReporting()`. Thus depth records the deepest discovered state, not the
level of the state that deadlocks or violates a property. TLC uses a shared FIFO
queue without a barrier between levels; other workers can discover deeper states
while the worker reporting the error prints its counterexample. It is not a
constant offset from the counterexample length.

Reproduction with the baseline jar, fixed `-fp 0`, six runs each:
`java -Xmx4g -XX:+UseParallelGC -cp tla2tools.jar tlc2.TLC -workers N -fp 0
-config ParallelDeadlockDepth.cfg ParallelDeadlockDepth.tla` (copy the spec and cfg
from `tests/specs` into a scratch directory first). With `N=1`, all runs generated
192 distinct states and reported depth 3. With `N=8`, depths were
19, 16, 20, 21, 21, 21 and generated/distinct counts were
1136, 972, 1230, 1245, 1296, 1284; every deadlock trace had three states.
Adding `Inv == branch # 1 \/ step < 2` and `INVARIANT Inv` in the cfg
reproduces it for safety violations too: three single-worker depths were 3, 3, 3
(129 generated/distinct); three eight-worker depths were 17, 21, 11
(1032, 1326, 657 generated/distinct).
These observed numbers demonstrate the race; they are not multi-worker test expectations.

**Which safety violation is reported with several workers (D-3).** The race
can change the reported kind and name as well as the trace. This small probe
has an invariant violation and an action-property violation at the same BFS
level:

```tla
---- MODULE SameLevelFanout ----
EXTENDS Naturals
VARIABLE x
Init == x \in 0..1
Next == IF x = 0 THEN x' \in 2..1000 ELSE x = 1 /\ x' = 1001
Inv == x # 1000
AProp == [][x' # 1001]_x
====
```

Use `INIT Init`, `NEXT Next`, `INVARIANT Inv`, `PROPERTY AProp` and
`CHECK_DEADLOCK FALSE` in the cfg, and run the baseline TLC jar in a scratch
directory with `-Xmx2g -fp 0`. One single-worker run reported `Inv` (the step
`x = 0` to `x = 1000`); three `-workers 4` runs reported `AProp` (the step
`x = 1` to `x = 1001`). Both are genuine two-state violations at depth 2.
These observed schedules are evidence of the race, not fixed multi-worker
expectations. The choice of a valid same-level violation (kind/name and
trace) is tier 3; the single-worker result remains the strict oracle.

The external `vanlightly-raft/standard-raft/RaftWithReconfigJointConsensus` model
also reproduces it with a reduced cfg: `Server = {n1, n2, n3}`,
`InitClusterSize = 2`, `MaxReconfigs = 1`, all other settings unchanged.
Three `-workers 1 -fp 0` runs reported depth 7 (546 generated / 337 distinct);
three `-workers 8 -fp 0` runs reported depths 8, 8, 9 (387/269, 340/240, 448/315).
Consequently difftest and spectest compare early-stop depth only with one worker;
completed model-checking searches continue to compare depth with several workers.

---

## 6. Fingerprints (`tlc2/util/FP64.java`)

- FP64 is a 64-bit Rabin fingerprint; the irreducible polynomial is chosen by `FP64.Init(n)` from
  `Polys[]` (`FP64.java:417-450`). `Extend(fp, int)` extends by 4 bytes, low first (`:144-166`);
  `Extend(fp, String)` uses only the **low 8 bits of each char** (`:61-71`).
- State fingerprint: `FP64.New()` then each variable's value fingerprint in index order
  (`T/TLCStateMut.java:247-258`). With VIEW, the fingerprint of the VIEW value (`:259-269`). With
  SYMMETRY, the lexicographically least value vector under `compareTo` over all permutations
  (`:205-245`).
- Layouts ("->" = successive Extend):

| Value | Layout | Source |
|---|---|---|
| Bool | `BOOLVALUE(byte)` -> `'t'/'f'(char)` | `V/BoolValue.java:168-172` |
| Int | `INTVALUE(byte)` -> `val(int)` | `V/IntValue.java:203-205` |
| String | `STRINGVALUE(byte)` -> `len(int)` -> `chars` | `V/StringValue.java:192-196` |
| ModelValue | `MODELVALUE(byte)` -> `tok(int)` (intern number, stable only within a run) | `V/ModelValue.java:361-363`, `U/UniqueString.java:251-254` |
| **all sets** | converted to a normalized `SetEnumValue`: `SETENUMVALUE` -> `size` -> element fingerprints in canonical order | `V/SetEnumValue.java:348-358`, `V/IntervalValue.java:266-277`, lazy sets delegate |
| **all functions** (FcnRcd, Tuple, Record, FcnLambda) | `FCNRCDVALUE` -> `n` -> per (domain element, value) the two fingerprints, domain in canonical order. A tuple writes `(INTVALUE, i)` and a record `(STRINGVALUE, len, name)` for domain elements, byte-identical to Int and String | `V/FcnRcdValue.java:814-834`, `V/TupleValue.java:326-337`, `V/RecordValue.java:691-704`, `V/FcnLambdaValue.java:745-748` |

Consequence: semantically equal values have equal fingerprints in any representation (a tuple, a
function on `1..n` and a function on `{1,..,n}`; a record and a string-domain function; empty
tuple, record and function are all `FCNRCDVALUE,0`; `{}` and `1..0` are `SETENUMVALUE,0`), while
`{}` and `<<>>` differ (they are not comparable in TLC anyway). `UserValue`s (`Nat`, `Seq(S)`) in a
state fail: "TLC has found a state in which the value of a variable contains ..."
(`V/Value.java:267-276`).

tlx does not reproduce FP64 values (counts are affected only by collisions) but guarantees
"semantically equal implies equal fingerprint" and that `{}` and `<<>>` stay distinct
(`tlx-value/src/fingerprint.rs`; design.md §5).

---

## 7. Standard module overrides (`M/`)

Overrides are bound per module: the Java class of the same name is loaded, `TLARegistry` maps method
names to operator names, and the method is attached to the same-named definitions of that module
(`TI/SpecProcessor.java:2114-2186`); annotation-based overrides (`@TLAPlusOperator`,
`@Evaluation`) are at `:2195-2310`. Argument type mismatches error (`V/MethodValue.java:137-170`).
tlx's equivalent is the `(module, definition)` -> `Builtin` table in `tlx-sema/src/builtins.rs`,
evaluated in `tlx-eval/src/builtins.rs` and `natives.rs`.

**Naturals / Integers**: `Nat`, `Int`, `+ - * ^ < \leq > \geq .. \div %`, unary `-` (Integers only);
see §4.

**Sequences** (`M/Sequences.java`):

| Operation | Behavior |
|---|---|
| `Seq(S)` | `UserValue`, **not enumerable** (`\E`, `\in` assignment and CHOOSE error). Membership: `toTuple`, then every element in S (`:393-410`). `IsFiniteSet(Seq(S))` is true only for empty S (`:418-421`) |
| `Len(s)` | length for strings; otherwise `toTuple` or error (`:59-73`) |
| `Head`, `Tail` | empty sequence: error "Attempted to apply Head to the empty sequence."; `Tail` accepts strings, `Head` does **not** (`:75-115`) |
| `Append`, `Cons` | `toTuple`; `Append({}, x)` errors; **no strings** (`:117-145`) |
| `\o` | strings concatenate (result interned at run time); string with non-string errors; an empty sequence returns the other side (`:147-190`) |
| `SubSeq(s,m,n)` | `m>n` returns `<<>>` (or `""`) **without bounds checks**; otherwise m and n must be in `1..Len(s)`. Strings supported (`:262-326`) |
| `SelectSeq(s, Test)` | filters in order; empty s returns empty without checking Test (`:328-366`) |
| functions | `Len`, etc. work on any function with domain `1..n` (`toTuple` succeeds, `V/FcnRcdValue.java:624-644`) |

**FiniteSets**: `IsFiniteSet` calls `isFinite()` (`Nat` is FALSE); `Cardinality` needs an Enumerable
(else "Attempted to compute cardinality of the value") and computes `size()`, overflow errors
(`M/FiniteSets.java:22-34`).

**TLC** (`M/TLC.java`; TLA definitions in `S/StandardModules/TLC.tla`):

| Operation | Native behavior |
|---|---|
| `Print(o,v)`, `PrintT(o)` | deep-copy and `deepNormalize`, then print; return v or TRUE (`:63-99`) |
| `Assert(c,o)` | TRUE if c, else error "The first argument of Assert evaluated to FALSE; the second argument was: ..." (`:113-120`) |
| `ToString(v)` | `toStringUnchecked`: sets in canonical order; functions with domain `1..n` as `<<..>>`, all-string domains as `[..]`, others as `(d :> v @@ ...)`; strings quoted (`:104-107`, `V/FcnRcdValue.java:925-975`) |
| `d :> e` | singleton `FcnRcdValue` (`:143-150`) |
| `f @@ g` | f's domain first, then g's part not in f; un-normalized `FcnRcdValue` (`:156-248`) |
| `Permutations(S)` | S normalized, n! bijections in lexicographic order, domain canonical (`:301-376`) |
| `SortSeq(s, Op)` | insertion sort from the back, swapping while `Op(new, prev)`; stable for strict orders (`:250-299`); the TLA definition uses CHOOSE and can differ for non-strict Op |
| `RandomElement(S)` | **random** via the `RandomEnumerableValues` RNG (seed from `-seed`) (`:378-435`): element `floor(nextDouble()*n)` of the normalized set; `[S->T]`, record sets and `\X` draw once per component |
| `Any` | `AnySet`, every value is a member (`M/AnySet.java:33-36`) |
| `JavaTime` | current seconds `& 0x7FFFFFFF` (`:126-141`) |
| `TLCGet(i)`, `TLCSet(i,v)` | one register file per worker thread; reading an unset register errors (`M/TLCGetSet.java:160-185, 491`) |
| `TLCGet("level")` | 0 in Init and ASSUME; otherwise `s0.getLevel()` (initial states: 1); in CONSTRAINT the level of the checked successor (`M/TLCGetSet.java:379-396`, `T/TLCState.java:37, 144-152`) |
| `TLCGet("diameter"/"distinct"/"generated"/"queue"/"duration"/"stats"/"config"/"spec"/"action"...)` | run-time statistics, nondeterministic (`M/TLCGetSet.java:186-480`) |
| `TLCEval(v)` | immediate evaluation (`M/TLCEval.java:66`) |

**Bags** (`M/Bags.java:52-450`): native `EmptyBag, IsABag, BagCardinality, BagIn, CopiesIn, (+), (-),
BagUnion, \sqsubseteq, BagOfAll, BagToSet, SetToBag` (**`SubBag` is not overridden**). Bags are
functions `S -> Nat\{0}`. Differences from the TLA definitions: `IsABag(non-function)` is FALSE;
`BagOfAll` does not check counts (an image appearing once keeps its original count, e.g.
`BagOfAll(LAMBDA x : x, <<"a", 3>>) = <<"a", 3>>`; only counts that must be added become integers);
`BagCardinality` and `(+)` on non-bags (counts <= 0 or non-integers) raise EvalException (exit 255);
`CopiesIn` returns the count unchanged; `BagIn`/`CopiesIn` on non-functions is a
NullPointerException (75); adding counts can raise TLC_MODULE_OVERFLOW. **BagsExt** (CommunityModules
`tlc2/overrides/BagsExt.java`) overrides only `FoldBag(op, base, B)`: domain order, each element
repeated by its count, `acc = op(acc, e)` (the TLA definition via MapThenFoldSet differs for
non-commutative op). tlx implements both natively in `tlx-eval/src/bags.rs`.

**Reals**: no real numbers and no Java override; the placeholder definitions of `Reals.tla` are
evaluated: `Real == "Reals"` (a string: `Real = "Reals"` and `Len(Real) = 5` hold, `1 \in Real`
errors), `a / b == CHOOSE m \in Real : ...` ("S was not enumerable", 75), `Infinity` is an
unbounded CHOOSE (75). A real literal `1.5` fails during spec processing with "TLC can't handle
real numbers." (exit 151). tlx evaluates the same placeholders (no native override).

**Apalache** (`Apalache.tla`): no override; TLA definitions: `x := e` is `x = e` (assigns in
Init/Next), `Gen(n) = {}`, `Guess(S) = CHOOSE x \in S : TRUE`, `ApaFoldSet` folds in CHOOSE (canonical)
order, `Skolem`/`Expand`/`ConstCardinality` are identities.

**Strings**: `STRING` is a `UserValue` whose only members are strings; any other non-MV value errors
(`M/Strings.java:23-48`).

**TLCExt** (`M/TLCExt.java`): `AssertError, PickSuccessor, ToTrace, CounterExample, Trace, TLCDefer,
TLCNoOp, TLCModelValue` (creates and interns an MV at run time), `TLCCache, TLCFP, TLCEvalDefinition,
TLCGetOrDefault`.

**Randomization** (`M/Randomization.java:42-120`): `RandomSubset`, `RandomSetOfSubsets`,
`RandomSubsetSet` are random; counts are not reproducible. `RandomSubset(k, S)` draws k indices with
a full-period LCG (`m, a` from `computeOptimalMandA(|S|)`, start `nextInt(n)`, increment a random one
of `RandomGenerator.primes`, the 1341 primes in [1277011, 1295953]); `RandomSetOfSubsets(k, n, S)`
flips k coins, each element chosen with probability n/|S|.

**Random stream** (`V/RandomEnumerableValues.java`): `java.util.Random` seeded by `-seed` (random if
absent). At startup (constant definitions, ASSUME, Init) the main thread uses one stream; in BFS
each expanded state reseeds with `seed ^ fingerprint(state)` (`TLCStateRandom`); in simulation each
thread has a stream that is never reseeded. **0-ary constant-level definitions are evaluated once
at startup** (`SpecProcessor.processConstantDefns`) even if they use `RandomElement`,
`RandomSubset`, `Print` or `JavaTime`: every later reference sees the same value (for example the
random graph `Edges` of `SpanTreeRandom`). Definitions whose startup evaluation fails (for example
`TLCGet("level")`, unset registers) swallow the error and are re-evaluated at each reference.

tlx (`tlx-eval/src/random.rs`, `JavaRandom`): with the same `-seed`, constant-level random choices
are bit-identical to TLC. State-level choices also reseed with `seed ^ fingerprint`, but tlx's
fingerprints differ from TLC's, so the values differ (independent of worker count, exploration order
and replay). **Without `-seed` tlx uses 0** (deterministic), the one deviation from TLC.

**Json** (`M/Json.java`): `ToJson, ToJsonArray, ToJsonObject, JsonSerialize, JsonDeserialize,
ndJson*`; no effect on state counts. tlx: `tlx-eval/src/natives/json.rs`.

---

## 8. Other behaviors that break naive implementations

1. Out-of-constraint states are not in `distinct`, are in `generated`, and have their invariants
   checked each time; deadlock means "no successor generated at all" (§5.4).
2. A nested `[A]_e` inside Next generates a stuttering successor; the top-level `[][N]_v` does not
   (§5.1, §5.3).
3. Duplicate successors count in `generated`: several disjuncts or `\E` values producing the same
   state, and the duplicates of `SetCupValue`/`UnionValue` (§1.5). A `SetEnumValue` is deduplicated
   before enumeration: `x' \in {1,1,2}` yields two successors.
4. CASE takes the first true guard in Init, Next and expression evaluation
   (`TI/Tool.java:698-726, 1321-1352, 2234-2260`); a nondeterministic choice would generate extra
   states.
5. `\A` in Init and Next expands to a conjunction, so `x' = ...` inside it assigns.
6. `UNCHANGED x` with an `x'` already assigned differently only warns and prunes the branch (§5.3).
7. **EXCEPT and function application out of domain**
   - EXCEPT with a key outside the domain returns the function unchanged
     (`V/FcnRcdValue.java:502-560`); a record EXCEPT with a non-string key prints a warning and
     replaces the whole value (`V/RecordValue.java:386-416`); applying a function outside its
     domain errors (`V/FcnRcdValue.java:357-363`).
   - Key lookup depends on the representation: `TupleValue` and interval-domain `FcnRcdValue` error
     on non-integer keys, `RecordValue` on non-string keys; a `FcnRcdValue` over an enumerated
     domain (`[k \in {1, 2} |-> e]`, `:>`, `@@`, Bags, elements of `[{1, 2} -> S]`) compares keys with
     `equals`, so a model-value key is "not in the domain" and EXCEPT returns the function
     unchanged, even when the domain happens to be `1..n` or a set of strings (such a function equals
     and prints like the tuple/record).
   - A lazy `FcnLambdaValue` (not yet materialized) tests domain membership first; an interval
     returns FALSE for an untyped MV, so the function is returned unchanged.
   - tlx keeps the enumerated-domain representation as `Value::Fcn` with `FcnKind`, and functions
     built over an interval `lo..hi` (`lo != 1`; function constructors, elements of `[lo..hi -> S]`,
     recursive functions and their EXCEPT results) as `Fcn` with `FcnDom::Interval`, which reports
     "Attempted to apply function with integer domain to the non-integer argument"
     (`tlx-value/src/value.rs`; tests `tests/specs/SN3`-`SN5`, `SN14`). The compiled encoding preserves
     the construction witness through `FcnWitness` on `Shape::Fcn` and `Shape::Map` (compat.md D-13).
8. String and model-value order is intern order (§1.3); it affects CHOOSE and so the reachable
   state set. Typed model values (`x_...`) error when compared with non-model values.
9. `\div` is flawed when only `Naturals` is extended (§4).
10. `Seq(S)`, `Nat`, `Int`, `STRING` are not enumerable: `x' \in Seq(S)` errors if x' is unassigned;
    once x' is assigned it is just a membership test.
11. **Lazy versus immediate evaluation.** `[x \in S |-> e]` with a Reducible S (`SetEnumValue`,
    `IntervalValue`) and no KeepLazy in the evaluation control is evaluated immediately to a
    `FcnRcdValue`, else kept as a `FcnLambdaValue` (`TI/Tool.java:2354-2380`); `{x \in S : P}` is
    analogous. KeepLazy is set when evaluating the `f` of `f[e]` (`OPCODE_fa`, `:2331`) and
    propagates through IF/CASE/LET, user operator bodies, operator arguments (LazyValue) and 0-ary
    definition bodies (TLC does not cache 0-ary definitions; constant definitions were already
    evaluated eagerly at startup, failed ones are re-evaluated lazily). A `FcnLambdaValue` remembers
    its construction control, so `[i \in S |-> [j \in T |-> e]][a][b]` evaluates one point;
    recursive function bodies are always KeepLazy (`makeRecursive`); an EXCEPT base function is lazy
    but `@` evaluates that point at once. Hence `[i \in 1..3 |-> 10 \div (i-2)][1]` does not fail
    while `DOMAIN [i \in 1..3 |-> 10 \div (i-2)]` does. Lazy values are evaluated on first comparison
    or fingerprint, and their errors appear then. This changes only **whether and when** an error
    occurs, not state counts. tlx: `Ctx::keep_lazy` (`tlx-eval/src/eval/context.rs`); under KeepLazy a cached
    0-ary definition tries the cached value first and falls back to lazy evaluation; a lazy function
    leaving the KeepLazy context (the result of an outer application) is built at once
    (`force_kept`), so `DOMAIN f[a]` evaluates earlier than in TLC.
12. SYMMETRY: the representative is the lexicographically least permuted value under `compareTo`;
    counts are order independent only when the spec is truly symmetric (§5.5, §6).
13. VIEW: `distinct` is the number of distinct view values and only the first discovered state of
    each is expanded, so the BFS order must be exact.
14. FP collisions: TLC's `distinct` counts 64-bit fingerprints; collisions are improbable but
    possible, so exact deduplication could in theory report more.
15. Duplicate initial states count in `generated` ("N states generated, with M of them distinct").
16. An ASSUME that fails to evaluate (rather than being false) reports "Evaluating assumption
    <location> failed.\n<error>" with the same exit code as a false assumption,
    VIOLATION_ASSUMPTION (10), as does a failing `Assert` (`EC.java:423-429`).
17. **Operators whose body is a number or string literal passed as arguments** (`LAMBDA x : 2`,
    `Op(x) == "a"`; parentheses are transparent, `-2` is not a literal): SANY's literal nodes carry
    their value (`SpecProcessor.processConstants`), and `SymbolNodeValueLookupProvider.lookup`
    returns that value for the operator, so an operator parameter receives `IntValue 2` rather than
    an `OpLambdaValue`. TLA+-defined higher-order operators use it as a constant (same result,
    argument never evaluated); Java overrides that need an operator error out: `BagOfAll`
    ("should be an operator"), the Folds, `SortSeq`, `SelectSeq`, `SelectInSubSeq` (OpValue cast
    fails), even for empty sets or bags; `MapThenFoldSet` is an exception. tlx:
    `Interp::native_op_val` (`tlx-eval/src/eval.rs`; test `tests/specs/SN13`).

---

## 9. How the cfg CONSTANT section binds (`TI/SpecProcessor.processConfig:549-768`)

The CONSTANT section has three tables: root-module values `name = v`, module-qualified values
`name = [M] v`, and replacements `name <- op`.

1. **Every constant of the root module must be bound** (value or replacement). "Root module
   constants" are `rootModule.getConstantDecls()`: declarations of the root module **and its EXTENDS
   closure**, operator constants (arity > 0) included; constants replaced by an INSTANCE `WITH` and
   those of nested modules are not included (`S/ModuleNode.java:384-394`). A missing one is
   `EC.TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM` = **2222**, reporting only the **first
   missing one in declaration order**, exit code 151 (`:553-564`). Whether the constant is used is
   irrelevant.
2. **Value assignments land only on root constants and root operator definitions** (`:566-580`,
   `rootConsts` and `rootModule.getOpDefs()`). TLC iterates only those two tables looking up cfg
   names, so any other assignment (names not in the spec, VARIABLEs, definitions that exist only in
   INSTANCEd modules) is **silently ignored**. An INSTANCE `WITH` substitution takes precedence, so
   the cfg cannot assign that name.
3. **`name = [M] v` applies only to operator definitions of module M** (`:582-602`; the source says
   "We do not allow this kind of replacement for constant decls"): the **body** of every same-named
   definition in M becomes v. If M is not in the spec or has no such name, it is silently ignored.
   `getOpDefs()` includes the EXTENDS closure and not INSTANCE definitions.
4. **Replacements `name <- op` are validated** (`:604-768`): the left side must be a root constant
   or definition; the right side must already be in `defns` (a bound constant or root definition),
   else 2224 `TLC_CONFIG_WRONG_SUBSTITUTION`; a right side that is also the left side of another
   replacement is `TLC_CONFIG_RHS_ID_APPEARED_AFTER_LHS_ID`; an unapplied left side is 2226
   `TLC_CONFIG_ID_DOES_NOT_APPEAR_IN_SPEC`; `name <- [M] op` with M missing is `TLC_NO_MODULES`,
   `name` missing in M is 2226, an arity mismatch is
   `TLC_CONFIG_WRONG_SUBSTITUTION_NUMBER_OF_ARGS`. All exit with 151.
5. **Order** (`TI/ModelConfig.java:422-449`): the value and replacement tables are insertion
   ordered, `[M]` entries are kept apart, and `processConfig` handles values before replacements.
6. **Which uses an override reaches.** `name = v` and `name <- op` set the tool object of the
   OpDefNode the root module's name denotes (`rootOpDefs[i].setToolObject`); evaluation looks a
   node's tool object up first, then its body's (`SymbolNodeValueLookupProvider.lookup`, through
   SubstInNode wrappers). Which uses share that node is SANY's business
   (`S/Generator.java`): a definition the root gets by EXTENDS is the module's own node, referenced
   by the bodies of the module in every INSTANCE of it, so they all see the override. A named
   instance `I == INSTANCE M` (module level or in a LET, with or without `WITH`, also of a module
   without declarations) creates new nodes `I!Op` whose body is M's (wrapped in a SubstInNode if
   there are substitutions), so a direct `I!Op` evaluates the original body even when `Op` is
   overridden, while `I!Next` calling `Op` sees the override. An anonymous `INSTANCE M` creates new
   nodes for definitions of modules with parameters (`generateInstance`; definitions of
   parameter-free modules, such as the standard modules, are shared unless the INSTANCE is
   LOCAL), so overriding such a name in the root leaves M's bodies alone. The `[M]` forms set the
   tool object of the **body** (`opDefs[j].getBody().setToolObject`), which the instance nodes
   share, so `I!Op` sees them too. (`Op <- [M] Other` for a 0-ary `Op` stores an OpDefNode where TLC
   expects a value: evaluating it throws a ClassCastException.) Example: tlaplus/Examples'
   MCCheckpointCoordinationFailure overrides `ShouldReplaceLease` with a definition that calls
   `CC!ShouldReplaceLease` of `LET CC == INSTANCE CheckpointCoordination`: the original body.
   tlx: `Program::entry_def` (`tlx-sema/src/resolve/mod.rs`) gives these uses definitions of their
   own and `bind_entries` (`tlx-eval/src/interp/cfg.rs`) makes the ones whose node is not
   overridden aliases; tests `tests/specs/OvrInst*`, `OvrEntry*` (compat.md D-23).

tlx: `Program::check_cfg_constants` and `Program::check_cfg_substitutions`
(`tlx-sema/src/resolve/mod.rs`) implement 1, 2 and 4 (left side, declared `CONSTANT` and
operator definition arity as of `v0.1.1`, right side also replaced, unknown module:
2223/2224/2225/2226/2245, exit 151); `bind_value` (`tlx-eval/src/interp/cfg.rs`) binds values.
Repeated unqualified `CONSTANT` directives resolve with last-directive-wins precedence (`<-`
after `=`) via `Config::last_constant_subst` and `Config::last_constant_value`
(`tlx-front/src/cfg/mod.rs`). `Program::check_cfg_defs` (`tlx-sema/src/resolve/mod.rs`) checks
that INVARIANT/INIT/NEXT/SPECIFICATION/PROPERTY/CONSTRAINT/ACTION_CONSTRAINT name 0-ary operator
definitions after `last_constant_subst` resolution (2228/2230/2233, undefined: 2229,
SPECIFICATION together with INIT/NEXT: 2227); `load_model` (`tlx-cli/src/load.rs`) runs these
checks together with missing INIT/NEXT (2231/2232) and `Program::check_cfg_levels` in TLC's
order. With INIT but no NEXT (`model.no_next` in `tlx-cli/src/check.rs`), TLC computes the
initial states first and reports 2115 / exit 75 if there are any.

---

## 10. Where tlx implements it

| Topic | tlx location |
|---|---|
| Total order, equality, typed model values (§1.2, §2) | `tlx_value::order::{cmp_tlc, eq_tlc}` |
| Intern order (§1.3) | `tlx-value/src/intern.rs`; `intern_cfg`, `intern_sources` in `tlx-eval/src/interp/cfg.rs`; `Program::sany_file_orders`; startup constants: `Program::tlc_constant_defn_order`, `Interp::eval_constant_defns` |
| Lazy sets and enumeration order (§1.5) | `tlx-value/src/ops/` (`enumerate.rs`, `sets.rs`), `tlx-value/src/lazy.rs`, `tlx-eval/src/lazy.rs` |
| CHOOSE (§3) | `tlx-eval/src/eval.rs` |
| Integers (§4) | `tlx_value::arith`, `div_floor` flag in `Interp` |
| Action splitting, Init/Next enumeration (§5.1-5.3) | `Interp::split_actions`, `tlx-eval/src/enumerate.rs` |
| Counting, constraints, deadlock (§5.4) | `tlx-runtime/src/explore/worker.rs`, `tlx_runtime::admits` |
| SYMMETRY / VIEW representatives (§5.5, §6) | `tlx-eval/src/model/symmetry.rs`, `least_in_orbit` in `tlx-eval/src/model/mod.rs` |
| Fingerprints (§6) | `tlx-value/src/fingerprint.rs` |
| Standard modules (§7) | `tlx-sema/src/builtins.rs`, `tlx-eval/src/builtins.rs`, `natives.rs`, `bags.rs`, `natives/json.rs` |
| Random streams (§7) | `tlx-eval/src/random.rs` (`JavaRandom`) |
| Lazy evaluation (§8, item 11) | `Ctx::keep_lazy` in `tlx-eval/src/eval/context.rs`, `force_kept` in `tlx-eval/src/apply.rs`; `tlx-eval/src/lazy.rs` |
| cfg binding (§9) | `tlx-front/src/cfg/mod.rs`, `tlx-sema/src/resolve/mod.rs`, `tlx-eval/src/interp/cfg.rs`, `load_model` in `tlx-cli/src/load.rs`, `no_next` in `tlx-cli/src/check.rs` |
