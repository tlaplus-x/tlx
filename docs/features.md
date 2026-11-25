# Supported features

This document answers "what of TLC does tlx support?": command-line options, `.cfg` keywords,
standard modules, CommunityModules and Apalache modules. The reference is TLC 2026.10.02 (rev
1813307, `third_party/tla2tools.jar`, verified against the declared baseline pin in
`scripts/dependencies.py`; see [compat.md](compat.md)) and `third_party/community` (CommunityModules:
`.tla` files plus `modules.jar`). Coverage of the language itself (expressions, LET, INSTANCE,
temporal operators) is not listed here: see [design.md](design.md) and the differential tests
([testing.md](testing.md)). Differences in behavior and known limitations are in
[compat.md](compat.md); the options themselves are specified in [configuration.md](configuration.md).

## 0. Legend and method

### 0.1 Status legend

| Status | Meaning |
|---|---|
| native | tlx has a native implementation (the builtin table in `tlx-sema/src/builtins.rs` plus `tlx-eval`), the counterpart of a TLC Java override |
| definition | no native implementation; evaluated from the module's TLA+ definition, and tested to give TLC's results |
| slow | works from the TLA+ definition and gives correct results, but TLC has a Java override and tlx is noticeably slower on larger inputs (exponential or quadratic) |
| unsupported | tlx does not support it (evaluation reports "not supported", or the command line rejects it), or the definition cannot be evaluated (unbounded `CHOOSE`, quantification over infinite sets such as `Int`, `STRING`, `Seq(S)`) |
| partial | supported with known differences, see the remarks |
| n/a | TLC cannot use it either (or only in special settings such as the Toolbox); tlx behaves the same |

### 0.2 Method

- **Command line**: every option of `java -cp tla2tools.jar tlc2.TLC -help`, plus options in
  `tlc2/TLC.java` that the help does not list (`-generate`, `-lncheck`, `-modelcheck`,
  `-noGenerateSpecTEBin`/`-noTEBin`, `-help`), each tried against tlx (an unrecognized `-xxx` in
  `crates/tlx-cli/src/args.rs` prints the usage and exits with 2).
- **TLC's Java overrides**: for the standard modules, the `tlc2/module/*.class` files of
  `tla2tools.jar` (compared with the TLC sources); for CommunityModules, the `@TLAPlusOperator` /
  `@Evaluation` annotations of `tlc2.overrides.*` in `modules.jar` (70 overrides) read by reflection.
- **Tested operators**: each operator was written as a small spec (`ASSUME PrintT(<<"RESULT", expr>>)`,
  or a spec with variables when state is needed) and run with TLC (`-DTLA-Library=community:apalache`,
  `modules.jar` on the classpath) and with `tlx check -I third_party/community -I third_party/apalache`
  (interpreter), and the outputs were compared. Operators that differ, or that TLC itself does not
  support, are described in the remark column.
- **Usage in the corpus**: module `EXTENDS`/`INSTANCE` counts and cfg keywords in
  `third_party/Examples` (424 `.tla` and 235 `.cfg` files) indicate how common something is (operator
  names are not unique, so the counts are indicative).

---

## 1. TLC command-line options

tlx usage: `tlx check Spec.tla [-config X.cfg] [-workers N|auto] [-deadlock] [-I dir]... [-progress] [-tool] [-nowarning] [-compile|-interp] [-tlc] [-optimize] [-proofdir DIR] [-noautosymmetry] [-checksymmetry [-suggest]] [-symmetrystates N] [-symmetrydepth D] [-symmetryperms N] [-symmetryedges N] [-maxmem X] [-spill auto|off|always] [-metadir DIR] [-maxdisk X] [-checkpoint MIN] [-recover DIR] [-fpmem X] [-fpbits N] [-simulate|-generate [num=N]] [-depth N] [-seed N] [-dump [dot[,actionlabels][,colorize]] file] [-dumpTrace json|tla file]... [-coverage N] [-stats [json[=FILE]]]` (`-h`/`-help`/`--help` print the full help). An unrecognized option prints the usage and exits with 2.

Each row is the support matrix: what TLC's option means, and whether (and how far) tlx accepts it. An
option's spelling, default and effect are specified once in [configuration.md](configuration.md); the
behavior behind them is in [usage.md](usage.md), [scale.md](scale.md) and [design.md](design.md).

| Option | TLC meaning | tlx | Remarks |
|---|---|---|---|
| `SPEC` (positional) | root module (`.tla` may be omitted) | supported | as TLC; `.tla` is appended when the extension is missing |
| `-config file` | cfg file, default `SPEC.cfg` | supported | as TLC; the resolution of a relative or extension-less name is in [configuration.md](configuration.md) |
| `-workers num\|auto` | number of worker threads | supported | depth and counterexample length equal TLC's single-worker run; the parallel BFS is in [usage.md](usage.md) section 6 |
| `-deadlock` | **disables** deadlock checking | supported | as TLC (overrides the cfg's CHECK_DEADLOCK) |
| `-simulate [num=N,file=X]` | random simulation | partial | `num=N` works; any other comma-separated `key=value` (`file=X` writes each behavior as a trace module in TLC) is rejected before the run with exit 2 (`unsupported -simulate parameter`, `tlx supports num=N`) |
| `-generate` (hidden) | simulation plus random choices inside actions | supported | |
| `-depth num` | maximum simulation depth (default 100, -1 unbounded) | supported | |
| `-seed num` | random seed (simulation, and `RandomElement`/Randomization) | supported | also seeds `RandomElement`/Randomization without `-simulate` (choices in constants and initial states equal TLC's, compat.md D-4); behavior choices in simulation use tlx's own generator and cannot reproduce TLC's behaviors one by one (D-2) |
| `-aril num` | adjust the simulation seed | unsupported | `TLCGet("config").aril` is fixed to `"0"` |
| `-dump [dot[,colorize,actionlabels,constrained]] file` | export states / state graph | partial | byte-for-byte identical with TLC apart from fingerprints; `constrained` (include states excluded by constraints) is silently ignored |
| `-tool` | tool output with message numbers | supported | |
| `-nowarning` | disable warnings | supported | |
| `-fpmem num` | fingerprint set memory: (0,1) a fraction of physical memory, >= 1 MiB (deprecated) | supported | both forms accepted; a fixed table that fills up is a capacity error with exit code 255; the growing table and the disk tier are in [scale.md](scale.md) sections 4.1 and 4.2 |
| `-continue` | continue after an invariant violation, report all violations | unsupported | commonly used to find several counterexamples at once |
| `-coverage minutes` | periodic action/expression coverage | partial | action level (`distinct:generated`, as TLC, same on all execution tiers, [usage.md](usage.md) section 9.3); expression-level counts and variable, invariant and constraint lines are not produced (compat.md D-12). `TLX_COVERAGE` is a compiled-tier diagnostic (a different thing) |
| `-dumpTrace tla\|json file` | export the counterexample as TLA+ / JSON on violation | supported | `json` and `tla`; liveness counterexamples (lassos) are written too; byte-for-byte TLC's format (the lasso is the one tlx chose, tier 3; `crates/tlx-cli/tests/dump_trace.rs`) |
| `-generateSpecTE` (default on) / `-noGenerateSpecTE` / `-noTE` | generate a trace exploration spec (`SpecTE.tla`/`*_TTrace_*.tla`) on violation | unsupported | tlx never generates a TE spec (always as `-noGenerateSpecTE`); `-noGenerateSpecTE` is accepted and ignored, `-noTE` is rejected |
| `-noGenerateSpecTEBin` / `-noTEBin` (hidden) | do not write the binary trace | unsupported | rejected |
| `-teSpecOutDir dir` | output directory of the TE spec | unsupported | as above |
| `-loadTrace tlc\|json file` | check against an existing trace | unsupported | |
| `-checkpoint minutes` | periodic checkpoint (default 30) | supported | writes into the metadir at BFS level boundaries ([scale.md](scale.md) section 9.2); kept when the run is killed or interrupted, deleted on a normal end |
| `-recover DIR` | recover from a checkpoint | supported | same tlx binary, spec, cfg and execution tier; verdict, counts, depth and counterexample length equal those of an uninterrupted run ([usage.md](usage.md) section 8) |
| `-metadir path` | metadata directory (states/) | supported | directory of the spill files and the checkpoint ([scale.md](scale.md) section 10) |
| `-cleanup` | clean the states directory | partial | accepted and ignored: tlx removes its metadir at the end of the run |
| `-gzip` | compress disk streams | unsupported | rejected |
| `-fp N` | choose the N-th irreducible polynomial | unsupported | rejected; tlx's fingerprint does not use FP64 polynomials (the start-up line prints `fp 0`) |
| `-fpbits num` | MultiFPSet shard bits | supported | 2^N shards by high bits ([scale.md](scale.md) section 4.1) |
| `-maxSetSize num` | upper bound for enumerable sets (default 10^6) | unsupported | tlx has no such bound (where TLC reports "too many elements", tlx keeps computing or times out) |
| `-inv expr` | add an invariant expression on the command line | unsupported | |
| `-invlevel n` | same as invariant `TLCGet("level") < n` | unsupported | |
| `-postCondition mod!oper` | POSTCONDITION on the command line | unsupported | |
| `-difftrace` | print only the changed variables in traces | unsupported | |
| `-terse` | `Print` does not expand values | unsupported | |
| `-view` | apply VIEW when printing states | unsupported | |
| `-userFile file` | write user output (`Print`) to a file | unsupported | |
| `-lncheck default\|final\|seqfinal` (hidden) | when liveness is checked | unsupported | tlx checks only after the search ends (about `final`) |
| `-dfid num` | iterative-deepening depth-first search | unsupported | |
| `-modelcheck` (hidden) | explicitly select BFS (no-op) | unsupported | rejected (BFS is the only mode) |
| `-debug` | debug output | unsupported | rejected |
| `-debugger [nosuspend,nohalt,port=N]` | DAP debugger (VS Code) | unsupported | no plans |
| `-messagesAsErrors codes` | treat the given messages as errors | unsupported | |
| `-suppressMessages codes` | suppress the given messages | unsupported | |
| `-h` / `-help` / `--help` | help | supported | prints the full option help to stdout, exit code 0 |
| Java `-DTLA-Library=...` | module search path | supported | tlx: `-I dir` (repeatable) or `TLX_PATH`; `TLX_CLASSPATH` corresponds to TLC's classpath (searched after the built-in modules) |
| Java `-Dtlc2.tool.impl.Tool.cdot=true` | enable the action composition `\cdot` | supported | always enabled in tlx (`TLCGet("-Dtlc2.tool.impl.Tool.cdot") = "true"`) |
| Java `-Dtlc2.TLC.stopAfter=sec` | stop after the given number of seconds | unsupported | occasionally used by benchmarks and CI |
| Java `-Dtlc2.tool.fp.FPSet.impl=...` etc. | choose fingerprint set / queue implementation | n/a | tlx has only one implementation |

tlx-only: `-I dir`, `-progress` (progress every 10 s), `-compile` (the default tier), `-interp`, `-tlc`, `-optimize`,
`-proofdir`, `-noautosymmetry`, `-checksymmetry` (`-suggest`), `-maxmem`, `-spill`, `-maxdisk`, `-stats`, the `TLX_*`
environment variables (inventory in [configuration.md](configuration.md)).

---

## 2. The cfg file

Keyword frequency in the 235 `.cfg` files of the corpus (number of files; singular and plural forms
counted separately, a file may use both): SPECIFICATION 204, CONSTANTS 144 / CONSTANT 80,
INVARIANT 122 / INVARIANTS 86, `<-` 88, CHECK_DEADLOCK 58, PROPERTY 52 / PROPERTIES 45, CONSTRAINT 23 /
CONSTRAINTS 5, INIT/NEXT 19, SYMMETRY 16, ALIAS 10, VIEW 6, `<- [M]` 5, `= [M]` 3,
ACTION_CONSTRAINT 2, POSTCONDITION 2.

| Feature | tlx | Remarks |
|---|---|---|
| `CONSTANT(S) c = v` (integers, strings, TRUE/FALSE, sets) | supported | extensions: negative integers, tuples (TLC does not accept them) |
| model value `p = p`, model value sets `{p1, p2}` | supported | interning order as SANY |
| typed model values (`A_p`) and the error when compared with non-model values | supported | error messages tested to agree |
| `c <- Def` (constant / operator replacement, including parameterized operator constants `F(_) <- Def`) | supported | either side may be an operator symbol (`++ <- PlusPlus`, `Plus <- +`, `\o <- +`) |
| `c <- [M] Def`, `c = [M] v` (replace definitions in instantiated modules) | supported | corpus MCPaxos, MCLeastCircularSubstring, MCNano pass |
| `F(args) = v` (define an operator constant pointwise) | supported | as TLC's OpRcdValue: F applied to other arguments is an error |
| `INIT` / `NEXT` | supported | |
| `SPECIFICATION` (including WF/SF fairness) | supported | split into Init, `[][Next]_v` and fairness through LET, operators applied to arguments and parameterized instances, as TLC; a conjunct naming a constant FALSE definition is an error |
| `INVARIANT(S)` | supported | a non-state predicate exits with 76, as TLC |
| `PROPERTY` / `PROPERTIES`: state-level / action-level `[][A]_v` / temporal (`<>`, `[]<>`, `~>`) | supported | liveness with tableau and SCC; TLC's warnings for state-level formulas are reproduced; split as TLC's SpecProcessor (through LET, operators applied to arguments, bounded `\A`), the parts checked during the search named as TLC names them (innermost definition, `Inv` of `[]Inv`, or the location of a conjunct) |
| `CONSTRAINT(S)` | supported | counting semantics as TLC |
| `ACTION_CONSTRAINT(S)` | supported | |
| `SYMMETRY` | supported | native permutations; the same warning as TLC when used with liveness. Without a declaration, tlx screens sets of model values the cfg binds to constants: under `-tlc` it suggests the declaration; in the default mode it applies a disjoint product of full groups to safety-only runs when a connected Lean certificate is generated ([usage.md](usage.md) sections 6.2, 6.3; `-noautosymmetry` turns it off) |
| `VIEW` | supported | VIEW with liveness reproduces TLC's algorithm; lasso counterexamples are only valid "modulo VIEW" (compat.md D-10; TLC's own are too) |
| `ALIAS` | partial | as TLC normally; when evaluating ALIAS fails TLC prints an `_ALIASEvalError = "..."` field and tlx silently falls back to printing the original state |
| `POSTCONDITION(S)` | partial | a list, checked in order (the first false one is reported); a constant-level one is an error, as in TLC; in BFS evaluated after normal completion and after `Deadlock` (not after invariant, action or temporal violations, where TLC also evaluates it for use with `CounterExample`), and in `-simulate`/`-generate` also evaluated after non-initial violations and errors |
| `CHECK_DEADLOCK TRUE/FALSE` | supported | |
| `_POSSIBLE` | supported | as TLC: each predicate must hold in some state (state level) or step (action level) of the model, tracked after the CONSTRAINTs (ACTION_CONSTRAINTs); checked after the search before the POSTCONDITIONs; the counts are in the named register `"s:_possible"` of each worker |
| `_PERIODIC`, `_RL_REWARD` (TLC internal) | partial | parsed and ignored |
| comments `\*`, `(* ... *)` (nestable) | supported | |
| repeated keywords (lists are concatenated) | supported | |
| string escapes | partial | tlx decodes `\"`, `\n` etc., TLC keeps the original text (rarely matters) |
| integer range | partial | tlx parses i64, TLC rejects literals beyond i32 (during evaluation tlx's integers are 32-bit with overflow errors as TLC) |

---

## 3. Standard modules and TLC-specific modules

tlx ships (in `crates/tlx-sema/modules/stdlib`, taken from tla2tools.jar): Naturals, Integers, Reals, Sequences,
FiniteSets, Bags, TLC, TLCExt, Randomization, Json, Toolbox, RealTime and `_Possible`. The column "TLC native"
says whether TLC has a Java override (`tlc2/module/*`).

### 3.1 Naturals / Integers / Reals / RealTime

| Operator | TLC native | tlx | Remarks |
|---|---|---|---|
| `+ - * ^ < > <= >= \div % ..`, `Nat` | yes | native | 32-bit overflow errors (`+ * ^`), `% 0`, `\div 0` and `0^0` give TLC's messages (tested); a failing ASSUME exits with 10 as in TLC |
| `-.` (unary minus), `Int` | yes | native | `\div`/`%` agree on negative numbers |
| `Real` | no | n/a | evaluated from the placeholder definition `Real == "Reals"` as TLC: `1 \in Real` is an error in both (tested); real literals are rejected at start-up |
| `/`, `Infinity` | no | n/a | evaluated from the placeholder definition; both report an error (a `CHOOSE` over a non-enumerable range / unbounded CHOOSE; tested); no plans |
| RealTime: `RTBound`, `RTnow`, `now` | no | n/a | depend on real numbers; neither TLC nor tlx can check them (SANY-level checks also reject the typical use of `RTnow`); no plans |

### 3.2 Sequences / FiniteSets

| Operator | TLC native | tlx | Remarks |
|---|---|---|---|
| `Seq`, `Len`, `\o`, `Append`, `Head`, `Tail`, `SubSeq`, `SelectSeq` | yes | native | `Len` and `\o` on strings agree; error messages agree |
| printing `{s \in Seq(S) : P}` | n/a | partial | TLC reports "cannot enumerate", tlx prints the lazy form `{x \in Seq({1}) : ...}` |
| `IsFiniteSet`, `Cardinality` | yes | native | `IsFiniteSet(Nat)` agrees (FALSE) |

### 3.3 Bags

TLC has Java overrides (`tlc2.module.Bags`) for 12 operators, all but `SubBag`; tlx implements the same 12 natively and evaluates `SubBag` from its definition.

| Operator | tlx | Remarks |
|---|---|---|
| `IsABag`, `BagToSet`, `SetToBag`, `BagIn`, `EmptyBag`, `(+)`, `(-)`, `BagUnion`, `\sqsubseteq`, `SubBag`, `BagOfAll`, `BagCardinality`, `CopiesIn` | native (`SubBag`: definition) | all tested to agree; the native code follows TLC's `Bags.java` (`tlx-eval/src/bags.rs`). `BagToSet([x \in {1} \|-> 2])` prints `{1}` in both (tested) |

### 3.4 TLC

| Operator | TLC native | tlx | Remarks |
|---|---|---|---|
| `Print`, `PrintT`, `Assert`, `JavaTime`, `:>`, `@@`, `Permutations`, `SortSeq`, `ToString`, `TLCEval` | yes | native | tested to agree |
| `RandomElement` | yes | native | reproduces TLC's `java.util.Random` stream: under the same `-seed` choices in constants and initial states equal TLC's; without `-seed` tlx uses 0 and TLC a random seed; choices made while expanding states differ because fingerprints differ (compat.md D-4) |
| `Any` (`x \in Any` is always true) | yes | native | TLC's `AnySet`: `v \in Any` is true for every value (number/string/set/record/function/model value), `S \subseteq Any` is true; but Any cannot be enumerated (`Cardinality(Any)`, `\A x \in Any`, enumerating `SUBSET Any` or `Any \cup {1}` are errors), comparing Any with anything outside `S \subseteq Any` (including `Any = Any`) is an error, `IsFiniteSet(Any)` is FALSE, it prints as `ANY`; `Any \cap {1}` / `Any \ {1}` are evaluated from the enumerable side. In the corpus all 10 occurrences are the English word in comments |
| `TLCSet(i, v)` / `TLCGet(i)` (integer registers) | yes | native | the error text when unset differs |
| `TLCSet("s:...", v)` / `TLCGet("s:...")` (named registers, `TLCGetSet.NAMED_REGISTER_PREFIX`) | yes | native | per worker like integer registers |
| `TLCGet("level"/"diameter"/"distinct"/"generated"/"queue"/"duration"/"stats"/"config"/"spec"/"action"/"revision")` | yes | native | `TLCGet("level")'` is the level of the next state, one more than the current one; `"revision".tag` is `"tlx"` (TLC: the git revision); `stats`/`spec` have the same keys but the printed order of set elements differs (these strings are interned on the Java side in TLC) |
| `TLCGet("all")` / `TLCGet("all:named")` (all registers) | yes | native | per integer / named register of worker 0, the tuple of every worker's value (`AbstractChecker.getAllValues` / `getAllNamedRegisterValues`) |
| `TLCSet("exit", TRUE)` | yes | supported | counts agree |
| `TLCSet("pause", ...)` | yes | partial | ignored (TLC pauses and waits for input) |
| `TLCSet("coverage", ...)`, `TLCGet("coverage")` and other keys | yes | unsupported | reports an unsupported register |

### 3.5 TLCExt

TLC has Java overrides for 12 of its operators (all but `AssertEq` and `TLCGetAndSet`); tlx's Java-only operators report an explicit error, the others are evaluated from their TLA+ definition or natively.

| Operator | tlx | Remarks |
|---|---|---|
| `AssertEq(a, b)` | definition | prints and is FALSE when unequal, as TLC |
| `AssertError(err, exp)` | native | (`TLCExt.assertError`) TRUE iff evaluating `exp` fails with the message `err` (a string literal); the messages the CommunityModules tests compare are TLC's, a message TLC ends with the location of the failing expression matches with it; an error inside the Java overrides `IsFiniteSet`, `Cardinality` and `ToString` carries TLC's wrapper ("Attempted to apply the operator overridden by the Java method ..."), as without `-tool` (TLC's texts carry the `-tool` markers otherwise) |
| `TLCGetOrDefault(key, d)` | native | (`TLCExt.tlcGetOrDefault`) the value of an integer or `"s:..."` register; `d` when unset or for other keys |
| `TLCGetAndSet(key, Op, v, d)` | definition | evaluated from the TLA+ definition through `TLCGetOrDefault` (TLC has no override either) |
| `Trace` | native | (`TLCExt.getTrace`) the sequence of records of the variables from an initial state to the current one: in the next-state relation and action properties the path to the state expanded, in invariants, constraints and the ALIAS of a counterexample the path to the state checked or shown (BFS: the path the search found; in simulation the current behavior, each record with the field `_action`). The search keeps the paths only when the spec uses `Trace`. In a CONSTRAINT TLC's path lacks the predecessor's (compat.md D-24) |
| `CounterExample` | unsupported | Java-only: placeholder `TRUE`; in TLC the `[state: ..., action: ...]` graph inside POSTCONDITION |
| `ToTrace(CE)` | unsupported | Java-only: placeholder `TRUE` |
| `TLCModelValue(str)` | supported | implemented natively (`tlx-eval/src/builtins.rs`, `TLCExt.tlcModelValue`): the model value named by `str` (including typed `T_...` prefixes; the `.tla` definition is an unbounded `CHOOSE`) |
| `TLCDefer(e)` | supported | defined as `TRUE`; its argument is passed by name, so `TLCDefer(Assert(FALSE, ...))` is TRUE as in TLC |
| `TLCNoOp(v)` | definition | |
| `PickSuccessor(e)` | partial | agrees when `e` is true; when `e` is false TLC chooses a successor interactively (no plans) |
| `TLCCache(e, closure)` | native | as TLCExt.java `tlcEval2`: a constant-level `e` is evaluated once per closure value (observable through side effects such as TLCSet); other expressions are evaluated each time |
| `TLCFP(v)` | supported | implemented natively (`tlx-eval/src/builtins.rs`, `TLCExt.tlcFingerprint`): 32-bit signed integer from tlx's fingerprint of `v` (differs from TLC's FP64, compat.md D-5; equal values have equal results; the `.tla` definition is `CHOOSE i \in Int : TRUE`) |
| `TLCEvalDefinition(name)` | unsupported | Java-only: placeholder `TRUE` |

### 3.6 Randomization

| Operator | TLC native | tlx | Remarks |
|---|---|---|---|
| `RandomSubset(k, S)` | yes | native | returns S when `k > \|S\|`, as TLC |
| `RandomSetOfSubsets(k, n, S)` | yes | native | |
| `TestRandomSetOfSubsets(k, n, S)` | no | definition | |

### 3.7 Json (shipped with tla2tools; all 7 operators are Java overrides in TLC, all native in tlx)

| Operator | tlx | Remarks |
|---|---|---|
| `ToJson(v)` | native | `Json.java getNode`: sequence to array, record / non-1..n function to object, set to array in canonical order, model value to string, scalars as they are; Gson escaping (no HTML escaping). Test `tests/specs/PH1.tla` |
| `ToJsonArray(v)` | native | as above (`getArrayNode`: sequence/set to array, a function that is not a sequence to object) |
| `ToJsonObject(v)` | native | as above (`getObjectNode`: record to object, sequence to an object with keys `"0"`, `"1"`, ...) |
| `JsonSerialize(file, v)`, `ndJsonSerialize(file, v)` | native | `Json.java serialize`/`ndSerialize`: `v` must be a sequence or record (`ndJson*`: a sequence); the file holds `ToJson(v)` (no trailing newline) / one line `ToJson(v[i])\n` per element; overwrites, creates parent directories. Byte-for-byte as TLC (apart from field order, compat.md D-11). Test `tests/specs/SJ2.tla` |
| `JsonDeserialize(file)`, `ndJsonDeserialize(file)` | native | `Json.java getValue`: array to sequence, object to record (a repeated key keeps the last value), number via Gson `getAsInt` (`3.7` to 3, `1e3` to 1000, beyond 32 bits truncated with wrap-around), `null` is an error; ndjson skips empty lines (`\n`, `\r\n` and `\r` end a line). Gson's lenient syntax (comments, single quotes, ...) is not supported |

(CommunityModules contains another `Json.tla` that differs from the standard one only in comments; with the built-in modules the standard version comes first, and a copy in a directory given with `-I` takes precedence, which is TLC's order too.)

### 3.8 Toolbox and TLC-internal modules

| Module / operator | tlx | Remarks |
|---|---|---|
| Toolbox: `_TETrace`, `_TEPosition` | n/a | only meaningful in Toolbox-generated trace exploration specs (an unbounded CHOOSE in ordinary TLC runs too); used in ALIAS TLC prints `_ALIASEvalError`, tlx silently prints the original state (section 2, ALIAS) |
| `_TLCTrace`, `_JsonTrace`, `_TLCActionTrace`, `_TLAPlusCounterExample`, `_DotTrace`, `_TLCTESpec`, `_TLCTracePlain` (TE spec internal modules) | unsupported | only used with `-loadTrace` / TE specs; tlx does not provide them |
| `_Possible` (the `_POSSIBLE` configuration) | partial | the module is provided and its operators are evaluated from the TLA+ source; the `_POSSIBLE` cfg keyword is implemented natively (section 2) |
| `AnySet` (`ANY`), `TransitiveClosure` (`Warshall`), `Strings` (`STRING`) | supported / unsupported / supported | TLC has only Java classes, no `.tla`; `ANY` see the table above, `STRING` is a tlx builtin, `TransitiveClosure` is not used in the corpus |

---

## 4. CommunityModules

`third_party/community` has 22 non-theorem modules (including the Json copy that has the same name as the standard one). `modules.jar` has 17 classes in `tlc2.overrides` with 70 overrides (66 `@TLAPlusOperator` and 4 `@Evaluation`: `IOUtils!Serialize`, `IOUtils!Deserialize`, `SequencesExt!ReplaceAllSubSeqs`/`ReplaceFirstSubSeq`). tlx overrides operators natively by module name for 13 modules only (`DyadicRationals!GCD` is LOCAL; the list `COMMUNITY_NATIVE_MODULES`: BagsExt, CSV, Combinatorics, DyadicRationals, FiniteSetsExt, Folds, Functions, Graphs, IOUtils, SequencesExt, Statistics, UndirectedGraphs, VectorClocks); Java overrides that tlx does not implement (IOUtils serialization, GraphViz, some SVG helpers, ...) report an explicit error (section 6.1).

Like TLC's jar, tlx ships the CommunityModules (`crates/tlx-sema/modules/community`, 34 `.tla` files, MIT license). Lookup order: spec directory, then `-I`/`TLX_PATH`, standard modules, CommunityModules, `TLX_CLASSPATH` (last, like TLC's classpath).

Corpus usage (EXTENDS/INSTANCE counts): IOUtils 11, Functions 10, SequencesExt 9, CSV 7, FiniteSetsExt 6, SVG 5, Json 4, UndirectedGraphs 3, Relation/Bitwise/DyadicRationals/BagsExt... 1-2.

Column "TLC" says whether `modules.jar` has a Java override. Statuses are as in the legend; all rows below were tested against TLC unless the remark says otherwise.

### 4.1 SequencesExt (EXTENDS Sequences, Naturals, FiniteSets, FiniteSetsExt, Folds, Functions, Bags, TLC)

| Operator | TLC | tlx | Remarks |
|---|---|---|---|
| `ToSet`, `ToBag` | | definition | |
| `SetToSeq` | yes | native | follows TLC's override (`SequencesExt.java`): the set is arranged into a sequence in TLC's normalized (sorted) order; the definition is `CHOOSE f \in [1..n -> S]` (n^n), which overflows |
| `SetToSeqs` | yes | native | follows TLC's override: all permutations (n! sequences; `{}` gives `{<<>>}`) |
| `SetToSortSeq` | | definition | `SortSeq` on the native SetToSeq |
| `SetToAllKPermutations` | | slow | based on SetToSeqs |
| `TupleOf`, `SeqOf`, `BoundedSeq` | | definition | |
| `Contains` | yes | definition | |
| `IsSorted` | | definition | |
| `Reverse`, `Remove`, `ReplaceAll` | | definition | |
| `SelectInSeq` | yes | definition | |
| `SelectInSubSeq` | yes | native | follows TLC's override: returns the index in the **original** sequence (`SelectInSubSeq(<<1,2,3,4>>, 2, 3, LAMBDA x: x > 2)` = 3); 0 when from > to or nothing matches |
| `SelectLastInSeq` | yes | definition | |
| `SelectLastInSubSeq` | yes | native | like SelectInSubSeq, the last match as an index in the original sequence: `(<<1,2,3,4>>, 2, 4, LAMBDA x: x < 4)` = 3 |
| `InsertAt`, `ReplaceAt`, `RemoveAt` | | definition | |
| `RemoveFirst`, `RemoveFirstMatch` | yes | definition | |
| `Cons`, `Snoc`, `Front`, `Last` | | definition | |
| `IsPrefix` | yes | definition | |
| `IsStrictPrefix`, `IsSuffix`, `IsStrictSuffix`, `Prefixes`, `CommonPrefixes` | | definition | |
| `LongestCommonPrefix` | yes | definition | |
| `Suffixes` | yes | definition | |
| `SeqMod` | | definition | |
| `FoldSeq`, `FoldLeft`, `FoldRight`, `FoldLeftDomain`, `FoldRightDomain` | yes | native | evaluated natively like TLC's override (same order as Java): FoldSeq over 1..50000 takes 0.1 s |
| `FlattenSeq`, `Zip`, `Interleave`, `SubSeqs` | | definition | |
| `AllSubSeqs` | yes | native | every subsequence in index order (the definition folds through FoldFunction and its order is decided by CHOOSE, which only the Java override guarantees); returns a normalized set; test `tests/specs/PH2.tla` |
| `IndexFirstSubSeq`, `ReplaceSubSeqAt` | | definition | |
| `ReplaceFirstSubSeq` | yes (Eval) | definition | agrees on sequences and strings |
| `ReplaceAllSubSeqs` | yes (Eval) | native | follows TLC's override for three strings (`StringUtils.replace`: the leftmost non-overlapping occurrences, the replacement not rescanned; an empty `s` interleaves `r` before every character, scalar-safe where TLC splits a surrogate pair, D-33) and the module definition for other values: its ordered guards (`s = t -> r`, `r = s -> t`, an empty `s` interleaving `r` before every element), the membership test comparing every window of `t` (so its comparison errors are observable), and the leftmost partition with the maximum number of matches (the definition's chunk-index tie-break can pick a later overlapping occurrence in TLC, D-34); tests `tests/specs/PH4.tla`, `PH6.tla` |

### 4.2 FiniteSetsExt (EXTENDS Integers, FiniteSets, Folds, Functions)

| Operator | TLC | tlx | Remarks |
|---|---|---|---|
| `FoldSet` | yes | native | evaluated natively like `FiniteSetsExt.foldSet` (normalized order, `acc = op(x, acc)`): 1..50000 takes 0.1 s (TLC: instant) |
| `SumSet`, `ProductSet`, `ReduceSet`, `MapThenSumSet` | | definition | on the native FoldSet; `MapThenSumSet` takes the linear fast path of MapThenFoldSet |
| `FlattenSet`, `SymDiff` | | definition | |
| `Quantify` | yes | definition | 1..100000 takes 0.1 s |
| `kSubset` | yes | native | a lazy set like TLC's `KSubsetValue`: membership, cardinality (binomial), emptiness and comparisons without enumeration (`{1, 2} \in kSubset(2, 1..64)`, `kSubset(0, Nat) = {{}}`), elements in normalized order, printed as the definition from 64 elements on |
| `Max`, `Min` | no | native | the error on an empty set agrees. 16/14 uses in the corpus |
| `Choices`, `ChooseUnique` | | definition | |

### 4.3 Functions (EXTENDS Integers, Folds)

| Operator | TLC | tlx | Remarks |
|---|---|---|---|
| `Restrict`, `RestrictDomain`, `RestrictValues`, `IsRestriction`, `Range`, `Pointwise`, `Inverse` | | definition | `Range`: 17 uses in the corpus |
| `AntiFunction` | yes | definition | |
| `IsInjective` | yes | native | (`Functions.IsInjective`) pairwise equality of the values, quadratic; like TLC also for a set of records `[a : S, b : T]` (its field sets) |
| `Injection`, `Surjection`, `Bijection`, `ExistsInjection`, `ExistsSurjection`, `ExistsBijection` | | definition | an enumeration of `[S -> T]` by itself, equally exponential in TLC |
| `FoldFunction`, `FoldFunctionOnSet` | yes | native | native (DOMAIN in normalized order): 1..50000 takes 0.1 s |
| `SumFunctionOnSet`, `SumFunction` | | definition | on the native FoldFunction(OnSet) |

### 4.4 Folds

| Operator | TLC | tlx | Remarks |
|---|---|---|---|
| `MapThenFoldSet` | no | native | TLC has no override and evaluates the recursive definition (1..20000 overflows TLC's stack). tlx takes the elements one by one with `choose`; when `choose` is `LAMBDA s : CHOOSE x \in s : TRUE` (the way MapThenSumSet and friends write it) it takes them directly in normalized order, linearly (1..50000: 9.1 s to 0.09 s; regression SJ1) |

### 4.5 Relation (EXTENDS Naturals, FiniteSets; TLC has no override)

| Operator | tlx | Remarks |
|---|---|---|
| `IsReflexive`, `IsIrreflexive`, `IsSymmetric`, `IsAntiSymmetric`, `IsAsymmetric`, `IsTransitive`, `IsStrictlyPartiallyOrdered`, `IsPartiallyOrdered`, `IsStrictlyTotallyOrdered`, `IsTotallyOrdered` | definition | |
| the 10 corresponding `...Under(op, S)` | definition | 3 spot-checked |
| `TransitiveClosure`, `ReflexiveTransitiveClosure`, `IsConnected` | definition | the same definition as TLC; tlx memoizes recursive function definitions in LET (section 6.3): 10 elements take < 0.1 s (TLC: 7 elements take 15 s). Regression spec SM1. 3 uses in the corpus |

### 4.6 Graphs (EXTENDS Naturals, Sequences, FiniteSets, SequencesExt, Relation)

| Operator | TLC | tlx | Remarks |
|---|---|---|---|
| `IsDirectedGraph`, `DirectedSubgraph`, `Transpose`, `IsUndirectedGraph`, `UndirectedSubgraph` | | definition | |
| `Path` | | n/a | a set over `Seq(G.node)`: membership works (tlx agrees with TLC), enumeration does not in either |
| `SimplePath` | yes | native | `AbstractGraphs.java simplePath`: DFS from every node collecting all non-empty paths with distinct nodes; edges of the wrong shape (not pairs) or with endpoints that are not nodes are ignored (`AreConnectedIn` and `IsStronglyConnected` follow the same rule). Test `tests/specs/SJ4.tla` |
| `AreConnectedIn`, `IsStronglyConnected` | yes | native | |
| `ConnectionsIn`, `IsTreeWithRoot`, `GraphUnion`, `IsBipartiteWithPartitions`, `HasCycle`, `IsDag` | | definition | `IsDag` with 8 nodes takes 0.2 s |
| `Successors`, `AllSuccessors`, `Predecessors`, `AllPredecessors`, `InDegree`, `OutDegree`, `Roots`, `Leaves`, `EmptyGraph`, `Graphs` | | definition | |
| `Ancestors`, `Descendants` | | definition | on Relation!TransitiveClosure (see above) |

### 4.7 UndirectedGraphs

| Operator | TLC | tlx | Remarks |
|---|---|---|---|
| `IsUndirectedGraph`, `IsLoopFreeUndirectedGraph`, `UndirectedSubgraph`, `UndirectedGraphs` | | definition | |
| `Path` | | n/a | as in Graphs |
| `SimplePath` | yes | native | as Graphs; an edge is a set of one or two nodes, `{a}` is a self-loop |
| `AreConnectedIn`, `ConnectedComponents` | yes | native | |
| `IsStronglyConnected` | no | native | native in tlx in addition |

### 4.8 IOUtils

| Operator | TLC | tlx | Remarks |
|---|---|---|---|
| `IOExec(cmd)` | yes | native | |
| `IOEnvExec(env, cmd)` | yes | native | the fields of `env` (values via `toUnquotedString`) are added to the inherited environment; the elements of `cmd` must be strings (as for `IOExec`; others are errors). Test SJ3 |
| `IOExecTemplate(tmpl, params)` | yes | native | `String.format(elem, params...)` for every element of `tmpl`; `params` must be strings (`%d` is an error, as in Java). 2 uses in the corpus |
| `IOEnvExecTemplate(env, tmpl, params)` | yes | native | the combination of the two |
| `IOEnv` | yes | native | 6 uses in the corpus |
| `atoi(str)` | yes | native | Java's `Integer.parseInt` (`"-0"`, `"+7"`, `"007"` parse; outside 32 bits an argument error), as TLC's override |
| `zeroPadN(n, w)` | | definition | |
| `IOSerialize(v, file, compress)` | yes | unsupported | Java-only (writes a file in Java's serialization format); a call reports an explicit error; differs from TLC |
| `IODeserialize(file, compressed)` | yes | unsupported | Java-only (reads a file; the definition is an unbounded CHOOSE); differs from TLC |
| `Serialize(v, dest, opts)` (TXT/JSON etc.) | yes (Eval) | unsupported | Java-only (placeholder definition `CHOOSE r \in [exitValue: Int, ...]`); a call reports an explicit error; SVGSerialize depends on it |
| `Deserialize(src, opts)` | yes (Eval) | unsupported | Java-only (the placeholder definition is an unbounded CHOOSE); a call reports an explicit error (1 use in the corpus) |

### 4.9 CSV

| Operator | TLC | tlx | Remarks |
|---|---|---|---|
| `CSVWrite(tmpl, val, file)` | yes | native | 6 uses in the corpus. The arguments of `String.format` are the printed strings of the values: `%s`/`%S`, `%n$s`, width and `-` are supported; `%d` is an error (as in Java) |
| `CSVRecords(file)` | yes | native | |
| `CSVWriteRecord(rec, delim, headers, file)` | yes | native | `CSV.java writeRecord`: fields in the record's normalized order; when `headers` is true a line of field names is appended first, then the line of values (in TLC's printed form, strings quoted), joined by `delim` |
| `CSVRead(columns, delim, file)` | yes | native | `CSV.java read`: every line is split by `delim` (a Java regex; tlx supports only a literal delimiter and escaped single characters such as `\\|`, other regexes are errors; trailing empty fields are dropped) into a string record `[columns[i] \|-> i-th part]`; fewer fields than columns is an error (array index out of bounds in TLC); a missing file gives `<<>>` |

### 4.10 Other modules

| Module | Operators | TLC | tlx | Remarks |
|---|---|---|---|---|
| Bitwise | `&`, `\|`, `^^`, `Not`, `shiftR` | yes (5) | definition | recursive definitions; 30-bit numbers are fast |
| Combinatorics | `factorial` | yes | definition | 13! overflows in both |
| | `choose(n, k)` | yes | native | follows `Combinatorics.java` (`tlc2.util.Combinatorics.choose`): the binomial coefficient without the definition's intermediate `factorial` overflow (`choose(20, 10)` = 184756), 0 for `k > n`, computed exactly through `min(k, n-k)` with the 32-bit overflow error instead of a value (`choose(34, 17)`); TLC's spurious values beyond 32 bits are not copied (D-32); test `tests/specs/PH4.tla`, `PH5.tla` |
| DyadicRationals | `IsDyadicRational`, `Zero`, `One`, `Add`, `Half`, `PrettyPrint` | Reduce (LOCAL) | definition (GCD native: follows the commons-math gcd used by TLC's Java `Reduce` - absolute values, gcd(0,0)=0, a result of 2^31 is an error - rather than the TLA+ definition) | |
| BagsExt | `BagAdd`, `BagRemove`, `BagRemoveAll`, `SumBag`, `ProductBag` | | definition | |
| | `FoldBag` | yes | native | follows `BagsExt.java` |
| VectorClocks | `IsCausalOrder` | | definition | |
| | `CausalOrder(log, clock, node, domain)` | yes | native | (`VectorClocks.causalOrder`) TLC's topological sort of the log (thousands of lines in milliseconds; the TLA+ definition is a `CHOOSE` over all permutations); concurrent lines in the order TLC gives under `-fp 0` (compat.md D-25) |
| Statistics | `ChiSquare(expected, actual, alpha)` | yes | native | the definition is constant `TRUE`; follows `Statistics.java` and Apache Commons Math 3.6.1 (`ChiSquareTest`, `Gamma.regularizedGammaP/Q`, Lanczos `logGamma`, rescaling); FALSE when p < alpha. Test `tests/specs/PH3.tla` |
| GraphViz | `DotDiGraph(G, VL, EL)` | yes | unsupported | Java-only (definition `TRUE`; TLC returns a dot string) |
| SVG | `SVGElem`, `Line`, `Circle`, `Rect`, `Text`, `Image`, `Group`, `Svg`, `SVGDoc`, `PointOnLine` | PointOnLine yes | definition | definitions that construct records |
| | `SVGElemToString` | yes | unsupported | Java-only (definition `TRUE`; TLC returns SVG text) |
| | `NodeOfRingNetwork` | yes | unsupported | Java-only (the definition is always `[x \|-> 0, y \|-> 0]`) |
| | `NodesOfDirectedMultiGraph` | yes | unsupported | `CHOOSE f \in [nodes -> [x: Int, y: Int]]`; TLC uses the JUNG layout algorithm; no plans |
| | `SVGSerialize` | | unsupported | depends on IOUtils!Serialize (3 uses in the corpus) |
| HTML | `HTMLFill`, `HTMLDocument`, `HTMLText`, ... 25 in all | | definition | plain string concatenation (via SequencesExt!ReplaceFirstSubSeq / FoldLeft); 2 spot-checked |
| Quorum | `QuorumSystem` | | definition | |
| ShiViz | `Host`, `Clock` | | n/a | depend on Toolbox `_TETrace`, usable only in TE/ALIAS settings |
| DifferentialEquations | `Integrate` | | n/a | real numbers; TLC cannot evaluate it either |
| Json (community copy) | as section 3.7 | | as section 3.7 | shadowed by the standard library Json |

---

## 5. Apalache modules and Apalache idioms

`third_party/apalache`: Apalache.tla, Variants.tla, Option.tla (TLC also evaluates them from their TLA+ definitions; there are no Java overrides). Two files of the corpus EXTEND Apalache.

| Module | Operators | tlx | Remarks |
|---|---|---|---|
| Apalache | `:=` (in actions and Init) | definition | equals `=`, successor counts agree |
| | `Gen(n)` | definition | defined as `{}` (only meaningful to Apalache), as in TLC |
| | `Guess(S)`, `SetAsFun`, `MkSeq`, `FunAsSeq`, `Skolem`, `Expand`, `ConstCardinality`, `ApaFoldSet`, `ApaFoldSeqLeft`, `Repeat` | definition | |
| Variants | `Variant`, `VariantTag`, `VariantGetUnsafe`, `VariantGetOrElse`, `VariantFilter`, `UNIT` | definition | |
| Option | `Some`, `None`, `IsSome`, `IsNone`, `OptionCase`, `OptionMap`, `OptionFlatMap`, `OptionGetOrElse`, `OptionToSeq`, `OptionToSet`, `OptionGuess`, `OptionFunApp`, `OptionPartialFun` | definition | 10 spot-checked |
| Idioms | type annotation comments (`\* @type: Int;`, `@typeAlias:`, also between CONSTANT/VARIABLE declarations) | supported | plain comments |
| | the old `<:` type annotation | supported | a user-defined operator (`a <: b == a`), an ordinary definition |
| | `ConstInit` / `--cinit`, `--inv`, `--length` etc. Apalache command-line options and the `CInit` convention | n/a | belong to Apalache itself; for TLC users constants are assigned in the cfg |

The Apalache `.tla` files are not bundled with tlx; put them on `-I` or `TLX_CLASSPATH` ([usage.md](usage.md) section 11).

---

## 6. Cross-cutting notes

### 6.1 Placeholder definitions

In the TLC ecosystem many operators have `.tla` definitions that are mere placeholders (`TRUE`, `CHOOSE val : TRUE`) whose real implementation is in Java. tlx never silently returns the placeholder value for these:

- **Implemented natively** (11): `Json!ToJson`/`ToJsonArray`/`ToJsonObject` (`crates/tlx-eval/src/natives/json.rs`, reproducing Gson's output byte for byte), `SequencesExt!AllSubSeqs` (`crates/tlx-eval/src/natives.rs`), `SequencesExt!SelectInSubSeq`/`SelectLastInSubSeq` (`crates/tlx-eval/src/builtins.rs`), `Statistics!ChiSquare` (`crates/tlx-eval/src/natives/stats.rs`, reproducing Commons Math's p-value algorithm), `TLCExt!TLCModelValue`/`TLCFP` (`crates/tlx-eval/src/builtins.rs`), `TLCExt!Trace` (the path the search provides, `tlx_runtime::live::current_path`) and `VectorClocks!CausalOrder` (`crates/tlx-eval/src/builtins.rs`, TLC's topological sort with its `-fp 0` node order). Tests: `tests/specs/PH1.tla`, `PH2.tla`, `PH3.tla` (TLC is the oracle; PH3 includes the boundary p = alpha and the rescaling path).
- **Explicit error** (10 operators: `GraphViz!DotDiGraph`, `IOUtils!IOSerialize`/`IODeserialize`/`Serialize`/`Deserialize`, `SVG!SVGElemToString`/`NodeOfRingNetwork`, `TLCExt!CounterExample`/`ToTrace`/`TLCEvalDefinition`): the `(module, operator)` table is the `java_only` section of `tlx-sema/src/builtins.rs`; applying one reports `"<Module>!<Op> is implemented by TLC in Java and is not supported by tlx"`. The compiled tier falls back to the interpreter for these operators through `is_strict_value_op` (`tlx-compile/src/lower/expr.rs`). The CLI regression test `crates/tlx-cli/tests/java_only.rs` covers 5 operators on 3 tiers.

`ChiSquare`'s p-value uses the platform `exp`/`log` rather than `FastMath`, differing from Commons Math by at most one ulp; end to end, its verdicts agree with TLC on 2000+ random and boundary cases (the verdict only compares `p < alpha`).

Side effect: the corpus model `KnuthYao/SimKnuthYao` has `ChiSquare(..., "0.2")` as POSTCONDITION; because it now really computes, about half of the runs statistically reject and report an error (5 of 10 runs exit with 10; TLC failed 1 of 3 runs the same way). This is the model's randomness, not a regression: `tests/expected_failures.json` has a `flaky` entry (`result: "error"`) for it so that `scripts/verify.py` does not report it.

### 6.2 Output and diagnostic differences (minor)

- In BFS, POSTCONDITION is evaluated on normal completion and after `Deadlock`, not after an invariant, action or temporal violation is found (TLC evaluates it there too, and `CounterExample` only makes sense there; in `-simulate`/`-generate`, tlx also evaluates POSTCONDITION after non-initial violations and errors).
- When evaluating ALIAS fails, TLC prints an `_ALIASEvalError` field and tlx silently falls back to the original state.
- A function whose domain is `{1, ..., n}` is normalized to a tuple and `DOMAIN` prints as `1..n` (TLC prints `{1, 2}`); this affects trace text but not values.
- Strings TLC creates on the Java side (the keys of `TLCGet("stats")`, ...) are interned in a different order, so sets print in a different order.
- `ToString`/`Print`/`PrintT` expand lazy sets and functions as TLC's `toStringUnchecked` does, and an expansion that fails (`{x \in Seq(S) : P}`, `SUBSET FALSE`, `[Nat -> S]`, ...) is an error (`tlx_value::fmt::check_printable`); error messages and traces still print the lazy form (TLC's `toString` swallows these errors).

### 6.3 Recursive functions that return function values

```tla
trcl[n \in Nat] == [x, y \in S |-> IF n = 0 THEN R[x, y]
                                   ELSE \/ trcl[n-1][x, y]
                                        \/ \E z \in S : trcl[n-1][x, z] /\ trcl[n-1][z, y]]
```

This is the definition of `Relation!TransitiveClosure` and a common idiom in hand-written specs. TLC does not cache: `trcl` is a LazyValue in the LET, the recursive references bind to the same `FcnLambdaValue`, but every application re-evaluates the function body, so the cost grows exponentially with |S| (15 s for |S| = 7). tlx puts recursive function definitions in a LET into the LET cache (`let_cacheable`): recursive references get the same `RecursiveFcn`, which memoizes its results per argument, and function values built under `KeepLazy` (`LambdaFcn`) memoize per point, so the total cost is polynomial (|S| = 10 takes < 0.1 s, identical in the interpreter and `-compile`). Only definitions without side effects that do not read the next state are cached (the same condition as LET caching). Top-level recursive functions were already memoized.
