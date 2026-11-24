# Fuzzing regressions

`findings.jsonl`: minimized expressions found by `scripts/fuzz_expr.py` (replay with
`python3 scripts/fuzz_expr.py --replay tests/fuzz/findings.jsonl`).

`specs/`: minimized specs found by `scripts/fuzz_spec.py` (docs/testing.md section 7.1). Each
`NAME` has `NAME.tla`, `NAME.cfg` (and `NAME_lib.tla` if it instantiates one), `NAME.json` (the
finding: `bug`, where it was `found`, a `summary`) and `tlc/NAME.out` (TLC's output, written by
`fuzz_spec.py --record NAME`). `fuzz_spec.py --replay-only` runs every regression in the five modes
against the saved TLC output (verify.py suite `fuzz` does it too). An open bug is listed in
`tests/expected_failures.json` (suite `fuzz*`, id `replay/NAME/MODE`) and, if generated specs keep
hitting it, in the `KNOWN` list of `fuzz_spec.py` under its `bug` id; when it is fixed the replay
reports XPASS: remove both entries.

| Regression | Bug id | Modes failing | What |
|---|---|---|---|
| `FzConstInvFalse` | constant-level-false | all but w4 | a constant-level INVARIANT that is FALSE: TLC reports an error before the search, tlx a violation by the initial state |
| `FzConstConstrFalse` | constant-level-false | all | a constant-level CONSTRAINT that is FALSE: TLC reports an error, tlx succeeds with 0 distinct states |
| `FzConstView` | constant-view | all | a constant VIEW (`<<1>>`): TLC rejects it ("cannot be a constant"; it accepts numeral and string literals), tlx accepts it |
| `FzConstBoxProp` | box-property-name | all | `PROPERTY [](FALSE)`: TLC names the violated invariant by the formula (`FALSE`), tlx by the property name |
| `FzConstrNoInitDepth` | constraint-no-initial-depth | all | no initial state satisfies the CONSTRAINT: TLC reports depth 1, tlx 0 |
| `FzWorkersAPropFirst` | workers-action-property-first | w4 | under VIEW with several workers tlx reports the action property violated by a step before the invariant violated by its new successor; TLC reports the invariant |
| `FzViewAPropTrace` | view-trace | interp, compile, paranoid | under VIEW tlx's counterexample of an action property ends in a stuttering step (the first state of the successor's view class); TLC rejects it |
| `FzCupDupGenerated` | fixed | none | `x' \in (S \X T) \cup {x}` with x in `S \X T`: TLC and the interpreter enumerate the duplicate twice (3 generated), the compiled tier once (2) |
| `FzEmptyFcnExcept` | fixed | none | EXCEPT with a string key on the empty function `[x \in {} \|-> ""]`: fixed by `FcnWitness` in `Shape::Fcn` / `Shape::Map` (docs/compat.md D-13) |
| `FzConstInvErrorCounts` | init-eval-error | all but w4 | a constant-level INVARIANT fails to evaluate on the initial states: TLC's error counts 2 generated states, tlx's 1 |
| `FzLivePredErrorCounts` | init-eval-error | all but w4 | a liveness property's state predicate fails to evaluate: TLC reports it while computing the initial states, tlx after the search (counts differ) |
| `FzLivePredErrorStats` | init-eval-error | all but w4 | a liveness predicate fails on an initial state that violates an invariant: TLC reports the violation with statistics, tlx without |
| `FzViewInitInvTrace` | view-trace | all but w4 | under VIEW, of two initial states with the same view the second violates TypeOK: tlx's counterexample shows the first (which satisfies it), TLC the violating one |
| `FzEmptySetEqSeq` | fixed | none | `(<<{}>>)[1] = I!W` with the variable `<<>>` (read through an INSTANCE): TLC and the interpreter report an equality error between `{}` and `<<>>`, the compiled tier evaluates it |
| `FzEmptySetEqFcn` | fixed | none | `x # (0 :> 3)` with `x = {}`: an error in TLC and the interpreter, TRUE in the compiled tier |
| `FzConstTemporalError` | startup-eval-error | all | a constant subformula of a temporal property fails to evaluate: TLC reports it before the search, tlx succeeds (no initial state) |
| `FzLivePredErrorVerdict` | liveness-eval-error | all | a liveness predicate fails to evaluate while a step violates `[][FALSE]_vars`: TLC with one worker reports the action property, tlx the evaluation error (a verdict difference) |
| `FzIntFcnEq` | fixed | none | `0 # v1` with `v1 = (m2 :> -1)`: an equality error in TLC and the interpreter, TRUE in the compiled tier |
| `FzTlcActionTraceShort` | tlc-short-action-trace | all but w4 | TLC defect candidate: TLC's counterexample of the violated action property is the initial state alone (rebuilding the step fails on `Max({})` in the other IF branch); tlx prints both states |

`FzIterSubset` and `FzIterChoose` guard against hoisting iteration sources into value
positions. `FzFoldMinInt` and `FzMixedFunctionOrder` check compiled evaluation of the
minimum integer and mixed record/function set order.

`expr-open.jsonl` retains the documented TLC `IsInjective` record defect (compat.md D-26),
reported as informational by the expression driver. Fixed findings have moved to
`findings.jsonl`, including lazy selection of `Restrict`, the two iteration-source cases,
the minimum integer, and mixed-function `SetToSeq`.

Two findings came from re-embedding TLC's printed output: a record field identifier
introduced by the expected value changes SANY's string intern order, and the printed
minimum integer contains the out-of-range positive literal `2147483648`. The driver
now embeds records as string-keyed functions and the minimum integer as
`(-2147483647 - 1)`; `scripts/test_fuzz_spec.py` locks in both rules.

Expression and spec fuzzing share `contract.compare` for error-versus-success
verdicts. Error messages and exit codes are tier 3: different errors in the
same expression are not failures. The saved `Restrict` and integer-domain
field-selection cases exercise this rule; normal values must still agree.

Expression and spec fuzzing share `contract.compare` for error-versus-success
verdicts. Error messages and exit codes are tier 3: different errors in the
same expression are not failures. The saved `Restrict` and integer-domain
field-selection cases exercise this rule; normal values must still agree.

Multi-worker verdicts: when two different violations are found at the same BFS level, TLC with
`-workers 4` may report another one than with one worker (and tlx agrees with it). `fuzz_spec.py`
then checks tlx's verdict against TLC with as many workers (docs/compat.md D-3).
