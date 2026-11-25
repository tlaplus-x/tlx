//! Regression tests for IR/C helper deduplication, CPS join-point factoring
//! (`Stmt::If` / `Stmt::Then`), and incremental IR/JIT reuse across
//! layout-miss restarts.

use std::collections::HashSet;
use std::sync::Arc;

use tlx_compile::cgen::CGen;
use tlx_compile::enc;
use tlx_compile::ir::{ExprKind, Stmt};
use tlx_compile::verify::Program;
use tlx_layout::Shape;
use tlx_runtime::{explore, Model, Options};
use tlx_testkit::{diff::Harness, module, spec};

/// Multi-action spec with:
/// - a 3-way non-assigning branching guard before a multi-branch continuation,
/// - sequential assigning `IF` / `CASE` stages (CPS join points),
/// - a shared pure non-recursive helper containing a quantifier called from
///   multiple actions and invariants,
/// - repeated constant encoded tables.
const DEDUP_SPEC: &str = r#"
EXTENDS Naturals, Sequences, FiniteSets
VARIABLES x, y, z, log

Nodes == {1, 2, 3}

\* Substantial pure non-recursive helper with a quantifier: outlined once as fn_*.
HasQuorum(s, thresh) ==
    LET matched == {n \in Nodes : n \in s /\ n >= thresh}
    IN \E q \in SUBSET Nodes : q \subseteq matched /\ Cardinality(q) * 2 > Cardinality(Nodes)

GuardBranch(a) == a = 0 \/ a = 1 \/ a = 2

StepA ==
    /\ GuardBranch(x)
    /\ IF x = 0 THEN x' = 1 ELSE IF x = 1 THEN x' = 2 ELSE x' = 0
    /\ CASE y = 0 -> y' = 1
         [] y = 1 -> y' = 2
         [] OTHER -> y' = 0
    /\ IF HasQuorum({1, 2, 3}, z) THEN z' = 1 ELSE z' = 2
    /\ log' = IF Len(log) < 2 THEN Append(log, [k |-> x, v |-> y]) ELSE Tail(log)

StepB ==
    /\ x' = x
    /\ IF HasQuorum({1, 2}, y) THEN y' = 1 ELSE y' = 2
    /\ z' = IF z < 2 THEN z + 1 ELSE 0
    /\ log' = log

Init == x = 0 /\ y = 0 /\ z = 0 /\ log = <<>>
Next == StepA \/ StepB
Inv == HasQuorum({1, 2, 3}, z) /\ (z <= 2) /\ (x <= 2)
"#;

#[test]
fn cps_then_helper_outlining_and_static_dedup() {
    let src = module("DedupAndFactor", DEDUP_SPEC);
    let h = Harness::new(&src, "INIT Init\nNEXT Next\nINVARIANT Inv\n");
    assert!(h.not_native().is_empty(), "all functions must compile natively: {:?}", h.not_native());
    h.run_reachable(40).assert_ok("dedup and factor parity");

    // 1. Sequential assigning IF/CASE in StepA must factor via Stmt::Then and Stmt::If
    //    instead of multiplying the continuation exponentially.
    let step_a = h.actions.iter().flatten().find(|a| a.name.as_ref().contains("StepA")).expect("StepA lowered");
    let (mut has_if, mut has_then, mut emits) = (false, false, 0usize);
    fn walk_stmt(s: &Stmt, has_if: &mut bool, has_then: &mut bool, emits: &mut usize) {
        match s {
            Stmt::If { .. } => *has_if = true,
            Stmt::Then { .. } => *has_then = true,
            Stmt::Emit => *emits += 1,
            _ => {}
        }
        s.for_each_sub_stmt(&mut |sub| walk_stmt(sub, has_if, has_then, emits));
    }
    walk_stmt(&step_a.body, &mut has_if, &mut has_then, &mut emits);
    assert!(has_if, "expected Stmt::If in StepA");
    assert!(has_then, "expected Stmt::Then join point in StepA");
    // Without factoring, 3 guard branches * 3 IF * 3 CASE * 2 IF = 54 emits.
    assert!(emits <= 12, "expected factored emits <= 12 in StepA, got {emits}");

    // 2. Shared pure helper `HasQuorum` must be outlined into `typing.funcs` and
    //    called via `ExprKind::Call` across actions/invariants.
    assert!(
        h.typing.funcs.iter().any(|f| f.name.as_ref() == "HasQuorum"),
        "expected HasQuorum to be outlined into typing.funcs, got {:?}",
        h.typing.funcs.iter().map(|f| f.name.as_ref()).collect::<Vec<_>>()
    );
    let mut call_sites = 0usize;
    fn count_calls(e: &tlx_compile::ir::Expr, n: &mut usize) {
        if matches!(&*e.kind, ExprKind::Call { .. }) {
            *n += 1;
        }
        e.for_each_child(&mut |c| count_calls(c, n));
    }
    for a in h.actions.iter().flatten() {
        a.body.for_each_expr_deep(&mut |e| count_calls(e, &mut call_sites));
    }
    for p in &h.invariants {
        count_calls(&p.body, &mut call_sites);
    }
    assert!(call_sites >= 3, "expected HasQuorum called from StepA, StepB, and Inv; got {call_sites}");

    // 3. Generated C source must deduplicate identical `static const` array initializers.
    let verified = Program::new(&h.typing, h.init.as_ref(), &h.actions, &h.invariants, &h.aprops).expect("verified program");
    let lib = CGen::new(&verified).library(h.base.action_names(), h.base.invariant_names());
    let mut seen_inits: HashSet<(String, String)> = HashSet::new();
    for line in lib.src.lines() {
        let trimmed = line.trim();
        if trimmed.starts_with("static const ") && trimmed.contains("[] = {") {
            let (lhs, rhs) = trimmed.split_once("[] = ").unwrap();
            let ty_part = lhs.rsplit_once(' ').unwrap().0.to_string();
            assert!(seen_inits.insert((ty_part.clone(), rhs.to_string())), "duplicate static const table emitted in C source: {trimmed}");
        }
    }
}

/// Multi-action spec where variable 0 (`msgs`) widens on layout misses during
/// exploration (shifting the offsets of variables 1..3), while `UpdateA` and
/// `UpdateB` only copy `msgs` via `UNCHANGED msgs` and `InvStable` only reads
/// the unchanged-shape variables.
const RESTART_REUSE_SPEC: &str = r#"
EXTENDS Naturals, FiniteSets
VARIABLES msgs, counter, flag, mode

SendMsg ==
    /\ counter < 5
    /\ msgs' = msgs \cup {[id |-> counter, kind |-> IF counter % 2 = 0 THEN "req" ELSE "ack"]}
    /\ counter' = counter + 1
    /\ UNCHANGED <<flag, mode>>

UpdateFlag ==
    /\ flag' = ~flag
    /\ mode' = IF flag THEN (mode + 1) % 3 ELSE mode
    /\ UNCHANGED <<msgs, counter>>

UpdateMode ==
    /\ mode < 2
    /\ mode' = mode + 1
    /\ UNCHANGED <<msgs, counter, flag>>

Init == msgs = {} /\ counter = 0 /\ flag = FALSE /\ mode = 0
Next == SendMsg \/ UpdateFlag \/ UpdateMode
InvStable == mode \in 0..2 /\ counter \in 0..5 /\ (flag \in BOOLEAN)
InvMsgs == Cardinality(msgs) <= 5
"#;

#[test]
fn layout_miss_restarts_reuse_ir_and_jit_with_exact_parity() {
    let src = module("RestartReuse", RESTART_REUSE_SPEC);
    let cfg = "INIT Init\nNEXT Next\nINVARIANT InvStable\nINVARIANT InvMsgs\n";
    let base = Arc::new(spec::load(&src, cfg));
    let opts = Options { workers: 1, ..Options::default() };

    let interp_report = explore(base.as_ref(), &opts);
    let (_enc_model, enc_report) = enc::check(base.clone(), &opts, 6).expect("compiled check succeeds");

    assert_eq!(enc_report.outcome, interp_report.outcome, "outcome must match interpreter across restarts");
    assert_eq!(enc_report.stats.distinct, interp_report.stats.distinct, "distinct state count must match interpreter across restarts");
    assert_eq!(enc_report.stats.generated, interp_report.stats.generated, "generated state count must match interpreter across restarts");
    assert!(enc_report.stats.distinct > 10, "non-trivial state space expected, got {}", enc_report.stats.distinct);
}

/// Regression for eager path counting over a multi-bound existential whose
/// first domain is empty at runtime while the second domain raises a runtime
/// error (`1 \div 0`): every backend (closure IR, C, JIT) must evaluate all
/// bounds upfront and report the error just like the interpreter.
#[test]
fn counted_multi_bound_quantifier_evaluates_second_domain_when_first_is_empty() {
    let src = module(
        "CountBounds",
        r#"
EXTENDS Naturals
VARIABLES pc, x
Init == pc = 0 /\ x = 0
Next ==
    /\ \E a \in (1..pc), b \in (1..(1 \div pc)) : a = b
    /\ pc' = pc + 1
    /\ x' = x + 1
"#,
    );
    let cfg = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";
    let h = Harness::new(&src, cfg);
    let rep = h.run_reachable(10);
    rep.assert_ok("empty first quantifier domain preserves error in second domain");
    let (exec, native) = rep.totals();
    assert!(exec.both_fail > 0 && native.both_fail > 0, "expected error in all tiers:\n{}", rep.render());

    // Also verify end-to-end `enc::check` agrees with `explore` (reports runtime error).
    let base = Arc::new(spec::load(&src, cfg));
    let opts = Options { workers: 1, check_deadlock: false, ..Options::default() };
    let interp = explore(base.as_ref(), &opts);
    let (_, compiled) = enc::check(base, &opts, 4).expect("enc::check");
    assert_eq!(compiled.outcome, interp.outcome, "compiled outcome must match interpreter error");
}

/// Regression for eager path counting over a lazy union of Cartesian products
/// with overlapping pairs (`(1..2 \X 1..2) \cup (1..2 \X 1..3)` has 4 + 6 = 10
/// enumerated elements with 4 duplicates): every backend must preserve
/// multiplicity and emit 10 successors (11 generated, 2 distinct including Init).
#[test]
fn counted_lazy_union_preserves_duplicate_successors() {
    let src = module(
        "CountUnion",
        r#"
EXTENDS Naturals
VARIABLES pc, x
Init == pc = 0 /\ x = 0
Next ==
    /\ pc = 0
    /\ \E p \in (({1, 2} \X {1, 2}) \cup ({1, 2} \X {1, 2, 3})) : p[1] >= 1
    /\ pc' = 1
    /\ x' = 1
"#,
    );
    let cfg = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";
    let h = Harness::new(&src, cfg);
    h.run_reachable(10).assert_ok("lazy union multiplicity preserved across tiers");

    let base = Arc::new(spec::load(&src, cfg));
    let opts = Options { workers: 1, check_deadlock: false, ..Options::default() };
    let interp = explore(base.as_ref(), &opts);
    let (_, compiled) = enc::check(base, &opts, 4).expect("enc::check");
    assert_eq!(interp.stats.generated, 11);
    assert_eq!(interp.stats.distinct, 2);
    assert_eq!(compiled.stats.generated, interp.stats.generated, "duplicate successors must be preserved");
    assert_eq!(compiled.stats.distinct, interp.stats.distinct);
    assert_eq!(compiled.outcome, interp.outcome);
}

/// Regression for eager path counting over a branching `\A` hidden behind a
/// named operator (`Guard`) vs written inline: rejecting `Fold { product: true }`
/// post-expansion keeps both forms on regular action enumeration so the first
/// binder varies fastest and division by zero at `(i, j) = (2, 1)` is reported
/// identically across interpreter, closure IR, generated C, and JIT.
#[test]
fn counted_forall_product_order_matches_named_and_inline() {
    let named = module(
        "ProductOrderNamed",
        r#"
EXTENDS Naturals
VARIABLE pc
Init == pc = 0
Guard == \A <<i, k>> \in {<<1, 1>>, <<2, 1>>}, j \in 1..2 :
    IF i = j THEN (TRUE \/ FALSE) ELSE IF i = 1 THEN FALSE ELSE 1 \div pc = 0
Next == Guard /\ pc' = 1
"#,
    );
    let inline = module(
        "ProductOrderInline",
        r#"
EXTENDS Naturals
VARIABLE pc
Init == pc = 0
Next ==
    /\ (\A <<i, k>> \in {<<1, 1>>, <<2, 1>>}, j \in 1..2 :
        IF i = j THEN (TRUE \/ FALSE) ELSE IF i = 1 THEN FALSE ELSE 1 \div pc = 0)
    /\ pc' = 1
"#,
    );
    let cfg = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";
    let opts = Options { workers: 1, check_deadlock: false, ..Options::default() };

    for (label, src) in [("named", named), ("inline", inline)] {
        let h = Harness::with_shapes(&src, cfg, vec![Shape::Int { lo: 0, hi: 2 }]);
        let rep = h.run_reachable(10);
        rep.assert_ok(&format!("{label} branching \\A product order"));
        let (exec, native) = rep.totals();
        assert!(exec.both_fail > 0 && native.both_fail > 0, "{label}: expected division-by-zero in all tiers:\n{}", rep.render());

        let base = Arc::new(spec::load(&src, cfg));
        let interp = explore(base.as_ref(), &opts);
        let (_, compiled) = enc::check(base, &opts, 4).expect("enc::check");
        assert_eq!(compiled.outcome, interp.outcome, "{label}: compiled outcome must match interpreter error");
    }
}
