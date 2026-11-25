//! Connected certificates for deleting unobserved variables with proved-total
//! pure deterministic updates over structured TLA+ values.
use std::collections::BTreeSet;
use std::fmt::Write;

use super::{
    branches_with_if, mentions_phase_var,
    sym_norm::SymNormalizer,
    sym_totality::{collect_const_info, CheckEnv, TotalityChecker},
    unchanged, variable, Branch, CheckSpec, FieldProjection,
};
use crate::{builtins::Builtin as B, hir::*, optimize::lean::literal, visit, Program};
use tlx_front::cfg::Config;

/// Single deterministic binding of an omitted variable on one normalized branch.
#[derive(Clone, Debug)]
pub(in crate::optimize::phase) enum HiddenBinding {
    /// Deterministic `v = rhs` (`!primed`) or `v' = rhs` (`primed`) at `term_idx`,
    /// guaranteed to contain no primed reads inside `rhs`.
    Assign { term_idx: usize, rhs: Expr },
    /// Frame `UNCHANGED` covering `v` (only valid when `primed == true`).
    Unchanged,
}

/// Extract the unique deterministic binding of `v` on `branch`, rejecting
/// missing bindings, multi-bindings (`UNCHANGED v /\ v' = e`), reversed
/// equalities (`e = v'`), non-deterministic `v' \in S` / `v' \subseteq S`,
/// and primed reads inside `rhs`.
pub(in crate::optimize::phase) fn branch_hidden_binding(branch: &Branch, v: VarId, primed: bool) -> Option<HiddenBinding> {
    let mut count = 0usize;
    let mut found = None;
    for (idx, term) in branch.terms.iter().enumerate() {
        match &*term.kind {
            ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 => {
                if variable(&args[0], primed) == Some(v) {
                    count += 1;
                    found = Some(HiddenBinding::Assign { term_idx: idx, rhs: args[1].clone() });
                } else if variable(&args[1], primed) == Some(v) {
                    return None;
                }
            }
            ExprKind::Builtin { op: B::In | B::SubsetEq, args } if args.len() == 2 => {
                if variable(&args[0], primed) == Some(v) {
                    return None;
                }
            }
            ExprKind::Builtin { op: B::Unchanged, args } if primed && args.len() == 1 => {
                let n = unchanged(&args[0], v);
                if n > 0 {
                    count += n;
                    found = Some(HiddenBinding::Unchanged);
                }
            }
            _ => {}
        }
    }
    if count != 1 {
        return None;
    }
    let binding = found?;
    if let HiddenBinding::Assign { ref rhs, .. } = binding {
        if mentions_phase_var(rhs, true) {
            return None;
        }
    }
    Some(binding)
}

pub fn unobserved_projection(program: &Program, init: &Expr, next: &Expr, observations: &[Expr]) -> Option<FieldProjection> {
    unobserved_projection_with_spec(program, &Config::default(), init, next, CheckSpec::invariants_only(observations))
}

pub fn unobserved_projection_with_spec(
    program: &Program,
    cfg: &Config,
    init: &Expr,
    next: &Expr,
    spec: CheckSpec<'_>,
) -> Option<FieldProjection> {
    if !super::cfg_constants_supported(program, cfg) {
        return None;
    }
    let mut expand = SymNormalizer::for_equiv_with_config(program, cfg);
    let init_norm = expand.normalize(init)?;
    let next_norm = expand.normalize(next)?;
    let norm = spec.try_map(|e| expand.normalize(e))?;
    let norm_spec = norm.as_spec();
    let all_obs: Vec<_> = norm_spec.all_exprs().cloned().collect();
    let liveness = crate::optimize::projection::unobserved_candidates(program, &init_norm, &next_norm, &all_obs)?;
    let initial = branches_with_if(&init_norm)?;
    let steps = branches_with_if(&next_norm)?;
    if initial.is_empty() || steps.is_empty() {
        return None;
    }

    let const_info = collect_const_info(program, cfg);
    let empty_keys = BTreeSet::new();
    let totality = TotalityChecker::with_const_info(program, &[], &empty_keys, const_info, &init_norm, &next_norm, None);
    if spec.is_constrained() && !constrained_observations_total(&totality, norm_spec) {
        return None;
    }

    // Iteratively prune any uncertifiable candidate variable (missing/multi
    // binding, primed RHS read, non-total/overflowing RHS, or leaked mention
    // in retained terms/bounds) and re-close the live cone so one uncertifiable
    // variable never blocks erasing genuinely certifiable dead variables.
    let mut forced_live = vec![false; program.vars.len()];
    let omitted = loop {
        let cand = liveness.dead_vars(&forced_live);
        if cand.is_empty() {
            return None;
        }
        let mut pruned_any = false;
        for &v in &cand {
            if !var_certifiable(&totality, v, &cand, &initial, &steps) {
                forced_live[v.idx()] = true;
                pruned_any = true;
            }
        }
        if !pruned_any {
            break cand;
        }
    };

    let mut emitter = Emitter { omitted: &omitted, atoms: vec![] };
    let certificate = expand.attach_const_subst(emitter.emit(&initial, &steps, norm_spec)?)?;
    let retained = program
        .vars
        .iter()
        .enumerate()
        .filter(|(i, _)| !omitted.contains(&VarId(*i as u32)))
        .map(|(i, v)| Expr::new(ExprKind::Var(VarId(i as u32)), v.span))
        .collect();
    Some(FieldProjection {
        view: Expr::new(ExprKind::Tuple(retained), init.span),
        fields: omitted.iter().map(|v| program.vars[v.idx()].name.to_string()).collect(),
        certificate: Some(certificate),
        ordered: None,
    })
}

fn constrained_observations_total(totality: &TotalityChecker<'_>, spec: CheckSpec<'_>) -> bool {
    let obs_env = CheckEnv::default();
    for obs in spec.init_props.iter().chain(spec.constraints.iter()) {
        if !totality.check_form_total(obs, false, false, &obs_env) {
            return false;
        }
    }
    for act in spec.action_constraints.iter().chain(spec.action_props.iter()) {
        if !totality.check_form_total(act, true, false, &obs_env) {
            return false;
        }
    }
    true
}

fn expr_mentions_var(e: &Expr, target: VarId) -> bool {
    if matches!(&*e.kind, ExprKind::Var(v) if *v == target) {
        return true;
    }
    let mut found = false;
    visit::children(e, &mut |child| found |= expr_mentions_var(child, target));
    found
}

fn is_var_or_tuple_frame(e: &Expr) -> bool {
    match &*e.kind {
        ExprKind::Var(_) => true,
        ExprKind::Tuple(es) => es.iter().all(is_var_or_tuple_frame),
        _ => false,
    }
}

/// Verify that candidate omitted variable `v` is single-bound, pure, total,
/// 32-bit overflow-free, and unreferenced by retained terms/bounds on every
/// `Init` and `Next` branch.
fn var_certifiable(totality: &TotalityChecker<'_>, v: VarId, omitted: &[VarId], initial: &[Branch], steps: &[Branch]) -> bool {
    for (branches, primed) in [(initial, false), (steps, true)] {
        for b in branches {
            let Some(bind) = branch_hidden_binding(b, v, primed) else {
                return false;
            };
            // Every branch bound and every retained (non-omitted-assignment)
            // term must be independent of `v`.
            if b.bounds.iter().any(|bnd| expr_mentions_var(&bnd.set, v)) {
                return false;
            }
            for term in &b.terms {
                match &*term.kind {
                    ExprKind::Builtin { op: B::Eq, args }
                        if args.len() == 2 && variable(&args[0], primed).is_some_and(|u| omitted.contains(&u)) => {}
                    ExprKind::Builtin { op: B::Unchanged, args } if primed && args.len() == 1 => {
                        if expr_mentions_var(&args[0], v) && !is_var_or_tuple_frame(&args[0]) {
                            return false;
                        }
                    }
                    _ => {
                        if expr_mentions_var(term, v) {
                            return false;
                        }
                    }
                }
            }
            if let HiddenBinding::Assign { term_idx, rhs } = bind {
                if !check_hidden_rhs_total(totality, b, term_idx, &rhs, primed) {
                    return false;
                }
            }
        }
    }
    true
}

/// Verify totality and `i32` overflow freedom of a hidden variable's RHS at
/// `term_idx` within `branch`, respecting TLC's left-to-right short-circuiting
/// evaluation order (only preceding guards/bindings in `branch.terms[..term_idx]`
/// are available as facts/bound variables).
fn check_hidden_rhs_total(totality: &TotalityChecker<'_>, branch: &Branch, term_idx: usize, rhs: &Expr, primed: bool) -> bool {
    let mut env = if primed { CheckEnv::default() } else { CheckEnv::with_var_tracking(false) };
    if totality.bind_branch_bounds(&branch.bounds, &mut env).is_none() {
        return false;
    }
    for term in &branch.terms[..term_idx] {
        if !primed {
            match &*term.kind {
                ExprKind::Builtin { op: B::Eq | B::In | B::SubsetEq, args } if args.len() == 2 => {
                    if let Some(u) = variable(&args[0], false) {
                        env.mark_var_bound(u);
                    }
                }
                _ => {}
            }
            totality.apply_positive_fact(term, false, &mut env);
        } else if !mentions_phase_var(term, true) {
            totality.apply_positive_fact(term, false, &mut env);
        }
    }
    totality.check_expr_total_shape(rhs, &env).is_some()
}

struct Emitter<'a> {
    omitted: &'a [VarId],
    atoms: Vec<String>,
}
impl Emitter<'_> {
    fn independent(&self, e: &Expr) -> bool {
        if matches!(&*e.kind, ExprKind::Var(v) if self.omitted.contains(v)) {
            return false;
        }
        let mut independent = true;
        visit::children(e, &mut |child| independent &= self.independent(child));
        independent
    }

    fn atom(&mut self, e: &Expr) -> Option<usize> {
        if !self.independent(e) {
            return None;
        }
        let id = self.atoms.len();
        self.atoms.push(format!("{e:#?}"));
        Some(id)
    }

    fn hidden_atom(&mut self, desc: String) -> usize {
        let id = self.atoms.len();
        self.atoms.push(desc);
        id
    }

    fn frame(&self, e: &Expr) -> Option<Expr> {
        if self.independent(e) {
            return Some(e.clone());
        }
        Some(Expr::new(
            match &*e.kind {
                ExprKind::Var(v) if self.omitted.contains(v) => ExprKind::Tuple(vec![]),
                ExprKind::Var(_) => return Some(e.clone()),
                ExprKind::Tuple(es) => ExprKind::Tuple(es.iter().map(|e| self.frame(e)).collect::<Option<_>>()?),
                _ => return None,
            },
            e.span,
        ))
    }

    fn transfer(&mut self, bind: &HiddenBinding, v: VarId, primed: bool) -> Option<String> {
        match bind {
            HiddenBinding::Unchanged => {
                let i = self.omitted.iter().position(|x| *x == v)?;
                Some(format!("h ⟨{i}, by decide⟩"))
            }
            HiddenBinding::Assign { rhs, .. } => Some(match &*rhs.kind {
                ExprKind::Num(n) if i32::try_from(*n).is_ok() => format!("sem.number ({n})"),
                ExprKind::Str(s) => format!("sem.string {}", literal(s)),
                ExprKind::Bool(b) => format!("sem.boolean {b}"),
                ExprKind::Var(u) if primed => {
                    if let Some(i) = self.omitted.iter().position(|x| x == u) {
                        format!("h ⟨{i}, by decide⟩")
                    } else {
                        format!("sem.value {} c", self.atom(rhs)?)
                    }
                }
                _ if !primed => {
                    let id = self.hidden_atom(format!("Hidden init expr HIR: {rhs:#?}"));
                    format!("sem.initExpr {id} c choice.2")
                }
                _ => {
                    let id = self.hidden_atom(format!("Hidden update expr HIR: {rhs:#?}"));
                    format!("sem.updateExpr {id} c d choice.2 h")
                }
            }),
        }
    }

    fn branch(&mut self, b: &Branch, primed: bool) -> Option<(String, String)> {
        let values = self
            .omitted
            .iter()
            .map(|&v| {
                let bind = branch_hidden_binding(b, v, primed)?;
                self.transfer(&bind, v, primed)
            })
            .collect::<Option<Vec<_>>>()?;
        let mut terms = vec![];
        for term in &b.terms {
            match &*term.kind {
                ExprKind::Builtin { op: B::Eq, args }
                    if args.len() == 2 && variable(&args[0], primed).is_some_and(|v| self.omitted.contains(&v)) => {}
                ExprKind::Builtin { op: B::Unchanged, args } if primed && args.len() == 1 => {
                    terms.push(Expr::new(ExprKind::Builtin { op: B::Unchanged, args: vec![self.frame(&args[0])?] }, term.span));
                }
                _ => terms.push(term.clone()),
            }
        }
        if !b.bounds.iter().all(|b| self.independent(&b.set)) || !terms.iter().all(|e| self.independent(e)) {
            return None;
        }
        let id = self.atoms.len();
        self.atoms.push(format!("bounds: {:#?}\nterms: {terms:#?}", b.bounds));
        let d = if primed { "d" } else { "c" };
        let mut update = "fun i => match i.val with\n".to_owned();
        for (i, value) in values.iter().enumerate() {
            writeln!(update, "    | {i} => {value}").unwrap();
        }
        // This default is unreachable for Fin omitted.len, but avoids a
        // dependent match and requires no inhabitant or correctness premise.
        writeln!(update, "    | _ => {}", values[0]).unwrap();
        Some((format!("sem.test {id} c {d} choice.2"), update))
    }

    fn emit(&mut self, initial: &[Branch], steps: &[Branch], spec: CheckSpec<'_>) -> Option<super::OpenCert> {
        let initial = initial.iter().map(|b| self.branch(b, false)).collect::<Option<Vec<_>>>()?;
        let steps = steps.iter().map(|b| self.branch(b, true)).collect::<Option<Vec<_>>>()?;
        let observations = spec.invariants.iter().map(|e| Some(format!("sem.observe {} c", self.atom(e)?))).collect::<Option<Vec<_>>>()?;
        let init_obs = spec.init_props.iter().map(|e| Some(format!("sem.observe {} c", self.atom(e)?))).collect::<Option<Vec<_>>>()?;
        let constraints = spec.constraints.iter().map(|e| Some(format!("sem.observe {} c", self.atom(e)?))).collect::<Option<Vec<_>>>()?;
        let action_constraints =
            spec.action_constraints.iter().map(|e| Some(format!("sem.actionObserve {} c d", self.atom(e)?))).collect::<Option<Vec<_>>>()?;
        let action_obs =
            spec.action_props.iter().map(|e| Some(format!("sem.actionObserve {} c d", self.atom(e)?))).collect::<Option<Vec<_>>>()?;
        let constrained = spec.is_constrained();
        let count = self.omitted.len();
        let mut out = String::from(include_str!("../ErasureCertificate.lean"));
        out.push_str("\nnamespace TlxOptimization.GeneratedErasure\nopen TlxOptimization ErasureRule\nnoncomputable section\nset_option linter.unusedVariables false\n");
        writeln!(out, "abbrev HiddenCount : Nat := {count}").unwrap();
        if constrained {
            out.push_str("\nstructure Semantics (C V W : Type) where\n  test : Nat → C → C → W → Prop\n  value : Nat → C → V\n  initExpr : Nat → C → W → V\n  updateExpr : Nat → C → C → W → (Fin HiddenCount → V) → V\n  observe : Nat → C → Prop\n  actionObserve : Nat → C → C → Prop\n  number : Int → V\n  string : String → V\n  boolean : Bool → V\n");
        } else {
            out.push_str("\nstructure Semantics (C V W : Type) where\n  test : Nat → C → C → W → Prop\n  value : Nat → C → V\n  initExpr : Nat → C → W → V\n  updateExpr : Nat → C → C → W → (Fin HiddenCount → V) → V\n  observe : Nat → C → Prop\n  number : Int → V\n  string : String → V\n  boolean : Bool → V\n");
        }
        for (i, atom) in self.atoms.iter().enumerate() {
            writeln!(out, "def atom{i}HIR : String := {}", literal(atom)).unwrap();
        }
        let params = "{C V W : Type} (sem : Semantics C V W)";
        writeln!(out, "variable {params}").unwrap();
        for (name, primed, branches) in [("initial", false, &initial), ("step", true, &steps)] {
            let d = if primed { "d" } else { "" };
            writeln!(out, "def {name} {params} (c {d} : C) (choice : Nat × W) : Prop :=\n  match choice.1 with").unwrap();
            for (i, (guard, _)) in branches.iter().enumerate() {
                writeln!(out, "  | {i} => {guard}").unwrap();
            }
            out.push_str("  | _ => False\n");
            let name = if primed { "update" } else { "seed" };
            let hidden = if primed { "(h : Fin HiddenCount → V)" } else { "" };
            writeln!(out, "def {name} {params} (c {d} : C) (choice : Nat × W) {hidden} : Fin HiddenCount → V :=\n  match choice.1 with")
                .unwrap();
            for (i, (_, update)) in branches.iter().enumerate() {
                writeln!(out, "  | {i} => {update}").unwrap();
            }
            out.push_str("  | _ => fun _ => sem.boolean false\n");
        }
        let join_conj = |parts: &[String]| if parts.is_empty() { "True".into() } else { parts.join(" ∧ ") };
        writeln!(out, "def observe {params} (c : C) : Prop := {}", join_conj(&observations)).unwrap();
        if constrained {
            writeln!(out, "def initObserve {params} (c : C) : Prop := {}", join_conj(&init_obs)).unwrap();
            writeln!(out, "def constraint {params} (c : C) : Prop := {}", join_conj(&constraints)).unwrap();
            writeln!(out, "def actionConstraint {params} (c d : C) : Prop := {}", join_conj(&action_constraints)).unwrap();
            writeln!(out, "def actionObserve {params} (c d : C) : Prop := {}", join_conj(&action_obs)).unwrap();
        }
        out.push_str("def model : ErasureRule.Model C (Fin HiddenCount → V) (Nat × W) where\n");
        for field in ["initial", "seed", "step", "update", "observe"] {
            writeln!(out, "  {field} := @{field} C V W sem").unwrap();
        }
        if constrained {
            for field in ["initObserve", "constraint", "actionConstraint", "actionObserve"] {
                writeln!(out, "  {field} := @{field} C V W sem").unwrap();
            }
        }
        let mut tail = String::new();
        tail.push_str("def before := (model sem).concrete\ndef after := (model sem).reduced\ndef project := (model sem).project\n");
        tail.push_str("theorem certificate : Certificate (before sem) (after sem) (project sem) := (model sem).certificate\n");
        tail.push_str("theorem optimization_correct :\n  (∀ s, Reachable (before sem) s → (before sem).safe s) ↔\n  (∀ a, Reachable (after sem) a → (after sem).safe a) := (model sem).optimization_correct\n");
        tail.push_str("theorem specification_correct :\n  (∀ s, Reachable (withStuttering (before sem)) s → (before sem).safe s) ↔\n  (∀ a, Reachable (withStuttering (after sem)) a → (after sem).safe a) := (model sem).specification_correct\n");
        tail.push_str("theorem counterexample_lifts {a} (ha : Reachable (after sem) a) (bad : ¬ (after sem).safe a) :\n  ∃ s, Reachable (before sem) s ∧ project sem s = a ∧ ¬ (before sem).safe s := (model sem).counterexample_lifts ha bad\n");
        tail.push_str("theorem deadlock_preserved (s : C × (Fin HiddenCount → V)) :\n  (¬ ∃ t, (before sem).next s t) ↔ (¬ ∃ a, (after sem).next (project sem s) a) := (model sem).deadlock_preserved s\n");
        for theorem in ["certificate", "optimization_correct", "specification_correct", "counterexample_lifts", "deadlock_preserved"] {
            writeln!(tail, "#print axioms {theorem}").unwrap();
        }
        Some(super::OpenCert::new(out, &tail, "GeneratedErasure", constrained, false, false))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    const SPEC: &str = r#"---- MODULE Erase ----
EXTENDS Integers
VARIABLE x, a, b
Init == x = 0 /\ a = 1 /\ b = 2
Next == x' = 1 - x /\ a' = b /\ b' = a
Inv == x \in {0, 1}
===="#;

    fn candidate(source: &str) -> Option<FieldProjection> {
        let dir = tlx_testkit::TempDir::with_spec("erasure-proof", source, "");
        let program = Program::load(&dir.join("Erase.tla"), &[]).unwrap();
        let expr = |name: &str| {
            let def = program.defs.iter().find(|d| &*d.name == name).unwrap();
            let DefKind::Op(e) = &def.kind else { panic!() };
            e.clone()
        };
        unobserved_projection(&program, &expr("Init"), &expr("Next"), &[expr("Inv")])
    }

    #[test]
    fn certificate_contains_actual_literals_and_simultaneous_copy_cycle() {
        let projection = candidate(SPEC).unwrap();
        assert_eq!(projection.fields, ["a", "b"]);
        let proof = projection.certificate.unwrap();
        assert!(proof.contains("sem.number (1)"));
        assert!(proof.contains("sem.number (2)"));
        assert!(proof.contains("| 0 => h ⟨1, by decide⟩"));
        assert!(proof.contains("| 1 => h ⟨0, by decide⟩"));
        assert!(proof.contains("GeneratedErasure"));
        assert!(proof.contains("theorem certificate : Certificate"));
    }

    #[test]
    fn structured_total_expressions_are_erased_and_partial_or_overflowing_refuse() {
        let structured = r#"---- MODULE Erase ----
EXTENDS Naturals, Sequences
VARIABLE x, log, stats, audit
Init == x = 0 /\ log = <<>> /\ stats = [k \in {0, 1} |-> FALSE] /\ audit = {}
Next == /\ x' = 1 - x
        /\ log' = IF Len(log) < 2 THEN Append(log, [kind |-> "flip", v |-> x]) ELSE <<>>
        /\ stats' = [stats EXCEPT ![x] = TRUE]
        /\ audit' = audit \cup {[who |-> x, ok |-> stats[x]]}
Inv == x \in {0, 1}
===="#;
        let proj = candidate(structured).expect("total structured ghost updates must certify");
        assert_eq!(proj.fields, ["log", "stats", "audit"]);
        let proof = proj.certificate.unwrap();
        assert!(proof.contains("sem.initExpr"));
        assert!(proof.contains("sem.updateExpr"));

        // Partial (div by zero), out-of-bounds sequence index, unbounded overflow,
        // and primed read inside hidden RHS must all refuse.
        for bad in [
            "---- MODULE Erase ----\nEXTENDS Integers\nVARIABLE x, bad\nInit == x = 0 /\\ bad = 0\nNext == x' = 1 - x /\\ bad' = 1 \\div 0\nInv == x \\in {0, 1}\n====",
            "---- MODULE Erase ----\nEXTENDS Naturals, Sequences\nVARIABLE x, bad\nInit == x = 0 /\\ bad = <<>>\nNext == x' = 1 - x /\\ bad' = bad[1]\nInv == x \\in {0, 1}\n====",
            "---- MODULE Erase ----\nEXTENDS Naturals\nVARIABLE x, bad\nInit == x = 0 /\\ bad = 0\nNext == x' = 1 - x /\\ bad' = bad + 1\nInv == x \\in {0, 1}\n====",
            "---- MODULE Erase ----\nEXTENDS Naturals\nVARIABLE x, bad\nInit == x = 0 /\\ bad = 0\nNext == x' = 1 - x /\\ bad' = x'\nInv == x \\in {0, 1}\n====",
        ] {
            assert!(candidate(bad).is_none(), "must refuse: {bad}");
        }
    }

    #[test]
    fn iterative_pruning_erases_certifiable_dead_vars_and_retains_uncertifiable_cone() {
        // `bad` overflows (`bad' = bad + 1`), `dep` feeds `bad` so re-closing the
        // live cone must retain `dep` too, while independent `good` is still erased.
        let spec = r#"---- MODULE Erase ----
EXTENDS Naturals
VARIABLE x, bad, dep, good
Init == x = 0 /\ bad = 0 /\ dep = 1 /\ good = {}
Next == x' = 1 - x /\ bad' = bad + dep /\ dep' = 1 /\ good' = good \cup {[v |-> x]}
Inv == x \in {0, 1}
===="#;
        let proj = candidate(spec).expect("good should survive pruning of bad/dep");
        assert_eq!(proj.fields, ["good"]);
    }

    #[test]
    fn incomplete_updates_and_observed_cycles_cannot_be_erased() {
        for spec in [
            SPEC.replace("Next ==", "Next == UNCHANGED x \\/ (").replace("\nInv ==", ")\nInv =="),
            SPEC.replace("Inv ==", "Inv == a = b /\\"),
            SPEC.replace("b' = a", "b' = a /\\ UNCHANGED b"),
        ] {
            assert!(candidate(&spec).is_none(), "{spec}");
        }
    }

    #[test]
    fn shape_inference_tracks_implies_forall_and_action_subscript_writes() {
        // Each construct can assign `x' = 2`, which `h' = x` copies to `h`, making
        // `<<1>>[h]` reachable and out of bounds; erasure must refuse every one.
        for write_x in ["(x >= 1 => x' = 2)", "(\\A i \\in {1} : x' = 2)", "([x' = 2]_x)", "(<<x' = 2>>_x)"] {
            let spec = format!(
                "---- MODULE Erase ----\nEXTENDS Naturals\nVARIABLES x, h\n\
                 Init == x = 1 /\\ h = 1\n\
                 Next == \\/ ({write_x} /\\ h' = x)\n\
                         \\/ (UNCHANGED x /\\ h' = <<1>>[h])\n\
                 Inv == x \\in {{1, 2}}\n===="
            );
            assert!(candidate(&spec).is_none(), "must refuse out-of-bounds lookup via {write_x}");
        }
    }
}
