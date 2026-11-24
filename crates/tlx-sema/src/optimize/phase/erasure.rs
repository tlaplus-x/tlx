//! Connected certificates for deleting unobserved variables with total updates.
use std::fmt::Write;

use super::{binding, branches, normalize, variable, Branch, CheckSpec, FieldProjection};
use crate::{builtins::Builtin as B, hir::*, optimize::lean::literal, visit, Program};
use tlx_front::cfg::Config;

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
    let mut expand = normalize::Normalizer::with_config(program, cfg);
    let init_norm = expand.root(init)?;
    let next_norm = expand.root(next)?;
    let norm = spec.try_map(|e| expand.root(e))?;
    let norm_spec = norm.as_spec();
    let all_obs: Vec<_> = norm_spec.all_exprs().cloned().collect();
    let omitted = crate::optimize::unobserved_variables(program, &init_norm, &next_norm, &all_obs);
    if omitted.is_empty() {
        return None;
    }
    if spec.is_constrained() && !super::sym_totality::check_constrained_observations_total(program, cfg, init, next, spec) {
        return None;
    }
    let initial = branches(&init_norm)?;
    let steps = branches(&next_norm)?;
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

    fn frame(&self, e: &Expr) -> Option<Expr> {
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

    fn transfer(&mut self, e: &Expr, primed: bool) -> Option<String> {
        Some(match &*e.kind {
            ExprKind::Num(n) if i32::try_from(*n).is_ok() => format!("sem.number ({n})"),
            ExprKind::Str(s) => format!("sem.string {}", literal(s)),
            ExprKind::Bool(b) => format!("sem.boolean {b}"),
            ExprKind::Var(v) if primed => {
                if let Some(i) = self.omitted.iter().position(|x| x == v) {
                    format!("h ⟨{i}, by decide⟩")
                } else {
                    format!("sem.value {} c", self.atom(e)?)
                }
            }
            _ => return None,
        })
    }

    fn branch(&mut self, b: &Branch, primed: bool) -> Option<(String, String)> {
        let values = self.omitted.iter().map(|v| self.transfer(&binding(b, *v, primed)?, primed)).collect::<Option<Vec<_>>>()?;
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
        let mut out = String::from(include_str!("../ErasureCertificate.lean"));
        out.push_str("\nnamespace TlxOptimization.GeneratedErasure\nopen TlxOptimization ErasureRule\nnoncomputable section\nset_option linter.unusedVariables false\n");
        if constrained {
            out.push_str("\nstructure Semantics (C V W : Type) where\n  test : Nat → C → C → W → Prop\n  value : Nat → C → V\n  observe : Nat → C → Prop\n  actionObserve : Nat → C → C → Prop\n  number : Int → V\n  string : String → V\n  boolean : Bool → V\n");
        } else {
            out.push_str("\nstructure Semantics (C V W : Type) where\n  test : Nat → C → C → W → Prop\n  value : Nat → C → V\n  observe : Nat → C → Prop\n  number : Int → V\n  string : String → V\n  boolean : Bool → V\n");
        }
        for (i, atom) in self.atoms.iter().enumerate() {
            writeln!(out, "def atom{i}HIR : String := {}", literal(atom)).unwrap();
        }
        let count = self.omitted.len();
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
            let hidden = if primed { format!("(h : Fin {count} → V)") } else { String::new() };
            writeln!(out, "def {name} {params} (c {d} : C) (choice : Nat × W) {hidden} : Fin {count} → V :=\n  match choice.1 with")
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
        writeln!(out, "def model : ErasureRule.Model C (Fin {count} → V) (Nat × W) where").unwrap();
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
        writeln!(tail, "theorem deadlock_preserved (s : C × (Fin {count} → V)) :\n  (¬ ∃ t, (before sem).next s t) ↔ (¬ ∃ a, (after sem).next (project sem s) a) := (model sem).deadlock_preserved s").unwrap();
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
    fn incomplete_updates_and_observed_cycles_cannot_be_erased() {
        for spec in [
            SPEC.replace("Next ==", "Next == UNCHANGED x \\/ (").replace("\nInv ==", ")\nInv =="),
            SPEC.replace("Inv ==", "Inv == a = b /\\"),
            SPEC.replace("b' = a", "b' = a /\\ UNCHANGED b"),
        ] {
            assert!(candidate(&spec).is_none(), "{spec}");
        }
    }
}
