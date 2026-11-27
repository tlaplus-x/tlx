//! Lower the actual length-only slice, retaining its branch choices and events.
use super::super::{max_local, mentions_vars};
use std::fmt::Write;

use super::super::{binding, variable, Branch};
use super::{Domain, Domains};
use crate::{builtins::Builtin as B, hir::*, optimize::lean::literal, visit};

pub(super) fn emit(
    vars: &[VarId],
    domains: &Domains,
    initial: &[Branch],
    steps: &[Branch],
    spec: super::super::CheckSpec<'_>,
) -> Option<super::super::OpenCert> {
    let mut e = Emitter { vars, domains, atoms: vec![] };
    let (initial_guards, seeds) = e.branches(initial, false)?;
    let (guards, transfers) = e.branches(steps, true)?;
    let observations = spec.invariants.iter().map(|o| e.leaf(o, "observe", true)).collect::<Option<Vec<_>>>()?;
    let init_obs = spec.init_props.iter().map(|o| e.leaf(o, "observe", true)).collect::<Option<Vec<_>>>()?;
    let constraints = spec.constraints.iter().map(|o| e.leaf(o, "observe", true)).collect::<Option<Vec<_>>>()?;
    let constrained = spec.is_constrained();
    let mut out = String::from(include_str!("../../LengthCertificate.lean"));
    out.push_str("\nnamespace TlxOptimization.GeneratedLength\nopen TlxOptimization LengthRule\nnoncomputable section\nset_option linter.unusedVariables false\nattribute [local instance] Classical.propDecidable\n");
    writeln!(out, "abbrev Key := Fin {}", vars.len()).unwrap();
    out.push_str("-- HIR lowering, inferred domains and leaf interpretation remain trusted.\nstructure Semantics (C E W : Type) where\n  test : Nat → C → C → W → (Key → Nat) → Prop\n  observe : Nat → C → (Key → Nat) → Prop\n  value : Nat → C → C → W → (Key → Nat) → E\n");
    for (i, atom) in e.atoms.iter().enumerate() {
        writeln!(out, "def atom{i}HIR : String := {}", literal(atom)).unwrap();
    }
    let params = "{C E W : Type} (sem : Semantics C E W)";
    writeln!(out, "variable {params}\ndef initial {params} (c : C) (choice : Nat × W) : Prop :=\n  let d := c\n  let n : Key → Nat := fun _ => 0\n  match choice.1 with").unwrap();
    for (i, guard) in initial_guards.iter().enumerate() {
        writeln!(out, "  | {i} => {guard}").unwrap();
    }
    out.push_str("  | _ => False\n");
    writeln!(out, "def seed {params} (c : C) (choice : Nat × W) (k : Key) : List E :=\n  let d := c\n  let n : Key → Nat := fun _ => 0\n  match choice.1 with").unwrap();
    for (i, row) in seeds.iter().enumerate() {
        writeln!(out, "  | {i} => match k.val with").unwrap();
        for (k, seed) in row.iter().enumerate() {
            writeln!(out, "    | {k} => ({seed}).concrete []").unwrap();
        }
        out.push_str("    | _ => []\n");
    }
    out.push_str("  | _ => []\n");
    writeln!(out, "def step {params} (c d : C) (choice : Nat × W) (n : Key → Nat) : Prop :=\n  match choice.1 with").unwrap();
    for (i, guard) in guards.iter().enumerate() {
        writeln!(out, "  | {i} => {guard}").unwrap();
    }
    out.push_str("  | _ => False\n");
    writeln!(out, "def transfer {params} (c d : C) (choice : Nat × W) (n : Key → Nat) (k : Key) : Transfer E :=\n  match choice.1 with")
        .unwrap();
    for (i, row) in transfers.iter().enumerate() {
        writeln!(out, "  | {i} => match k.val with").unwrap();
        for (k, transfer) in row.iter().enumerate() {
            writeln!(out, "    | {k} => {transfer}").unwrap();
        }
        out.push_str("    | _ => Transfer.keep\n");
    }
    out.push_str("  | _ => Transfer.keep\n");
    writeln!(out, "def observe {params} (c : C) (n : Key → Nat) : Prop := {}", conjunction(&observations)).unwrap();
    if constrained {
        writeln!(out, "def initObserve {params} (c : C) (n : Key → Nat) : Prop := {}", conjunction(&init_obs)).unwrap();
        writeln!(out, "def constraint {params} (c : C) (n : Key → Nat) : Prop := {}", conjunction(&constraints)).unwrap();
    }
    out.push_str("def model : LengthRule.Model C Key E (Nat × W) where\n  initial := initial sem\n  seed := seed sem\n  step := step sem\n  transfer := transfer sem\n  observe := observe sem\n");
    if constrained {
        out.push_str("  initObserve := initObserve sem\n  constraint := constraint sem\n");
    }
    Some(super::super::OpenCert::new(out, include_str!("certificate.lean"), "GeneratedLength", constrained, false, false))
}

struct Emitter<'a> {
    vars: &'a [VarId],
    domains: &'a Domains,
    atoms: Vec<String>,
}

impl Emitter<'_> {
    fn branches(&mut self, branches: &[Branch], primed: bool) -> Option<(Vec<String>, Vec<Vec<String>>)> {
        let mut guards = vec![];
        let mut transfers = vec![];
        for branch in branches {
            let mut tests = vec![];
            for bound in &branch.bounds {
                let BoundVars::Many(ids) = &bound.vars else { return None };
                for id in ids {
                    let member = Expr::new(
                        ExprKind::Builtin { op: B::In, args: vec![Expr::new(ExprKind::Local(*id), bound.set.span), bound.set.clone()] },
                        bound.set.span,
                    );
                    tests.push(self.leaf(&member, "test", primed)?);
                }
            }
            for term in &branch.terms {
                if matches!(&*term.kind, ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 && variable(&args[0], primed).is_some_and(|v| self.vars.contains(&v)))
                {
                    continue;
                }
                let term = if let ExprKind::Builtin { op: B::Unchanged, args } = &*term.kind {
                    if !primed || args.len() != 1 {
                        return None;
                    }
                    Expr::new(ExprKind::Builtin { op: B::Unchanged, args: vec![self.remove_sequences(&args[0])?] }, term.span)
                } else {
                    term.clone()
                };
                tests.push(self.leaf(&term, "test", primed)?);
            }
            guards.push(conjunction(&tests));
            let mut row = vec![];
            for var in self.vars {
                row.push(self.transfer(&binding(branch, *var, primed)?, *var, primed)?);
            }
            transfers.push(row);
        }
        Some((guards, transfers))
    }

    fn remove_sequences(&self, e: &Expr) -> Option<Expr> {
        let kind = match &*e.kind {
            ExprKind::Var(v) if self.vars.contains(v) => ExprKind::Tuple(vec![]),
            ExprKind::Var(_) => return Some(e.clone()),
            ExprKind::Tuple(es) => ExprKind::Tuple(es.iter().map(|e| self.remove_sequences(e)).collect::<Option<_>>()?),
            _ => return None,
        };
        Some(Expr::new(kind, e.span))
    }

    fn transfer(&mut self, e: &Expr, var: VarId, primed: bool) -> Option<String> {
        Some(match &*e.kind {
            ExprKind::Var(v) if primed && *v == var => "Transfer.keep".into(),
            ExprKind::Tuple(es) => {
                format!("(Transfer.reset [{}])", es.iter().map(|e| self.leaf(e, "value", primed)).collect::<Option<Vec<_>>>()?.join(", "))
            }
            ExprKind::Builtin { op: B::Append, args } if args.len() == 2 => {
                format!("(Transfer.append {} {})", self.transfer(&args[0], var, primed)?, self.leaf(&args[1], "value", primed)?)
            }
            ExprKind::If { cond, then, els } => format!(
                "(if {} then {} else {})",
                self.leaf(cond, "test", primed)?,
                self.transfer(then, var, primed)?,
                self.transfer(els, var, primed)?
            ),
            _ => return None,
        })
    }

    fn leaf(&mut self, e: &Expr, kind: &str, lengths: bool) -> Option<String> {
        let mut local = max_local(e).checked_add(1)?;
        let mut holes = Vec::new();
        let masked = self.mask(e, lengths, &mut local, &mut holes)?;
        let id = self.atoms.len();
        self.atoms.push(format!("{kind} HIR: {masked:#?}\nLength holes (LocalId, sequence slot): {holes:?}"));
        Some(if kind == "observe" { format!("(sem.observe {id} c n)") } else { format!("(sem.{kind} {id} c d choice.2 n)") })
    }

    fn mentions(&self, e: &Expr) -> bool {
        mentions_vars(e, self.vars)
    }

    fn mask(&self, e: &Expr, lengths: bool, next: &mut u32, holes: &mut Vec<(LocalId, usize)>) -> Option<Expr> {
        if let ExprKind::Builtin { op: B::Len, args } = &*e.kind {
            if args.len() == 1 {
                if let Some(k) = variable(&args[0], false).and_then(|v| self.vars.iter().position(|x| *x == v)) {
                    if !lengths {
                        return None;
                    }
                    let local = LocalId(*next);
                    *next = next.checked_add(1)?;
                    holes.push((local, k));
                    return Some(Expr::new(ExprKind::Local(local), e.span));
                }
            }
        }
        if let ExprKind::Builtin { op: B::In, args } = &*e.kind {
            if args.len() == 2
                && variable(&args[0], false).is_some_and(|v| {
                    self.vars.contains(&v)
                        && matches!(self.domains.vars[v.idx()], Domain::Seq(_))
                        && self.domains.belongs(&self.domains.vars[v.idx()], &args[1])
                })
            {
                return Some(Expr::new(ExprKind::Bool(true), e.span));
            }
        }
        if matches!(&*e.kind, ExprKind::Var(v) if self.vars.contains(v))
            || matches!(&*e.kind, ExprKind::Builtin { op: B::Prime, .. } if self.mentions(e))
        {
            return None;
        }
        let mut masked = e.clone();
        let mut valid = true;
        visit::children_mut(&mut masked, &mut |child| {
            if let Some(e) = self.mask(child, lengths, next, holes) {
                *child = e;
            } else {
                valid = false;
            }
        });
        valid.then_some(masked)
    }
}

fn conjunction(parts: &[String]) -> String {
    if parts.is_empty() {
        "True".into()
    } else {
        format!("({})", parts.join(" ∧ "))
    }
}
