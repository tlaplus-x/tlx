//! Immutable table payloads can depend on retained values and explicit live reads.
use super::{binding, schema, syntax, variable, Atom, Branch, Emitter, Expr, ExprKind, Mode, VarId};
use crate::{builtins::Builtin as B, hir::BoundVars, visit};
use std::fmt::Write;

impl Emitter<'_, '_> {
    pub(super) fn history_reads(&mut self, e: &Expr, mode: Mode) -> Option<Expr> {
        let Some(h) = self.plan.history.clone() else { return Some(e.clone()) };
        if let ExprKind::FnApp { func, args } = &*e.kind {
            if variable(func, false) == Some(VarId(h.variable as u32)) {
                if matches!(mode, Mode::Initial) {
                    return None;
                }
                let [key] = args.as_slice() else { return None };
                let reference = if let Some((f, r)) = self.reference(key) {
                    if f != h.family {
                        return None;
                    }
                    r
                } else {
                    let Atom::Num(n) = self.context.atom(key)? else { return None };
                    self.anchor(h.family, n)?
                };
                let hole = self.context.fresh()?;
                self.targets
                    .push(format!("{hole:?}: payload lookup from reads {reference}; missing lookup is outside the totality contract"));
                return Some(Expr::new(ExprKind::Local(hole), e.span));
            }
        }
        if matches!(&*e.kind, ExprKind::Var(v) if v.idx()==h.variable) {
            return None;
        }
        // Never turn a next-state table read into a current-state payload hole.
        if matches!(&*e.kind, ExprKind::Builtin { op: B::Prime, .. }) {
            return self.independent(e).then(|| e.clone());
        }
        let mut out = e.clone();
        let mut valid = true;
        visit::children_mut(&mut out, &mut |child| match self.history_reads(child, mode) {
            Some(value) => *child = value,
            None => valid = false,
        });
        valid.then_some(out)
    }

    pub(super) fn history_payload(&mut self, b: &Branch, primed: bool) -> Option<Option<String>> {
        let Some(h) = &self.plan.history else { return Some(None) };
        let var = VarId(h.variable as u32);
        let rhs = binding(b, var, primed)?;
        if primed && variable(&rhs, false) == Some(var) {
            return Some(None);
        }
        let singleton = if primed { syntax::history_extension(&rhs, var)? } else { &rhs };
        let ExprKind::FnConstruct { bounds, body } = &*singleton.kind else { return None };
        let [bound] = bounds.as_slice() else { return None };
        let BoundVars::Many(ids) = &bound.vars else { return None };
        let [id] = ids.as_slice() else { return None };
        let ExprKind::SetEnum(keys) = &*bound.set.kind else { return None };
        let [key] = keys.as_slice() else { return None };
        let mode = if primed { Mode::Step } else { Mode::Initial };
        let value = self.history_reads(&schema::substitute(body, *id, key), mode)?;
        if !self.independent(&value) {
            return None;
        }
        let i = self.atoms.len();
        self.atoms.push(format!("Immutable history payload HIR: {value:#?}; only retained values and explicit lookup holes"));
        Some(Some(if primed { format!("sem.payload {i} c d choice.2 reads") } else { format!("sem.seedPayload {i} c choice.2") }))
    }

    pub(super) fn live_semantics(&self, out: &mut String) {
        let h = self.plan.history.as_ref().unwrap();
        writeln!(out, "def historyFamily : Family := ⟨{}, by decide⟩", h.family).unwrap();
        out.push_str("abbrev Reads (V : Type) := Reference (Slot historyFamily) (Anchor historyFamily) → Option V\nstructure Semantics (C W V : Type) where\n  fallback : V\n  initial : Nat → C → W → Prop\n  test : Nat → C → C → W → Reads V → Prop\n  observe : Nat → C → Reads V → Prop\n  seedPayload : Nat → C → W → V\n  payload : Nat → C → C → W → Reads V → V\nvariable {C W V : Type} (sem : Semantics C W V)\n");
    }

    pub(super) fn live_model(&self, out: &mut String, seeds: &[super::Seed], cases: &[super::Case], observation: &str) {
        let h = self.plan.history.as_ref().unwrap();
        out.push_str("def tick {W : Type} (choice : BranchId × W) : Bool :=\n  match choice.1.val with\n");
        for (b, c) in cases.iter().enumerate() {
            writeln!(out, "  | {b} => {}", if c.deltas[h.family] == 1 { "true" } else { "false" }).unwrap();
        }
        out.push_str("  | _ => false\ntheorem historyDelta {W : Type} (w : BranchId × W) : delta w historyFamily = (if tick w then 1 else 0) := by\n  rcases w with ⟨⟨n, hn⟩, w⟩\n");
        let count = seeds.len().max(cases.len());
        let values = (0..count).map(|i| format!("n = {i}")).collect::<Vec<_>>().join(" ∨ ");
        let names = (0..count).map(|i| format!("h{i}")).collect::<Vec<_>>().join(" | ");
        writeln!(out, "  have h : {values} := by omega\n  rcases h with {names} <;> subst n <;> rfl").unwrap();
        out.push_str(
            "def seedPayload {C W V : Type} (sem : Semantics C W V) (c : C) (choice : BranchId × W) : V :=\n  match choice.1.val with\n",
        );
        for (b, s) in seeds.iter().enumerate() {
            writeln!(out, "  | {b} => {}", s.payload.as_deref().expect("validated live initial payload")).unwrap();
        }
        out.push_str("  | _ => sem.fallback\ndef payload {C W V : Type} (sem : Semantics C W V) (c d : C) (choice : BranchId × W) (reads : Reads V) : V :=\n  match choice.1.val with\n");
        for (b, c) in cases.iter().enumerate() {
            writeln!(out, "  | {b} => {}", c.payload.as_deref().unwrap_or("sem.fallback")).unwrap();
        }
        out.push_str("  | _ => sem.fallback\n");
        writeln!(out,"def observe {{C W V : Type}} (sem : Semantics C W V) (c : C) (reads : Reads V) : FamilyTest Family Slot Anchor := {observation}").unwrap();
        out.push_str("def model : LiveRule.Model C Family (BranchId × W) V Slot Anchor where\n  layout := layout\n  family := historyFamily\n  initial := initial sem\n  seedValues := seedValues\n  seedPayload := seedPayload sem\n  tick := tick\n  delta := delta\n  historyDelta := historyDelta\n  transfers := transfers sem\n  guard := guard sem\n  payload := payload sem\n  observe := observe sem\n");
        out.push_str(
            include_str!("certificate.lean").replace("rankKey", "runtimeKey").replace("GeneratedNested", "GeneratedLive").as_str(),
        );
    }
}
