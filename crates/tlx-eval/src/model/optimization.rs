//! Apply frontend state-reduction proofs through the existing VIEW machinery.

use tlx_front::cfg::ConstBinding;
use tlx_sema::hir::*;

use super::{behavior, Behavior, InterpModel};

impl InterpModel {
    /// Forget proved irrelevant values in fingerprints, retaining concrete
    /// values and original actions for execution and counterexample replay.
    /// Safety only; an existing VIEW/SYMMETRY takes precedence.
    pub fn project_state(&mut self) -> Option<(&'static str, Vec<String>)> {
        let cfg = &self.ip.cfg;
        if !self.live.is_empty()
            || self.has_view_or_symmetry()
            || cfg.symmetry.is_some()
            || !self.possible.is_empty()
            || !self.postconditions.is_empty()
            || !cfg.constants.iter().all(|b| {
                matches!(b, ConstBinding::Value { name, module: None, .. }
                if self.ip.root_def(name).is_none())
            })
        {
            return None;
        }
        let Ok(Behavior::Full { next, .. }) = behavior(&self.ip, cfg) else { return None };
        let observations: Vec<_> = self
            .invariants
            .iter()
            .chain(&self.constraints)
            .chain(&self.action_constraints)
            .chain(&self.action_props)
            .chain(self.init_props.iter().map(|(_, e)| e))
            .chain(&self.alias)
            .cloned()
            .collect();
        let omitted = tlx_sema::optimize::unobserved_variables(&self.ip.prog, &self.init, &next, &observations);
        if omitted.is_empty() {
            let projection = tlx_sema::optimize::phase_projection(&self.ip.prog, cfg, &self.init, &next, &observations)?;
            self.view = Some(projection.view);
            return Some(("phase-field-projection", projection.fields));
        }
        let retained = self
            .ip
            .prog
            .vars
            .iter()
            .enumerate()
            .filter(|(i, _)| !omitted.contains(&VarId(*i as u32)))
            .map(|(i, v)| Expr::new(ExprKind::Var(VarId(i as u32)), v.span))
            .collect();
        self.view = Some(Expr::new(ExprKind::Tuple(retained), self.init.span));
        Some(("unobserved-state-projection", omitted.iter().map(|v| self.ip.prog.vars[v.idx()].name.to_string()).collect()))
    }
}
