//! Apply frontend state-reduction proofs through the existing VIEW machinery.

use tlx_front::cfg::ConstBinding;
use tlx_sema::hir::*;
use tlx_value::{ops, Value};

use crate::{env::Env, error::EResult, eval::Ctx};

use super::{behavior, Behavior, InterpModel};

impl InterpModel {
    /// Forget proved irrelevant values in fingerprints, retaining concrete
    /// values and original actions for execution and counterexample replay.
    /// Safety only. Existing VIEWs take precedence. Symmetry composes only
    /// when every constant introduced by the projection is fixed by it.
    pub fn project_state(&mut self) -> Option<(&'static str, Vec<String>)> {
        let cfg = &self.ip.cfg;
        if !self.live.is_empty()
            || self.has_view()
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
            let (rule, projection) =
                if let Some(p) = tlx_sema::optimize::phase_projection(&self.ip.prog, cfg, &self.init, &next, &observations) {
                    ("phase-field-projection", p)
                } else {
                    (
                        "sequence-length-projection",
                        tlx_sema::optimize::sequence_length_projection(&self.ip.prog, cfg, &self.init, &next, &observations)?,
                    )
                };
            if !self.projection_equivariant(&projection.view) {
                return None;
            }
            self.view = Some(projection.view);
            self.state_projection = true;
            return Some((rule, projection.fields));
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
        self.state_projection = true;
        Some(("unobserved-state-projection", omitted.iter().map(|v| self.ip.prog.vars[v.idx()].name.to_string()).collect()))
    }

    pub fn has_projected_symmetry(&self) -> bool {
        self.state_projection && !self.symmetry.is_empty()
    }

    fn projection_equivariant(&self, e: &Expr) -> bool {
        if self.symmetry.is_empty() {
            return true;
        }
        if matches!(&*e.kind, ExprKind::Const(_)) {
            let Ok(value) = self.ip.eval(e, &Env::default(), &Ctx::NONE) else { return false };
            return self.symmetry.iter().all(|p| ops::permute(&value, &|s| p.get(&s).cloned()).is_ok_and(|v| v == value));
        }
        let mut valid = true;
        tlx_sema::visit::children(e, &mut |child| valid &= self.projection_equivariant(child));
        valid
    }

    /// Canonicalize the projected value, so forgotten fields cannot decide
    /// which permutation represents its orbit. Internal sentinels may have
    /// different types from retained values; use the total structural order.
    pub(super) fn projected_orbit(&self, projected: Value) -> EResult<Value> {
        let mut least = projected.clone();
        for permutation in &self.symmetry {
            let image = ops::permute(&projected, &|s| permutation.get(&s).cloned())?;
            if tlx_value::order::try_total_cmp(&image, &least)?.is_lt() {
                least = image;
            }
        }
        Ok(least)
    }
}
