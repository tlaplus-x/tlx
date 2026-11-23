//! Choice-bearing expression lowering (`ChoiceTest`, `ChoiceExpr`, `ChoiceSlotExpr`)
//! with `UniqueKind`, `ProjKind`, `bindFold`, and leaf candidate totality verification.

use super::super::sym_totality::{CheckEnv, Shape};
use super::super::variable;
use super::bounds::{eval_elem_bound, eval_val_bound, fold_partial_sums_fit_i32, mask_key_count, LocalBounds, ValBound, I32_MIN};
use super::domain_infer::{domain_is_integer, expr_has_choose, group_mask_exact, mask_atoms_domain, GroupInfo, VarShape};
use super::mentions_local;
use super::pure_expr::{bounded, AuxScope, MsgBoundVar};
use super::{subst_local, Domain, Domains, Emitter, GroupMask, KeyRef, Locals};
use crate::{builtins::Builtin as B, hir::*, visit};
use std::collections::HashMap;
use std::sync::Arc;

pub(super) enum ExtractedChoice {
    Fold { mask: GroupMask, filter: String, term: String, hole: LocalId, replaced: Expr },
    Proj { pk: String, hole: LocalId, replaced: Expr },
    Unique { uk: String, mask: GroupMask, hole: LocalId, replaced: Expr },
}

impl Emitter<'_> {
    pub(super) fn contains_any_choose(&self, e: &Expr) -> bool {
        if matches!(&*e.kind, ExprKind::Choose { .. }) {
            return true;
        }
        let mut found = false;
        visit::children(e, &mut |c| found |= self.contains_any_choose(c));
        found
    }

    pub(super) fn choose_scope_env(&self, keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> (Locals, LocalBounds) {
        let mut locals = self.step_locals.clone();
        let mut lbounds = self.step_local_bounds.clone();
        for &(lid, kmask) in keys {
            locals.insert(lid, self.mask_domain(kmask));
            lbounds.insert(lid, ValBound::Top);
        }
        for mv in &aux.msg_vars {
            if let Some(d) = self.msg_var_record_domain(mv) {
                locals.insert(mv.local, d);
            }
            if let Some(b) = self.msg_var_record_bound(mv) {
                lbounds.insert(mv.local, b);
            }
        }
        for &lid in &aux.fold_ints {
            locals.insert(lid, Domain::Integer(I32_MIN));
            lbounds.insert(lid, ValBound::Top);
        }
        for &lid in &aux.count_nats {
            locals.insert(lid, Domain::Integer(0));
            lbounds.insert(lid, ValBound::Top);
        }
        (locals, lbounds)
    }

    fn msg_var_record_domain(&self, mv: &MsgBoundVar) -> Option<Domain> {
        for (vi, sh) in self.shapes.iter().enumerate() {
            if let VarShape::MsgSet { fields, key_field, val_field, .. } = sh {
                if *fields == mv.fields && *key_field == mv.key_field && *val_field == mv.val_field {
                    if let Domain::Set(elem) = &self.domains.vars[vi] {
                        return Some((**elem).clone());
                    }
                }
            }
        }
        None
    }

    fn msg_var_record_bound(&self, mv: &MsgBoundVar) -> Option<ValBound> {
        for (vi, sh) in self.shapes.iter().enumerate() {
            if let VarShape::MsgSet { fields, key_field, val_field, .. } = sh {
                if *fields == mv.fields && *key_field == mv.key_field && *val_field == mv.val_field {
                    return Some(self.model_bounds.vars[vi].set_elem());
                }
            }
        }
        None
    }

    fn choose_check_env(&self, keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> CheckEnv {
        let mut env = self.step_check_env.clone();
        for &(lid, kmask) in keys {
            env.bind_local(lid, self.totality.group_key_shape(kmask), None);
        }
        for mv in &aux.msg_vars {
            if let Some(sh) = self.msg_var_record_shape(mv) {
                env.bind_local(mv.local, sh, None);
            }
        }
        for &lid in &aux.fold_ints {
            env.bind_local(lid, Shape::Int(None), None);
        }
        for &lid in &aux.count_nats {
            env.bind_local(lid, Shape::Int(None), None);
        }
        env
    }

    fn msg_var_record_shape(&self, mv: &MsgBoundVar) -> Option<Shape> {
        for (vi, sh) in self.shapes.iter().enumerate() {
            if let VarShape::MsgSet { fields, key_field, val_field, .. } = sh {
                if *fields == mv.fields && *key_field == mv.key_field && *val_field == mv.val_field {
                    return self.totality.var_elem_shape(VarId(vi as u32));
                }
            }
        }
        None
    }

    fn eval_bound(&self, e: &Expr, lbounds: &LocalBounds) -> ValBound {
        eval_val_bound(e, &self.model_bounds, lbounds, None, self.domains, self.fold_vars, self.groups, &self.shapes, 0)
    }

    fn eval_elem_bound_here(&self, s: &Expr, lbounds: &LocalBounds) -> ValBound {
        eval_elem_bound(s, &self.model_bounds, lbounds, None, self.domains, self.fold_vars, self.groups, &self.shapes, 0)
    }

    /// Reject any un-extracted non-fold `CHOOSE` inside a leaf choice predicate/value, and
    /// check `[S \in SUBSET D]` domain inclusion (`fold_arg_in_superset`) on nested sum folds.
    fn check_leaf_fold_invariants(&self, e: &Expr, locals: &Locals, lbounds: &LocalBounds) -> bool {
        match &*e.kind {
            ExprKind::Quant { bounds, body, .. } | ExprKind::SetMap { expr: body, bounds } => {
                let mut scope = locals.clone();
                let mut bscope = lbounds.clone();
                for bnd in bounds {
                    let BoundVars::Many(ids) = &bnd.vars else { return false };
                    if !self.check_leaf_fold_invariants(&bnd.set, &scope, &bscope) {
                        return false;
                    }
                    let ed = self.eval_expr_element_domain(&bnd.set, &scope);
                    let eb = self.eval_elem_bound_here(&bnd.set, &bscope);
                    for &id in ids {
                        scope.insert(id, ed.clone());
                        bscope.insert(id, eb.clone());
                    }
                }
                self.check_leaf_fold_invariants(body, &scope, &bscope)
            }
            ExprKind::SetFilter { bound, pred } => {
                let BoundVars::Many(ids) = &bound.vars else { return false };
                if !self.check_leaf_fold_invariants(&bound.set, locals, lbounds) {
                    return false;
                }
                let mut scope = locals.clone();
                let mut bscope = lbounds.clone();
                let ed = self.eval_expr_element_domain(&bound.set, locals);
                let eb = self.eval_elem_bound_here(&bound.set, lbounds);
                for &id in ids {
                    scope.insert(id, ed.clone());
                    bscope.insert(id, eb.clone());
                }
                self.check_leaf_fold_invariants(pred, &scope, &bscope)
            }
            ExprKind::Choose { vars: BoundVars::Many(ids), set: Some(s), body } if ids.len() == 1 => {
                let id = ids[0];
                let Some(superset_opt) = self.fold_vars.get(&id) else {
                    return false;
                };
                if !self.check_leaf_fold_invariants(s, locals, lbounds) {
                    return false;
                }
                if let Some(superset) = superset_opt {
                    if !self.check_leaf_fold_invariants(superset, locals, lbounds) || !self.fold_arg_in_superset(s, superset, locals) {
                        return false;
                    }
                }
                let mut scope = locals.clone();
                let mut bscope = lbounds.clone();
                scope.insert(id, self.eval_expr_element_domain(s, locals));
                bscope.insert(id, self.eval_elem_bound_here(s, lbounds));
                self.check_leaf_fold_invariants(body, &scope, &bscope)
            }
            ExprKind::Choose { .. } => false,
            _ => {
                let mut ok = true;
                visit::children(e, &mut |c| ok &= self.check_leaf_fold_invariants(c, locals, lbounds));
                ok
            }
        }
    }

    fn check_choose_expr(&self, e: &Expr, env: &CheckEnv, locals: &Locals, lbounds: &LocalBounds) -> Option<Shape> {
        if !self.check_leaf_fold_invariants(e, locals, lbounds) {
            return None;
        }
        self.totality.check_expr_total_shape(e, env)
    }

    fn check_choose_bool(&self, e: &Expr, env: &CheckEnv, locals: &Locals, lbounds: &LocalBounds) -> bool {
        self.check_leaf_fold_invariants(e, locals, lbounds) && self.totality.check_form_total(e, false, false, env)
    }

    pub(super) fn choice_tests(&mut self, es: &[Expr], keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> Option<String> {
        let mut out = "(ChoiceTest.pure (PureTest.truth true))".to_owned();
        for e in es {
            let t = self.choice_test(e, keys, aux)?;
            out = if out == "(ChoiceTest.pure (PureTest.truth true))" { t } else { bounded(format!("(ChoiceTest.conj {out} {t})"))? };
        }
        Some(out)
    }

    fn choice_test(&mut self, e: &Expr, keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> Option<String> {
        if !self.contains_any_choose(e) {
            return bounded(format!("(ChoiceTest.pure {})", self.pure_test(e, keys, aux)?));
        }
        match &*e.kind {
            ExprKind::And(es) => return self.choice_tests(es, keys, aux),
            ExprKind::Or(es) if !es.is_empty() => {
                let mut it = es.iter();
                let mut out = self.choice_test(it.next()?, keys, aux)?;
                for item in it {
                    out = bounded(format!("(ChoiceTest.disj {out} {})", self.choice_test(item, keys, aux)?))?;
                }
                return Some(out);
            }
            ExprKind::Builtin { op, args } => match (op, args.as_slice()) {
                (B::Not, [a]) => return bounded(format!("(ChoiceTest.neg {})", self.choice_test(a, keys, aux)?)),
                (B::Implies, [a, b]) => {
                    return bounded(format!(
                        "(ChoiceTest.disj (ChoiceTest.neg {}) {})",
                        self.choice_test(a, keys, aux)?,
                        self.choice_test(b, keys, aux)?
                    ))
                }
                _ => {}
            },
            ExprKind::If { cond, then, els } => {
                return bounded(format!(
                    "(ChoiceTest.ite {} {} {})",
                    self.choice_test(cond, keys, aux)?,
                    self.choice_test(then, keys, aux)?,
                    self.choice_test(els, keys, aux)?
                ));
            }
            _ => {}
        }
        match self.extract_one_choice(e, keys, aux)? {
            ExtractedChoice::Fold { mask, filter, term, hole, replaced } => {
                let mut aux2 = aux.clone();
                aux2.fold_ints.insert(0, hole);
                let inner = self.choice_test(&replaced, keys, &aux2)?;
                bounded(format!("(ChoiceTest.bindFold {} {filter} {term} {inner})", self.mask_lean(mask)))
            }
            ExtractedChoice::Proj { pk, hole, replaced } => {
                let mut aux2 = aux.clone();
                aux2.proj_vals.insert(0, hole);
                let inner = self.choice_test(&replaced, keys, &aux2)?;
                bounded(format!("(ChoiceTest.bindProj {pk} {inner})"))
            }
            ExtractedChoice::Unique { uk, mask, hole, replaced } => {
                let mut keys2 = keys.to_vec();
                keys2.insert(0, (hole, mask));
                let inner = self.choice_test(&replaced, &keys2, aux)?;
                bounded(format!("(ChoiceTest.bindUnique {uk} {inner})"))
            }
        }
    }

    pub(super) fn choice_expr(&mut self, e: &Expr, keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> Option<String> {
        if !self.contains_any_choose(e) {
            return bounded(format!("(ChoiceExpr.pure {})", self.pure_expr(e, keys, aux)?));
        }
        if let ExprKind::If { cond, then, els } = &*e.kind {
            return bounded(format!(
                "(ChoiceExpr.ite {} {} {})",
                self.choice_test(cond, keys, aux)?,
                self.choice_expr(then, keys, aux)?,
                self.choice_expr(els, keys, aux)?
            ));
        }
        match self.extract_one_choice(e, keys, aux)? {
            ExtractedChoice::Fold { mask, filter, term, hole, replaced } => {
                let mut aux2 = aux.clone();
                aux2.fold_ints.insert(0, hole);
                let inner = self.choice_expr(&replaced, keys, &aux2)?;
                bounded(format!("(ChoiceExpr.bindFold {} {filter} {term} {inner})", self.mask_lean(mask)))
            }
            ExtractedChoice::Proj { pk, hole, replaced } => {
                let mut aux2 = aux.clone();
                aux2.proj_vals.insert(0, hole);
                let inner = self.choice_expr(&replaced, keys, &aux2)?;
                bounded(format!("(ChoiceExpr.bindProj {pk} {inner})"))
            }
            ExtractedChoice::Unique { uk, mask, hole, replaced } => {
                let mut keys2 = keys.to_vec();
                keys2.insert(0, (hole, mask));
                let inner = self.choice_expr(&replaced, &keys2, aux)?;
                bounded(format!("(ChoiceExpr.bindUnique {uk} {inner})"))
            }
        }
    }

    pub(super) fn choice_slot_expr(
        &mut self,
        e: &Expr,
        mask: GroupMask,
        has_fixed: bool,
        keys: &[(LocalId, GroupMask)],
        aux: &AuxScope,
    ) -> Option<String> {
        if !self.contains_any_choose(e) {
            if let ExprKind::If { cond, then, els } = &*e.kind {
                return bounded(format!(
                    "(ChoiceSlotExpr.ite (ChoiceTest.pure {}) {} {})",
                    self.pure_test(cond, keys, aux)?,
                    self.choice_slot_expr(then, mask, has_fixed, keys, aux)?,
                    self.choice_slot_expr(els, mask, has_fixed, keys, aux)?
                ));
            }
            if let Some((kref, kmask, k_has_fixed)) = self.key_ref(e, keys, aux) {
                if (kmask & !mask) != 0 || (k_has_fixed && !has_fixed) {
                    return None;
                }
                return Some(format!("(ChoiceSlotExpr.ref {})", kref.lean()));
            }
            if has_fixed {
                return bounded(format!("(ChoiceSlotExpr.fixedVal {})", self.pure_expr(e, keys, aux)?));
            }
            return None;
        }
        if let ExprKind::If { cond, then, els } = &*e.kind {
            return bounded(format!(
                "(ChoiceSlotExpr.ite {} {} {})",
                self.choice_test(cond, keys, aux)?,
                self.choice_slot_expr(then, mask, has_fixed, keys, aux)?,
                self.choice_slot_expr(els, mask, has_fixed, keys, aux)?
            ));
        }
        match self.extract_one_choice(e, keys, aux)? {
            ExtractedChoice::Fold { mask: fmask, filter, term, hole, replaced } => {
                let mut aux2 = aux.clone();
                aux2.fold_ints.insert(0, hole);
                let inner = self.choice_slot_expr(&replaced, mask, has_fixed, keys, &aux2)?;
                bounded(format!("(ChoiceSlotExpr.bindFold {} {filter} {term} {inner})", self.mask_lean(fmask)))
            }
            ExtractedChoice::Proj { pk, hole, replaced } => {
                let mut aux2 = aux.clone();
                aux2.proj_vals.insert(0, hole);
                let inner = self.choice_slot_expr(&replaced, mask, has_fixed, keys, &aux2)?;
                bounded(format!("(ChoiceSlotExpr.bindProj {pk} {inner})"))
            }
            ExtractedChoice::Unique { uk, mask: umask, hole, replaced } => {
                let mut keys2 = keys.to_vec();
                keys2.insert(0, (hole, umask));
                let inner = self.choice_slot_expr(&replaced, mask, has_fixed, &keys2, aux)?;
                bounded(format!("(ChoiceSlotExpr.bindUnique {uk} {inner})"))
            }
        }
    }

    /// Extract the leftmost unconditional choice item from `e` without crossing
    /// short-circuiting boolean operators, conditionals, or binders.
    pub(super) fn extract_one_choice(&mut self, e: &Expr, keys: &[(LocalId, GroupMask)], aux: &AuxScope) -> Option<ExtractedChoice> {
        if let ExprKind::Field { record, field } = &*e.kind {
            if let ExprKind::Choose { vars: BoundVars::Many(ids), set: Some(cset), body: cpred } = &*record.kind {
                if let [v] = ids.as_slice() {
                    if !self.fold_vars.contains_key(v) {
                        let pk = self.lower_proj_kind(*v, cset, cpred, field, keys, aux)?;
                        let hole = self.alloc_local();
                        let replaced = Expr::new(ExprKind::Local(hole), e.span);
                        return Some(ExtractedChoice::Proj { pk, hole, replaced });
                    }
                }
            }
        }
        if let ExprKind::Choose { vars: BoundVars::Many(ids), set: Some(cset), body: cpred } = &*e.kind {
            let [v] = ids.as_slice() else { return None };
            if let Some(superset_opt) = self.fold_vars.get(v).cloned() {
                let (mask, filter, term) = self.lower_fold_item(*v, cset, superset_opt.as_ref(), cpred, keys, aux)?;
                let hole = self.alloc_local();
                let replaced = Expr::new(ExprKind::Local(hole), e.span);
                return Some(ExtractedChoice::Fold { mask, filter, term, hole, replaced });
            }
            let (uk, mask) = self.lower_unique_kind(*v, cset, cpred, keys, aux)?;
            let hole = self.alloc_local();
            let replaced = Expr::new(ExprKind::Local(hole), e.span);
            return Some(ExtractedChoice::Unique { uk, mask, hole, replaced });
        }
        if is_choice_hoist_barrier(e) {
            return None;
        }
        // In `[base EXCEPT ![k1][k2] = rhs]`, `base` and `k1` are always evaluated
        // unconditionally; `rhs` is unconditionally evaluated only when `k1` is proved to be in
        // `DOMAIN base` (e.g. a single-key update on a `FixedMap`/`BoolMapFlag` variable).
        if let ExprKind::Except { base, updates } = &*e.kind {
            if updates.iter().any(|(path, rhs)| {
                path.iter().skip(1).any(|k| matches!(k, ExceptKey::Index(ixs) if ixs.iter().any(|x| self.contains_any_choose(x))))
                    || (self.contains_any_choose(rhs) && !self.except_update_unconditional(base, path))
            }) {
                return None;
            }
            if self.contains_any_choose(base) {
                let mut ex = self.extract_one_choice(base, keys, aux)?;
                let repl = match &ex {
                    ExtractedChoice::Fold { replaced, .. }
                    | ExtractedChoice::Proj { replaced, .. }
                    | ExtractedChoice::Unique { replaced, .. } => replaced.clone(),
                };
                let out = Expr::new(ExprKind::Except { base: repl, updates: updates.clone() }, e.span);
                match &mut ex {
                    ExtractedChoice::Fold { replaced, .. }
                    | ExtractedChoice::Proj { replaced, .. }
                    | ExtractedChoice::Unique { replaced, .. } => *replaced = out,
                }
                return Some(ex);
            }
            for (ui, (path, rhs)) in updates.iter().enumerate() {
                if let Some(ExceptKey::Index(ixs)) = path.first() {
                    for (ii, ix) in ixs.iter().enumerate() {
                        if self.contains_any_choose(ix) {
                            let mut ex = self.extract_one_choice(ix, keys, aux)?;
                            let repl = match &ex {
                                ExtractedChoice::Fold { replaced, .. }
                                | ExtractedChoice::Proj { replaced, .. }
                                | ExtractedChoice::Unique { replaced, .. } => replaced.clone(),
                            };
                            let mut new_updates = updates.clone();
                            if let ExceptKey::Index(ref mut new_ixs) = new_updates[ui].0[0] {
                                new_ixs[ii] = repl;
                            }
                            let out = Expr::new(ExprKind::Except { base: base.clone(), updates: new_updates }, e.span);
                            match &mut ex {
                                ExtractedChoice::Fold { replaced, .. }
                                | ExtractedChoice::Proj { replaced, .. }
                                | ExtractedChoice::Unique { replaced, .. } => *replaced = out,
                            }
                            return Some(ex);
                        }
                    }
                }
                if self.contains_any_choose(rhs) && self.except_update_unconditional(base, path) {
                    let mut ex = self.extract_one_choice(rhs, keys, aux)?;
                    let repl = match &ex {
                        ExtractedChoice::Fold { replaced, .. }
                        | ExtractedChoice::Proj { replaced, .. }
                        | ExtractedChoice::Unique { replaced, .. } => replaced.clone(),
                    };
                    let mut new_updates = updates.clone();
                    new_updates[ui].1 = repl;
                    let out = Expr::new(ExprKind::Except { base: base.clone(), updates: new_updates }, e.span);
                    match &mut ex {
                        ExtractedChoice::Fold { replaced, .. }
                        | ExtractedChoice::Proj { replaced, .. }
                        | ExtractedChoice::Unique { replaced, .. } => *replaced = out,
                    }
                    return Some(ex);
                }
            }
            return None;
        }
        let mut extracted: Option<ExtractedChoice> = None;
        let mut failed = false;
        let mut out = e.clone();
        visit::children_mut(&mut out, &mut |child| {
            if extracted.is_some() || failed || !self.contains_any_choose(child) {
                return;
            }
            match self.extract_one_choice(child, keys, aux) {
                Some(ex) => {
                    let repl = match &ex {
                        ExtractedChoice::Fold { replaced, .. }
                        | ExtractedChoice::Proj { replaced, .. }
                        | ExtractedChoice::Unique { replaced, .. } => replaced.clone(),
                    };
                    *child = repl;
                    extracted = Some(ex);
                }
                None => failed = true,
            }
        });
        if failed {
            return None;
        }
        if let Some(mut ex) = extracted {
            match &mut ex {
                ExtractedChoice::Fold { replaced, .. }
                | ExtractedChoice::Proj { replaced, .. }
                | ExtractedChoice::Unique { replaced, .. } => *replaced = out,
            }
            return Some(ex);
        }
        None
    }

    fn except_update_unconditional(&self, base: &Expr, path: &[ExceptKey]) -> bool {
        let [ExceptKey::Index(ixs)] = path else { return false };
        let [ix] = ixs.as_slice() else { return false };
        let ExprKind::Var(v) = &*base.kind else { return false };
        let mask = match self.shapes.get(v.idx()) {
            Some(VarShape::FixedMap { mask, .. } | VarShape::BoolMapFlag { mask, .. }) => *mask,
            _ => return false,
        };
        let mask_atoms = mask_atoms_domain(self.groups, mask);
        let ix_dom = self.domains.value(ix, &self.step_locals);
        matches!((&ix_dom, &mask_atoms), (Domain::Atoms(ia), Domain::Atoms(ma)) if !ia.is_empty() && ia.is_subset(ma))
    }

    fn fold_arg_in_superset(&self, s: &Expr, superset: &Expr, locals: &Locals) -> bool {
        if Self::same_keyset_var(s, superset) {
            return true;
        }
        if let ExprKind::SetFilter { bound, .. } = &*s.kind {
            if self.fold_arg_in_superset(&bound.set, superset, locals) {
                return true;
            }
        }
        if let Some(sup_exact) = self.domains.exact_set(superset) {
            return match self.eval_expr_element_domain(s, locals) {
                Domain::Bottom => true,
                Domain::Atoms(elems) => elems.is_subset(&sup_exact),
                _ => false,
            };
        }
        false
    }

    fn same_keyset_var(a: &Expr, b: &Expr) -> bool {
        match (&*a.kind, &*b.kind) {
            (ExprKind::Var(v1), ExprKind::Var(v2)) => v1 == v2,
            (ExprKind::Local(l1), ExprKind::Local(l2)) => l1 == l2,
            (ExprKind::Const(c1), ExprKind::Const(c2)) => c1 == c2,
            _ => false,
        }
    }

    fn lower_fold_item(
        &mut self,
        elem_var: LocalId,
        target_set: &Expr,
        superset_opt: Option<&Expr>,
        term_expr: &Expr,
        keys: &[(LocalId, GroupMask)],
        aux: &AuxScope,
    ) -> Option<(GroupMask, String, String)> {
        let (base_locals, base_lbounds) = self.choose_scope_env(keys, aux);
        let base_env = self.choose_check_env(keys, aux);
        self.check_choose_expr(target_set, &base_env, &base_locals, &base_lbounds)?;
        if let Some(superset) = superset_opt {
            self.check_choose_expr(superset, &base_env, &base_locals, &base_lbounds)?;
            let tmask = self.keyset_expr_mask(target_set, keys, aux)?;
            if let Some(exact_super) = self.domains.exact_set(superset) {
                let (smask, fixed) = group_mask_exact(self.groups, &exact_super)?;
                if smask == 0 || !fixed.is_empty() || (tmask & !smask) != 0 {
                    return None;
                }
            } else if !Self::same_keyset_var(target_set, superset) {
                return None;
            }
        }
        let (mask, filter) = if let Some(exact) = self.domains.exact_set(target_set) {
            let (m, fixed) = group_mask_exact(self.groups, &exact)?;
            if m == 0 || !fixed.is_empty() {
                return None;
            }
            (m, "(PureTest.truth true)".to_owned())
        } else {
            let m = self.keyset_expr_mask(target_set, keys, aux)?;
            if m == 0 {
                return None;
            }
            let fresh = self.alloc_local();
            let mut scope = keys.to_vec();
            scope.insert(0, (fresh, m));
            let f = self.key_in_set_pure(KeyRef::Bound(0), m, target_set, &scope, aux)?;
            (m, f)
        };
        let mut scope = keys.to_vec();
        scope.insert(0, (elem_var, mask));
        let mut locals = base_locals;
        let mut lbounds = base_lbounds;
        locals.insert(elem_var, self.mask_domain(mask));
        lbounds.insert(elem_var, ValBound::Top);
        let term_env = base_env.with_local(elem_var, self.totality.group_key_shape(mask));
        self.check_choose_expr(term_expr, &term_env, &locals, &lbounds)?;
        if !domain_is_integer(&self.eval_expr_domain(term_expr, &locals)) {
            return None;
        }
        // Prove every intermediate partial sum across all `n` keys in `mask` fits in checked
        // 32-bit signed integers (`i32::MIN..=i32::MAX`) regardless of CHOOSE evaluation order.
        let term_bound = self.eval_bound(term_expr, &lbounds).as_int();
        let key_count = mask_key_count(self.groups, mask);
        if !fold_partial_sums_fit_i32(term_bound, key_count) {
            return None;
        }
        let term = self.pure_expr(term_expr, &scope, aux)?;
        self.used_choose = true;
        Some((mask, filter, term))
    }

    fn lower_proj_kind(
        &mut self,
        v: LocalId,
        cset: &Expr,
        cpred: &Expr,
        field: &Arc<str>,
        keys: &[(LocalId, GroupMask)],
        aux: &AuxScope,
    ) -> Option<String> {
        let (base_locals, base_lbounds) = self.choose_scope_env(keys, aux);
        let base_env = self.choose_check_env(keys, aux);
        let cset_shape = self.check_choose_expr(cset, &base_env, &base_locals, &base_lbounds)?;
        let cset_elem_shape = self.totality.set_elem_of(&cset_shape)?;
        let mut pred_locals = base_locals.clone();
        let mut pred_lbounds = base_lbounds.clone();
        pred_locals.insert(v, self.eval_expr_element_domain(cset, &base_locals));
        pred_lbounds.insert(v, self.eval_elem_bound_here(cset, &base_lbounds));
        let pred_env = base_env.with_local(v, cset_elem_shape);
        if !self.check_choose_bool(cpred, &pred_env, &pred_locals, &pred_lbounds) {
            return None;
        }
        if let ExprKind::SetMap { expr: rec_expr, bounds } = &*cset.kind {
            if let [Bound { vars: BoundVars::Many(pids), set: dom_set }] = bounds.as_slice() {
                if let [p_id] = pids.as_slice() {
                    return self.lower_comprehension_proj(v, *p_id, rec_expr, dom_set, cpred, field, keys, aux);
                }
            }
        }
        let (msg_var, combined_pred) = match &*cset.kind {
            ExprKind::SetFilter { bound, pred: fpred } => {
                let BoundVars::Many(ids) = &bound.vars else { return None };
                let [fid] = ids.as_slice() else { return None };
                let mv = variable(&bound.set, false)?;
                let sub = subst_local(fpred, *fid, &Expr::new(ExprKind::Local(v), cset.span));
                (mv, Expr::new(ExprKind::And(vec![sub, cpred.clone()]), cpred.span))
            }
            _ => (variable(cset, false)?, cpred.clone()),
        };
        let VarShape::MsgSet { mask, msg_id, ref fields, ref key_field, ref val_field } = self.shapes[msg_var.idx()].clone() else {
            return None;
        };
        if val_field.as_ref() != Some(field) {
            return None;
        }
        let mut conjuncts = Vec::new();
        flatten_and(&combined_pred, &mut conjuncts);
        let mut pinned: Option<(usize, Expr)> = None;
        for (idx, c) in conjuncts.iter().enumerate() {
            if let ExprKind::Builtin { op: B::Eq, args } = &*c.kind {
                if let [lhs, rhs] = args.as_slice() {
                    if is_local_field(lhs, v, field) && !mentions_local(rhs, v) {
                        pinned = Some((idx, rhs.clone()));
                        break;
                    }
                    if is_local_field(rhs, v, field) && !mentions_local(lhs, v) {
                        pinned = Some((idx, lhs.clone()));
                        break;
                    }
                }
            }
        }
        let mut scope = keys.to_vec();
        scope.insert(0, (v, mask));
        let mut aux2 = aux.clone();
        aux2.msg_vars
            .insert(0, MsgBoundVar { local: v, fields: fields.clone(), key_field: key_field.clone(), val_field: val_field.clone() });
        if let Some((pidx, pexpr)) = pinned {
            if self.check_choose_expr(&pexpr, &base_env, &base_locals, &base_lbounds).is_some() {
                if let Some(pinned_pure) = self.pure_expr(&pexpr, keys, aux) {
                    let rest: Vec<Expr> = conjuncts.iter().enumerate().filter(|(i, _)| *i != pidx).map(|(_, &e)| e.clone()).collect();
                    let filter_pure = self.pure_tests(&rest, &scope, &aux2)?;
                    self.used_choose = true;
                    return Some(format!("(ProjKind.msgPinned ⟨{msg_id}, by decide⟩ {filter_pure} {pinned_pure})"));
                }
            }
        }
        let filter_pure = self.pure_test(&combined_pred, &scope, &aux2)?;
        self.req_uniform_msgs.insert(msg_id);
        self.used_choose = true;
        Some(format!("(ProjKind.msgUniform ⟨{msg_id}, by decide⟩ {filter_pure})"))
    }

    #[allow(clippy::too_many_arguments)] // lowers a SetMap comprehension projected CHOOSE with its bound key and field context
    fn lower_comprehension_proj(
        &mut self,
        v: LocalId,
        p_id: LocalId,
        rec_expr: &Expr,
        dom_set: &Expr,
        cpred: &Expr,
        field: &Arc<str>,
        keys: &[(LocalId, GroupMask)],
        aux: &AuxScope,
    ) -> Option<String> {
        let (base_locals, base_lbounds) = self.choose_scope_env(keys, aux);
        let base_env = self.choose_check_env(keys, aux);
        let ExprKind::Record(fs) = &*rec_expr.kind else { return None };
        let (_, val_expr) = fs.iter().find(|(k, _)| k == field)?;
        if mentions_local(val_expr, p_id) || self.check_choose_expr(val_expr, &base_env, &base_locals, &base_lbounds).is_none() {
            return None;
        }
        let (mask, dom_filter_opt) = if let Some(exact) = self.domains.exact_set(dom_set) {
            let (m, fixed) = group_mask_exact(self.groups, &exact)?;
            if m == 0 || !fixed.is_empty() {
                return None;
            }
            (m, None)
        } else {
            let m = self.keyset_expr_mask(dom_set, keys, aux)?;
            if m == 0 {
                return None;
            }
            let mut scope = keys.to_vec();
            scope.insert(0, (p_id, m));
            let df = self.key_in_set_pure(KeyRef::Bound(0), m, dom_set, &scope, aux)?;
            (m, Some(df))
        };
        let val_pure = self.pure_expr(val_expr, keys, aux)?;
        let sub_pred = simplify_record_fields(&subst_local(cpred, v, rec_expr));
        let mut pred_locals = base_locals;
        let mut pred_lbounds = base_lbounds;
        pred_locals.insert(p_id, self.mask_domain(mask));
        pred_lbounds.insert(p_id, ValBound::Top);
        let pred_env = base_env.with_local(p_id, self.totality.group_key_shape(mask));
        if !self.check_choose_bool(&sub_pred, &pred_env, &pred_locals, &pred_lbounds) {
            return None;
        }
        let mut scope = keys.to_vec();
        scope.insert(0, (p_id, mask));
        let mut filter_pure = self.pure_test(&sub_pred, &scope, aux)?;
        if let Some(df) = dom_filter_opt {
            filter_pure = bounded(format!("(PureTest.conj {df} {filter_pure})"))?;
        }
        self.used_choose = true;
        Some(format!("(ProjKind.keyConst {} {filter_pure} {val_pure})", self.mask_lean(mask)))
    }

    fn lower_unique_kind(
        &mut self,
        v: LocalId,
        cset: &Expr,
        cpred: &Expr,
        keys: &[(LocalId, GroupMask)],
        aux: &AuxScope,
    ) -> Option<(String, GroupMask)> {
        let (base_locals, base_lbounds) = self.choose_scope_env(keys, aux);
        let base_env = self.choose_check_env(keys, aux);
        self.check_choose_expr(cset, &base_env, &base_locals, &base_lbounds)?;
        let (base_set, combined_pred) = match &*cset.kind {
            ExprKind::SetFilter { bound, pred: fpred } => {
                let BoundVars::Many(ids) = &bound.vars else { return None };
                let [fid] = ids.as_slice() else { return None };
                let sub = subst_local(fpred, *fid, &Expr::new(ExprKind::Local(v), cset.span));
                (&bound.set, Expr::new(ExprKind::And(vec![sub, cpred.clone()]), cpred.span))
            }
            _ => (cset, cpred.clone()),
        };

        let mut flag_from_set: Option<(usize, GroupMask)> = None;
        let mask = if let Some(exact) = self.domains.exact_set(base_set) {
            let (m, fixed) = group_mask_exact(self.groups, &exact)?;
            if m == 0 || !fixed.is_empty() {
                return None;
            }
            m
        } else if let Some(sv) = variable(base_set, false) {
            if let VarShape::KeySetFlag { mask, flag_id } = self.shapes[sv.idx()] {
                flag_from_set = Some((flag_id, mask));
                mask
            } else {
                return None;
            }
        } else {
            return None;
        };

        let mut pred_locals = base_locals;
        let mut pred_lbounds = base_lbounds;
        pred_locals.insert(v, self.mask_domain(mask));
        pred_lbounds.insert(v, ValBound::Top);
        let pred_env = base_env.with_local(v, self.totality.group_key_shape(mask));
        if !self.check_choose_bool(&combined_pred, &pred_env, &pred_locals, &pred_lbounds) {
            return None;
        }

        let mut conjuncts = Vec::new();
        flatten_and(&combined_pred, &mut conjuncts);

        if flag_from_set.is_none() && conjuncts.len() == 2 {
            if let Some(q_expr) = match_only_pattern(v, base_set, conjuncts[0], conjuncts[1], self.domains, self.groups, mask) {
                let mut scope = keys.to_vec();
                scope.insert(0, (v, mask));
                let q_pure = self.pure_test(q_expr, &scope, aux)?;
                self.used_choose = true;
                return Some((format!("(UniqueKind.only {} {q_pure})", self.mask_lean(mask)), mask));
            }
        }

        if let Some(eq_res) = self.try_unique_eq(v, base_set, mask, flag_from_set.is_some(), &conjuncts, cset.span, keys, aux) {
            return Some(eq_res);
        }

        if let Some((flag_id, fmask)) = flag_from_set {
            let mut scope = keys.to_vec();
            scope.insert(0, (v, mask));
            let extra_pure = self.pure_test(&combined_pred, &scope, aux)?;
            self.req_at_most_one_flags.insert((flag_id, fmask));
            self.used_choose = true;
            return Some((format!("(UniqueKind.atMostOneFlag {} ⟨{flag_id}, by decide⟩ {extra_pure})", self.mask_lean(mask)), mask));
        }
        for (idx, c) in conjuncts.iter().enumerate() {
            if let Some((flag_id, fmask)) = self.match_flag_conjunct(v, c) {
                let eff_mask = mask & fmask;
                if eff_mask == 0 {
                    continue;
                }
                let mut scope = keys.to_vec();
                scope.insert(0, (v, eff_mask));
                let rest: Vec<Expr> = conjuncts.iter().enumerate().filter(|(i, _)| *i != idx).map(|(_, &e)| e.clone()).collect();
                let extra_pure = self.pure_tests(&rest, &scope, aux)?;
                self.req_at_most_one_flags.insert((flag_id, fmask));
                self.used_choose = true;
                return Some((
                    format!("(UniqueKind.atMostOneFlag {} ⟨{flag_id}, by decide⟩ {extra_pure})", self.mask_lean(eff_mask)),
                    eff_mask,
                ));
            }
        }
        None
    }

    #[allow(clippy::too_many_arguments)] // matches UniqueKind.eq over conjuncts while preserving optional KeySetFlag membership
    fn try_unique_eq(
        &mut self,
        v: LocalId,
        base_set: &Expr,
        mask: GroupMask,
        has_flag_set: bool,
        conjuncts: &[&Expr],
        span: Span,
        keys: &[(LocalId, GroupMask)],
        aux: &AuxScope,
    ) -> Option<(String, GroupMask)> {
        for (idx, c) in conjuncts.iter().enumerate() {
            if let ExprKind::Builtin { op: B::Eq, args } = &*c.kind {
                if let [lhs, rhs] = args.as_slice() {
                    let target_opt = if matches!(&*lhs.kind, ExprKind::Local(l) if *l == v) && !mentions_local(rhs, v) {
                        Some(rhs)
                    } else if matches!(&*rhs.kind, ExprKind::Local(l) if *l == v) && !mentions_local(lhs, v) {
                        Some(lhs)
                    } else {
                        None
                    };
                    if let Some(texpr) = target_opt {
                        if let Some(tkref) = self.key_or_fixed_ref(texpr, keys, aux) {
                            let mut scope = keys.to_vec();
                            scope.insert(0, (v, mask));
                            let mut rest: Vec<Expr> =
                                conjuncts.iter().enumerate().filter(|(i, _)| *i != idx).map(|(_, &e)| e.clone()).collect();
                            if has_flag_set {
                                rest.insert(
                                    0,
                                    Expr::new(
                                        ExprKind::Builtin { op: B::In, args: vec![Expr::new(ExprKind::Local(v), span), base_set.clone()] },
                                        span,
                                    ),
                                );
                            }
                            let extra_pure = self.pure_tests(&rest, &scope, aux)?;
                            self.used_choose = true;
                            return Some((format!("(UniqueKind.eq {} {} {extra_pure})", self.mask_lean(mask), tkref.lean()), mask));
                        }
                    }
                }
            }
        }
        None
    }

    fn match_flag_conjunct(&self, v: LocalId, c: &Expr) -> Option<(usize, GroupMask)> {
        match &*c.kind {
            ExprKind::Builtin { op: B::In, args } if args.len() == 2 => {
                if matches!(&*args[0].kind, ExprKind::Local(l) if *l == v) {
                    let sv = variable(&args[1], false)?;
                    if let VarShape::KeySetFlag { mask, flag_id } = self.shapes[sv.idx()] {
                        return Some((flag_id, mask));
                    }
                }
                None
            }
            ExprKind::FnApp { func, args } if args.len() == 1 => {
                if matches!(&*args[0].kind, ExprKind::Local(l) if *l == v) {
                    if let Some((mask, flag_id)) = self.bool_map_flag_target(func) {
                        return Some((flag_id, mask));
                    }
                }
                None
            }
            ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 => {
                if matches!(&*args[1].kind, ExprKind::Bool(true)) {
                    self.match_flag_conjunct(v, &args[0])
                } else if matches!(&*args[0].kind, ExprKind::Bool(true)) {
                    self.match_flag_conjunct(v, &args[1])
                } else {
                    None
                }
            }
            _ => None,
        }
    }
}

fn flatten_and<'e>(e: &'e Expr, out: &mut Vec<&'e Expr>) {
    match &*e.kind {
        ExprKind::And(es) => es.iter().for_each(|x| flatten_and(x, out)),
        _ => out.push(e),
    }
}

fn is_local_field(e: &Expr, v: LocalId, field: &Arc<str>) -> bool {
    matches!(&*e.kind, ExprKind::Field { record, field: f } if f == field && matches!(&*record.kind, ExprKind::Local(l) if *l == v))
}

fn simplify_record_fields(e: &Expr) -> Expr {
    let mut out = e.clone();
    visit::children_mut(&mut out, &mut |c| *c = simplify_record_fields(c));
    if let ExprKind::Field { record, field } = &*out.kind {
        if let ExprKind::Record(fs) = &*record.kind {
            if let Some((_, val)) = fs.iter().find(|(k, _)| k == field) {
                return val.clone();
            }
        }
    }
    out
}

fn match_only_pattern<'a>(
    x: LocalId,
    set: &Expr,
    q: &'a Expr,
    all: &'a Expr,
    domains: &Domains,
    groups: &[GroupInfo],
    expected_mask: GroupMask,
) -> Option<&'a Expr> {
    let ExprKind::Quant { kind: QuantKind::Forall, bounds, body: imp } = &*all.kind else { return None };
    let [Bound { vars: BoundVars::Many(ys), set: s2 }] = bounds.as_slice() else { return None };
    let [y] = ys.as_slice() else { return None };
    if mentions_local(s2, x) {
        return None;
    }
    let exact2 = domains.exact_set(s2)?;
    let (m2, f2) = group_mask_exact(groups, &exact2)?;
    if m2 != expected_mask || !f2.is_empty() {
        return None;
    }
    let _ = set;
    let ExprKind::Builtin { op: B::Implies, args } = &*imp.kind else { return None };
    let [qy, eq] = args.as_slice() else { return None };
    let ExprKind::Builtin { op: B::Eq, args: eargs } = &*eq.kind else { return None };
    let [e0, e1] = eargs.as_slice() else { return None };
    let is_loc = |e: &Expr, id: LocalId| matches!(&*e.kind, ExprKind::Local(l) if *l == id);
    let names_both = *y != x && ((is_loc(e0, *y) && is_loc(e1, x)) || (is_loc(e0, x) && is_loc(e1, *y)));
    if !names_both || !same_expr_renamed(qy, q, *y, x) {
        return None;
    }
    Some(q)
}

/// Exact capture-avoiding alpha-equivalence check verifying `a == b[old_var := new_var]`
/// with `new_var` not appearing free in `b` and `old_var` replaced at every occurrence.
fn same_expr_renamed(a: &Expr, b: &Expr, new_var: LocalId, old_var: LocalId) -> bool {
    let all = |xs: &[Expr], ys: &[Expr]| xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| same_expr_renamed(x, y, new_var, old_var));
    match (&*a.kind, &*b.kind) {
        (ExprKind::Local(la), ExprKind::Local(lb)) => {
            if *lb == old_var {
                *la == new_var
            } else {
                *lb != new_var && la == lb
            }
        }
        (ExprKind::Var(x), ExprKind::Var(y)) => x == y,
        (ExprKind::Const(x), ExprKind::Const(y)) => x == y,
        (ExprKind::Num(x), ExprKind::Num(y)) => x == y,
        (ExprKind::Str(x), ExprKind::Str(y)) => x == y,
        (ExprKind::Bool(x), ExprKind::Bool(y)) => x == y,
        (ExprKind::Builtin { op: o, args: xs }, ExprKind::Builtin { op: p, args: ys }) => o == p && all(xs, ys),
        (ExprKind::And(xs), ExprKind::And(ys)) | (ExprKind::Or(xs), ExprKind::Or(ys)) => all(xs, ys),
        (ExprKind::SetEnum(xs), ExprKind::SetEnum(ys)) | (ExprKind::Tuple(xs), ExprKind::Tuple(ys)) => all(xs, ys),
        (ExprKind::FnApp { func: f, args: xs }, ExprKind::FnApp { func: g, args: ys }) => {
            same_expr_renamed(f, g, new_var, old_var) && all(xs, ys)
        }
        (ExprKind::Field { record: x, field: f }, ExprKind::Field { record: y, field: g }) => {
            f == g && same_expr_renamed(x, y, new_var, old_var)
        }
        _ => false,
    }
}

fn is_state_modal_barrier(e: &Expr) -> bool {
    matches!(
        &*e.kind,
        ExprKind::TemporalQuant { .. }
            | ExprKind::Let { .. }
            | ExprKind::InstVar { .. }
            | ExprKind::BoxAction { .. }
            | ExprKind::AngleAction { .. }
            | ExprKind::Fairness { .. }
            | ExprKind::Builtin {
                op: B::Prime | B::Enabled | B::Unchanged | B::Always | B::Eventually | B::LeadsTo | B::Compose | B::WhilePlus,
                ..
            }
    )
}

fn is_choice_hoist_barrier(e: &Expr) -> bool {
    is_state_modal_barrier(e)
        || matches!(
            &*e.kind,
            ExprKind::And(_)
                | ExprKind::Or(_)
                | ExprKind::If { .. }
                | ExprKind::Case { .. }
                | ExprKind::Quant { .. }
                | ExprKind::QuantUnbounded { .. }
                | ExprKind::Choose { .. }
                | ExprKind::FnConstruct { .. }
                | ExprKind::SetFilter { .. }
                | ExprKind::SetMap { .. }
                | ExprKind::Lambda { .. }
                | ExprKind::Apply { .. }
                | ExprKind::Builtin { op: B::Implies | B::Equiv, .. }
        )
}

pub(super) fn find_first_choice_node(e: &Expr, fold_vars: &HashMap<LocalId, Option<Expr>>) -> Option<Expr> {
    if let ExprKind::Field { record, .. } = &*e.kind {
        if let ExprKind::Choose { vars: BoundVars::Many(ids), set: Some(_), .. } = &*record.kind {
            if let [v] = ids.as_slice() {
                if !fold_vars.contains_key(v) {
                    return Some(e.clone());
                }
            }
        }
    }
    if matches!(&*e.kind, ExprKind::Choose { .. }) {
        return Some(e.clone());
    }
    if is_choice_hoist_barrier(e) {
        return None;
    }
    let mut found = None;
    visit::children(e, &mut |c| {
        if found.is_none() && expr_has_choose(c) {
            found = find_first_choice_node(c, fold_vars);
        }
    });
    found
}

pub(super) fn replace_cached_choices(e: &Expr, cache: &[(Expr, Expr)], fold_vars: &HashMap<LocalId, Option<Expr>>) -> Expr {
    if is_state_modal_barrier(e) {
        return e.clone();
    }
    for (orig, repl) in cache {
        if ast_equiv(e, orig, fold_vars) {
            return repl.clone();
        }
    }
    let mut out = e.clone();
    visit::children_mut(&mut out, &mut |c| *c = replace_cached_choices(c, cache, fold_vars));
    out
}

pub(super) fn ast_equiv(a: &Expr, b: &Expr, fold_vars: &HashMap<LocalId, Option<Expr>>) -> bool {
    let all = |xs: &[Expr], ys: &[Expr]| xs.len() == ys.len() && xs.iter().zip(ys).all(|(x, y)| ast_equiv(x, y, fold_vars));
    match (&*a.kind, &*b.kind) {
        (ExprKind::Local(x), ExprKind::Local(y)) => x == y,
        (ExprKind::Var(x), ExprKind::Var(y)) => x == y,
        (ExprKind::Const(x), ExprKind::Const(y)) => x == y,
        (ExprKind::Num(x), ExprKind::Num(y)) => x == y,
        (ExprKind::Str(x), ExprKind::Str(y)) => x == y,
        (ExprKind::Bool(x), ExprKind::Bool(y)) => x == y,
        (ExprKind::Builtin { op: o, args: xs }, ExprKind::Builtin { op: p, args: ys }) => o == p && all(xs, ys),
        (ExprKind::And(xs), ExprKind::And(ys)) | (ExprKind::Or(xs), ExprKind::Or(ys)) => all(xs, ys),
        (ExprKind::SetEnum(xs), ExprKind::SetEnum(ys)) | (ExprKind::Tuple(xs), ExprKind::Tuple(ys)) => all(xs, ys),
        (ExprKind::Record(xs), ExprKind::Record(ys)) => {
            xs.len() == ys.len() && xs.iter().zip(ys).all(|((kx, vx), (ky, vy))| kx == ky && ast_equiv(vx, vy, fold_vars))
        }
        (ExprKind::FnApp { func: f, args: xs }, ExprKind::FnApp { func: g, args: ys }) => ast_equiv(f, g, fold_vars) && all(xs, ys),
        (ExprKind::Field { record: x, field: f }, ExprKind::Field { record: y, field: g }) => f == g && ast_equiv(x, y, fold_vars),
        (
            ExprKind::Choose { vars: BoundVars::Many(vx), set: Some(sx), body: bx },
            ExprKind::Choose { vars: BoundVars::Many(vy), set: Some(sy), body: by },
        ) if vx.len() == 1 && vy.len() == 1 => {
            let fold_ok = match (fold_vars.get(&vx[0]), fold_vars.get(&vy[0])) {
                (None, None) | (Some(None), Some(None)) => true,
                (Some(Some(sup_x)), Some(Some(sup_y))) => ast_equiv(sup_x, sup_y, fold_vars),
                _ => false,
            };
            fold_ok
                && ast_equiv(sx, sy, fold_vars)
                && ast_equiv(
                    &subst_local(bx, vx[0], &Expr::new(ExprKind::Local(LocalId(u32::MAX - 1)), bx.span)),
                    &subst_local(by, vy[0], &Expr::new(ExprKind::Local(LocalId(u32::MAX - 1)), by.span)),
                    fold_vars,
                )
        }
        _ => false,
    }
}
