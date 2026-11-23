//! Step-branch expansion and per-shape update lowering (`Write`, `SlotExpr`, and
//! core fixed-part guards) for `keyed`.

use super::{
    expressions, group_mask_exact, independent, subst_local, unchanged, variable, Atom, Branch, Case, Emitter, FieldShape, GroupMask,
    KeyRef, Locals, RecordMsgShape, VarShape,
};
use crate::{builtins::Builtin as B, hir::*};
use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

impl Emitter<'_> {
    pub(super) fn cases_for_branch(&mut self, b: &Branch, out: &mut Vec<Case>) -> Option<()> {
        let mut clean = Vec::new();
        self.expand_mixed_bounds(b, 0, &mut clean)?;
        for cb in &clean {
            out.push(self.case(cb)?);
        }
        Some(())
    }

    fn expand_mixed_bounds(&self, b: &Branch, idx: usize, out: &mut Vec<Branch>) -> Option<()> {
        if out.len() > 64 {
            return None;
        }
        if idx >= b.bounds.len() {
            out.push(b.clone());
            return Some(());
        }
        let bnd = &b.bounds[idx];
        let BoundVars::Many(ids) = &bnd.vars else { return None };
        if let Some(exact) = self.domains.exact_set(&bnd.set) {
            if let Some((mask, fixed)) = group_mask_exact(self.groups, &exact) {
                if mask != 0 && !fixed.is_empty() {
                    if fixed.len() > 8 || ids.len() > 2 {
                        return None;
                    }
                    let mut variants = vec![(Vec::<LocalId>::new(), b.terms.clone())];
                    for &id in ids {
                        let mut next_v = Vec::new();
                        for (kept, terms) in variants {
                            let mut kept_k = kept.clone();
                            kept_k.push(id);
                            next_v.push((kept_k, terms.clone()));
                            for atom in &fixed {
                                let aexpr = self.domains.atom_expr(atom, bnd.set.span)?;
                                let terms_f: Vec<_> = terms.iter().map(|t| subst_local(t, id, &aexpr)).collect();
                                next_v.push((kept.clone(), terms_f));
                            }
                        }
                        variants = next_v;
                        if variants.len() > 64 {
                            return None;
                        }
                    }
                    let key_set_expr = self.key_groups_expr(mask, bnd.set.span)?;
                    for (kept, terms) in variants {
                        let has_kept = !kept.is_empty();
                        let mut nb = Branch { bounds: b.bounds[..idx].to_vec(), terms };
                        if has_kept {
                            nb.bounds.push(Bound { vars: BoundVars::Many(kept), set: key_set_expr.clone() });
                        }
                        nb.bounds.extend_from_slice(&b.bounds[idx + 1..]);
                        let next_idx = if has_kept { idx + 1 } else { idx };
                        self.expand_mixed_bounds(&nb, next_idx, out)?;
                    }
                    return Some(());
                }
            }
        }
        self.expand_mixed_bounds(b, idx + 1, out)
    }

    fn key_groups_expr(&self, mask: GroupMask, span: Span) -> Option<Expr> {
        let mut parts = Vec::new();
        for (gi, g) in self.groups.iter().enumerate() {
            if (mask & (1 << gi)) != 0 {
                let mut found = None;
                for c_idx in 0..self.num_consts as u32 {
                    let e = Expr::new(ExprKind::Const(ConstId(c_idx)), span);
                    if self.domains.exact_set(&e).as_ref() == Some(&g.keys) {
                        found = Some(e);
                        break;
                    }
                }
                parts.push(found?);
            }
        }
        let mut it = parts.into_iter();
        let mut acc = it.next()?;
        for p in it {
            acc = Expr::new(ExprKind::Builtin { op: B::Cup, args: vec![acc, p] }, span);
        }
        Some(acc)
    }

    fn case(&mut self, b: &Branch) -> Option<Case> {
        let hidden = self.hidden_updates(b)?;
        let locals = self.domains.locals(&b.bounds);
        let mut keys: Vec<(LocalId, GroupMask)> = vec![];
        let mut guards: Vec<Expr> = vec![];
        let mut extra_test_strs: Vec<String> = vec![];

        for bound in &b.bounds {
            let BoundVars::Many(ids) = &bound.vars else { return None };
            if let Some(exact) = self.domains.exact_set(&bound.set) {
                let (mask, fixed) = group_mask_exact(self.groups, &exact)?;
                if mask != 0 && fixed.is_empty() {
                    for &id in ids {
                        let idx = keys.len();
                        keys.push((id, mask));
                        extra_test_strs.push(format!("(Test.inGroup (KeyRef.bound {idx}) {})", self.mask_lean(mask)));
                    }
                    continue;
                }
            }
            if let Some(v) = variable(&bound.set, false) {
                if let VarShape::KeySet { mask, has_fixed: false, .. } = self.shapes[v.idx()] {
                    for &id in ids {
                        let idx = keys.len();
                        keys.push((id, mask));
                        extra_test_strs.push(format!("(Test.inGroup (KeyRef.bound {idx}) {})", self.mask_lean(mask)));
                        guards.push(Expr::new(
                            ExprKind::Builtin { op: B::In, args: vec![Expr::new(ExprKind::Local(id), bound.set.span), bound.set.clone()] },
                            bound.set.span,
                        ));
                    }
                    continue;
                }
            }
            for id in ids {
                if !independent(locals.get(id)?, self.all_keys) {
                    return None;
                }
                guards.push(Expr::new(
                    ExprKind::Builtin { op: B::In, args: vec![Expr::new(ExprKind::Local(*id), bound.set.span), bound.set.clone()] },
                    bound.set.span,
                ));
            }
        }

        let mut writes: Vec<String> = vec![];
        let mut slot_writes: Vec<String> = vec![];
        let mut consumed_terms: Vec<bool> = vec![false; b.terms.len()];
        let mut core_update_guards: Vec<String> = vec![];

        for &var in &self.omitted {
            match primed_binding(b, var) {
                PrimedBinding::Eq { term_idx, .. } => consumed_terms[term_idx] = true,
                PrimedBinding::Unchanged => {}
                PrimedBinding::None | PrimedBinding::Ambiguous => return None,
            }
        }

        for vi in 0..self.shapes.len() {
            let var = VarId(vi as u32);
            if self.omitted.contains(&var) {
                continue;
            }
            let shape = self.shapes[vi].clone();
            match shape {
                VarShape::Core => {}
                VarShape::FixedMap { mask, map_id } => match primed_binding(b, var) {
                    PrimedBinding::Unchanged => continue,
                    PrimedBinding::Eq { term_idx, rhs } => {
                        consumed_terms[term_idx] = true;
                        if variable(&rhs, false) == Some(var) {
                            continue;
                        }
                        self.emit_map_update(var, map_id, mask, &rhs, &keys, &mut writes)?;
                    }
                    PrimedBinding::None | PrimedBinding::Ambiguous => return None,
                },
                VarShape::MixedMap { mask, fixed_keys, map_id } => match primed_binding(b, var) {
                    PrimedBinding::Unchanged => {
                        core_update_guards.push(self.core_leaf_from_desc(format!("MixedMap fixed-part unchanged: var {}", var.idx())));
                        continue;
                    }
                    PrimedBinding::Eq { term_idx, rhs } => {
                        consumed_terms[term_idx] = true;
                        if variable(&rhs, false) == Some(var) {
                            core_update_guards.push(self.core_leaf_from_desc(format!("MixedMap fixed-part unchanged: var {}", var.idx())));
                            continue;
                        }
                        self.emit_mixed_map_update(var, map_id, mask, &fixed_keys, &rhs, &keys, &mut writes, &mut core_update_guards)?;
                    }
                    PrimedBinding::None | PrimedBinding::Ambiguous => return None,
                },
                VarShape::ScalarSlot { mask, has_fixed, slot_id } => match primed_binding(b, var) {
                    PrimedBinding::Unchanged => continue,
                    PrimedBinding::Eq { term_idx, rhs } => {
                        consumed_terms[term_idx] = true;
                        if variable(&rhs, false) == Some(var) {
                            continue;
                        }
                        let se = self.slot_expr(&rhs, mask, has_fixed, &keys)?;
                        slot_writes.push(format!("⟨⟨{slot_id}, by decide⟩, {se}⟩"));
                    }
                    PrimedBinding::None => {
                        let (in_idx, set_expr) = self.unique_primed_membership(b, var)?;
                        let exact = self.domains.exact_set(&set_expr)?;
                        let (set_mask, fixed) = group_mask_exact(self.groups, &exact)?;
                        if set_mask == 0 || !fixed.is_empty() || (set_mask & !mask) != 0 {
                            return None;
                        }
                        let fresh = self.alloc_local();
                        let idx = keys.len();
                        keys.push((fresh, set_mask));
                        extra_test_strs.push(format!("(Test.inGroup (KeyRef.bound {idx}) {})", self.mask_lean(set_mask)));
                        slot_writes.push(format!("⟨⟨{slot_id}, by decide⟩, (SlotExpr.ref (KeyRef.bound {idx}))⟩"));
                        consumed_terms[in_idx] = true;
                    }
                    PrimedBinding::Ambiguous => return None,
                },
                VarShape::KeySet { mask, has_fixed, map_id } => match primed_binding(b, var) {
                    PrimedBinding::Unchanged => {
                        if has_fixed {
                            core_update_guards.push(self.core_leaf_from_desc(format!("KeySet fixed-part unchanged: var {}", var.idx())));
                        }
                        continue;
                    }
                    PrimedBinding::Eq { term_idx, rhs } => {
                        consumed_terms[term_idx] = true;
                        if variable(&rhs, false) == Some(var) {
                            if has_fixed {
                                core_update_guards
                                    .push(self.core_leaf_from_desc(format!("KeySet fixed-part unchanged: var {}", var.idx())));
                            }
                            continue;
                        }
                        self.emit_keyset_update(var, map_id, mask, has_fixed, &rhs, &keys, &mut writes, &mut core_update_guards)?;
                    }
                    PrimedBinding::None | PrimedBinding::Ambiguous => return None,
                },
                VarShape::RecordSet { keyed, has_free } => match primed_binding(b, var) {
                    PrimedBinding::Unchanged => {
                        if has_free {
                            core_update_guards.push(self.core_leaf_from_desc(format!("RecordSet free-part unchanged: var {}", var.idx())));
                        }
                        continue;
                    }
                    PrimedBinding::Eq { term_idx, rhs } => {
                        consumed_terms[term_idx] = true;
                        if variable(&rhs, false) == Some(var) {
                            if has_free {
                                core_update_guards
                                    .push(self.core_leaf_from_desc(format!("RecordSet free-part unchanged: var {}", var.idx())));
                            }
                            continue;
                        }
                        self.emit_recordset_update(var, &keyed, has_free, &rhs, &keys, &mut writes, &mut core_update_guards)?;
                    }
                    PrimedBinding::None | PrimedBinding::Ambiguous => return None,
                },
                VarShape::FixedRecord { fields } => match primed_binding(b, var) {
                    PrimedBinding::Unchanged => {
                        if fields.values().any(|f| matches!(f, FieldShape::Core)) {
                            core_update_guards
                                .push(self.core_leaf_from_desc(format!("FixedRecord core-part unchanged: var {}", var.idx())));
                        }
                        continue;
                    }
                    PrimedBinding::Eq { term_idx, rhs } => {
                        consumed_terms[term_idx] = true;
                        if variable(&rhs, false) == Some(var) {
                            if fields.values().any(|f| matches!(f, FieldShape::Core)) {
                                core_update_guards
                                    .push(self.core_leaf_from_desc(format!("FixedRecord core-part unchanged: var {}", var.idx())));
                            }
                            continue;
                        }
                        self.emit_fixed_record_update(var, &fields, &rhs, &keys, &mut writes, &mut slot_writes, &mut core_update_guards)?;
                    }
                    PrimedBinding::None | PrimedBinding::Ambiguous => return None,
                },
            }
        }

        for (idx, term) in b.terms.iter().enumerate() {
            if consumed_terms[idx] {
                continue;
            }
            let term = if let ExprKind::Builtin { op: B::Unchanged, args } = &*term.kind {
                let [arg] = args.as_slice() else { return None };
                Expr::new(ExprKind::Builtin { op: B::Unchanged, args: vec![self.frames(arg)?] }, term.span)
            } else {
                term.clone()
            };
            guards.push(term);
        }

        let mut guard = self.tests(&guards, &keys)?;
        for extra in extra_test_strs.into_iter().chain(core_update_guards) {
            guard = expressions::bounded(format!("(Test.conj {guard} {extra})"))?;
        }
        Some(Case { hidden, guard, writes, slot_writes, keys })
    }

    fn unique_primed_membership(&self, b: &Branch, v: VarId) -> Option<(usize, Expr)> {
        let mut found = Vec::new();
        for (idx, term) in b.terms.iter().enumerate() {
            if let ExprKind::Builtin { op: B::In, args } = &*term.kind {
                if args.len() == 2 && variable(&args[0], true) == Some(v) {
                    found.push((idx, args[1].clone()));
                }
            }
        }
        if found.len() == 1 {
            found.pop()
        } else {
            None
        }
    }

    fn emit_map_update(
        &mut self,
        var: VarId,
        map_id: usize,
        mask: GroupMask,
        rhs: &Expr,
        keys: &[(LocalId, GroupMask)],
        writes: &mut Vec<String>,
    ) -> Option<()> {
        let base_expr = Expr::new(ExprKind::Var(var), rhs.span);
        self.emit_map_update_expr(&base_expr, map_id, mask, rhs, keys, writes)
    }

    fn emit_map_update_expr(
        &mut self,
        base_target: &Expr,
        map_id: usize,
        mask: GroupMask,
        rhs: &Expr,
        keys: &[(LocalId, GroupMask)],
        writes: &mut Vec<String>,
    ) -> Option<()> {
        if expr_is_same_map_target(rhs, base_target) {
            return Some(());
        }
        match &*rhs.kind {
            ExprKind::Except { base, updates } => {
                if !expr_is_same_map_target(base, base_target) || updates.is_empty() {
                    return None;
                }
                let mut grouped: Vec<(KeyRef, Vec<(Vec<ExceptKey>, Expr)>)> = Vec::new();
                for (path, value) in updates {
                    let (ExceptKey::Index(args), rest) = path.split_first()? else { return None };
                    let [arg] = args.as_slice() else { return None };
                    let (kref, k_mask, _) = self.key_ref(arg, keys)?;
                    if (k_mask & !mask) != 0 {
                        return None;
                    }
                    if let Some(last) = grouped.last_mut() {
                        if last.0 == kref {
                            last.1.push((rest.to_vec(), value.clone()));
                            continue;
                        }
                    }
                    grouped.push((kref, vec![(rest.to_vec(), value.clone())]));
                }
                if grouped.len() > 1 && grouped.iter().any(|(_, ps)| ps.iter().any(|(r, _)| !r.is_empty())) {
                    return None;
                }
                for (kref, patches) in grouped {
                    let mut payload = None;
                    let arg_expr = self.key_ref_expr(kref, keys, rhs.span)?;
                    for (rest, val) in patches {
                        let previous = payload
                            .unwrap_or_else(|| Expr::new(ExprKind::FnApp { func: base.clone(), args: vec![arg_expr.clone()] }, rhs.span));
                        payload = Some(if rest.is_empty() {
                            val
                        } else {
                            Expr::new(ExprKind::Except { base: previous, updates: vec![(rest, val)] }, rhs.span)
                        });
                    }
                    let val_lean = self.value(&payload?, keys)?;
                    writes.push(format!("(Write.point ⟨{map_id}, by decide⟩ {} {val_lean})", kref.lean()));
                }
                Some(())
            }
            ExprKind::FnConstruct { bounds, body } if bounds.len() == 1 => {
                let bnd = &bounds[0];
                let BoundVars::Many(ids) = &bnd.vars else { return None };
                let [id] = ids.as_slice() else { return None };
                let exact = self.domains.exact_set(&bnd.set)?;
                let (bmask, fixed) = group_mask_exact(self.groups, &exact)?;
                if bmask != mask || !fixed.is_empty() {
                    return None;
                }
                let mut scope = keys.to_vec();
                scope.insert(0, (*id, mask));
                let val_lean = self.value(body, &scope)?;
                writes.push(format!("(Write.all ⟨{map_id}, by decide⟩ {} {val_lean})", self.mask_lean(mask)));
                Some(())
            }
            _ => None,
        }
    }

    #[allow(clippy::too_many_arguments)] // threads MixedMap fixed-key obligations and Write output lists together
    fn emit_mixed_map_update(
        &mut self,
        var: VarId,
        map_id: usize,
        mask: GroupMask,
        fixed_keys: &BTreeSet<Atom>,
        rhs: &Expr,
        keys: &[(LocalId, GroupMask)],
        writes: &mut Vec<String>,
        core_guards: &mut Vec<String>,
    ) -> Option<()> {
        let ExprKind::Except { base, updates } = &*rhs.kind else { return None };
        if variable(base, false) != Some(var) || updates.is_empty() {
            return None;
        }
        let mut keyed_updates = Vec::new();
        let mut fixed_updates = Vec::new();
        for (path, val) in updates {
            let (ExceptKey::Index(args), rest) = path.split_first()? else { return None };
            let [arg] = args.as_slice() else { return None };
            if let Some((kref, k_mask, false)) = self.key_ref(arg, keys) {
                if (k_mask & !mask) != 0 {
                    return None;
                }
                keyed_updates.push((kref, rest.to_vec(), val.clone()));
            } else if let Some(atom) = self.domains.atom_value(arg) {
                if !fixed_keys.contains(&atom) {
                    return None;
                }
                fixed_updates.push((arg.clone(), rest.to_vec(), val.clone()));
            } else {
                return None;
            }
        }
        if keyed_updates.len() > 1 && keyed_updates.iter().any(|(_, r, _)| !r.is_empty()) {
            return None;
        }
        for (kref, rest, val) in keyed_updates {
            let arg_expr = self.key_ref_expr(kref, keys, rhs.span)?;
            let previous = Expr::new(ExprKind::FnApp { func: base.clone(), args: vec![arg_expr] }, rhs.span);
            let payload =
                if rest.is_empty() { val } else { Expr::new(ExprKind::Except { base: previous, updates: vec![(rest, val)] }, rhs.span) };
            let val_lean = self.value(&payload, keys)?;
            writes.push(format!("(Write.point ⟨{map_id}, by decide⟩ {} {val_lean})", kref.lean()));
        }
        if fixed_updates.is_empty() {
            core_guards.push(self.core_leaf_from_desc(format!("MixedMap fixed-part unchanged: var {}", var.idx())));
        } else {
            for (arg, rest, val) in fixed_updates {
                if Atom::literal(&arg).is_none() {
                    let arg_leaf = self.leaf(&arg, keys, "Test")?;
                    core_guards.push(arg_leaf);
                }
                let previous = Expr::new(ExprKind::FnApp { func: base.clone(), args: vec![arg.clone()] }, rhs.span);
                let payload = if rest.is_empty() {
                    val
                } else {
                    Expr::new(ExprKind::Except { base: previous, updates: vec![(rest, val)] }, rhs.span)
                };
                let test_leaf = self.leaf(&payload, keys, "Test")?;
                let id = self.atoms.len() - 1;
                self.atoms[id].push_str(&format!("\nMixedMap fixed write var {} at {arg:#?}", var.idx()));
                core_guards.push(test_leaf);
            }
        }
        Some(())
    }

    #[allow(clippy::too_many_arguments)] // threads KeySet fixed-key obligations and Write output lists together
    fn emit_keyset_update(
        &mut self,
        var: VarId,
        map_id: usize,
        mask: GroupMask,
        has_fixed: bool,
        rhs: &Expr,
        keys: &[(LocalId, GroupMask)],
        writes: &mut Vec<String>,
        core_guards: &mut Vec<String>,
    ) -> Option<()> {
        if let Some(added) = self.extract_var_union_elems(var, rhs) {
            let mut key_refs = Vec::new();
            let mut fixed_elems = Vec::new();
            for item in &added {
                if let Some((kref, kmask, false)) = self.key_ref(item, keys) {
                    if (kmask & !mask) != 0 {
                        return None;
                    }
                    key_refs.push(kref);
                } else if independent(&self.domains.value(item, &Locals::new()), self.all_keys) {
                    if !has_fixed {
                        return None;
                    }
                    fixed_elems.push(item.clone());
                } else {
                    return None;
                }
            }
            if !key_refs.is_empty() {
                let true_val = self.const_bool_value(true);
                for kref in key_refs {
                    writes.push(format!("(Write.point ⟨{map_id}, by decide⟩ {} {true_val})", kref.lean()));
                }
            }
            if has_fixed {
                if fixed_elems.is_empty() {
                    core_guards.push(self.core_leaf_from_desc(format!("KeySet fixed-part unchanged: var {}", var.idx())));
                } else {
                    let set_expr = Expr::new(ExprKind::SetEnum(fixed_elems), rhs.span);
                    let leaf = self.leaf(&set_expr, keys, "Test")?;
                    core_guards.push(leaf);
                }
            }
            return Some(());
        }
        let fresh = self.alloc_local();
        let mut scope = keys.to_vec();
        scope.insert(0, (fresh, mask));
        let mem_test = self.key_in_set_expr(KeyRef::Bound(0), mask, rhs, &scope)?;
        let true_val = self.const_bool_value(true);
        let false_val = self.const_bool_value(false);
        let val_lean = format!("(ValueExpr.branch {mem_test} {true_val} {false_val})");
        writes.push(format!("(Write.all ⟨{map_id}, by decide⟩ {} {val_lean})", self.mask_lean(mask)));
        if has_fixed {
            if matches!(&*rhs.kind, ExprKind::SetEnum(es) if es.is_empty()) {
                core_guards.push(self.core_leaf_from_desc(format!("KeySet fixed-part reset to empty: var {}", var.idx())));
            } else if let Some(exact) = self.domains.exact_set(rhs) {
                let (_, fixed) = group_mask_exact(self.groups, &exact)?;
                core_guards.push(self.core_leaf_from_desc(format!("KeySet fixed-part set to {fixed:?}: var {}", var.idx())));
            } else {
                return None;
            }
        }
        Some(())
    }

    #[allow(clippy::too_many_arguments)] // threads RecordSet keyed/free update channels together
    fn emit_recordset_update(
        &mut self,
        var: VarId,
        keyed: &[RecordMsgShape],
        has_free: bool,
        rhs: &Expr,
        keys: &[(LocalId, GroupMask)],
        writes: &mut Vec<String>,
        core_guards: &mut Vec<String>,
    ) -> Option<()> {
        if matches!(&*rhs.kind, ExprKind::SetEnum(es) if es.is_empty()) {
            let empty_val = self.const_empty_set_value();
            for sh in keyed {
                writes.push(format!("(Write.all ⟨{}, by decide⟩ {} {empty_val})", sh.map_id, self.mask_lean(sh.mask)));
            }
            if has_free {
                core_guards.push(self.core_leaf_from_desc(format!("RecordSet free-part reset empty: var {}", var.idx())));
            }
            return Some(());
        }
        let added = self.extract_var_union_elems(var, rhs)?;
        let mut by_shape: BTreeMap<usize, Vec<(KeyRef, Expr)>> = BTreeMap::new();
        let mut free_added: Vec<Expr> = Vec::new();
        for item in &added {
            let ExprKind::Record(fs) = &*item.kind else { return None };
            let mut field_names: Vec<Arc<str>> = fs.iter().map(|(k, _)| k.clone()).collect();
            field_names.sort();
            if let Some(sh) = keyed.iter().find(|sh| sh.fields == field_names) {
                let (_, kexpr) = fs.iter().find(|(k, _)| *k == sh.key_field)?;
                let (kref, kmask, false) = self.key_ref(kexpr, keys)? else { return None };
                if (kmask & !sh.mask) != 0 {
                    return None;
                }
                let rest: Vec<(Arc<str>, Expr)> = fs.iter().filter(|(k, _)| *k != sh.key_field).cloned().collect();
                let rest_rec = Expr::new(ExprKind::Record(rest), item.span);
                by_shape.entry(sh.map_id).or_default().push((kref, rest_rec));
            } else {
                free_added.push(item.clone());
            }
        }
        for sh in keyed {
            let Some(items) = by_shape.get(&sh.map_id) else { continue };
            if items.len() == 1 {
                let (kref, rest_rec) = &items[0];
                let val_lean = self.record_set_add_value(sh.map_id, *kref, rest_rec, keys)?;
                writes.push(format!("(Write.point ⟨{}, by decide⟩ {} {val_lean})", sh.map_id, kref.lean()));
            } else {
                return None;
            }
        }
        if !free_added.is_empty() {
            if !has_free {
                return None;
            }
            for rec in &free_added {
                let leaf = self.leaf(rec, keys, "Test")?;
                let id = self.atoms.len() - 1;
                self.atoms[id].push_str(&format!("\nRecordSet free-part union var {}", var.idx()));
                core_guards.push(leaf);
            }
        } else if has_free {
            core_guards.push(self.core_leaf_from_desc(format!("RecordSet free-part unchanged: var {}", var.idx())));
        }
        Some(())
    }

    #[allow(clippy::too_many_arguments)] // dispatches per-field FixedRecord map, slot, and core updates together
    fn emit_fixed_record_update(
        &mut self,
        var: VarId,
        fields: &BTreeMap<Arc<str>, FieldShape>,
        rhs: &Expr,
        keys: &[(LocalId, GroupMask)],
        writes: &mut Vec<String>,
        slot_writes: &mut Vec<String>,
        core_guards: &mut Vec<String>,
    ) -> Option<()> {
        match &*rhs.kind {
            ExprKind::Except { base, updates } => {
                if variable(base, false) != Some(var) || updates.is_empty() {
                    return None;
                }
                let mut by_field: BTreeMap<Arc<str>, Vec<(Vec<ExceptKey>, Expr)>> = BTreeMap::new();
                for (path, val) in updates {
                    let (ExceptKey::Field(fname), rest) = path.split_first()? else { return None };
                    if !fields.contains_key(fname) {
                        return None;
                    }
                    by_field.entry(fname.clone()).or_default().push((rest.to_vec(), val.clone()));
                }
                for (fname, fshape) in fields {
                    let Some(patches) = by_field.get(fname) else {
                        if matches!(fshape, FieldShape::Core) {
                            core_guards.push(self.core_leaf_from_desc(format!(
                                "FixedRecord core field unchanged: var {}.{}",
                                var.idx(),
                                fname
                            )));
                        }
                        continue;
                    };
                    let field_base =
                        Expr::new(ExprKind::Field { record: Expr::new(ExprKind::Var(var), rhs.span), field: fname.clone() }, rhs.span);
                    match fshape {
                        FieldShape::Core => {
                            let mut payload = None;
                            for (rest, val) in patches {
                                let prev = payload.unwrap_or_else(|| field_base.clone());
                                payload = Some(if rest.is_empty() {
                                    val.clone()
                                } else {
                                    Expr::new(ExprKind::Except { base: prev, updates: vec![(rest.clone(), val.clone())] }, rhs.span)
                                });
                            }
                            let val = payload?;
                            let leaf = self.leaf(&val, keys, "Test")?;
                            let id = self.atoms.len() - 1;
                            self.atoms[id].push_str(&format!("\nFixedRecord core field write: var {}.{}", var.idx(), fname));
                            core_guards.push(leaf);
                        }
                        FieldShape::ScalarSlot { mask, has_fixed, slot_id } => {
                            if patches.len() != 1 || !patches[0].0.is_empty() {
                                return None;
                            }
                            let se = self.slot_expr(&patches[0].1, *mask, *has_fixed, keys)?;
                            slot_writes.push(format!("⟨⟨{slot_id}, by decide⟩, {se}⟩"));
                        }
                        FieldShape::FixedMap { mask, map_id } => {
                            let map_rhs = if patches.len() == 1 && patches[0].0.is_empty() {
                                patches[0].1.clone()
                            } else {
                                Expr::new(ExprKind::Except { base: field_base.clone(), updates: patches.clone() }, rhs.span)
                            };
                            self.emit_map_update_expr(&field_base, *map_id, *mask, &map_rhs, keys, writes)?;
                        }
                    }
                }
                Some(())
            }
            ExprKind::Record(rec_fields) => {
                if rec_fields.len() != fields.len() {
                    return None;
                }
                for (fname, fshape) in fields {
                    let (_, val) = rec_fields.iter().find(|(k, _)| k == fname)?;
                    let field_base =
                        Expr::new(ExprKind::Field { record: Expr::new(ExprKind::Var(var), rhs.span), field: fname.clone() }, rhs.span);
                    match fshape {
                        FieldShape::Core => {
                            let leaf = self.leaf(val, keys, "Test")?;
                            let id = self.atoms.len() - 1;
                            self.atoms[id].push_str(&format!("\nFixedRecord core field write: var {}.{}", var.idx(), fname));
                            core_guards.push(leaf);
                        }
                        FieldShape::ScalarSlot { mask, has_fixed, slot_id } => {
                            let se = self.slot_expr(val, *mask, *has_fixed, keys)?;
                            slot_writes.push(format!("⟨⟨{slot_id}, by decide⟩, {se}⟩"));
                        }
                        FieldShape::FixedMap { mask, map_id } => {
                            self.emit_map_update_expr(&field_base, *map_id, *mask, val, keys, writes)?;
                        }
                    }
                }
                Some(())
            }
            _ => None,
        }
    }

    fn extract_var_union_elems(&self, var: VarId, e: &Expr) -> Option<Vec<Expr>> {
        let mut out = Vec::new();
        fn go(var: VarId, e: &Expr, out: &mut Vec<Expr>) -> bool {
            if variable(e, false) == Some(var) {
                return true;
            }
            if let ExprKind::Builtin { op: B::Cup, args } = &*e.kind {
                if args.len() == 2 {
                    if let ExprKind::SetEnum(es) = &*args[1].kind {
                        if go(var, &args[0], out) {
                            out.extend(es.iter().cloned());
                            return true;
                        }
                    }
                    if let ExprKind::SetEnum(es) = &*args[0].kind {
                        if go(var, &args[1], out) {
                            out.extend(es.iter().cloned());
                            return true;
                        }
                    }
                }
            }
            false
        }
        go(var, e, &mut out).then_some(out)
    }

    pub(super) fn key_ref_expr(&self, kref: KeyRef, keys: &[(LocalId, GroupMask)], span: Span) -> Option<Expr> {
        match kref {
            KeyRef::Bound(i) => Some(Expr::new(ExprKind::Local(keys.get(i)?.0), span)),
            KeyRef::Slot(s) => {
                for (vi, sh) in self.shapes.iter().enumerate() {
                    match sh {
                        VarShape::ScalarSlot { slot_id, .. } if *slot_id == s => {
                            return Some(Expr::new(ExprKind::Var(VarId(vi as u32)), span));
                        }
                        VarShape::FixedRecord { fields } => {
                            for (fname, fsh) in fields {
                                if matches!(fsh, FieldShape::ScalarSlot { slot_id, .. } if *slot_id == s) {
                                    return Some(Expr::new(
                                        ExprKind::Field { record: Expr::new(ExprKind::Var(VarId(vi as u32)), span), field: fname.clone() },
                                        span,
                                    ));
                                }
                            }
                        }
                        _ => {}
                    }
                }
                None
            }
            KeyRef::Fixed(_) => None,
        }
    }

    pub(super) fn core_leaf_from_desc(&mut self, desc: String) -> String {
        let id = self.atoms.len();
        self.atoms.push(desc);
        format!("(Test.leaf {id} [] [] [])")
    }

    fn const_bool_value(&mut self, b: bool) -> String {
        let id = self.atoms.len();
        self.atoms.push(format!("Constant Bool payload: {b}"));
        format!("(ValueExpr.leaf {id} [] [] [])")
    }

    fn const_empty_set_value(&mut self) -> String {
        let id = self.atoms.len();
        self.atoms.push("Constant empty set payload: {}".into());
        format!("(ValueExpr.leaf {id} [] [] [])")
    }

    fn frames(&self, e: &Expr) -> Option<Expr> {
        Some(Expr::new(
            match &*e.kind {
                ExprKind::Var(v) if self.is_non_core(*v) || self.omitted.contains(v) => ExprKind::Tuple(vec![]),
                ExprKind::Var(_) => return Some(e.clone()),
                ExprKind::Tuple(es) => ExprKind::Tuple(es.iter().map(|e| self.frames(e)).collect::<Option<_>>()?),
                _ => return None,
            },
            e.span,
        ))
    }
}

fn expr_is_same_map_target(a: &Expr, b: &Expr) -> bool {
    match (&*a.kind, &*b.kind) {
        (ExprKind::Var(x), ExprKind::Var(y)) => x == y,
        (ExprKind::Field { record: r1, field: f1 }, ExprKind::Field { record: r2, field: f2 }) => {
            f1 == f2 && expr_is_same_map_target(r1, r2)
        }
        _ => false,
    }
}

enum PrimedBinding {
    None,
    Eq { term_idx: usize, rhs: Expr },
    Unchanged,
    Ambiguous,
}

fn primed_binding(branch: &Branch, v: VarId) -> PrimedBinding {
    let mut found = PrimedBinding::None;
    for (idx, e) in branch.terms.iter().enumerate() {
        match &*e.kind {
            ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 && variable(&args[0], true) == Some(v) => {
                if !matches!(found, PrimedBinding::None) {
                    return PrimedBinding::Ambiguous;
                }
                found = PrimedBinding::Eq { term_idx: idx, rhs: args[1].clone() };
            }
            ExprKind::Builtin { op: B::Unchanged, args } if args.len() == 1 => {
                let count = unchanged(&args[0], v);
                if count > 1 || (count == 1 && !matches!(found, PrimedBinding::None)) {
                    return PrimedBinding::Ambiguous;
                }
                if count == 1 {
                    found = PrimedBinding::Unchanged;
                }
            }
            _ => {}
        }
    }
    found
}
