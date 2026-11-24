//! Strict action, formula, expression, and membership totality checking for
//! `TotalityChecker`.

use std::collections::{BTreeMap, BTreeSet};

use super::shape::*;
use super::{CheckEnv, ConstInfo, MvType, Shape, TotalityChecker, MAX_I32_U32};
use crate::{builtins::Builtin as B, hir::*};

impl<'a> TotalityChecker<'a> {
    // ---- Action-level vs Value-position totality checking ----

    /// Check top-level `Init` / `Next` action formula.
    /// Action-level `And`, `Or`, and `Exists` enumerate successors exhaustively (never
    /// short-circuit across keys), while every guard, non-action formula, and value-position
    /// expression (`ok' = (\E ...)`, `IF cond`, `~P`, `P => Q`, `\A`, etc.) requires full totality.
    pub(super) fn check_action_formula(
        &self,
        e: &Expr,
        allow_prime: bool,
        env: &mut CheckEnv,
        bound_targets: &mut BTreeSet<VarId>,
        steps: &mut usize,
    ) -> bool {
        if *steps == 0 {
            return false;
        }
        *steps -= 1;
        match &*e.kind {
            ExprKind::Bool(_) => true,
            ExprKind::And(es) => {
                let mut local_env = env.clone();
                for item in es {
                    if !self.check_action_formula(item, allow_prime, &mut local_env, bound_targets, steps) {
                        return false;
                    }
                    self.apply_positive_fact(item, false, &mut local_env);
                }
                env.bound_vars = local_env.bound_vars;
                true
            }
            ExprKind::Or(es) => {
                let mut out_bound = bound_targets.clone();
                let mut def_bound: Option<Option<(bool, BTreeSet<VarId>)>> = None;
                for item in es {
                    let mut branch_bound = bound_targets.clone();
                    let mut branch_env = env.clone();
                    if !self.check_action_formula(item, allow_prime, &mut branch_env, &mut branch_bound, steps) {
                        return false;
                    }
                    out_bound.extend(branch_bound);
                    match &mut def_bound {
                        None => def_bound = Some(branch_env.bound_vars),
                        Some(acc) => {
                            if let (Some((p1, a)), Some((p2, b))) = (acc, &branch_env.bound_vars) {
                                if p1 == p2 {
                                    a.retain(|v| b.contains(v));
                                }
                            }
                        }
                    }
                }
                *bound_targets = out_bound;
                if let Some(db) = def_bound {
                    env.bound_vars = db;
                }
                true
            }
            ExprKind::Quant { kind: QuantKind::Exists, bounds, body } => {
                let mut local_env = env.clone();
                for b in bounds {
                    if self.check_enumerable_set(&b.set, allow_prime, false, &local_env, steps).is_none() {
                        return false;
                    }
                    let (elem, origin) = self.bound_elem_info(&b.set, false, &local_env);
                    match &b.vars {
                        BoundVars::Many(ids) => {
                            for &id in ids {
                                local_env.bind_local(id, elem.clone(), origin.clone());
                            }
                        }
                        BoundVars::Tuple(ids) => {
                            let Some(parts) = extract_exact_tuple_arity(&elem, ids.len()) else { return false };
                            for (&id, p) in ids.iter().zip(parts) {
                                local_env.bind_local(id, p, None);
                            }
                        }
                    }
                }
                let ok = self.check_action_formula(body, allow_prime, &mut local_env, bound_targets, steps);
                env.bound_vars = local_env.bound_vars;
                ok
            }
            ExprKind::If { cond, then, els } => {
                if !self.check_form(cond, allow_prime, false, env, steps) {
                    return false;
                }
                let mut t_env = env.clone();
                self.apply_positive_fact(cond, false, &mut t_env);
                let mut t_bound = bound_targets.clone();
                if !self.check_action_formula(then, allow_prime, &mut t_env, &mut t_bound, steps) {
                    return false;
                }
                let mut e_env = env.clone();
                self.apply_negative_fact(cond, false, &mut e_env);
                let mut e_bound = bound_targets.clone();
                if !self.check_action_formula(els, allow_prime, &mut e_env, &mut e_bound, steps) {
                    return false;
                }
                bound_targets.extend(t_bound);
                bound_targets.extend(e_bound);
                t_env.intersect_var_bound(&e_env.bound_vars);
                env.bound_vars = t_env.bound_vars;
                true
            }
            ExprKind::Case { arms, other } => {
                let Some(o) = other else { return false };
                let mut out_bound = bound_targets.clone();
                let mut def_bound: Option<Option<(bool, BTreeSet<VarId>)>> = None;
                for (c, b) in arms {
                    if !self.check_form(c, allow_prime, false, env, steps) {
                        return false;
                    }
                    let mut arm_bound = bound_targets.clone();
                    let mut arm_env = env.clone();
                    if !self.check_action_formula(b, allow_prime, &mut arm_env, &mut arm_bound, steps) {
                        return false;
                    }
                    out_bound.extend(arm_bound);
                    match &mut def_bound {
                        None => def_bound = Some(arm_env.bound_vars),
                        Some(acc) => {
                            if let (Some((p1, a)), Some((p2, b))) = (acc, &arm_env.bound_vars) {
                                if p1 == p2 {
                                    a.retain(|v| b.contains(v));
                                }
                            }
                        }
                    }
                }
                let mut other_bound = bound_targets.clone();
                let mut other_env = env.clone();
                if !self.check_action_formula(o, allow_prime, &mut other_env, &mut other_bound, steps) {
                    return false;
                }
                out_bound.extend(other_bound);
                if let Some(acc) = &mut def_bound {
                    if let (Some((p1, a)), Some((p2, b))) = (acc, &other_env.bound_vars) {
                        if p1 == p2 {
                            a.retain(|v| b.contains(v));
                        }
                    }
                    env.bound_vars = def_bound.unwrap();
                } else {
                    env.bound_vars = other_env.bound_vars;
                }
                *bound_targets = out_bound;
                true
            }
            ExprKind::Builtin { op: B::Unchanged, args } if allow_prime && args.len() == 1 => {
                if is_var_frame(&args[0]) {
                    let mut frame_vars = BTreeSet::new();
                    collect_var_frame(&args[0], &mut frame_vars);
                    if frame_vars.iter().all(|v| !bound_targets.contains(v)) {
                        for v in frame_vars {
                            bound_targets.insert(v);
                            env.mark_var_bound(v);
                        }
                        return true;
                    }
                }
                // Computed or already-bound expression inside `UNCHANGED`: evaluate in both states and require total equality.
                let Some(s0) = self.check_expr(&args[0], true, false, env, steps) else { return false };
                let Some(s1) = self.check_expr(&args[0], true, true, env, steps) else { return false };
                shapes_comparable(&s0, &s1) && shape_has_safe_set_cards(&s0, self.groups) && shape_has_safe_set_cards(&s1, self.groups)
            }
            // Primed assignment `v' = rhs` or `v' \in S` in action position:
            // Matches `Enumerator::assign_eq`: ONLY an unbound target on the **left** (`args[0]`)
            // assigns `v'`; `rhs = v'` or an already-bound `v'` is evaluated as an equality test.
            // Mark `v` bound ONLY AFTER checking its RHS so self-reads like `ok' = (... \/ ok')` fail.
            ExprKind::Builtin { op: B::Eq, args } if allow_prime && args.len() == 2 => {
                if let Some(v) = target_var(&args[0], true) {
                    if !bound_targets.contains(&v) {
                        if self.check_expr(&args[1], allow_prime, false, env, steps).is_none() {
                            return false;
                        }
                        bound_targets.insert(v);
                        env.mark_var_bound(v);
                        return true;
                    }
                }
                self.check_form(e, allow_prime, false, env, steps)
            }
            ExprKind::Builtin { op: B::In, args } if allow_prime && args.len() == 2 => {
                if let Some(v) = target_var(&args[0], true) {
                    if !bound_targets.contains(&v) {
                        // Fresh `v' \in S` enumerates `S` to generate successors, so `S` must be
                        // finitely enumerable (e.g. reject `n' \in Nat`).
                        if self.check_enumerable_set(&args[1], allow_prime, false, env, steps).is_none() {
                            return false;
                        }
                        bound_targets.insert(v);
                        env.mark_var_bound(v);
                        return true;
                    }
                }
                self.check_form(e, allow_prime, false, env, steps)
            }
            // Initial assignment `v = rhs` or `v \in S` in Init:
            // Matches `Enumerator::assign_eq`: ONLY an unbound target on the **left** (`args[0]`)
            // assigns `v`; `rhs = v` or an already-bound `v` is evaluated as an equality test.
            // Mark `v` bound ONLY AFTER checking its RHS so unbound Init self-reads fail.
            ExprKind::Builtin { op: B::Eq, args } if !allow_prime && args.len() == 2 => {
                if let Some(v) = target_var(&args[0], false) {
                    if !bound_targets.contains(&v) {
                        if self.check_expr(&args[1], false, false, env, steps).is_none() {
                            return false;
                        }
                        bound_targets.insert(v);
                        env.mark_var_bound(v);
                        return true;
                    }
                }
                self.check_form(e, false, false, env, steps)
            }
            ExprKind::Builtin { op: B::In, args } if !allow_prime && args.len() == 2 => {
                if let Some(v) = target_var(&args[0], false) {
                    if !bound_targets.contains(&v) {
                        if self.check_enumerable_set(&args[1], false, false, env, steps).is_none() {
                            return false;
                        }
                        bound_targets.insert(v);
                        env.mark_var_bound(v);
                        return true;
                    }
                }
                self.check_form(e, false, false, env, steps)
            }
            // Subset assignment `v \subseteq S` (Init) or `v' \subseteq S` (Next):
            // Matches `Enumerator::assign_subseteq`: ONLY an unbound target on the left (`args[0]`)
            // enumerates `powerset(S)` (requiring `|S| <= 30`, `2^30 <= i32::MAX`).
            ExprKind::Builtin { op: B::SubsetEq, args } if args.len() == 2 => {
                if let Some(v) = target_var(&args[0], allow_prime) {
                    if !bound_targets.contains(&v) {
                        if self.check_enumerable_set(&args[1], allow_prime, false, env, steps).is_none_or(|(_, ca)| ca > 30) {
                            return false;
                        }
                        bound_targets.insert(v);
                        env.mark_var_bound(v);
                        return true;
                    }
                }
                self.check_form(e, allow_prime, false, env, steps)
            }
            // Any other action guard or leaf formula must be strictly total!
            _ => self.check_form(e, allow_prime, false, env, steps),
        }
    }

    // ---- Strict Boolean formula & value expression totality ----

    pub(super) fn check_form(&self, e: &Expr, allow_prime: bool, in_prime: bool, env: &CheckEnv, steps: &mut usize) -> bool {
        if *steps == 0 {
            return false;
        }
        *steps -= 1;
        match &*e.kind {
            ExprKind::Bool(_) => true,
            ExprKind::And(es) => {
                let mut local_env = env.clone();
                for item in es {
                    if !self.check_form(item, allow_prime, in_prime, &local_env, steps) {
                        return false;
                    }
                    self.apply_positive_fact(item, in_prime, &mut local_env);
                }
                true
            }
            ExprKind::Or(es) => {
                let mut local_env = env.clone();
                for item in es {
                    if !self.check_form(item, allow_prime, in_prime, &local_env, steps) {
                        return false;
                    }
                    self.apply_negative_fact(item, in_prime, &mut local_env);
                }
                true
            }
            ExprKind::If { cond, then, els } => {
                if !self.check_form(cond, allow_prime, in_prime, env, steps) {
                    return false;
                }
                let mut t_env = env.clone();
                self.apply_positive_fact(cond, in_prime, &mut t_env);
                if !self.check_form(then, allow_prime, in_prime, &t_env, steps) {
                    return false;
                }
                let mut e_env = env.clone();
                self.apply_negative_fact(cond, in_prime, &mut e_env);
                self.check_form(els, allow_prime, in_prime, &e_env, steps)
            }
            ExprKind::Case { arms, other } => {
                let Some(o) = other else { return false };
                arms.iter().all(|(c, b)| {
                    self.check_form(c, allow_prime, in_prime, env, steps) && self.check_form(b, allow_prime, in_prime, env, steps)
                }) && self.check_form(o, allow_prime, in_prime, env, steps)
            }
            ExprKind::Quant { bounds, body, .. } => {
                let mut local_env = env.clone();
                for b in bounds {
                    if self.check_enumerable_set(&b.set, allow_prime, in_prime, &local_env, steps).is_none() {
                        return false;
                    }
                    let (elem, origin) = self.bound_elem_info(&b.set, in_prime, &local_env);
                    match &b.vars {
                        BoundVars::Many(ids) => {
                            for &id in ids {
                                local_env.bind_local(id, elem.clone(), origin.clone());
                            }
                        }
                        BoundVars::Tuple(ids) => {
                            let Some(parts) = extract_exact_tuple_arity(&elem, ids.len()) else { return false };
                            for (&id, p) in ids.iter().zip(parts) {
                                local_env.bind_local(id, p, None);
                            }
                        }
                    }
                }
                self.check_form(body, allow_prime, in_prime, &local_env, steps)
            }
            ExprKind::BoxAction { action, sub } | ExprKind::AngleAction { action, sub } if allow_prime && !in_prime => {
                if !self.check_form(action, allow_prime, false, env, steps) {
                    return false;
                }
                let Some(s0) = self.check_expr(sub, true, false, env, steps) else { return false };
                let Some(s1) = self.check_expr(sub, true, true, env, steps) else { return false };
                shapes_comparable(&s0, &s1) && shape_has_safe_set_cards(&s0, self.groups) && shape_has_safe_set_cards(&s1, self.groups)
            }
            ExprKind::Builtin { op, args } => match (op, args.as_slice()) {
                (B::Not, [a]) => self.check_form(a, allow_prime, in_prime, env, steps),
                (B::Implies, [a, b]) => {
                    if !self.check_form(a, allow_prime, in_prime, env, steps) {
                        return false;
                    }
                    let mut local_env = env.clone();
                    self.apply_positive_fact(a, in_prime, &mut local_env);
                    self.check_form(b, allow_prime, in_prime, &local_env, steps)
                }
                (B::Equiv, [a, b]) => {
                    self.check_form(a, allow_prime, in_prime, env, steps) && self.check_form(b, allow_prime, in_prime, env, steps)
                }
                (B::Eq | B::Neq, [a, b]) => {
                    if self.check_age_deadline_cmp(a, b, allow_prime, in_prime, env, steps) {
                        return true;
                    }
                    let Some(sa) = self.check_expr(a, allow_prime, in_prime, env, steps) else { return false };
                    let Some(sb) = self.check_expr(b, allow_prime, in_prime, env, steps) else { return false };
                    shapes_comparable(&sa, &sb) && shape_has_safe_set_cards(&sa, self.groups) && shape_has_safe_set_cards(&sb, self.groups)
                }
                (B::Lt | B::Le | B::Gt | B::Ge, [a, b]) => {
                    if self.check_age_deadline_cmp(a, b, allow_prime, in_prime, env, steps) {
                        return true;
                    }
                    let Some(sa) = self.check_expr(a, allow_prime, in_prime, env, steps) else { return false };
                    let Some(sb) = self.check_expr(b, allow_prime, in_prime, env, steps) else { return false };
                    is_int_shape(&sa) && is_int_shape(&sb)
                }
                (B::In | B::NotIn, [a, s]) => {
                    let Some(sa) = self.check_expr(a, allow_prime, in_prime, env, steps) else { return false };
                    self.check_membership(&sa, s, allow_prime, in_prime, env, steps)
                }
                (B::SubsetEq, [a, b]) => {
                    let Some(sa) = self.check_expr(a, allow_prime, in_prime, env, steps) else { return false };
                    let Some(ea) = set_elem_of_shape(&sa) else { return false };
                    shape_has_safe_set_cards(&sa, self.groups) && self.check_membership(&ea, b, allow_prime, in_prime, env, steps)
                }
                (B::IsFiniteSet, [s]) => self
                    .check_expr(s, allow_prime, in_prime, env, steps)
                    .is_some_and(|ss| is_finite_set_arg(&ss) && shape_has_safe_set_cards(&ss, self.groups)),
                (B::IsInjective, [f]) => {
                    let Some(sf) = self.check_expr(f, allow_prime, in_prime, env, steps) else { return false };
                    fn_dom_range(&sf).is_some_and(|(d, r, c)| {
                        c.is_some_and(|n| n <= MAX_I32_U32)
                            && shape_self_comparable(&d)
                            && shape_self_comparable(&r)
                            && shape_has_safe_set_cards(&d, self.groups)
                            && shape_has_safe_set_cards(&r, self.groups)
                    })
                }
                (B::Unchanged, [a]) if allow_prime && !in_prime => {
                    let Some(s0) = self.check_expr(a, true, false, env, steps) else { return false };
                    let Some(s1) = self.check_expr(a, true, true, env, steps) else { return false };
                    shapes_comparable(&s0, &s1) && shape_has_safe_set_cards(&s0, self.groups) && shape_has_safe_set_cards(&s1, self.groups)
                }
                (B::Prime, [a]) if allow_prime && !in_prime => self.check_form(a, allow_prime, true, env, steps),
                (B::TLCEval, [a]) => self.check_form(a, allow_prime, in_prime, env, steps),
                (B::Assert, _) => false,
                _ => self.check_expr(e, allow_prime, in_prime, env, steps).is_some_and(|s| is_bool_shape(&s)),
            },
            _ => self.check_expr(e, allow_prime, in_prime, env, steps).is_some_and(|s| is_bool_shape(&s)),
        }
    }

    /// Strict totality check for a value expression, returning its verified `Shape`.
    pub(super) fn check_expr(&self, e: &Expr, allow_prime: bool, in_prime: bool, env: &CheckEnv, steps: &mut usize) -> Option<Shape> {
        if *steps == 0 {
            return None;
        }
        *steps -= 1;
        match &*e.kind {
            ExprKind::Bool(_) => Some(Shape::Bool),
            ExprKind::Num(n) => i32::try_from(*n).ok().map(|k| Shape::Int(Some((k, k)))),
            ExprKind::Str(s) => Some(Shape::Str(Some(BTreeSet::from([s.clone()])))),
            ExprKind::Var(v) => {
                if let Some((tracked_prime, bv)) = &env.bound_vars {
                    if in_prime == *tracked_prime && !bv.contains(v) {
                        return None;
                    }
                }
                Some(
                    env.var_overrides
                        .get(&(*v, in_prime))
                        .cloned()
                        .unwrap_or_else(|| self.var_shapes.get(v.idx()).cloned().unwrap_or(Shape::Top)),
                )
            }
            ExprKind::Local(l) => {
                if let Some(s) = env.locals.get(l) {
                    return Some(s.clone());
                }
                if self.allow_choose_folds.is_some_and(|fv| fv.contains_key(l)) {
                    return Some(Shape::Int(None));
                }
                None
            }
            ExprKind::At => env.at_shape.clone(),
            ExprKind::Const(c) => match self.consts.get(c)? {
                ConstInfo::Value(v) => {
                    let s = self.cfg_value_shape(v);
                    (!shape_contains_top(&s) && shape_self_comparable(&s) && shape_has_safe_set_cards(&s, self.groups)).then_some(s)
                }
                ConstInfo::Builtin(op) => {
                    let b = Expr::new(ExprKind::Builtin { op: *op, args: vec![] }, e.span);
                    self.check_expr(&b, false, false, &CheckEnv::default(), steps)
                }
                ConstInfo::Subst(def_id) => match &self.program.defs[def_id.idx()].kind {
                    DefKind::Op(body) => self.check_expr(body, false, false, &CheckEnv::default(), steps),
                    _ => None,
                },
            },
            ExprKind::And(_) | ExprKind::Or(_) | ExprKind::Quant { .. } => {
                self.check_form(e, allow_prime, in_prime, env, steps).then_some(Shape::Bool)
            }
            ExprKind::Tuple(es) => {
                let parts = es.iter().map(|x| self.check_expr(x, allow_prime, in_prime, env, steps)).collect::<Option<Vec<_>>>()?;
                Some(Shape::Tuple(parts))
            }
            ExprKind::Record(fs) => {
                let mut map = BTreeMap::new();
                for (name, val) in fs {
                    map.insert(name.clone(), self.check_expr(val, allow_prime, in_prime, env, steps)?);
                }
                Some(Shape::Record(map))
            }
            ExprKind::Field { record, field } => {
                let rs = self.check_expr(record, allow_prime, in_prime, env, steps)?;
                field_of_shape_total(&rs, field)
            }
            ExprKind::Choose { vars, set, body } => {
                let fv = self.allow_choose_folds?;
                let s = set.as_ref()?;
                let (elem, max_card) = self.check_enumerable_set(s, allow_prime, in_prime, env, steps)?;
                let mut local_env = env.clone();
                let (_, origin) = self.bound_elem_info(s, in_prime, env);
                let is_fold = matches!(vars, BoundVars::Many(ids) if ids.len() == 1 && fv.contains_key(&ids[0]));
                match vars {
                    BoundVars::Many(ids) if ids.len() == 1 => local_env.bind_local(ids[0], elem.clone(), origin),
                    BoundVars::Tuple(ids) => {
                        let parts = extract_exact_tuple_arity(&elem, ids.len())?;
                        for (&id, p) in ids.iter().zip(parts) {
                            local_env.bind_local(id, p, None);
                        }
                    }
                    _ => return None,
                }
                if is_fold {
                    let Shape::Int(Some((lo, hi))) = self.check_expr(body, allow_prime, in_prime, &local_env, steps)? else {
                        return None;
                    };
                    let max_pos = i32::try_from((max_card as i128) * (hi.max(0) as i128)).ok()?;
                    let min_neg = i32::try_from((max_card as i128) * (lo.min(0) as i128)).ok()?;
                    Some(Shape::Int(Some((min_neg, max_pos))))
                } else {
                    self.check_form(body, allow_prime, in_prime, &local_env, steps).then_some(elem)
                }
            }
            ExprKind::SetEnum(es) => {
                let mut elem = Shape::Bottom;
                for x in es {
                    let s = self.check_expr(x, allow_prime, in_prime, env, steps)?;
                    if !shape_has_safe_set_cards(&s, self.groups) {
                        return None;
                    }
                    if !matches!(elem, Shape::Bottom) && !shapes_comparable(&elem, &s) {
                        return None;
                    }
                    elem = join_shape(&elem, &s);
                }
                let card = u32::try_from(es.len()).ok().filter(|&v| v <= MAX_I32_U32)?;
                Some(Shape::Set { elem: Box::new(elem), finite: true, max_card: Some(card) })
            }
            ExprKind::SetFilter { bound, pred } => {
                let (elem, max_card) = self.check_enumerable_set(&bound.set, allow_prime, in_prime, env, steps)?;
                let mut local_env = env.clone();
                let (_, origin) = self.bound_elem_info(&bound.set, in_prime, env);
                match &bound.vars {
                    BoundVars::Many(ids) => {
                        for &id in ids {
                            local_env.bind_local(id, elem.clone(), origin.clone());
                        }
                    }
                    BoundVars::Tuple(ids) => {
                        let parts = extract_exact_tuple_arity(&elem, ids.len())?;
                        for (&id, p) in ids.iter().zip(parts) {
                            local_env.bind_local(id, p, None);
                        }
                    }
                }
                if !self.check_form(pred, allow_prime, in_prime, &local_env, steps) {
                    return None;
                }
                Some(Shape::Set { elem: Box::new(elem), finite: true, max_card: Some(max_card) })
            }
            ExprKind::SetMap { expr, bounds } => {
                let mut local_env = env.clone();
                let mut card: Option<u32> = Some(1);
                for b in bounds {
                    let (elem, c) = self.check_enumerable_set(&b.set, allow_prime, in_prime, &local_env, steps)?;
                    let (_, origin) = self.bound_elem_info(&b.set, in_prime, &local_env);
                    let count = match &b.vars {
                        BoundVars::Many(ids) => {
                            for &id in ids {
                                local_env.bind_local(id, elem.clone(), origin.clone());
                            }
                            ids.len()
                        }
                        BoundVars::Tuple(ids) => {
                            let parts = extract_exact_tuple_arity(&elem, ids.len())?;
                            for (&id, p) in ids.iter().zip(parts) {
                                local_env.bind_local(id, p, None);
                            }
                            1
                        }
                    };
                    for _ in 0..count {
                        card = card.and_then(|a| a.checked_mul(c)).filter(|&v| v <= MAX_I32_U32);
                    }
                }
                let res = self.check_expr(expr, allow_prime, in_prime, &local_env, steps)?;
                if !shape_self_comparable(&res) || !shape_has_safe_set_cards(&res, self.groups) {
                    return None;
                }
                let card = card.or_else(|| shape_universe_size(&res, self.groups)).filter(|&v| v <= MAX_I32_U32)?;
                Some(Shape::Set { elem: Box::new(res), finite: true, max_card: Some(card) })
            }
            ExprKind::FnConstruct { bounds, body } => {
                let mut local_env = env.clone();
                let mut doms = Vec::new();
                let mut max_dom: Option<u32> = Some(1);
                for b in bounds {
                    let (elem, c) = self.check_enumerable_set(&b.set, allow_prime, in_prime, &local_env, steps)?;
                    let (_, origin) = self.bound_elem_info(&b.set, in_prime, &local_env);
                    match &b.vars {
                        BoundVars::Many(ids) => {
                            for &id in ids {
                                local_env.bind_local(id, elem.clone(), origin.clone());
                                doms.push(elem.clone());
                                max_dom = max_dom.and_then(|a| a.checked_mul(c)).filter(|&v| v <= MAX_I32_U32);
                            }
                        }
                        BoundVars::Tuple(ids) => {
                            let parts = extract_exact_tuple_arity(&elem, ids.len())?;
                            for (&id, p) in ids.iter().zip(parts) {
                                local_env.bind_local(id, p, None);
                            }
                            doms.push(elem);
                            max_dom = max_dom.and_then(|a| a.checked_mul(c)).filter(|&v| v <= MAX_I32_U32);
                        }
                    }
                }
                let exact_dom = bounds.iter().all(|b| self.is_exact_static_set(&b.set));
                let range = self.check_expr(body, allow_prime, in_prime, &local_env, steps)?;
                let dom = if doms.len() == 1 { doms.pop().unwrap() } else { Shape::Tuple(doms) };
                let max_dom = max_dom.or_else(|| shape_universe_size(&dom, self.groups)).filter(|&v| v <= MAX_I32_U32)?;
                Some(Shape::Func { dom: Box::new(dom), exact_dom, range: Box::new(range), max_dom: Some(max_dom) })
            }
            ExprKind::FnApp { func, args } => {
                let fs = self.check_expr(func, allow_prime, in_prime, env, steps)?;
                let arg_shapes = args.iter().map(|a| self.check_expr(a, allow_prime, in_prime, env, steps)).collect::<Option<Vec<_>>>()?;
                let key_shape = if arg_shapes.len() == 1 { arg_shapes[0].clone() } else { Shape::Tuple(arg_shapes) };
                // Fast exact checks:
                if args.len() == 1 {
                    if let ExprKind::Str(field) = &*args[0].kind {
                        if matches!(&fs, Shape::Record(_)) {
                            return field_of_shape_total(&fs, field);
                        }
                    }
                    // Proven `x \in DOMAIN f` (or `x \in 1..Len(seq)`) via DomOrigin:
                    if let ExprKind::Local(l) = &*args[0].kind {
                        if let Some((orig_expr, orig_prime)) = env.local_dom.get(l) {
                            if expr_struct_eq(func, in_prime, orig_expr, *orig_prime) && fnapp_index_valid_for(&fs, &key_shape, self.groups)
                            {
                                if let Some((_, range, _)) = fn_dom_range(&fs) {
                                    return Some(range);
                                }
                            }
                        }
                    }
                    if let Shape::Tuple(ts) = &fs {
                        if let Shape::Int(Some((lo, hi))) = key_shape {
                            if lo >= 1 && (hi as usize) <= ts.len() {
                                let mut out = Shape::Bottom;
                                for item in &ts[(lo as usize - 1)..(hi as usize)] {
                                    out = join_shape(&out, item);
                                }
                                return Some(out);
                            }
                        }
                        return None;
                    }
                    if let Shape::Seq { elem, min_len, .. } = &fs {
                        if let Shape::Int(Some((lo, hi))) = key_shape {
                            if lo >= 1 && (hi as u32) <= *min_len {
                                return Some((**elem).clone());
                            }
                        }
                        return None;
                    }
                }
                // General fixed-domain function application: requires `exact_dom == true` so
                // dynamic subset domains like `[q \in {r} |-> r]` can NEVER masquerade as `Proc`!
                if let Shape::Func { dom, exact_dom: true, range, .. } = &fs {
                    if shape_in_exact_domain(&key_shape, dom) && fnapp_index_valid_for(&fs, &key_shape, self.groups) {
                        if let Some(key) = fn_app_place(func, args, in_prime) {
                            if let Some(ov) = env.fn_app_overrides.get(&key) {
                                return Some(ov.clone());
                            }
                        }
                        return Some((**range).clone());
                    }
                }
                None
            }
            ExprKind::Except { base, updates } => {
                let mut cur = self.check_expr(base, allow_prime, in_prime, env, steps)?;
                for (ui, (path, rhs)) in updates.iter().enumerate() {
                    let mut step_shape = cur.clone();
                    let mut step_expr: Option<Expr> = Some(base.clone());
                    let mut absent = false;
                    for (step_idx, k) in path.iter().enumerate() {
                        if step_idx > 0 && ui > 0 {
                            step_expr = None;
                        }
                        match k {
                            ExceptKey::Field(f) => {
                                if !absent && !except_field_valid_for(&step_shape) {
                                    return None;
                                }
                                step_expr = step_expr.map(|record| Expr::new(ExprKind::Field { record, field: f.clone() }, e.span));
                            }
                            ExceptKey::Index(ixs) => {
                                let mut ix_shapes = Vec::with_capacity(ixs.len());
                                for ix in ixs {
                                    ix_shapes.push(self.check_expr(ix, allow_prime, in_prime, env, steps)?);
                                }
                                if !absent {
                                    let dom_nonempty = ixs.len() == 1
                                        && match (&*ixs[0].kind, step_expr.as_ref()) {
                                            (ExprKind::Local(l), Some(ce)) => {
                                                env.local_dom.get(l).is_some_and(|(orig, op)| expr_struct_eq(ce, in_prime, orig, *op))
                                            }
                                            _ => false,
                                        };
                                    let key_shape = if ix_shapes.len() == 1 { ix_shapes.pop().unwrap() } else { Shape::Tuple(ix_shapes) };
                                    if !except_index_valid_for_with_dom_proof(&step_shape, &key_shape, dom_nonempty, self.groups) {
                                        return None;
                                    }
                                    if except_key_provably_absent(&step_shape, &key_shape, self.groups) {
                                        absent = true;
                                    }
                                }
                                step_expr = step_expr.map(|func| Expr::new(ExprKind::FnApp { func, args: ixs.clone() }, e.span));
                            }
                        }
                        if !absent {
                            step_shape = lookup_except_path(&step_shape, std::slice::from_ref(k));
                        }
                    }
                    // A provably absent key leaves the value unchanged without evaluating `rhs`.
                    if absent {
                        continue;
                    }
                    let old_at = except_old_at_shape(base, &cur, path, in_prime, env, ui == 0);
                    let mut rhs_env = env.clone();
                    rhs_env.at_shape = Some(old_at);
                    let val = self.check_expr(rhs, allow_prime, in_prime, &rhs_env, steps)?;
                    cur = apply_except_shape(&cur, path, &val);
                }
                Some(cur)
            }
            ExprKind::If { cond, then, els } => {
                if !self.check_form(cond, allow_prime, in_prime, env, steps) {
                    return None;
                }
                let mut t_env = env.clone();
                self.apply_positive_fact(cond, in_prime, &mut t_env);
                let a = self.check_expr(then, allow_prime, in_prime, &t_env, steps)?;
                let mut e_env = env.clone();
                self.apply_negative_fact(cond, in_prime, &mut e_env);
                let b = self.check_expr(els, allow_prime, in_prime, &e_env, steps)?;
                Some(join_shape(&a, &b))
            }
            ExprKind::Case { arms, other } => {
                let o = other.as_ref()?;
                let mut acc = self.check_expr(o, allow_prime, in_prime, env, steps)?;
                for (c, b) in arms {
                    if !self.check_form(c, allow_prime, in_prime, env, steps) {
                        return None;
                    }
                    let s = self.check_expr(b, allow_prime, in_prime, env, steps)?;
                    acc = join_shape(&acc, &s);
                }
                Some(acc)
            }
            ExprKind::FnSet { domain, range } => {
                let (d, dc) = self.check_enumerable_set(domain, allow_prime, in_prime, env, steps)?;
                let (r, rc) = self.check_enumerable_set(range, allow_prime, in_prime, env, steps)?;
                let exact_dom = self.is_exact_static_set(domain);
                let card = if dc == 0 || rc <= 1 { Some(1) } else { rc.checked_pow(dc) }.filter(|&v| v <= MAX_I32_U32)?;
                Some(Shape::Set {
                    elem: Box::new(Shape::Func { dom: Box::new(d), exact_dom, range: Box::new(r), max_dom: Some(dc) }),
                    finite: true,
                    max_card: Some(card),
                })
            }
            ExprKind::RecordSet(fs) => {
                let mut map = BTreeMap::new();
                let mut card: Option<u32> = Some(1);
                for (name, set) in fs {
                    let (elem, c) = self.check_enumerable_set(set, allow_prime, in_prime, env, steps)?;
                    map.insert(name.clone(), elem);
                    card = card.and_then(|a| a.checked_mul(c)).filter(|&v| v <= MAX_I32_U32);
                }
                let elem = Shape::Record(map);
                let card = card.or_else(|| shape_universe_size(&elem, self.groups)).filter(|&v| v <= MAX_I32_U32)?;
                Some(Shape::Set { elem: Box::new(elem), finite: true, max_card: Some(card) })
            }
            ExprKind::Builtin { op, args } => self.check_builtin(e, (*op, args), allow_prime, in_prime, env, steps),
            _ => None,
        }
    }

    fn check_builtin(
        &self,
        e: &Expr,
        (op, args): (B, &[Expr]),
        allow_prime: bool,
        in_prime: bool,
        env: &CheckEnv,
        steps: &mut usize,
    ) -> Option<Shape> {
        match (op, args) {
            (B::Prime, [a]) if allow_prime && !in_prime => self.check_expr(a, allow_prime, true, env, steps),
            (B::TLCEval, [a]) => self.check_expr(a, allow_prime, in_prime, env, steps),
            (
                B::Not
                | B::Implies
                | B::Equiv
                | B::Eq
                | B::Neq
                | B::In
                | B::NotIn
                | B::SubsetEq
                | B::Lt
                | B::Le
                | B::Gt
                | B::Ge
                | B::IsFiniteSet
                | B::IsInjective,
                _,
            ) => self.check_form(e, allow_prime, in_prime, env, steps).then_some(Shape::Bool),
            (B::Boolean, []) => Some(Shape::Set { elem: Box::new(Shape::Bool), finite: true, max_card: Some(2) }),
            (B::DotDot, [a, b]) => {
                let sa = self.check_expr(a, allow_prime, in_prime, env, steps)?;
                let sb = self.check_expr(b, allow_prime, in_prime, env, steps)?;
                match (sa, sb) {
                    (Shape::Int(Some((al, ah))), Shape::Int(Some((_bl, bh)))) => {
                        let max_card =
                            if bh < al { 0 } else { u32::try_from(bh as i128 - al as i128 + 1).ok().filter(|&v| v <= MAX_I32_U32)? };
                        let elem = if bh < al { Shape::Bottom } else { Shape::Int(Some((al, bh.max(ah)))) };
                        Some(Shape::Set { elem: Box::new(elem), finite: true, max_card: Some(max_card) })
                    }
                    (Shape::Int(Some((1, 1))), Shape::Int(None))
                        if self.allow_unbounded_seq_len
                            && matches!(&*b.kind, ExprKind::Builtin { op: B::Len, args } if args.len() == 1 && self.is_definitely_seq(&args[0], in_prime, env)) =>
                    {
                        Some(Shape::Set { elem: Box::new(Shape::Int(None)), finite: true, max_card: None })
                    }
                    _ => None,
                }
            }
            (B::Cup, [a, b]) => {
                let (ea, ca) = self.check_enumerable_set(a, allow_prime, in_prime, env, steps)?;
                let (eb, cb) = self.check_enumerable_set(b, allow_prime, in_prime, env, steps)?;
                if !shapes_comparable(&ea, &eb) {
                    return None;
                }
                let joined = join_shape(&ea, &eb);
                let card = ca.checked_add(cb).or_else(|| shape_universe_size(&joined, self.groups)).filter(|&v| v <= MAX_I32_U32)?;
                Some(Shape::Set { elem: Box::new(joined), finite: true, max_card: Some(card) })
            }
            (B::Cap, [a, b]) => {
                let (ea, ca) = self.check_enumerable_set(a, allow_prime, in_prime, env, steps)?;
                let (eb, cb) = self.check_enumerable_set(b, allow_prime, in_prime, env, steps)?;
                if !shapes_comparable(&ea, &eb)
                    || !self.check_membership(&ea, b, allow_prime, in_prime, env, steps)
                    || !self.check_membership(&eb, a, allow_prime, in_prime, env, steps)
                {
                    return None;
                }
                Some(Shape::Set { elem: Box::new(join_shape(&ea, &eb)), finite: true, max_card: Some(ca.min(cb)) })
            }
            (B::SetMinus, [a, b]) => {
                let (ea, ca) = self.check_enumerable_set(a, allow_prime, in_prime, env, steps)?;
                let (eb, _) = self.check_enumerable_set(b, allow_prime, in_prime, env, steps)?;
                if !shapes_comparable(&ea, &eb) || !self.check_membership(&ea, b, allow_prime, in_prime, env, steps) {
                    return None;
                }
                Some(Shape::Set { elem: Box::new(ea), finite: true, max_card: Some(ca) })
            }
            (B::Subset, [a]) => {
                let (ea, ca) = self.check_enumerable_set(a, allow_prime, in_prime, env, steps)?;
                if ca > 30 {
                    return None;
                }
                Some(Shape::Set {
                    elem: Box::new(Shape::Set { elem: Box::new(ea), finite: true, max_card: Some(ca) }),
                    finite: true,
                    max_card: Some(1u32 << ca),
                })
            }
            (B::KSubset, [k, a]) => {
                let Shape::Int(Some((kl, _))) = self.check_expr(k, allow_prime, in_prime, env, steps)? else { return None };
                if kl < 0 {
                    return None;
                }
                let (ea, ca) = self.check_enumerable_set(a, allow_prime, in_prime, env, steps)?;
                if ca > 30 {
                    return None;
                }
                Some(Shape::Set {
                    elem: Box::new(Shape::Set { elem: Box::new(ea), finite: true, max_card: Some(ca) }),
                    finite: true,
                    max_card: Some(1u32 << ca),
                })
            }
            (B::SelectSeq, [s, lam]) => {
                let ss = self.check_expr(s, allow_prime, in_prime, env, steps)?;
                let (elem, _, max_len) = seq_elem_bounds(&ss)?;
                let ExprKind::Lambda { params, body } = &*lam.kind else { return None };
                if params.len() != 1 {
                    return None;
                }
                let mut local_env = env.clone();
                local_env.bind_local(params[0], elem.clone(), None);
                if !self.check_form(body, allow_prime, in_prime, &local_env, steps) {
                    return None;
                }
                Some(Shape::Seq { elem: Box::new(elem), min_len: 0, max_len })
            }
            (B::Union, [a]) => {
                let (outer, oc) = self.check_enumerable_set(a, allow_prime, in_prime, env, steps)?;
                match outer {
                    Shape::Bottom => Some(Shape::Set { elem: Box::new(Shape::Bottom), finite: true, max_card: Some(0) }),
                    Shape::Set { elem, finite: true, max_card } => {
                        if !shape_self_comparable(&elem) || !shape_has_safe_set_cards(&elem, self.groups) {
                            return None;
                        }
                        let ic = max_card.or_else(|| shape_universe_size(&elem, self.groups)).filter(|&v| v <= MAX_I32_U32)?;
                        let card = oc.checked_mul(ic).or_else(|| shape_universe_size(&elem, self.groups)).filter(|&v| v <= MAX_I32_U32)?;
                        Some(Shape::Set { elem, finite: true, max_card: Some(card) })
                    }
                    _ => None,
                }
            }
            (B::Times, es) if es.len() >= 2 => {
                let mut parts = Vec::with_capacity(es.len());
                let mut card: Option<u32> = Some(1);
                for x in es {
                    let (e, c) = self.check_enumerable_set(x, allow_prime, in_prime, env, steps)?;
                    parts.push(e);
                    card = card.and_then(|a| a.checked_mul(c)).filter(|&v| v <= MAX_I32_U32);
                }
                let elem = Shape::Tuple(parts);
                let card = card.or_else(|| shape_universe_size(&elem, self.groups)).filter(|&v| v <= MAX_I32_U32)?;
                Some(Shape::Set { elem: Box::new(elem), finite: true, max_card: Some(card) })
            }
            (B::Domain, [f]) => {
                let fs = self.check_expr(f, allow_prime, in_prime, env, steps)?;
                match domain_of_shape(&fs) {
                    Shape::Set { elem, finite: true, max_card } => {
                        let card = max_card.or_else(|| shape_universe_size(&elem, self.groups)).filter(|&v| v <= MAX_I32_U32)?;
                        Some(Shape::Set { elem, finite: true, max_card: Some(card) })
                    }
                    _ => None,
                }
            }
            (B::Cardinality, [s]) => {
                let (_, max_c) = self.check_enumerable_set(s, allow_prime, in_prime, env, steps)?;
                Some(Shape::Int(Some((0, max_c as i32))))
            }
            (B::Len, [s]) => match self.check_expr(s, allow_prime, in_prime, env, steps)? {
                Shape::Tuple(ts) => i32::try_from(ts.len()).ok().map(|n| Shape::Int(Some((n, n)))),
                Shape::Seq { min_len, max_len: Some(hi), .. } if hi <= MAX_I32_U32 => {
                    Some(Shape::Int(Some((min_len.min(MAX_I32_U32) as i32, hi as i32))))
                }
                Shape::Seq { .. } if self.allow_unbounded_seq_len => Some(Shape::Int(None)),
                _ => None,
            },
            (B::Append, [s, x]) => {
                let ex = self.check_expr(x, allow_prime, in_prime, env, steps)?;
                match self.check_expr(s, allow_prime, in_prime, env, steps)? {
                    Shape::Tuple(mut ts) => {
                        ts.push(ex);
                        Some(Shape::Tuple(ts))
                    }
                    Shape::Seq { elem, min_len, max_len: Some(hi) } if hi < MAX_I32_U32 => Some(Shape::Seq {
                        elem: Box::new(join_shape(&elem, &ex)),
                        min_len: min_len.saturating_add(1),
                        max_len: Some(hi + 1),
                    }),
                    _ => None,
                }
            }
            (B::Concat, [a, b]) => {
                let sa = self.check_expr(a, allow_prime, in_prime, env, steps)?;
                let sb = self.check_expr(b, allow_prime, in_prime, env, steps)?;
                match (sa, sb) {
                    (Shape::Tuple(mut ta), Shape::Tuple(tb)) => {
                        ta.extend(tb);
                        Some(Shape::Tuple(ta))
                    }
                    (a, b) => {
                        let (ea, lo1, hi1) = seq_elem_bounds(&a)?;
                        let (eb, lo2, hi2) = seq_elem_bounds(&b)?;
                        let hi = hi1?.checked_add(hi2?).filter(|&v| v <= MAX_I32_U32)?;
                        Some(Shape::Seq { elem: Box::new(join_shape(&ea, &eb)), min_len: lo1.saturating_add(lo2), max_len: Some(hi) })
                    }
                }
            }
            (B::Head, [s]) => match self.check_expr(s, allow_prime, in_prime, env, steps)? {
                Shape::Tuple(ts) if !ts.is_empty() => Some(ts[0].clone()),
                Shape::Seq { elem, min_len, .. } if min_len >= 1 => Some(*elem),
                _ => None,
            },
            (B::Tail, [s]) => match self.check_expr(s, allow_prime, in_prime, env, steps)? {
                Shape::Tuple(ts) if !ts.is_empty() => Some(Shape::Tuple(ts[1..].to_vec())),
                Shape::Seq { elem, min_len, max_len } if min_len >= 1 => {
                    Some(Shape::Seq { elem, min_len: min_len - 1, max_len: max_len.map(|m| m.saturating_sub(1)) })
                }
                _ => None,
            },
            (B::ColonGt, [k, v]) => {
                let ks = self.check_expr(k, allow_prime, in_prime, env, steps)?;
                let vs = self.check_expr(v, allow_prime, in_prime, env, steps)?;
                let exact_dom = matches!(&*k.kind, ExprKind::Num(_) | ExprKind::Str(_));
                Some(Shape::Func { dom: Box::new(ks), exact_dom, range: Box::new(vs), max_dom: Some(1) })
            }
            (B::AtAt, [a, b]) => {
                let sa = self.check_expr(a, allow_prime, in_prime, env, steps)?;
                let sb = self.check_expr(b, allow_prime, in_prime, env, steps)?;
                let (da, ra, ca) = fn_dom_range(&sa)?;
                let (db, rb, cb) = fn_dom_range(&sb)?;
                if !shapes_comparable(&da, &db)
                    || !shape_self_comparable(&da)
                    || !shape_self_comparable(&db)
                    || !shape_has_safe_set_cards(&da, self.groups)
                    || !shape_has_safe_set_cards(&db, self.groups)
                {
                    return None;
                }
                let joined_dom = join_shape(&da, &db);
                let ca = ca.or_else(|| shape_universe_size(&da, self.groups));
                let cb = cb.or_else(|| shape_universe_size(&db, self.groups));
                let card = ca
                    .and_then(|x| cb.and_then(|y| x.checked_add(y)))
                    .or_else(|| shape_universe_size(&joined_dom, self.groups))
                    .filter(|&v| v <= MAX_I32_U32)?;
                Some(Shape::Func {
                    dom: Box::new(joined_dom),
                    exact_dom: false,
                    range: Box::new(join_shape(&ra, &rb)),
                    max_dom: Some(card),
                })
            }
            // Strict checked 32-bit signed arithmetic across all modes.
            (B::Plus, [a, b]) => self.check_arith_bin((a, b), allow_prime, in_prime, env, steps, arith_add),
            (B::Minus, [a, b]) => self.check_arith_bin((a, b), allow_prime, in_prime, env, steps, arith_sub),
            (B::Mul, [a, b]) => self.check_arith_bin((a, b), allow_prime, in_prime, env, steps, arith_mul),
            (B::Div, [a, b]) => self.check_arith_bin((a, b), allow_prime, in_prime, env, steps, arith_div_pos),
            (B::Mod, [a, b]) => self.check_arith_bin((a, b), allow_prime, in_prime, env, steps, arith_mod_pos),
            (B::Pow, [a, b]) => self.check_arith_bin((a, b), allow_prime, in_prime, env, steps, arith_pow),
            (B::Gcd, [a, b]) => {
                let Shape::Int(Some((al, _))) = self.check_expr(a, allow_prime, in_prime, env, steps)? else { return None };
                let Shape::Int(Some((bl, _))) = self.check_expr(b, allow_prime, in_prime, env, steps)? else { return None };
                (al > i32::MIN && bl > i32::MIN).then_some(Shape::Int(Some((0, i32::MAX))))
            }
            (B::Neg, [a]) => {
                let Shape::Int(Some((lo, hi))) = self.check_expr(a, allow_prime, in_prime, env, steps)? else { return None };
                Some(Shape::Int(Some(arith_neg(lo, hi)?)))
            }
            (B::SubSeq, [s, lo, hi]) => {
                let ss = self.check_expr(s, allow_prime, in_prime, env, steps)?;
                let (elem, min_len, max_len) = seq_elem_bounds(&ss)?;
                let Shape::Int(Some((l_lo, _))) = self.check_expr(lo, allow_prime, in_prime, env, steps)? else { return None };
                let Shape::Int(Some((h_lo, h_hi))) = self.check_expr(hi, allow_prime, in_prime, env, steps)? else { return None };
                if l_lo > h_hi || (l_lo >= 1 && (h_hi as u32) <= min_len && h_lo >= 0) {
                    Some(Shape::Seq { elem: Box::new(elem), min_len: 0, max_len })
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// Scoped strictly to certified relative-age projections: accepts
    /// `(stamp + d) cmp clock` / `clock cmp (stamp + d)` (or `stamp cmp clock`)
    /// where `clock` is the proven mathematical clock variable, `0 <= d <= i32::MAX / 2`,
    /// and `stamp` itself passes strict totality as an integer expression.
    fn check_age_deadline_cmp(&self, a: &Expr, b: &Expr, allow_prime: bool, in_prime: bool, env: &CheckEnv, steps: &mut usize) -> bool {
        let Some(clock) = self.age_clock else {
            return false;
        };
        let is_clock = |e: &Expr| matches!(&*e.kind, ExprKind::Var(v) if *v == clock);
        let other = if is_clock(a) {
            b
        } else if is_clock(b) {
            a
        } else {
            return false;
        };
        let stamp = match &*other.kind {
            ExprKind::Builtin { op: B::Plus, args } if args.len() == 2 => match (&*args[0].kind, &*args[1].kind) {
                (_, ExprKind::Num(d)) if *d >= 0 && *d <= (i32::MAX / 2) as i128 => &args[0],
                (ExprKind::Num(d), _) if *d >= 0 && *d <= (i32::MAX / 2) as i128 => &args[1],
                _ => return false,
            },
            _ => other,
        };
        self.check_expr(stamp, allow_prime, in_prime, env, steps).is_some_and(|s| is_int_shape(&s))
    }

    fn check_arith_bin(
        &self,
        (a, b): (&Expr, &Expr),
        allow_prime: bool,
        in_prime: bool,
        env: &CheckEnv,
        steps: &mut usize,
        op: fn((i32, i32), (i32, i32)) -> Option<(i32, i32)>,
    ) -> Option<Shape> {
        let Shape::Int(Some(ba)) = self.check_expr(a, allow_prime, in_prime, env, steps)? else { return None };
        let Shape::Int(Some(bb)) = self.check_expr(b, allow_prime, in_prime, env, steps)? else { return None };
        Some(Shape::Int(Some(op(ba, bb)?)))
    }

    /// Recursive finite enumerability + verified `<= i32::MAX` cardinality bound.
    /// Explicitly rejects `Nat`, `Int`, `STRING`, `Seq(S)`, `SUBSET Nat`, `SUBSET (1..31)`,
    /// and any set whose cardinality is not bounded by `i32::MAX`.
    fn check_enumerable_set(&self, s: &Expr, allow_prime: bool, in_prime: bool, env: &CheckEnv, steps: &mut usize) -> Option<(Shape, u32)> {
        if *steps == 0 {
            return None;
        }
        match &*s.kind {
            ExprKind::Builtin { op: B::Nat | B::Int | B::StringSet | B::Seq, .. } => None,
            _ => match self.check_expr(s, allow_prime, in_prime, env, steps)? {
                Shape::Set { elem, finite: true, max_card } => {
                    if !shape_self_comparable(&elem) || !shape_has_safe_set_cards(&elem, self.groups) {
                        return None;
                    }
                    let bound = max_card
                        .or_else(|| shape_universe_size(&elem, self.groups))
                        .or_else(|| {
                            (self.allow_unbounded_seq_len
                                && matches!(
                                    &*s.kind,
                                    ExprKind::Builtin { op: B::DotDot, args }
                                        if args.len() == 2
                                            && matches!(&*args[0].kind, ExprKind::Num(1))
                                            && matches!(&*args[1].kind, ExprKind::Builtin { op: B::Len, args: la } if la.len() == 1)
                                ))
                            .then_some(MAX_I32_U32)
                        })
                        .filter(|&v| v <= MAX_I32_U32)?;
                    Some((*elem, bound))
                }
                _ => None,
            },
        }
    }

    /// Check `x \in S` membership with exact runtime preconditions for each set
    /// constructor (matching `tlx-value/src/ops/member.rs`).
    fn check_membership(&self, val: &Shape, set: &Expr, allow_prime: bool, in_prime: bool, env: &CheckEnv, steps: &mut usize) -> bool {
        match &*set.kind {
            ExprKind::Builtin { op: B::Nat | B::Int, args } if args.is_empty() => shapes_comparable(val, &Shape::Int(None)),
            ExprKind::Builtin { op: B::StringSet, args } if args.is_empty() => shapes_comparable(val, &Shape::Str(None)),
            ExprKind::Builtin { op: B::Boolean, args } if args.is_empty() => shapes_comparable(val, &Shape::Bool),
            ExprKind::Builtin { op: B::Seq, args } if args.len() == 1 => {
                if !is_seq_or_untyped_model(val) || self.check_membership_domain_elem(&args[0], allow_prime, in_prime, env, steps).is_none()
                {
                    return false;
                }
                self.check_seq_set_member(val, &args[0], allow_prime, in_prime, env, steps)
            }
            ExprKind::Builtin { op: B::Subset, args } if args.len() == 1 => {
                // `v \in SUBSET S` requires `v` to be a finitely enumerable Set with safe cardinality
                // (untyped model values and overflowing sets ERROR at runtime!).
                let Some(val_elem) = set_elem_of_shape_strict(val) else { return false };
                shape_has_safe_set_cards(val, self.groups) && self.check_membership(&val_elem, &args[0], allow_prime, in_prime, env, steps)
            }
            ExprKind::Builtin { op: B::KSubset, args } if args.len() == 2 => {
                if self.check_expr(set, allow_prime, in_prime, env, steps).is_none() {
                    return false;
                }
                let Some(val_elem) = set_elem_of_shape_strict(val) else { return false };
                shape_has_safe_set_cards(val, self.groups) && self.check_membership(&val_elem, &args[1], allow_prime, in_prime, env, steps)
            }
            ExprKind::SetFilter { bound, .. } => {
                self.check_expr(set, allow_prime, in_prime, env, steps).is_some()
                    && shape_has_safe_set_cards(val, self.groups)
                    && self.check_membership(val, &bound.set, allow_prime, in_prime, env, steps)
            }
            ExprKind::FnSet { domain, range } => {
                if !is_fn_like_or_untyped_model(val) {
                    return false;
                }
                let Some((dom, _)) = self.check_enumerable_set(domain, allow_prime, in_prime, env, steps) else { return false };
                if self.check_membership_domain_elem(range, allow_prime, in_prime, env, steps).is_none() {
                    return false;
                }
                self.check_fn_set_member(val, (&dom, range), allow_prime, in_prime, env, steps)
            }
            ExprKind::RecordSet(fs) => {
                if !is_record_or_empty_tuple_or_untyped_model(val) {
                    return false;
                }
                let mut sorted: BTreeMap<&str, &Expr> = BTreeMap::new();
                for (name, s) in fs {
                    if self.check_membership_domain_elem(s, allow_prime, in_prime, env, steps).is_none() {
                        return false;
                    }
                    sorted.insert(name.as_ref(), s);
                }
                self.check_record_set_member(val, &sorted, allow_prime, in_prime, env, steps)
            }
            ExprKind::If { cond, then, els } => {
                if !self.check_form(cond, allow_prime, in_prime, env, steps) {
                    return false;
                }
                let mut t_env = env.clone();
                self.apply_positive_fact(cond, in_prime, &mut t_env);
                if !self.check_membership(val, then, allow_prime, in_prime, &t_env, steps) {
                    return false;
                }
                let mut e_env = env.clone();
                self.apply_negative_fact(cond, in_prime, &mut e_env);
                self.check_membership(val, els, allow_prime, in_prime, &e_env, steps)
            }
            ExprKind::Case { arms, other } => {
                let Some(o) = other else { return false };
                arms.iter().all(|(c, b)| {
                    self.check_form(c, allow_prime, in_prime, env, steps)
                        && self.check_membership(val, b, allow_prime, in_prime, env, steps)
                }) && self.check_membership(val, o, allow_prime, in_prime, env, steps)
            }
            ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => {
                self.check_membership(val, &args[0], allow_prime, in_prime, env, steps)
            }
            ExprKind::Builtin { op: B::Cup, args } if args.len() == 2 => {
                // Eager union construction requires comparable element shapes across both operands.
                let Some(ea) = self.check_membership_domain_elem(&args[0], allow_prime, in_prime, env, steps) else {
                    return false;
                };
                let Some(eb) = self.check_membership_domain_elem(&args[1], allow_prime, in_prime, env, steps) else {
                    return false;
                };
                if !shapes_comparable(&ea, &eb) {
                    return false;
                }
                self.check_membership(val, &args[0], allow_prime, in_prime, env, steps)
                    && self.check_membership(val, &args[1], allow_prime, in_prime, env, steps)
            }
            ExprKind::Builtin { op: B::Cap | B::SetMinus, args } if args.len() == 2 => {
                self.check_expr(set, allow_prime, in_prime, env, steps).is_some()
                    && shape_has_safe_set_cards(val, self.groups)
                    && self.check_membership(val, &args[0], allow_prime, in_prime, env, steps)
                    && self.check_membership(val, &args[1], allow_prime, in_prime, env, steps)
            }
            ExprKind::Builtin { op: B::Times, args } if args.len() >= 2 => {
                if !is_tuple_or_untyped_model(val) {
                    return false;
                }
                for a in args {
                    if self.check_membership_domain_elem(a, allow_prime, in_prime, env, steps).is_none() {
                        return false;
                    }
                }
                self.check_times_set_member(val, args, allow_prime, in_prime, env, steps)
            }
            _ => {
                // Only truly materialized sets (explicit enumerations, intervals, literal cfg sets,
                // and completed pre-state variables normalized by `to_state`) skip lazy-set
                // membership checks; freshly bound `Init` variables (`bound_vars == Some((false, _))`),
                // primed `Next` variables, `UNION`, `DOMAIN`, `Const(Subst)`, `Local`, and computed
                // expressions may still hold lazy sets during enumeration.
                let is_materialized = match &*set.kind {
                    ExprKind::SetEnum(_) | ExprKind::SetMap { .. } | ExprKind::Builtin { op: B::DotDot | B::Boolean, .. } => true,
                    ExprKind::Const(c) => matches!(self.consts.get(c), Some(ConstInfo::Value(_))),
                    ExprKind::Var(_) => !in_prime && !matches!(env.bound_vars, Some((false, _))),
                    _ => false,
                };
                match self.check_enumerable_set(set, allow_prime, in_prime, env, steps) {
                    Some((elem, _)) => {
                        if !is_materialized
                            && (shape_may_contain_lazy_strict(&elem) || !shape_safe_for_lazy_membership(val, &elem, self.groups))
                        {
                            return false;
                        }
                        shapes_comparable(val, &elem) && shape_has_safe_set_cards(val, self.groups)
                    }
                    None => false,
                }
            }
        }
    }

    fn check_seq_set_member(
        &self,
        val: &Shape,
        range_expr: &Expr,
        allow_prime: bool,
        in_prime: bool,
        env: &CheckEnv,
        steps: &mut usize,
    ) -> bool {
        match val {
            Shape::Bottom | Shape::Model { mv_type: MvType::Untyped, .. } => true,
            Shape::Tuple(ts) => ts.iter().all(|t| self.check_membership(t, range_expr, allow_prime, in_prime, env, steps)),
            Shape::Seq { elem, .. } => self.check_membership(elem, range_expr, allow_prime, in_prime, env, steps),
            Shape::Union(us) if !us.is_empty() => {
                us.iter().all(|u| self.check_seq_set_member(u, range_expr, allow_prime, in_prime, env, steps))
            }
            _ => false,
        }
    }

    fn check_fn_set_member(
        &self,
        val: &Shape,
        (dom, range_expr): (&Shape, &Expr),
        allow_prime: bool,
        in_prime: bool,
        env: &CheckEnv,
        steps: &mut usize,
    ) -> bool {
        match val {
            Shape::Bottom | Shape::Model { mv_type: MvType::Untyped, .. } => true,
            Shape::Union(us) if !us.is_empty() => {
                us.iter().all(|u| self.check_fn_set_member(u, (dom, range_expr), allow_prime, in_prime, env, steps))
            }
            _ => {
                let Some((vdom, vrng, _)) = fn_dom_range(val) else { return false };
                shapes_comparable(&vdom, dom)
                    && shape_has_safe_set_cards(&vdom, self.groups)
                    && shape_has_safe_set_cards(dom, self.groups)
                    && self.check_membership(&vrng, range_expr, allow_prime, in_prime, env, steps)
            }
        }
    }

    fn check_times_set_member(
        &self,
        val: &Shape,
        factors: &[Expr],
        allow_prime: bool,
        in_prime: bool,
        env: &CheckEnv,
        steps: &mut usize,
    ) -> bool {
        match val {
            Shape::Bottom | Shape::Model { mv_type: MvType::Untyped, .. } => true,
            Shape::Tuple(ts) => {
                ts.len() != factors.len()
                    || ts.iter().zip(factors).all(|(t, f)| self.check_membership(t, f, allow_prime, in_prime, env, steps))
            }
            Shape::Union(us) if !us.is_empty() => {
                us.iter().all(|u| self.check_times_set_member(u, factors, allow_prime, in_prime, env, steps))
            }
            _ => false,
        }
    }

    /// Check `val \in [f1 : S1, ...]` in exact runtime field order (`member.rs:138-148`):
    /// when field counts match, the runtime evaluates `member(r[k], S[k])` for every
    /// matching prefix field before stopping at the first differing field name.
    fn check_record_set_member(
        &self,
        val: &Shape,
        sorted_fields: &BTreeMap<&str, &Expr>,
        allow_prime: bool,
        in_prime: bool,
        env: &CheckEnv,
        steps: &mut usize,
    ) -> bool {
        match val {
            Shape::Bottom | Shape::Model { mv_type: MvType::Untyped, .. } => true,
            Shape::Tuple(ts) => ts.is_empty(),
            Shape::Union(us) if !us.is_empty() => {
                us.iter().all(|u| self.check_record_set_member(u, sorted_fields, allow_prime, in_prime, env, steps))
            }
            Shape::Record(r) => {
                if r.len() != sorted_fields.len() {
                    return true;
                }
                // Runtime records iterate `Sym`s in intern order, so any shared field may be
                // checked before a differing field name is reached.
                for (name, v_shape) in r {
                    if let Some(&s_expr) = sorted_fields.get(name.as_ref()) {
                        if !self.check_membership(v_shape, s_expr, allow_prime, in_prime, env, steps) {
                            return false;
                        }
                    }
                }
                true
            }
            _ => false,
        }
    }

    fn check_membership_domain_elem(
        &self,
        set: &Expr,
        allow_prime: bool,
        in_prime: bool,
        env: &CheckEnv,
        steps: &mut usize,
    ) -> Option<Shape> {
        match &*set.kind {
            ExprKind::Builtin { op: B::Nat, args } if args.is_empty() => Some(Shape::Int(Some((0, i32::MAX)))),
            ExprKind::Builtin { op: B::Int, args } if args.is_empty() => Some(Shape::Int(None)),
            ExprKind::Builtin { op: B::StringSet, args } if args.is_empty() => Some(Shape::Str(None)),
            ExprKind::Builtin { op: B::Boolean, args } if args.is_empty() => Some(Shape::Bool),
            ExprKind::Builtin { op: B::Seq, args } if args.len() == 1 => {
                let elem = self.check_membership_domain_elem(&args[0], allow_prime, in_prime, env, steps)?;
                Some(Shape::Seq { elem: Box::new(elem), min_len: 0, max_len: None })
            }
            ExprKind::Builtin { op: B::Subset, args } if args.len() == 1 => {
                let finite = self.check_enumerable_set(&args[0], allow_prime, in_prime, env, steps).is_some();
                let elem = self.check_membership_domain_elem(&args[0], allow_prime, in_prime, env, steps)?;
                Some(Shape::Set { elem: Box::new(elem), finite, max_card: None })
            }
            ExprKind::FnSet { domain, range } => {
                let (dom, _) = self.check_enumerable_set(domain, allow_prime, in_prime, env, steps)?;
                let rng = self.check_membership_domain_elem(range, allow_prime, in_prime, env, steps)?;
                Some(Shape::Func { dom: Box::new(dom), exact_dom: false, range: Box::new(rng), max_dom: None })
            }
            ExprKind::RecordSet(fs) => {
                let mut map = BTreeMap::new();
                for (name, s) in fs {
                    map.insert(name.clone(), self.check_membership_domain_elem(s, allow_prime, in_prime, env, steps)?);
                }
                Some(Shape::Record(map))
            }
            ExprKind::Builtin { op: B::Cup, args } if args.len() == 2 => {
                let a = self.check_membership_domain_elem(&args[0], allow_prime, in_prime, env, steps)?;
                let b = self.check_membership_domain_elem(&args[1], allow_prime, in_prime, env, steps)?;
                if !shapes_comparable(&a, &b) {
                    return None;
                }
                Some(join_shape(&a, &b))
            }
            ExprKind::Builtin { op: B::Times, args } if args.len() >= 2 => {
                let mut parts = Vec::with_capacity(args.len());
                for a in args {
                    parts.push(self.check_membership_domain_elem(a, allow_prime, in_prime, env, steps)?);
                }
                Some(Shape::Tuple(parts))
            }
            _ => self.check_enumerable_set(set, allow_prime, in_prime, env, steps).map(|(elem, _)| elem),
        }
    }
}
