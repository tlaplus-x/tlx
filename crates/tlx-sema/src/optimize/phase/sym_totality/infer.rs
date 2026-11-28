//! Fixed-point abstract shape inference and path-sensitive narrowing for
//! `TotalityChecker`.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use tlx_front::cfg::CfgValue;

use super::super::sym_norm::{classify_ac_op, is_chooses_first_lambda, AcOpKind, RecOpKind};
use super::progress::{apply_progress_bound, infer_progress_bounds, seed_progress_bound};
use super::shape::*;
use super::{CheckEnv, ConstInfo, MvType, PlaceKey, Shape, TotalityChecker, MAX_I32_U32, MAX_STEPS, MAX_STR_SET, MAX_UNMOVED_SET};
use crate::{builtins::Builtin as B, hir::*};

impl<'a> TotalityChecker<'a> {
    // ---- Fixed-point shape inference (Init + Next with verified post-fixed-point closure) ----

    pub(super) fn infer_var_shapes(&self, init: &Expr, next: &Expr) -> Vec<Shape> {
        let n = self.program.vars.len();
        if n == 0 {
            return Vec::new();
        }
        // Step 1: Iterate Init to a fixed point so dependent initializations (`a = "x" /\ b = a`)
        // propagate cleanly instead of leaving `b` at `Bottom`.
        let mut cur = vec![Shape::Bottom; n];
        let mut init_converged = false;
        for _ in 0..16 {
            let mut next_img = vec![Shape::Bottom; n];
            let mut steps = MAX_STEPS;
            self.collect_assignments(init, false, &cur, &CheckEnv::default(), &mut next_img, &mut steps);
            if steps == 0 {
                return vec![Shape::Top; n];
            }
            let joined: Vec<Shape> = cur.iter().zip(&next_img).map(|(a, b)| cap_shape(join_shape(a, b))).collect();
            if joined == cur {
                init_converged = true;
                break;
            }
            cur = joined;
        }
        if !init_converged {
            return vec![Shape::Top; n];
        }
        // Any variable still `Bottom` after Init was never assigned -> sound fallback `Top`.
        for s in &mut cur {
            if matches!(s, Shape::Bottom) {
                *s = Shape::Top;
            }
        }
        let init_shapes = cur.clone();

        // Step 2: Iterate Next to a fixed point.
        let mut step2_converged = false;
        for round in 0..40 {
            let mut next_img = vec![Shape::Bottom; n];
            let mut steps = MAX_STEPS;
            self.collect_assignments(next, true, &cur, &CheckEnv::default(), &mut next_img, &mut steps);
            if steps == 0 {
                return vec![Shape::Top; n];
            }
            let mut joined: Vec<Shape> = cur.iter().zip(&next_img).map(|(a, b)| cap_shape(join_shape(a, b))).collect();
            if round >= 24 {
                for (old, new) in cur.iter().zip(&mut joined) {
                    if old != new {
                        *new = widen_diff(old, new);
                    }
                }
            }
            if joined == cur {
                step2_converged = true;
                break;
            }
            cur = joined;
        }

        // Step 2b: Only when Step 2 converged to an inductive post-fixed-point, check if an
        // Init+Next-only finite-progress measure soundly bounds widened counters/logs, and re-run
        // Step 2 seeded/clamped by those proven progress invariants so dependent variables
        // (e.g. `fifoAt`) inherit the tight finite bounds.
        let prog_bounds = if step2_converged { infer_progress_bounds(self, next, &init_shapes, &cur) } else { vec![None; n] };
        if prog_bounds.iter().any(Option::is_some) {
            cur = init_shapes
                .iter()
                .zip(&prog_bounds)
                .map(|(s, b)| b.as_ref().map_or_else(|| s.clone(), |pb| seed_progress_bound(s, pb)))
                .collect();
            let mut step2b_converged = false;
            for round in 0..40 {
                let mut next_img = vec![Shape::Bottom; n];
                let mut steps = MAX_STEPS;
                self.collect_assignments(next, true, &cur, &CheckEnv::default(), &mut next_img, &mut steps);
                if steps == 0 {
                    return vec![Shape::Top; n];
                }
                let mut joined: Vec<Shape> = cur
                    .iter()
                    .zip(&next_img)
                    .enumerate()
                    .map(|(i, (a, b))| {
                        let j = cap_shape(join_shape(a, b));
                        prog_bounds[i].as_ref().map_or(j.clone(), |pb| apply_progress_bound(&j, pb))
                    })
                    .collect();
                if round >= 24 {
                    for (i, (old, new)) in cur.iter().zip(&mut joined).enumerate() {
                        if old != new {
                            let w = widen_diff(old, new);
                            *new = prog_bounds[i].as_ref().map_or(w.clone(), |pb| apply_progress_bound(&w, pb));
                        }
                    }
                }
                if joined == cur {
                    step2b_converged = true;
                    break;
                }
                cur = joined;
            }
            if !step2b_converged {
                return vec![Shape::Top; n];
            }
        }

        // Step 3: Explicit post-fixed-point closure verification!
        // Guarantees inductiveness: if ANY variable still grows in one step of Init or Next
        // (modulo progress-proven counter/log caps), discard all unverified bounds and fall
        // back to `Top` for every variable.
        let mut verify_init = vec![Shape::Bottom; n];
        let mut verify_next = vec![Shape::Bottom; n];
        let mut steps = MAX_STEPS;
        self.collect_assignments(init, false, &cur, &CheckEnv::default(), &mut verify_init, &mut steps);
        self.collect_assignments(next, true, &cur, &CheckEnv::default(), &mut verify_next, &mut steps);
        if steps == 0 {
            return vec![Shape::Top; n];
        }
        for i in 0..n {
            let next_checked =
                prog_bounds[i].as_ref().map_or_else(|| verify_next[i].clone(), |pb| apply_progress_bound(&verify_next[i], pb));
            if !shape_leq(&verify_init[i], &cur[i]) || !shape_leq(&next_checked, &cur[i]) {
                return vec![Shape::Top; n];
            }
        }
        cur
    }

    fn collect_assignments(&self, e: &Expr, primed: bool, vars: &[Shape], env: &CheckEnv, out: &mut [Shape], steps: &mut usize) {
        if *steps == 0 {
            return;
        }
        *steps -= 1;
        match &*e.kind {
            ExprKind::And(es) => {
                let mut local_env = env.clone();
                for item in es {
                    self.collect_assignments(item, primed, vars, &local_env, out, steps);
                    self.apply_fact_with_vars(item, true, false, vars, &mut local_env);
                }
            }
            ExprKind::Or(es) => {
                for item in es {
                    self.collect_assignments(item, primed, vars, env, out, steps);
                }
            }
            ExprKind::If { cond, then, els } => {
                let mut t_env = env.clone();
                self.apply_fact_with_vars(cond, true, false, vars, &mut t_env);
                self.collect_assignments(then, primed, vars, &t_env, out, steps);
                let mut e_env = env.clone();
                self.apply_fact_with_vars(cond, false, false, vars, &mut e_env);
                self.collect_assignments(els, primed, vars, &e_env, out, steps);
            }
            ExprKind::Case { arms, other } => {
                for (_, body) in arms {
                    self.collect_assignments(body, primed, vars, env, out, steps);
                }
                if let Some(o) = other {
                    self.collect_assignments(o, primed, vars, env, out, steps);
                }
            }
            ExprKind::Quant { kind: QuantKind::Exists | QuantKind::Forall, bounds, body } => {
                let mut local_env = env.clone();
                if !self.bind_quant_bounds(bounds, false, vars, &mut local_env, steps) {
                    return;
                }
                self.collect_assignments(body, primed, vars, &local_env, out, steps);
            }
            ExprKind::Builtin { op: B::Implies, args } if args.len() == 2 => {
                // `Enumerator::implies` tests `args[0]` and executes `args[1]` as an action.
                let mut local_env = env.clone();
                self.apply_fact_with_vars(&args[0], true, false, vars, &mut local_env);
                self.collect_assignments(&args[1], primed, vars, &local_env, out, steps);
            }
            ExprKind::BoxAction { action, sub } if primed => {
                self.collect_assignments(action, primed, vars, env, out, steps);
                self.collect_unchanged(sub, vars, out);
            }
            ExprKind::AngleAction { action, .. } if primed => {
                self.collect_assignments(action, primed, vars, env, out, steps);
            }
            ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 => {
                if let Some(v) = target_var(&args[0], primed) {
                    let s = self.infer_expr(&args[1], false, vars, env, steps);
                    out[v.idx()] = cap_shape(join_shape(&out[v.idx()], &s));
                } else if let Some(v) = target_var(&args[1], primed) {
                    let s = self.infer_expr(&args[0], false, vars, env, steps);
                    out[v.idx()] = cap_shape(join_shape(&out[v.idx()], &s));
                } else if may_hide_target(&args[0], primed, env) {
                    out.fill(Shape::Top);
                }
            }
            ExprKind::Builtin { op: B::In, args } if args.len() == 2 => {
                if let Some(v) = target_var(&args[0], primed) {
                    let s = self.infer_set_elem(&args[1], false, vars, env, steps);
                    out[v.idx()] = cap_shape(join_shape(&out[v.idx()], &s));
                } else if may_hide_target(&args[0], primed, env) {
                    out.fill(Shape::Top);
                }
            }
            ExprKind::Builtin { op: B::SubsetEq, args } if args.len() == 2 => {
                if let Some(v) = target_var(&args[0], primed) {
                    let (elem, finite, max_card) = self.infer_set_info(&args[1], false, vars, env, steps);
                    let s = if finite { Shape::Set { elem: Box::new(elem), finite: true, max_card } } else { Shape::Top };
                    out[v.idx()] = cap_shape(join_shape(&out[v.idx()], &s));
                } else if may_hide_target(&args[0], primed, env) {
                    out.fill(Shape::Top);
                }
            }
            ExprKind::Builtin { op: B::Unchanged, args } if primed && args.len() == 1 => {
                self.collect_unchanged(&args[0], vars, out);
            }
            // Fail closed on remaining action constructs that `Enumerator::go_inner` can execute
            // to assign variables (`A \cdot B`, unexpanded `LET`/`Apply`, lazy `FnApp`, by-name `Local`).
            ExprKind::Builtin { op: B::Compose, .. } if primed => out.fill(Shape::Top),
            ExprKind::Let { .. } | ExprKind::Apply { .. } => out.fill(Shape::Top),
            ExprKind::FnApp { func, .. }
                if matches!(&*func.kind, ExprKind::FnConstruct { .. } | ExprKind::Apply { .. } | ExprKind::Let { .. })
                    || matches!(&*func.kind, ExprKind::Local(l) if !env.locals.contains_key(l)) =>
            {
                out.fill(Shape::Top);
            }
            ExprKind::Local(l) if !env.locals.contains_key(l) => out.fill(Shape::Top),
            _ => {}
        }
    }

    fn collect_unchanged(&self, arg: &Expr, vars: &[Shape], out: &mut [Shape]) {
        match &*arg.kind {
            ExprKind::Var(v) => out[v.idx()] = join_shape(&out[v.idx()], &vars[v.idx()]),
            ExprKind::Tuple(es) => {
                for e in es {
                    self.collect_unchanged(e, vars, out);
                }
            }
            _ => {}
        }
    }
}

/// True if `lhs` could resolve to an assignment target via `Enumerator::target`
/// (`Let`, `Apply`, or a by-name `Local`, directly or inside `Prime`).
fn may_hide_target(lhs: &Expr, primed: bool, env: &CheckEnv) -> bool {
    let inner = if primed {
        match &*lhs.kind {
            ExprKind::Builtin { op: B::Prime, args } if args.len() == 1 => &args[0],
            _ => lhs,
        }
    } else {
        lhs
    };
    matches!(&*inner.kind, ExprKind::Let { .. } | ExprKind::Apply { .. })
        || matches!(&*inner.kind, ExprKind::Local(l) if !env.locals.contains_key(l))
}

impl<'a> TotalityChecker<'a> {
    fn bind_quant_bounds(&self, bounds: &[Bound], in_prime: bool, vars: &[Shape], env: &mut CheckEnv, steps: &mut usize) -> bool {
        for b in bounds {
            let elem = self.infer_set_elem(&b.set, in_prime, vars, env, steps);
            if matches!(elem, Shape::Bottom) {
                return false;
            }
            match &b.vars {
                BoundVars::Many(ids) => {
                    for &id in ids {
                        env.bind_local(id, elem.clone(), None);
                    }
                }
                BoundVars::Tuple(ids) => {
                    if let Some(parts) = extract_exact_tuple_arity(&elem, ids.len()) {
                        for (&id, p) in ids.iter().zip(parts) {
                            env.bind_local(id, p, None);
                        }
                    } else {
                        for &id in ids {
                            env.bind_local(id, Shape::Top, None);
                        }
                    }
                }
            }
        }
        true
    }

    // ---- Expression shape inference ----

    pub(super) fn infer_expr(&self, e: &Expr, in_prime: bool, vars: &[Shape], env: &CheckEnv, steps: &mut usize) -> Shape {
        if *steps == 0 {
            return Shape::Top;
        }
        *steps -= 1;
        match &*e.kind {
            ExprKind::Bool(_) => Shape::Bool,
            ExprKind::Num(n) => i32::try_from(*n).map_or(Shape::Top, |k| Shape::Int(Some((k, k)))),
            ExprKind::Str(s) => Shape::Str(Some(BTreeSet::from([s.clone()]))),
            ExprKind::CfgLiteral(v) => self.cfg_value_shape(v),
            ExprKind::Var(v) => {
                if let Some(ov) = env.var_overrides.get(&(*v, in_prime)) {
                    return ov.clone();
                }
                vars.get(v.idx()).cloned().unwrap_or(Shape::Top)
            }
            ExprKind::Local(l) => {
                if let Some(s) = env.locals.get(l) {
                    return s.clone();
                }
                if self.allow_choose_folds.is_some_and(|fv| fv.contains_key(l)) {
                    return Shape::Int(None);
                }
                Shape::Top
            }
            ExprKind::At => env.at_shape.clone().unwrap_or(Shape::Top),
            ExprKind::Const(c) => match self.consts.get(c) {
                Some(ConstInfo::Value(v)) => self.cfg_value_shape(v),
                Some(ConstInfo::Builtin(op)) => {
                    let b = Expr::new(ExprKind::Builtin { op: *op, args: vec![] }, e.span);
                    self.infer_expr(&b, false, vars, &CheckEnv::default(), steps)
                }
                Some(ConstInfo::Subst(def_id)) => match &self.program.defs[def_id.idx()].kind {
                    DefKind::Op(body) => self.infer_expr(body, false, vars, &CheckEnv::default(), steps),
                    _ => Shape::Top,
                },
                None => Shape::Top,
            },
            ExprKind::And(_) | ExprKind::Or(_) | ExprKind::Quant { .. } => Shape::Bool,
            ExprKind::Tuple(es) => Shape::Tuple(es.iter().map(|x| self.infer_expr(x, in_prime, vars, env, steps)).collect()),
            ExprKind::Record(fs) => {
                let mut map = BTreeMap::new();
                for (name, val) in fs {
                    map.insert(name.clone(), self.infer_expr(val, in_prime, vars, env, steps));
                }
                Shape::Record(map)
            }
            ExprKind::Field { record, field } => {
                let rs = self.infer_expr(record, in_prime, vars, env, steps);
                field_of_shape(&rs, field)
            }
            ExprKind::SetEnum(es) => {
                let mut elem = Shape::Bottom;
                for x in es {
                    let s = self.infer_expr(x, in_prime, vars, env, steps);
                    elem = join_shape(&elem, &s);
                }
                Shape::Set { elem: Box::new(elem), finite: true, max_card: u32::try_from(es.len()).ok() }
            }
            ExprKind::SetFilter { bound, pred } => {
                let (elem, finite, max_card) = self.infer_set_info(&bound.set, in_prime, vars, env, steps);
                // A filter keeps only the elements that satisfy `pred`, so the
                // established place narrowing (tagged record unions, integer
                // ranges, membership) may be assumed while inferring the
                // element shape of the filtered set.
                let elem = self.narrow_filter_elem(bound, pred, &elem, in_prime, vars, env);
                Shape::Set { elem: Box::new(elem), finite, max_card }
            }
            ExprKind::SetMap { expr, bounds } => {
                let mut local_env = env.clone();
                let mut finite = true;
                let mut card: Option<u32> = Some(1);
                for b in bounds {
                    let (elem, f, c) = self.infer_set_info(&b.set, in_prime, vars, &local_env, steps);
                    finite &= f;
                    let count = match &b.vars {
                        BoundVars::Many(ids) => {
                            for &id in ids {
                                local_env.bind_local(id, elem.clone(), None);
                            }
                            ids.len()
                        }
                        BoundVars::Tuple(ids) => {
                            if let Some(parts) = extract_exact_tuple_arity(&elem, ids.len()) {
                                for (&id, p) in ids.iter().zip(parts) {
                                    local_env.bind_local(id, p, None);
                                }
                            } else {
                                for &id in ids {
                                    local_env.bind_local(id, Shape::Top, None);
                                }
                            }
                            1
                        }
                    };
                    for _ in 0..count {
                        card = card.and_then(|a| c.and_then(|b| a.checked_mul(b))).filter(|&v| v <= MAX_I32_U32);
                    }
                }
                let elem = self.infer_expr(expr, in_prime, vars, &local_env, steps);
                Shape::Set { elem: Box::new(elem), finite, max_card: card }
            }
            ExprKind::FnConstruct { bounds, body } => {
                let mut local_env = env.clone();
                let mut doms = Vec::new();
                let mut max_dom: Option<u32> = Some(1);
                for b in bounds {
                    let (elem, _, c) = self.infer_set_info(&b.set, in_prime, vars, &local_env, steps);
                    match &b.vars {
                        BoundVars::Many(ids) => {
                            for &id in ids {
                                local_env.bind_local(id, elem.clone(), None);
                                doms.push(elem.clone());
                                max_dom = max_dom.and_then(|a| c.and_then(|b| a.checked_mul(b))).filter(|&v| v <= MAX_I32_U32);
                            }
                        }
                        BoundVars::Tuple(ids) => {
                            if let Some(parts) = extract_exact_tuple_arity(&elem, ids.len()) {
                                for (&id, p) in ids.iter().zip(parts) {
                                    local_env.bind_local(id, p, None);
                                }
                            } else {
                                for &id in ids {
                                    local_env.bind_local(id, Shape::Top, None);
                                }
                            }
                            doms.push(elem);
                            max_dom = max_dom.and_then(|a| c.and_then(|b| a.checked_mul(b))).filter(|&v| v <= MAX_I32_U32);
                        }
                    }
                }
                let exact_dom = bounds.iter().all(|b| self.is_exact_static_set(&b.set));
                let dom = if doms.len() == 1 { doms.pop().unwrap() } else { Shape::Tuple(doms) };
                let range = self.infer_expr(body, in_prime, vars, &local_env, steps);
                Shape::Func { dom: Box::new(dom), exact_dom, range: Box::new(range), max_dom }
            }
            ExprKind::FnApp { func, args } => {
                if let Some((_, _, ov)) = env.expr_overrides.iter().rev().find(|(oe, op, _)| expr_alpha_eq(e, in_prime, oe, *op)) {
                    return ov.clone();
                }
                if let Some(key) = fn_app_place(func, args, in_prime) {
                    if let Some(ov) = env.fn_app_overrides.get(&key) {
                        return ov.clone();
                    }
                }
                let fs = self.infer_expr(func, in_prime, vars, env, steps);
                if args.len() == 1 {
                    if let ExprKind::Str(field) = &*args[0].kind {
                        if let Shape::Record(_) = &fs {
                            return field_of_shape(&fs, field);
                        }
                    }
                    if let Shape::Tuple(ts) = &fs {
                        if let Shape::Int(Some((lo, hi))) = self.infer_expr(&args[0], in_prime, vars, env, steps) {
                            if lo >= 1 && (hi as usize) <= ts.len() {
                                let mut out = Shape::Bottom;
                                for item in &ts[(lo as usize - 1)..(hi as usize)] {
                                    out = join_shape(&out, item);
                                }
                                return out;
                            }
                        }
                    }
                }
                fn_app_range(&fs)
            }
            ExprKind::Except { base, updates } => {
                let mut cur = self.infer_expr(base, in_prime, vars, env, steps);
                for (ui, (path, rhs)) in updates.iter().enumerate() {
                    if let Some(ExceptKey::Index(ixs)) = path.first() {
                        let key_shape = if ixs.len() == 1 {
                            self.infer_expr(&ixs[0], in_prime, vars, env, steps)
                        } else {
                            Shape::Tuple(ixs.iter().map(|ix| self.infer_expr(ix, in_prime, vars, env, steps)).collect())
                        };
                        if except_key_provably_absent(&cur, &key_shape, self.groups) {
                            continue;
                        }
                    }
                    let old_at = except_old_at_shape(base, &cur, path, in_prime, env, ui == 0);
                    let mut rhs_env = env.clone();
                    rhs_env.at_shape = Some(old_at);
                    let val = self.infer_expr(rhs, in_prime, vars, &rhs_env, steps);
                    cur = apply_except_shape(&cur, path, &val);
                }
                cur
            }
            ExprKind::If { cond, then, els } => {
                let mut t_env = env.clone();
                self.apply_fact_with_vars(cond, true, in_prime, vars, &mut t_env);
                let a = self.infer_expr(then, in_prime, vars, &t_env, steps);
                let mut e_env = env.clone();
                self.apply_fact_with_vars(cond, false, in_prime, vars, &mut e_env);
                let b = self.infer_expr(els, in_prime, vars, &e_env, steps);
                join_shape(&a, &b)
            }
            ExprKind::Case { arms, other } => {
                let Some(o) = other else { return Shape::Top };
                let mut acc = self.infer_expr(o, in_prime, vars, env, steps);
                for (_, body) in arms {
                    let s = self.infer_expr(body, in_prime, vars, env, steps);
                    acc = join_shape(&acc, &s);
                }
                acc
            }
            ExprKind::FnSet { domain, range } => {
                let (d, df, dc) = self.infer_set_info(domain, in_prime, vars, env, steps);
                let (r, rf, rc) = self.infer_set_info(range, in_prime, vars, env, steps);
                let exact_dom = self.is_exact_static_set(domain);
                // `dc` is an upper bound; if the actual domain can be empty, `[{} -> {}]` still has
                // cardinality 1 (the empty function), so floor the power bound at 1.
                let card = dc.and_then(|dn| rc.and_then(|rn| rn.checked_pow(dn)).map(|p| p.max(1))).filter(|&v| v <= MAX_I32_U32);
                Shape::Set {
                    elem: Box::new(Shape::Func { dom: Box::new(d), exact_dom, range: Box::new(r), max_dom: dc }),
                    finite: df && rf,
                    max_card: card,
                }
            }
            ExprKind::RecordSet(fs) => {
                let mut map = BTreeMap::new();
                let mut finite = true;
                let mut card: Option<u32> = Some(1);
                for (name, set) in fs {
                    let (elem, f, c) = self.infer_set_info(set, in_prime, vars, env, steps);
                    finite &= f;
                    map.insert(name.clone(), elem);
                    card = card.and_then(|a| c.and_then(|b| a.checked_mul(b))).filter(|&v| v <= MAX_I32_U32);
                }
                Shape::Set { elem: Box::new(Shape::Record(map)), finite, max_card: card }
            }
            ExprKind::Choose { vars: cvars, set, .. } => {
                if let Some(fv) = self.allow_choose_folds {
                    if let BoundVars::Many(ids) = cvars {
                        if ids.len() == 1 && fv.contains_key(&ids[0]) {
                            return Shape::Int(None);
                        }
                    }
                    if let Some(s) = set {
                        return self.infer_set_elem(s, in_prime, vars, env, steps);
                    }
                }
                if let Some(s) = set {
                    let (elem, finite, _) = self.infer_set_info(s, in_prime, vars, env, steps);
                    if finite && shape_is_key_free(&elem) {
                        return elem;
                    }
                }
                Shape::Top
            }
            ExprKind::Apply { op: OpRef::Def(id), args } => match self.rec_ops.get(id) {
                Some(RecOpKind::FixSet) if args.len() == 2 => {
                    let ExprKind::Lambda { params, body: step } = &*args[1].kind else { return Shape::Top };
                    let [s_var] = params.as_slice() else { return Shape::Top };
                    let (mut elem, finite, mut card) = self.infer_set_info(&args[0], in_prime, vars, env, steps);
                    if !finite || *steps == 0 {
                        return Shape::Top;
                    }
                    let mut converged = false;
                    for _ in 0..8 {
                        let mut local_env = env.clone();
                        local_env.bind_local(*s_var, Shape::Set { elem: Box::new(elem.clone()), finite: true, max_card: card }, None);
                        let (se, sf, sc) = self.infer_set_info(step, in_prime, vars, &local_env, steps);
                        if !sf || *steps == 0 {
                            return Shape::Top;
                        }
                        let joined = cap_shape(join_shape(&elem, &se));
                        let next_card = shape_universe_size(&joined, self.groups)
                            .or_else(|| card.and_then(|a| sc.and_then(|b| a.checked_add(b))))
                            .filter(|&v| v <= MAX_I32_U32);
                        if joined == elem && next_card == card {
                            converged = true;
                            break;
                        }
                        elem = joined;
                        card = next_card;
                    }
                    if !converged {
                        return Shape::Top;
                    }
                    Shape::Set { elem: Box::new(elem), finite: true, max_card: card }
                }
                Some(RecOpKind::IterRec) if args.len() == 2 => {
                    let ExprKind::Lambda { params, body } = &*args[1].kind else { return Shape::Top };
                    let [x_var] = params.as_slice() else { return Shape::Top };
                    let ExprKind::If { cond, then: step, els: base } = &*body.kind else { return Shape::Top };
                    let mut cur = self.infer_expr(&args[0], in_prime, vars, env, steps);
                    let mut acc = Shape::Bottom;
                    for _ in 0..16 {
                        if *steps == 0 {
                            return Shape::Top;
                        }
                        let mut local_env = env.clone();
                        local_env.bind_local(*x_var, cur.clone(), None);
                        let mut e_env = local_env.clone();
                        self.apply_fact_with_vars(cond, false, in_prime, vars, &mut e_env);
                        if !e_env.unreachable {
                            let b = self.infer_expr(base, in_prime, vars, &e_env, steps);
                            acc = cap_shape(join_shape(&acc, &b));
                        }
                        let mut t_env = local_env.clone();
                        self.apply_fact_with_vars(cond, true, in_prime, vars, &mut t_env);
                        if t_env.unreachable {
                            return acc;
                        }
                        let next = self.infer_expr(step, in_prime, vars, &t_env, steps);
                        if matches!(next, Shape::Bottom) {
                            return acc;
                        }
                        cur = next;
                    }
                    Shape::Top
                }
                _ => Shape::Top,
            },
            ExprKind::Builtin { op, args } => self.infer_builtin(*op, args, in_prime, vars, env, steps),
            _ => Shape::Top,
        }
    }

    fn infer_builtin(&self, op: B, args: &[Expr], in_prime: bool, vars: &[Shape], env: &CheckEnv, steps: &mut usize) -> Shape {
        match (op, args) {
            (B::Prime, [a]) => self.infer_expr(a, true, vars, env, steps),
            (B::TLCEval, [a]) => self.infer_expr(a, in_prime, vars, env, steps),
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
            ) => Shape::Bool,
            (B::Boolean, []) => Shape::Set { elem: Box::new(Shape::Bool), finite: true, max_card: Some(2) },
            (B::Nat, []) => Shape::Set { elem: Box::new(Shape::Int(Some((0, i32::MAX)))), finite: false, max_card: None },
            (B::Int, []) => Shape::Set { elem: Box::new(Shape::Int(None)), finite: false, max_card: None },
            (B::StringSet, []) => Shape::Set { elem: Box::new(Shape::Str(None)), finite: false, max_card: None },
            (B::DotDot, [a, b]) => {
                let sa = self.infer_expr(a, in_prime, vars, env, steps);
                let sb = self.infer_expr(b, in_prime, vars, env, steps);
                match (sa, sb) {
                    (Shape::Int(Some((al, ah))), Shape::Int(Some((_bl, bh)))) => {
                        let max_card =
                            if bh < al { Some(0) } else { u32::try_from(bh as i128 - al as i128 + 1).ok().filter(|&v| v <= MAX_I32_U32) };
                        let elem = if bh < al { Shape::Bottom } else { Shape::Int(Some((al, bh.max(ah)))) };
                        Shape::Set { elem: Box::new(elem), finite: true, max_card }
                    }
                    _ => Shape::Set { elem: Box::new(Shape::Int(None)), finite: true, max_card: None },
                }
            }
            (B::Cup, [a, b]) => {
                let (ea, fa, ca) = self.infer_set_info(a, in_prime, vars, env, steps);
                let (eb, fb, cb) = self.infer_set_info(b, in_prime, vars, env, steps);
                let card = ca.and_then(|x| cb.and_then(|y| x.checked_add(y))).filter(|&v| v <= MAX_I32_U32);
                Shape::Set { elem: Box::new(join_shape(&ea, &eb)), finite: fa && fb, max_card: card }
            }
            (B::Cap, [a, b]) => {
                let (ea, fa, ca) = self.infer_set_info(a, in_prime, vars, env, steps);
                let (eb, fb, cb) = self.infer_set_info(b, in_prime, vars, env, steps);
                let card = match (ca, cb) {
                    (Some(x), Some(y)) => Some(x.min(y)),
                    (Some(x), None) | (None, Some(x)) => Some(x),
                    (None, None) => None,
                };
                Shape::Set { elem: Box::new(join_shape(&ea, &eb)), finite: fa || fb, max_card: card }
            }
            (B::SetMinus, [a, _]) => {
                let (ea, fa, ca) = self.infer_set_info(a, in_prime, vars, env, steps);
                Shape::Set { elem: Box::new(ea), finite: fa, max_card: ca }
            }
            (B::Subset, [a]) | (B::KSubset, [_, a]) => {
                let (ea, fa, ca) = self.infer_set_info(a, in_prime, vars, env, steps);
                let card = ca.and_then(|n| (n <= 30).then(|| 1u32 << n));
                Shape::Set { elem: Box::new(Shape::Set { elem: Box::new(ea), finite: fa, max_card: ca }), finite: fa, max_card: card }
            }
            (B::Union, [a]) => {
                let (outer, of, oc) = self.infer_set_info(a, in_prime, vars, env, steps);
                match outer {
                    Shape::Set { elem, finite, max_card } => {
                        let card = oc.and_then(|x| max_card.and_then(|y| x.checked_mul(y))).filter(|&v| v <= MAX_I32_U32);
                        Shape::Set { elem, finite: of && finite, max_card: card }
                    }
                    Shape::Bottom => Shape::Set { elem: Box::new(Shape::Bottom), finite: true, max_card: Some(0) },
                    _ => Shape::Top,
                }
            }
            (B::Times, es) if es.len() >= 2 => {
                let mut parts = Vec::with_capacity(es.len());
                let mut finite = true;
                let mut card: Option<u32> = Some(1);
                for x in es {
                    let (e, f, c) = self.infer_set_info(x, in_prime, vars, env, steps);
                    finite &= f;
                    parts.push(e);
                    card = card.and_then(|a| c.and_then(|b| a.checked_mul(b))).filter(|&v| v <= MAX_I32_U32);
                }
                Shape::Set { elem: Box::new(Shape::Tuple(parts)), finite, max_card: card }
            }
            (B::Seq, [a]) => {
                let elem = self.infer_set_elem(a, in_prime, vars, env, steps);
                Shape::Set { elem: Box::new(Shape::Seq { elem: Box::new(elem), min_len: 0, max_len: None }), finite: false, max_card: None }
            }
            (B::Domain, [f]) => {
                let fs = self.infer_expr(f, in_prime, vars, env, steps);
                domain_of_shape(&fs)
            }
            (B::Cardinality, [s]) => {
                let (elem, _, c) = self.infer_set_info(s, in_prime, vars, env, steps);
                let bound = c.or_else(|| shape_universe_size(&elem, self.groups));
                match bound {
                    Some(m) if m <= MAX_I32_U32 => Shape::Int(Some((0, m as i32))),
                    _ => Shape::Int(None),
                }
            }
            (B::Len, [s]) => match self.infer_expr(s, in_prime, vars, env, steps) {
                Shape::Bottom => Shape::Bottom,
                Shape::Tuple(ts) => i32::try_from(ts.len()).map_or(Shape::Int(None), |n| Shape::Int(Some((n, n)))),
                Shape::Seq { min_len, max_len: Some(hi), .. } if hi <= MAX_I32_U32 => {
                    Shape::Int(Some((min_len.min(MAX_I32_U32) as i32, hi as i32)))
                }
                Shape::Seq { .. } => Shape::Int(Some((0, i32::MAX))),
                _ => Shape::Top,
            },
            (B::Append, [s, x]) => {
                let elem_x = self.infer_expr(x, in_prime, vars, env, steps);
                match self.infer_expr(s, in_prime, vars, env, steps) {
                    Shape::Tuple(mut ts) => {
                        ts.push(elem_x);
                        Shape::Tuple(ts)
                    }
                    Shape::Seq { elem, min_len, max_len } => Shape::Seq {
                        elem: Box::new(join_shape(&elem, &elem_x)),
                        min_len: min_len.saturating_add(1),
                        max_len: max_len.and_then(|m| m.checked_add(1)).filter(|&v| v <= MAX_I32_U32),
                    },
                    _ => Shape::Top,
                }
            }
            (B::Concat, [a, b]) => {
                let sa = self.infer_expr(a, in_prime, vars, env, steps);
                let sb = self.infer_expr(b, in_prime, vars, env, steps);
                match (sa, sb) {
                    (Shape::Tuple(mut ta), Shape::Tuple(tb)) => {
                        ta.extend(tb);
                        Shape::Tuple(ta)
                    }
                    (a, b) => match (seq_elem_bounds(&a), seq_elem_bounds(&b)) {
                        (Some((ea, lo1, hi1)), Some((eb, lo2, hi2))) => Shape::Seq {
                            elem: Box::new(join_shape(&ea, &eb)),
                            min_len: lo1.saturating_add(lo2),
                            max_len: hi1.and_then(|x| hi2.and_then(|y| x.checked_add(y))).filter(|&v| v <= MAX_I32_U32),
                        },
                        _ => Shape::Top,
                    },
                }
            }
            (B::Head, [s]) => match self.infer_expr(s, in_prime, vars, env, steps) {
                Shape::Bottom => Shape::Bottom,
                Shape::Tuple(ts) if !ts.is_empty() => ts[0].clone(),
                Shape::Tuple(_) => Shape::Bottom,
                Shape::Seq { elem, .. } => *elem,
                _ => Shape::Top,
            },
            (B::Tail, [s]) => match self.infer_expr(s, in_prime, vars, env, steps) {
                Shape::Bottom => Shape::Bottom,
                Shape::Tuple(ts) if !ts.is_empty() => Shape::Tuple(ts[1..].to_vec()),
                Shape::Tuple(_) => Shape::Bottom,
                Shape::Seq { elem, min_len, max_len } => {
                    Shape::Seq { elem, min_len: min_len.saturating_sub(1), max_len: max_len.map(|m| m.saturating_sub(1)) }
                }
                _ => Shape::Top,
            },
            (B::SubSeq | B::SelectSeq, [s, ..]) => match seq_elem_bounds(&self.infer_expr(s, in_prime, vars, env, steps)) {
                Some((elem, _, max_len)) => Shape::Seq { elem: Box::new(elem), min_len: 0, max_len },
                None => Shape::Top,
            },
            (B::ColonGt, [k, v]) => {
                let ks = self.infer_expr(k, in_prime, vars, env, steps);
                let vs = self.infer_expr(v, in_prime, vars, env, steps);
                // Do NOT mark `Bool` literal singletons (`TRUE :> v`) as `exact_dom` because
                // `Shape::Bool` represents `{TRUE, FALSE}`, not `{TRUE}`.
                let exact_dom = matches!(&*k.kind, ExprKind::Num(_) | ExprKind::Str(_));
                Shape::Func { dom: Box::new(ks), exact_dom, range: Box::new(vs), max_dom: Some(1) }
            }
            (B::AtAt, [a, b]) => {
                let sa = self.infer_expr(a, in_prime, vars, env, steps);
                let sb = self.infer_expr(b, in_prime, vars, env, steps);
                match (fn_dom_range(&sa), fn_dom_range(&sb)) {
                    (Some((da, ra, ca)), Some((db, rb, cb))) => Shape::Func {
                        dom: Box::new(join_shape(&da, &db)),
                        exact_dom: false,
                        range: Box::new(join_shape(&ra, &rb)),
                        max_dom: ca.and_then(|x| cb.and_then(|y| x.checked_add(y))).filter(|&v| v <= MAX_I32_U32),
                    },
                    _ => Shape::Top,
                }
            }
            (B::Plus, [a, b]) => {
                arith_bin_shape(self.infer_expr(a, in_prime, vars, env, steps), self.infer_expr(b, in_prime, vars, env, steps), arith_add)
            }
            (B::Minus, [a, b]) => {
                arith_bin_shape(self.infer_expr(a, in_prime, vars, env, steps), self.infer_expr(b, in_prime, vars, env, steps), arith_sub)
            }
            (B::Mul, [a, b]) => {
                arith_bin_shape(self.infer_expr(a, in_prime, vars, env, steps), self.infer_expr(b, in_prime, vars, env, steps), arith_mul)
            }
            (B::Neg, [a]) => match self.infer_expr(a, in_prime, vars, env, steps) {
                Shape::Int(Some((lo, hi))) => arith_neg(lo, hi).map_or(Shape::Int(None), |b| Shape::Int(Some(b))),
                Shape::Int(None) => Shape::Int(None),
                _ => Shape::Top,
            },
            (B::Div, [a, b]) => arith_bin_shape(
                self.infer_expr(a, in_prime, vars, env, steps),
                self.infer_expr(b, in_prime, vars, env, steps),
                arith_div_pos,
            ),
            (B::Mod, [a, b]) => arith_bin_shape(
                self.infer_expr(a, in_prime, vars, env, steps),
                self.infer_expr(b, in_prime, vars, env, steps),
                arith_mod_pos,
            ),
            (B::Pow, [a, b]) => {
                arith_bin_shape(self.infer_expr(a, in_prime, vars, env, steps), self.infer_expr(b, in_prime, vars, env, steps), arith_pow)
            }
            (B::FoldSet, [op_lam, base, set]) => {
                let Some(ac) = classify_ac_op(op_lam) else { return Shape::Top };
                let base_s = self.infer_expr(base, in_prime, vars, env, steps);
                let (elem_s, finite, max_card) = self.infer_set_info(set, in_prime, vars, env, steps);
                if !finite {
                    return Shape::Top;
                }
                self.infer_ac_fold_shape(ac, &base_s, &elem_s, max_card)
            }
            (B::FoldFunction, [op_lam, base, fun]) => {
                let Some(ac) = classify_ac_op(op_lam) else { return Shape::Top };
                let base_s = self.infer_expr(base, in_prime, vars, env, steps);
                let fun_s = self.infer_expr(fun, in_prime, vars, env, steps);
                let Some((dom, range, max_dom)) = fn_dom_range(&fun_s) else { return Shape::Top };
                let max_card = max_dom.or_else(|| shape_universe_size(&dom, self.groups));
                self.infer_ac_fold_shape(ac, &base_s, &range, max_card)
            }
            (B::FoldFunctionOnSet, [op_lam, base, fun, indices]) => {
                let Some(ac) = classify_ac_op(op_lam) else { return Shape::Top };
                let base_s = self.infer_expr(base, in_prime, vars, env, steps);
                let fun_s = self.infer_expr(fun, in_prime, vars, env, steps);
                let (_, finite, max_card) = self.infer_set_info(indices, in_prime, vars, env, steps);
                if !finite {
                    return Shape::Top;
                }
                let Some((_, range, _)) = fn_dom_range(&fun_s) else { return Shape::Top };
                self.infer_ac_fold_shape(ac, &base_s, &range, max_card)
            }
            (B::MapThenFoldSet, [op_lam, base, f_lam, choose_lam, set, ..]) if args.len() == 5 || args.len() == 6 => {
                let Some(ac) = classify_ac_op(op_lam) else { return Shape::Top };
                if !is_chooses_first_lambda(choose_lam) {
                    return Shape::Top;
                }
                let ExprKind::Lambda { params, body } = &*f_lam.kind else { return Shape::Top };
                let [p] = params.as_slice() else { return Shape::Top };
                let base_s = self.infer_expr(base, in_prime, vars, env, steps);
                let (elem_s, finite, max_card) = self.infer_set_info(set, in_prime, vars, env, steps);
                if !finite {
                    return Shape::Top;
                }
                let mut local_env = env.clone();
                local_env.bind_local(*p, elem_s, None);
                let mapped_s = self.infer_expr(body, in_prime, vars, &local_env, steps);
                self.infer_ac_fold_shape(ac, &base_s, &mapped_s, max_card)
            }
            (B::FoldSeq, [op_lam, base, seq]) => {
                let seq_s = self.infer_expr(seq, in_prime, vars, env, steps);
                if is_seq_shape(&seq_s) {
                    self.infer_seq_fold_shape(op_lam, base, seq, false, false, in_prime, vars, env, steps)
                } else {
                    let Some(ac) = classify_ac_op(op_lam) else { return Shape::Top };
                    let base_s = self.infer_expr(base, in_prime, vars, env, steps);
                    let Some((dom, range, max_dom)) = fn_dom_range(&seq_s) else { return Shape::Top };
                    let max_card = max_dom.or_else(|| shape_universe_size(&dom, self.groups));
                    self.infer_ac_fold_shape(ac, &base_s, &range, max_card)
                }
            }
            (B::FoldLeft, [op_lam, base, seq]) => self.infer_seq_fold_shape(op_lam, base, seq, false, true, in_prime, vars, env, steps),
            (B::FoldRight, [op_lam, seq, base]) => self.infer_seq_fold_shape(op_lam, base, seq, false, false, in_prime, vars, env, steps),
            (B::FoldLeftDomain, [op_lam, base, seq]) => {
                self.infer_seq_fold_shape(op_lam, base, seq, true, true, in_prime, vars, env, steps)
            }
            (B::FoldRightDomain, [op_lam, seq, base]) => {
                self.infer_seq_fold_shape(op_lam, base, seq, true, false, in_prime, vars, env, steps)
            }
            _ => self.infer_bag_builtin(op, args, in_prime, vars, env, steps).unwrap_or(Shape::Top),
        }
    }

    pub(super) fn infer_ac_fold_shape(&self, ac: AcOpKind, base: &Shape, elem: &Shape, max_card: Option<u32>) -> Shape {
        if matches!(base, Shape::Bottom) {
            return Shape::Bottom;
        }
        if max_card == Some(0) || matches!(elem, Shape::Bottom) {
            return base.clone();
        }
        match ac {
            AcOpKind::IntAdd | AcOpKind::IntMul => match (base, elem, max_card) {
                (Shape::Int(Some(b_bounds)), Shape::Int(Some(e_bounds)), Some(c)) => {
                    Shape::Int(super::folds::ac_int_fold_bounds(ac, *b_bounds, *e_bounds, c))
                }
                (Shape::Int(_), Shape::Int(_), _) => Shape::Int(None),
                _ => Shape::Top,
            },
            AcOpKind::SetCup => match (base, elem) {
                (Shape::Set { elem: be, finite: bf, max_card: bc }, Shape::Set { elem: ee, finite: ef, max_card: ec }) => {
                    let joined = join_shape(be, ee);
                    let card = max_card
                        .and_then(|c| ec.and_then(|e| bc.and_then(|b| c.checked_mul(e)?.checked_add(b))))
                        .or_else(|| shape_universe_size(&joined, self.groups))
                        .filter(|&v| v <= MAX_I32_U32);
                    Shape::Set { elem: Box::new(joined), finite: *bf && *ef, max_card: card }
                }
                _ => Shape::Top,
            },
            AcOpKind::SetCap => match (base, elem) {
                (Shape::Set { elem: be, finite: bf, max_card: bc }, Shape::Set { finite: ef, .. }) => {
                    Shape::Set { elem: be.clone(), finite: *bf && *ef, max_card: *bc }
                }
                _ => Shape::Top,
            },
            AcOpKind::BoolAnd | AcOpKind::BoolOr => {
                if is_bool_shape(base) && is_bool_shape(elem) {
                    Shape::Bool
                } else {
                    Shape::Top
                }
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    pub(super) fn infer_seq_fold_shape(
        &self,
        op_lam: &Expr,
        base: &Expr,
        seq: &Expr,
        on_domain: bool,
        acc_first: bool,
        in_prime: bool,
        vars: &[Shape],
        env: &CheckEnv,
        steps: &mut usize,
    ) -> Shape {
        let ExprKind::Lambda { params, body } = &*op_lam.kind else { return Shape::Top };
        let [p0, p1] = params.as_slice() else { return Shape::Top };
        let seq_s = self.infer_expr(seq, in_prime, vars, env, steps);
        let Some((elem_s, _, max_len)) = seq_elem_bounds(&seq_s) else { return Shape::Top };
        let item_s = if on_domain {
            match max_len {
                Some(0) => Shape::Bottom,
                Some(hi) if hi <= MAX_I32_U32 => Shape::Int(Some((1, hi as i32))),
                _ => Shape::Int(None),
            }
        } else {
            elem_s
        };
        let mut acc = self.infer_expr(base, in_prime, vars, env, steps);
        if max_len == Some(0) {
            return acc;
        }
        let iters = max_len.map_or(16, |n| n.min(64));
        let (acc_param, item_param) = if acc_first { (*p0, *p1) } else { (*p1, *p0) };
        let mut converged = false;
        for _ in 0..iters {
            let mut local_env = env.clone();
            local_env.bind_local(acc_param, acc.clone(), None);
            local_env.bind_local(item_param, item_s.clone(), None);
            let next = self.infer_expr(body, in_prime, vars, &local_env, steps);
            let joined = cap_shape(join_shape(&acc, &next));
            if joined == acc {
                converged = true;
                break;
            }
            acc = joined;
        }
        if !converged && max_len.is_none_or(|n| n > 64) {
            acc = widen_shape(&acc);
            let mut local_env = env.clone();
            local_env.bind_local(acc_param, acc.clone(), None);
            local_env.bind_local(item_param, item_s, None);
            let next = self.infer_expr(body, in_prime, vars, &local_env, steps);
            if !shape_leq(&next, &acc) {
                return Shape::Top;
            }
        }
        acc
    }

    pub(super) fn infer_set_info(
        &self,
        set: &Expr,
        in_prime: bool,
        vars: &[Shape],
        env: &CheckEnv,
        steps: &mut usize,
    ) -> (Shape, bool, Option<u32>) {
        match self.infer_expr(set, in_prime, vars, env, steps) {
            Shape::Set { elem, finite, max_card } => {
                let bound = if finite { max_card.or_else(|| shape_universe_size(&elem, self.groups)) } else { None };
                (*elem, finite, bound)
            }
            Shape::Bottom => (Shape::Bottom, true, Some(0)),
            _ => (Shape::Top, false, None),
        }
    }

    fn infer_set_elem(&self, set: &Expr, in_prime: bool, vars: &[Shape], env: &CheckEnv, steps: &mut usize) -> Shape {
        self.infer_set_info(set, in_prime, vars, env, steps).0
    }

    pub(super) fn set_elem_shape(&self, set: &Expr, in_prime: bool, env: &CheckEnv, steps: &mut usize) -> Shape {
        self.infer_set_elem(set, in_prime, &self.var_shapes, env, steps)
    }

    pub(super) fn cfg_value_shape(&self, v: &CfgValue) -> Shape {
        match v {
            CfgValue::Bool(_) => Shape::Bool,
            CfgValue::Int(n) => i32::try_from(*n).map_or(Shape::Top, |k| Shape::Int(Some((k, k)))),
            CfgValue::Str(s) => Shape::Str(Some(BTreeSet::from([Arc::from(s.as_str())]))),
            CfgValue::ModelValue(m) => self.model_atom_shape(m),
            CfgValue::Tuple(es) => Shape::Tuple(es.iter().map(|x| self.cfg_value_shape(x)).collect()),
            CfgValue::Set(es) => {
                let mut elem = Shape::Bottom;
                for x in es {
                    elem = join_shape(&elem, &self.cfg_value_shape(x));
                }
                Shape::Set { elem: Box::new(elem), finite: true, max_card: u32::try_from(es.len()).ok() }
            }
        }
    }

    pub(super) fn const_exact_i32(&self, e: &Expr) -> Option<i32> {
        self.const_exact_i32_inner(e, &mut Vec::new(), 0)
    }

    fn const_exact_i32_inner(&self, e: &Expr, seen: &mut Vec<ConstId>, depth: usize) -> Option<i32> {
        if depth >= 32 {
            return None;
        }
        match &*e.kind {
            ExprKind::Num(n) => i32::try_from(*n).ok(),
            ExprKind::CfgLiteral(v) => match &**v {
                CfgValue::Int(n) => i32::try_from(*n).ok(),
                _ => None,
            },
            ExprKind::Const(c) => match self.consts.get(c)? {
                ConstInfo::Value(CfgValue::Int(n)) => i32::try_from(*n).ok(),
                ConstInfo::Subst(def_id) => {
                    if seen.contains(c) {
                        return None;
                    }
                    seen.push(*c);
                    let res = match &self.program.defs[def_id.idx()].kind {
                        DefKind::Op(body) => self.const_exact_i32_inner(body, seen, depth + 1),
                        _ => None,
                    };
                    seen.pop();
                    res
                }
                _ => None,
            },
            ExprKind::Builtin { op: B::Neg, args } if args.len() == 1 => {
                self.const_exact_i32_inner(&args[0], seen, depth + 1)?.checked_neg()
            }
            ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => self.const_exact_i32_inner(&args[0], seen, depth + 1),
            _ => None,
        }
    }

    fn cfg_set_is_exact(&self, es: &[CfgValue]) -> bool {
        if es.is_empty() {
            return true;
        }
        let mut bools = [false; 2];
        let mut ints = BTreeSet::new();
        let mut strs = 0usize;
        let mut model_keys: BTreeSet<&str> = BTreeSet::new();
        let mut unmoved_count = 0usize;
        for v in es {
            match v {
                CfgValue::Bool(b) => bools[usize::from(*b)] = true,
                CfgValue::Int(n) => {
                    let Ok(k) = i32::try_from(*n) else { return false };
                    ints.insert(k);
                }
                CfgValue::Str(_) => strs += 1,
                CfgValue::ModelValue(m) => {
                    if self.all_keys.contains(m.as_str()) {
                        model_keys.insert(m.as_str());
                    } else {
                        unmoved_count += 1;
                    }
                }
                _ => return false,
            }
        }
        if (bools[0] || bools[1]) && !(bools[0] && bools[1]) {
            return false;
        }
        if !ints.is_empty() {
            let lo = *ints.iter().next().unwrap();
            let hi = *ints.iter().next_back().unwrap();
            if (hi as i128 - lo as i128 + 1) != ints.len() as i128 {
                return false;
            }
        }
        if strs > MAX_STR_SET || unmoved_count > MAX_UNMOVED_SET {
            return false;
        }
        for g in self.groups {
            let count = g.key_set.iter().filter(|k| model_keys.contains(k.as_ref())).count();
            if count > 0 && count != g.key_set.len() {
                return false;
            }
        }
        true
    }

    /// True ONLY when `s` is statically guaranteed to evaluate to the exact set
    /// represented by its inferred element shape (no dynamic subsets, no integer gaps).
    pub(super) fn is_exact_static_set(&self, s: &Expr) -> bool {
        self.is_exact_static_set_inner(s, &mut Vec::new(), 0)
    }

    fn is_exact_static_set_inner(&self, s: &Expr, seen: &mut Vec<ConstId>, depth: usize) -> bool {
        if depth >= 32 {
            return false;
        }
        match &*s.kind {
            ExprKind::Builtin { op: B::Boolean, args } if args.is_empty() => true,
            ExprKind::Builtin { op: B::DotDot, args } if args.len() == 2 => {
                self.const_exact_i32(&args[0]).is_some() && self.const_exact_i32(&args[1]).is_some()
            }
            ExprKind::Builtin { op: B::Times, args } if args.len() >= 2 => {
                args.iter().all(|a| self.is_exact_static_set_inner(a, seen, depth + 1))
            }
            ExprKind::Builtin { op: B::Cup, args } if args.len() == 2 => {
                if !self.is_exact_static_set_inner(&args[0], seen, depth + 1) || !self.is_exact_static_set_inner(&args[1], seen, depth + 1)
                {
                    return false;
                }
                let mut steps = 500;
                let sa = self.infer_set_elem(&args[0], false, &self.var_shapes, &CheckEnv::default(), &mut steps);
                let sb = self.infer_set_elem(&args[1], false, &self.var_shapes, &CheckEnv::default(), &mut steps);
                // Only allow `Cup` exactness on exact scalar sets (`Bool`, `Str`, `Model`):
                // joining `Int` intervals can add gaps and joining `Tuple`s componentwise loses
                // correlation (e.g. `({"a"} \X {"a"}) \cup ({"b"} \X {"b"})` would include `<<"a","b">>`).
                shape_is_exact_cup_scalar(&sa) && shape_is_exact_cup_scalar(&sb) && !matches!(join_shape(&sa, &sb), Shape::Top)
            }
            ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => self.is_exact_static_set_inner(&args[0], seen, depth + 1),
            ExprKind::CfgLiteral(v) => match &**v {
                CfgValue::Set(es) => self.cfg_set_is_exact(es),
                _ => false,
            },
            ExprKind::Const(c) => match self.consts.get(c) {
                Some(ConstInfo::Value(CfgValue::Set(es))) => self.cfg_set_is_exact(es),
                Some(ConstInfo::Subst(def_id)) => {
                    if seen.contains(c) {
                        return false;
                    }
                    seen.push(*c);
                    let res = match &self.program.defs[def_id.idx()].kind {
                        DefKind::Op(body) => self.is_exact_static_set_inner(body, seen, depth + 1),
                        _ => false,
                    };
                    seen.pop();
                    res
                }
                _ => false,
            },
            ExprKind::SetEnum(es) => {
                let mut vals = Vec::with_capacity(es.len());
                for x in es {
                    match &*x.kind {
                        ExprKind::Bool(b) => vals.push(CfgValue::Bool(*b)),
                        ExprKind::Num(n) => {
                            let Ok(k) = i64::try_from(*n) else { return false };
                            vals.push(CfgValue::Int(k));
                        }
                        ExprKind::Str(st) => vals.push(CfgValue::Str(st.to_string())),
                        ExprKind::CfgLiteral(v) => match &**v {
                            v @ (CfgValue::Bool(_) | CfgValue::Int(_) | CfgValue::Str(_) | CfgValue::ModelValue(_)) => {
                                vals.push(v.clone());
                            }
                            _ => return false,
                        },
                        ExprKind::Const(c) => match self.consts.get(c) {
                            Some(ConstInfo::Value(
                                v @ (CfgValue::Bool(_) | CfgValue::Int(_) | CfgValue::Str(_) | CfgValue::ModelValue(_)),
                            )) => {
                                vals.push((*v).clone());
                            }
                            _ => return false,
                        },
                        _ => return false,
                    }
                }
                self.cfg_set_is_exact(&vals)
            }
            _ => false,
        }
    }

    pub(super) fn model_atom_shape(&self, m: &str) -> Shape {
        let mv_type = MvType::of_name(m);
        for (gi, g) in self.groups.iter().enumerate() {
            if g.key_set.contains(m) {
                return Shape::Model { groups: 1u16 << gi, mv_type, unmoved: Some(BTreeSet::new()) };
            }
        }
        Shape::Model { groups: 0, mv_type, unmoved: Some(BTreeSet::from([Arc::from(m)])) }
    }

    // ---- Sound narrowing (exact single-atom exclusion & integer bounds ONLY) ----

    pub(super) fn apply_fact(&self, cond: &Expr, positive: bool, in_prime: bool, env: &mut CheckEnv) {
        self.apply_fact_with_vars(cond, positive, in_prime, &self.var_shapes, env);
    }

    /// Refine the element shape of `{x \in S : pred}` by assuming `pred` on the
    /// bound element. Every element of the filtered set satisfies `pred`, so the
    /// existing place narrowing (tagged record unions, integer ranges,
    /// membership) applies. Only the single-binder form is refined.
    pub(super) fn narrow_filter_elem(
        &self,
        bound: &Bound,
        pred: &Expr,
        elem: &Shape,
        in_prime: bool,
        vars: &[Shape],
        env: &CheckEnv,
    ) -> Shape {
        let BoundVars::Many(ids) = &bound.vars else { return elem.clone() };
        let [id] = ids.as_slice() else { return elem.clone() };
        let mut local_env = env.clone();
        local_env.bind_local(*id, elem.clone(), None);
        self.apply_fact_with_vars(pred, true, in_prime, vars, &mut local_env);
        local_env.locals.get(id).cloned().unwrap_or_else(|| elem.clone())
    }

    fn apply_fact_with_vars(&self, cond: &Expr, positive: bool, in_prime: bool, vars: &[Shape], env: &mut CheckEnv) {
        match &*cond.kind {
            ExprKind::Bool(b) => {
                if *b != positive {
                    env.unreachable = true;
                }
            }
            ExprKind::And(es) if positive => {
                for item in es {
                    self.apply_fact_with_vars(item, true, in_prime, vars, env);
                }
            }
            ExprKind::Or(es) if !positive => {
                for item in es {
                    self.apply_fact_with_vars(item, false, in_prime, vars, env);
                }
            }
            ExprKind::Builtin { op: B::Not, args } if args.len() == 1 => {
                self.apply_fact_with_vars(&args[0], !positive, in_prime, vars, env);
            }
            ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 => {
                if !positive {
                    if matches!(&*args[1].kind, ExprKind::SetEnum(es) if es.is_empty()) {
                        env.nonempty_sets.push((args[0].clone(), in_prime));
                    } else if matches!(&*args[0].kind, ExprKind::SetEnum(es) if es.is_empty()) {
                        env.nonempty_sets.push((args[1].clone(), in_prime));
                    }
                }
                self.narrow_eq(&args[0], &args[1], positive, in_prime, vars, env);
                self.narrow_eq(&args[1], &args[0], positive, in_prime, vars, env);
            }
            ExprKind::Builtin { op: B::Neq, args } if args.len() == 2 => {
                if positive {
                    if matches!(&*args[1].kind, ExprKind::SetEnum(es) if es.is_empty()) {
                        env.nonempty_sets.push((args[0].clone(), in_prime));
                    } else if matches!(&*args[0].kind, ExprKind::SetEnum(es) if es.is_empty()) {
                        env.nonempty_sets.push((args[1].clone(), in_prime));
                    }
                }
                self.narrow_eq(&args[0], &args[1], !positive, in_prime, vars, env);
                self.narrow_eq(&args[1], &args[0], !positive, in_prime, vars, env);
            }
            ExprKind::Builtin { op: B::In, args } if positive && args.len() == 2 => {
                env.nonempty_sets.push((args[1].clone(), in_prime));
                env.proven_members.push((args[0].clone(), args[1].clone(), in_prime));
                let mut steps = 2000;
                let elem = self.infer_set_elem(&args[1], in_prime, vars, env, &mut steps);
                // `r.f \in S` rules out tagged-record-union variants whose `f`
                // cannot be in `S`, exactly like `r.f = lit` does.
                if let ExprKind::Field { record, field } = &*args[0].kind {
                    if let Some(cur) = self.read_place(record, in_prime, vars, env) {
                        if let Some(narrowed) = narrow_record_field_eq(&cur, field, &elem, true) {
                            self.write_place(record, in_prime, vars, narrowed, None, env);
                        }
                    }
                }
                let origin = match &*args[1].kind {
                    ExprKind::Builtin { op: B::Domain | B::BagToSet, args: da } if da.len() == 1 => {
                        env.proven_in_dom.push((args[0].clone(), da[0].clone(), in_prime));
                        Some((da[0].clone(), in_prime))
                    }
                    _ => None,
                };
                if let Some(cur) = self.read_place(&args[0], in_prime, vars, env) {
                    let narrowed = narrow_shape(&cur, &elem);
                    if !matches!(cur, Shape::Bottom) && matches!(narrowed, Shape::Bottom) {
                        env.unreachable = true;
                    }
                    self.write_place(&args[0], in_prime, vars, narrowed, origin, env);
                }
            }
            ExprKind::Builtin { op: B::BagIn, args } if positive && args.len() == 2 => {
                let mut steps = 2000;
                let sb = self.infer_expr(&args[1], in_prime, vars, env, &mut steps);
                env.proven_in_dom.push((args[0].clone(), args[1].clone(), in_prime));
                let origin = Some((args[1].clone(), in_prime));
                if let Some((dom, _, _)) = super::bags::bag_fn_info(&sb) {
                    if let Some(cur) = self.read_place(&args[0], in_prime, vars, env) {
                        let narrowed = narrow_shape(&cur, &dom);
                        self.write_place(&args[0], in_prime, vars, narrowed, origin, env);
                    }
                }
            }
            ExprKind::Builtin { op: op @ (B::Lt | B::Le | B::Gt | B::Ge), args } if args.len() == 2 => {
                let eff = if positive {
                    *op
                } else {
                    match op {
                        B::Lt => B::Ge,
                        B::Le => B::Gt,
                        B::Gt => B::Le,
                        B::Ge => B::Lt,
                        _ => unreachable!(),
                    }
                };
                if let Some(k) = self.const_exact_i32(&args[1]) {
                    self.narrow_int_cmp(&args[0], eff, k, in_prime, vars, env);
                } else if let Some(k) = self.const_exact_i32(&args[0]) {
                    let flipped = match eff {
                        B::Lt => B::Gt,
                        B::Le => B::Ge,
                        B::Gt => B::Lt,
                        B::Ge => B::Le,
                        _ => unreachable!(),
                    };
                    self.narrow_int_cmp(&args[1], flipped, k, in_prime, vars, env);
                }
            }
            _ => {}
        }
    }

    fn narrow_eq(&self, place: &Expr, other: &Expr, eq: bool, in_prime: bool, vars: &[Shape], env: &mut CheckEnv) {
        // Sound tagged-record union narrowing: `m.field = lit` or `m.field /= lit`
        // filters variants of a `Shape::Union` of `Shape::Record`s held in `m`.
        if let ExprKind::Field { record, field } = &*place.kind {
            if let Some(cur) = self.read_place(record, in_prime, vars, env) {
                let mut steps = 2000;
                let other_s = self.infer_expr(other, in_prime, vars, env, &mut steps);
                if let Some(narrowed) = narrow_record_field_eq(&cur, field, &other_s, eq) {
                    self.write_place(record, in_prime, vars, narrowed, None, env);
                }
            }
            return;
        }
        // Sound `Len(seq) = k` narrowing:
        if let ExprKind::Builtin { op: B::Len, args } = &*place.kind {
            if args.len() == 1 {
                if let Some(k) = self.const_exact_i32(other) {
                    if eq {
                        self.narrow_seq_len(&args[0], B::Ge, k, in_prime, vars, env);
                        self.narrow_seq_len(&args[0], B::Le, k, in_prime, vars, env);
                    } else if k == 0 {
                        self.narrow_seq_len(&args[0], B::Gt, 0, in_prime, vars, env);
                    }
                }
            }
            return;
        }
        // Sound `Cardinality(S) # 0` / `Cardinality(S) = k` (`k >= 1`) non-emptiness tracking:
        if let ExprKind::Builtin { op: B::Cardinality, args } = &*place.kind {
            if args.len() == 1 {
                if let Some(k) = self.const_exact_i32(other) {
                    if (!eq && k == 0) || (eq && k >= 1) {
                        env.nonempty_sets.push((args[0].clone(), in_prime));
                    }
                }
            }
            return;
        }
        // Expression-level narrowing for non-var `FnApp` (e.g. constant tuple `TaskParent[t] # 0`).
        let Some(cur) = self.read_place(place, in_prime, vars, env) else {
            if matches!(&*place.kind, ExprKind::FnApp { .. }) {
                let mut steps = 2000;
                let cur = self.infer_expr(place, in_prime, vars, env, &mut steps);
                let other_s = self.infer_expr(other, in_prime, vars, env, &mut steps);
                if eq {
                    if !matches!(cur, Shape::Top | Shape::Bottom) && !matches!(other_s, Shape::Top | Shape::Bottom) {
                        let narrowed = narrow_shape(&cur, &other_s);
                        if matches!(narrowed, Shape::Bottom) {
                            env.unreachable = true;
                        }
                        if narrowed != cur {
                            env.expr_overrides.push((place.clone(), in_prime, narrowed));
                        }
                    }
                } else if let Some(excluded) = exclude_single_value(&cur, &other_s) {
                    if !matches!(cur, Shape::Bottom) && matches!(excluded, Shape::Bottom) {
                        env.unreachable = true;
                    }
                    env.expr_overrides.push((place.clone(), in_prime, excluded));
                }
            } else {
                let mut steps = 2000;
                let sa = self.infer_expr(place, in_prime, vars, env, &mut steps);
                let sb = self.infer_expr(other, in_prime, vars, env, &mut steps);
                if (!eq && is_singleton_equal(&sa, &sb))
                    || (eq
                        && !matches!(sa, Shape::Top | Shape::Bottom)
                        && !matches!(sb, Shape::Top | Shape::Bottom)
                        && matches!(narrow_shape(&sa, &sb), Shape::Bottom))
                {
                    env.unreachable = true;
                }
            }
            return;
        };
        let mut steps = 2000;
        let other_s = self.infer_expr(other, in_prime, vars, env, &mut steps);
        if eq {
            if let ExprKind::Local(l) = &*place.kind {
                if let Some(ok) = place_key_of(other, in_prime) {
                    let lk = PlaceKey::Local(*l);
                    let extra: Vec<_> = env
                        .fn_app_overrides
                        .iter()
                        .filter(|((_, _, ks), _)| ks.contains(&ok))
                        .map(|((v, pr, ks), sh)| {
                            let mapped: Vec<_> = ks.iter().map(|&k| if k == ok { lk } else { k }).collect();
                            ((*v, *pr, mapped), sh.clone())
                        })
                        .collect();
                    for (k, sh) in extra {
                        env.fn_app_overrides.insert(k, sh);
                    }
                }
            }
            if !matches!(other_s, Shape::Top | Shape::Bottom) {
                let narrowed = narrow_shape(&cur, &other_s);
                if !matches!(cur, Shape::Bottom) && matches!(narrowed, Shape::Bottom) {
                    env.unreachable = true;
                }
                self.write_place(place, in_prime, vars, narrowed, None, env);
            }
        } else {
            // `l \in DOMAIN f \cup {excl} /\ l # excl ==> l \in DOMAIN f` (used by `BagsExt!BagAdd`).
            if let ExprKind::Local(l) = &*place.kind {
                if let Some((func, fp, excl)) = env.local_dom_except.get(l).cloned() {
                    if expr_struct_eq(other, in_prime, &excl, fp) {
                        env.local_dom.insert(*l, (func, fp));
                    }
                }
            }
            // `seq # <<>>` proves `min_len >= 1` (and makes an empty tuple unreachable):
            if matches!(&other_s, Shape::Tuple(ts) if ts.is_empty()) {
                if matches!(&cur, Shape::Tuple(ts) if ts.is_empty()) {
                    env.unreachable = true;
                    self.write_place(place, in_prime, vars, Shape::Bottom, None, env);
                    return;
                }
                if let Shape::Seq { elem, min_len, max_len } = &cur {
                    self.write_place(
                        place,
                        in_prime,
                        vars,
                        Shape::Seq { elem: elem.clone(), min_len: (*min_len).max(1), max_len: *max_len },
                        None,
                        env,
                    );
                    return;
                }
            }
            // Exact single-value exclusion ONLY: never remove all unmoved values on `slot # A`!
            if let Some(excluded) = exclude_single_value(&cur, &other_s) {
                if !matches!(cur, Shape::Bottom) && matches!(excluded, Shape::Bottom) {
                    env.unreachable = true;
                }
                self.write_place(place, in_prime, vars, excluded, None, env);
            }
        }
    }

    fn narrow_int_cmp(&self, place: &Expr, op: B, k: i32, in_prime: bool, vars: &[Shape], env: &mut CheckEnv) {
        if let ExprKind::Builtin { op: B::Cardinality, args } = &*place.kind {
            if args.len() == 1 && ((op == B::Gt && k >= 0) || (op == B::Ge && k >= 1)) {
                env.nonempty_sets.push((args[0].clone(), in_prime));
            }
            return;
        }
        if let ExprKind::Builtin { op: B::Len, args } = &*place.kind {
            if args.len() == 1 {
                self.narrow_seq_len(&args[0], op, k, in_prime, vars, env);
            }
            return;
        }
        if let ExprKind::Builtin { op: B::BagCardinality, args } = &*place.kind {
            if args.len() == 1 {
                self.narrow_bag_card(&args[0], op, k, in_prime, vars, env);
            }
            return;
        }
        if let ExprKind::Builtin { op: B::CopiesIn, args } = &*place.kind {
            if let [elem, bag] = args.as_slice() {
                self.narrow_copies_in((elem, bag), op, k, in_prime, vars, env);
            }
            return;
        }
        let Some(Shape::Int(bounds)) = self.read_place(place, in_prime, vars, env) else {
            let mut steps = 2000;
            if let Shape::Int(Some((lo, hi))) = self.infer_expr(place, in_prime, vars, env, &mut steps) {
                let (nlo, nhi) = match op {
                    B::Lt => (lo, hi.min(k.saturating_sub(1))),
                    B::Le => (lo, hi.min(k)),
                    B::Gt => (lo.max(k.saturating_add(1)), hi),
                    B::Ge => (lo.max(k), hi),
                    _ => return,
                };
                if nlo > nhi {
                    env.unreachable = true;
                }
            }
            return;
        };
        let (lo, hi) = bounds.unwrap_or((i32::MIN, i32::MAX));
        let (nlo, nhi) = match op {
            B::Lt => (lo, hi.min(k.saturating_sub(1))),
            B::Le => (lo, hi.min(k)),
            B::Gt => (lo.max(k.saturating_add(1)), hi),
            B::Ge => (lo.max(k), hi),
            _ => return,
        };
        if nlo <= nhi {
            self.write_place(place, in_prime, vars, Shape::Int(Some((nlo, nhi))), None, env);
        } else {
            env.unreachable = true;
        }
    }

    fn narrow_seq_len(&self, place: &Expr, op: B, k: i32, in_prime: bool, vars: &[Shape], env: &mut CheckEnv) {
        let Some(cur) = self.read_place(place, in_prime, vars, env) else { return };
        if let Shape::Tuple(ts) = &cur {
            let len = ts.len() as i32;
            let holds = match op {
                B::Lt => len < k,
                B::Le => len <= k,
                B::Gt => len > k,
                B::Ge => len >= k,
                _ => true,
            };
            if !holds {
                self.write_place(place, in_prime, vars, Shape::Bottom, None, env);
            }
            return;
        }
        let Shape::Seq { elem, min_len, max_len } = cur else { return };
        let (mut lo, mut hi) = (min_len, max_len);
        match op {
            B::Lt => {
                if k <= 0 {
                    return;
                }
                let bound = (k - 1) as u32;
                hi = Some(hi.map_or(bound, |m| m.min(bound)));
            }
            B::Le => {
                if k < 0 {
                    return;
                }
                let bound = k as u32;
                hi = Some(hi.map_or(bound, |m| m.min(bound)));
            }
            B::Gt => {
                if k >= 0 {
                    lo = lo.max((k as u32).saturating_add(1));
                }
            }
            B::Ge => {
                if k >= 0 {
                    lo = lo.max(k as u32);
                }
            }
            _ => return,
        }
        if hi.is_none_or(|h| lo <= h) {
            self.write_place(place, in_prime, vars, Shape::Seq { elem, min_len: lo, max_len: hi }, None, env);
        }
    }

    fn narrow_bag_card(&self, bag: &Expr, op: B, k: i32, in_prime: bool, vars: &[Shape], env: &mut CheckEnv) {
        let max_total = match op {
            B::Lt => k.checked_sub(1),
            B::Le => Some(k),
            _ => None,
        };
        let Some(max_total) = max_total else { return };
        let Some(Shape::Func { dom, exact_dom, range, max_dom }) = self.read_place(bag, in_prime, vars, env) else {
            return;
        };
        // Only narrow an already-proved bag (`lo >= 1`) or empty bag; never fabricate positivity.
        if max_total < 0 {
            return;
        }
        if max_total == 0 {
            if matches!(*range, Shape::Bottom) || matches!(*range, Shape::Int(Some((lo, _))) if lo >= 1) {
                self.write_place(bag, in_prime, vars, super::bags::empty_bag_shape(), None, env);
            }
            return;
        }
        let Shape::Int(Some((lo, hi))) = *range else { return };
        if lo < 1 {
            return;
        }
        let new_hi = hi.min(max_total);
        let new_max_dom = Some(max_dom.map_or(max_total as u32, |m| m.min(max_total as u32)));
        if lo <= new_hi {
            self.write_place(
                bag,
                in_prime,
                vars,
                Shape::Func { dom, exact_dom, range: Box::new(Shape::Int(Some((lo, new_hi)))), max_dom: new_max_dom },
                None,
                env,
            );
        }
    }

    fn narrow_copies_in(&self, (elem, bag): (&Expr, &Expr), op: B, k: i32, in_prime: bool, vars: &[Shape], env: &mut CheckEnv) {
        let Some(key) = fn_app_place(bag, std::slice::from_ref(elem), in_prime) else { return };
        let cur = if let Some(ov) = env.fn_app_overrides.get(&key) {
            ov.clone()
        } else {
            let Some(fs) = self.read_place(bag, in_prime, vars, env) else { return };
            fn_app_range(&fs)
        };
        let Shape::Int(bounds) = cur else { return };
        let (lo, hi) = bounds.unwrap_or((i32::MIN, i32::MAX));
        let (nlo, nhi, implies_in_dom) = match op {
            B::Lt => (lo, hi.min(k.saturating_sub(1)), false),
            B::Le => (lo, hi.min(k), false),
            B::Gt => (lo.max(k.saturating_add(1)), hi, k >= 0),
            B::Ge => (lo.max(k), hi, k >= 1),
            _ => return,
        };
        if implies_in_dom {
            env.proven_in_dom.push((elem.clone(), bag.clone(), in_prime));
        }
        if nlo <= nhi {
            env.fn_app_overrides.insert(key, Shape::Int(Some((nlo, nhi))));
        }
    }

    fn read_place(&self, e: &Expr, in_prime: bool, vars: &[Shape], env: &CheckEnv) -> Option<Shape> {
        match &*e.kind {
            ExprKind::Var(v) => Some(env.var_overrides.get(&(*v, in_prime)).cloned().unwrap_or_else(|| vars[v.idx()].clone())),
            ExprKind::Local(l) => env.locals.get(l).cloned(),
            ExprKind::Field { record, field } => {
                let rs = self.read_place(record, in_prime, vars, env)?;
                Some(field_of_shape(&rs, field))
            }
            ExprKind::FnApp { func, args } => {
                let key = fn_app_place(func, args, in_prime)?;
                if let Some(ov) = env.fn_app_overrides.get(&key) {
                    return Some(ov.clone());
                }
                let fs = self.read_place(func, in_prime, vars, env)?;
                Some(fn_app_range(&fs))
            }
            _ => None,
        }
    }

    fn write_place(&self, e: &Expr, in_prime: bool, vars: &[Shape], shape: Shape, origin: Option<(Expr, bool)>, env: &mut CheckEnv) {
        match &*e.kind {
            ExprKind::Var(v) => env.bind_var_override(*v, in_prime, shape),
            ExprKind::Local(l) => {
                let keep = origin.or_else(|| env.local_dom.get(l).cloned());
                env.bind_local(*l, shape, keep);
            }
            ExprKind::Field { record, field } => match self.read_place(record, in_prime, vars, env) {
                Some(Shape::Record(mut map)) => {
                    map.insert(field.clone(), shape);
                    self.write_place(record, in_prime, vars, Shape::Record(map), None, env);
                }
                // A tagged-record union narrows the field inside every variant
                // that carries it, so `m.acc \in Acceptor` refines `m` instead
                // of being dropped with the union structure.
                Some(Shape::Union(us)) => {
                    let updated: Vec<Shape> = us
                        .iter()
                        .map(|u| match u {
                            Shape::Record(fs) => match fs.get(field) {
                                Some(cur) => {
                                    let mut map = fs.clone();
                                    map.insert(field.clone(), narrow_shape(cur, &shape));
                                    Shape::Record(map)
                                }
                                None => u.clone(),
                            },
                            _ => u.clone(),
                        })
                        .collect();
                    self.write_place(record, in_prime, vars, Shape::Union(updated), None, env);
                }
                _ => {}
            },
            ExprKind::FnApp { func, args } => {
                if let Some(key) = fn_app_place(func, args, in_prime) {
                    env.fn_app_overrides.insert(key, shape);
                }
            }
            _ => {}
        }
    }
}
