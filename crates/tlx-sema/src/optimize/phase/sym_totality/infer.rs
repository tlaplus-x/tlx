//! Fixed-point abstract shape inference and path-sensitive narrowing for
//! `TotalityChecker`.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use tlx_front::cfg::CfgValue;

use super::shape::*;
use super::{CheckEnv, ConstInfo, MvType, Shape, TotalityChecker, MAX_I32_U32, MAX_STEPS, MAX_STR_SET, MAX_UNMOVED_SET};
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

        // Step 2: Iterate Next to a fixed point.
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
                break;
            }
            cur = joined;
        }

        // Step 3: Explicit post-fixed-point closure verification!
        // Guarantees inductiveness: if ANY variable still grows in one step of Init or Next,
        // discard all unverified bounds and fall back to `Top` for every variable.
        let mut verify_init = vec![Shape::Bottom; n];
        let mut verify_next = vec![Shape::Bottom; n];
        let mut steps = MAX_STEPS;
        self.collect_assignments(init, false, &cur, &CheckEnv::default(), &mut verify_init, &mut steps);
        self.collect_assignments(next, true, &cur, &CheckEnv::default(), &mut verify_next, &mut steps);
        if steps == 0 {
            return vec![Shape::Top; n];
        }
        for i in 0..n {
            if !shape_leq(&verify_init[i], &cur[i]) || !shape_leq(&verify_next[i], &cur[i]) {
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
            ExprKind::Quant { kind: QuantKind::Exists, bounds, body } => {
                let mut local_env = env.clone();
                if !self.bind_quant_bounds(bounds, false, vars, &mut local_env, steps) {
                    return;
                }
                self.collect_assignments(body, primed, vars, &local_env, out, steps);
            }
            ExprKind::Builtin { op: B::Eq, args } if args.len() == 2 => {
                if let Some(v) = target_var(&args[0], primed) {
                    let s = self.infer_expr(&args[1], false, vars, env, steps);
                    out[v.idx()] = cap_shape(join_shape(&out[v.idx()], &s));
                } else if let Some(v) = target_var(&args[1], primed) {
                    let s = self.infer_expr(&args[0], false, vars, env, steps);
                    out[v.idx()] = cap_shape(join_shape(&out[v.idx()], &s));
                }
            }
            ExprKind::Builtin { op: B::In, args } if args.len() == 2 => {
                if let Some(v) = target_var(&args[0], primed) {
                    let s = self.infer_set_elem(&args[1], false, vars, env, steps);
                    out[v.idx()] = cap_shape(join_shape(&out[v.idx()], &s));
                }
            }
            ExprKind::Builtin { op: B::SubsetEq, args } if args.len() == 2 => {
                if let Some(v) = target_var(&args[0], primed) {
                    let (elem, finite, max_card) = self.infer_set_info(&args[1], false, vars, env, steps);
                    let s = if finite { Shape::Set { elem: Box::new(elem), finite: true, max_card } } else { Shape::Top };
                    out[v.idx()] = cap_shape(join_shape(&out[v.idx()], &s));
                }
            }
            ExprKind::Builtin { op: B::Unchanged, args } if primed && args.len() == 1 => {
                self.collect_unchanged(&args[0], vars, out);
            }
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
            ExprKind::SetFilter { bound, pred: _ } => {
                let (elem, finite, max_card) = self.infer_set_info(&bound.set, in_prime, vars, env, steps);
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
                    if let ExprKind::Num(idx) = &*args[0].kind {
                        if let Shape::Tuple(ts) = &fs {
                            if let Some(u) = usize::try_from(*idx).ok().filter(|&u| (1..=ts.len()).contains(&u)) {
                                return ts[u - 1].clone();
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
                Shape::Top
            }
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
            _ => Shape::Top,
        }
    }

    fn infer_set_info(&self, set: &Expr, in_prime: bool, vars: &[Shape], env: &CheckEnv, steps: &mut usize) -> (Shape, bool, Option<u32>) {
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
        match &*e.kind {
            ExprKind::Num(n) => i32::try_from(*n).ok(),
            ExprKind::Const(c) => match self.consts.get(c)? {
                ConstInfo::Value(CfgValue::Int(n)) => i32::try_from(*n).ok(),
                ConstInfo::Subst(def_id) => match &self.program.defs[def_id.idx()].kind {
                    DefKind::Op(body) => self.const_exact_i32(body),
                    _ => None,
                },
                _ => None,
            },
            ExprKind::Builtin { op: B::Neg, args } if args.len() == 1 => self.const_exact_i32(&args[0])?.checked_neg(),
            ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => self.const_exact_i32(&args[0]),
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
        match &*s.kind {
            ExprKind::Builtin { op: B::Boolean, args } if args.is_empty() => true,
            ExprKind::Builtin { op: B::DotDot, args } if args.len() == 2 => {
                self.const_exact_i32(&args[0]).is_some() && self.const_exact_i32(&args[1]).is_some()
            }
            ExprKind::Builtin { op: B::Times, args } if args.len() >= 2 => args.iter().all(|a| self.is_exact_static_set(a)),
            ExprKind::Builtin { op: B::Cup, args } if args.len() == 2 => {
                if !self.is_exact_static_set(&args[0]) || !self.is_exact_static_set(&args[1]) {
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
            ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => self.is_exact_static_set(&args[0]),
            ExprKind::Const(c) => match self.consts.get(c) {
                Some(ConstInfo::Value(CfgValue::Set(es))) => self.cfg_set_is_exact(es),
                Some(ConstInfo::Subst(def_id)) => match &self.program.defs[def_id.idx()].kind {
                    DefKind::Op(body) => self.is_exact_static_set(body),
                    _ => false,
                },
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

    fn apply_fact_with_vars(&self, cond: &Expr, positive: bool, in_prime: bool, vars: &[Shape], env: &mut CheckEnv) {
        match &*cond.kind {
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
                self.narrow_eq(&args[0], &args[1], positive, in_prime, vars, env);
                self.narrow_eq(&args[1], &args[0], positive, in_prime, vars, env);
            }
            ExprKind::Builtin { op: B::Neq, args } if args.len() == 2 => {
                self.narrow_eq(&args[0], &args[1], !positive, in_prime, vars, env);
                self.narrow_eq(&args[1], &args[0], !positive, in_prime, vars, env);
            }
            ExprKind::Builtin { op: B::In, args } if positive && args.len() == 2 => {
                let mut steps = 2000;
                let elem = self.infer_set_elem(&args[1], in_prime, vars, env, &mut steps);
                let origin = match &*args[1].kind {
                    ExprKind::Builtin { op: B::Domain, args: da } if da.len() == 1 => Some((da[0].clone(), in_prime)),
                    _ => None,
                };
                if let Some(cur) = self.read_place(&args[0], in_prime, vars, env) {
                    let narrowed = narrow_shape(&cur, &elem);
                    self.write_place(&args[0], in_prime, vars, narrowed, origin, env);
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
        let Some(cur) = self.read_place(place, in_prime, vars, env) else { return };
        let mut steps = 2000;
        let other_s = self.infer_expr(other, in_prime, vars, env, &mut steps);
        if eq {
            if !matches!(other_s, Shape::Top | Shape::Bottom) {
                self.write_place(place, in_prime, vars, narrow_shape(&cur, &other_s), None, env);
            }
        } else {
            // `seq # <<>>` proves `min_len >= 1`:
            if matches!(&other_s, Shape::Tuple(ts) if ts.is_empty()) {
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
                self.write_place(place, in_prime, vars, excluded, None, env);
            }
        }
    }

    fn narrow_int_cmp(&self, place: &Expr, op: B, k: i32, in_prime: bool, vars: &[Shape], env: &mut CheckEnv) {
        if let ExprKind::Builtin { op: B::Len, args } = &*place.kind {
            if args.len() == 1 {
                self.narrow_seq_len(&args[0], op, k, in_prime, vars, env);
            }
            return;
        }
        let Some(Shape::Int(bounds)) = self.read_place(place, in_prime, vars, env) else { return };
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
                let fs = env.var_overrides.get(&(key.0, key.1)).cloned().unwrap_or_else(|| vars[key.0.idx()].clone());
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
            ExprKind::Field { record, field } => {
                if let Some(Shape::Record(mut map)) = self.read_place(record, in_prime, vars, env) {
                    map.insert(field.clone(), shape);
                    self.write_place(record, in_prime, vars, Shape::Record(map), None, env);
                }
            }
            ExprKind::FnApp { func, args } => {
                if let Some(key) = fn_app_place(func, args, in_prime) {
                    env.fn_app_overrides.insert(key, shape);
                }
            }
            _ => {}
        }
    }
}
