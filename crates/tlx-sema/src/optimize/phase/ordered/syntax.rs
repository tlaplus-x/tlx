use super::{binding, variable, Branch, Family, History};
use crate::{builtins::Builtin as B, hir::*, visit};
use std::collections::HashMap;

pub(super) fn conditionals(e: &Expr) -> Expr {
    let kind = match &*e.kind {
        ExprKind::And(es) => ExprKind::And(es.iter().map(conditionals).collect()),
        ExprKind::Or(es) => ExprKind::Or(es.iter().map(conditionals).collect()),
        ExprKind::Quant { kind: QuantKind::Exists, bounds, body } => {
            ExprKind::Quant { kind: QuantKind::Exists, bounds: bounds.clone(), body: conditionals(body) }
        }
        ExprKind::If { cond, then, els } => ExprKind::Or(vec![
            Expr::new(ExprKind::And(vec![cond.clone(), conditionals(then)]), e.span),
            Expr::new(
                ExprKind::And(vec![Expr::new(ExprKind::Builtin { op: B::Not, args: vec![cond.clone()] }, cond.span), conditionals(els)]),
                e.span,
            ),
        ]),
        _ => return e.clone(),
    };
    Expr::new(kind, e.span)
}

pub(super) fn increment(e: &Expr, v: VarId) -> Option<Expr> {
    if variable(e, false) == Some(v) {
        return Some(Expr::new(ExprKind::Num(0), e.span));
    }
    let ExprKind::Builtin { op: B::Plus, args } = &*e.kind else { return None };
    (args.len() == 2 && variable(&args[0], false) == Some(v)).then(|| args[1].clone())
}

pub(super) fn frame(e: &Expr) -> bool {
    match &*e.kind {
        ExprKind::Var(_) => true,
        ExprKind::Tuple(es) => es.iter().all(frame),
        _ => false,
    }
}

pub(super) fn history_extension(e: &Expr, v: VarId) -> Option<&Expr> {
    let ExprKind::Builtin { op: B::AtAt, args } = &*e.kind else { return None };
    if args.len() != 2 {
        return None;
    }
    if variable(&args[0], false) == Some(v) {
        Some(&args[1])
    } else if variable(&args[1], false) == Some(v) {
        Some(&args[0])
    } else {
        None
    }
}

fn singleton_key(e: &Expr) -> Option<&Expr> {
    let ExprKind::FnConstruct { bounds, .. } = &*e.kind else { return None };
    if bounds.len() != 1 || bounds[0].vars.locals().len() != 1 {
        return None;
    }
    let ExprKind::SetEnum(keys) = &*bounds[0].set.kind else { return None };
    (keys.len() == 1).then(|| &keys[0])
}

pub(super) fn history(initial: &[Branch], steps: &[Branch], families: &[Family], variables: usize) -> Option<History> {
    for (family, f) in families.iter().enumerate() {
        for i in 0..variables {
            let v = VarId(i as u32);
            let valid_init = initial.iter().all(|b| {
                binding(b, v, false).is_some_and(|e| {
                    singleton_key(&e).is_some_and(|key| {
                        variable(key, false) == Some(f.variable) || matches!(&*key.kind, ExprKind::Num(n) if *n == f.initial)
                    })
                })
            });
            if !valid_init {
                continue;
            }
            let valid_steps = steps.iter().all(|b| {
                let Some(clock) = binding(b, f.variable, true).and_then(|e| increment(&e, f.variable)) else { return false };
                let Some(rhs) = binding(b, v, true) else { return false };
                if matches!(&*clock.kind, ExprKind::Num(0)) {
                    return variable(&rhs, false) == Some(v);
                }
                matches!(&*clock.kind, ExprKind::Num(1))
                    && history_extension(&rhs, v)
                        .and_then(singleton_key)
                        .and_then(|key| increment(key, f.variable))
                        .is_some_and(|delta| matches!(&*delta.kind, ExprKind::Num(1)))
            });
            if valid_steps {
                return Some(History { variable: v, family });
            }
        }
    }
    None
}

pub(super) fn latest(e: &Expr, history: VarId) -> bool {
    let ExprKind::Choose { vars, set: Some(set), body } = &*e.kind else { return false };
    let [x] = vars.locals() else { return false };
    if !domain(set, history) {
        return false;
    }
    let ExprKind::Quant { kind: QuantKind::Forall, bounds, body } = &*body.kind else { return false };
    if bounds.len() != 1 || !domain(&bounds[0].set, history) {
        return false;
    }
    let [y] = bounds[0].vars.locals() else { return false };
    let ExprKind::Builtin { op, args } = &*body.kind else { return false };
    let local = |e: &Expr, id: LocalId| matches!(&*e.kind, ExprKind::Local(l) if *l == id);
    args.len() == 2
        && ((*op == B::Ge && local(&args[0], *x) && local(&args[1], *y)) || (*op == B::Le && local(&args[1], *x) && local(&args[0], *y)))
}
fn domain(e: &Expr, v: VarId) -> bool {
    matches!(&*e.kind, ExprKind::Builtin { op: B::Domain, args } if args.len() == 1 && variable(&args[0], false) == Some(v))
}

/// Compare normalized expressions modulo bound-local renaming and locations.
/// Free locals remain distinct. Normalization gives hygienic binding IDs.
pub(super) fn same(a: &Expr, b: &Expr) -> bool {
    fn canonical(e: &Expr) -> String {
        fn collect(e: &Expr, ids: &mut HashMap<LocalId, LocalId>) {
            let mut bind = |v: &BoundVars| {
                for id in v.locals() {
                    let next = LocalId(u32::MAX - ids.len() as u32);
                    ids.entry(*id).or_insert(next);
                }
            };
            match &*e.kind {
                ExprKind::Quant { bounds, .. } | ExprKind::FnConstruct { bounds, .. } | ExprKind::SetMap { bounds, .. } => {
                    for b in bounds {
                        bind(&b.vars);
                    }
                }
                ExprKind::Choose { vars, .. } => bind(vars),
                ExprKind::SetFilter { bound, .. } => bind(&bound.vars),
                _ => {}
            }
            visit::children(e, &mut |c| collect(c, ids));
        }
        fn rewrite(e: &mut Expr, ids: &HashMap<LocalId, LocalId>) {
            let mut kind = (*e.kind).clone();
            let bind = |v: &mut BoundVars| {
                *v = match v {
                    BoundVars::Many(v) => BoundVars::Many(v.iter().map(|l| ids[l]).collect()),
                    BoundVars::Tuple(v) => BoundVars::Tuple(v.iter().map(|l| ids[l]).collect()),
                };
            };
            match &mut kind {
                ExprKind::Local(l) => *l = ids.get(l).copied().unwrap_or(*l),
                ExprKind::Quant { bounds, .. } | ExprKind::FnConstruct { bounds, .. } | ExprKind::SetMap { bounds, .. } => {
                    for b in bounds {
                        bind(&mut b.vars);
                    }
                }
                ExprKind::Choose { vars, .. } => bind(vars),
                ExprKind::SetFilter { bound, .. } => bind(&mut bound.vars),
                _ => {}
            }
            *e = Expr::new(kind, Span::default());
            visit::children_mut(e, &mut |c| rewrite(c, ids));
        }
        let mut ids = HashMap::new();
        collect(e, &mut ids);
        let mut out = e.clone();
        rewrite(&mut out, &ids);
        format!("{out:?}")
    }
    canonical(a) == canonical(b)
}

/// Pull an independent stuttering frame out of a nonempty universal action.
/// Empty domains must not acquire assignments that the original relation lacks.
pub(super) fn lift_frames(e: &Expr, program: &crate::Program, cfg: &tlx_front::cfg::Config) -> Expr {
    fn nonempty(e: &Expr, program: &crate::Program, cfg: &tlx_front::cfg::Config) -> bool {
        match &*e.kind {
            ExprKind::SetEnum(es) => !es.is_empty(),
            ExprKind::Const(c) => matches!(
                cfg.last_constant_value(&program.consts[c.idx()].name),
                Some(tlx_front::cfg::CfgValue::Set(es)) if !es.is_empty()
            ),
            _ => false,
        }
    }
    let mut out = e.clone();
    visit::children_mut(&mut out, &mut |e| *e = lift_frames(e, program, cfg));
    if let ExprKind::Quant { kind: QuantKind::Forall, bounds, body } = &*out.kind {
        if !bounds.iter().all(|b| nonempty(&b.set, program, cfg)) {
            return out;
        }
        let ExprKind::And(terms) = &*body.kind else { return out };
        let (frames, guards): (Vec<_>, Vec<_>) = terms
            .iter()
            .cloned()
            .partition(|e| matches!(&*e.kind, ExprKind::Builtin {op: B::Unchanged,args} if args.len()==1 && frame(&args[0])));
        if frames.is_empty() {
            return out;
        }
        let mut terms = frames;
        terms.push(Expr::new(
            ExprKind::Quant { kind: QuantKind::Forall, bounds: bounds.clone(), body: Expr::new(ExprKind::And(guards), body.span) },
            out.span,
        ));
        return Expr::new(ExprKind::And(terms), out.span);
    }
    out
}
