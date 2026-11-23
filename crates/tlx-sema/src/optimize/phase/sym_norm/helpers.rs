//! Structural helpers, `Enumerator::target` preservation wrappers, branch
//! splitting, and public forward-domain queries backed by [`SymNormalizer`].

use std::sync::Arc;

use tlx_front::cfg::Config;

use crate::{builtins::Builtin as B, hir::*, visit, Program};

use super::super::{
    domain::{Atom, Domain, Domains},
    Branch,
};
use super::SymNormalizer;

fn is_syntactic_target_or_frame(e: &Expr) -> bool {
    match &*e.kind {
        ExprKind::Var(_) => true,
        ExprKind::Builtin { op: B::Prime, args } if args.len() == 1 => is_syntactic_target_or_frame(&args[0]),
        ExprKind::Tuple(es) => !es.is_empty() && es.iter().all(is_syntactic_target_or_frame),
        _ => false,
    }
}

/// Prevent non-nullary operator calls (e.g. `Id(owner')`), operator parameters/lambdas,
/// constant substitutions, and `InstVar`s from normalizing into bare assignment targets or
/// `UNCHANGED` variable frames that `Enumerator::target` / `Enumerator::unchanged` reject.
pub(in crate::optimize::phase) fn block_non_target(e: Expr) -> Expr {
    if is_syntactic_target_or_frame(&e) {
        let span = e.span;
        Expr::new(ExprKind::Builtin { op: B::TLCEval, args: vec![e] }, span)
    } else {
        e
    }
}

/// `Enumerator::var_of` looks through `LET` for a single variable (`LET a == 1 IN x`),
/// whereas `Enumerator::unchanged` treats `UNCHANGED (LET a == 1 IN <<x, y>>)` as a test.
pub(in crate::optimize::phase) fn block_unchanged_tuple(e: Expr) -> Expr {
    if matches!(&*e.kind, ExprKind::Tuple(es) if !es.is_empty() && es.iter().all(is_syntactic_target_or_frame)) {
        let span = e.span;
        Expr::new(ExprKind::Builtin { op: B::TLCEval, args: vec![e] }, span)
    } else {
        e
    }
}

pub(super) fn expr_contains_at(e: &Expr) -> bool {
    if matches!(&*e.kind, ExprKind::At) {
        return true;
    }
    let mut found = false;
    visit::children(e, &mut |c| found |= expr_contains_at(c));
    found
}

pub(in crate::optimize::phase) fn mentions_local(e: &Expr, target: LocalId) -> bool {
    if matches!(&*e.kind, ExprKind::Local(id) if *id == target) {
        return true;
    }
    let mut found = false;
    visit::children(e, &mut |c| found |= mentions_local(c, target));
    found
}

/// Look up an already-resolved root definition or constant by name without
/// mutating `Program`. Fails closed if ambiguous or still `Pending`.
pub(in crate::optimize::phase) fn lookup_resolved_root(program: &Program, name: &str) -> Option<RootSymbol> {
    let mut found_def = None;
    for (i, d) in program.defs.iter().enumerate() {
        let id = DefId(i as u32);
        if &*d.name == name && program.def_instance(id).is_none() && !program.def_is_let(id) {
            if found_def.is_some() {
                return None;
            }
            found_def = Some(id);
        }
    }
    if let Some(id) = found_def {
        return (!matches!(program.defs[id.idx()].kind, DefKind::Pending)).then_some(RootSymbol::Def(id));
    }
    let mut found_const = None;
    for (i, c) in program.consts.iter().enumerate() {
        if &*c.name == name {
            if found_const.is_some() {
                return None;
            }
            found_const = Some(ConstId(i as u32));
        }
    }
    found_const.map(RootSymbol::Const)
}

/// Returns `Some(n)` only when every element of `set` is provably a tuple of
/// exact length `n`. Never guesses on variables or heterogeneous sets.
pub(in crate::optimize::phase) fn exact_tuple_arity(set: &Expr) -> Option<usize> {
    match &*set.kind {
        ExprKind::Builtin { op: B::Times, args } if !args.is_empty() => Some(args.len()),
        ExprKind::SetEnum(es) if !es.is_empty() => {
            let mut arity = None;
            for e in es {
                let ExprKind::Tuple(ts) = &*e.kind else { return None };
                match arity {
                    None => arity = Some(ts.len()),
                    Some(n) if n != ts.len() => return None,
                    _ => {}
                }
            }
            arity
        }
        ExprKind::SetMap { expr, .. } => match &*expr.kind {
            ExprKind::Tuple(ts) => Some(ts.len()),
            _ => None,
        },
        ExprKind::SetFilter { bound, .. } => exact_tuple_arity(&bound.set),
        ExprKind::Builtin { op: B::SetMinus, args } if args.len() == 2 => exact_tuple_arity(&args[0]),
        ExprKind::Builtin { op: B::Cup, args } if args.len() == 2 => {
            let a = exact_tuple_arity(&args[0])?;
            let b = exact_tuple_arity(&args[1])?;
            (a == b).then_some(a)
        }
        _ => None,
    }
}

pub(super) fn is_infallible_path(path: &[ExceptKey]) -> bool {
    path.iter().all(|k| match k {
        ExceptKey::Field(_) => true,
        ExceptKey::Index(args) => args.iter().all(|a| {
            matches!(
                &*a.kind,
                ExprKind::Local(_) | ExprKind::Var(_) | ExprKind::Const(_) | ExprKind::Num(_) | ExprKind::Str(_) | ExprKind::Bool(_)
            )
        }),
    })
}

pub(super) fn paths_disjoint(a: &[ExceptKey], b: &[ExceptKey]) -> bool {
    a.iter().zip(b).any(|(a, b)| match (a, b) {
        (ExceptKey::Field(a), ExceptKey::Field(b)) => a != b,
        (ExceptKey::Index(ax), ExceptKey::Index(bx)) if ax.len() == 1 && bx.len() == 1 => {
            match (Atom::literal(&ax[0]), Atom::literal(&bx[0])) {
                (Some(la), Some(lb)) => la != lb,
                _ => false,
            }
        }
        _ => false,
    })
}

pub(super) fn expr_syntactically_eq(a: &Expr, b: &Expr) -> bool {
    match (&*a.kind, &*b.kind) {
        (ExprKind::Var(x), ExprKind::Var(y)) => x == y,
        (ExprKind::Local(x), ExprKind::Local(y)) => x == y,
        (ExprKind::Const(x), ExprKind::Const(y)) => x == y,
        (ExprKind::Num(x), ExprKind::Num(y)) => x == y,
        (ExprKind::Str(x), ExprKind::Str(y)) => x == y,
        (ExprKind::Bool(x), ExprKind::Bool(y)) => x == y,
        (ExprKind::Field { record: r1, field: f1 }, ExprKind::Field { record: r2, field: f2 }) => f1 == f2 && expr_syntactically_eq(r1, r2),
        (ExprKind::FnApp { func: f1, args: a1 }, ExprKind::FnApp { func: f2, args: a2 }) => {
            a1.len() == a2.len() && expr_syntactically_eq(f1, f2) && a1.iter().zip(a2).all(|(x, y)| expr_syntactically_eq(x, y))
        }
        (ExprKind::Tuple(a1), ExprKind::Tuple(a2)) => a1.len() == a2.len() && a1.iter().zip(a2).all(|(x, y)| expr_syntactically_eq(x, y)),
        _ => false,
    }
}

/// Split an action/init expression into disjunctive branches, splitting
/// top-level `Or`, `And`, `Exists`, and `If` (including desugared `CASE ... OTHER`).
pub(in crate::optimize::phase) fn split_branches(e: &Expr) -> Option<Vec<Branch>> {
    fn split(e: &Expr, remaining: &mut usize, depth: usize) -> Option<Vec<Branch>> {
        if *remaining == 0 || depth >= 128 {
            return None;
        }
        *remaining -= 1;
        match &*e.kind {
            ExprKind::Or(es) => {
                let mut out = Vec::new();
                for e in es {
                    out.extend(split(e, remaining, depth + 1)?);
                    if out.len() > 512 {
                        return None;
                    }
                }
                Some(out)
            }
            ExprKind::And(es) => {
                let mut out = vec![Branch { bounds: vec![], terms: vec![] }];
                for e in es {
                    let alternatives = split(e, remaining, depth + 1)?;
                    if out.len().saturating_mul(alternatives.len()) > 512 {
                        return None;
                    }
                    let mut combined = Vec::new();
                    for a in &out {
                        for b in &alternatives {
                            if a.terms.len() + b.terms.len() > 512 || a.bounds.len() + b.bounds.len() > 128 {
                                return None;
                            }
                            let mut branch = a.clone();
                            branch.bounds.extend(b.bounds.iter().cloned());
                            branch.terms.extend(b.terms.iter().cloned());
                            combined.push(branch);
                        }
                    }
                    out = combined;
                }
                Some(out)
            }
            ExprKind::Quant { kind: QuantKind::Exists, bounds, body } => {
                let mut out = split(body, remaining, depth + 1)?;
                for b in &mut out {
                    if bounds.len() + b.bounds.len() > 128 {
                        return None;
                    }
                    let mut combined = bounds.clone();
                    combined.append(&mut b.bounds);
                    b.bounds = combined;
                }
                Some(out)
            }
            ExprKind::If { cond, then, els } => {
                let mut left = split(then, remaining, depth + 1)?;
                let right = split(els, remaining, depth + 1)?;
                let neg = Expr::new(ExprKind::Builtin { op: B::Not, args: vec![cond.clone()] }, cond.span);
                for b in &mut left {
                    b.terms.insert(0, cond.clone());
                }
                let mut right = right;
                for b in &mut right {
                    b.terms.insert(0, neg.clone());
                }
                left.extend(right);
                if left.len() > 512 {
                    return None;
                }
                Some(left)
            }
            _ => Some(vec![Branch { bounds: vec![], terms: vec![e.clone()] }]),
        }
    }
    split(e, &mut 100_000, 0)
}

/// Normalize `Init` and `Next` and infer forward may-value domains for every
/// state variable, returning `(var_name, debug_domain)` pairs.
///
/// Strictly sound: derived only from `Init` and `Next`, never from checked
/// invariants.
pub fn infer_var_domains(program: &Program, cfg: &Config, init: &Expr, next: &Expr) -> Option<Vec<(Arc<str>, String)>> {
    let mut norm = SymNormalizer::with_config(program, cfg);
    let init_norm = norm.normalize(init)?;
    let next_norm = norm.normalize(next)?;
    let init_branches = split_branches(&init_norm)?;
    let next_branches = split_branches(&next_norm)?;
    let domains = Domains::infer(program, cfg, &init_branches, &next_branches)?;
    Some(program.vars.iter().zip(domains.vars.iter()).map(|(v, d)| (v.name.clone(), format_domain(d))).collect())
}

/// Check whether forward domain inference proves `var \in type_set` from `Init`
/// and `Next` alone (never assuming checked invariants).
pub fn proves_var_membership(program: &Program, cfg: &Config, init: &Expr, next: &Expr, var: VarId, type_set: &Expr) -> Option<bool> {
    let mut norm = SymNormalizer::with_config(program, cfg);
    let init_norm = norm.normalize(init)?;
    let next_norm = norm.normalize(next)?;
    let set_norm = norm.normalize(type_set)?;
    let init_branches = split_branches(&init_norm)?;
    let next_branches = split_branches(&next_norm)?;
    let domains = Domains::infer(program, cfg, &init_branches, &next_branches)?;
    let dom = domains.vars.get(var.idx())?;
    Some(domains.belongs(dom, &set_norm))
}

fn format_domain(d: &Domain) -> String {
    match d {
        Domain::Bottom => "Bottom".into(),
        Domain::Top => "Top".into(),
        Domain::Atoms(atoms) => {
            let parts: Vec<String> = atoms
                .iter()
                .map(|a| match a {
                    Atom::Num(n) => n.to_string(),
                    Atom::Str(s) => format!("{s:?}"),
                    Atom::Bool(b) => if *b { "TRUE" } else { "FALSE" }.into(),
                    Atom::Model(m) => format!("@{m}"),
                })
                .collect();
            format!("Atoms({{{}}})", parts.join(", "))
        }
        Domain::Integer(lo) => format!("Integer(>={lo})"),
        Domain::Set(inner) => format!("Set({})", format_domain(inner)),
        Domain::Seq(inner) => format!("Seq({})", format_domain(inner)),
        Domain::Record(fs) => {
            let parts: Vec<String> = fs.iter().map(|(k, v)| format!("{k}: {}", format_domain(v))).collect();
            format!("Record({})", parts.join(", "))
        }
        Domain::Records(rs) => {
            let parts: Vec<String> = rs
                .iter()
                .map(|fs| {
                    let inner: Vec<String> = fs.iter().map(|(k, v)| format!("{k}: {}", format_domain(v))).collect();
                    format!("{{{}}}", inner.join(", "))
                })
                .collect();
            format!("Records([{}])", parts.join(" | "))
        }
        Domain::Function(ks, range) => {
            let keys: Vec<String> = ks
                .iter()
                .map(|a| match a {
                    Atom::Num(n) => n.to_string(),
                    Atom::Str(s) => format!("{s:?}"),
                    Atom::Bool(b) => if *b { "TRUE" } else { "FALSE" }.into(),
                    Atom::Model(m) => format!("@{m}"),
                })
                .collect();
            format!("Function({{{}}} -> {})", keys.join(", "), format_domain(range))
        }
        Domain::Mapping(range) => format!("Mapping({})", format_domain(range)),
    }
}
