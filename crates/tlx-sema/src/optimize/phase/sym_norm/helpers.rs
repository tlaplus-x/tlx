//! Structural helpers, `Enumerator::target` preservation wrappers, and public
//! forward-domain queries backed by [`SymNormalizer`].

use std::sync::Arc;

use tlx_front::cfg::Config;

use crate::{builtins::Builtin as B, hir::*, visit, Program};

use super::super::{
    branches_with_if,
    domain::{Atom, Domain, Domains},
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

/// Look up an already-resolved root definition or constant by name without
/// mutating `Program`. Fails closed if absent or still `Pending`.
pub(in crate::optimize::phase) fn lookup_resolved_root(program: &Program, name: &str) -> Option<RootSymbol> {
    program.lookup_resolved_root(name)
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

const MAX_DESUGAR_AT_NODES: usize = 100_000;

/// Desugar `ExprKind::At` inside `ExprKind::Except` using exact lexical `@`
/// scoping (outer `@` for `base` and update `path` indices, inner `@` for each
/// update RHS). Fails closed (`None`) whenever a later update uses `@` after an
/// earlier update that is not provably disjoint (`paths_disjoint`), or when a
/// bare `@` appears outside an `Except` RHS, or on budget exhaustion.
pub(in crate::optimize::phase) fn desugar_except_at(e: &Expr) -> Option<Expr> {
    let mut unused = false;
    let mut budget = MAX_DESUGAR_AT_NODES;
    desugar_except_at_rec(e, None, &mut unused, &mut budget)
}

fn desugar_except_at_rec(e: &Expr, outer_at: Option<&Expr>, used_outer_at: &mut bool, budget: &mut usize) -> Option<Expr> {
    *budget = budget.checked_sub(1)?;
    match &*e.kind {
        ExprKind::At => {
            let repl = outer_at?;
            *used_outer_at = true;
            Some(repl.clone())
        }
        ExprKind::Except { base, updates } => {
            let base_d = desugar_except_at_rec(base, outer_at, used_outer_at, budget)?;
            let mut expanded: Vec<(Vec<ExceptKey>, Expr)> = Vec::with_capacity(updates.len());
            for (path, rhs) in updates {
                let mut keys = Vec::with_capacity(path.len());
                let mut old = base_d.clone();
                for key in path {
                    let key_d = match key {
                        ExceptKey::Field(f) => ExceptKey::Field(f.clone()),
                        ExceptKey::Index(args) => {
                            let args_d = args
                                .iter()
                                .map(|a| desugar_except_at_rec(a, outer_at, used_outer_at, budget))
                                .collect::<Option<Vec<_>>>()?;
                            ExceptKey::Index(args_d)
                        }
                    };
                    old = Expr::new(
                        match &key_d {
                            ExceptKey::Field(f) => ExprKind::Field { record: old, field: f.clone() },
                            ExceptKey::Index(args) => ExprKind::FnApp { func: old, args: args.clone() },
                        },
                        rhs.span,
                    );
                    keys.push(key_d);
                }
                let mut inner_used = false;
                let rhs_d = desugar_except_at_rec(rhs, Some(&old), &mut inner_used, budget)?;
                // TLA+ EXCEPT updates are sequential: reading from `base_d` is
                // sound only when no prior update can alias `keys`.
                if inner_used && expanded.iter().any(|(prior, _)| !paths_disjoint(prior, &keys)) {
                    return None;
                }
                expanded.push((keys, rhs_d));
            }
            Some(Expr::new(ExprKind::Except { base: base_d, updates: expanded }, e.span))
        }
        _ => {
            let mut out = e.clone();
            let mut ok = true;
            visit::children_mut(&mut out, &mut |child| {
                if ok {
                    if let Some(c) = desugar_except_at_rec(child, outer_at, used_outer_at, budget) {
                        *child = c;
                    } else {
                        ok = false;
                    }
                }
            });
            ok.then_some(out)
        }
    }
}

/// Deliberately narrower than `hir_util::expr_structurally_eq`: the `EXCEPT`
/// merge below only needs the scalar, field, application and tuple arms, and
/// widening the relation would accept additional merges and change normalized
/// output. `SetEnum` / `Builtin` equality is sound in general, so this stays a
/// separate documented relation rather than a duplicate of the threshold walker.
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

/// Normalize `Init` and `Next` and infer forward may-value domains for every
/// state variable, returning `(var_name, debug_domain)` pairs.
///
/// Strictly sound: derived only from `Init` and `Next`, never from checked
/// invariants.
pub fn infer_var_domains(program: &Program, cfg: &Config, init: &Expr, next: &Expr) -> Option<Vec<(Arc<str>, String)>> {
    let mut norm = SymNormalizer::with_config(program, cfg);
    let init_norm = norm.normalize(init)?;
    let next_norm = norm.normalize(next)?;
    let init_branches = branches_with_if(&init_norm)?;
    let next_branches = branches_with_if(&next_norm)?;
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
    let init_branches = branches_with_if(&init_norm)?;
    let next_branches = branches_with_if(&next_norm)?;
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
