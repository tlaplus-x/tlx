//! Subexpression references `D!sel` (SANY's Subexpression algorithm,
//! tla2sany/semantic/Generator.java).
//!
//! A selected subexpression becomes a synthetic definition with the selected
//! definition's parameters, context and module, memoized per (definition,
//! normalized selector path). Selecting the body of a binding construct
//! (`!(e1, ..., en)`) or a labeled expression with parameters
//! (`!lab(e1, ..., en)`) lifts it out of the construct: the bound
//! identifiers become extra parameters of the synthetic definition, and the
//! selector's arguments extra arguments of the reference. Selections inside
//! a LET body keep the LET definitions around the selected expression.

use std::sync::Arc;

use tlx_front::ast::{self, Span};

use super::{DefSrc, DefState, DefUnit, Env, Program};
use crate::hir::*;

/// Normalized selector (for memoizing synthetic subexpression definitions).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(super) enum SelKey {
    Index(usize),
    Left,
    Right,
    /// `!(args)` with this many arguments.
    Args(usize),
    /// `!@`.
    At,
    /// `!:`.
    Colon,
    Label(Arc<str>, usize),
}

/// The result of following a selector path.
struct Selected {
    body: ast::Expr,
    /// Bound identifiers (and parameters of selected LET definitions)
    /// lifted into parameters.
    params: Vec<ast::OpDecl>,
    /// Definitions of the LETs the selection went into (outermost first).
    lets: Vec<Vec<ast::Unit>>,
}

impl Program {
    /// The definition denoting subexpression `path` of definition `d` (`d`
    /// itself for an empty path or only `!:`), and the extra arguments the
    /// reference passes to it (after `d`'s own arguments).
    pub(super) fn select(
        &mut self,
        env: &mut Env,
        d: DefId,
        path: &[ast::Selector],
        op_arg: bool,
        span: Span,
    ) -> Result<(DefId, Vec<ast::Expr>), ()> {
        // Keep `SelKey::Colon` only where `!:` actually changes `navigate`'s
        // `after_opsel` state before a `Label` (trailing or redundant `!:` are
        // no-ops and share the same synthetic definition).
        let mut key: Vec<SelKey> = Vec::with_capacity(path.len());
        let mut after_opsel = false;
        let mut pending_colon = false;
        for s in path {
            match s {
                ast::Selector::Colon => {
                    if !after_opsel {
                        pending_colon = true;
                    }
                    after_opsel = true;
                }
                ast::Selector::Label(l, a) => {
                    if pending_colon {
                        key.push(SelKey::Colon);
                        pending_colon = false;
                    }
                    key.push(SelKey::Label(l.name.clone(), a.len()));
                    after_opsel = false;
                }
                _ => {
                    pending_colon = false;
                    after_opsel = true;
                    key.push(match s {
                        ast::Selector::Index(i) => SelKey::Index(*i),
                        ast::Selector::Left => SelKey::Left,
                        ast::Selector::Right => SelKey::Right,
                        ast::Selector::Args(a) => SelKey::Args(a.len()),
                        ast::Selector::At => SelKey::At,
                        ast::Selector::Colon | ast::Selector::Label(..) => unreachable!(),
                    });
                }
            }
        }
        // The selector arguments, in order.
        let sel_args: Vec<ast::Expr> = path
            .iter()
            .flat_map(|s| match s {
                ast::Selector::Args(a) | ast::Selector::Label(_, a) => a.clone(),
                _ => Vec::new(),
            })
            .collect();
        if key.is_empty() {
            return Ok((d, Vec::new()));
        }
        let dname = self.defs[d.idx()].name.clone();
        if self.defs[d.idx()].builtin.is_some() {
            return self.fail(span, format!("cannot select a subexpression of built-in operator `{dname}`"));
        }
        let od = match &self.def_src[d.idx()].unit {
            DefUnit::Op(o) => o.clone(),
            DefUnit::Fn(_) => {
                return self.fail(span, format!("subexpression selectors on function definition `{dname}` are not supported"))
            }
        };
        let sel = match navigate(&od.body, path, op_arg) {
            Ok(s) => s,
            Err(msg) => return self.fail(span, format!("in `{dname}!...`: {msg}")),
        };
        if let Some(&sd) = self.subexpr_defs.get(&(d, key.clone())) {
            return Ok((sd, sel_args));
        }
        let mut body = sel.body;
        for defs in sel.lets.into_iter().rev() {
            let s = body.span;
            body = ast::Expr { kind: Box::new(ast::ExprKind::Let { defs, body }), span: s };
        }
        let mut name = dname.to_string();
        for k in &key {
            match k {
                SelKey::Index(i) => name.push_str(&format!("!{i}")),
                SelKey::Left => name.push_str("!<<"),
                SelKey::Right => name.push_str("!>>"),
                SelKey::Args(_) => name.push_str("!(..)"),
                SelKey::At => name.push_str("!@"),
                SelKey::Colon => name.push_str("!:"),
                SelKey::Label(l, _) => name.push_str(&format!("!{l}")),
            }
        }
        let name: Arc<str> = Arc::from(name);
        let (ctx, module, state) = {
            let src = &self.def_src[d.idx()];
            let st = if src.state == DefState::Local { DefState::Local } else { DefState::Unresolved };
            (src.ctx, src.module, st)
        };
        let mut params = od.params.clone();
        params.extend(sel.params);
        let unit = DefUnit::Op(ast::OpDef {
            name: ast::Ident { name: name.clone(), span: od.name.span },
            params,
            body,
            local: od.local,
            span: od.span,
        });
        let sd = self.new_def(name, None, od.span, DefSrc { ctx, module, unit: unit.clone(), state });
        self.subexpr_defs.insert((d, key), sd);
        if state == DefState::Local {
            // Like the LET definition it is part of, resolve it in the enclosing
            // environment (TLA+ forbids shadowing, so the names visible at the
            // reference site include those visible at the definition).
            self.fill_def(env, sd, &unit, Vec::new())?;
        }
        Ok((sd, sel_args))
    }
}

fn strip_labels(mut e: &ast::Expr) -> &ast::Expr {
    while let ast::ExprKind::Label { body, .. } = &*e.kind {
        e = body;
    }
    e
}

fn tuple(es: &[ast::Expr], span: Span) -> ast::Expr {
    ast::Expr { kind: Box::new(ast::ExprKind::Tuple(es.to_vec())), span }
}

/// The bound identifiers and body of a binding construct (or LAMBDA).
fn binder(e: &ast::Expr) -> Option<(Vec<ast::Ident>, &ast::Expr)> {
    use ast::ExprKind as A;
    let vars = |bs: &[ast::Bound]| -> Vec<ast::Ident> {
        bs.iter()
            .flat_map(|b| match &b.vars {
                ast::BoundVars::Many(v) | ast::BoundVars::Tuple(v) => v.clone(),
            })
            .collect()
    };
    Some(match &*e.kind {
        A::Quant { bounds, body, .. } | A::FnConstruct { bounds, body } => (vars(bounds), body),
        A::SetMap { expr, bounds } => (vars(bounds), expr),
        A::SetFilter { bound, pred } => (vars(std::slice::from_ref(bound)), pred),
        A::Choose { vars: v, body, .. } => (
            match v {
                ast::BoundVars::Many(v) | ast::BoundVars::Tuple(v) => v.clone(),
            },
            body,
        ),
        A::QuantUnbounded { vars, body, .. } | A::TemporalQuant { vars, body, .. } | A::Lambda { params: vars, body } => {
            (vars.clone(), body)
        }
        _ => return None,
    })
}

/// The operands `!1`, `!2`, ... of an expression (SANY's argument lists),
/// or an error.
fn operands(e: &ast::Expr) -> Result<Vec<ast::Expr>, String> {
    use ast::ExprKind as A;
    Ok(match &*e.kind {
        A::And(es) | A::Or(es) | A::Tuple(es) | A::SetEnum(es) => es.clone(),
        A::OpAppl { args, .. } => args.clone(),
        A::If { cond, then, els } => vec![cond.clone(), then.clone(), els.clone()],
        // `f[a, b]` is `f[<<a, b>>]`.
        A::FnApp { func, args } if args.len() == 1 => vec![func.clone(), args[0].clone()],
        A::FnApp { func, args } => vec![func.clone(), tuple(args, e.span)],
        A::FnSet { domain, range } => vec![domain.clone(), range.clone()],
        A::Record(fs) | A::RecordSet(fs) => fs.iter().map(|(_, v)| v.clone()).collect(),
        A::Field { record, field } => {
            vec![record.clone(), ast::Expr { kind: Box::new(A::Str(field.name.clone())), span: field.span }]
        }
        A::BoxAction { action, sub } | A::AngleAction { action, sub } => vec![action.clone(), sub.clone()],
        A::Fairness { sub, action, .. } => vec![sub.clone(), action.clone()],
        // The bounds of a binding construct.
        A::Quant { bounds, .. } | A::FnConstruct { bounds, .. } | A::SetMap { bounds, .. } => {
            bounds.iter().map(|b| b.set.clone()).collect()
        }
        A::SetFilter { bound, .. } => vec![bound.set.clone()],
        A::Choose { set: Some(s), .. } => vec![s.clone()],
        A::Num(_) | A::Decimal(_) | A::Str(_) | A::Bool(_) | A::At => {
            return Err("choosing an operand of a subexpression with no operands".into())
        }
        _ => return Err("this kind of expression has no operands that can be selected".into()),
    })
}

/// SANY's ArgNum: the operand number selected by `!n`, `!<<` or `!>>`.
fn arg_num(sel: &ast::Selector, arity: usize) -> Option<usize> {
    match sel {
        ast::Selector::Index(i) if *i <= arity => Some(*i),
        ast::Selector::Left if arity > 0 => Some(1),
        ast::Selector::Right if arity == 2 => Some(2),
        _ => None,
    }
}

fn sel_name(sel: &ast::Selector) -> String {
    match sel {
        ast::Selector::Index(i) => format!("!{i}"),
        ast::Selector::Left => "!<<".into(),
        ast::Selector::Right => "!>>".into(),
        _ => "!".into(),
    }
}

fn expr_params(vars: Vec<ast::Ident>) -> impl Iterator<Item = ast::OpDecl> {
    vars.into_iter().map(|name| ast::OpDecl { name, arity: 0 })
}

/// Follow a selector path inside a definition body.
///
/// A reference used as an operator argument (`Op3(D!lab!@, ...)`) gives no
/// arguments to its selectors: the identifiers they would bind still
/// become parameters of the selected subexpression.
fn navigate(body: &ast::Expr, path: &[ast::Selector], op_arg: bool) -> Result<Selected, String> {
    use ast::ExprKind as A;
    let mut out = Selected { body: body.clone(), params: Vec::new(), lets: Vec::new() };
    let mut i = 0;
    // After an operand selector or `!:`, a name selects an operator defined
    // in the LET at hand (if any) rather than a label.
    let mut after_opsel = false;
    while i < path.len() {
        let sel = &path[i];
        let cur = strip_labels(&out.body).clone();
        let prev_opsel = std::mem::replace(&mut after_opsel, !matches!(sel, ast::Selector::Label(..)));
        match sel {
            ast::Selector::Colon => {}
            ast::Selector::At => {
                if !op_arg {
                    return Err("`!@` (an operator) can only be used as an operator argument".into());
                }
                let Some((vars, body)) = binder(&cur) else {
                    return Err("`!@` selects the body of a binding construct or LAMBDA".into());
                };
                out.params.extend(expr_params(vars));
                out.body = body.clone();
            }
            ast::Selector::Index(_) | ast::Selector::Left | ast::Selector::Right => match &*cur.kind {
                A::Let { defs, body } => {
                    if arg_num(sel, 1) != Some(1) {
                        return Err("a LET/IN expression has only one operand".into());
                    }
                    out.lets.push(defs.clone());
                    out.body = body.clone();
                }
                A::Case { arms, other } => {
                    // `!i!j`: arm i, then its guard (j = 1) or value (j = 2).
                    let n = arms.len() + other.is_some() as usize;
                    let a = arg_num(sel, n).ok_or_else(|| format!("`{}` is out of range ({n} CASE arm(s))", sel_name(sel)))?;
                    let Some(next) = path.get(i + 1) else {
                        return Err("a subexpression of CASE must have the form !i!j".into());
                    };
                    let j = arg_num(next, 2).ok_or("the second selector of a CASE subexpression must select one of two operands")?;
                    i += 1;
                    out.body = match (arms.get(a - 1), j) {
                        (Some((g, _)), 1) => g.clone(),
                        (Some((_, v)), _) => v.clone(),
                        (None, 1) => return Err("selecting OTHER in a CASE expression".into()),
                        (None, _) => other.clone().expect("arm index checked"),
                    };
                }
                A::Except { base, updates } => {
                    let n = 1 + updates.len();
                    match arg_num(sel, n) {
                        Some(1) => out.body = base.clone(),
                        Some(_) => return Err("selecting a subexpression of an EXCEPT is not yet implemented".into()),
                        None => return Err(format!("`{}` is out of range (the expression has {n} operand(s))", sel_name(sel))),
                    }
                }
                _ => {
                    let ops = operands(&cur)?;
                    let n = ops.len();
                    let a = arg_num(sel, n)
                        .ok_or_else(|| format!("`{}` is out of range (the expression has {n} operand(s))", sel_name(sel)))?;
                    out.body = ops[a - 1].clone();
                }
            },
            ast::Selector::Args(args) => {
                let Some((vars, body)) = binder(&cur) else {
                    return Err("`!(...)` selects the body of a binding construct or LAMBDA".into());
                };
                if vars.len() != args.len() {
                    return Err(format!(
                        "selector with {} argument(s) used for an expression with {} bound identifier(s)",
                        args.len(),
                        vars.len()
                    ));
                }
                out.params.extend(expr_params(vars));
                out.body = body.clone();
            }
            ast::Selector::Label(l, args) if prev_opsel && let_def(&cur, &l.name).is_some() => {
                let A::Let { defs, .. } = &*cur.kind else { unreachable!() };
                let od = let_def(&cur, &l.name).expect("checked");
                if !(op_arg && args.is_empty()) && args.len() != od.params.len() {
                    return Err(format!("`{}` takes {} argument(s), {} given", l.name, od.params.len(), args.len()));
                }
                out.lets.push(defs.clone());
                out.params.extend(od.params.iter().cloned());
                out.body = od.body.clone();
            }
            ast::Selector::Label(l, args) => {
                let mut lets = Vec::new();
                let Some((params, body)) = find_label(&out.body.clone(), &l.name, &mut lets) else {
                    return Err(format!("label `{}` not found", l.name));
                };
                if !(op_arg && args.is_empty()) && params.len() != args.len() {
                    return Err(format!("label `{}` has {} parameter(s), {} argument(s) given", l.name, params.len(), args.len()));
                }
                out.lets.extend(lets);
                out.params.extend(expr_params(params));
                out.body = body;
            }
        }
        i += 1;
    }
    Ok(out)
}

/// The operator definition `name` of LET expression `e`.
fn let_def<'e>(e: &'e ast::Expr, name: &str) -> Option<&'e ast::OpDef> {
    let ast::ExprKind::Let { defs, .. } = &*e.kind else { return None };
    defs.iter().find_map(|d| match d {
        ast::Unit::OpDef(od) if &*od.name.name == name => Some(od),
        _ => None,
    })
}

/// Pre-order search for label `name` (not inside LET definitions, nor
/// inside other labels: nested labels are selected through their outer
/// label). Returns the label's parameters and body; `lets` receives the
/// definitions of the LETs on the way.
fn find_label(e: &ast::Expr, name: &str, lets: &mut Vec<Vec<ast::Unit>>) -> Option<(Vec<ast::Ident>, ast::Expr)> {
    use ast::ExprKind as A;
    if let A::Label { name: l, params, body } = &*e.kind {
        if &*l.name == name {
            return Some((params.clone(), body.clone()));
        }
        return None;
    }
    if let A::Let { defs, body } = &*e.kind {
        lets.push(defs.clone());
        let r = find_label(body, name, lets);
        if r.is_none() {
            lets.pop();
        }
        return r;
    }
    let mut kids: Vec<&ast::Expr> = Vec::new();
    match &*e.kind {
        A::Num(_) | A::Decimal(_) | A::Str(_) | A::Bool(_) | A::At | A::Label { .. } | A::Let { .. } => {}
        A::OpAppl { prefix, args, .. } => {
            kids.extend(prefix.iter().flat_map(|p| &p.args));
            kids.extend(args.iter());
        }
        A::Subexpr { base, .. } => kids.push(base),
        A::Lambda { body, .. } | A::QuantUnbounded { body, .. } | A::TemporalQuant { body, .. } => kids.push(body),
        A::And(es) | A::Or(es) | A::Tuple(es) | A::SetEnum(es) => kids.extend(es.iter()),
        A::Quant { bounds, body, .. } | A::FnConstruct { bounds, body } => {
            kids.extend(bounds.iter().map(|b| &b.set));
            kids.push(body);
        }
        A::SetMap { expr, bounds } => {
            kids.extend(bounds.iter().map(|b| &b.set));
            kids.push(expr);
        }
        A::Choose { set, body, .. } => {
            kids.extend(set.iter());
            kids.push(body);
        }
        A::SetFilter { bound, pred } => {
            kids.push(&bound.set);
            kids.push(pred);
        }
        A::If { cond, then, els } => kids.extend([cond, then, els]),
        A::Case { arms, other } => {
            for (g, v) in arms {
                kids.push(g);
                kids.push(v);
            }
            kids.extend(other.iter());
        }
        A::FnApp { func, args } => {
            kids.push(func);
            kids.extend(args.iter());
        }
        A::FnSet { domain, range } => kids.extend([domain, range]),
        A::Record(fs) | A::RecordSet(fs) => kids.extend(fs.iter().map(|(_, v)| v)),
        A::Field { record, .. } => kids.push(record),
        A::Except { base, updates } => {
            kids.push(base);
            for (keys, v) in updates {
                for k in keys {
                    if let ast::ExceptKey::Index(ix) = k {
                        kids.extend(ix.iter());
                    }
                }
                kids.push(v);
            }
        }
        A::BoxAction { action, sub } | A::AngleAction { action, sub } => kids.extend([action, sub]),
        A::Fairness { sub, action, .. } => kids.extend([sub, action]),
    }
    kids.into_iter().find_map(|k| find_label(k, name, lets))
}
