//! Conservative HIR-to-verification-IR translation. No unknown expression is
//! discarded: the complete Init, Next and invariant roots must translate.

use std::collections::HashMap;

use tlx_front::cfg::{CfgValue, Config, ConstBinding};

use crate::builtins::Builtin as B;
use crate::hir::*;
use crate::Program;

use super::ir::*;
use super::Diagnostic;

pub(super) fn lower(program: &mut Program, cfg: &Config) -> Result<Model, Diagnostic> {
    if cfg.specification.is_some()
        || !cfg.properties.is_empty()
        || !cfg.constraints.is_empty()
        || !cfg.action_constraints.is_empty()
        || cfg.symmetry.is_some()
        || cfg.view.is_some()
        || cfg.alias.is_some()
        || !cfg.postconditions.is_empty()
        || !cfg.possible.is_empty()
    {
        return Err(Diagnostic::new(
            "supported configuration: INIT, NEXT, INVARIANT, scalar integer CONSTANT assignments, CHECK_DEADLOCK FALSE; \
             temporal specifications, constraints, views, symmetry and other observations require additional rules",
        ));
    }
    if cfg.check_deadlock != Some(false) {
        return Err(Diagnostic::new("optimization requires CHECK_DEADLOCK FALSE; deadlock transfer is not implemented"));
    }
    if cfg.invariants.is_empty() {
        return Err(Diagnostic::new("optimization requires at least one target INVARIANT"));
    }
    let init = root(program, cfg.init.as_deref().ok_or_else(|| Diagnostic::new("missing INIT"))?)?;
    let next = root(program, cfg.next.as_deref().ok_or_else(|| Diagnostic::new("missing NEXT"))?)?;
    let properties = cfg.invariants.iter().map(|name| root(program, name)).collect::<Result<Vec<_>, _>>()?;
    if let Some(name) = program.check_cfg_constants(cfg) {
        return Err(Diagnostic::new(format!("unassigned constant {name}")));
    }
    let mut constants = HashMap::new();
    for binding in &cfg.constants {
        let ConstBinding::Value { name, value: CfgValue::Int(value), module: None } = binding else {
            return Err(Diagnostic::new("only global scalar integer constant assignments are supported; overrides are rejected"));
        };
        let Some(RootSymbol::Const(id)) = program.lookup_root(name) else {
            return Err(Diagnostic::new(format!("{name} is not a constant parameter")));
        };
        if program.consts[id.idx()].arity != 0 || constants.insert(id, i128::from(*value)).is_some() {
            return Err(Diagnostic::new(format!("duplicate or operator-valued constant {name}")));
        }
    }
    let errors = program.take_errors();
    if !errors.is_empty() {
        return Err(Diagnostic::new(errors.iter().map(ToString::to_string).collect::<Vec<_>>().join("\n")));
    }
    if program.vars.is_empty() {
        return Err(Diagnostic::new("optimization requires state variables"));
    }
    let mut expander = Expander { program, constants, remaining: 100_000, stack: Vec::new() };
    for assumption in &program.assumes {
        let e = expander.expand(assumption, &HashMap::new(), 0)?;
        if predicate(&e)? != Predicate::Bool(true) {
            return Err(Diagnostic::at(e.span, "ASSUME must reduce to TRUE in the supported constant fragment"));
        }
    }
    let init = expander.expand(&init, &HashMap::new(), 0)?;
    let next = expander.expand(&next, &HashMap::new(), 0)?;
    let n = program.vars.len();
    let mut initial = vec![None; n];
    let mut conjuncts = Vec::new();
    flatten_and(&init, &mut conjuncts);
    for e in conjuncts {
        if let Some((B::Eq, [left, right])) = binary(e) {
            let (var, value) = match (&*left.kind, &*right.kind) {
                (ExprKind::Var(v), _) => (v.idx(), natural(right)?),
                (_, ExprKind::Var(v)) => (v.idx(), natural(left)?),
                _ => return Err(Diagnostic::at(e.span, "Init requires scalar variable = natural assignments")),
            };
            if initial[var].replace(value).is_some() {
                return Err(Diagnostic::at(e.span, "duplicate initialization"));
            }
        } else if !matches!(&*e.kind, ExprKind::Bool(true)) {
            return Err(Diagnostic::at(e.span, "Init requires a conjunction of scalar assignments"));
        }
    }
    let initial = initial
        .into_iter()
        .enumerate()
        .map(|(i, value)| value.ok_or_else(|| Diagnostic::new(format!("Init does not assign {}", program.vars[i].name))))
        .collect::<Result<Vec<_>, _>>()?;
    let mut branches = Vec::new();
    flatten_or(&next, &mut branches);
    let actions = branches.into_iter().map(|e| action(e, n)).collect::<Result<Vec<_>, _>>()?;
    let properties = properties
        .iter()
        .zip(&cfg.invariants)
        .map(|(e, name)| {
            let e = expander.expand(e, &HashMap::new(), 0)?;
            Ok(Property { name: name.clone(), span: e.span, predicate: predicate(&e)? })
        })
        .collect::<Result<_, Diagnostic>>()?;
    Ok(Model {
        variables: program.vars.iter().map(|v| Variable { name: v.name.to_string(), span: v.span, domain: Domain::Natural }).collect(),
        initial,
        actions,
        properties,
    })
}

fn root(program: &mut Program, name: &str) -> Result<Expr, Diagnostic> {
    let Some(RootSymbol::Def(d)) = program.lookup_root(name) else {
        return Err(Diagnostic::new(format!("{name} must name a definition")));
    };
    program.require(d);
    let def = &program.defs[d.idx()];
    if !def.params.is_empty() {
        return Err(Diagnostic::at(def.span, "configuration roots must have no parameters"));
    }
    Ok(Expr::new(ExprKind::Apply { op: OpRef::Def(d), args: Vec::new() }, def.span))
}

struct Expander<'a> {
    program: &'a Program,
    constants: HashMap<ConstId, i128>,
    remaining: usize,
    stack: Vec<DefId>,
}

impl Expander<'_> {
    fn expand(&mut self, e: &Expr, env: &HashMap<LocalId, Expr>, depth: usize) -> Result<Expr, Diagnostic> {
        if depth >= 128 || self.remaining == 0 {
            return Err(Diagnostic::at(e.span, "normalization budget exceeded (128 levels / 100000 nodes)"));
        }
        self.remaining -= 1;
        if let ExprKind::Builtin { op, .. } = &*e.kind {
            if op.metadata().effect != crate::builtins::Effect::Pure {
                return Err(Diagnostic::at(e.span, "effectful operators are outside the optimization contract"));
            }
        }
        match &*e.kind {
            ExprKind::Const(c) => self
                .constants
                .get(c)
                .map(|n| Expr::new(ExprKind::Num(*n), e.span))
                .ok_or_else(|| Diagnostic::at(e.span, "unbound or unsupported constant")),
            ExprKind::Local(l) => match env.get(l) {
                Some(value) => self.expand(value, &HashMap::new(), depth + 1),
                None => Err(Diagnostic::at(e.span, "unbound local or unsupported binding form")),
            },
            ExprKind::Let { body, .. } => self.expand(body, env, depth + 1),
            ExprKind::Apply { op, args } => {
                let args = args.iter().map(|arg| self.expand(arg, env, depth + 1)).collect::<Result<Vec<_>, _>>()?;
                match op {
                    OpRef::Builtin(op) => self.expand(&Expr::new(ExprKind::Builtin { op: *op, args }, e.span), env, depth + 1),
                    OpRef::Def(d) => {
                        let def = &self.program.defs[d.idx()];
                        if let Some(op) = def.builtin {
                            return self.expand(&Expr::new(ExprKind::Builtin { op, args }, e.span), env, depth + 1);
                        }
                        if self.stack.contains(d) || def.params.len() != args.len() {
                            return Err(Diagnostic::at(e.span, "recursive or malformed operator application"));
                        }
                        let DefKind::Op(body) = &def.kind else {
                            return Err(Diagnostic::at(e.span, "unsupported function or unresolved definition"));
                        };
                        let mut bound = env.clone();
                        bound.extend(def.params.iter().copied().zip(args));
                        self.stack.push(*d);
                        let result = self.expand(body, &bound, depth + 1);
                        self.stack.pop();
                        result
                    }
                    _ => Err(Diagnostic::at(e.span, "operator constants and higher-order parameters require effect summaries")),
                }
            }
            _ => {
                let mut result = Expr::new((*e.kind).clone(), e.span);
                let mut error = None;
                crate::visit::children_mut(&mut result, &mut |child| {
                    if error.is_none() {
                        match self.expand(child, env, depth + 1) {
                            Ok(expanded) => *child = expanded,
                            Err(e) => error = Some(e),
                        }
                    }
                });
                match error {
                    Some(e) => Err(e),
                    None => Ok(result),
                }
            }
        }
    }
}

fn binary(e: &Expr) -> Option<(B, &[Expr; 2])> {
    match &*e.kind {
        ExprKind::Builtin { op, args } => Some((*op, args.as_slice().try_into().ok()?)),
        _ => None,
    }
}

fn natural(e: &Expr) -> Result<u32, Diagnostic> {
    match &*e.kind {
        ExprKind::Num(n) if (0..=i128::from(i32::MAX)).contains(n) => Ok(*n as u32),
        _ => Err(Diagnostic::at(e.span, "expected a configured natural literal within the backend integer range")),
    }
}

fn flatten_and<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
    match &*e.kind {
        ExprKind::And(es) => es.iter().for_each(|e| flatten_and(e, out)),
        _ => out.push(e),
    }
}

fn flatten_or<'a>(e: &'a Expr, out: &mut Vec<&'a Expr>) {
    match &*e.kind {
        ExprKind::Or(es) => es.iter().for_each(|e| flatten_or(e, out)),
        _ => out.push(e),
    }
}

fn primed_var(e: &Expr) -> Option<usize> {
    match &*e.kind {
        ExprKind::Builtin { op: B::Prime, args } if args.len() == 1 => match &*args[0].kind {
            ExprKind::Var(v) => Some(v.idx()),
            _ => None,
        },
        _ => None,
    }
}

fn action(e: &Expr, n: usize) -> Result<Action, Diagnostic> {
    let mut updates = vec![None; n];
    let mut guards = Vec::new();
    let mut conjuncts = Vec::new();
    flatten_and(e, &mut conjuncts);
    for term in conjuncts {
        let mut assign = |var: usize, update| {
            if updates[var].replace(update).is_some() {
                Err(Diagnostic::at(term.span, "multiple updates for a variable in one action"))
            } else {
                Ok(())
            }
        };
        if let Some((B::Eq, [left, right])) = binary(term).filter(|(_, [a, b])| primed_var(a).is_some() || primed_var(b).is_some()) {
            let (var, rhs) = match primed_var(left) {
                Some(var) => (var, right),
                None => (primed_var(right).expect("filtered primed variable"), left),
            };
            let update =
                match &*rhs.kind {
                    ExprKind::Num(0) => Update::Reset,
                    ExprKind::Var(v) if v.idx() == var => Update::Keep,
                    _ => match binary(rhs) {
                        Some((B::Plus, [a, b]))
                            if matches!(&*a.kind, ExprKind::Var(v) if v.idx() == var) && matches!(&*b.kind, ExprKind::Num(1)) =>
                        {
                            Update::Increment
                        }
                        _ => return Err(Diagnostic::at(
                            rhs.span,
                            "counter update must keep, reset to zero, or increment itself by one; copies and decrements are unsupported",
                        )),
                    },
                };
            assign(var, update)?;
        } else if let ExprKind::Builtin { op: B::Unchanged, args } = &*term.kind {
            let [arg] = args.as_slice() else { return Err(Diagnostic::at(term.span, "malformed UNCHANGED")) };
            let values = match &*arg.kind {
                ExprKind::Tuple(values) => values.as_slice(),
                _ => std::slice::from_ref(arg),
            };
            for value in values {
                let ExprKind::Var(v) = &*value.kind else { return Err(Diagnostic::at(value.span, "UNCHANGED requires scalar variables")) };
                assign(v.idx(), Update::Keep)?;
            }
        } else {
            guards.push(predicate(term)?);
        }
    }
    let updates = updates
        .into_iter()
        .map(|u| u.ok_or_else(|| Diagnostic::at(e.span, "every action must explicitly update or UNCHANGED every variable")))
        .collect::<Result<_, _>>()?;
    Ok(Action { span: e.span, guard: Predicate::And(guards), updates })
}

fn predicate(e: &Expr) -> Result<Predicate, Diagnostic> {
    let result = match &*e.kind {
        ExprKind::Bool(b) => Predicate::Bool(*b),
        ExprKind::And(es) => Predicate::And(es.iter().map(predicate).collect::<Result<_, _>>()?),
        ExprKind::Or(es) => Predicate::Or(es.iter().map(predicate).collect::<Result<_, _>>()?),
        ExprKind::Builtin { op: B::Not, args } if args.len() == 1 => Predicate::Not(Box::new(predicate(&args[0])?)),
        ExprKind::Builtin { op: B::Implies, args } if args.len() == 2 => {
            Predicate::Or(vec![Predicate::Not(Box::new(predicate(&args[0])?)), predicate(&args[1])?])
        }
        _ => {
            let Some((op, [a, b])) = binary(e) else {
                return Err(Diagnostic::at(
                    e.span,
                    "unsupported observation; expected a Boolean combination of counter-to-constant comparisons",
                ));
            };
            let op = match op {
                B::Eq => Comparison::Eq,
                B::Neq => Comparison::Ne,
                B::Lt => Comparison::Lt,
                B::Le => Comparison::Le,
                B::Gt => Comparison::Gt,
                B::Ge => Comparison::Ge,
                _ => return Err(Diagnostic::at(e.span, "unsupported observation operator")),
            };
            match (&*a.kind, &*b.kind) {
                (ExprKind::Var(v), _) => Predicate::Compare { var: v.idx(), op, value: natural(b)? },
                (_, ExprKind::Var(v)) => Predicate::Compare { var: v.idx(), op: op.reverse(), value: natural(a)? },
                _ => Predicate::Bool(op.test(u64::from(natural(a)?), u64::from(natural(b)?))),
            }
        }
    };
    Ok(result)
}
