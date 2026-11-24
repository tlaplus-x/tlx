//! Bounded, analysis-only expansion. Executable definitions remain untouched.

use std::collections::{BTreeMap, HashMap};

use tlx_front::cfg::Config;

use super::ConstSubstTarget;
use crate::{builtins::Effect, hir::*, visit, Program};

pub(super) struct Normalizer<'a> {
    program: &'a Program,
    cfg: &'a Config,
    stack: Vec<DefId>,
    const_stack: Vec<ConstId>,
    expanded_substs: BTreeMap<ConstId, String>,
    remaining: usize,
    local: u32,
    at_stack: Vec<(Expr, bool)>,
    let_at: HashMap<DefId, Option<usize>>,
}

impl<'a> Normalizer<'a> {
    pub fn with_config(program: &'a Program, cfg: &'a Config) -> Self {
        Self {
            program,
            cfg,
            stack: Vec::new(),
            const_stack: Vec::new(),
            expanded_substs: BTreeMap::new(),
            remaining: 100_000,
            local: program.locals.len() as u32,
            at_stack: Vec::new(),
            let_at: HashMap::new(),
        }
    }

    fn def_body(d: &Def) -> Option<Expr> {
        match &d.kind {
            DefKind::Op(body) => Some(body.clone()),
            DefKind::Fn { bounds, body } => Some(Expr::new(ExprKind::FnConstruct { bounds: bounds.clone(), body: body.clone() }, d.span)),
            DefKind::Pending => None,
        }
    }

    pub fn attach_const_subst(&self, cert: super::OpenCert) -> Option<String> {
        super::attach_const_subst_obligation(
            self.program,
            self.cfg,
            &self.expanded_substs,
            |cid| Self::expand_declared_const_subst(self.program, self.cfg, cid),
            cert,
        )
    }

    pub fn expand_declared_const_subst(program: &'a Program, cfg: &'a Config, c: ConstId) -> Option<String> {
        let (seen, terminal) = super::resolve_const_subst_chain(program, cfg, c)?;
        let resolved = match terminal {
            ConstSubstTarget::PureBuiltin(op, span) => Expr::new(ExprKind::Builtin { op, args: vec![] }, span),
            ConstSubstTarget::Const(other) => Expr::new(ExprKind::Const(other), Span::default()),
            ConstSubstTarget::Def(id) => {
                let body = Self::def_body(&program.defs[id.idx()])?;
                let mut fresh = Self::with_config(program, cfg);
                fresh.const_stack.extend_from_slice(&seen);
                fresh.stack.push(id);
                fresh.expand(&body, &HashMap::new(), None, 1)?
            }
        };
        super::canonical_expr_repr(program, &resolved)
    }

    fn record_const_subst(&mut self, c: ConstId, res: &Expr) -> bool {
        let Some(repr) = super::canonical_expr_repr(self.program, res) else {
            return false;
        };
        match self.expanded_substs.get(&c) {
            Some(prev) => prev == &repr,
            None => {
                self.expanded_substs.insert(c, repr);
                true
            }
        }
    }

    pub fn root(&mut self, e: &Expr) -> Option<Expr> {
        self.expand(e, &HashMap::new(), None, 0)
    }

    fn bind(&mut self, vars: &BoundVars, env: &mut HashMap<LocalId, Expr>, span: Span) -> BoundVars {
        let ids = vars
            .locals()
            .iter()
            .map(|old| {
                let id = LocalId(self.local);
                self.local += 1;
                env.insert(*old, Expr::new(ExprKind::Local(id), span));
                id
            })
            .collect();
        match vars {
            BoundVars::Many(_) => BoundVars::Many(ids),
            BoundVars::Tuple(_) => BoundVars::Tuple(ids),
        }
    }

    fn bounds(&mut self, bounds: &[Bound], env: &mut HashMap<LocalId, Expr>, lex_at: Option<usize>, depth: usize) -> Option<Vec<Bound>> {
        bounds
            .iter()
            .map(|b| {
                let set = self.expand(&b.set, env, lex_at, depth)?;
                let vars = self.bind(&b.vars, env, b.set.span);
                Some(Bound { vars, set })
            })
            .collect()
    }

    fn expand_const(&mut self, c: ConstId, span: Span, env: &HashMap<LocalId, Expr>, lex_at: Option<usize>, depth: usize) -> Option<Expr> {
        if self.program.consts[c.idx()].arity != 0 || self.cfg.last_constant_subst(&self.program.consts[c.idx()].name).is_none() {
            return Some(Expr::new(ExprKind::Const(c), span));
        }
        if self.const_stack.contains(&c) {
            return None;
        }
        let res = match super::resolve_const_subst_target(self.program, self.cfg, c)? {
            ConstSubstTarget::PureBuiltin(op, _) => Expr::new(ExprKind::Builtin { op, args: vec![] }, span),
            ConstSubstTarget::Def(id) => {
                if self.stack.contains(&id) {
                    return None;
                }
                let body = Self::def_body(&self.program.defs[id.idx()])?;
                self.const_stack.push(c);
                self.stack.push(id);
                let res = self.expand(&body, &HashMap::new(), None, depth + 1);
                self.stack.pop();
                self.const_stack.pop();
                res?
            }
            ConstSubstTarget::Const(other) => {
                self.const_stack.push(c);
                let res = self.expand(&Expr::new(ExprKind::Const(other), span), env, lex_at, depth + 1);
                self.const_stack.pop();
                res?
            }
        };
        self.record_const_subst(c, &res).then_some(res)
    }

    fn expand(&mut self, e: &Expr, env: &HashMap<LocalId, Expr>, lex_at: Option<usize>, depth: usize) -> Option<Expr> {
        if depth >= 128 || self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        let kind = match &*e.kind {
            ExprKind::Local(l) => return Some(env.get(l).unwrap_or(e).clone()),
            ExprKind::Const(c) => return self.expand_const(*c, e.span, env, lex_at, depth),
            ExprKind::At => {
                let idx = lex_at?;
                let (expr, used) = self.at_stack.get_mut(idx)?;
                *used = true;
                return Some(expr.clone());
            }
            ExprKind::Let { defs, body } => {
                let prev: Vec<_> = defs.iter().map(|&d| (d, self.let_at.insert(d, lex_at))).collect();
                let res = self.expand(body, env, lex_at, depth + 1);
                for (d, old) in prev {
                    match old {
                        Some(v) => {
                            self.let_at.insert(d, v);
                        }
                        None => {
                            self.let_at.remove(&d);
                        }
                    }
                }
                return res;
            }
            ExprKind::Apply { op, args } => {
                let args: Vec<_> = args.iter().map(|a| self.expand(a, env, lex_at, depth + 1)).collect::<Option<_>>()?;
                match op {
                    OpRef::Builtin(op) => ExprKind::Builtin { op: *op, args },
                    OpRef::Def(id) => {
                        let d = &self.program.defs[id.idx()];
                        if let Some(op) = d.builtin {
                            ExprKind::Builtin { op, args }
                        } else {
                            if self.stack.contains(id) || d.params.len() != args.len() {
                                return None;
                            }
                            if self.program.is_strict_call_def(*id) && !strict_call_preserves_args(self.program, d) {
                                return None;
                            }
                            // TLA+ parameters are by name. Substitution keeps
                            // each actual read in the callee's control context;
                            // expansion above still refuses effectful actuals.
                            let mut scope = env.clone();
                            scope.extend(d.params.iter().copied().zip(args));
                            let body = Self::def_body(d)?;
                            let def_at = self.let_at.get(id).copied().unwrap_or(None);
                            self.stack.push(*id);
                            let result = self.expand(&body, &scope, def_at, depth + 1);
                            self.stack.pop();
                            return result;
                        }
                    }
                    OpRef::Const(_) | OpRef::Param(_) => return None,
                }
            }
            ExprKind::OpArg(_) | ExprKind::Lambda { .. } | ExprKind::InstVar { .. } => return None,
            ExprKind::Quant { kind, bounds, body } => {
                let mut scope = env.clone();
                let bounds = self.bounds(bounds, &mut scope, lex_at, depth + 1)?;
                ExprKind::Quant { kind: *kind, bounds, body: self.expand(body, &scope, lex_at, depth + 1)? }
            }
            ExprKind::FnConstruct { bounds, body } => {
                let mut scope = env.clone();
                let bounds = self.bounds(bounds, &mut scope, lex_at, depth + 1)?;
                ExprKind::FnConstruct { bounds, body: self.expand(body, &scope, lex_at, depth + 1)? }
            }
            ExprKind::SetMap { expr, bounds } => {
                let mut scope = env.clone();
                let bounds = self.bounds(bounds, &mut scope, lex_at, depth + 1)?;
                ExprKind::SetMap { expr: self.expand(expr, &scope, lex_at, depth + 1)?, bounds }
            }
            ExprKind::SetFilter { bound, pred } => {
                let mut scope = env.clone();
                let mut bounds = self.bounds(std::slice::from_ref(bound), &mut scope, lex_at, depth + 1)?;
                ExprKind::SetFilter { bound: bounds.remove(0), pred: self.expand(pred, &scope, lex_at, depth + 1)? }
            }
            ExprKind::Choose { vars, set, body } => {
                let set = match set {
                    Some(s) => Some(self.expand(s, env, lex_at, depth + 1)?),
                    None => None,
                };
                let mut scope = env.clone();
                let vars = self.bind(vars, &mut scope, e.span);
                ExprKind::Choose { vars, set, body: self.expand(body, &scope, lex_at, depth + 1)? }
            }
            ExprKind::Except { base, updates } => {
                let base = self.expand(base, env, lex_at, depth + 1)?;
                let mut expanded = Vec::new();
                for (path, rhs) in updates {
                    let mut old = base.clone();
                    let mut keys = Vec::new();
                    for key in path {
                        let key = match key {
                            ExceptKey::Field(field) => ExceptKey::Field(field.clone()),
                            ExceptKey::Index(args) => {
                                ExceptKey::Index(args.iter().map(|e| self.expand(e, env, lex_at, depth + 1)).collect::<Option<_>>()?)
                            }
                        };
                        old = Expr::new(
                            match &key {
                                ExceptKey::Field(field) => ExprKind::Field { record: old, field: field.clone() },
                                ExceptKey::Index(args) => ExprKind::FnApp { func: old, args: args.clone() },
                            },
                            e.span,
                        );
                        keys.push(key);
                    }
                    let at_idx = self.at_stack.len();
                    self.at_stack.push((old, false));
                    let rhs = self.expand(rhs, env, Some(at_idx), depth + 1);
                    let (_, at_used) = self.at_stack.pop().unwrap();
                    // EXCEPT updates are sequential. Using the original base
                    // for @ is valid only when preceding writes cannot touch
                    // this point. Check after expansion to include LET helpers.
                    if at_used && expanded.iter().any(|(prior, _): &(Vec<ExceptKey>, Expr)| !disjoint(prior, path)) {
                        return None;
                    }
                    expanded.push((keys, rhs?));
                }
                ExprKind::Except { base, updates: expanded }
            }
            ExprKind::QuantUnbounded { .. } | ExprKind::TemporalQuant { .. } => return None,
            _ => {
                let mut out = Expr::new((*e.kind).clone(), e.span);
                let mut valid = true;
                visit::children_mut(&mut out, &mut |c| match self.expand(c, env, lex_at, depth + 1) {
                    Some(x) => *c = x,
                    None => valid = false,
                });
                if !valid {
                    return None;
                }
                (*out.kind).clone()
            }
        };
        if matches!(&kind, ExprKind::Builtin { op, .. } if op.metadata().effect != Effect::Pure) {
            return None;
        }
        Some(Expr::new(kind, e.span))
    }
}

fn disjoint(a: &[ExceptKey], b: &[ExceptKey]) -> bool {
    // Different field names at the same path depth cannot alias, regardless
    // of whether earlier indices select the same entry. Prefixes may alias.
    a.iter().zip(b).any(|(a, b)| matches!((a, b), (ExceptKey::Field(a), ExceptKey::Field(b)) if a != b))
}

/// Whether call-by-name inlining of a strict call-by-value definition
/// (`Program::is_strict_call_def`) is guaranteed to evaluate every value
/// argument unconditionally, so partial or asymmetric arguments (such as
/// `1 \div 0` or `CHOOSE`) are never erased before totality or dependency
/// analysis.
pub(in crate::optimize::phase) fn strict_call_preserves_args(program: &Program, d: &Def) -> bool {
    let DefKind::Op(body) = &d.kind else {
        return false;
    };
    d.params.iter().all(|&p| program.locals[p.idx()].arity > 0 || param_evaluated_unconditionally(program, body, p))
}

fn param_evaluated_unconditionally(program: &Program, e: &Expr, param: LocalId) -> bool {
    use crate::builtins::Builtin as B;
    match &*e.kind {
        ExprKind::Local(l) => *l == param,
        ExprKind::And(es) | ExprKind::Or(es) => es.first().is_some_and(|a| param_evaluated_unconditionally(program, a, param)),
        ExprKind::If { cond, then, els } => {
            param_evaluated_unconditionally(program, cond, param)
                || (param_evaluated_unconditionally(program, then, param) && param_evaluated_unconditionally(program, els, param))
        }
        ExprKind::Quant { bounds, .. } | ExprKind::FnConstruct { bounds, .. } | ExprKind::SetMap { bounds, .. } => {
            bounds.first().is_some_and(|b| param_evaluated_unconditionally(program, &b.set, param))
        }
        ExprKind::SetFilter { bound, .. } => param_evaluated_unconditionally(program, &bound.set, param),
        ExprKind::Choose { set: Some(s), .. } => param_evaluated_unconditionally(program, s, param),
        ExprKind::Builtin { op, args } => match op {
            B::Implies | B::Not => args.first().is_some_and(|a| param_evaluated_unconditionally(program, a, param)),
            _ if op.is_strict_value_op() => args.iter().any(|a| param_evaluated_unconditionally(program, a, param)),
            _ => false,
        },
        ExprKind::Apply { op, args } => match op {
            OpRef::Builtin(b) => match b {
                B::Implies | B::Not => args.first().is_some_and(|a| param_evaluated_unconditionally(program, a, param)),
                _ if b.is_strict_value_op() => args.iter().any(|a| param_evaluated_unconditionally(program, a, param)),
                _ => false,
            },
            OpRef::Def(id) => {
                let d = &program.defs[id.idx()];
                if d.builtin.is_some_and(B::is_strict_value_op) || program.is_strict_call_def(*id) {
                    args.iter().any(|a| param_evaluated_unconditionally(program, a, param))
                } else {
                    false
                }
            }
            OpRef::Const(_) | OpRef::Param(_) => false,
        },
        ExprKind::Tuple(es) | ExprKind::SetEnum(es) => es.iter().any(|a| param_evaluated_unconditionally(program, a, param)),
        ExprKind::Record(fs) | ExprKind::RecordSet(fs) => fs.iter().any(|(_, a)| param_evaluated_unconditionally(program, a, param)),
        ExprKind::FnApp { func, args } => {
            param_evaluated_unconditionally(program, func, param) || args.iter().any(|a| param_evaluated_unconditionally(program, a, param))
        }
        ExprKind::Field { record, .. } => param_evaluated_unconditionally(program, record, param),
        ExprKind::Except { base, .. } => param_evaluated_unconditionally(program, base, param),
        ExprKind::FnSet { domain, range } => {
            param_evaluated_unconditionally(program, domain, param) || param_evaluated_unconditionally(program, range, param)
        }
        ExprKind::Let { body, .. } => param_evaluated_unconditionally(program, body, param),
        _ => false,
    }
}
