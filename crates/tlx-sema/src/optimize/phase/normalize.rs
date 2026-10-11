//! Bounded, analysis-only expansion. Executable definitions remain untouched.

use std::collections::HashMap;

use crate::{builtins::Effect, hir::*, visit, Program};

pub(super) struct Normalizer<'a> {
    program: &'a Program,
    stack: Vec<DefId>,
    remaining: usize,
    local: u32,
    at: Option<Expr>,
    at_reads: usize,
}

impl<'a> Normalizer<'a> {
    pub fn new(program: &'a Program) -> Self {
        Self { program, stack: Vec::new(), remaining: 100_000, local: program.locals.len() as u32, at: None, at_reads: 0 }
    }

    pub fn root(&mut self, e: &Expr) -> Option<Expr> {
        self.expand(e, &HashMap::new(), 0)
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

    fn bounds(&mut self, bounds: &[Bound], env: &mut HashMap<LocalId, Expr>, depth: usize) -> Option<Vec<Bound>> {
        bounds
            .iter()
            .map(|b| {
                let set = self.expand(&b.set, env, depth)?;
                let vars = self.bind(&b.vars, env, b.set.span);
                Some(Bound { vars, set })
            })
            .collect()
    }

    fn expand(&mut self, e: &Expr, env: &HashMap<LocalId, Expr>, depth: usize) -> Option<Expr> {
        if depth >= 128 || self.remaining == 0 {
            return None;
        }
        self.remaining -= 1;
        let kind = match &*e.kind {
            ExprKind::Local(l) => return Some(env.get(l).unwrap_or(e).clone()),
            ExprKind::At => {
                self.at_reads += 1;
                return self.at.clone();
            }
            ExprKind::Let { body, .. } => return self.expand(body, env, depth + 1),
            ExprKind::Apply { op, args } => {
                let args: Vec<_> = args.iter().map(|a| self.expand(a, env, depth + 1)).collect::<Option<_>>()?;
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
                            // TLA+ parameters are by name. Substitution keeps
                            // each actual read in the callee's control context;
                            // expansion above still refuses effectful actuals.
                            let mut scope = env.clone();
                            scope.extend(d.params.iter().copied().zip(args));
                            let body = match &d.kind {
                                DefKind::Op(body) => body.clone(),
                                DefKind::Fn { bounds, body } => {
                                    Expr::new(ExprKind::FnConstruct { bounds: bounds.clone(), body: body.clone() }, d.span)
                                }
                                DefKind::Pending => return None,
                            };
                            self.stack.push(*id);
                            let result = self.expand(&body, &scope, depth + 1);
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
                let bounds = self.bounds(bounds, &mut scope, depth + 1)?;
                ExprKind::Quant { kind: *kind, bounds, body: self.expand(body, &scope, depth + 1)? }
            }
            ExprKind::FnConstruct { bounds, body } => {
                let mut scope = env.clone();
                let bounds = self.bounds(bounds, &mut scope, depth + 1)?;
                ExprKind::FnConstruct { bounds, body: self.expand(body, &scope, depth + 1)? }
            }
            ExprKind::SetMap { expr, bounds } => {
                let mut scope = env.clone();
                let bounds = self.bounds(bounds, &mut scope, depth + 1)?;
                ExprKind::SetMap { expr: self.expand(expr, &scope, depth + 1)?, bounds }
            }
            ExprKind::SetFilter { bound, pred } => {
                let mut scope = env.clone();
                let mut bounds = self.bounds(std::slice::from_ref(bound), &mut scope, depth + 1)?;
                ExprKind::SetFilter { bound: bounds.remove(0), pred: self.expand(pred, &scope, depth + 1)? }
            }
            ExprKind::Choose { vars, set, body } => {
                let set = match set {
                    Some(s) => Some(self.expand(s, env, depth + 1)?),
                    None => None,
                };
                let mut scope = env.clone();
                let vars = self.bind(vars, &mut scope, e.span);
                ExprKind::Choose { vars, set, body: self.expand(body, &scope, depth + 1)? }
            }
            ExprKind::Except { base, updates } => {
                let base = self.expand(base, env, depth + 1)?;
                let mut expanded = Vec::new();
                for (path, rhs) in updates {
                    let mut old = base.clone();
                    let mut keys = Vec::new();
                    for key in path {
                        let key = match key {
                            ExceptKey::Field(field) => ExceptKey::Field(field.clone()),
                            ExceptKey::Index(args) => {
                                ExceptKey::Index(args.iter().map(|e| self.expand(e, env, depth + 1)).collect::<Option<_>>()?)
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
                    let outer = self.at.replace(old);
                    let reads = self.at_reads;
                    let rhs = self.expand(rhs, env, depth + 1);
                    self.at = outer;
                    // EXCEPT updates are sequential. Using the original base
                    // for @ is valid only when preceding writes cannot touch
                    // this point. Check after expansion to include LET helpers.
                    if self.at_reads != reads && expanded.iter().any(|(prior, _): &(Vec<ExceptKey>, Expr)| !disjoint(prior, path)) {
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
                visit::children_mut(&mut out, &mut |c| match self.expand(c, env, depth + 1) {
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
