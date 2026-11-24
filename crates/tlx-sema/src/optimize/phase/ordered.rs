//! Order-isomorphic allocation values and garbage collection of immutable
//! versions. Applicability depends on value provenance, not schema names.

mod infer;
mod lean;
mod nested;
mod shape;
mod syntax;
#[cfg(test)]
mod tests;

use super::{binding, branches, normalize::Normalizer, variable, Branch, FieldProjection};
use crate::{builtins::Builtin as B, hir::*, Program};
use shape::Shape;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;
use tlx_front::cfg::{CfgValue, Config};

/// Structural positions whose integers belong to one allocation family.
/// Unlisted components remain exact. This is an analysis result, not user input.
#[derive(Clone, Debug, Default)]
pub struct OrderedShape {
    pub family: Option<usize>,
    pub fields: BTreeMap<Arc<str>, OrderedShape>,
    pub key: Option<Box<OrderedShape>>,
    pub value: Option<Box<OrderedShape>>,
    pub element: Option<Box<OrderedShape>>,
}

#[derive(Clone, Debug)]
pub struct OrderedHistory {
    pub variable: usize,
    pub family: usize,
}

#[derive(Clone, Debug)]
pub struct OrderedPlan {
    pub variables: Vec<OrderedShape>,
    pub anchors: Vec<Vec<i128>>,
    pub history: Option<OrderedHistory>,
}

#[derive(Clone)]
struct Family {
    variable: VarId,
    initial: i128,
}
#[derive(Clone)]
struct History {
    variable: VarId,
    family: usize,
}

struct Analysis<'a> {
    families: Vec<Family>,
    history: Option<History>,
    shapes: Vec<Shape>,
    constants: HashMap<ConstId, Shape>,
    increments: Vec<Expr>,
    observations: Vec<Shape>,
    program: &'a Program,
}

pub fn ordered_projection(program: &Program, cfg: &Config, init: &Expr, next: &Expr, observations: &[Expr]) -> Option<FieldProjection> {
    let candidate = candidate(program, cfg, init, next, observations)?;
    candidate.certificate.as_ref()?;
    Some(candidate)
}

fn candidate(program: &Program, cfg: &Config, init: &Expr, next: &Expr, observations: &[Expr]) -> Option<FieldProjection> {
    let mut expand = Normalizer::new(program);
    let initial = branches(&syntax::conditionals(&expand.root(init)?))?;
    let steps = branches(&syntax::conditionals(&syntax::lift_frames(&expand.root(next)?, program, cfg)))?;
    let observations = observations.iter().map(|e| expand.root(e)).collect::<Option<Vec<_>>>()?;
    let mut families = Vec::new();
    for i in 0..program.vars.len() {
        let v = VarId(i as u32);
        let seeds = initial
            .iter()
            .map(|b| match &*binding(b, v, false)?.kind {
                ExprKind::Num(n) if *n > 0 => Some(*n),
                _ => None,
            })
            .collect::<Option<Vec<_>>>();
        let Some(seeds) = seeds else { continue };

        if seeds.is_empty() || seeds.iter().any(|n| *n != seeds[0]) {
            continue;
        }
        if steps
            .iter()
            .any(|b| binding(b, v, true).and_then(|e| syntax::increment(&e, v)).is_some_and(|e| !matches!(&*e.kind, ExprKind::Num(0))))
            && steps.iter().all(|b| binding(b, v, true).and_then(|e| syntax::increment(&e, v)).is_some())
        {
            families.push(Family { variable: v, initial: seeds[0] });
        }
    }
    if families.is_empty() {
        return None;
    }
    let history = syntax::history(&initial, &steps, &families, program.vars.len());
    let mut constants = HashMap::new();
    for (i, c) in program.consts.iter().enumerate() {
        let value = (c.arity == 0).then(|| cfg.last_constant_value(&c.name)).flatten()?;
        constants.insert(ConstId(i as u32), config_shape(value)?);
    }
    let mut analysis = Analysis {
        shapes: vec![Shape::default(); program.vars.len()],
        constants,
        families,
        history,
        increments: vec![],
        observations: vec![],
        program,
    };
    for (i, f) in analysis.families.iter().enumerate() {
        analysis.shapes[f.variable.idx()] = Shape::family(i);
    }
    let mut stable = false;
    for _ in 0..48 {
        analysis.observations.clear();
        let old = analysis.shapes.clone();
        for (bs, primed) in [(&initial, false), (&steps, true)] {
            for b in bs {
                analysis.branch(b, primed, false)?;
            }
        }
        if analysis.shapes == old {
            stable = true;
            break;
        }
    }
    if !stable {
        return None;
    }
    analysis.observations.clear();
    // Re-check the complete relation at the post-fixed point. No read is
    // authorized using an incomplete provenance approximation.
    for (bs, primed) in [(&initial, false), (&steps, true)] {
        for b in bs {
            analysis.branch(b, primed, true)?;
        }
    }
    analysis.increments = analysis.families.iter().map(|_| Expr::new(ExprKind::Num(0), init.span)).collect();
    for e in &observations {
        analysis.value(e, &HashMap::new(), 0)?;
    }
    if let Some(h) = &analysis.history {
        if analysis.shapes[h.variable.idx()].value.as_ref()?.has_family(h.family) {
            return None;
        }
    }
    let seeds: Vec<_> = analysis.families.iter().map(|f| f.initial).collect();
    let mut anchors = vec![BTreeSet::new(); seeds.len()];
    for shape in analysis.shapes.iter().chain(&analysis.observations) {
        shape.anchors(&seeds, &mut anchors)?;
    }
    let plan = OrderedPlan {
        variables: analysis.shapes.iter().map(plan_shape).collect(),
        anchors: anchors.into_iter().map(|s| s.into_iter().collect()).collect(),
        history: analysis.history.as_ref().map(|h| OrderedHistory { variable: h.variable.idx(), family: h.family }),
    };
    let mut fields: Vec<_> = analysis.families.iter().map(|f| format!("{}.ordered-values", program.vars[f.variable.idx()].name)).collect();
    if let Some(h) = &analysis.history {
        fields.push(format!("{}.live-versions", program.vars[h.variable.idx()].name));
    }
    let values = program.vars.iter().enumerate().map(|(i, v)| Expr::new(ExprKind::Var(VarId(i as u32)), v.span)).collect();
    let certificate = lean::emit(&analysis.families, &plan, &initial, &steps, &observations)
        .or_else(|| nested::emit(program, cfg, &analysis.families, &plan, &initial, &steps, &observations));
    Some(FieldProjection { view: Expr::new(ExprKind::Tuple(values), init.span), fields, certificate, ordered: Some(plan) })
}

impl Analysis<'_> {
    fn branch(&mut self, branch: &Branch, primed: bool, check: bool) -> Option<()> {
        self.increments = self
            .families
            .iter()
            .map(|f| {
                if primed {
                    syntax::increment(&binding(branch, f.variable, true)?, f.variable)
                } else {
                    Some(Expr::new(ExprKind::Num(0), self.program.vars[f.variable.idx()].span))
                }
            })
            .collect::<Option<_>>()?;
        let locals = self.bounds(&branch.bounds, &HashMap::new(), 0)?;
        for (i, e) in self.increments.clone().iter().enumerate() {
            if !self.nonnegative(e, &locals)
                || (self.history.as_ref().is_some_and(|h| h.family == i) && !matches!(&*e.kind, ExprKind::Num(0 | 1)))
            {
                return None;
            }
        }
        for i in 0..self.shapes.len() {
            let v = VarId(i as u32);
            let rhs = match binding(branch, v, primed) {
                Some(rhs) => rhs,
                None => {
                    // A domain binding cannot rescue conflicting assignments.
                    // Otherwise the later relation check would skip their RHSs.
                    if branch.terms.iter().any(|e| match &*e.kind {
                        ExprKind::Builtin { op: B::Eq, args } => args.len() == 2 && variable(&args[0], primed) == Some(v),
                        ExprKind::Builtin { op: B::Unchanged, args } => primed && args.len() == 1 && super::unchanged(&args[0], v) != 0,
                        _ => false,
                    }) {
                        return None;
                    }
                    let domains: Vec<_> = branch
                        .terms
                        .iter()
                        .filter_map(|e| match &*e.kind {
                            ExprKind::Builtin { op: B::In, args } if args.len() == 2 && variable(&args[0], primed) == Some(v) => {
                                Some(&args[1])
                            }
                            _ => None,
                        })
                        .collect();
                    if domains.len() != 1 {
                        return None;
                    }
                    let image = self.value(domains[0], &locals, 0)?.element.map(|s| *s)?;
                    self.shapes[i].join(&image)?;
                    continue;
                }
            };
            let image = if let Some(f) = self.families.iter().position(|f| f.variable == v) {
                // Allocation transfer syntax and non-negativity were checked
                // above. Initial frontiers are positive integer literals.
                Shape::family(f)
            } else if self.history.as_ref().is_some_and(|h| h.variable == v) {
                if variable(&rhs, false) == Some(v) {
                    self.shapes[i].clone()
                } else {
                    let payload = syntax::history_extension(&rhs, v).unwrap_or(&rhs);
                    self.value(payload, &locals, 0)?
                }
            } else {
                self.value(&rhs, &locals, 0)?
            };
            self.shapes[i].join(&image)?;
        }
        if check {
            for term in &branch.terms {
                if let ExprKind::Builtin { op: B::Eq, args } = &*term.kind {
                    if args.len() == 2 && variable(&args[0], primed).is_some() {
                        continue;
                    }
                }
                if let ExprKind::Builtin { op: B::Unchanged, args } = &*term.kind {
                    if primed && args.len() == 1 && syntax::frame(&args[0]) {
                        continue;
                    }
                }
                self.value(term, &locals, 0)?;
            }
        }
        Some(())
    }
}

fn config_shape(value: &CfgValue) -> Option<Shape> {
    Some(match value {
        CfgValue::Int(n) => Shape::number(i128::from(*n)),
        CfgValue::Set(es) | CfgValue::Tuple(es) => {
            let mut element = Shape::default();
            for e in es {
                element.join(&config_shape(e)?)?;
            }
            if matches!(value, CfgValue::Set(_)) {
                Shape::set(element)
            } else {
                Shape::function(Shape::integer(), element)
            }
        }
        _ => Shape::plain(),
    })
}
fn plan_shape(s: &Shape) -> OrderedShape {
    if !s.colored() {
        return OrderedShape::default();
    }
    OrderedShape {
        family: s.family,
        fields: s.fields.iter().map(|(k, s)| (k.clone(), plan_shape(s))).collect(),
        key: s.key.as_deref().map(|s| Box::new(plan_shape(s))),
        value: s.value.as_deref().map(|s| Box::new(plan_shape(s))),
        element: s.element.as_deref().map(|s| Box::new(plan_shape(s))),
    }
}
