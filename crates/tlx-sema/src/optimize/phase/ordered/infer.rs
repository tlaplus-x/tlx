//! Equivariance checks over normalized expressions and their numeric origins.
use super::{shape::Shape, syntax, variable, Analysis};
use crate::{builtins::Builtin as B, hir::*};
use std::collections::HashMap;

type Locals = HashMap<LocalId, Shape>;

impl Analysis<'_> {
    pub(super) fn bounds(&mut self, bounds: &[Bound], locals: &Locals, depth: usize) -> Option<Locals> {
        let mut scope = locals.clone();
        for b in bounds {
            let element = self.value(&b.set, &scope, depth + 1)?.elements()?;
            let BoundVars::Many(ids) = &b.vars else { return None };
            for id in ids {
                scope.insert(*id, element.clone());
            }
        }
        Some(scope)
    }

    pub(super) fn value(&mut self, e: &Expr, locals: &Locals, depth: usize) -> Option<Shape> {
        let shape = self.infer_value(e, locals, depth)?;
        // A consumer can erase provenance while still observing equality or
        // order inside its argument: Cardinality({frontier, 1}) is one case.
        // Retain anchors at every intermediate value, not just comparisons
        // and stored variable shapes.
        if shape.colored() {
            self.observations.push(shape.clone());
        }
        Some(shape)
    }

    fn infer_value(&mut self, e: &Expr, locals: &Locals, depth: usize) -> Option<Shape> {
        if depth > 160 {
            return None;
        }
        if let Some(h) = &self.history {
            if syntax::latest(e, h.variable) {
                return Some(Shape::family(h.family));
            }
        }
        let out = match &*e.kind {
            ExprKind::Var(v) => {
                if self.history.as_ref().is_some_and(|h| h.variable == *v) {
                    return None;
                }
                self.shapes[v.idx()].clone()
            }
            ExprKind::Num(n) => Shape::number(*n),
            ExprKind::Str(_) | ExprKind::Bool(_) => Shape::plain(),
            ExprKind::Const(c) => self.constants.get(c)?.clone(),
            ExprKind::Local(l) => locals.get(l)?.clone(),
            ExprKind::Record(fields) => {
                let mut out = Shape::default();
                for (name, value) in fields {
                    out.fields.insert(name.clone(), self.value(value, locals, depth + 1)?);
                }
                out
            }
            ExprKind::Field { record, field } => self.value(record, locals, depth + 1)?.field(field)?,
            ExprKind::FnApp { func, args } => {
                if args.len() != 1 {
                    return None;
                }
                let key = self.value(&args[0], locals, depth + 1)?;
                if let Some(h) = &self.history {
                    if variable(func, false).or_else(|| variable(func, true)) == Some(h.variable) {
                        let value = self.shapes[h.variable.idx()].value.as_deref().cloned().unwrap_or_default();
                        self.observations.push(Shape::family(h.family).joined(&key)?);
                        return Some(value);
                    }
                }
                let f = self.value(func, locals, depth + 1)?;
                if let Some(domain) = &f.key {
                    self.observations.push(domain.as_ref().clone().joined(&key)?);
                }
                if let ExprKind::Str(name) = &*args[0].kind {
                    f.field(name)?
                } else {
                    f.range()?
                }
            }
            ExprKind::Tuple(es) | ExprKind::SetEnum(es) => {
                let mut elements = Shape::default();
                for e in es {
                    elements.join(&self.value(e, locals, depth + 1)?)?;
                }
                if matches!(&*e.kind, ExprKind::Tuple(_)) {
                    Shape::function(Shape::integer(), elements)
                } else {
                    Shape::set(elements)
                }
            }
            ExprKind::FnConstruct { bounds, body } => {
                if bounds.len() != 1 {
                    return None;
                }
                let keys = self.value(&bounds[0].set, locals, depth + 1)?.elements()?;
                let scope = self.bounds(bounds, locals, depth + 1)?;
                Shape::function(keys, self.value(body, &scope, depth + 1)?)
            }
            ExprKind::SetMap { expr, bounds } => {
                let scope = self.bounds(bounds, locals, depth + 1)?;
                Shape::set(self.value(expr, &scope, depth + 1)?)
            }
            ExprKind::SetFilter { bound, pred } => {
                let domain = self.value(&bound.set, locals, depth + 1)?;
                let scope = self.bounds(std::slice::from_ref(bound), locals, depth + 1)?;
                self.value(pred, &scope, depth + 1)?;
                domain
            }
            ExprKind::Quant { bounds, body, .. } => {
                let scope = self.bounds(bounds, locals, depth + 1)?;
                self.value(body, &scope, depth + 1)?;
                Shape::plain()
            }
            ExprKind::Choose { vars, set: Some(set), body } => {
                let element = self.value(set, locals, depth + 1)?.elements()?;
                let BoundVars::Many(ids) = vars else { return None };
                if ids.len() != 1 {
                    return None;
                }
                let mut scope = locals.clone();
                scope.insert(ids[0], element.clone());
                self.value(body, &scope, depth + 1)?;
                element
            }
            ExprKind::If { cond, then, els } => {
                self.value(cond, locals, depth + 1)?;
                self.value(then, locals, depth + 1)?.joined(&self.value(els, locals, depth + 1)?)?
            }
            ExprKind::And(es) | ExprKind::Or(es) => {
                for e in es {
                    self.value(e, locals, depth + 1)?;
                }
                Shape::plain()
            }
            ExprKind::Except { base, updates } => {
                let mut out = self.value(base, locals, depth + 1)?;
                for (path, rhs) in updates {
                    let value = self.value(rhs, locals, depth + 1)?;
                    self.update(&mut out, path, &value, locals, depth + 1)?;
                }
                out
            }
            ExprKind::FnSet { domain, range } => {
                let keys = self.value(domain, locals, depth + 1)?.elements()?;
                let values = self.value(range, locals, depth + 1)?.elements()?;
                Shape::set(Shape::function(keys, values))
            }
            ExprKind::RecordSet(fields) => {
                let mut out = Shape::default();
                for (name, value) in fields {
                    out.fields.insert(name.clone(), self.value(value, locals, depth + 1)?.elements()?);
                }
                Shape::set(out)
            }
            ExprKind::BoxAction { action, sub } | ExprKind::AngleAction { action, sub } => {
                self.value(action, locals, depth + 1)?;
                self.value(sub, locals, depth + 1)?;
                Shape::plain()
            }
            ExprKind::Builtin { op, args } => return self.builtin(*op, args, locals, depth + 1),
            _ => return None,
        };
        Some(out)
    }

    fn update(&mut self, shape: &mut Shape, path: &[ExceptKey], rhs: &Shape, locals: &Locals, depth: usize) -> Option<()> {
        let Some((head, tail)) = path.split_first() else {
            return shape.join(rhs);
        };
        shape.container()?;
        match head {
            ExceptKey::Field(name) => self.update(shape.fields.entry(name.clone()).or_default(), tail, rhs, locals, depth + 1),
            ExceptKey::Index(args) if args.len() == 1 => {
                let key = self.value(&args[0], locals, depth + 1)?;
                shape.key.get_or_insert_with(Default::default).join(&key)?;
                self.update(shape.value.get_or_insert_with(Default::default), tail, rhs, locals, depth + 1)
            }
            _ => None,
        }
    }

    fn builtin(&mut self, op: B, args: &[Expr], locals: &Locals, depth: usize) -> Option<Shape> {
        if op == B::Prime && args.len() == 1 {
            return self.value(&args[0], locals, depth + 1);
        }
        let shapes = args.iter().map(|a| self.value(a, locals, depth + 1)).collect::<Option<Vec<_>>>()?;
        let out = match (op, shapes.as_slice()) {
            (B::Plus, [a, b]) if a.family.is_some() || b.family.is_some() => {
                let family = a.family?;
                if variable(&args[0], false) != Some(self.families[family].variable) || b.colored() || !self.nonnegative(&args[1], locals) {
                    return None;
                }
                let delta = &self.increments[family];
                let within = match (&*args[1].kind, &*delta.kind) {
                    (ExprKind::Num(n), ExprKind::Num(d)) => n <= d,
                    _ => syntax::same(&args[1], delta),
                };
                if !within {
                    return None;
                }
                Shape::family(family)
            }
            (B::DotDot, [a, b]) if a.family.is_some() || b.family.is_some() => {
                let family = a.family?;
                if b.family != Some(family) || variable(&args[0], false) != Some(self.families[family].variable) {
                    return None;
                }
                Shape::set(Shape::family(family))
            }
            (B::Eq | B::Neq | B::Lt | B::Le | B::Gt | B::Ge, [a, b]) => {
                self.observations.push(a.clone().joined(b)?);
                Shape::plain()
            }
            (B::In | B::NotIn, [a, b]) => {
                if !matches!(&*args[1].kind, ExprKind::Builtin { op: B::Nat | B::Int, args } if args.is_empty()) {
                    self.observations.push(a.clone().joined(&b.elements()?)?);
                }
                Shape::plain()
            }
            (B::Not | B::Implies | B::Equiv, _) => Shape::plain(),
            (B::Domain, [a]) => {
                a.container()?;
                let mut keys = a.key.as_deref().cloned().unwrap_or_default();
                if !a.fields.is_empty() {
                    keys.join(&Shape::plain())?;
                }
                Shape::set(keys)
            }
            (B::Cardinality, [_]) => Shape::integer(),
            (B::Len, [a]) if !a.key.as_deref().is_some_and(Shape::colored) => Shape::integer(),
            (B::Cup | B::Cap | B::SetMinus, [a, b]) => a.clone().joined(b)?,
            (B::SubsetEq, [a, b]) => {
                self.observations.push(a.clone().joined(b)?);
                Shape::plain()
            }
            (B::Union, [a]) => a.elements()?,
            (B::Subset, [a]) => Shape::set(a.clone()),
            (B::Append, [a, b]) if !a.key.as_deref().is_some_and(Shape::colored) => {
                Shape::function(Shape::integer(), a.range()?.joined(b)?)
            }
            (B::Concat, [a, b]) if !a.key.as_deref().is_some_and(Shape::colored) && !b.key.as_deref().is_some_and(Shape::colored) => {
                Shape::function(Shape::integer(), a.range()?.joined(&b.range()?)?)
            }
            (B::Head, [a]) if !a.key.as_deref().is_some_and(Shape::colored) => a.range()?,
            (B::Tail, [a]) if !a.key.as_deref().is_some_and(Shape::colored) => a.clone(),
            (B::ColonGt, [a, b]) => Shape::function(a.clone(), b.clone()),
            (B::AtAt, [a, b]) => a.clone().joined(b)?,
            (B::DotDot, _) if !shapes.iter().any(Shape::colored) => Shape::set(Shape::integer()),
            (B::Neg, [a]) if !a.colored() && !a.integer && !a.opaque && !a.numbers.is_empty() => {
                let mut out = Shape::default();
                for n in &a.numbers {
                    out.numbers.insert(n.checked_neg()?);
                }
                out
            }
            (B::Plus | B::Minus | B::Mul | B::Div | B::Mod | B::Neg, _) if !shapes.iter().any(Shape::colored) => Shape::integer(),
            (B::Boolean | B::StringSet, []) => Shape::set(Shape::plain()),
            (B::Nat | B::Int, []) => Shape::set(Shape::integer()),
            _ if !shapes.iter().any(Shape::colored) => Shape::plain(),
            _ => return None,
        };
        Some(out)
    }

    pub(super) fn nonnegative(&mut self, e: &Expr, locals: &Locals) -> bool {
        match &*e.kind {
            ExprKind::Num(n) => *n >= 0,
            ExprKind::Builtin { op: B::Cardinality, args } if args.len() == 1 => {
                self.value(&args[0], locals, 0).is_some_and(|s| s.element.is_some())
            }
            _ => false,
        }
    }
}
