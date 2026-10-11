//! Structural result shapes for anonymous VIEW expressions. These follow
//! from the state layout, so rebuilding that layout also rebuilds the VIEW.

use tlx_layout::{Layout, Shape};
use tlx_sema::{builtins::Builtin as B, hir::*};

pub(super) fn infer(e: &Expr, layout: &Layout) -> Option<Shape> {
    shape(e, layout, &mut 100_000, 0)
}

fn shape(e: &Expr, layout: &Layout, remaining: &mut usize, depth: usize) -> Option<Shape> {
    if *remaining == 0 || depth >= 128 {
        return None;
    }
    *remaining -= 1;
    let mut sub = |e| shape(e, layout, remaining, depth + 1);
    match &*e.kind {
        ExprKind::Var(v) => layout.vars.get(v.idx()).cloned(),
        ExprKind::Bool(_) => Some(Shape::Bool),
        ExprKind::Tuple(es) => Some(Shape::Tuple(es.iter().map(&mut sub).collect::<Option<Vec<_>>>()?.into())),
        ExprKind::Field { record, field } => {
            let Shape::Record(fs) = sub(record)? else { return None };
            fs.iter().find(|(name, _)| name.as_str() == &**field).map(|(_, s)| s.clone())
        }
        ExprKind::FnApp { func, .. } => match sub(func)? {
            Shape::Fcn { range, .. } => Some(*range),
            _ => None,
        },
        ExprKind::If { then, els, .. } => Some(sub(then)?.join(&sub(els)?)),
        ExprKind::Except { base, updates } => {
            let Shape::Record(fs) = sub(base)? else { return None };
            let mut fs = fs.to_vec();
            for (path, rhs) in updates {
                let [ExceptKey::Field(field)] = path.as_slice() else { return None };
                let (_, value) = fs.iter_mut().find(|(name, _)| name.as_str() == &**field)?;
                let replacement = sub(rhs)?;
                // New dynamic handles need a lifetime/encoding policy. The
                // existing state-variable handles can still be copied above.
                if super::super::speculate::has_dyn(&replacement) {
                    return None;
                }
                *value = replacement;
            }
            Some(Shape::Record(fs.into()))
        }
        ExprKind::FnConstruct { bounds, body } if bounds.len() == 1 => {
            let BoundVars::Many(ids) = &bounds[0].vars else { return None };
            if ids.len() != 1 {
                return None;
            }
            let ExprKind::Builtin { op: B::Domain, args } = &*bounds[0].set.kind else { return None };
            if args.len() != 1 {
                return None;
            }
            let Shape::Fcn { dom, .. } = sub(&args[0])? else { return None };
            Some(Shape::Fcn { dom, range: Box::new(sub(body)?) })
        }
        _ => None,
    }
}
