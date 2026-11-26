//! Structural result shapes for anonymous VIEW expressions. These follow
//! from the state layout, so rebuilding that layout also rebuilds the VIEW.

use std::sync::Arc;

use tlx_eval::{env::Env, eval::Ctx, InterpModel};
use tlx_layout::{Layout, Shape};
use tlx_sema::{builtins::Builtin as B, hir::*};
use tlx_value::{Sym, Value};

pub(super) fn infer(base: &InterpModel, e: &Expr, layout: &Layout) -> Option<Shape> {
    let s = shape(base, e, layout, &mut 100_000, 0)?;
    (!super::super::speculate::has_dyn(&s)).then_some(s)
}

fn shape(base: &InterpModel, e: &Expr, layout: &Layout, remaining: &mut usize, depth: usize) -> Option<Shape> {
    if *remaining == 0 || depth >= 128 {
        return None;
    }
    *remaining -= 1;
    let mut sub = |e| shape(base, e, layout, remaining, depth + 1);
    match &*e.kind {
        ExprKind::Var(v) => layout.vars.get(v.idx()).cloned(),
        ExprKind::Bool(_) => Some(Shape::Bool),
        ExprKind::Num(n) => i64::try_from(*n).ok().map(|v| Shape::Int { lo: v, hi: v }),
        ExprKind::Str(s) => Some(Shape::Atom(Arc::from(vec![Value::Str(Sym::new(s))]))),
        ExprKind::Const(_) => {
            let v = base.ip.eval(e, &Env::default(), &Ctx::NONE).ok()?.normalize().ok()?;
            Some(Shape::of(&v))
        }
        ExprKind::SetEnum(es) => {
            let mut elem = Shape::Never;
            for item in es {
                elem = elem.join(&sub(item)?);
            }
            Some(Shape::Set { elem: Box::new(elem), max_card: es.len() })
        }
        ExprKind::Record(fs) => {
            let mut pairs: Vec<(Sym, Shape)> = fs.iter().map(|(k, v)| Some((Sym::new(k), sub(v)?))).collect::<Option<_>>()?;
            pairs.sort_by_key(|(k, _)| *k);
            Some(Shape::Record(Arc::from(pairs)))
        }
        ExprKind::Tuple(es) => Some(Shape::Tuple(es.iter().map(&mut sub).collect::<Option<Vec<_>>>()?.into())),
        ExprKind::Field { record, field } => {
            let Shape::Record(fs) = sub(record)? else { return None };
            fs.iter().find(|(name, _)| name.as_str() == &**field).map(|(_, s)| s.clone())
        }
        ExprKind::FnApp { func, .. } => match sub(func)? {
            Shape::Fcn { range, .. } => Some(*range),
            _ => None,
        },
        ExprKind::If { then, els, .. } => {
            let a = sub(then)?;
            let b = sub(els)?;
            match (&a, &b) {
                (Shape::Ref(r), _) if !matches!(b, Shape::Dyn | Shape::Never) => Some(Shape::Ref(r.clone())),
                (_, Shape::Ref(r)) if !matches!(a, Shape::Dyn | Shape::Never) => Some(Shape::Ref(r.clone())),
                _ => Some(a.join(&b)),
            }
        }
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
            let Shape::Fcn { dom, witness, key_variants, .. } = sub(&args[0])? else { return None };
            if witness == tlx_layout::FcnWitness::Dynamic || !key_variants.is_empty() {
                return None;
            }
            let range = sub(body)?;
            if super::super::speculate::has_dyn(&range) {
                return None;
            }
            Some(Shape::Fcn { dom, range: Box::new(range), witness, key_variants: Arc::from([]) })
        }
        _ => None,
    }
}
