//! Fixed container shapes and source paths for numeric and retained leaves.
use super::{Atom, Context, Expr, ExprKind, Family, LocalId, OrderedShape, VarId};
use crate::{
    hir::{BoundVars, ExceptKey},
    visit,
};
use std::collections::BTreeMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct Path {
    pub var: VarId,
    pub keys: Vec<Atom>,
}
impl Path {
    pub fn child(&self, key: Atom) -> Self {
        let mut p = self.clone();
        p.keys.push(key);
        p
    }
}
#[derive(Clone)]
pub(super) enum Schema {
    History,
    Plain,
    Number(usize),
    Record(BTreeMap<String, Schema>),
    Tuple(Vec<Schema>),
    Function(BTreeMap<Atom, Schema>),
}
#[derive(Clone, Debug)]
pub(super) struct Slot {
    pub path: Path,
    pub family: usize,
    pub index: usize,
}

pub(super) fn colored(s: &OrderedShape) -> bool {
    s.family.is_some() || s.fields.values().any(colored) || [&s.key, &s.value, &s.element].into_iter().flatten().any(|s| colored(s))
}

impl Context<'_> {
    pub(super) fn schema(&mut self, expr: &Expr, shape: &OrderedShape) -> Option<Schema> {
        if !colored(shape) {
            return Some(Schema::Plain);
        }
        if let Some(f) = shape.family {
            return Some(Schema::Number(f));
        }
        if shape.key.as_deref().is_some_and(colored) || shape.element.as_deref().is_some_and(colored) {
            return None;
        }
        match &*expr.kind {
            ExprKind::Record(fs) if shape.value.is_none() => {
                let mut fields = BTreeMap::new();
                for (name, e) in fs {
                    let schema = match shape.fields.get(name) {
                        Some(s) => self.schema(e, s)?,
                        None => Schema::Plain,
                    };
                    fields.insert(name.to_string(), schema);
                }
                if shape.fields.keys().any(|k| !fields.contains_key(k.as_ref())) {
                    return None;
                }
                Some(Schema::Record(fields))
            }
            ExprKind::Tuple(es) if shape.fields.is_empty() => {
                let value = shape.value.as_deref()?;
                Some(Schema::Tuple(es.iter().map(|e| self.schema(e, value)).collect::<Option<_>>()?))
            }
            ExprKind::FnConstruct { bounds, body } if shape.fields.is_empty() => {
                let [bound] = bounds.as_slice() else { return None };
                let BoundVars::Many(ids) = &bound.vars else { return None };
                let [id] = ids.as_slice() else { return None };
                let keys = self.domains.exact_set(&bound.set)?;
                if keys.len() > 256 {
                    return None;
                }
                let mut values = BTreeMap::new();
                for key in keys {
                    let arg = self.atom_expr(&key, expr.span)?;
                    let body = substitute(body, *id, &arg);
                    values.insert(key, self.schema(&body, shape.value.as_deref()?)?);
                }
                Some(Schema::Function(values))
            }
            _ => None,
        }
    }

    /// Resolve one structural selection, preserving EXCEPT order and @ lowering.
    pub(super) fn select(&mut self, e: &Expr, keys: &[Atom]) -> Option<Expr> {
        let Some((key, rest)) = keys.split_first() else { return Some(e.clone()) };
        match &*e.kind {
            ExprKind::Record(fs) => {
                let Atom::Str(field) = key else { return None };
                self.select(&fs.iter().find(|(f, _)| f == field)?.1, rest)
            }
            ExprKind::Tuple(es) => {
                let Atom::Num(i) = key else { return None };
                self.select(es.get(usize::try_from(i.checked_sub(1)?).ok()?)?, rest)
            }
            ExprKind::FnConstruct { bounds, body } => {
                let [bound] = bounds.as_slice() else { return None };
                let BoundVars::Many(ids) = &bound.vars else { return None };
                let [id] = ids.as_slice() else { return None };
                if !self.domains.exact_set(&bound.set)?.contains(key) {
                    return None;
                }
                let arg = self.atom_expr(key, e.span)?;
                self.select(&substitute(body, *id, &arg), rest)
            }
            ExprKind::Except { base, updates } => {
                let mut value = self.select(base, keys)?;
                for (path, rhs) in updates {
                    let path = path
                        .iter()
                        .map(|k| match k {
                            ExceptKey::Field(f) => Some(Atom::Str(f.clone())),
                            ExceptKey::Index(args) => match args.as_slice() {
                                [e] => self.atom(e),
                                _ => None,
                            },
                        })
                        .collect::<Option<Vec<_>>>()?;
                    if keys.starts_with(&path) {
                        value = self.select(rhs, &keys[path.len()..])?;
                    } else if path.starts_with(keys) {
                        let remaining = path[keys.len()..]
                            .iter()
                            .map(|a| Some(ExceptKey::Index(vec![self.atom_expr(a, e.span)?])))
                            .collect::<Option<_>>()?;
                        value = Expr::new(ExprKind::Except { base: value, updates: vec![(remaining, rhs.clone())] }, e.span);
                    }
                }
                Some(value)
            }
            ExprKind::If { cond, then, els } => {
                Some(Expr::new(ExprKind::If { cond: cond.clone(), then: self.select(then, keys)?, els: self.select(els, keys)? }, e.span))
            }
            _ => {
                // An old structural read must have the exact inferred shape.
                let path = self.path(e)?;
                let schema = self.at_path(&path)?;
                schema.child(key)?;
                let arg = self.atom_expr(key, e.span)?;
                let selected = Expr::new(ExprKind::FnApp { func: e.clone(), args: vec![arg] }, e.span);
                // The recursive check resolves the same path before descending.
                self.select(&selected, rest)
            }
        }
    }

    pub(super) fn path(&self, e: &Expr) -> Option<Path> {
        match &*e.kind {
            ExprKind::Var(v) => Some(Path { var: *v, keys: vec![] }),
            ExprKind::Field { record, field } => Some(self.path(record)?.child(Atom::Str(field.clone()))),
            ExprKind::FnApp { func, args } => {
                let [key] = args.as_slice() else { return None };
                Some(self.path(func)?.child(self.atom(key)?))
            }
            _ => None,
        }
    }
    pub(super) fn at_path(&self, path: &Path) -> Option<&Schema> {
        let mut schema = self.schemas.get(path.var.idx())?;
        for key in &path.keys {
            schema = schema.child(key)?;
        }
        Some(schema)
    }

    /// Container domains/shapes are part of the source representation invariant.
    pub(super) fn shape_matches(&mut self, e: &Expr, schema: &Schema) -> Option<()> {
        match schema {
            Schema::History => None,
            Schema::Plain | Schema::Number(_) => Some(()),
            _ => {
                if let ExprKind::If { then, els, .. } = &*e.kind {
                    self.shape_matches(then, schema)?;
                    return self.shape_matches(els, schema);
                }
                if let ExprKind::Except { base, updates } = &*e.kind {
                    self.shape_matches(base, schema)?;
                    for (keys, value) in updates {
                        let mut target = schema;
                        for key in keys {
                            let key = match key {
                                ExceptKey::Field(f) => Atom::Str(f.clone()),
                                ExceptKey::Index(es) => {
                                    let [e] = es.as_slice() else { return None };
                                    self.atom(e)?
                                }
                            };
                            target = target.child(&key)?;
                        }
                        self.shape_matches(value, target)?;
                    }
                    return Some(());
                }
                match (schema, &*e.kind) {
                    (Schema::Record(fs), ExprKind::Record(es)) if fs.len() == es.len() => {
                        for (name, sub) in fs {
                            self.shape_matches(&es.iter().find(|(n, _)| n.as_ref() == name)?.1, sub)?;
                        }
                        Some(())
                    }
                    (Schema::Tuple(ss), ExprKind::Tuple(es)) if ss.len() == es.len() => {
                        for (s, e) in ss.iter().zip(es) {
                            self.shape_matches(e, s)?;
                        }
                        Some(())
                    }
                    (Schema::Function(fs), ExprKind::FnConstruct { bounds, body }) => {
                        let [bound] = bounds.as_slice() else { return None };
                        let BoundVars::Many(ids) = &bound.vars else { return None };
                        let [id] = ids.as_slice() else { return None };
                        if !self.domains.exact_set(&bound.set)?.iter().eq(fs.keys()) {
                            return None;
                        }
                        for (key, s) in fs {
                            let arg = self.atom_expr(key, e.span)?;
                            self.shape_matches(&substitute(body, *id, &arg), s)?;
                        }
                        Some(())
                    }
                    _ => self.at_path(&self.path(e)?).filter(|s| s.same_shape(schema)).map(|_| ()),
                }
            }
        }
    }
}

impl Schema {
    fn child(&self, key: &Atom) -> Option<&Self> {
        match (self, key) {
            (Self::Record(fs), Atom::Str(k)) => fs.get(k.as_ref()),
            (Self::Tuple(es), Atom::Num(i)) => es.get(usize::try_from(i.checked_sub(1)?).ok()?),
            (Self::Function(fs), key) => fs.get(key),
            _ => None,
        }
    }
    fn same_shape(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Plain, Self::Plain) => true,
            (Self::Number(a), Self::Number(b)) => a == b,
            (Self::Record(a), Self::Record(b)) => {
                a.len() == b.len() && a.iter().zip(b).all(|((ak, av), (bk, bv))| ak == bk && av.same_shape(bv))
            }
            (Self::Tuple(a), Self::Tuple(b)) => a.len() == b.len() && a.iter().zip(b).all(|(a, b)| a.same_shape(b)),
            (Self::Function(a), Self::Function(b)) => {
                a.len() == b.len() && a.iter().zip(b).all(|((ak, av), (bk, bv))| ak == bk && av.same_shape(bv))
            }
            _ => false,
        }
    }
    pub fn leaves(&self, path: Path, numeric: &mut Vec<Slot>, plain: &mut Vec<Path>, families: &[Family]) {
        match self {
            Self::History => {}
            Self::Plain => plain.push(path),
            Self::Number(f) => {
                if families[*f].variable == path.var && path.keys.is_empty() {
                    return;
                }
                let index = numeric.iter().filter(|s| s.family == *f).count();
                numeric.push(Slot { path, family: *f, index });
            }
            Self::Record(fs) => {
                for (name, s) in fs {
                    s.leaves(path.child(Atom::Str(name.as_str().into())), numeric, plain, families);
                }
            }
            Self::Tuple(es) => {
                for (i, s) in es.iter().enumerate() {
                    s.leaves(path.child(Atom::Num(i as i128 + 1)), numeric, plain, families);
                }
            }
            Self::Function(fs) => {
                for (key, s) in fs {
                    s.leaves(path.child(key.clone()), numeric, plain, families);
                }
            }
        }
    }
}

pub(super) fn substitute(e: &Expr, id: LocalId, arg: &Expr) -> Expr {
    if matches!(&*e.kind,ExprKind::Local(i) if *i==id) {
        return arg.clone();
    }
    let mut out = e.clone();
    visit::children_mut(&mut out, &mut |e| *e = substitute(e, id, arg));
    out
}
