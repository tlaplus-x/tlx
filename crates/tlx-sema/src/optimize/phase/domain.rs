//! Forward may-value domains, inferred from Init and every Next alternative.
//! Unknown operations widen to Top. Checked properties are never assumptions.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use tlx_front::cfg::{CfgValue, Config, ConstBinding};

use crate::{builtins::Builtin as B, hir::*, Program};

use super::{binding, Branch};

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(super) enum Atom {
    Num(i128),
    Str(Arc<str>),
    Bool(bool),
    Model(Arc<str>),
}

impl Atom {
    pub fn literal(e: &Expr) -> Option<Self> {
        match &*e.kind {
            ExprKind::Num(n) if i32::try_from(*n).is_ok() => Some(Self::Num(*n)),
            ExprKind::Str(s) => Some(Self::Str(s.clone())),
            ExprKind::Bool(b) => Some(Self::Bool(*b)),
            _ => None,
        }
    }

    pub fn expr(&self, span: Span) -> Option<Expr> {
        Some(Expr::new(
            match self {
                Self::Num(n) => ExprKind::Num(*n),
                Self::Str(s) => ExprKind::Str(s.clone()),
                Self::Bool(b) => ExprKind::Bool(*b),
                Self::Model(_) => return None,
            },
            span,
        ))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum Domain {
    Bottom,
    Top,
    Atoms(BTreeSet<Atom>),
    // A lower bound on successfully evaluated integer values. Arithmetic
    // errors remain observable reads; this is only a type/value analysis.
    Integer(i128),
    Set(Box<Domain>),
    Seq(Box<Domain>),
    Record(BTreeMap<Arc<str>, Domain>),
    Function(BTreeSet<Atom>, Box<Domain>),
    Mapping(Box<Domain>),
}

impl Domain {
    pub fn join(&self, other: &Self) -> Self {
        match (self, other) {
            (Self::Bottom, x) | (x, Self::Bottom) => x.clone(),
            (Self::Atoms(a), Self::Atoms(b)) => {
                let values: BTreeSet<_> = a.union(b).cloned().collect();
                if values.len() <= 64 {
                    Self::Atoms(values)
                } else {
                    Self::Top
                }
            }
            (Self::Integer(a), b) | (b, Self::Integer(a)) => b.integer_min().map_or(Self::Top, |b| Self::Integer((*a).min(b))),
            (Self::Set(a), Self::Set(b)) => Self::Set(Box::new(a.join(b))),
            (Self::Seq(a), Self::Seq(b)) => Self::Seq(Box::new(a.join(b))),
            (Self::Record(a), Self::Record(b)) if a.keys().eq(b.keys()) => {
                Self::Record(a.iter().map(|(k, v)| (k.clone(), v.join(&b[k]))).collect())
            }
            (Self::Function(a, x), Self::Function(b, y)) if a == b => Self::Function(a.clone(), Box::new(x.join(y))),
            (a, b) if a.range().is_some() && b.range().is_some() => Self::Mapping(Box::new(a.range().unwrap().join(b.range().unwrap()))),
            _ => Self::Top,
        }
    }

    fn atom(a: Atom) -> Self {
        Self::Atoms(BTreeSet::from([a]))
    }

    pub fn atoms(&self) -> Option<&BTreeSet<Atom>> {
        match self {
            Self::Atoms(a) => Some(a),
            _ => None,
        }
    }

    fn integer_min(&self) -> Option<i128> {
        match self {
            Self::Integer(n) => Some(*n),
            Self::Atoms(values) if !values.is_empty() => {
                values.iter().map(|a| if let Atom::Num(n) = a { Some(*n) } else { None }).collect::<Option<Vec<_>>>()?.into_iter().min()
            }
            _ => None,
        }
    }

    fn range(&self) -> Option<&Self> {
        match self {
            Self::Seq(d) | Self::Function(_, d) | Self::Mapping(d) => Some(d),
            _ => None,
        }
    }
}

pub(super) struct Domains {
    pub vars: Vec<Domain>,
    constants: HashMap<ConstId, Domain>,
}

pub(super) type Locals = HashMap<LocalId, Domain>;

impl Domains {
    pub fn atom_value(&self, e: &Expr) -> Option<Atom> {
        let d = self.value(e, &Locals::new());
        let values = d.atoms()?;
        (values.len() == 1).then(|| values.first().unwrap().clone())
    }

    pub fn atom_expr(&self, a: &Atom, span: Span) -> Option<Expr> {
        if let Some(e) = a.expr(span) {
            return Some(e);
        }
        // Use a configured constant, never invent a model-value literal or
        // depend on its interpreter-specific numeric identity.
        let id = self
            .constants
            .iter()
            .filter_map(|(id, d)| (d.atoms() == Some(&BTreeSet::from([a.clone()]))).then_some(*id))
            .min_by_key(|id| id.idx())?;
        Some(Expr::new(ExprKind::Const(id), span))
    }

    pub fn infer(program: &Program, cfg: &Config, init: &[Branch], next: &[Branch]) -> Option<Self> {
        let mut constants = HashMap::new();
        for (i, c) in program.consts.iter().enumerate() {
            let value = cfg.constants.iter().find_map(|b| match b {
                ConstBinding::Value { name, value, module: None } if name == &*c.name && c.arity == 0 => Some(value),
                _ => None,
            });
            constants.insert(ConstId(i as u32), value.map(config_value).unwrap_or(Domain::Top));
        }
        let mut out = Self { vars: vec![Domain::Bottom; program.vars.len()], constants };
        // Each iteration joins Init and Next images. Equality establishes a
        // post-fixed point; a budget miss discards the candidate analysis.
        for _ in 0..64 {
            let mut values = out.vars.clone();
            for (branches, primed) in [(init, false), (next, true)] {
                for branch in branches {
                    let locals = out.locals(&branch.bounds);
                    for (i, value) in values.iter_mut().enumerate() {
                        let rhs = binding(branch, VarId(i as u32), primed);
                        let image = rhs.as_ref().map(|e| out.value(e, &locals)).unwrap_or(Domain::Top);
                        *value = value.join(&image);
                    }
                }
            }
            if out.vars == values {
                return Some(out);
            }
            out.vars = values;
        }
        None
    }

    pub fn locals(&self, bounds: &[Bound]) -> Locals {
        let mut locals = Locals::new();
        for b in bounds {
            let value = match self.value(&b.set, &locals) {
                Domain::Set(element) => *element,
                _ => Domain::Top,
            };
            for l in b.vars.locals() {
                locals.insert(*l, if matches!(b.vars, BoundVars::Many(_)) { value.clone() } else { Domain::Top });
            }
        }
        locals
    }

    pub fn value(&self, e: &Expr, locals: &Locals) -> Domain {
        self.eval(e, locals, 0)
    }

    fn eval(&self, e: &Expr, locals: &Locals, depth: usize) -> Domain {
        use Domain as D;
        if depth >= 32 {
            return D::Top;
        }
        let val = |e| self.eval(e, locals, depth + 1);
        if let Some(a) = Atom::literal(e) {
            return D::atom(a);
        }
        match &*e.kind {
            ExprKind::Var(v) => self.vars[v.idx()].clone(),
            ExprKind::Const(c) => self.constants.get(c).cloned().unwrap_or(D::Top),
            ExprKind::Local(l) => locals.get(l).cloned().unwrap_or(D::Top),
            ExprKind::SetEnum(es) => D::Set(Box::new(es.iter().fold(D::Bottom, |d, e| d.join(&val(e))))),
            ExprKind::Tuple(es) => D::Seq(Box::new(es.iter().fold(D::Bottom, |d, e| d.join(&val(e))))),
            ExprKind::Record(fs) => D::Record(fs.iter().map(|(k, e)| (k.clone(), val(e))).collect()),
            ExprKind::FnConstruct { bounds, body } if bounds.len() == 1 => {
                let b = &bounds[0];
                let BoundVars::Many(ids) = &b.vars else { return D::Top };
                if ids.len() != 1 {
                    return D::Top;
                }
                let Some(keys) = self.exact_set(&b.set) else { return D::Top };
                let mut scope = locals.clone();
                scope.insert(ids[0], D::Atoms(keys.clone()));
                D::Function(keys, Box::new(self.eval(body, &scope, depth + 1)))
            }
            ExprKind::FnApp { func, .. } => match val(func) {
                // An upper bound on successfully evaluated values. Definedness
                // is a separate liveness obligation, never inferred here.
                D::Function(_, v) | D::Seq(v) | D::Mapping(v) => *v,
                D::Bottom => D::Bottom,
                _ => D::Top,
            },
            ExprKind::Field { record, field } => match val(record) {
                D::Record(fs) => fs.get(field).cloned().unwrap_or(D::Top),
                D::Bottom => D::Bottom,
                _ => D::Top,
            },
            ExprKind::Except { base, updates } => {
                let mut result = val(base);
                for (keys, e) in updates {
                    update(&mut result, keys, &val(e));
                }
                result
            }
            ExprKind::If { then, els, .. } => val(then).join(&val(els)),
            ExprKind::Builtin { op: B::Prime, args } if args.len() == 1 => val(&args[0]),
            ExprKind::Builtin { op, args } => self.builtin(*op, &args.iter().map(val).collect::<Vec<_>>()),
            _ => D::Top,
        }
    }

    fn builtin(&self, op: B, args: &[Domain]) -> Domain {
        use Domain as D;
        // These operators are strict. Bottom denotes no successfully
        // evaluated value, not an unknown value (which is Top).
        if matches!(op, B::Cup | B::Append | B::ColonGt | B::AtAt | B::Neg | B::Plus) && args.iter().any(|d| matches!(d, D::Bottom)) {
            return D::Bottom;
        }
        match (op, args) {
            (B::Cup, [D::Set(a), D::Set(b)]) => D::Set(Box::new(a.join(b))),
            (B::Append, [D::Seq(a), b]) => D::Seq(Box::new(a.join(b))),
            (B::ColonGt, [_, b]) => D::Mapping(Box::new(b.clone())),
            (B::AtAt, [a, b]) => match (a.range(), b.range()) {
                (Some(a), Some(b)) => D::Mapping(Box::new(a.join(b))),
                _ => D::Top,
            },
            (B::Neg, [D::Atoms(a)]) if a.len() == 1 => match a.first() {
                Some(Atom::Num(n)) if i32::try_from(-n).is_ok() => D::atom(Atom::Num(-n)),
                _ => D::Top,
            },
            (B::Plus, [a, b]) => match (a.integer_min(), b.integer_min()) {
                (Some(a), Some(b)) => D::Integer((a + b).clamp(i128::from(i32::MIN), i128::from(i32::MAX))),
                _ => D::Top,
            },
            _ => D::Top,
        }
    }

    /// True only when every possible value belongs to the given structural
    /// type. This proves the observation; it never reads assumed invariants.
    pub fn belongs(&self, value: &Domain, set: &Expr) -> bool {
        if matches!(value, Domain::Bottom) {
            return false;
        }
        match (&*set.kind, value) {
            (ExprKind::Builtin { op: B::Nat, args }, _) if args.is_empty() => value.integer_min().is_some_and(|n| n >= 0),
            (ExprKind::Builtin { op: B::Int, args }, _) if args.is_empty() => value.integer_min().is_some(),
            (ExprKind::Builtin { op: B::Boolean, args }, Domain::Atoms(values)) if args.is_empty() => {
                values.iter().all(|a| matches!(a, Atom::Bool(_)))
            }
            (ExprKind::Builtin { op: B::Cup, args }, _) if args.len() == 2 => {
                // Nat union {-1}, for example, is an integer interval.
                // Restrict this proof to numeric operands; a heterogeneous
                // union may introduce comparison errors during membership.
                self.integer_floor(set).zip(value.integer_min()).is_some_and(|(floor, low)| low >= floor)
                    || value
                        .atoms()
                        .is_some_and(|values| self.exact_set(set).is_some_and(|allowed| compatible(&allowed) && values.is_subset(&allowed)))
            }
            (ExprKind::Builtin { op: B::Seq, args }, Domain::Seq(element)) if args.len() == 1 => {
                self.type_set(&args[0]) && (matches!(**element, Domain::Bottom) || self.belongs(element, &args[0]))
            }
            (ExprKind::FnSet { domain, range }, Domain::Function(keys, element)) => {
                self.exact_set(domain).as_ref() == Some(keys) && self.belongs(element, range)
            }
            (ExprKind::RecordSet(fs), Domain::Record(values)) => {
                fs.len() == values.len()
                    && fs.iter().map(|(k, _)| k).collect::<BTreeSet<_>>().len() == values.len()
                    && fs.iter().all(|(k, s)| values.get(k).is_some_and(|v| self.belongs(v, s)))
            }
            (_, Domain::Atoms(values)) => self.exact_set(set).is_some_and(|allowed| compatible(&allowed) && values.is_subset(&allowed)),
            _ => false,
        }
    }

    // Validate the operand of a structural type even for empty containers.
    // This prevents a vacuous membership proof hiding an invalid type set.
    fn type_set(&self, set: &Expr) -> bool {
        match &*set.kind {
            ExprKind::RecordSet(fs) => {
                fs.iter().map(|(k, _)| k).collect::<BTreeSet<_>>().len() == fs.len() && fs.iter().all(|(_, s)| self.type_set(s))
            }
            ExprKind::Builtin { op: B::Nat | B::Int | B::Boolean, args } => args.is_empty(),
            ExprKind::Builtin { op: B::Cup, .. } => {
                self.integer_floor(set).is_some() || self.exact_set(set).is_some_and(|s| compatible(&s))
            }
            _ => self.exact_set(set).is_some_and(|s| compatible(&s)),
        }
    }

    fn integer_floor(&self, set: &Expr) -> Option<i128> {
        let ExprKind::Builtin { op: B::Cup, args } = &*set.kind else { return None };
        if args.len() != 2 {
            return None;
        }
        for (nat, rest) in [(&args[0], &args[1]), (&args[1], &args[0])] {
            if !matches!(&*nat.kind, ExprKind::Builtin { op: B::Nat, args } if args.is_empty()) {
                continue;
            }
            let extra = self.exact_set(rest)?;
            let mut floor = 0;
            while extra.contains(&Atom::Num(floor - 1)) {
                floor -= 1;
            }
            if extra.iter().all(|a| matches!(a, Atom::Num(_))) {
                return Some(floor);
            }
        }
        None
    }

    // A may-element set is not an exact set: `{x}` does not have every value
    // in x's domain as a member. Fixed function domains need this distinction.
    pub fn exact_set(&self, e: &Expr) -> Option<BTreeSet<Atom>> {
        match &*e.kind {
            ExprKind::Const(c) => match self.constants.get(c)? {
                Domain::Set(d) if matches!(&**d, Domain::Bottom) => Some(BTreeSet::new()),
                Domain::Set(d) => d.atoms().cloned(),
                _ => None,
            },
            ExprKind::SetEnum(es) => es.iter().map(|e| self.atom_value(e)).collect(),
            ExprKind::Builtin { op: B::Cup, args } if args.len() == 2 => {
                let mut a = self.exact_set(&args[0])?;
                a.extend(self.exact_set(&args[1])?);
                Some(a)
            }
            _ => None,
        }
    }
}

fn update(domain: &mut Domain, keys: &[ExceptKey], value: &Domain) {
    let Some((key, rest)) = keys.split_first() else {
        *domain = domain.join(value);
        return;
    };
    match (key, &mut *domain) {
        (ExceptKey::Index(_), Domain::Function(_, element) | Domain::Mapping(element) | Domain::Seq(element)) => {
            update(element, rest, value)
        }
        (ExceptKey::Field(k), Domain::Record(fs)) => {
            if let Some(field) = fs.get_mut(k) {
                update(field, rest, value);
            }
        }
        (_, Domain::Bottom) => {}
        _ => *domain = Domain::Top,
    }
}

fn config_value(v: &CfgValue) -> Domain {
    match v {
        CfgValue::Int(n) if i32::try_from(*n).is_ok() => Domain::atom(Atom::Num(i128::from(*n))),
        CfgValue::Str(s) => Domain::atom(Atom::Str(s.as_str().into())),
        CfgValue::Bool(b) => Domain::atom(Atom::Bool(*b)),
        CfgValue::ModelValue(s) => Domain::atom(Atom::Model(s.as_str().into())),
        CfgValue::Set(es) => Domain::Set(Box::new(es.iter().fold(Domain::Bottom, |d, e| d.join(&config_value(e))))),
        CfgValue::Tuple(es) => Domain::Seq(Box::new(es.iter().fold(Domain::Bottom, |d, e| d.join(&config_value(e))))),
        _ => Domain::Top,
    }
}

// Avoid erasing type errors from heterogeneous comparisons or typed model
// values. Untyped model values can coexist with one ordinary scalar family.
pub(super) fn compatible(values: &BTreeSet<Atom>) -> bool {
    let mut family = None;
    for a in values {
        let f = match a {
            Atom::Num(_) => 0,
            Atom::Str(_) => 1,
            Atom::Bool(_) => 2,
            Atom::Model(s) => {
                if s.as_bytes().get(1) == Some(&b'_') {
                    return false;
                }
                continue;
            }
        };
        if family.is_some_and(|old| old != f) {
            return false;
        }
        family = Some(f);
    }
    true
}
