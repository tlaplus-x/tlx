//! Forward may-value domains, inferred from Init and every Next alternative.
//! Unknown operations widen to Top. Checked properties are never assumptions.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::sync::Arc;

use tlx_front::cfg::{CfgValue, Config};

use crate::{builtins::Builtin as B, hir::*, visit, Program};

use super::{
    sym_norm::{lookup_resolved_root, SymNormalizer},
    Branch,
};

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
    // Distinct record shapes, kept separate so optional fields are not
    // mistaken for fields present in every value. Bounded to eight shapes.
    Records(Vec<BTreeMap<Arc<str>, Domain>>),
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
            (Self::Record(_) | Self::Records(_), Self::Record(_) | Self::Records(_)) => {
                let mut records = self.records().unwrap();
                for other in other.records().unwrap() {
                    if let Some(old) = records.iter_mut().find(|r| r.keys().eq(other.keys())) {
                        for (k, v) in old {
                            *v = v.join(&other[k]);
                        }
                    } else {
                        records.push(other);
                    }
                }
                if records.len() > 8 {
                    return Self::Top;
                }
                records.sort_by(|a, b| a.keys().cmp(b.keys()));
                Self::Records(records)
            }
            (Self::Function(a, x), Self::Function(b, y)) if a == b => Self::Function(a.clone(), Box::new(x.join(y))),
            (a, b) if a.range().is_some() && b.range().is_some() => Self::Mapping(Box::new(a.range().unwrap().join(b.range().unwrap()))),
            _ => Self::Top,
        }
    }

    fn atom(a: Atom) -> Self {
        Self::Atoms(BTreeSet::from([a]))
    }

    fn boolean() -> Self {
        Self::Atoms(BTreeSet::from([Atom::Bool(false), Atom::Bool(true)]))
    }

    pub fn records(&self) -> Option<Vec<BTreeMap<Arc<str>, Domain>>> {
        match self {
            Self::Record(r) => Some(vec![r.clone()]),
            Self::Records(rs) => Some(rs.clone()),
            _ => None,
        }
    }

    // Upper bound on successful reads only; missing fields may still fail.
    fn field(&self, key: &str) -> Self {
        match self {
            Self::Record(fs) => fs.get(key).cloned().unwrap_or(Self::Bottom),
            Self::Records(rs) => rs.iter().filter_map(|fs| fs.get(key)).fold(Self::Bottom, |d, v| d.join(v)),
            Self::Bottom => Self::Bottom,
            _ => Self::Top,
        }
    }

    pub fn atoms(&self) -> Option<&BTreeSet<Atom>> {
        match self {
            Self::Atoms(a) => Some(a),
            _ => None,
        }
    }

    pub(super) fn integer_min(&self) -> Option<i128> {
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
    exact_const_sets: HashMap<ConstId, BTreeSet<Atom>>,
    total_const_atoms: HashMap<ConstId, Atom>,
    fold_vars: Option<HashSet<LocalId>>,
}

pub(super) type Locals = HashMap<LocalId, Domain>;

impl Domains {
    /// Return `Some(atom)` ONLY when `e` is a guaranteed-total constant scalar expression
    /// (never accepting `If`, `Case`, division, state variables, or partial projections).
    pub fn atom_value(&self, e: &Expr) -> Option<Atom> {
        if let Some(a) = Atom::literal(e) {
            return Some(a);
        }
        match &*e.kind {
            ExprKind::Const(c) => self.total_const_atoms.get(c).cloned(),
            ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => self.atom_value(&args[0]),
            ExprKind::Builtin { op: B::Neg, args } if args.len() == 1 => {
                let Atom::Num(n) = self.atom_value(&args[0])? else { return None };
                i32::try_from(-n).ok().map(|k| Atom::Num(i128::from(k)))
            }
            ExprKind::Builtin { op: op @ (B::Plus | B::Minus | B::Mul), args } if args.len() == 2 => {
                let (Atom::Num(a), Atom::Num(b)) = (self.atom_value(&args[0])?, self.atom_value(&args[1])?) else {
                    return None;
                };
                let r = match op {
                    B::Plus => a + b,
                    B::Minus => a - b,
                    B::Mul => a * b,
                    _ => unreachable!(),
                };
                i32::try_from(r).ok().map(|k| Atom::Num(i128::from(k)))
            }
            ExprKind::Builtin { op: B::Cardinality, args } if args.len() == 1 => {
                let s = self.exact_set(&args[0])?;
                atoms_mutually_comparable(&s).then_some(Atom::Num(s.len() as i128))
            }
            _ => None,
        }
    }

    /// Return `Some(atom)` when `e` is guaranteed total in every reachable state and
    /// evaluates to a unique scalar `Atom` (accepting `aliases` locals, `Var`, present
    /// `Domain::Record` fields, and in-domain `Domain::Function` lookups, while rejecting
    /// conditionals, `Mapping`/`Seq` indexing, division, and partial operators).
    pub fn state_atom_value(&self, e: &Expr, aliases: &BTreeMap<LocalId, Atom>) -> Option<Atom> {
        if let Some(a) = self.atom_value(e) {
            return Some(a);
        }
        if let ExprKind::Local(id) = &*e.kind {
            if let Some(a) = aliases.get(id) {
                return Some(a.clone());
            }
        }
        match &*e.kind {
            ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => self.state_atom_value(&args[0], aliases),
            ExprKind::Builtin { op: B::Neg, args } if args.len() == 1 => {
                let Atom::Num(n) = self.state_atom_value(&args[0], aliases)? else { return None };
                i32::try_from(-n).ok().map(|k| Atom::Num(i128::from(k)))
            }
            ExprKind::Builtin { op: op @ (B::Plus | B::Minus | B::Mul), args } if args.len() == 2 => {
                let (Atom::Num(a), Atom::Num(b)) = (self.state_atom_value(&args[0], aliases)?, self.state_atom_value(&args[1], aliases)?)
                else {
                    return None;
                };
                let r = match op {
                    B::Plus => a + b,
                    B::Minus => a - b,
                    B::Mul => a * b,
                    _ => unreachable!(),
                };
                i32::try_from(r).ok().map(|k| Atom::Num(i128::from(k)))
            }
            _ => {
                let dom = self.total_state_domain(e, aliases)?;
                dom.atoms().filter(|s| s.len() == 1).and_then(|s| s.first()).cloned()
            }
        }
    }

    fn total_state_domain(&self, e: &Expr, aliases: &BTreeMap<LocalId, Atom>) -> Option<Domain> {
        match &*e.kind {
            ExprKind::Var(v) => self.vars.get(v.idx()).cloned(),
            ExprKind::Const(c) => self.constants.get(c).cloned(),
            ExprKind::Field { record, field } => match self.total_state_domain(record, aliases)? {
                Domain::Record(fs) => fs.get(field).cloned(),
                _ => None,
            },
            ExprKind::FnApp { func, args } if args.len() == 1 => match self.total_state_domain(func, aliases)? {
                Domain::Function(dom_keys, val_dom) => {
                    let key = self.state_atom_value(&args[0], aliases)?;
                    dom_keys.contains(&key).then_some(*val_dom)
                }
                _ => None,
            },
            ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => self.total_state_domain(&args[0], aliases),
            _ => None,
        }
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
        Self::infer_inner(program, cfg, init, next, None)
    }

    pub fn infer_with_folds(
        program: &Program,
        cfg: &Config,
        init: &[Branch],
        next: &[Branch],
        fold_vars: &HashMap<LocalId, Option<Expr>>,
    ) -> Option<Self> {
        Self::infer_inner(program, cfg, init, next, Some(fold_vars.keys().copied().collect()))
    }

    fn infer_inner(program: &Program, cfg: &Config, init: &[Branch], next: &[Branch], fold_vars: Option<HashSet<LocalId>>) -> Option<Self> {
        let mut constants = HashMap::new();
        let mut exact_const_sets = HashMap::new();
        let mut total_const_atoms = HashMap::new();
        for (i, c) in program.consts.iter().enumerate() {
            let id = ConstId(i as u32);
            let value = (c.arity == 0).then(|| cfg.last_constant_value(&c.name)).flatten();
            if let Some(v) = value {
                let dom = config_value(v);
                if let Some(atoms) = dom.atoms().filter(|s| s.len() == 1) {
                    total_const_atoms.insert(id, atoms.first().unwrap().clone());
                }
                constants.insert(id, dom);
                if let Some(exact) = config_exact_set(v) {
                    exact_const_sets.insert(id, exact);
                }
            } else {
                constants.insert(id, Domain::Top);
            }
        }
        let allow_reversed = fold_vars.is_none();
        let mut out = Self { vars: vec![Domain::Bottom; program.vars.len()], constants, exact_const_sets, total_const_atoms, fold_vars };
        out.resolve_const_substs(program, cfg);
        // Each iteration joins Init and Next images. Equality establishes a
        // post-fixed point; a budget miss discards the candidate analysis.
        for _ in 0..64 {
            let mut values = out.vars.clone();
            for (branches, primed) in [(init, false), (next, true)] {
                for branch in branches {
                    let locals = out.locals(&branch.bounds);
                    let binds = super::BranchBindings::new(branch, primed);
                    for (i, value) in values.iter_mut().enumerate() {
                        let var = VarId(i as u32);
                        let rhs_opt = if allow_reversed { binds.get_or_reversed(var) } else { binds.get(var) };
                        let image = if let Some(rhs) = rhs_opt {
                            out.value(&rhs, &locals)
                        } else {
                            out.membership_domain(branch, var, primed, &locals)
                        };
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

    // Resolve `CONSTANT C <- Def` bindings for pure, zero-argument constant
    // definitions so they do not unnecessarily widen to `Top`.
    // Keep exact-set evidence separate from overapproximated may-value domains.
    fn resolve_const_substs(&mut self, program: &Program, cfg: &Config) {
        let passes = program.consts.len().min(16);
        for _ in 0..passes {
            let mut changed = false;
            for (i, c) in program.consts.iter().enumerate() {
                if c.arity != 0 {
                    continue;
                }
                let id = ConstId(i as u32);
                let Some(target) = cfg.last_constant_subst(&c.name) else {
                    continue;
                };
                let (resolved, exact, atom) = match lookup_resolved_root(program, target) {
                    Some(RootSymbol::Const(other)) => (
                        self.constants.get(&other).cloned().unwrap_or(Domain::Top),
                        self.exact_const_sets.get(&other).cloned(),
                        self.total_const_atoms.get(&other).cloned(),
                    ),
                    Some(RootSymbol::Def(def_id)) if program.defs[def_id.idx()].params.is_empty() => {
                        let call = Expr::new(ExprKind::Apply { op: OpRef::Def(def_id), args: vec![] }, program.defs[def_id.idx()].span);
                        let mut norm = SymNormalizer::with_config(program, cfg);
                        match norm.normalize(&call) {
                            Some(expr) if is_const_only(&expr) => {
                                let atom = self.atom_value(&expr);
                                let exact = self.exact_set(&expr);
                                let dom = if is_total_const_expr(self, &expr) { self.eval(&expr, &Locals::new(), 0) } else { Domain::Top };
                                (dom, exact, atom)
                            }
                            _ => (Domain::Top, None, None),
                        }
                    }
                    _ => (Domain::Top, None, None),
                };
                if !matches!(resolved, Domain::Top) && self.constants.get(&id) != Some(&resolved) {
                    self.constants.insert(id, resolved);
                    changed = true;
                }
                if let Some(exact) = exact {
                    if self.exact_const_sets.get(&id) != Some(&exact) {
                        self.exact_const_sets.insert(id, exact);
                        changed = true;
                    }
                }
                if let Some(atom) = atom {
                    if self.total_const_atoms.get(&id) != Some(&atom) {
                        self.total_const_atoms.insert(id, atom);
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
    }

    pub fn locals(&self, bounds: &[Bound]) -> Locals {
        let mut locals = Locals::new();
        for b in bounds {
            self.bind_bound(b, &mut locals, 0);
        }
        locals
    }

    fn bind_bound(&self, b: &Bound, locals: &mut Locals, depth: usize) {
        match &b.vars {
            BoundVars::Many(ids) => {
                let value = self.element_domain(&b.set, locals, depth + 1);
                for l in ids {
                    locals.insert(*l, value.clone());
                }
            }
            BoundVars::Tuple(ids) => {
                if let Some(parts) = self.tuple_component_domains(&b.set, ids.len(), locals, depth + 1) {
                    for (l, dom) in ids.iter().zip(parts) {
                        locals.insert(*l, dom);
                    }
                } else {
                    for l in ids {
                        locals.insert(*l, Domain::Top);
                    }
                }
            }
        }
    }

    fn tuple_component_domains(&self, set: &Expr, arity: usize, locals: &Locals, depth: usize) -> Option<Vec<Domain>> {
        if depth >= 32 {
            return None;
        }
        match &*set.kind {
            ExprKind::Builtin { op: B::Times, args } if args.len() == arity => {
                Some(args.iter().map(|a| self.element_domain(a, locals, depth + 1)).collect())
            }
            ExprKind::SetEnum(es) if !es.is_empty() => {
                let mut acc = vec![Domain::Bottom; arity];
                for e in es {
                    let ExprKind::Tuple(ts) = &*e.kind else { return None };
                    if ts.len() != arity {
                        return None;
                    }
                    for (slot, item) in acc.iter_mut().zip(ts.iter()) {
                        *slot = slot.join(&self.eval(item, locals, depth + 1));
                    }
                }
                Some(acc)
            }
            ExprKind::SetMap { expr, bounds } => {
                let ExprKind::Tuple(ts) = &*expr.kind else { return None };
                if ts.len() != arity {
                    return None;
                }
                let mut scope = locals.clone();
                for b in bounds {
                    self.bind_bound(b, &mut scope, depth + 1);
                }
                Some(ts.iter().map(|item| self.eval(item, &scope, depth + 1)).collect())
            }
            ExprKind::SetFilter { bound, .. } => self.tuple_component_domains(&bound.set, arity, locals, depth + 1),
            ExprKind::Builtin { op: B::SetMinus, args } if args.len() == 2 => {
                self.tuple_component_domains(&args[0], arity, locals, depth + 1)
            }
            ExprKind::Builtin { op: B::Cup, args } if args.len() == 2 => {
                let a = self.tuple_component_domains(&args[0], arity, locals, depth + 1)?;
                let b = self.tuple_component_domains(&args[1], arity, locals, depth + 1)?;
                Some(a.into_iter().zip(b).map(|(x, y)| x.join(&y)).collect())
            }
            _ => match self.element_domain(set, locals, depth + 1) {
                Domain::Seq(elem) => Some(vec![*elem; arity]),
                Domain::Bottom => Some(vec![Domain::Bottom; arity]),
                _ => None,
            },
        }
    }

    fn membership_domain(&self, branch: &Branch, v: VarId, primed: bool, locals: &Locals) -> Domain {
        for e in &branch.terms {
            if let ExprKind::Builtin { op, args } = &*e.kind {
                if args.len() == 2 && super::variable(&args[0], primed) == Some(v) {
                    let dom = match op {
                        B::In => self.element_domain(&args[1], locals, 0),
                        B::SubsetEq => Domain::Set(Box::new(self.element_domain(&args[1], locals, 0))),
                        _ => continue,
                    };
                    if !matches!(dom, Domain::Top) {
                        return dom;
                    }
                }
            }
        }
        Domain::Top
    }

    pub fn element_domain(&self, set: &Expr, locals: &Locals, depth: usize) -> Domain {
        use Domain as D;
        if depth >= 32 {
            return D::Top;
        }
        match &*set.kind {
            ExprKind::Const(c) => match self.constants.get(c) {
                Some(D::Set(element)) => (**element).clone(),
                _ => D::Top,
            },
            ExprKind::SetEnum(es) => es.iter().fold(D::Bottom, |d, e| d.join(&self.eval(e, locals, depth + 1))),
            ExprKind::SetFilter { bound, .. } => self.element_domain(&bound.set, locals, depth + 1),
            ExprKind::SetMap { expr, bounds } => {
                let mut scope = locals.clone();
                for b in bounds {
                    self.bind_bound(b, &mut scope, depth + 1);
                }
                self.eval(expr, &scope, depth + 1)
            }
            ExprKind::RecordSet(fs) => D::Record(fs.iter().map(|(k, s)| (k.clone(), self.element_domain(s, locals, depth + 1))).collect()),
            ExprKind::FnSet { domain, range } => {
                let elem = Box::new(self.element_domain(range, locals, depth + 1));
                if let Some(ks) = self.exact_set(domain) {
                    D::Function(ks, elem)
                } else {
                    D::Mapping(elem)
                }
            }
            ExprKind::If { then, els, .. } => {
                self.element_domain(then, locals, depth + 1).join(&self.element_domain(els, locals, depth + 1))
            }
            ExprKind::Case { arms, other } => {
                let mut out = arms.iter().fold(D::Bottom, |d, (_, e)| d.join(&self.element_domain(e, locals, depth + 1)));
                if let Some(e) = other {
                    out = out.join(&self.element_domain(e, locals, depth + 1));
                }
                out
            }
            ExprKind::Builtin { op, args } => match (op, args.as_slice()) {
                (B::Boolean, []) => D::boolean(),
                (B::Nat, []) => D::Integer(0),
                (B::Int, []) => D::Integer(i128::from(i32::MIN)),
                (B::Cup, [a, b]) => self.element_domain(a, locals, depth + 1).join(&self.element_domain(b, locals, depth + 1)),
                (B::Cap, [a, b]) => meet_domain(self.element_domain(a, locals, depth + 1), self.element_domain(b, locals, depth + 1)),
                (B::SetMinus, [a, _]) => self.element_domain(a, locals, depth + 1),
                (B::Subset, [s]) => D::Set(Box::new(self.element_domain(s, locals, depth + 1))),
                (B::Union, [s]) => match self.element_domain(s, locals, depth + 1) {
                    D::Set(inner) => *inner,
                    D::Bottom => D::Bottom,
                    _ => D::Top,
                },
                (B::Seq, [s]) => D::Seq(Box::new(self.element_domain(s, locals, depth + 1))),
                (B::Times, args) if !args.is_empty() => {
                    D::Seq(Box::new(args.iter().fold(D::Bottom, |d, a| d.join(&self.element_domain(a, locals, depth + 1)))))
                }
                (B::Domain, [f]) => match self.eval(f, locals, depth + 1) {
                    D::Function(ks, _) => {
                        if ks.is_empty() {
                            D::Bottom
                        } else {
                            D::Atoms(ks)
                        }
                    }
                    D::Seq(_) => D::Integer(1),
                    D::Record(fs) => field_names_domain(&fs),
                    D::Records(rs) => rs.iter().fold(D::Bottom, |d, fs| d.join(&field_names_domain(fs))),
                    D::Bottom => D::Bottom,
                    _ => D::Top,
                },
                (B::DotDot, [lo, hi]) => {
                    let lo_d = self.eval(lo, locals, depth + 1);
                    let hi_d = self.eval(hi, locals, depth + 1);
                    if let (Some(Atom::Num(a)), Some(Atom::Num(b))) = (
                        lo_d.atoms().filter(|s| s.len() == 1).and_then(|s| s.first()),
                        hi_d.atoms().filter(|s| s.len() == 1).and_then(|s| s.first()),
                    ) {
                        if *b < *a {
                            return D::Bottom;
                        }
                        if *b - *a <= 32 {
                            return D::Atoms((*a..=*b).map(Atom::Num).collect());
                        }
                    }
                    lo_d.integer_min().map_or(D::Top, D::Integer)
                }
                _ => match self.eval(set, locals, depth + 1) {
                    D::Set(element) => *element,
                    D::Bottom => D::Bottom,
                    _ => D::Top,
                },
            },
            _ => match self.eval(set, locals, depth + 1) {
                D::Set(element) => *element,
                D::Bottom => D::Bottom,
                _ => D::Top,
            },
        }
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
            ExprKind::And(_) | ExprKind::Or(_) | ExprKind::Quant { .. } => D::boolean(),
            ExprKind::SetEnum(es) => D::Set(Box::new(es.iter().fold(D::Bottom, |d, e| d.join(&val(e))))),
            // Successful filtering only removes members; predicate definedness
            // is handled separately, as for other may-value domains.
            ExprKind::SetFilter { bound, .. } => match val(&bound.set) {
                D::Bottom => D::Bottom,
                D::Set(elem) => D::Set(elem),
                _ => D::Set(Box::new(self.element_domain(&bound.set, locals, depth + 1))),
            },
            ExprKind::SetMap { .. } | ExprKind::RecordSet(_) | ExprKind::FnSet { .. } => {
                D::Set(Box::new(self.element_domain(e, locals, depth + 1)))
            }
            ExprKind::Choose { vars: BoundVars::Many(ids), set: Some(s), .. } if ids.len() == 1 => match &self.fold_vars {
                Some(fvars) if fvars.contains(&ids[0]) => D::Integer(i128::from(i32::MIN)),
                Some(_) => self.element_domain(s, locals, depth + 1),
                None => D::Top,
            },
            ExprKind::Tuple(es) => D::Seq(Box::new(es.iter().fold(D::Bottom, |d, e| d.join(&val(e))))),
            ExprKind::Record(fs) => D::Record(fs.iter().map(|(k, e)| (k.clone(), val(e))).collect()),
            ExprKind::FnConstruct { bounds, body } => {
                if bounds.len() == 1 {
                    let b = &bounds[0];
                    if let BoundVars::Many(ids) = &b.vars {
                        if ids.len() == 1 {
                            if let Some(keys) = self.exact_set(&b.set) {
                                let mut scope = locals.clone();
                                scope.insert(ids[0], if keys.is_empty() { D::Bottom } else { D::Atoms(keys.clone()) });
                                return D::Function(keys, Box::new(self.eval(body, &scope, depth + 1)));
                            }
                        }
                    }
                }
                if bounds.iter().any(|b| matches!(val(&b.set), D::Bottom)) {
                    return D::Bottom;
                }
                let mut scope = locals.clone();
                for b in bounds {
                    self.bind_bound(b, &mut scope, depth + 1);
                }
                D::Mapping(Box::new(self.eval(body, &scope, depth + 1)))
            }
            ExprKind::FnApp { func, .. } => match val(func) {
                // An upper bound on successfully evaluated values. Definedness
                // is a separate liveness obligation, never inferred here.
                D::Function(_, v) | D::Seq(v) | D::Mapping(v) => *v,
                D::Bottom => D::Bottom,
                _ => D::Top,
            },
            ExprKind::Field { record, field } => val(record).field(field),
            ExprKind::Except { base, updates } => {
                let mut result = val(base);
                for (keys, e) in updates {
                    update(&mut result, keys, &val(e));
                }
                result
            }
            ExprKind::If { then, els, .. } => val(then).join(&val(els)),
            ExprKind::Case { arms, other } => {
                let mut out = arms.iter().fold(D::Bottom, |d, (_, e)| d.join(&val(e)));
                if let Some(e) = other {
                    out = out.join(&val(e));
                }
                out
            }
            ExprKind::Builtin { op: B::Prime, args } if args.len() == 1 => val(&args[0]),
            ExprKind::Builtin { op: B::Domain, args } if args.len() == 1 => match val(&args[0]) {
                D::Bottom => D::Bottom,
                _ => D::Set(Box::new(self.element_domain(e, locals, depth + 1))),
            },
            ExprKind::Builtin { op: B::Subset | B::Seq | B::Union, args } if args.len() == 1 => match val(&args[0]) {
                D::Bottom => D::Bottom,
                _ => D::Set(Box::new(self.element_domain(e, locals, depth + 1))),
            },
            ExprKind::Builtin { op: B::Boolean | B::Nat | B::Int | B::DotDot | B::Times, .. } => {
                D::Set(Box::new(self.element_domain(e, locals, depth + 1)))
            }
            ExprKind::Builtin { op, args } => self.builtin(*op, &args.iter().map(val).collect::<Vec<_>>()),
            _ => D::Top,
        }
    }

    fn builtin(&self, op: B, args: &[Domain]) -> Domain {
        use Domain as D;
        // These operators are strict. Bottom denotes no successfully
        // evaluated value, not an unknown value (which is Top).
        if matches!(
            op,
            B::Cup
                | B::Cap
                | B::SetMinus
                | B::Len
                | B::Cardinality
                | B::Append
                | B::Concat
                | B::Head
                | B::Tail
                | B::SubSeq
                | B::ColonGt
                | B::AtAt
                | B::Neg
                | B::Plus
                | B::Minus
                | B::Mul
                | B::Div
                | B::Mod
        ) && args.iter().any(|d| matches!(d, D::Bottom))
        {
            return D::Bottom;
        }
        match (op, args) {
            (
                B::Eq
                | B::Neq
                | B::In
                | B::NotIn
                | B::SubsetEq
                | B::Not
                | B::Implies
                | B::Equiv
                | B::Lt
                | B::Gt
                | B::Le
                | B::Ge
                | B::Unchanged
                | B::IsFiniteSet,
                _,
            ) => D::boolean(),
            (B::Len, [D::Seq(_)]) | (B::Cardinality, [D::Set(_)]) => D::Integer(0),
            (B::Cup, [D::Set(a), D::Set(b)]) => D::Set(Box::new(a.join(b))),
            (B::Cap, [D::Set(a), D::Set(b)]) => D::Set(Box::new(meet_domain((**a).clone(), (**b).clone()))),
            (B::SetMinus, [D::Set(a), D::Set(_)]) => D::Set(a.clone()),
            (B::Append, [D::Seq(a), b]) => D::Seq(Box::new(a.join(b))),
            (B::Concat, [D::Seq(a), D::Seq(b)]) => D::Seq(Box::new(a.join(b))),
            (B::Head, [D::Seq(a)]) => (**a).clone(),
            (B::Tail, [D::Seq(a)]) | (B::SubSeq, [D::Seq(a), _, _]) => D::Seq(a.clone()),
            (B::ColonGt, [D::Atoms(ks), b]) if ks.len() == 1 => D::Function(ks.clone(), Box::new(b.clone())),
            (B::ColonGt, [_, b]) => D::Mapping(Box::new(b.clone())),
            (B::AtAt, [D::Function(ka, va), D::Function(kb, vb)]) => {
                let union: BTreeSet<_> = ka.union(kb).cloned().collect();
                if union.len() <= 64 && compatible(&union) {
                    D::Function(union, Box::new(va.join(vb)))
                } else {
                    D::Mapping(Box::new(va.join(vb)))
                }
            }
            (B::AtAt, [a, b]) => match (a.range(), b.range()) {
                (Some(a), Some(b)) => D::Mapping(Box::new(a.join(b))),
                _ => D::Top,
            },
            (B::Neg, [D::Atoms(a)]) if a.len() == 1 => match a.first() {
                Some(Atom::Num(n)) if i32::try_from(-n).is_ok() => D::atom(Atom::Num(-n)),
                _ => D::Top,
            },
            (B::Neg, [a]) if a.integer_min().is_some() => D::Integer(i128::from(i32::MIN)),
            (B::Plus, [a, b]) => match (a.integer_min(), b.integer_min()) {
                (Some(a), Some(b)) => D::Integer((a + b).clamp(i128::from(i32::MIN), i128::from(i32::MAX))),
                _ => D::Top,
            },
            (B::Mul, [a, b]) => match (a.integer_min(), b.integer_min()) {
                (Some(x), Some(y)) if x >= 0 && y >= 0 => D::Integer(0),
                (Some(_), Some(_)) => D::Integer(i128::from(i32::MIN)),
                _ => D::Top,
            },
            (B::Mod, [a, b]) if a.integer_min().is_some() && b.integer_min().is_some() => D::Integer(0),
            (B::Div, [a, b]) if a.integer_min().is_some() && b.integer_min().is_some() => D::Integer(i128::from(i32::MIN)),
            (B::Minus, [a, b]) => {
                if let (Some(as_), Some(bs)) = (a.atoms(), b.atoms()) {
                    let mut out = BTreeSet::new();
                    let mut ok = !as_.is_empty() && !bs.is_empty();
                    'outer: for x in as_ {
                        for y in bs {
                            match (x, y) {
                                (Atom::Num(xn), Atom::Num(yn)) if i32::try_from(xn - yn).is_ok() => {
                                    out.insert(Atom::Num(xn - yn));
                                    if out.len() > 64 {
                                        ok = false;
                                        break 'outer;
                                    }
                                }
                                _ => {
                                    ok = false;
                                    break 'outer;
                                }
                            }
                        }
                    }
                    if ok {
                        return D::Atoms(out);
                    }
                }
                if a.integer_min().is_some() && b.integer_min().is_some() {
                    D::Integer(i128::from(i32::MIN))
                } else {
                    D::Top
                }
            }
            _ => D::Top,
        }
    }

    /// True only when every possible value belongs to the given structural
    /// type. This proves the observation; it never reads assumed invariants.
    pub fn belongs(&self, value: &Domain, set: &Expr) -> bool {
        if matches!(value, Domain::Bottom) {
            return false;
        }
        if let Domain::Records(records) = value {
            return records.iter().all(|r| self.belongs(&Domain::Record(r.clone()), set));
        }
        match (&*set.kind, value) {
            (ExprKind::Builtin { op: B::Nat, args }, _) if args.is_empty() => value.integer_min().is_some_and(|n| n >= 0),
            (ExprKind::Builtin { op: B::Int, args }, _) if args.is_empty() => value.integer_min().is_some(),
            (ExprKind::Builtin { op: B::Boolean, args }, Domain::Atoms(values)) if args.is_empty() => {
                values.iter().all(|a| matches!(a, Atom::Bool(_)))
            }
            (ExprKind::Builtin { op: B::DotDot, args }, Domain::Atoms(values)) if args.len() == 2 && !values.is_empty() => {
                matches!((self.atom_value(&args[0]), self.atom_value(&args[1])), (Some(Atom::Num(a)), Some(Atom::Num(b))) if values.iter().all(|v| matches!(v, Atom::Num(n) if *n >= a && *n <= b)))
            }
            (ExprKind::Builtin { op: B::Cup, args }, _) if args.len() == 2 => {
                // Nat union {-1}, for example, is an integer interval.
                // Restrict this proof to numeric operands; a heterogeneous
                // union may introduce comparison errors during membership.
                self.integer_floor(set).zip(value.integer_min()).is_some_and(|(floor, low)| low >= floor)
                    || value
                        .atoms()
                        .is_some_and(|values| self.exact_set(set).is_some_and(|allowed| compatible(&allowed) && values.is_subset(&allowed)))
                    || self.record_union(set).is_some_and(|shapes| {
                        matches!(value, Domain::Record(r) if shapes.iter().any(|(keys, s)| {
                            r.keys().cloned().collect::<Vec<_>>() == *keys && self.belongs(value, s)
                        }))
                    })
            }
            (ExprKind::Builtin { op: B::Seq, args }, Domain::Seq(element)) if args.len() == 1 => {
                self.type_set(&args[0]) && (matches!(**element, Domain::Bottom) || self.belongs(element, &args[0]))
            }
            (ExprKind::Builtin { op: B::Subset, args }, Domain::Set(_)) if args.len() == 1 => self.subset_belongs(value, &args[0]),
            (ExprKind::FnSet { domain, range }, Domain::Function(keys, element)) => {
                self.exact_set(domain).as_ref() == Some(keys) && self.belongs(element, range)
            }
            (ExprKind::RecordSet(fs), Domain::Record(values)) => {
                fs.len() == values.len()
                    && fs.iter().map(|(k, _)| k).collect::<BTreeSet<_>>().len() == values.len()
                    && fs.iter().all(|(k, s)| values.get(k).is_some_and(|v| self.belongs(v, s)))
            }
            (ExprKind::SetEnum(es), Domain::Record(values)) if es.len() == 1 => es.iter().any(|e| {
                let ExprKind::Record(fs) = &*e.kind else { return false };
                fs.len() == values.len()
                    && fs.iter().map(|(k, _)| k).collect::<BTreeSet<_>>().len() == values.len()
                    && fs.iter().all(|(k, e)| {
                        self.atom_value(e).is_some_and(|a| values.get(k).and_then(Domain::atoms) == Some(&BTreeSet::from([a])))
                    })
            }),
            (_, Domain::Atoms(values)) => self.exact_set(set).is_some_and(|allowed| compatible(&allowed) && values.is_subset(&allowed)),
            _ => false,
        }
    }

    // Disjoint record shapes make membership total across union alternatives ONLY when
    // equal-length alternatives also agree on the value types of every shared field
    // (runtime `RecordSet` membership iterates `Sym`s in intern order and may test a
    // shared field before encountering a differing field name).
    fn record_union<'a>(&self, set: &'a Expr) -> Option<Vec<(Vec<Arc<str>>, &'a Expr)>> {
        let mut typed = self.record_union_typed(set)?;
        for (i, (_, fa, _)) in typed.iter().enumerate() {
            for (_, fb, _) in &typed[(i + 1)..] {
                if fa.len() == fb.len() {
                    for (name, ta) in fa {
                        if let Some(tb) = fb.get(name) {
                            if !type_families_compatible(ta, tb) {
                                return None;
                            }
                        }
                    }
                }
            }
        }
        Some(typed.drain(..).map(|(keys, _, expr)| (keys, expr)).collect())
    }

    fn record_union_typed<'a>(&self, set: &'a Expr) -> Option<Vec<(Vec<Arc<str>>, BTreeMap<Arc<str>, TypeFamily>, &'a Expr)>> {
        let shape = |fields: &[(Arc<str>, Expr)]| {
            let keys: BTreeSet<_> = fields.iter().map(|(k, _)| k.clone()).collect();
            (keys.len() == fields.len()).then(|| keys.into_iter().collect::<Vec<_>>())
        };
        match &*set.kind {
            ExprKind::Builtin { op: B::Cup, args } if args.len() == 2 => {
                let mut a = self.record_union_typed(&args[0])?;
                let b = self.record_union_typed(&args[1])?;
                if a.iter().any(|(k, _, _)| b.iter().any(|(j, _, _)| k == j)) {
                    return None;
                }
                a.extend(b);
                Some(a)
            }
            ExprKind::RecordSet(fs) => {
                let keys = shape(fs)?;
                let mut map = BTreeMap::new();
                for (k, e) in fs {
                    map.insert(k.clone(), self.type_family(e)?);
                }
                Some(vec![(keys, map, set)])
            }
            ExprKind::SetEnum(es) if es.len() == 1 => {
                let ExprKind::Record(fs) = &*es[0].kind else { return None };
                let keys = shape(fs)?;
                let mut map = BTreeMap::new();
                for (k, e) in fs {
                    let atom = self.atom_value(e)?;
                    map.insert(k.clone(), atom_type_family(&BTreeSet::from([atom]))?);
                }
                Some(vec![(keys, map, set)])
            }
            _ => None,
        }
    }

    pub fn subset_belongs(&self, value: &Domain, set: &Expr) -> bool {
        let Domain::Set(element) = value else { return false };
        if !(self.type_set(set) || self.record_union(set).is_some()) {
            return false;
        }
        matches!(**element, Domain::Bottom) || self.belongs(element, set)
    }

    // Validate the operand of a structural type even for empty containers.
    // This prevents a vacuous membership proof hiding an invalid type set.
    fn type_set(&self, set: &Expr) -> bool {
        self.type_family(set).is_some()
    }

    fn type_family(&self, set: &Expr) -> Option<TypeFamily> {
        match &*set.kind {
            ExprKind::RecordSet(fs) => {
                if fs.iter().map(|(k, _)| k).collect::<BTreeSet<_>>().len() != fs.len() {
                    return None;
                }
                let mut map = BTreeMap::new();
                for (k, s) in fs {
                    map.insert(k.clone(), self.type_family(s)?);
                }
                Some(TypeFamily::Record(map))
            }
            ExprKind::FnSet { domain, range } => {
                let dom = self.exact_set(domain).filter(compatible)?;
                Some(TypeFamily::Fn(dom, Box::new(self.type_family(range)?)))
            }
            ExprKind::Builtin { op: B::Nat | B::Int, args } if args.is_empty() => Some(TypeFamily::Scalar(Some(0))),
            ExprKind::Builtin { op: B::Boolean, args } if args.is_empty() => Some(TypeFamily::Scalar(Some(2))),
            ExprKind::Builtin { op: B::Subset, args } if args.len() == 1 => Some(TypeFamily::Set(Box::new(self.type_family(&args[0])?))),
            ExprKind::Builtin { op: B::Seq, args } if args.len() == 1 => Some(TypeFamily::Seq(Box::new(self.type_family(&args[0])?))),
            ExprKind::Builtin { op: B::DotDot, args } if args.len() == 2 => {
                let (Atom::Num(a), Atom::Num(b)) = (self.atom_value(&args[0])?, self.atom_value(&args[1])?) else {
                    return None;
                };
                if b >= a && i32::try_from(b - a + 1).is_err() {
                    return None;
                }
                Some(TypeFamily::Scalar(Some(0)))
            }
            ExprKind::Builtin { op: B::Cup, .. } => {
                if self.integer_floor(set).is_some() {
                    return Some(TypeFamily::Scalar(Some(0)));
                }
                if let Some(s) = self.exact_set(set).filter(compatible) {
                    return atom_type_family(&s);
                }
                let typed = self.record_union_typed(set)?;
                let _ = self.record_union(set)?;
                Some(TypeFamily::RecordUnion(typed.into_iter().map(|(_, m, _)| m).collect()))
            }
            _ => atom_type_family(&self.exact_set(set).filter(compatible)?),
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
            ExprKind::Const(c) => self.exact_const_sets.get(c).cloned(),
            ExprKind::SetEnum(es) => {
                let s: BTreeSet<Atom> = es.iter().map(|e| self.atom_value(e)).collect::<Option<_>>()?;
                (s.len() <= 64 && atoms_mutually_comparable(&s)).then_some(s)
            }
            ExprKind::Builtin { op: B::Boolean, args } if args.is_empty() => Some(BTreeSet::from([Atom::Bool(false), Atom::Bool(true)])),
            ExprKind::Builtin { op: B::DotDot, args } if args.len() == 2 => {
                let (Atom::Num(a), Atom::Num(b)) = (self.atom_value(&args[0])?, self.atom_value(&args[1])?) else {
                    return None;
                };
                if b < a {
                    return Some(BTreeSet::new());
                }
                if b - a <= 64 {
                    Some((a..=b).map(Atom::Num).collect())
                } else {
                    None
                }
            }
            ExprKind::Builtin { op: B::Cup, args } if args.len() == 2 => {
                let mut a = self.exact_set(&args[0])?;
                a.extend(self.exact_set(&args[1])?);
                (a.len() <= 64 && atoms_mutually_comparable(&a)).then_some(a)
            }
            ExprKind::Builtin { op: B::SetMinus, args } if args.len() == 2 => {
                let a = self.exact_set(&args[0])?;
                let b = self.exact_set(&args[1])?;
                let union: BTreeSet<_> = a.union(&b).cloned().collect();
                atoms_mutually_comparable(&union).then(|| a.difference(&b).cloned().collect())
            }
            ExprKind::Builtin { op: B::Cap, args } if args.len() == 2 => {
                let a = self.exact_set(&args[0])?;
                let b = self.exact_set(&args[1])?;
                let union: BTreeSet<_> = a.union(&b).cloned().collect();
                atoms_mutually_comparable(&union).then(|| a.intersection(&b).cloned().collect())
            }
            ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => self.exact_set(&args[0]),
            ExprKind::Builtin { op: B::Domain, args }
                if args.len() == 1 && matches!(&*args[0].kind, ExprKind::Var(_) | ExprKind::Const(_)) =>
            {
                match self.eval(&args[0], &Locals::new(), 0) {
                    Domain::Function(ks, _) => Some(ks),
                    Domain::Record(fs) if fs.len() <= 64 => Some(fs.keys().map(|k| Atom::Str(k.clone())).collect()),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

fn is_const_only(e: &Expr) -> bool {
    if matches!(&*e.kind, ExprKind::Var(_) | ExprKind::InstVar { .. } | ExprKind::At) {
        return false;
    }
    let mut ok = true;
    visit::children(e, &mut |c| ok &= is_const_only(c));
    ok
}

fn is_total_const_expr(domains: &Domains, e: &Expr) -> bool {
    if domains.atom_value(e).is_some() || domains.exact_set(e).is_some() {
        return true;
    }
    match &*e.kind {
        ExprKind::Const(c) => !matches!(domains.constants.get(c), None | Some(Domain::Top)),
        ExprKind::Tuple(es) => es.iter().all(|x| is_total_const_expr(domains, x)),
        ExprKind::Record(fs) => fs.iter().all(|(_, x)| is_total_const_expr(domains, x)),
        ExprKind::Builtin { op: B::TLCEval, args } if args.len() == 1 => is_total_const_expr(domains, &args[0]),
        _ => false,
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
enum TypeFamily {
    /// `None` = empty or untyped model values only; `Some(0|1|2)` = `Num|Str|Bool` (+ optional untyped model values).
    Scalar(Option<u8>),
    Set(Box<TypeFamily>),
    Seq(Box<TypeFamily>),
    Fn(BTreeSet<Atom>, Box<TypeFamily>),
    Record(BTreeMap<Arc<str>, TypeFamily>),
    RecordUnion(Vec<BTreeMap<Arc<str>, TypeFamily>>),
}

fn atom_type_family(values: &BTreeSet<Atom>) -> Option<TypeFamily> {
    if !compatible(values) {
        return None;
    }
    let mut fam = None;
    for a in values {
        let f = match a {
            Atom::Num(_) => 0,
            Atom::Str(_) => 1,
            Atom::Bool(_) => 2,
            Atom::Model(_) => continue,
        };
        if fam.is_some_and(|old| old != f) {
            return None;
        }
        fam = Some(f);
    }
    Some(TypeFamily::Scalar(fam))
}

fn type_families_compatible(a: &TypeFamily, b: &TypeFamily) -> bool {
    match (a, b) {
        (TypeFamily::Scalar(k1), TypeFamily::Scalar(k2)) => match (k1, k2) {
            (None, _) | (_, None) => true,
            (Some(x), Some(y)) => x == y,
        },
        (TypeFamily::Set(x), TypeFamily::Set(y)) | (TypeFamily::Seq(x), TypeFamily::Seq(y)) => type_families_compatible(x, y),
        (TypeFamily::Fn(d1, r1), TypeFamily::Fn(d2, r2)) => {
            let u: BTreeSet<_> = d1.union(d2).cloned().collect();
            atoms_mutually_comparable(&u) && type_families_compatible(r1, r2)
        }
        (TypeFamily::Record(r1), TypeFamily::Record(r2)) => {
            r1.len() != r2.len()
                || r1.iter().all(|(k, v)| match r2.get(k) {
                    Some(w) => type_families_compatible(v, w),
                    None => true,
                })
        }
        (TypeFamily::RecordUnion(rs), other) | (other, TypeFamily::RecordUnion(rs)) => {
            rs.iter().all(|r| type_families_compatible(&TypeFamily::Record(r.clone()), other))
        }
        _ => false,
    }
}

pub(super) fn atoms_mutually_comparable(values: &BTreeSet<Atom>) -> bool {
    let mut scalar_fam: Option<u8> = None;
    let mut typed_mv: Option<char> = None;
    for a in values {
        match a {
            Atom::Num(_) => {
                if typed_mv.is_some() || scalar_fam.is_some_and(|old| old != 0) {
                    return false;
                }
                scalar_fam = Some(0);
            }
            Atom::Str(_) => {
                if typed_mv.is_some() || scalar_fam.is_some_and(|old| old != 1) {
                    return false;
                }
                scalar_fam = Some(1);
            }
            Atom::Bool(_) => {
                if typed_mv.is_some() || scalar_fam.is_some_and(|old| old != 2) {
                    return false;
                }
                scalar_fam = Some(2);
            }
            Atom::Model(s) => {
                let mut chars = s.chars();
                if let (Some(c0), Some('_'), Some(_)) = (chars.next(), chars.next(), chars.next()) {
                    if scalar_fam.is_some() || typed_mv.is_some_and(|old| old != c0) {
                        return false;
                    }
                    typed_mv = Some(c0);
                }
            }
        }
    }
    true
}

fn field_names_domain(fs: &BTreeMap<Arc<str>, Domain>) -> Domain {
    if fs.is_empty() {
        return Domain::Bottom;
    }
    if fs.len() > 64 {
        return Domain::Top;
    }
    Domain::Atoms(fs.keys().map(|k| Atom::Str(k.clone())).collect())
}

// Sound upper bound on set intersection `a \cap b`.
fn meet_domain(a: Domain, b: Domain) -> Domain {
    match (a, b) {
        (Domain::Bottom, _) | (_, Domain::Bottom) => Domain::Bottom,
        (Domain::Top, x) | (x, Domain::Top) => x,
        (Domain::Atoms(sa), Domain::Atoms(sb)) => {
            let inter: BTreeSet<_> = sa.intersection(&sb).cloned().collect();
            if inter.is_empty() {
                Domain::Bottom
            } else {
                Domain::Atoms(inter)
            }
        }
        (a, _) => a,
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
        (ExceptKey::Field(k), Domain::Records(records)) => {
            // EXCEPT ignores an absent field. Update each possible record
            // shape separately, preserving optional timestamp presence.
            for fields in records {
                if let Some(field) = fields.get_mut(k) {
                    update(field, rest, value);
                }
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

fn config_exact_set(v: &CfgValue) -> Option<BTreeSet<Atom>> {
    let CfgValue::Set(es) = v else { return None };
    let mut out = BTreeSet::new();
    for e in es {
        let atom = match e {
            CfgValue::Int(n) if i32::try_from(*n).is_ok() => Atom::Num(i128::from(*n)),
            CfgValue::Str(s) => Atom::Str(s.as_str().into()),
            CfgValue::Bool(b) => Atom::Bool(*b),
            CfgValue::ModelValue(s) => Atom::Model(s.as_str().into()),
            _ => return None,
        };
        out.insert(atom);
        if out.len() > 64 {
            return None;
        }
    }
    Some(out)
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
