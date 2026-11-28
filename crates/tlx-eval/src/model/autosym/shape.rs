//! Shapes: an over-approximation of the values an expression can take,
//! recording where elements of the candidate sets may occur.
//!
//! A shape is a union of kinds (scalar, set, function, record, tuple,
//! operator, or "any value"), each with the shapes of its parts. The mask
//! of a part is the set of candidate sets (bit `i`: candidate `i`) whose
//! elements it may contain. Shapes form a lattice: `Sh::default()` (no
//! value) is the least element, `join` the least upper bound. Every shape
//! is finite: `limit` cuts it at a depth, replacing deeper parts by "any
//! value" with their mask.

use std::collections::BTreeMap;
use std::hash::{Hash, Hasher};
use std::rc::Rc;
use std::sync::Arc;

use tlx_sema::builtins::Builtin;
use tlx_sema::hir::{DefId, Expr, ExprKind, LocalId};
use tlx_value::LazySet;
use tlx_value::{Sym, Value};

/// Candidate sets, one bit each.
pub(super) type Mask = u64;

/// Every candidate set.
pub(super) const ALL: Mask = Mask::MAX;

/// The values an expression may take (`None`: none, the least shape).
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub(super) struct Sh(Option<Rc<Node>>);

#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
struct Node {
    /// Any value at all, with elements of at most these candidate sets.
    any: Option<Mask>,
    /// A Boolean, integer, string or model value, possibly an element of
    /// these candidate sets.
    scalar: Option<Mask>,
    /// A set with elements of this shape (`Some(Sh::default())`: empty).
    set: Option<Sh>,
    /// A function: the shapes of its domain elements and of its values.
    fcn: Option<(Sh, Sh)>,
    /// A record, by field.
    rec: Option<BTreeMap<Arc<str>, Sh>>,
    /// A tuple of this many components.
    tup: Option<Vec<Sh>>,
    /// An operator (an argument of a higher-order operator).
    ops: Vec<OpVal>,
}

/// An operator passed as an argument.
#[derive(Clone, Debug)]
pub(super) enum OpVal {
    Def(DefId),
    Builtin(Builtin),
    /// `LAMBDA params : body` (the expression itself).
    Lambda(Expr),
}

impl OpVal {
    fn key(&self) -> (u8, usize) {
        match self {
            OpVal::Def(d) => (0, d.idx()),
            OpVal::Builtin(b) => (1, *b as usize),
            OpVal::Lambda(e) => (2, Arc::as_ptr(&e.kind) as *const () as usize),
        }
    }
}

impl PartialEq for OpVal {
    fn eq(&self, o: &OpVal) -> bool {
        self.key() == o.key()
    }
}

impl Eq for OpVal {}

impl Hash for OpVal {
    fn hash<H: Hasher>(&self, h: &mut H) {
        self.key().hash(h)
    }
}

/// Tuples of more components are taken as functions (sequences).
const MAX_TUPLE: usize = 8;

fn join_opt(a: Option<Mask>, b: Option<Mask>) -> Option<Mask> {
    match (a, b) {
        (Some(x), Some(y)) => Some(x | y),
        (x, None) => x,
        (None, y) => y,
    }
}

fn join_sh_opt(a: &Option<Sh>, b: &Option<Sh>) -> Option<Sh> {
    match (a, b) {
        (Some(x), Some(y)) => Some(x.join(y)),
        (Some(x), None) | (None, Some(x)) => Some(x.clone()),
        (None, None) => None,
    }
}

impl Sh {
    /// (A node with an "any value" part absorbs the parts it covers, so
    /// that "any value" is the top of the lattice below its mask.)
    fn node(mut n: Node) -> Sh {
        if let Some(m) = n.any {
            let covered = |s: &Sh| s.mask() & !m == 0;
            if n.scalar.is_some_and(|x| x & !m == 0) {
                n.scalar = None;
            }
            if n.set.as_ref().is_some_and(covered) {
                n.set = None;
            }
            if n.fcn.as_ref().is_some_and(|(d, r)| covered(d) && covered(r)) {
                n.fcn = None;
            }
            if n.rec.as_ref().is_some_and(|fs| fs.values().all(covered)) {
                n.rec = None;
            }
            if n.tup.as_ref().is_some_and(|ts| ts.iter().all(covered)) {
                n.tup = None;
            }
        }
        Sh(Some(Rc::new(n)))
    }

    pub(super) fn any(m: Mask) -> Sh {
        Sh::node(Node { any: Some(m), ..Node::default() })
    }

    pub(super) fn scalar(m: Mask) -> Sh {
        Sh::node(Node { scalar: Some(m), ..Node::default() })
    }

    /// A Boolean, integer or string.
    pub(super) fn plain() -> Sh {
        Sh::scalar(0)
    }

    pub(super) fn set(elems: Sh) -> Sh {
        Sh::node(Node { set: Some(elems), ..Node::default() })
    }

    pub(super) fn fcn(dom: Sh, range: Sh) -> Sh {
        Sh::node(Node { fcn: Some((dom, range)), ..Node::default() })
    }

    /// A sequence with elements of this shape.
    pub(super) fn seq(elems: Sh) -> Sh {
        Sh::fcn(Sh::plain(), elems)
    }

    pub(super) fn rec(fields: BTreeMap<Arc<str>, Sh>) -> Sh {
        Sh::node(Node { rec: Some(fields), ..Node::default() })
    }

    pub(super) fn tup(es: Vec<Sh>) -> Sh {
        if es.len() > MAX_TUPLE {
            let all = es.iter().fold(Sh::default(), |a, e| a.join(e));
            return Sh::seq(all);
        }
        Sh::node(Node { tup: Some(es), ..Node::default() })
    }

    pub(super) fn op(o: OpVal) -> Sh {
        Sh::node(Node { ops: vec![o], ..Node::default() })
    }

    pub(super) fn join(&self, o: &Sh) -> Sh {
        let (a, b) = match (&self.0, &o.0) {
            (None, _) => return o.clone(),
            (_, None) => return self.clone(),
            (Some(a), Some(b)) if Rc::ptr_eq(a, b) || a == b => return self.clone(),
            (Some(a), Some(b)) => (a, b),
        };
        let mut n = Node {
            any: join_opt(a.any, b.any),
            scalar: join_opt(a.scalar, b.scalar),
            set: join_sh_opt(&a.set, &b.set),
            fcn: match (&a.fcn, &b.fcn) {
                (Some((d, r)), Some((e, s))) => Some((d.join(e), r.join(s))),
                (Some(x), None) | (None, Some(x)) => Some(x.clone()),
                (None, None) => None,
            },
            rec: match (&a.rec, &b.rec) {
                (Some(x), Some(y)) => {
                    let mut m = x.clone();
                    for (k, v) in y {
                        let e = m.entry(k.clone()).or_default();
                        *e = e.join(v);
                    }
                    Some(m)
                }
                (Some(x), None) | (None, Some(x)) => Some(x.clone()),
                (None, None) => None,
            },
            tup: None,
            ops: a.ops.clone(),
        };
        for op in &b.ops {
            if !n.ops.contains(op) {
                n.ops.push(op.clone());
            }
        }
        // (Tuples of different lengths are joined by position: component i
        // of either.)
        match (&a.tup, &b.tup) {
            (Some(x), Some(y)) => {
                let at = |t: &[Sh], i: usize| t.get(i).cloned().unwrap_or_default();
                n.tup = Some((0..x.len().max(y.len())).map(|i| at(x, i).join(&at(y, i))).collect());
            }
            (Some(x), None) | (None, Some(x)) => n.tup = Some(x.clone()),
            (None, None) => {}
        }
        Sh::node(n)
    }

    /// Every candidate set whose elements may occur in a value of this
    /// shape (operators passed as arguments do not count: they are not
    /// values).
    pub(super) fn mask(&self) -> Mask {
        let Some(n) = &self.0 else { return 0 };
        let mut m = n.any.unwrap_or(0) | n.scalar.unwrap_or(0);
        if let Some(s) = &n.set {
            m |= s.mask();
        }
        if let Some((d, r)) = &n.fcn {
            m |= d.mask() | r.mask();
        }
        if let Some(fs) = &n.rec {
            m |= fs.values().fold(0, |a, f| a | f.mask());
        }
        if let Some(ts) = &n.tup {
            m |= ts.iter().fold(0, |a, t| a | t.mask());
        }
        m
    }

    /// The "any value" part, as a shape (default: none).
    fn any_part(&self) -> Sh {
        match self.0.as_ref().and_then(|n| n.any) {
            Some(m) => Sh::any(m),
            None => Sh::default(),
        }
    }

    /// The scalar part (strings and sequences share `\o`, `Tail`, ...).
    pub(super) fn scalar_part(&self) -> Sh {
        match self.0.as_ref().and_then(|n| n.scalar) {
            Some(m) => Sh::scalar(m),
            None => Sh::default(),
        }
    }

    /// The elements, used as a set.
    pub(super) fn elems(&self) -> Sh {
        let Some(n) = &self.0 else { return Sh::default() };
        let s = n.set.clone().unwrap_or_default();
        s.join(&self.any_part())
    }

    /// The domain elements, used as a function.
    pub(super) fn dom(&self) -> Sh {
        let Some(n) = &self.0 else { return Sh::default() };
        let mut d = self.any_part();
        if let Some((x, _)) = &n.fcn {
            d = d.join(x);
        }
        if n.rec.is_some() || n.tup.is_some() {
            d = d.join(&Sh::plain());
        }
        d
    }

    /// The values, used as a function (all of them).
    pub(super) fn range(&self) -> Sh {
        let Some(n) = &self.0 else { return Sh::default() };
        let mut r = self.any_part();
        if let Some((_, x)) = &n.fcn {
            r = r.join(x);
        }
        if let Some(fs) = &n.rec {
            r = fs.values().fold(r, |a, f| a.join(f));
        }
        if let Some(ts) = &n.tup {
            r = ts.iter().fold(r, |a, t| a.join(t));
        }
        r
    }

    /// The value of field `f`.
    pub(super) fn field(&self, f: &str) -> Sh {
        let Some(n) = &self.0 else { return Sh::default() };
        let mut r = self.any_part();
        if let Some((_, x)) = &n.fcn {
            r = r.join(x);
        }
        if let Some(fs) = &n.rec {
            if let Some(x) = fs.get(f) {
                r = r.join(x);
            }
        }
        r
    }

    /// The value at index `i` (1-based) of a tuple, or of any function.
    pub(super) fn index(&self, i: i128) -> Sh {
        let Some(n) = &self.0 else { return Sh::default() };
        let mut r = self.any_part();
        if let Some((_, x)) = &n.fcn {
            r = r.join(x);
        }
        if let Some(ts) = &n.tup {
            if i >= 1 && (i as usize) <= ts.len() {
                r = r.join(&ts[i as usize - 1]);
            }
        }
        r
    }

    /// The value at a key of this shape (`key`: a literal key, if known).
    pub(super) fn apply(&self, key: Option<&Lit>) -> Sh {
        match key {
            Some(Lit::Str(f)) => self.field(f),
            Some(Lit::Int(i)) => self.index(*i),
            None => self.range(),
        }
    }

    /// This shape with the value at `key` (of shape `k`) replaced by
    /// one of shape `v` (EXCEPT), joined with the original.
    pub(super) fn with_entry(&self, k: &Sh, key: Option<&Lit>, v: &Sh) -> Sh {
        let Some(n) = &self.0 else { return Sh::default() };
        let mut out = (**n).clone();
        if let Some(m) = out.any.as_mut() {
            *m |= v.mask();
        }
        if let Some((d, r)) = out.fcn.as_mut() {
            *d = d.join(k);
            *r = r.join(v);
        }
        if let Some(fs) = out.rec.as_mut() {
            match key {
                Some(Lit::Str(f)) => {
                    if let Some(x) = fs.get_mut(&**f) {
                        *x = x.join(v);
                    }
                }
                _ => fs.values_mut().for_each(|x| *x = x.join(v)),
            }
        }
        if let Some(ts) = out.tup.as_mut() {
            match key {
                Some(Lit::Int(i)) if *i >= 1 && (*i as usize) <= ts.len() => {
                    let x = &mut ts[*i as usize - 1];
                    *x = x.join(v);
                }
                _ => ts.iter_mut().for_each(|x| *x = x.join(v)),
            }
        }
        Sh::node(out)
    }

    /// The operators of this shape.
    pub(super) fn ops(&self) -> Vec<OpVal> {
        self.0.as_ref().map(|n| n.ops.clone()).unwrap_or_default()
    }

    /// This shape cut at `depth`: deeper parts become "any value" with
    /// their mask (so that every chain of joins is finite).
    pub(super) fn limit(&self, depth: usize) -> Sh {
        let Some(n) = &self.0 else { return Sh::default() };
        let has_parts = n.set.is_some() || n.fcn.is_some() || n.rec.is_some() || n.tup.is_some();
        if depth == 0 && has_parts {
            return Sh::node(Node { any: Some(self.mask()), ops: n.ops.clone(), ..Node::default() });
        }
        if !has_parts {
            return self.clone();
        }
        let d = depth.saturating_sub(1);
        Sh::node(Node {
            any: n.any,
            scalar: n.scalar,
            set: n.set.as_ref().map(|s| s.limit(d)),
            fcn: n.fcn.as_ref().map(|(x, y)| (x.limit(d), y.limit(d))),
            rec: n.rec.as_ref().map(|fs| fs.iter().map(|(k, v)| (k.clone(), v.limit(d))).collect()),
            tup: n.tup.as_ref().map(|ts| ts.iter().map(|t| t.limit(d)).collect()),
            ops: n.ops.clone(),
        })
    }

    /// Whether every value of `self` is a value of `o` (for fixpoints: a
    /// sufficient test, joining and comparing).
    pub(super) fn le(&self, o: &Sh) -> bool {
        &o.join(self) == o
    }
}

/// A literal key: a string (field) or an integer (index).
#[derive(Clone, Debug)]
pub(super) enum Lit {
    Str(Arc<str>),
    Int(i128),
}

impl Lit {
    pub(super) fn of(e: &Expr) -> Option<Lit> {
        match &*e.kind {
            ExprKind::Str(s) => Some(Lit::Str(s.clone())),
            ExprKind::Num(n) => Some(Lit::Int(*n)),
            _ => None,
        }
    }
}

/// The shape of a value: `None` if it cannot be told without enumerating
/// a set the evaluator defines (a filter of an infinite set) or a
/// function over a lazy domain.
pub(super) fn of_value(v: &Value, mask_of: &dyn Fn(Sym) -> Mask) -> Option<Sh> {
    let join_all = |es: &mut dyn Iterator<Item = &Value>| -> Option<Sh> {
        let mut s = Sh::default();
        for e in es {
            s = s.join(&of_value(e, mask_of)?);
        }
        Some(s)
    };
    Some(match v {
        Value::Bool(_) | Value::Int(_) | Value::Str(_) => Sh::plain(),
        Value::ModelValue(m) => Sh::scalar(mask_of(*m)),
        Value::Interval(..) => Sh::set(Sh::plain()),
        Value::Set(es) => Sh::set(join_all(&mut es.iter())?),
        Value::Tuple(es) if es.len() <= MAX_TUPLE => Sh::tup(es.iter().map(|e| of_value(e, mask_of)).collect::<Option<_>>()?),
        Value::Tuple(es) => Sh::seq(join_all(&mut es.iter())?),
        Value::Record(fs) => {
            let mut m = BTreeMap::new();
            for (k, x) in fs.iter() {
                m.insert(Arc::from(k.as_str()), of_value(x, mask_of)?);
            }
            Sh::rec(m)
        }
        Value::Fcn(ps, _) => Sh::fcn(join_all(&mut ps.iter().map(|(k, _)| k))?, join_all(&mut ps.iter().map(|(_, x)| x))?),
        Value::LazySet(l) => match &**l {
            LazySet::Enum(es) => Sh::set(join_all(&mut es.iter())?),
            LazySet::Subset(x) | LazySet::KSubset(_, x) => Sh::set(Sh::set(of_value(x, mask_of)?.elems())),
            LazySet::FcnSet(a, b) => Sh::set(Sh::fcn(of_value(a, mask_of)?.elems(), of_value(b, mask_of)?.elems())),
            LazySet::Product(vs) => Sh::set(Sh::tup(vs.iter().map(|x| Some(of_value(x, mask_of)?.elems())).collect::<Option<_>>()?)),
            LazySet::RecordSet(fs) => {
                let mut m = BTreeMap::new();
                for (k, x) in fs {
                    m.insert(Arc::from(k.as_str()), of_value(x, mask_of)?.elems());
                }
                Sh::set(Sh::rec(m))
            }
            LazySet::Seq(x) => Sh::set(Sh::seq(of_value(x, mask_of)?.elems())),
            LazySet::Union(x) => Sh::set(of_value(x, mask_of)?.elems().elems()),
            LazySet::Cup(a, b) => Sh::set(of_value(a, mask_of)?.elems().join(&of_value(b, mask_of)?.elems())),
            LazySet::Cap(a, _) | LazySet::Diff(a, _) => Sh::set(of_value(a, mask_of)?.elems()),
            LazySet::Nat | LazySet::Int | LazySet::StringSet => Sh::set(Sh::plain()),
            LazySet::Any => Sh::set(Sh::any(0)),
            LazySet::Custom(_) => return None,
        },
        Value::LazyFcn(_) => return None,
    })
}

/// Whether the transposition of the model values `a` and `b` maps `v` to
/// itself; `None` if that cannot be told without enumerating a set the
/// evaluator defines.
pub(super) fn fixed_by(v: &Value, a: Sym, b: Sym) -> Option<bool> {
    let image = |atom| {
        let tlx_value::SymAtom::Model(m) = atom else { return None };
        if m == a {
            Some(Value::ModelValue(b))
        } else if m == b {
            Some(Value::ModelValue(a))
        } else {
            None
        }
    };
    match v {
        Value::LazySet(l) => match &**l {
            LazySet::Enum(_) => v.normalize().ok().and_then(|v| fixed_by(&v, a, b)),
            LazySet::Subset(x) | LazySet::KSubset(_, x) | LazySet::Seq(x) | LazySet::Union(x) => fixed_by(x, a, b),
            LazySet::FcnSet(x, y) | LazySet::Cup(x, y) | LazySet::Cap(x, y) | LazySet::Diff(x, y) => {
                Some(fixed_by(x, a, b)? && fixed_by(y, a, b)?)
            }
            LazySet::Product(vs) => vs.iter().try_fold(true, |acc, x| Some(acc && fixed_by(x, a, b)?)),
            LazySet::RecordSet(fs) => fs.iter().try_fold(true, |acc, (_, x)| Some(acc && fixed_by(x, a, b)?)),
            LazySet::Nat | LazySet::Int | LazySet::StringSet | LazySet::Any => Some(true),
            LazySet::Custom(_) => None,
        },
        Value::LazyFcn(_) => None,
        _ if !mentions(v, a) && !mentions(v, b) => Some(true),
        _ => match tlx_value::ops::permute_shared(v, &image) {
            Ok(None) => Some(true),
            Ok(Some(w)) => Some(w == *v),
            Err(_) => None,
        },
    }
}

/// Whether model value `m` occurs in `v` (enumerated values only; a lazy
/// value counts as mentioning it).
fn mentions(v: &Value, m: Sym) -> bool {
    match v {
        Value::ModelValue(x) => *x == m,
        Value::Bool(_) | Value::Int(_) | Value::Str(_) | Value::Interval(..) => false,
        Value::Set(es) | Value::Tuple(es) => es.iter().any(|e| mentions(e, m)),
        Value::Record(fs) => fs.iter().any(|(_, x)| mentions(x, m)),
        Value::Fcn(ps, _) => ps.iter().any(|(k, x)| mentions(k, m) || mentions(x, m)),
        Value::LazySet(_) | Value::LazyFcn(_) => true,
    }
}

/// The local variables bound by an operator value's parameters (for a
/// LAMBDA).
pub(super) fn lambda_parts(e: &Expr) -> Option<(&[LocalId], &Expr)> {
    match &*e.kind {
        ExprKind::Lambda { params, body } => Some((params, body)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn join_is_an_upper_bound_and_idempotent() {
        let a = Sh::set(Sh::scalar(1));
        let b = Sh::set(Sh::scalar(2));
        let j = a.join(&b);
        assert_eq!(j.elems().mask(), 3);
        assert!(a.le(&j) && b.le(&j));
        assert_eq!(j.join(&j), j);
        assert_eq!(Sh::default().join(&a), a);
    }

    #[test]
    fn records_are_field_sensitive() {
        let mut m = BTreeMap::new();
        m.insert(Arc::from("acc"), Sh::scalar(1));
        m.insert(Arc::from("bal"), Sh::plain());
        let r = Sh::rec(m);
        assert_eq!(r.field("bal").mask(), 0);
        assert_eq!(r.field("acc").mask(), 1);
        assert_eq!(r.range().mask(), 1);
        let msgs = Sh::set(r);
        assert_eq!(msgs.elems().field("bal").mask(), 0);
    }

    #[test]
    fn tuples_of_different_lengths_join_by_position() {
        let a = Sh::tup(vec![Sh::scalar(1)]);
        let b = Sh::tup(vec![Sh::plain(), Sh::scalar(2)]);
        let j = a.join(&b);
        assert_eq!(j.index(1).mask(), 1);
        assert_eq!(j.index(2).mask(), 2);
        assert_eq!(j.range().mask(), 3);
        assert_eq!(j.dom().mask(), 0);
    }

    #[test]
    fn limit_keeps_the_mask() {
        let deep = Sh::set(Sh::set(Sh::set(Sh::scalar(4))));
        let cut = deep.limit(1);
        assert_eq!(cut.mask(), 4);
        assert!(deep.le(&cut));
    }

    #[test]
    fn transpositions_fix_symmetric_values() {
        let (a, b, c) = (Sym::new("autosym_a"), Sym::new("autosym_b"), Sym::new("autosym_c"));
        let set = Value::set_from(vec![Value::ModelValue(a), Value::ModelValue(b)]).unwrap();
        assert_eq!(fixed_by(&set, a, b), Some(true));
        assert_eq!(fixed_by(&Value::ModelValue(a), a, b), Some(false));
        assert_eq!(fixed_by(&Value::ModelValue(c), a, b), Some(true));
        let pairs = Value::set_from(vec![set.clone(), Value::set_from(vec![Value::ModelValue(a), Value::ModelValue(c)]).unwrap()]).unwrap();
        assert_eq!(fixed_by(&pairs, a, b), Some(false));
    }
}
