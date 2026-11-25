//! Shapes: static descriptions of the set of values a variable (or
//! sub-value) can take, precise enough to give it a fixed-width encoding.

use std::borrow::Cow;
use std::sync::Arc;

use tlx_value::{Sym, Value};

/// Universes up to this many elements are encoded as bitsets.
pub const MAX_BITSET_UNIVERSE: u64 = 4096;
/// Unions with more alternatives than this collapse to `Dyn`.
pub const MAX_UNION_ARMS: usize = 8;
/// Most tuple arms (of different lengths) kept apart in a union; more
/// become one `Seq`.
pub const MAX_TUPLE_ARMS: usize = 4;
/// Largest encoding of a `Map` (presence bitset and slots), in words.
pub const MAX_MAP_WORDS: usize = 4096;

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Shape {
    /// No value observed yet (bottom of the lattice).
    Never,
    Bool,
    /// Integers in `lo..=hi`.
    Int {
        lo: i64,
        hi: i64,
    },
    /// Atomic values (model values, strings) from a finite universe, sorted in
    /// TLC order (`Value::cmp`), without duplicates.
    Atom(Arc<[Value]>),
    /// Sets of `elem` with at most `max_card` elements.
    Set {
        elem: Box<Shape>,
        max_card: usize,
    },
    /// Functions with the fixed finite domain `dom` (sorted, canonical,
    /// neither `1..n` nor all strings — those are `Tuple`/`Record`).
    Fcn {
        dom: Arc<[Value]>,
        range: Box<Shape>,
    },
    /// Functions whose domain varies over subsets of the finite universe of
    /// `key` (bags, functions on `0..n` with a variable `n`, ...): a
    /// presence bitset over the universe, then one `range` slot per
    /// universe element (all zero when absent). Keys are enumerated in TLC
    /// order (see `map_key_ok`).
    Map {
        key: Box<Shape>,
        range: Box<Shape>,
    },
    /// Records with a fixed set of fields (sorted by `Sym` order).
    Record(Arc<[(Sym, Shape)]>),
    /// Tuples / functions on `1..n` with a fixed length `n` (one shape per position).
    Tuple(Arc<[Shape]>),
    /// Sequences of varying length up to `max_len`.
    Seq {
        elem: Box<Shape>,
        max_len: usize,
    },
    /// Alternatives of different kinds (e.g. records with different field
    /// sets); each arm has a distinct kind key (see `kind_key`).
    Union(Arc<[Shape]>),
    /// Anything: stored as an interned `Value` handle.
    Dyn,
    /// Any finite value: a handle into the run's value store
    /// (`crate::store`, `TLX_VALUE_STORE`). Layouts use it where shape
    /// inference chose `Dyn`; inference itself never produces it. All `Ref`
    /// shapes of a run share one store (and compare equal).
    Ref(crate::store::StoreRef),
}

/// Discriminates union arms: two shapes with the same key are joined into
/// one arm, different keys become separate arms.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum KindKey {
    Bool,
    Int,
    Atom,
    Set,
    Fcn(Arc<[Value]>),
    Map,
    /// Field count first, then names: records sort like TLC compares them
    /// (so a union of record arms is in TLC order).
    Record(usize, Vec<Sym>),
    Tuple(usize),
    Seq,
}

/// Join family of a shape: shapes of the same family are joined
/// componentwise, different families become union arms. This is coarser than
/// `KindKey`: tuples of any length and sequences form one family (their join
/// is a `Seq`, or tuple arms by length, see `join_seq_like`), and functions with any domain form one family (their join is
/// `Dyn` when the domains differ).
#[derive(PartialEq, Eq)]
enum Family<'a> {
    Bool,
    Int,
    Atom,
    Set,
    Fcn,
    Record(&'a [(Sym, Shape)]),
    SeqLike,
}

fn family(s: &Shape) -> Option<Family<'_>> {
    Some(match s {
        Shape::Bool => Family::Bool,
        Shape::Int { .. } => Family::Int,
        Shape::Atom(_) => Family::Atom,
        Shape::Set { .. } => Family::Set,
        Shape::Fcn { .. } | Shape::Map { .. } => Family::Fcn,
        Shape::Record(fs) => Family::Record(fs),
        Shape::Tuple(_) | Shape::Seq { .. } => Family::SeqLike,
        Shape::Never | Shape::Union(_) | Shape::Dyn | Shape::Ref(_) => return None,
    })
}

impl Shape {
    /// Make tuples whose components all belong to one family homogeneous
    /// (every position gets the join of all positions), recursively. Such
    /// tuples usually model arrays indexed by a variable (`f[i]`), which
    /// can only be compiled to a dynamic index if all slots have the same
    /// encoding; it also avoids one layout miss per position.
    pub fn homogenize(&self) -> Shape {
        match self {
            Shape::Set { elem, max_card } => Shape::Set { elem: Box::new(elem.homogenize()), max_card: *max_card },
            Shape::Seq { elem, max_len } => Shape::Seq { elem: Box::new(elem.homogenize()), max_len: *max_len },
            Shape::Fcn { dom, range } => Shape::Fcn { dom: dom.clone(), range: Box::new(range.homogenize()) },
            Shape::Map { key, range } => Shape::Map { key: key.clone(), range: Box::new(range.homogenize()) },
            Shape::Record(fs) => Shape::Record(fs.iter().map(|(k, f)| (*k, f.homogenize())).collect()),
            Shape::Union(arms) => Shape::Union(arms.iter().map(Shape::homogenize).collect()),
            Shape::Tuple(es) => {
                let es: Vec<Shape> = es.iter().map(Shape::homogenize).collect();
                if es.len() >= 2 {
                    let j = es[1..].iter().fold(es[0].clone(), |acc, e| acc.join(e));
                    // One family, or already-mixed slots (some position is a
                    // union): an array whose slots share one encoding.
                    let one_family = es.windows(2).all(|w| same_family(&w[0], &w[1])) && !matches!(j, Shape::Union(_));
                    let mixed = es.iter().any(|e| matches!(e, Shape::Union(_))) && matches!(j, Shape::Union(_));
                    if (one_family || mixed) && !matches!(j, Shape::Dyn) && es.iter().all(|e| j.covers(e)) {
                        return Shape::Tuple(vec![j; es.len()].into());
                    }
                }
                Shape::Tuple(es.into())
            }
            _ => self.clone(),
        }
    }

    /// Whether every value of `other` is a value of `self` (structural, for
    /// shapes of the same family).
    fn covers(&self, other: &Shape) -> bool {
        self.join(other) == *self
    }
}

fn same_family(a: &Shape, b: &Shape) -> bool {
    match (family(a), family(b)) {
        (Some(Family::Record(x)), Some(Family::Record(y))) => same_field_names(x, y),
        (Some(Family::Record(_)), _) | (_, Some(Family::Record(_))) => false,
        (Some(x), Some(y)) => x == y,
        _ => false,
    }
}

/// Join of shapes of the same family.
fn join_same(a: &Shape, b: &Shape) -> Shape {
    match (a, b) {
        (Shape::Bool, Shape::Bool) => Shape::Bool,
        (Shape::Int { lo: l1, hi: h1 }, Shape::Int { lo: l2, hi: h2 }) => Shape::Int { lo: (*l1).min(*l2), hi: (*h1).max(*h2) },
        (Shape::Atom(x), Shape::Atom(y)) => Shape::Atom(merge_atoms(x, y)),
        (Shape::Set { elem: e1, max_card: m1 }, Shape::Set { elem: e2, max_card: m2 }) => {
            Shape::Set { elem: Box::new(e1.join(e2)), max_card: (*m1).max(*m2) }
        }
        (Shape::Fcn { dom: d1, range: r1 }, Shape::Fcn { dom: d2, range: r2 }) if d1 == d2 => {
            Shape::Fcn { dom: d1.clone(), range: Box::new(r1.join(r2)) }
        }
        (Shape::Fcn { .. } | Shape::Map { .. }, Shape::Fcn { .. } | Shape::Map { .. }) => {
            // Functions with different domains: a map over the union.
            let (k1, r1) = map_view(a);
            let (k2, r2) = map_view(b);
            map_shape(k1.join(&k2), r1.join(&r2))
        }
        (Shape::Record(x), Shape::Record(y)) => Shape::Record(x.iter().zip(y.iter()).map(|(p, q)| (p.0, p.1.join(&q.1))).collect()),
        (Shape::Tuple(x), Shape::Tuple(y)) if x.len() == y.len() => Shape::Tuple(x.iter().zip(y.iter()).map(|(p, q)| p.join(q)).collect()),
        _ => {
            // Tuple/Seq of different lengths: a sequence.
            let (e1, l1) = seq_view(a);
            let (e2, l2) = seq_view(b);
            Shape::Seq { elem: Box::new(e1.join(&e2)), max_len: l1.max(l2) }
        }
    }
}

fn is_seq_like(s: &Shape) -> bool {
    matches!(s, Shape::Tuple(_) | Shape::Seq { .. })
}

/// Join of tuple and sequence shapes (the seq-like arms of a union): one
/// `Tuple` if all have the same length; tuple arms discriminated by length
/// (sorted by length, i.e. in TLC order) if the values look like
/// alternatives with positional types rather than a sequence (see
/// `tuple_alternatives`); otherwise one `Seq`.
fn join_seq_like(shapes: Vec<Shape>) -> Vec<Shape> {
    let mut by_len: Vec<Shape> = Vec::new();
    let mut seq = false;
    for s in &shapes {
        match s {
            Shape::Tuple(es) => match by_len.iter_mut().find(|t| matches!(t, Shape::Tuple(x) if x.len() == es.len())) {
                Some(t) => *t = join_same(t, s),
                None => by_len.push(s.clone()),
            },
            _ => seq = true,
        }
    }
    if !seq && (by_len.len() == 1 || tuple_alternatives(&by_len)) {
        by_len.sort_by_key(|t| match t {
            Shape::Tuple(es) => es.len(),
            _ => unreachable!(),
        });
        return by_len;
    }
    let mut it = shapes.into_iter();
    let first = it.next().expect("seq-like shapes");
    vec![it.fold(first, |acc, s| join_same(&acc, &s))]
}

/// Whether tuples of these (distinct) lengths are kept apart as union arms
/// instead of being joined into a sequence: every non-empty one has
/// components of different families (positional types, like a
/// `<<node, round>>` pair next to an empty `<<>>` default), and there are
/// few of them. A sequence that grows element by element passes through
/// length 1, whose tuple is never mixed, so such values stay a `Seq`.
fn tuple_alternatives(tuples: &[Shape]) -> bool {
    tuples.len() <= MAX_TUPLE_ARMS
        && tuples.iter().all(|t| match t {
            Shape::Tuple(es) => es.is_empty() || es.windows(2).any(|w| !same_family(&w[0], &w[1])),
            _ => false,
        })
}

/// Key and range shapes of a function or map shape.
fn map_view(s: &Shape) -> (Shape, Shape) {
    match s {
        Shape::Fcn { dom, range } => (join_all(dom.iter().map(Shape::of)), (**range).clone()),
        Shape::Map { key, range } => ((**key).clone(), (**range).clone()),
        _ => unreachable!("map_view on {s:?}"),
    }
}

/// Keys whose rank order is TLC's value order (so a map's domain is
/// enumerated like TLC's). (`order_safe` in tlx-compile's lowering also
/// accepts unions of tuples, which TLC orders by length first; map keys do
/// not, which keeps the choice of map shapes as it is.)
fn map_key_ok(s: &Shape) -> bool {
    match s {
        _ if s.is_scalar() => true,
        Shape::Record(fs) => fs.iter().all(|(_, f)| map_key_ok(f)),
        Shape::Tuple(es) => es.iter().all(map_key_ok),
        Shape::Union(arms) => arms.iter().all(|a| matches!(a, Shape::Record(_)) && map_key_ok(a)),
        _ => false,
    }
}

/// `Map { key, range }` if it has a compact encoding, else `Dyn`.
pub fn map_shape(key: Shape, range: Shape) -> Shape {
    use crate::decisions::{note, summary};
    let Some(u) = crate::layout::bitset_universe(&key) else {
        note(|| format!("Dyn: function keys {} have no finite universe of at most 4096 values", summary(&key)));
        return Shape::Dyn;
    };
    let w = crate::layout::MapDims::new(u as usize, crate::pack::SlotLayout::of(&range)).words();
    if !map_key_ok(&key) || w > MAX_MAP_WORDS || range == Shape::Dyn {
        note(|| {
            if !map_key_ok(&key) {
                format!("Dyn: function keys {} have no encoding in TLC order (universe {u})", summary(&key))
            } else if w > MAX_MAP_WORDS {
                format!("Dyn: map of {u} keys to {} needs {w} words, more than {MAX_MAP_WORDS}", summary(&range))
            } else {
                format!("Dyn: function values are Dyn (keys {})", summary(&key))
            }
        });
        return Shape::Dyn;
    }
    Shape::Map { key: Box::new(key), range: Box::new(range) }
}

/// Whether a value of the tuple / sequence or record shape `a` can equal
/// a value of the function or map shape `b`: a function built over an
/// enumerated domain (`Value::Fcn`) is equal to the tuple / record with the
/// same pairs. Such shapes must not become separate union arms (equal values
/// would get different encodings, hence different fingerprints).
fn equal_values_possible(a: &Shape, b: &Shape) -> bool {
    match (a, b) {
        // In TLA+, `[k \in {} |-> v]` equals `<<>>`, so any `Map` shares the
        // empty value `<<>>` with `Seq` and empty `Tuple`.
        (Shape::Seq { .. }, Shape::Map { .. }) | (Shape::Map { .. }, Shape::Seq { .. }) => return true,
        (Shape::Tuple(es), Shape::Map { .. }) | (Shape::Map { .. }, Shape::Tuple(es)) if es.is_empty() => return true,
        _ => {}
    }
    let keys = match b {
        Shape::Fcn { dom, .. } => match dom.first() {
            None => return is_seq_like(a),
            Some(Value::Int(_)) => KeyKind::Int,
            Some(Value::Str(_)) => KeyKind::Str,
            _ => return false,
        },
        Shape::Map { key, .. } => match &**key {
            Shape::Int { .. } => KeyKind::Int,
            Shape::Atom(u) if u.iter().any(|k| matches!(k, Value::Str(_))) => KeyKind::Str,
            _ => return false,
        },
        _ => return false,
    };
    match a {
        Shape::Tuple(_) | Shape::Seq { .. } => keys == KeyKind::Int,
        Shape::Record(_) => keys == KeyKind::Str,
        _ => false,
    }
}

#[derive(PartialEq)]
enum KeyKind {
    Int,
    Str,
}

/// Key and range shapes of a tuple, sequence or record shape seen as a map.
fn fcn_view(s: &Shape) -> (Shape, Shape) {
    match s {
        Shape::Record(fs) => (join_all(fs.iter().map(|(k, _)| Shape::of(&Value::Str(*k)))), join_all(fs.iter().map(|(_, f)| f.clone()))),
        Shape::Tuple(_) | Shape::Seq { .. } => {
            let (e, n) = seq_view(s);
            (if n == 0 { Shape::Never } else { Shape::Int { lo: 1, hi: n as i64 } }, e)
        }
        _ => map_view(s),
    }
}

/// Merge union arms that can hold equal values (`equal_values_possible`)
/// into one map; false if that has no compact encoding (the join is then
/// `Dyn`).
fn merge_equal_arms(arms: &mut Vec<Shape>) -> bool {
    loop {
        let pair =
            (0..arms.len()).find_map(|i| (0..arms.len()).find(|&j| j != i && equal_values_possible(&arms[i], &arms[j])).map(|j| (i, j)));
        let Some((i, j)) = pair else { return true };
        let (k1, r1) = fcn_view(&arms[i]);
        let (k2, r2) = fcn_view(&arms[j]);
        let m = map_shape(k1.join(&k2), r1.join(&r2));
        if m == Shape::Dyn {
            return false;
        }
        let (lo, hi) = (i.min(j), i.max(j));
        arms.remove(hi);
        arms[lo] = m;
        // (A map may now be joined with another map arm of the same family.)
        if let Some(k) = (0..arms.len()).find(|&k| k != lo && same_family(&arms[k], &arms[lo])) {
            let j = join_same(&arms[k], &arms[lo]);
            if j == Shape::Dyn {
                return false;
            }
            let (lo2, hi2) = (k.min(lo), k.max(lo));
            arms.remove(hi2);
            arms[lo2] = j;
        }
    }
}

/// Element shape and maximal length of a tuple or sequence shape.
fn seq_view(s: &Shape) -> (Shape, usize) {
    match s {
        Shape::Tuple(es) => (join_all(es.iter().cloned()), es.len()),
        Shape::Seq { elem, max_len } => ((**elem).clone(), *max_len),
        _ => unreachable!("seq_view on {s:?}"),
    }
}

fn merge_atoms(x: &Arc<[Value]>, y: &Arc<[Value]>) -> Arc<[Value]> {
    if y.iter().all(|v| x.binary_search(v).is_ok()) {
        return x.clone();
    }
    if x.iter().all(|v| y.binary_search(v).is_ok()) {
        return y.clone();
    }
    let mut out: Vec<Value> = Vec::with_capacity(x.len() + y.len());
    let (mut i, mut j) = (0, 0);
    while i < x.len() && j < y.len() {
        match x[i].cmp(&y[j]) {
            std::cmp::Ordering::Less => {
                out.push(x[i].clone());
                i += 1;
            }
            std::cmp::Ordering::Greater => {
                out.push(y[j].clone());
                j += 1;
            }
            std::cmp::Ordering::Equal => {
                out.push(x[i].clone());
                i += 1;
                j += 1;
            }
        }
    }
    out.extend_from_slice(&x[i..]);
    out.extend_from_slice(&y[j..]);
    Arc::from(out)
}

/// Join of any number of shapes (`Never` for none).
pub fn join_all(shapes: impl IntoIterator<Item = Shape>) -> Shape {
    let mut acc = Shape::Never;
    for s in shapes {
        acc = acc.join(&s);
        if acc == Shape::Dyn {
            break;
        }
    }
    acc
}

fn arms_of(s: &Shape) -> &[Shape] {
    match s {
        Shape::Union(arms) => arms,
        _ => std::slice::from_ref(s),
    }
}

/// Binomial coefficient, `None` on u64 overflow.
pub(crate) fn binom(n: u64, k: u64) -> Option<u64> {
    if k > n {
        return Some(0);
    }
    let k = k.min(n - k);
    let mut c: u128 = 1;
    for i in 0..k {
        c = c * (n - i) as u128 / (i + 1) as u128;
        if c > u64::MAX as u128 {
            return None;
        }
    }
    Some(c as u64)
}

/// Elements of a (normalized) set value; `None` if `v` is not an enumerated
/// set or interval.
pub(crate) fn set_elems(v: &Value) -> Option<Cow<'_, [Value]>> {
    match v {
        Value::Set(es) => Some(Cow::Borrowed(&es[..])),
        Value::Interval(lo, hi) => Some(Cow::Owned((*lo..=*hi).map(Value::Int).collect())),
        _ => None,
    }
}

/// Number of elements of a set value without materializing intervals.
pub(crate) fn set_len(v: &Value) -> Option<u64> {
    match v {
        Value::Set(es) => Some(es.len() as u64),
        Value::Interval(lo, hi) => Some(if hi < lo { 0 } else { (hi - lo) as u64 + 1 }),
        _ => None,
    }
}

/// Normalize a lazy value (`None` if it cannot be normalized); non-lazy
/// values are returned as is.
/// `v` in the function representation of a shape that holds functions
/// (`to_fcn`: `Shape::Fcn`) or tuples / sequences / records: a function
/// built over an enumerated domain `1..n` or set of strings (a `Value::Fcn`,
/// see `tlx_value::FcnKind`) equals the `Tuple` / `Record` with the same
/// pairs, so it is encoded as one in a tuple, sequence or record shape, and
/// a `Tuple` / `Record` as such an `Fcn` in a function shape. (Decoding gives
/// the shape's representation.)
pub(crate) fn fit_repr(to_fcn: bool, v: Cow<'_, Value>) -> Cow<'_, Value> {
    match &*v {
        Value::Fcn(..) if !to_fcn => match v.fcn_canonical() {
            Some(c) => Cow::Owned(c),
            None => v,
        },
        Value::Tuple(_) | Value::Record(_) if to_fcn => Cow::Owned(v.into_owned().into_fcn_rcd()),
        _ => v,
    }
}

/// `fit_repr` for a value encoded in shape `s`.
pub(crate) fn fit_shape<'a>(s: &Shape, v: Cow<'a, Value>) -> Cow<'a, Value> {
    match s {
        Shape::Fcn { .. } => fit_repr(true, v),
        Shape::Tuple(_) | Shape::Seq { .. } | Shape::Record(_) => fit_repr(false, v),
        _ => v,
    }
}

pub(crate) fn force(v: &Value) -> Option<Cow<'_, Value>> {
    match v {
        Value::LazySet(_) | Value::LazyFcn(_) => {
            v.normalize().ok().filter(|n| !matches!(n, Value::LazySet(_) | Value::LazyFcn(_))).map(Cow::Owned)
        }
        _ => Some(Cow::Borrowed(v)),
    }
}

impl Shape {
    /// The most precise shape of a single (normalized) value.
    pub fn of(v: &Value) -> Shape {
        match v {
            Value::Bool(_) => Shape::Bool,
            Value::Int(n) => Shape::Int { lo: *n, hi: *n },
            Value::Str(_) | Value::ModelValue(_) => Shape::Atom(Arc::from(vec![v.clone()])),
            Value::Set(es) => Shape::Set { elem: Box::new(join_all(es.iter().map(Shape::of))), max_card: es.len() },
            Value::Interval(lo, hi) => {
                if hi < lo {
                    Shape::Set { elem: Box::new(Shape::Never), max_card: 0 }
                } else {
                    Shape::Set { elem: Box::new(Shape::Int { lo: *lo, hi: *hi }), max_card: (hi - lo) as usize + 1 }
                }
            }
            Value::Tuple(es) => Shape::Tuple(es.iter().map(Shape::of).collect()),
            Value::Record(fs) => Shape::Record(fs.iter().map(|(k, x)| (*k, Shape::of(x))).collect()),
            Value::Fcn(ps, _) => {
                Shape::Fcn { dom: ps.iter().map(|p| p.0.clone()).collect(), range: Box::new(join_all(ps.iter().map(|p| Shape::of(&p.1)))) }
            }
            Value::LazySet(_) | Value::LazyFcn(_) => match force(v) {
                Some(n) => Shape::of(&n),
                None => Shape::Dyn,
            },
        }
    }

    /// Least upper bound (with collapse to `Dyn` when unions grow too large).
    pub fn join(&self, other: &Shape) -> Shape {
        match (self, other) {
            (Shape::Never, x) | (x, Shape::Never) => return x.clone(),
            (Shape::Dyn | Shape::Ref(_), _) | (_, Shape::Dyn | Shape::Ref(_)) => return Shape::Dyn,
            _ => {}
        }
        if is_seq_like(self) && is_seq_like(other) {
            let mut arms = join_seq_like(vec![self.clone(), other.clone()]);
            return if arms.len() == 1 { arms.pop().unwrap() } else { Shape::Union(Arc::from(arms)) };
        }
        if same_family(self, other) {
            return join_same(self, other);
        }
        // Tuples are functions on `1..n` (the empty one, `<<>>`, is also an
        // empty map): with other functions they form a map.
        match (self, other) {
            (s @ (Shape::Tuple(_) | Shape::Seq { .. }), m @ (Shape::Fcn { .. } | Shape::Map { .. }))
            | (m @ (Shape::Fcn { .. } | Shape::Map { .. }), s @ (Shape::Tuple(_) | Shape::Seq { .. })) => {
                let (k, r) = map_view(m);
                let (e, n) = seq_view(s);
                if n == 0 {
                    return map_shape(k, r);
                }
                let j = map_shape(k.join(&Shape::Int { lo: 1, hi: n as i64 }), r.join(&e));
                if j != Shape::Dyn || equal_values_possible(s, m) {
                    return j;
                }
            }
            _ => {}
        }
        let mut arms: Vec<Shape> = Vec::new();
        let mut seqs: Vec<Shape> = Vec::new();
        for b in arms_of(self).iter().chain(arms_of(other)) {
            if is_seq_like(b) {
                seqs.push(b.clone());
                continue;
            }
            match arms.iter().position(|a| same_family(a, b)) {
                Some(i) => {
                    let j = join_same(&arms[i], b);
                    if j == Shape::Dyn {
                        return Shape::Dyn;
                    }
                    arms[i] = j;
                }
                None => arms.push(b.clone()),
            }
        }
        if !seqs.is_empty() {
            arms.extend(join_seq_like(seqs));
        }
        if !merge_equal_arms(&mut arms) {
            crate::decisions::note(|| "Dyn: equal values would fall into different union arms".to_string());
            return Shape::Dyn;
        }
        if arms.len() == 1 {
            return arms.pop().unwrap();
        }
        if arms.len() > MAX_UNION_ARMS {
            crate::decisions::note(|| format!("Dyn: values of more than {MAX_UNION_ARMS} kinds (union arms)"));
            return Shape::Dyn;
        }
        arms.sort_by_cached_key(|a| a.kind_key());
        Shape::Union(Arc::from(arms))
    }

    /// Scalars (`Int`, `Atom`, `Bool`): encoded in one word, equal to their
    /// rank (see `layout`).
    pub fn is_scalar(&self) -> bool {
        matches!(self, Shape::Int { .. } | Shape::Atom(_) | Shape::Bool)
    }

    /// Call `f` on each directly nested shape, in order: the element of a
    /// set or sequence, the range of a function, the key then the range of
    /// a map, the fields of a record, the components of a tuple, the arms
    /// of a union.
    pub fn for_each_child(&self, mut f: impl FnMut(&Shape)) {
        match self {
            Shape::Set { elem, .. } | Shape::Seq { elem, .. } => f(elem),
            Shape::Fcn { range, .. } => f(range),
            Shape::Map { key, range } => {
                f(key);
                f(range);
            }
            Shape::Record(fs) => fs.iter().for_each(|(_, x)| f(x)),
            Shape::Tuple(es) | Shape::Union(es) => es.iter().for_each(f),
            Shape::Never | Shape::Bool | Shape::Int { .. } | Shape::Atom(_) | Shape::Dyn | Shape::Ref(_) => {}
        }
    }

    pub fn kind_key(&self) -> Option<KindKey> {
        Some(match self {
            Shape::Bool => KindKey::Bool,
            Shape::Int { .. } => KindKey::Int,
            Shape::Atom(_) => KindKey::Atom,
            Shape::Set { .. } => KindKey::Set,
            Shape::Fcn { dom, .. } => KindKey::Fcn(dom.clone()),
            Shape::Map { .. } => KindKey::Map,
            Shape::Record(fs) => KindKey::Record(fs.len(), fs.iter().map(|f| f.0).collect()),
            Shape::Tuple(es) => KindKey::Tuple(es.len()),
            Shape::Seq { .. } => KindKey::Seq,
            Shape::Never | Shape::Union(_) | Shape::Dyn | Shape::Ref(_) => return None,
        })
    }

    /// Number of distinct values of this shape, if finite and representable
    /// in u64 (`None` = infinite/too large).
    pub fn cardinality(&self) -> Option<u64> {
        match self {
            Shape::Never => Some(0),
            Shape::Bool => Some(2),
            Shape::Int { lo, hi } => {
                let n = (*hi as i128) - (*lo as i128) + 1;
                u64::try_from(n.max(0)).ok()
            }
            Shape::Atom(u) => Some(u.len() as u64),
            Shape::Set { elem, max_card } => {
                let n = elem.cardinality()?;
                let m = *max_card as u64;
                if m >= n {
                    return if n < 64 { Some(1u64 << n) } else { None };
                }
                let mut total: u64 = 0;
                for j in 0..=m {
                    total = total.checked_add(binom(n, j)?)?;
                }
                Some(total)
            }
            Shape::Fcn { dom, range } => checked_pow(range.cardinality()?, dom.len()),
            // Sum over domains D of |range|^|D| = (|range| + 1)^|universe|.
            Shape::Map { key, range } => checked_pow(range.cardinality()?.checked_add(1)?, usize::try_from(key.cardinality()?).ok()?),
            Shape::Record(fs) => fs.iter().try_fold(1u64, |acc, f| acc.checked_mul(f.1.cardinality()?)),
            Shape::Tuple(es) => es.iter().try_fold(1u64, |acc, e| acc.checked_mul(e.cardinality()?)),
            Shape::Seq { elem, max_len } => {
                let c = elem.cardinality()?;
                match c {
                    0 => Some(1),
                    1 => (*max_len as u64).checked_add(1),
                    _ => {
                        let mut total: u64 = 0;
                        for l in 0..=*max_len {
                            total = total.checked_add(checked_pow(c, l)?)?;
                        }
                        Some(total)
                    }
                }
            }
            Shape::Union(arms) => arms.iter().try_fold(0u64, |acc, a| acc.checked_add(a.cardinality()?)),
            Shape::Dyn | Shape::Ref(_) => None,
        }
    }

    /// Whether `v` is described by this shape (encoding would succeed).
    pub fn contains(&self, v: &Value) -> bool {
        if let Shape::Ref(_) = self {
            // Every finite value has a store representation.
            return v.normalize().is_ok_and(|n| n.is_normal());
        }
        let Some(v) = force(v) else { return matches!(self, Shape::Dyn) };
        let v = fit_shape(self, v);
        let v = &*v;
        match (self, v) {
            (Shape::Dyn, _) => true,
            (Shape::Bool, Value::Bool(_)) => true,
            (Shape::Int { lo, hi }, Value::Int(n)) => lo <= n && n <= hi,
            (Shape::Atom(u), Value::Str(_) | Value::ModelValue(_)) => u.binary_search(v).is_ok(),
            (Shape::Set { elem, max_card }, Value::Set(_) | Value::Interval(..)) => {
                if set_len(v).unwrap() > *max_card as u64 {
                    return false;
                }
                set_elems(v).unwrap().iter().all(|e| elem.contains(e))
            }
            (Shape::Fcn { dom, range }, Value::Fcn(ps, _)) => {
                ps.len() == dom.len() && ps.iter().zip(dom.iter()).all(|(p, d)| p.0 == *d) && ps.iter().all(|p| range.contains(&p.1))
            }
            (Shape::Record(fs), Value::Record(vs)) => {
                fs.len() == vs.len() && fs.iter().zip(vs.iter()).all(|(f, x)| f.0 == x.0 && f.1.contains(&x.1))
            }
            (Shape::Map { key, range }, _) => match fcn_pairs(v) {
                Some(ps) => ps.iter().all(|(k, x)| key.contains(k) && range.contains(x)),
                None => false,
            },
            (Shape::Tuple(ss), Value::Tuple(vs)) => ss.len() == vs.len() && ss.iter().zip(vs.iter()).all(|(s, x)| s.contains(x)),
            (Shape::Seq { elem, max_len }, Value::Tuple(vs)) => vs.len() <= *max_len && vs.iter().all(|x| elem.contains(x)),
            (Shape::Union(arms), _) => match arm_for(arms, v) {
                Some(i) => arms[i].contains(v),
                None => false,
            },
            _ => false,
        }
    }
}

/// The (key, value) pairs of a function value (tuples and records are
/// functions too); `None` if `v` is not a function.
pub(crate) fn fcn_pairs(v: &Value) -> Option<Vec<(Value, Value)>> {
    match v {
        Value::Fcn(ps, _) => Some(ps.to_vec()),
        Value::Tuple(es) => Some(es.iter().enumerate().map(|(i, x)| (Value::Int(i as i64 + 1), x.clone())).collect()),
        Value::Record(fs) => Some(fs.iter().map(|(k, x)| (Value::Str(*k), x.clone())).collect()),
        _ => None,
    }
}

fn checked_pow(base: u64, exp: usize) -> Option<u64> {
    base.checked_pow(u32::try_from(exp).ok()?)
}

/// Index of the union arm whose kind matches the (normalized) value `v`.
pub(crate) fn arm_for(arms: &[Shape], v: &Value) -> Option<usize> {
    let direct = arms.iter().position(|a| match (a, v) {
        (Shape::Bool, Value::Bool(_))
        | (Shape::Int { .. }, Value::Int(_))
        | (Shape::Atom(_), Value::Str(_) | Value::ModelValue(_))
        | (Shape::Set { .. }, Value::Set(_) | Value::Interval(..))
        | (Shape::Seq { .. }, Value::Tuple(_))
        | (Shape::Fcn { .. } | Shape::Map { .. }, Value::Fcn(..)) => true,
        // Tuple arms are discriminated by length.
        (Shape::Tuple(ss), Value::Tuple(vs)) => ss.len() == vs.len(),
        (Shape::Record(fs), Value::Record(vs)) => same_field_names(fs, vs),
        _ => false,
    });
    // Tuples and records are functions too: a map arm takes them otherwise,
    // or a function arm over their domain; a function over an enumerated
    // `1..n` or set of strings goes to a tuple / sequence / record arm (see
    // `fit_repr`).
    direct.or_else(|| match v {
        Value::Tuple(_) | Value::Record(_) => arms.iter().position(|a| matches!(a, Shape::Map { .. })).or_else(|| {
            let Value::Fcn(ps, _) = v.clone().into_fcn_rcd() else { return None };
            arms.iter().position(
                |a| matches!(a, Shape::Fcn { dom, .. } if ps.len() == dom.len() && ps.iter().zip(dom.iter()).all(|(p, d)| p.0 == *d)),
            )
        }),
        Value::Fcn(..) => v.fcn_canonical().and_then(|c| arm_for(arms, &c)),
        _ => None,
    })
}

/// Whether two field lists have the same names in the same order.
#[inline]
pub(crate) fn same_field_names<A, B>(a: &[(Sym, A)], b: &[(Sym, B)]) -> bool {
    a.len() == b.len() && a.iter().zip(b).all(|(x, y)| x.0 == y.0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty_fcn_union_canonicality() {
        let atom_map =
            Shape::Map { key: Box::new(Shape::Atom(Arc::from([Value::Str(Sym::new("a"))]))), range: Box::new(Shape::Int { lo: 1, hi: 2 }) };
        let seq = Shape::Seq { elem: Box::new(Shape::Int { lo: 1, hi: 2 }), max_len: 2 };
        let empty_tuple = Shape::Tuple(Arc::from([]));
        let one_tuple = Shape::Tuple(Arc::from([Shape::Int { lo: 1, hi: 2 }]));

        // `Map` and `Seq` both admit `<<>>`, so joining an Atom-keyed `Map`
        // with `Seq` must widen to `Dyn` rather than forming a non-canonical `Union`.
        assert_eq!(atom_map.join(&seq), Shape::Dyn);
        assert_eq!(seq.join(&atom_map), Shape::Dyn);

        // `Tuple([])` is absorbed into `Map` (its empty map represents `<<>>`).
        assert_eq!(atom_map.join(&empty_tuple), atom_map);
        assert_eq!(empty_tuple.join(&atom_map), atom_map);

        // Through `merge_equal_arms` inside a multi-arm `Union`:
        let bool_or_map = Shape::Bool.join(&atom_map);
        assert_eq!(bool_or_map.join(&seq), Shape::Dyn);
        assert_eq!(bool_or_map.join(&empty_tuple), bool_or_map);

        // A non-empty `Tuple` cannot hold `<<>>` and has Int keys, so it stays
        // a disjoint `Union` arm with an Atom-keyed `Map`.
        assert!(matches!(atom_map.join(&one_tuple), Shape::Union(arms) if arms.len() == 2));
    }
}
