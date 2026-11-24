//! Constant values in encodings: encoding at compile time, and choosing
//! shapes for constants that do not come with one. Chosen shapes reuse the
//! atom universes and integer ranges already interned (those of the state
//! layout come first), so that constant elements compare and index
//! directly with state values.

use tlx_value::ops::{cardinality, cardinality_of_normalized, enumerate_normalized, for_each_enumerated, normalize_enumerated};
use tlx_value::{Sym, Value};

use super::*;

/// Most elements of a constant set to encode as a list or bitset.
const MAX_CONST_ELEMS: usize = 4096;

/// Most elements of a constant set to list in a variable's encoding.
const MAX_LISTED_ELEMS: usize = 1 << 16;

/// Most elements of a constant tuple, and points of a constant function,
/// that `fit_shape` gives a shape of its own (a part per element, a slot
/// per point): of scalars (a lookup table), and of other values. A larger
/// one (a trace validation's log of thousands of records) stays a value:
/// fitting and encoding it at every use would cost its size each time, and
/// its shape would be as large.
const MAX_FIT_SCALARS: usize = MAX_CONST_ELEMS;
const MAX_FIT_PARTS: usize = 64;

/// Whether `fit_shape` gives `n` elements or points `vs` a part each.
fn fits_parts<'v>(n: usize, mut vs: impl Iterator<Item = &'v Value>) -> bool {
    n <= MAX_FIT_PARTS
        || n <= MAX_FIT_SCALARS && vs.all(|v| matches!(v, Value::Int(_) | Value::Bool(_) | Value::Str(_) | Value::ModelValue(_)))
}

impl Lowerer<'_> {
    /// Encode a constant into shape `sid` at compile time (preserving witness).
    pub(super) fn const_words(&self, v: &Value, sid: ShapeId) -> Option<Expr> {
        let t = &self.typing;
        let mut out = vec![0u64; t.words(sid) as usize];
        tlx_layout::layout::encode(t.shape(sid), &v.normalize().ok()?, &mut out).ok()?;
        Some(Expr::new(Ty::Enc(sid), ExprKind::ConstWords(out.into())))
    }

    /// Encode a constant into shape `sid` at compile time ignoring
    /// function-domain construction witnesses (for semantic equality/membership).
    pub(super) fn const_words_semantic(&self, v: &Value, sid: ShapeId) -> Option<Expr> {
        let t = &self.typing;
        let mut out = vec![0u64; t.words(sid) as usize];
        tlx_layout::layout::encode_semantic(t.shape(sid), &v.normalize().ok()?, &mut out).ok()?;
        Some(Expr::new(Ty::Enc(sid), ExprKind::ConstWords(out.into())))
    }

    /// Encode a constant set or interval into `Shape::Set` `sid`, preserving
    /// exact element witnesses (for `Value::Interval`, every element is a plain
    /// integer with no alternative witness, so only the outer interval tag is
    /// dropped).
    pub(super) fn const_set_words_exact_elems(&self, v: &Value, sid: ShapeId) -> Option<Expr> {
        match v {
            Value::Interval(..) => self.const_words_semantic(v, sid),
            _ => self.const_words(v, sid),
        }
    }

    /// The elements of constant set `v` (TLC enumeration order, as the
    /// interpreter enumerates them) encoded in shape `es`.
    pub(super) fn const_elems(&mut self, v: &Value, es: &Shape) -> Option<(Expr, Ty)> {
        let elems = enumerate_listed(v)?.ok()?;
        self.encode_elems(&elems, es)
    }

    /// `const_elems` of a set whose enumeration is `elems`.
    fn encode_elems(&mut self, elems: &[Value], es: &Shape) -> Option<(Expr, Ty)> {
        if elems.is_empty() || elems.len() > MAX_LISTED_ELEMS {
            return None;
        }
        let esid = self.sid(es);
        let n = self.words_of(es) as usize;
        let mut words = Vec::with_capacity(n * elems.len());
        for x in elems {
            let mut w = vec![0u64; n];
            tlx_layout::layout::encode(es, &x.normalize().ok()?, &mut w).ok()?;
            words.extend(w);
        }
        let list = Expr::new(Ty::Val, ExprKind::ConstElems { elem: esid, words: words.into(), count: elems.len() as u32 });
        Some((list, Ty::Enc(esid)))
    }

    /// Iteration over constant set `v` in TLC order: a static list of
    /// encodings, or (failing that) the set encoded as a whole.
    pub(super) fn const_iter(&mut self, v: &Value) -> Option<(Expr, Ty)> {
        // (A set too large for either form is not enumerated: [D -> R] can
        // have millions of elements. Counted as it is enumerated first, so
        // a large set filter is not materialized just to be rejected.)
        // The one enumeration also gives the size, the normalized elements
        // and the listed encodings: a set filter `{x \in S : P}` evaluates
        // `P` on all of S on every enumeration (five of them made lowering
        // twice as slow on LoopInvariance/MCBinarySearch).
        let listed = enumerate_listed(v)?;
        let normalized = listed.as_ref().ok().map(|es| normalize_enumerated(v, es.clone()));
        let card = match &normalized {
            Some(Ok(ns)) => cardinality_of_normalized(v, ns),
            _ => cardinality(v),
        };
        if !card.is_ok_and(|n| n <= MAX_CONST_ELEMS as i64) {
            return None;
        }
        if let Some(elems) = normalized.and_then(|r| r.ok()).filter(|es| !es.is_empty() && es.len() <= MAX_CONST_ELEMS) {
            if let Some(es) = self.fit_shape(&elems) {
                let es = self.layout_seqs(&es);
                if let Some(x) = listed.as_ref().ok().and_then(|l| self.encode_elems(l, &es)) {
                    return Some(x);
                }
            }
        }
        let elem = self.const_elem_shape(v)?;
        let n = cardinality(v).unwrap_or(0) as usize;
        let ssid = self.sid(&Shape::Set { elem: Box::new(elem.clone()), max_card: n.max(1) });
        let c = self.const_set_words_exact_elems(v, ssid)?;
        let esid = self.sid(&elem);
        Some((c, Ty::Enc(esid)))
    }

    /// `s` with the homogeneous tuples in its record fields encoded as a
    /// sequence shape of the layout holding them (the smallest capacity
    /// that fits): the elements of `[elems: [1..n -> T]]` then have the
    /// shape of a state variable `[elems: Seq(T)]` and compare, slice and
    /// concatenate with it directly instead of being converted (a tuple of
    /// another length would not even convert).
    fn layout_seqs(&self, s: &Shape) -> Shape {
        let t = &self.typing;
        let layout_seq = |es: &[Shape]| -> Option<Shape> {
            let e = es.first()?;
            if es.iter().any(|x| x != e) {
                return None;
            }
            (0..t.num_shapes() as ShapeId)
                .filter(|&sid| t.in_layout(sid))
                .map(|sid| t.shape(sid))
                .filter(|sh| matches!(sh, Shape::Seq { elem, max_len } if **elem == *e && *max_len >= es.len()))
                .min_by_key(|sh| match sh {
                    Shape::Seq { max_len, .. } => *max_len,
                    _ => usize::MAX,
                })
                .cloned()
        };
        match s {
            Shape::Record(fs) => Shape::Record(
                fs.iter()
                    .map(|(n, f)| {
                        let f = match f {
                            Shape::Tuple(es) => layout_seq(es).unwrap_or_else(|| f.clone()),
                            _ => self.layout_seqs(f),
                        };
                        (*n, f)
                    })
                    .collect(),
            ),
            _ => s.clone(),
        }
    }

    /// A constant set of scalars as an encoded bitset.
    pub(super) fn const_bitset(&mut self, v: &Value) -> Option<Expr> {
        if !small_set(v) {
            return None;
        }
        let elems = enumerate_normalized(v).ok()?;
        if elems.is_empty() || elems.len() > MAX_CONST_ELEMS {
            return None;
        }
        let es = self.fit_shape(&elems)?;
        let card = es.cardinality()? as usize;
        let ssid = self.sid(&Shape::Set { elem: Box::new(es), max_card: card });
        if !self.is_bitset(Ty::Enc(ssid)) {
            return None;
        }
        self.const_set_words_exact_elems(v, ssid)
    }

    /// A shape describing all of `vals`, reusing the layout's atom universes
    /// and integer ranges where possible (so values compare and index
    /// directly with state values): ints, atoms, sets (bitsets over a reused
    /// universe), records and tuples of those.
    pub(super) fn fit_shape(&self, vals: &[Value]) -> Option<Shape> {
        if vals.is_empty() || vals.iter().any(typed::has_non_reducible_lazy_set) {
            return None;
        }
        if let Some((lo, hi)) = int_bounds(vals) {
            // Prefer an existing integer shape covering the values.
            let t = &self.typing;
            let covering = (0..t.num_shapes() as ShapeId)
                .map(|sid| t.shape(sid))
                .find(|s| matches!(s, Shape::Int { lo: a, hi: b } if *a <= lo && hi <= *b));
            return Some(covering.cloned().unwrap_or(Shape::Int { lo, hi }));
        }
        if vals.iter().all(|v| matches!(v, Value::Bool(_))) {
            return Some(Shape::Bool);
        }
        if vals.iter().all(|v| matches!(v, Value::ModelValue(_) | Value::Str(_))) {
            let s = Value::set_from(vals.to_vec()).ok()?;
            return self.const_elem_shape(&s);
        }
        if vals.iter().all(|v| matches!(v, Value::Set(_))) {
            let mut inner = Vec::new();
            let mut max_card = 0;
            for v in vals {
                let es = enumerate_normalized(v).ok()?;
                max_card = max_card.max(es.len());
                inner.extend(es);
            }
            if inner.is_empty() {
                // Every member is the empty set: the smallest element shape
                // that admits them (and every future value of a shape must
                // admit the encoded value, so a wider element shape buys
                // nothing here).
                return Some(Shape::Set { elem: Box::new(Shape::Never), max_card: 0 });
            }
            let elem = self.fit_shape(&inner)?;
            let card = elem.cardinality()? as usize;
            return Some(Shape::Set { elem: Box::new(elem), max_card: if card <= MAX_CONST_ELEMS { card } else { max_card } });
        }
        if let Some(Value::Record(first)) = vals.first() {
            if vals
                .iter()
                .any(|v| !matches!(v, Value::Record(fs) if fs.len() == first.len() && fs.iter().zip(first.iter()).all(|(a, b)| a.0 == b.0)))
            {
                // Records with different fields: an interned union of
                // records holding them all (e.g. a map's key shape).
                let t = &self.typing;
                return (0..t.num_shapes() as ShapeId)
                    .map(|sid| t.shape(sid))
                    .find(|s| {
                        matches!(s, Shape::Union(arms) if arms.iter().all(|a| matches!(a, Shape::Record(_))))
                            && vals.iter().all(|v| s.contains(v))
                    })
                    .cloned();
            }
            let names: Vec<Sym> = first.iter().map(|(n, _)| *n).collect();
            let mut fields = Vec::new();
            for (i, n) in names.iter().enumerate() {
                let col: Option<Vec<Value>> = vals
                    .iter()
                    .map(|v| match v {
                        Value::Record(fs) if fs.len() == names.len() && fs[i].0 == *n => Some(fs[i].1.clone()),
                        _ => None,
                    })
                    .collect();
                fields.push((*n, self.fit_shape(&col?)?));
            }
            return Some(Shape::Record(fields.into()));
        }
        if let Some(Value::Tuple(first)) = vals.first() {
            let len = first.len();
            if !vals.iter().all(|v| matches!(v, Value::Tuple(es) if fits_parts(es.len(), es.iter()))) {
                return None;
            }
            let mut parts = Vec::new();
            for i in 0..len {
                let col: Option<Vec<Value>> = vals
                    .iter()
                    .map(|v| match v {
                        Value::Tuple(es) if es.len() == len => Some(es[i].clone()),
                        _ => None,
                    })
                    .collect();
                parts.push(self.fit_shape(&col?)?);
            }
            unify_empty_sets(&mut parts);
            return Some(Shape::Tuple(parts.into()));
        }
        if let Some(Value::Fcn(first, dom_kind)) = vals.first() {
            // Functions with one (fixed) domain.
            if !fits_parts(first.len(), first.iter().map(|(_, x)| x)) {
                return None;
            }
            let dom: Vec<Value> = first.iter().map(|(k, _)| k.clone()).collect();
            let mut witness = tlx_layout::FcnWitness::from_dom(*dom_kind);
            let mut range = Vec::new();
            for v in vals {
                let Value::Fcn(ps, dk) = v else { return None };
                if ps.len() != dom.len() || ps.iter().zip(&dom).any(|((k, _), d)| !k.exact_eq(d)) {
                    return None;
                }
                witness = witness.join(tlx_layout::FcnWitness::from_dom(*dk));
                range.extend(ps.iter().map(|(_, x)| x.clone()));
            }
            let range = self.fit_shape(&range)?;
            return Some(Shape::Fcn { dom: dom.into(), range: Box::new(range), witness, key_variants: Arc::from([]) });
        }
        None
    }

    /// Element shape for iterating over a constant set: an integer range, or
    /// an atom universe (preferably one already interned, so that elements
    /// compare/index directly with state values).
    fn const_elem_shape(&self, v: &Value) -> Option<Shape> {
        let elems = enumerate_normalized(v).ok()?;
        if elems.is_empty() || elems.len() > MAX_CONST_ELEMS {
            return None;
        }
        if let Some((lo, hi)) = int_bounds(&elems) {
            return (hi - lo < MAX_CONST_ELEMS as i64).then_some(Shape::Int { lo, hi });
        }
        if !elems.iter().all(|e| matches!(e, Value::ModelValue(_) | Value::Str(_))) {
            return None;
        }
        let t = &self.typing;
        let existing = (0..t.num_shapes() as ShapeId)
            .map(|sid| t.shape(sid))
            .find(|s| matches!(s, Shape::Atom(u) if elems.iter().all(|e| u.contains(e))));
        Some(existing.cloned().unwrap_or_else(|| Shape::Atom(elems.into())))
    }
}

/// Give every component of a constant tuple that admits the empty set alone
/// the shape of its set-valued siblings, when those share one shape. The
/// empty set fits every `Set{elem}` shape, so no value of the constant is
/// lost, and the components then share a representation: an index into the
/// tuple selects one of them instead of falling back to a boxed application
/// (a tuple `<<{1}, {}>>` of a sequence member type, e.g. Accord's task
/// transaction sets, is the case that matters).
fn unify_empty_sets(parts: &mut [Shape]) {
    let mut widest: Option<Shape> = None;
    for p in parts.iter() {
        let Shape::Set { elem, .. } = p else { continue };
        if elem.cardinality() == Some(0) {
            continue;
        }
        match &widest {
            None => widest = Some(p.clone()),
            Some(w) if w == p => {}
            Some(_) => return,
        }
    }
    let Some(widest) = widest else { return };
    for p in parts.iter_mut() {
        if matches!(p, Shape::Set { elem, .. } if elem.cardinality() == Some(0)) {
            *p = widest.clone();
        }
    }
}

/// Whether constant set `v` has at most `MAX_CONST_ELEMS` elements (counted
/// without enumerating it where possible).
fn small_set(v: &Value) -> bool {
    cardinality(v).is_ok_and(|n| n <= MAX_CONST_ELEMS as i64)
}

/// Least and greatest of `vals` if they are all integers (and not empty).
fn int_bounds(vals: &[Value]) -> Option<(i64, i64)> {
    let ints: Vec<i64> = vals.iter().map(|v| if let Value::Int(i) = v { Some(*i) } else { None }).collect::<Option<_>>()?;
    Some((*ints.iter().min()?, *ints.iter().max()?))
}

/// `enumerate(v)` if it yields at most `MAX_LISTED_ELEMS` elements (an
/// error if it fails), else `None`. Collected as `v` is enumerated: a large
/// set filter over a set that is not enumerated (`{c \in [a: S, b: T] : P}`)
/// is not materialized just to be rejected.
fn enumerate_listed(v: &Value) -> Option<tlx_value::Result<Vec<Value>>> {
    let mut out = Vec::new();
    let r = for_each_enumerated(v, &mut |x| {
        if out.len() == MAX_LISTED_ELEMS {
            return Ok(false);
        }
        out.push(x);
        Ok(true)
    });
    match r {
        Ok(true) => Some(Ok(out)),
        Ok(false) => None,
        Err(e) => Some(Err(e)),
    }
}
