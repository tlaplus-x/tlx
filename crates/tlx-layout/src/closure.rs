//! When a layout slot provably accepts every value some expression can take
//! (`docs/scale.md` §6).
//!
//! The compiled tier keeps expanded states in the layout-miss archive only
//! while a later value can fail [`crate::layout::Layout::encode_state`]. A
//! slot whose shape accepts every value its assignments and materialized
//! definitions can produce cannot miss, so its archive can be elided.
//!
//! [`Shape::accepts_shape`] is the conservative containment test the driver's
//! closed-layout analysis uses. It answers "does every *finite* value of
//! `other` encode into a slot of shape `self` without a `Miss`?" and never
//! answers `true` for a value set it cannot bound: an over-approximating shape
//! (`Dyn`) is accepted only by `Dyn`/`Ref` slots. `StoreError::Full` from a
//! `Ref` slot is a hard value-store budget stop, not a layout miss, so `Ref`
//! accepts every value like `Dyn`.

use tlx_value::Value;

use crate::shape::{fcn_dom_exact_eq, fcn_dom_matches_record, fcn_dom_matches_tuple, values_exact_eq, Shape};

impl Shape {
    /// Whether this shape describes every value of `Ref`/`Dyn` slots: a slot
    /// of this shape encodes any finite value without a layout miss.
    pub fn is_unbounded(&self) -> bool {
        matches!(self, Shape::Dyn | Shape::Ref(_))
    }

    /// Whether every finite value described by `other` encodes into a slot of
    /// this shape without a layout miss.
    ///
    /// Conservative: `other` is a shape-level over-approximation of the values
    /// (see `tlx_compile::enc::closure`), and an unrecognized case returns
    /// `false` rather than guessing. The cases mirror `LayoutNode::enc_impl`:
    ///
    /// - `Dyn`/`Ref` accept any value (a `Ref` store-full error is not a miss);
    /// - `Bool`, `Int`, `Atom`, `Set`, `Record`, `Tuple`, `Seq`, `Union` accept
    ///   values of their kind whose leaves fit;
    /// - a fixed-domain `Fcn` accepts exactly its domain and construction
    ///   witness (unless the witness is `Dynamic`), and `Tuple`/`Record`
    ///   values only through a `Dynamic` witness with a matching domain;
    /// - a `Map` accepts functions, tuples and records (`Dynamic` witness) over
    ///   a subset of its key universe, of the shape's construction witness.
    pub fn accepts_shape(&self, other: &Shape) -> bool {
        use Shape::*;
        if self.is_unbounded() {
            return true;
        }
        if matches!(other, Never) {
            // `Never` describes no value (an empty set's element shape).
            return true;
        }
        if other.is_unbounded() {
            // `Dyn`/`Ref` values are beyond this slot's fixed shape.
            return false;
        }
        match (self, other) {
            (Never, _) => false,
            (Bool, Bool) => true,
            (Int { lo, hi }, Int { lo: olo, hi: ohi }) => lo <= olo && ohi <= hi,
            (Atom(u), Atom(v)) => v.iter().all(|x| u.binary_search(x).is_ok()),
            (Set { elem, max_card }, Set { elem: oelem, max_card: omax }) => omax <= max_card && elem.accepts_shape(oelem),
            (Fcn { dom, range, witness, key_variants }, Fcn { dom: odom, range: orange, witness: owitness, key_variants: okv }) => {
                // The slot's `match_fcn_keys_exact` accepts a key that is a
                // variant, and `dom[pos]` is `variants[0]`: a value shape
                // without alternate keys always matches. A value shape *with*
                // variants must use exactly the slot's variants, or a key this
                // slot cannot represent would be a miss.
                let dom_ok = values_exact_eq(dom, odom) && (okv.is_empty() || fcn_dom_exact_eq(dom, key_variants, odom, okv));
                dom_ok && witness.accepts(*owitness) && range.accepts_shape(orange)
            }
            (Fcn { dom, range, witness, key_variants }, Tuple(es)) => {
                *witness == crate::FcnWitness::Dynamic
                    && key_variants.is_empty()
                    && fcn_dom_matches_tuple(dom, es.len())
                    && es.iter().all(|e| range.accepts_shape(e))
            }
            (Fcn { dom, range, witness, key_variants }, Record(fs)) => {
                *witness == crate::FcnWitness::Dynamic
                    && key_variants.is_empty()
                    && fcn_dom_matches_record(dom, fs.as_ref())
                    && fs.iter().all(|(_, e)| range.accepts_shape(e))
            }
            (Map { key, range, witness }, Map { key: okey, range: orange, witness: owitness }) => {
                key.accepts_shape(okey) && witness.accepts_map(*owitness) && range.accepts_shape(orange)
            }
            (Map { key, range, witness }, Fcn { dom, range: orange, witness: owitness, key_variants }) => {
                (*witness == crate::FcnWitness::Dynamic || witness.accepts_map(*owitness))
                    // Every key (and every alternate key representation) must
                    // rank in the slot's finite universe.
                    && dom.iter().chain(key_variants.iter().flat_map(|(_, vs)| vs.iter())).all(|k| key.contains(k))
                    && range.accepts_shape(orange)
            }
            (Map { key, range, witness }, Tuple(es)) => {
                // `accepts_map_value`: `Dynamic` records any construction, an
                // `Interval` witness accepts tuples (their interval domain),
                // `Enumerated` does not.
                *witness != crate::FcnWitness::Enumerated
                    && (1..=es.len() as i64).all(|i| key.contains(&Value::Int(i)))
                    && es.iter().all(|e| range.accepts_shape(e))
            }
            (Map { key, range, witness }, Record(fs)) => {
                *witness == crate::FcnWitness::Dynamic
                    && fs.iter().all(|(f, _)| key.contains(&Value::Str(*f)))
                    && fs.iter().all(|(_, e)| range.accepts_shape(e))
            }
            (Record(fs), Record(ofs)) => {
                fs.len() == ofs.len() && fs.iter().zip(ofs.iter()).all(|(f, o)| f.0 == o.0 && f.1.accepts_shape(&o.1))
            }
            (Tuple(es), Tuple(oes)) => es.len() == oes.len() && es.iter().zip(oes.iter()).all(|(e, o)| e.accepts_shape(o)),
            (Seq { elem, max_len }, Seq { elem: oelem, max_len: omax }) => omax <= max_len && elem.accepts_shape(oelem),
            (Seq { elem, max_len }, Tuple(es)) => es.len() <= *max_len && es.iter().all(|e| elem.accepts_shape(e)),
            (Union(arms), Union(oarms)) => oarms.iter().all(|o| union_arm_accepts(arms, o)),
            (Union(arms), _) => union_arm_accepts(arms, other),
            _ => false,
        }
    }
}

/// Whether some arm of a union slot accepts the value shape `other`.
fn union_arm_accepts(arms: &[Shape], other: &Shape) -> bool {
    let Some(key) = other.kind_key() else { return false };
    arms.iter().find(|a| a.kind_key().as_ref() == Some(&key)).is_some_and(|a| a.accepts_shape(other))
}

impl crate::FcnWitness {
    /// Whether a fixed-domain slot witness encodes a value whose witness is
    /// `other`: `Dynamic` records the witness word, the fixed witnesses only
    /// accept themselves.
    fn accepts(self, other: crate::FcnWitness) -> bool {
        self == crate::FcnWitness::Dynamic || self == other
    }

    /// Whether a `Map` slot witness encodes a function valued of witness
    /// `other` (`Dynamic` records it; the fixed witnesses accept only their
    /// own construction).
    fn accepts_map(self, other: crate::FcnWitness) -> bool {
        self == crate::FcnWitness::Dynamic || self == other
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::FcnWitness;
    use std::sync::Arc;

    fn int(lo: i64, hi: i64) -> Shape {
        Shape::Int { lo, hi }
    }

    fn atom(names: &[&str]) -> Shape {
        let mut vs: Vec<Value> = names.iter().map(|n| Value::Str(tlx_value::Sym::new(n))).collect();
        vs.sort_by(Value::exact_cmp);
        Shape::Atom(Arc::from(vs))
    }

    fn set(elem: Shape, max_card: usize) -> Shape {
        Shape::Set { elem: Box::new(elem), max_card }
    }

    #[test]
    fn unbounded_slots_accept_anything() {
        assert!(Shape::Dyn.accepts_shape(&Shape::Bool));
        assert!(Shape::Dyn.accepts_shape(&Shape::Dyn));
        let store = crate::store::StoreRef::new(usize::MAX);
        assert!(Shape::Ref(store.clone()).accepts_shape(&Shape::Dyn));
        assert!(!Shape::Bool.accepts_shape(&Shape::Dyn));
        assert!(!Shape::Bool.accepts_shape(&Shape::Ref(store)));
        assert!(Shape::Bool.accepts_shape(&Shape::Never));
    }

    #[test]
    fn scalars_compare_ranges_and_universes() {
        assert!(int(0, 10).accepts_shape(&int(2, 4)));
        assert!(!int(0, 10).accepts_shape(&int(2, 11)));
        assert!(!int(0, 10).accepts_shape(&Shape::Bool));
        assert!(atom(&["a", "b"]).accepts_shape(&atom(&["a"])));
        assert!(!atom(&["a"]).accepts_shape(&atom(&["a", "b"])));
    }

    #[test]
    fn sets_respect_cardinality_and_elements() {
        assert!(set(atom(&["a", "b"]), 2).accepts_shape(&set(atom(&["a"]), 2)));
        assert!(!set(atom(&["a", "b"]), 1).accepts_shape(&set(atom(&["a", "b"]), 2)));
        assert!(!set(atom(&["a"]), 2).accepts_shape(&set(atom(&["a", "b"]), 1)));
        // An empty set shape (Never elements) fits any set slot.
        assert!(set(atom(&["a"]), 2).accepts_shape(&set(Shape::Never, 0)));
    }

    #[test]
    fn fixed_domain_functions_require_exact_domains_and_witnesses() {
        let dom: Arc<[Value]> = Arc::from([Value::Int(1), Value::Int(2)]);
        let fcn = |witness, range| Shape::Fcn { dom: dom.clone(), range: Box::new(range), witness, key_variants: Arc::from([]) };
        assert!(fcn(FcnWitness::Enumerated, int(0, 2)).accepts_shape(&fcn(FcnWitness::Enumerated, int(0, 2))));
        assert!(!fcn(FcnWitness::Enumerated, int(0, 2)).accepts_shape(&fcn(FcnWitness::Interval, int(0, 2))));
        assert!(fcn(FcnWitness::Dynamic, int(0, 2)).accepts_shape(&fcn(FcnWitness::Interval, int(0, 2))));
        // A tuple (1..n) value only fits a Dynamic-witness function slot.
        let tuple = Shape::Tuple(Arc::from([int(0, 2), int(0, 2)]));
        assert!(!fcn(FcnWitness::Interval, int(0, 2)).accepts_shape(&tuple));
        assert!(fcn(FcnWitness::Dynamic, int(0, 2)).accepts_shape(&tuple));
        // Alternate key representations in the value shape need the slot's
        // exact variants; none of them always match the first variant.
        let variants: Arc<[(usize, Arc<[Value]>)]> = Arc::from([(0usize, Arc::from([Value::Int(1), Value::Int(2)]))]);
        let with_variants =
            Shape::Fcn { dom: dom.clone(), range: Box::new(int(0, 2)), witness: FcnWitness::Enumerated, key_variants: variants.clone() };
        assert!(with_variants.accepts_shape(&fcn(FcnWitness::Enumerated, int(0, 2))));
        // A value that may use a second key representation can miss a slot
        // that only knows the first one.
        assert!(!fcn(FcnWitness::Enumerated, int(0, 2)).accepts_shape(&with_variants));
        // A domain mismatch is a miss even with equal ranges.
        let other_dom = Shape::Fcn {
            dom: Arc::from([Value::Int(1), Value::Int(3)]),
            range: Box::new(int(0, 2)),
            witness: FcnWitness::Enumerated,
            key_variants: Arc::from([]),
        };
        assert!(!fcn(FcnWitness::Enumerated, int(0, 2)).accepts_shape(&other_dom));
    }

    #[test]
    fn tuples_records_and_sequences_compare_componentwise() {
        let t = Shape::Tuple(Arc::from([int(0, 2), Shape::Bool]));
        assert!(t.accepts_shape(&Shape::Tuple(Arc::from([int(0, 1), Shape::Bool]))));
        assert!(!t.accepts_shape(&Shape::Tuple(Arc::from([int(0, 1)]))));
        let r = Shape::Record(Arc::from([(tlx_value::Sym::new("a"), int(0, 2))]));
        let r2 = Shape::Record(Arc::from([(tlx_value::Sym::new("a"), int(0, 1))]));
        assert!(r.accepts_shape(&r2));
        let seq = Shape::Seq { elem: Box::new(int(0, 2)), max_len: 3 };
        assert!(seq.accepts_shape(&Shape::Seq { elem: Box::new(int(0, 1)), max_len: 2 }));
        assert!(!seq.accepts_shape(&Shape::Seq { elem: Box::new(int(0, 1)), max_len: 4 }));
        assert!(seq.accepts_shape(&Shape::Tuple(Arc::from([int(0, 0)]))));
        assert!(!seq.accepts_shape(&Shape::Tuple(Arc::from(vec![int(0, 0); 4]))));
    }

    #[test]
    fn maps_accept_functions_tuples_and_records_over_their_key_universe() {
        let map = Shape::Map { key: Box::new(atom(&["a", "b"])), range: Box::new(int(0, 2)), witness: FcnWitness::Dynamic };
        let fcn = Shape::Fcn {
            dom: Arc::from([Value::Str(tlx_value::Sym::new("a"))]),
            range: Box::new(int(0, 1)),
            witness: FcnWitness::Enumerated,
            key_variants: Arc::from([]),
        };
        assert!(map.accepts_shape(&fcn));
        let record = Shape::Record(Arc::from([(tlx_value::Sym::new("a"), int(0, 1))]));
        assert!(map.accepts_shape(&record));
        let key_outside = Shape::Fcn {
            dom: Arc::from([Value::Str(tlx_value::Sym::new("c"))]),
            range: Box::new(int(0, 1)),
            witness: FcnWitness::Enumerated,
            key_variants: Arc::from([]),
        };
        assert!(!map.accepts_shape(&key_outside));
        // A tuple is a function over `1..n`: an `Interval` map records its
        // witness, an `Enumerated` one cannot.
        let enumerated = Shape::Map { key: Box::new(int(1, 1)), range: Box::new(int(0, 1)), witness: FcnWitness::Enumerated };
        let tuple = Shape::Tuple(Arc::from([int(0, 1)]));
        assert!(!enumerated.accepts_shape(&tuple));
        let interval = Shape::Map { key: Box::new(int(1, 1)), range: Box::new(int(0, 1)), witness: FcnWitness::Interval };
        assert!(interval.accepts_shape(&tuple));
        // Alternate key representations on a `Fcn` must also fit the map's key universe.
        let tuple_map =
            Shape::Map { key: Box::new(Shape::Tuple(Arc::from([int(0, 0)]))), range: Box::new(int(0, 1)), witness: FcnWitness::Enumerated };
        let fcn_with_alt_key = Shape::Fcn {
            dom: Arc::from([Value::Tuple(Arc::from([Value::Int(0)]))]),
            range: Box::new(int(0, 1)),
            witness: FcnWitness::Enumerated,
            key_variants: Arc::from([(
                0usize,
                Arc::from([
                    Value::Tuple(Arc::from([Value::Int(0)])),
                    Value::fcn_rcd_from_pairs(vec![(Value::Int(1), Value::Int(0))]).unwrap(),
                ]),
            )]),
        };
        assert!(!tuple_map.accepts_shape(&fcn_with_alt_key));
    }

    #[test]
    fn unions_match_arms_by_kind() {
        let u = Shape::Union(Arc::from([Shape::Bool, int(0, 2)]));
        assert!(u.accepts_shape(&Shape::Bool));
        assert!(u.accepts_shape(&int(1, 2)));
        assert!(!u.accepts_shape(&int(1, 3)));
        assert!(u.accepts_shape(&Shape::Union(Arc::from([Shape::Bool, int(0, 1)]))));
        assert!(!u.accepts_shape(&Shape::Union(Arc::from([Shape::Bool, atom(&["a"])]))));
    }
}
