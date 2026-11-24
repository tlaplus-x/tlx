//! Serialization of shapes, layouts and the `Dyn` interner (`tlx_layout::ser`):
//! property-style round trips on random shapes and on shapes inferred from
//! random values.

use std::sync::Arc;

use tlx_layout::shape::{FcnWitness, Shape};
use tlx_layout::{dynval, ser, Layout};
use tlx_value::ser::{Reader, Writer};
use tlx_value::{Sym, Value};

use tlx_testkit::XorShift64Star as Rng;

const NAMES: &[&str] = &["ser_a", "ser_b", "ser_c", "pc", "ack", "msgs"];

fn atom(r: &mut Rng) -> Value {
    let name = NAMES[r.below(NAMES.len() as u64) as usize];
    if r.below(2) == 0 {
        Value::str(name)
    } else {
        Value::model_value(name)
    }
}

/// Any shape (not necessarily one that inference would produce: the codec
/// must not care).
fn shape(r: &mut Rng, depth: u32) -> Shape {
    let leaf = depth == 0 || r.below(3) == 0;
    if leaf {
        return match r.below(5) {
            0 => Shape::Never,
            1 => Shape::Bool,
            2 => {
                let lo = r.next_u64() as i64 >> r.below(64);
                Shape::Int { lo, hi: lo.saturating_add(r.below(100) as i64) }
            }
            3 => Shape::Atom((0..r.below(5)).map(|_| atom(r)).collect()),
            _ => Shape::Dyn,
        };
    }
    let d = depth - 1;
    let n = r.below(5) as usize;
    match r.below(8) {
        0 => Shape::Set { elem: Box::new(shape(r, d)), max_card: r.below(1 << 20) as usize },
        1 => {
            if n > 0 && r.below(4) == 0 {
                let tup_key = Value::tuple(vec![Value::Int(0)]);
                let enum_key = Value::fcn_with_dom(vec![(Value::Int(1), Value::Int(0))], tlx_value::FcnDom::Enumerated);
                Shape::Fcn {
                    dom: Arc::from([tup_key.clone()]),
                    range: Box::new(shape(r, d)),
                    witness: FcnWitness::Enumerated,
                    key_variants: Arc::from([(0usize, Arc::from([tup_key, enum_key]))]),
                }
            } else {
                Shape::Fcn {
                    dom: (0..n).map(|i| if i % 2 == 0 { atom(r) } else { Value::Int(r.below(9) as i64) }).collect(),
                    range: Box::new(shape(r, d)),
                    witness: match r.below(3) {
                        0 => FcnWitness::Enumerated,
                        1 => FcnWitness::Interval,
                        _ => FcnWitness::Dynamic,
                    },
                    key_variants: Arc::from([]),
                }
            }
        }
        2 => Shape::Map {
            key: Box::new(shape(r, d)),
            range: Box::new(shape(r, d)),
            witness: match r.below(3) {
                0 => FcnWitness::Enumerated,
                1 => FcnWitness::Interval,
                _ => FcnWitness::Dynamic,
            },
        },
        3 => Shape::Record((0..n).map(|_| (Sym::new(NAMES[r.below(6) as usize]), shape(r, d))).collect()),
        4 => Shape::Tuple((0..n).map(|_| shape(r, d)).collect()),
        5 => Shape::Seq { elem: Box::new(shape(r, d)), max_len: r.below(1000) as usize },
        6 => Shape::Union((0..n).map(|_| shape(r, d)).collect()),
        _ => Shape::Dyn,
    }
}

fn round_trip(s: &Shape) -> Shape {
    let mut w = Writer::new();
    ser::write_shape(&mut w, s);
    let b = w.into_bytes();
    let mut r = Reader::new(&b);
    let back = ser::read_shape(&mut r).unwrap_or_else(|e| panic!("{s:?}: {e}"));
    r.finish().unwrap();
    back
}

#[test]
fn random_shapes_round_trip() {
    let mut r = Rng::new(0xfeed_beef_1234_5678);
    for i in 0..20_000 {
        let s = shape(&mut r, 1 + i % 6);
        assert_eq!(round_trip(&s), s);
    }
}

fn sample_values() -> Vec<Value> {
    vec![
        Value::record(vec![(Sym::new("pc"), Value::str("ser_a")), (Sym::new("ack"), Value::Int(3))]),
        Value::record(vec![(Sym::new("pc"), Value::str("ser_b")), (Sym::new("ack"), Value::Int(-2))]),
        Value::tuple(vec![Value::Int(1), Value::model_value("ser_c")]),
        Value::set_from(vec![Value::Int(1), Value::Int(5)]).unwrap(),
        Value::fcn_from_pairs(vec![(Value::model_value("ser_a"), Value::Int(0)), (Value::model_value("ser_b"), Value::Int(1))]).unwrap(),
        Value::fcn_from_pairs(vec![(Value::Int(0), Value::TRUE), (Value::Int(2), Value::FALSE)]).unwrap(),
        Value::Interval(1, 4),
        Value::tuple(vec![Value::str("ser_a"), Value::str("ser_b"), Value::str("ser_a")]),
    ]
}

/// Shapes as inference produces them: `Shape::of` joined over values.
fn inferred_shapes() -> Vec<Shape> {
    let mut out = Vec::new();
    let mut acc = Shape::Never;
    for v in sample_values() {
        let s = Shape::of(&v);
        acc = acc.join(&s);
        out.push(s);
        out.push(acc.clone());
        out.push(acc.homogenize());
    }
    out.push(Shape::Dyn);
    out
}

#[test]
fn inferred_shapes_round_trip() {
    let shapes = inferred_shapes();
    assert!(shapes.iter().any(|s| matches!(s, Shape::Union(_))));
    assert!(shapes.iter().any(|s| matches!(s, Shape::Map { .. } | Shape::Fcn { .. })));
    for s in &shapes {
        assert_eq!(round_trip(s), *s);
    }
}

#[test]
fn layout_round_trip() {
    let shapes = inferred_shapes();
    let mut r = Rng::new(99);
    for _ in 0..500 {
        let vars: Vec<Shape> = (0..r.below(8)).map(|_| shapes[r.below(shapes.len() as u64) as usize].clone()).collect();
        let l = Layout::new(vars);
        let mut w = Writer::new();
        ser::write_layout(&mut w, &l);
        let b = w.into_bytes();
        let mut rd = Reader::new(&b);
        let back = ser::read_layout(&mut rd).unwrap();
        rd.finish().unwrap();
        assert_eq!(back.vars, l.vars);
        assert_eq!(back.offsets, l.offsets);
        assert_eq!(back.words, l.words);
    }
}

#[test]
fn dyn_table_round_trip_in_process() {
    let vals: Vec<Value> = (0..200).map(|i| Value::tuple(vec![Value::Int(i), Value::str("ser_dyn"), Value::Interval(0, i)])).collect();
    let handles: Vec<u64> = vals.iter().map(dynval::intern).collect();
    let snap = dynval::snapshot();
    assert_eq!(snap.len(), dynval::SHARD_COUNT);
    let mut w = Writer::new();
    ser::write_dyn_table(&mut w, &snap).unwrap();
    let b = w.into_bytes();
    let mut r = Reader::new(&b);
    let back = ser::read_dyn_table(&mut r).unwrap();
    r.finish().unwrap();
    assert_eq!(back.len(), snap.len());
    for (x, y) in back.iter().zip(&snap) {
        assert!(x.len() == y.len() && x.iter().zip(y).all(|(a, b)| a == b));
    }
    // Restoring onto the same interner is a no-op (its contents are a prefix).
    dynval::restore(&back).unwrap();
    for (v, h) in vals.iter().zip(&handles) {
        assert_eq!(dynval::intern(v), *h);
    }
    // A snapshot contradicting the interner is refused.
    let mut bad = back.clone();
    let si = bad.iter().position(|s| !s.is_empty()).unwrap();
    bad[si][0] = Value::str("ser_not_there");
    assert!(dynval::restore(&bad).is_err());
    assert!(dynval::restore(&back[1..]).is_err());
}

#[test]
fn rejects_invalid_fcn_key_variants() {
    use std::sync::Arc;
    use tlx_layout::FcnWitness;

    let tup = Value::tuple(vec![Value::Int(0)]);
    let fcn = Value::fcn_rcd_from_pairs(vec![(Value::Int(1), Value::Int(0))]).unwrap();
    let (lo, hi) = if tup.exact_cmp(&fcn) == std::cmp::Ordering::Less { (tup, fcn) } else { (fcn, tup) };

    let bad_shapes = [
        // Two distinct integer keys in one variant slot (not TLA+-equal).
        Shape::Fcn {
            dom: Arc::from([Value::Int(1)]),
            range: Box::new(Shape::Int { lo: 0, hi: 0 }),
            witness: FcnWitness::Enumerated,
            key_variants: Arc::from([(0, Arc::from([Value::Int(1), Value::Int(2)]))]),
        },
        // First variant key does not exact_eq dom[pos].
        Shape::Fcn {
            dom: Arc::from([hi.clone()]),
            range: Box::new(Shape::Int { lo: 0, hi: 0 }),
            witness: FcnWitness::Enumerated,
            key_variants: Arc::from([(0, Arc::from([lo.clone(), hi.clone()]))]),
        },
        // Variants not strictly increasing under exact_cmp.
        Shape::Fcn {
            dom: Arc::from([hi.clone()]),
            range: Box::new(Shape::Int { lo: 0, hi: 0 }),
            witness: FcnWitness::Enumerated,
            key_variants: Arc::from([(0, Arc::from([hi.clone(), lo.clone()]))]),
        },
        // Duplicate exact variants.
        Shape::Fcn {
            dom: Arc::from([lo.clone()]),
            range: Box::new(Shape::Int { lo: 0, hi: 0 }),
            witness: FcnWitness::Enumerated,
            key_variants: Arc::from([(0, Arc::from([lo.clone(), lo.clone()]))]),
        },
    ];
    for s in &bad_shapes {
        let mut w = Writer::new();
        ser::write_shape(&mut w, s);
        let bytes = w.into_bytes();
        let mut r = Reader::new(&bytes);
        assert!(ser::read_shape(&mut r).is_err(), "decoder must reject invalid key_variants: {s:?}");
    }

    // Valid sparse variant list still round-trips.
    let good = Shape::Fcn {
        dom: Arc::from([lo.clone()]),
        range: Box::new(Shape::Int { lo: 0, hi: 0 }),
        witness: FcnWitness::Enumerated,
        key_variants: Arc::from([(0, Arc::from([lo, hi]))]),
    };
    assert_eq!(round_trip(&good), good);
}
