//! Random values of layout shapes (for property tests on encoded states).

use tlx_layout::{layout, Shape};
use tlx_value::Value;

use crate::Rng;

/// A random value of shape `s` (normalized; `s.contains` it). Integer ranges
/// favour their bounds, sets and sequences their sizes 0 and maximal.
pub fn random_value(s: &Shape, rng: &mut Rng) -> Value {
    let v = gen(s, rng);
    v.normalize().expect("random values are normalizable")
}

/// A random state: one value per shape.
pub fn random_state(shapes: &[Shape], rng: &mut Rng) -> Vec<Value> {
    shapes.iter().map(|s| random_value(s, rng)).collect()
}

/// A random size in `0..=max`, favouring 0 and `max`.
fn size(max: usize, rng: &mut Rng) -> usize {
    match rng.below(6) {
        0 => 0,
        1 => max,
        _ => rng.range(0, max as i64) as usize,
    }
}

fn gen(s: &Shape, rng: &mut Rng) -> Value {
    match s {
        Shape::Never => panic!("no value of shape Never"),
        Shape::Bool => Value::Bool(rng.chance(1, 2)),
        Shape::Int { lo, hi } => match rng.below(8) {
            0 => Value::Int(*lo),
            1 => Value::Int(*hi),
            _ => Value::Int(rng.range(*lo, *hi)),
        },
        Shape::Atom(u) => u[rng.below(u.len() as u64) as usize].clone(),
        Shape::Set { elem, max_card } => {
            if matches!(**elem, Shape::Never) {
                return Value::empty_set();
            }
            let card = elem.cardinality().map_or(usize::MAX, |c| c.min(usize::MAX as u64) as usize);
            let n = size((*max_card).min(card), rng);
            let mut es: Vec<Value> = Vec::with_capacity(n);
            // Distinct elements (a few attempts each; small universes fill up).
            let mut attempts = 0;
            while es.len() < n && attempts < 8 * n + 8 {
                attempts += 1;
                let e = random_value(elem, rng);
                if !es.contains(&e) {
                    es.push(e);
                }
            }
            Value::set_from(es).expect("comparable elements")
        }
        Shape::Fcn { dom, range, witness, key_variants } => {
            let mut kv_slot = 0usize;
            let pairs: Vec<(Value, Value)> = (0..dom.len())
                .map(|pos| {
                    let key =
                        tlx_layout::shape::fcn_key_at(dom, key_variants, &mut kv_slot, pos, |_, vs| rng.below(vs.len() as u64) as usize)
                            .clone();
                    (key, random_value(range, rng))
                })
                .collect();
            witness.decode_fcn(pairs, || u64::from(!rng.chance(1, 2)))
        }
        Shape::Map { key, range, witness } => {
            let u = key.cardinality().expect("map keys have a finite universe");
            let dense = rng.below(4);
            let mut pairs: Vec<(Value, Value)> = Vec::new();
            for r in 0..u {
                let present = match dense {
                    0 => false,
                    1 => true,
                    _ => rng.chance(1, 2),
                };
                if present {
                    pairs.push((layout::unrank(key, r), random_value(range, rng)));
                }
            }
            witness.decode_map(pairs, || u64::from(!rng.chance(1, 2)))
        }
        Shape::Record(fs) => Value::record(fs.iter().map(|(k, f)| (*k, random_value(f, rng))).collect()),
        Shape::Tuple(es) => Value::tuple(es.iter().map(|e| random_value(e, rng)).collect()),
        Shape::Seq { elem, max_len } => {
            if matches!(**elem, Shape::Never) {
                return Value::tuple(Vec::new());
            }
            let n = size(*max_len, rng);
            Value::tuple((0..n).map(|_| random_value(elem, rng)).collect())
        }
        Shape::Union(arms) => random_value(&arms[rng.below(arms.len() as u64) as usize], rng),
        Shape::Dyn | Shape::Ref(_) => match rng.below(3) {
            0 => Value::Int(rng.range(-3, 3)),
            1 => Value::str(["a", "b"][rng.below(2) as usize]),
            _ => Value::set_from(vec![Value::Int(rng.range(0, 2))]).unwrap(),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::{random_state, random_value};
    use crate::Rng;
    use tlx_layout::Shape;
    use tlx_value::Value;

    /// Every sampled value lies inside its shape: this is the contract the
    /// encoded differential tests rely on (normalization is part of it).
    #[test]
    fn random_values_are_inside_their_shape() {
        let shapes = [
            Shape::Bool,
            Shape::Int { lo: -3, hi: 5 },
            Shape::Set { elem: Box::new(Shape::Bool), max_card: 3 },
            Shape::Seq { elem: Box::new(Shape::Int { lo: 0, hi: 2 }), max_len: 4 },
            Shape::Tuple(vec![Shape::Bool, Shape::Int { lo: 0, hi: 1 }].into()),
        ];
        let mut rng = Rng::new(7);
        for _ in 0..200 {
            for s in &shapes {
                let v = random_value(s, &mut rng);
                assert!(s.contains(&v), "{s:?} does not contain {v:?}");
            }
        }
    }

    /// Sequence sizes favour 0 and the maximum length (the sampling bias the
    /// compiled differential tests were written against).
    #[test]
    fn sequence_sizes_favour_zero_and_the_maximum() {
        let seq = Shape::Seq { elem: Box::new(Shape::Bool), max_len: 4 };
        let mut rng = Rng::new(11);
        let sizes: Vec<usize> = (0..24)
            .map(|_| match random_value(&seq, &mut rng) {
                Value::Tuple(items) => items.len(),
                other => panic!("a sequence is a tuple, got {other:?}"),
            })
            .collect();
        assert!(sizes.contains(&0) && sizes.contains(&4), "{sizes:?}");
        assert!(sizes.iter().all(|&n| n <= 4), "{sizes:?}");
    }

    /// The seeded sampling sequence over a mixed shape list is pinned, so a
    /// change to the value layout or PRNG use must update this deliberately.
    #[test]
    fn random_state_golden() {
        let shapes = [Shape::Bool, Shape::Int { lo: 0, hi: 3 }];
        let mut rng = Rng::new(7);
        assert_eq!(random_state(&shapes, &mut rng), vec![Value::Bool(true), Value::Int(0)]);
    }
}
