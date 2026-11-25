//! Property tests: the precomputed layout tree (`LayoutNode`) agrees with
//! the `Shape`-based functions of `layout` on random values of random
//! shapes (encodings, misses, decoding, ranks, unranks, sizes).

use std::sync::Arc;

use tlx_layout::layout::{bitset_universe, decode, encode, rank, unrank, words};
use tlx_layout::layout_tree::transcode;
use tlx_layout::shape::{map_shape, set_shape, FcnWitness};
use tlx_layout::{Layout, LayoutNode, Shape};
use tlx_value::{Sym, Value};

use tlx_testkit::XorShift64Star as Rng;

const ATOMS: [&str; 6] = ["a", "b", "c", "d", "e", "f"];
const FIELDS: [&str; 5] = ["f", "g", "h", "k", "x"];

fn atom(rng: &mut Rng) -> Value {
    let a = ATOMS[rng.below_or_zero(ATOMS.len() as u64) as usize];
    if rng.chance_inclusive(0.5) {
        Value::model_value(a)
    } else {
        Value::str(a)
    }
}

fn atom_shape(rng: &mut Rng) -> Shape {
    let n = 1 + rng.below_or_zero(4);
    let mut vs: Vec<Value> = (0..n).map(|_| atom(rng)).collect();
    vs.sort();
    vs.dedup();
    Shape::Atom(Arc::from(vs))
}

fn int_shape(rng: &mut Rng) -> Shape {
    let lo = rng.range(-3, 3);
    let hi = if rng.chance_inclusive(0.1) { lo + 5000 } else { lo + rng.range(0, 4) };
    Shape::Int { lo, hi }
}

/// A key shape for maps (integers, atoms, records/tuples of those).
fn key_shape(rng: &mut Rng) -> Shape {
    match rng.below_or_zero(4) {
        0 => Shape::Int { lo: rng.range(-1, 2), hi: rng.range(2, 6) },
        1 => atom_shape(rng),
        2 => Shape::Tuple(Arc::from(vec![Shape::Bool, atom_shape(rng)])),
        _ => record_shape(rng, 0, true),
    }
}

fn record_shape(rng: &mut Rng, depth: u32, scalar: bool) -> Shape {
    let n = 1 + rng.below_or_zero(3) as usize;
    let mut names: Vec<Sym> = (0..n).map(|_| Sym::new(FIELDS[rng.below_or_zero(FIELDS.len() as u64) as usize])).collect();
    names.sort();
    names.dedup();
    let fs: Vec<(Sym, Shape)> = names
        .into_iter()
        .map(|k| {
            (
                k,
                if scalar {
                    if rng.chance_inclusive(0.5) {
                        Shape::Bool
                    } else {
                        atom_shape(rng)
                    }
                } else {
                    shape(rng, depth + 1)
                },
            )
        })
        .collect();
    Shape::Record(Arc::from(fs))
}

fn shape(rng: &mut Rng, depth: u32) -> Shape {
    let leaf = depth >= 3 || rng.chance_inclusive(0.3);
    if leaf {
        return match rng.below_or_zero(10) {
            0..=2 => Shape::Bool,
            3..=5 => int_shape(rng),
            6..=8 => atom_shape(rng),
            _ => Shape::Dyn,
        };
    }
    match rng.below_or_zero(9) {
        0 => {
            let elem = shape(rng, depth + 1);
            set_shape(elem, rng.below_or_zero(5) as usize)
        }
        1 => {
            let n = 1 + rng.below_or_zero(3);
            let (pairs, witness): (Vec<(Value, Value)>, FcnWitness) = if rng.chance_inclusive(0.4) {
                let w = match rng.below_or_zero(3) {
                    0 => FcnWitness::Enumerated,
                    1 => FcnWitness::Interval,
                    _ => FcnWitness::Dynamic,
                };
                ((0..n).map(|i| (Value::Int(i as i64), Value::TRUE)).collect(), w)
            } else if rng.chance_inclusive(0.5) {
                let w = if rng.chance_inclusive(0.5) { FcnWitness::Enumerated } else { FcnWitness::Dynamic };
                ((1..=n).map(|i| (Value::Int(i as i64), Value::TRUE)).collect(), w)
            } else {
                let mut a: Vec<Value> = (0..n).map(|i| Value::model_value(ATOMS[i as usize])).collect();
                a.push(Value::Int(7));
                (a.into_iter().map(|k| (k, Value::TRUE)).collect(), FcnWitness::Enumerated)
            };
            let Value::Fcn(ps, _) = Value::fcn_rcd_from_pairs(pairs).unwrap() else { unreachable!() };
            let dom: Arc<[Value]> = ps.iter().map(|p| p.0.clone()).collect();
            Shape::Fcn { dom, range: Box::new(shape(rng, depth + 1)), witness, key_variants: Arc::from([]) }
        }
        2 => {
            let key = key_shape(rng);
            let witness = if matches!(key, Shape::Int { .. }) {
                match rng.below_or_zero(3) {
                    0 => FcnWitness::Enumerated,
                    1 => FcnWitness::Interval,
                    _ => FcnWitness::Dynamic,
                }
            } else if rng.chance_inclusive(0.5) {
                FcnWitness::Enumerated
            } else {
                FcnWitness::Dynamic
            };
            map_shape(key, shape(rng, depth + 1), witness)
        }
        3 => record_shape(rng, depth, false),
        4 => Shape::Tuple((0..rng.below_or_zero(4)).map(|_| shape(rng, depth + 1)).collect()),
        5 => Shape::Seq { elem: Box::new(shape(rng, depth + 1)), max_len: rng.below_or_zero(4) as usize },
        6 | 7 => {
            // Unions through joins of shapes of different families.
            let mut s = shape(rng, depth + 1);
            for _ in 0..1 + rng.below_or_zero(2) {
                s = s.join(&shape(rng, depth + 1));
            }
            s
        }
        _ => Shape::Set { elem: Box::new(Shape::Never), max_card: 0 },
    }
}

/// A random value that usually belongs to `s`.
fn value(rng: &mut Rng, s: &Shape, depth: u32) -> Value {
    if depth > 8 {
        return if rng.chance_inclusive(0.5) { Value::Int(rng.range(-2, 2)) } else { atom(rng) };
    }
    if depth > 0 && rng.chance_inclusive(0.03) {
        return any_value(rng, depth + 1);
    }
    match s {
        Shape::Never => any_value(rng, depth + 1),
        Shape::Bool => Value::Bool(rng.chance_inclusive(0.5)),
        Shape::Int { lo, hi } => Value::Int(rng.range(*lo, (*hi).min(*lo + 6000))),
        Shape::Atom(u) => u[rng.below_or_zero(u.len() as u64) as usize].clone(),
        Shape::Set { elem, max_card } => {
            let n = rng.below_or_zero(*max_card as u64 + 1);
            let mut es: Vec<Value> =
                if **elem == Shape::Never { Vec::new() } else { (0..n).map(|_| value(rng, elem, depth + 1)).collect() };
            es.sort();
            es.dedup();
            if es.len() >= 2 && rng.chance_inclusive(0.2) {
                if let (Value::Int(a), Value::Int(b)) = (&es[0], &es[es.len() - 1]) {
                    if b - a + 1 == es.len() as i64 {
                        return Value::Interval(*a, *b);
                    }
                }
            }
            Value::Set(Arc::from(es))
        }
        Shape::Fcn { dom, range, witness, key_variants } => {
            let mut kv_slot = 0usize;
            let pairs: Vec<(Value, Value)> = (0..dom.len())
                .map(|pos| {
                    let key = tlx_layout::shape::fcn_key_at(dom, key_variants, &mut kv_slot, pos, |_, vs| {
                        rng.below_or_zero(vs.len() as u64) as usize
                    })
                    .clone();
                    (key, value(rng, range, depth + 1))
                })
                .collect();
            witness.decode_fcn(pairs, || u64::from(!rng.chance_inclusive(0.5)))
        }
        Shape::Map { key, range, witness } => {
            let n = rng.below_or_zero(4);
            let mut pairs: Vec<(Value, Value)> = (0..n).map(|_| (value(rng, key, depth + 1), value(rng, range, depth + 1))).collect();
            pairs.sort_by(|a, b| a.0.cmp(&b.0));
            pairs.dedup_by(|a, b| a.0 == b.0);
            let Ok(Value::Fcn(sorted, _)) = Value::fcn_rcd_from_pairs(pairs) else {
                return Value::TRUE;
            };
            witness.decode_map(sorted.to_vec(), || u64::from(!rng.chance_inclusive(0.5)))
        }
        Shape::Record(fs) => Value::Record(fs.iter().map(|(k, f)| (*k, value(rng, f, depth + 1))).collect()),
        Shape::Tuple(es) => Value::tuple(es.iter().map(|e| value(rng, e, depth + 1)).collect()),
        Shape::Seq { elem, max_len } => {
            let n = rng.below_or_zero(*max_len as u64 + 1);
            Value::tuple((0..n).map(|_| value(rng, elem, depth + 1)).collect())
        }
        Shape::Union(arms) => {
            let i = rng.below_or_zero(arms.len() as u64) as usize;
            value(rng, &arms[i], depth + 1)
        }
        Shape::Dyn | Shape::Ref(_) => any_value(rng, depth + 1),
    }
}

fn any_value(rng: &mut Rng, depth: u32) -> Value {
    let s = shape(rng, 2);
    value(rng, &s, depth.max(5))
}

/// How many checks of each kind succeeded (to make sure the generators
/// exercise more than misses).
#[derive(Default, Debug)]
struct Stats {
    encoded: usize,
    missed: usize,
    ranked: usize,
    unranked: usize,
}

fn check(rng: &mut Rng, s: &Shape, st: &mut Stats) {
    let n = LayoutNode::new(s);
    assert_eq!(n.words(), words(s), "words of {s:?}");
    assert_eq!(n.cardinality(), s.cardinality(), "cardinality of {s:?}");
    assert_eq!(n.bitset_universe(), bitset_universe(s), "bitset universe of {s:?}");
    let w = words(s);
    for _ in 0..40 {
        let v = value(rng, s, 0);
        let (mut a, mut b) = (vec![7u64; w + 2], vec![7u64; w + 2]);
        let ra = encode(s, &v, &mut a);
        let rb = n.encode(&v, &mut b);
        assert_eq!(ra, rb, "encode result of {v} in {s:?}");
        if ra.is_ok() {
            st.encoded += 1;
            assert_eq!(a, b, "encoding of {v} in {s:?}");
            let d = n.decode(&b);
            assert_eq!(d, decode(s, &a), "decoding of {v} in {s:?}");
            assert_eq!(d, v.normalize().unwrap(), "round trip of {v} in {s:?}");
        } else {
            st.missed += 1;
        }
        let r = rank(s, &v);
        st.ranked += r.is_ok() as usize;
        assert_eq!(r, n.rank(&v), "rank of {v} in {s:?}");
    }
    if let Some(c) = s.cardinality() {
        for i in 0..20 {
            let r = if i < 5 && i < c {
                i
            } else if (5..10).contains(&i) && i - 5 < c {
                c - 1 - (i - 5)
            } else {
                rng.below_or_zero(c)
            };
            if c == 0 {
                break;
            }
            let v = unrank(s, r);
            st.unranked += 1;
            assert_eq!(n.unrank(r), v, "unrank {r} in {s:?}");
            // (Not always `r`: e.g. an empty map in a union with a sequence
            // arm is `<<>>`, which ranks in the sequence arm.)
            assert_eq!(n.rank(&v), rank(s, &v), "rank of unrank {r} in {s:?}");
        }
    }
}

#[test]
fn tree_matches_shape_functions() {
    let mut rng = Rng::new(0x9e37_79b9_7f4a_7c15);
    let mut kinds = std::collections::HashMap::<&str, usize>::new();
    let mut st = Stats::default();
    for _ in 0..3000 {
        let s = shape(&mut rng, 0);
        let k = match &s {
            Shape::Never => "never",
            Shape::Bool | Shape::Int { .. } | Shape::Atom(_) => "scalar",
            Shape::Set { .. } => "set",
            Shape::Fcn { .. } => "fcn",
            Shape::Map { .. } => "map",
            Shape::Record(_) => "record",
            Shape::Tuple(_) => "tuple",
            Shape::Seq { .. } => "seq",
            Shape::Union(_) => "union",
            Shape::Dyn | Shape::Ref(_) => "dyn",
        };
        *kinds.entry(k).or_default() += 1;
        check(&mut rng, &s, &mut st);
    }
    // Every kind of shape was exercised.
    for k in ["scalar", "set", "fcn", "map", "record", "tuple", "seq", "union", "dyn"] {
        assert!(kinds.get(k).copied().unwrap_or(0) >= 20, "too few {k} shapes: {kinds:?}");
    }
    eprintln!("{kinds:?} {st:?}");
    assert!(st.encoded > 20_000 && st.missed > 1_000 && st.ranked > 10_000 && st.unranked > 10_000, "{st:?}");
}

#[test]
fn layout_state_matches_per_variable_encoding() {
    let mut rng = Rng::new(12345);
    for _ in 0..300 {
        let vars: Vec<Shape> = (0..1 + rng.below_or_zero(4)).map(|_| shape(&mut rng, 1)).collect();
        let l = Layout::new(vars.clone());
        assert_eq!(l.words, vars.iter().map(words).sum::<usize>());
        for _ in 0..10 {
            let vals: Vec<Value> = vars.iter().map(|s| value(&mut rng, s, 1)).collect();
            let mut out = vec![0u64; l.words];
            let res = l.encode_state(&vals, &mut out);
            let mut want = vec![0u64; l.words];
            let mut miss = None;
            for (i, (s, v)) in vars.iter().zip(&vals).enumerate() {
                if let Err(m) = encode(s, v, &mut want[l.offsets[i]..]) {
                    miss = Some(i);
                    assert_eq!(res.as_ref().unwrap_err().var_index(), Some(i));
                    assert!(res.as_ref().unwrap_err().path.ends_with(&m.path));
                    break;
                }
            }
            if miss.is_none() {
                res.unwrap();
                assert_eq!(out, want);
                let back = l.decode_state(&out);
                let direct: Vec<Value> = vars.iter().enumerate().map(|(i, s)| decode(s, &out[l.offsets[i]..])).collect();
                assert_eq!(back, direct);
                #[allow(clippy::needless_range_loop)] // `i` indexes vars and l.offsets alike
                for i in 0..vars.len() {
                    assert_eq!(l.var_range(i), l.offsets[i]..l.offsets[i] + words(&vars[i]));
                }
            }
        }
    }
}

#[test]
fn transcode_matches_reencoding() {
    let mut rng = Rng::new(777);
    let mut copied = 0;
    for _ in 0..2000 {
        let old = shape(&mut rng, 0);
        // A wider shape: joined with the shapes of a few random values (of
        // this shape or of other ones), which widens integer ranges, atom
        // universes, set cardinalities, sequence lengths, unions, ...
        let mut new = old.clone();
        for _ in 0..1 + rng.below_or_zero(3) {
            let v = if rng.chance_inclusive(0.7) { value(&mut rng, &old, 1) } else { any_value(&mut rng, 1) };
            if let Ok(v) = v.normalize() {
                new = new.join(&Shape::of(&v));
            }
        }
        let (no, nn) = (LayoutNode::new(&old), LayoutNode::new(&new));
        for _ in 0..10 {
            let v = value(&mut rng, &old, 0);
            let mut src = vec![0u64; no.words()];
            if no.encode(&v, &mut src).is_err() {
                continue;
            }
            let mut got = vec![0u64; nn.words()];
            let ok = transcode(&no, &nn, &src, &mut got);
            let decoded = no.decode(&src);
            let mut want = vec![0u64; nn.words()];
            let fits = nn.encode(&decoded, &mut want).is_ok();
            assert_eq!(ok, fits, "transcode of {v} from {old:?} to {new:?}");
            if ok {
                assert_eq!(got, want, "transcode of {v} from {old:?} to {new:?}");
                let mut orig = vec![0u64; nn.words()];
                if nn.encode(&v, &mut orig).is_ok() {
                    let mut got_can = got.clone();
                    nn.canonicalize_words(&mut got_can);
                    nn.canonicalize_words(&mut orig);
                    assert_eq!(got_can, orig, "canonical transcode of {v} from {old:?} to {new:?}");
                }
                copied += 1;
            }
        }
    }
    assert!(copied > 5000, "{copied}");
}

fn set_of(elem: Shape, max_card: usize) -> Shape {
    Shape::Set { elem: Box::new(elem), max_card }
}

fn atoms(names: &[&str]) -> Shape {
    let mut vs: Vec<Value> = names.iter().map(|a| Value::str(a)).collect();
    vs.sort();
    Shape::Atom(Arc::from(vs))
}

/// `<<>>` or `<<node, round>>` (the vertices of tests/specs/TU1).
fn vertex(hi: i64) -> Shape {
    Shape::Union(Arc::from(vec![
        Shape::Tuple(Arc::from(vec![])),
        Shape::Tuple(Arc::from(vec![atoms(&["a", "b"]), Shape::Int { lo: 0, hi }])),
    ]))
}

/// Pairs of state layouts (before and after a widening) of the specs whose
/// archived states did not re-encode as their fresh encodings:
/// tests/specs/TU1 and corpus YoYo/YoYoAllGraphs.
fn repro_layouts() -> Vec<(Vec<Shape>, Vec<Shape>)> {
    let edges = |m| set_of(Shape::Tuple(Arc::from(vec![vertex(3), vertex(5)])), m);
    let log = |m| Shape::Seq { elem: Box::new(Shape::Tuple(Arc::from(vec![atoms(&["a", "b"]), Shape::Int { lo: 0, hi: 3 }]))), max_len: m };
    let tu1 = (vec![set_of(vertex(3), 4), edges(3), log(3)], vec![set_of(vertex(3), 9), edges(3), log(3)]);
    let tu1_wider = (vec![set_of(vertex(3), 4), edges(3), log(3)], vec![set_of(vertex(3), 9), edges(6), log(5)]);
    let five = |s: Shape| Shape::Tuple(Arc::from(vec![s; 5]));
    let phase = atoms(&["leader", "source", "sink", "internal", "down", "up", "yes", "no"]);
    let node = Shape::Int { lo: 0, hi: 7 };
    let msg = Shape::Record(Arc::from(vec![
        (Sym::new("phase"), phase.clone()),
        (Sym::new("sndr"), node.clone()),
        (Sym::new("val"), node.clone()),
    ]));
    let yoyo = |inc, mailbox: Shape| {
        vec![five(Shape::Bool), five(phase.clone()), five(set_of(node.clone(), inc)), five(set_of(node.clone(), 8)), five(mailbox)]
    };
    let yoyo = (yoyo(3, set_of(Shape::Never, 0)), yoyo(3, set_of(msg.clone(), 3)));
    vec![tu1, tu1_wider, yoyo]
}

/// Transcoding random states (as `EncModel::migrate` does, variable by
/// variable) between a layout and a widened one gives the fresh encoding of
/// the decoded values in the widened layout, or fails exactly when that
/// encoding misses: on the layouts of the repros and on random widenings of
/// them.
#[test]
fn transcode_states_match_fresh_encoding() {
    let mut rng = Rng::new(4242);
    let mut copied = 0;
    for (old, new) in repro_layouts() {
        let mut pairs = vec![(old.clone(), new.clone())];
        for _ in 0..30 {
            let wider: Vec<Shape> = old
                .iter()
                .map(|s| {
                    let mut w = s.clone();
                    for _ in 0..rng.below_or_zero(3) {
                        if let Ok(v) = value(&mut rng, s, 1).normalize() {
                            w = w.join(&Shape::of(&v));
                        }
                    }
                    w
                })
                .collect();
            pairs.push((old.clone(), wider));
        }
        for (old, new) in pairs {
            let (lo, ln) = (Layout::new(old.clone()), Layout::new(new.clone()));
            for _ in 0..200 {
                let vals: Vec<Value> = old.iter().map(|s| value(&mut rng, s, 1)).collect();
                let mut src = vec![0u64; lo.words];
                if lo.encode_state(&vals, &mut src).is_err() {
                    continue;
                }
                let mut got = vec![0u64; ln.words];
                let ok = (0..new.len()).all(|i| transcode(lo.node(i), ln.node(i), &src[lo.offsets[i]..], &mut got[ln.offsets[i]..]));
                let decoded = lo.decode_state(&src);
                let mut want = vec![0u64; ln.words];
                let fits = ln.encode_state(&decoded, &mut want).is_ok();
                assert_eq!(ok, fits, "transcode of {decoded:?} from {old:?} to {new:?}");
                if ok {
                    assert_eq!(got, want, "transcode of {decoded:?} from {old:?} to {new:?}");
                    copied += 1;
                }
            }
        }
    }
    assert!(copied > 5000, "{copied}");
}

/// A bitset holding more elements than its shape's maximal cardinality is
/// not an encoding of that shape: transcoding a bitset into a set shape of
/// the same elements succeeds exactly when the target admits that many.
#[test]
fn transcode_checks_bitset_cardinality() {
    let elem = Shape::Int { lo: 0, hi: 7 };
    let wide = LayoutNode::new(&set_of(elem.clone(), 8));
    let v = Value::Set(Arc::from((1..=4).map(Value::Int).collect::<Vec<_>>()));
    let mut src = vec![0u64; wide.words()];
    wide.encode(&v, &mut src).unwrap();
    for m in 0..=8 {
        let to = LayoutNode::new(&set_of(elem.clone(), m));
        let mut got = vec![0u64; to.words()];
        let mut want = vec![0u64; to.words()];
        let fits = to.encode(&v, &mut want).is_ok();
        assert_eq!(fits, m >= 4);
        assert_eq!(transcode(&wide, &to, &src, &mut got), fits, "max_card {m}");
        if fits {
            assert_eq!(got, want);
        }
    }
}

/// Property test: `LayoutNode::cmp_tlc_words` agrees with `tlx_value::order::cmp_tlc`
/// across random shapes (scalars, packed sub-word composites, bitsets, sorted-array
/// sets, functions, maps, sequences, records, tuples, unions, dynamic witnesses, and
/// `Dyn`) whenever it returns `Some`, and returns `None` whenever `cmp_tlc` errors.
#[test]
fn cmp_tlc_words_matches_cmp_tlc_random() {
    let mut rng = Rng::new(0x517c_c1b7_2722_0a95);
    let mut compared_some = 0usize;
    let mut compared_none = 0usize;
    let mut tlc_errs = 0usize;
    for _ in 0..2500 {
        let s = shape(&mut rng, 0);
        let node = LayoutNode::new(&s);
        let w = node.words();
        let mut samples: Vec<(Value, Vec<u64>)> = Vec::new();
        for _ in 0..12 {
            let v = value(&mut rng, &s, 0);
            let mut enc = vec![0u64; w];
            if node.encode(&v, &mut enc).is_ok() {
                let dec = node.decode(&enc);
                samples.push((dec, enc));
            }
        }
        for (va, wa) in &samples {
            for (vb, wb) in &samples {
                let got = node.cmp_tlc_words(wa, wb);
                let want = tlx_value::order::cmp_tlc(va, vb);
                match (got, want) {
                    (Some(g), Ok(w)) => {
                        assert_eq!(g, w, "cmp_tlc_words mismatch for {va} vs {vb} in {s:?}");
                        compared_some += 1;
                    }
                    (Some(g), Err(e)) => {
                        panic!("cmp_tlc_words returned Some({g:?}) where cmp_tlc errored ({e:?}) for {va} vs {vb} in {s:?}");
                    }
                    (None, Ok(_)) => compared_none += 1,
                    (None, Err(_)) => tlc_errs += 1,
                }
            }
        }
    }
    assert!(compared_some > 50_000, "expected broad word-level coverage, got {compared_some}");
    assert!(compared_none > 0 || tlc_errs > 0, "expected Dyn/incomparable fallbacks");
}

/// Targeted edge cases for `LayoutNode::cmp_tlc_words`: packed sub-word scalars,
/// mixed typed/untyped/string atoms, multi-word bitsets, sorted-array sets of
/// non-word-ordered elements, dynamic-witness functions/maps, reversed-order
/// unions, `Ref` store handles, and malformed inputs.
#[test]
fn cmp_tlc_words_edge_cases() {
    use std::cmp::Ordering;
    use tlx_layout::store::StoreRef;

    let check_all = |s: &Shape, vals: &[Value], require_some_on_ok: bool| {
        let node = LayoutNode::new(s);
        let encs: Vec<Vec<u64>> = vals
            .iter()
            .map(|v| {
                let mut w = vec![0u64; node.words()];
                node.encode(v, &mut w).unwrap_or_else(|m| panic!("encode {v} in {s:?}: {m:?}"));
                w
            })
            .collect();
        for (va, wa) in vals.iter().zip(&encs) {
            for (vb, wb) in vals.iter().zip(&encs) {
                let got = node.cmp_tlc_words(wa, wb);
                let want = tlx_value::order::cmp_tlc(va, vb);
                match (got, want) {
                    (Some(g), Ok(w)) => assert_eq!(g, w, "{va} vs {vb} in {s:?}"),
                    (None, Err(_)) => {}
                    (None, Ok(w)) if !require_some_on_ok => {
                        let _ = w;
                    }
                    (g, w) => panic!("mismatch for {va} vs {vb} in {s:?}: got {g:?}, want {w:?}"),
                }
            }
        }
    };

    // 1. Mixed typed model values + untyped model value + strings (standalone and packed in Record).
    let mut mixed_atoms = vec![
        Value::model_value("a_1"),
        Value::model_value("a_2"),
        Value::model_value("b_1"),
        Value::model_value("plain"),
        Value::str("s1"),
        Value::str("s2"),
    ];
    mixed_atoms.sort();
    let mixed_shape = Shape::Atom(Arc::from(mixed_atoms.clone()));
    check_all(&mixed_shape, &mixed_atoms, true);

    let mut rec_fields =
        vec![(Sym::new("a"), Shape::Bool), (Sym::new("b"), mixed_shape.clone()), (Sym::new("c"), Shape::Int { lo: -2, hi: 2 })];
    rec_fields.sort_by_key(|f| f.0);
    let packed_rec = Shape::Record(Arc::from(rec_fields));
    assert_eq!(LayoutNode::new(&packed_rec).words(), 1, "expected sub-word packed record");
    let rec_vals: Vec<Value> = [false, true]
        .into_iter()
        .flat_map(|b| {
            mixed_atoms.iter().flat_map(move |m| {
                [-2, 0, 2].into_iter().map(move |n| {
                    Value::record(vec![(Sym::new("a"), Value::Bool(b)), (Sym::new("b"), m.clone()), (Sym::new("c"), Value::Int(n))])
                })
            })
        })
        .collect();
    check_all(&packed_rec, &rec_vals, true);

    // 2. Multi-word bitset (130 elements -> 3 words) with differing and equal cardinalities.
    let big_bitset = Shape::Set { elem: Box::new(Shape::Int { lo: 0, hi: 129 }), max_card: 130 };
    assert_eq!(LayoutNode::new(&big_bitset).words(), 3);
    let bs_vals: Vec<Value> =
        [vec![], vec![0], vec![64], vec![129], vec![1, 120], vec![2, 70], vec![0, 64, 129], vec![0, 65, 128], vec![1, 64, 128]]
            .into_iter()
            .map(|xs| Value::set_from(xs.into_iter().map(Value::Int).collect()).unwrap())
            .collect();
    check_all(&big_bitset, &bs_vals, true);

    // 3. Sorted-array set of bitsets (raw word order != TLC order: {2, 3} has smaller bitmask than {1, 4}).
    let inner_set = Shape::Set { elem: Box::new(Shape::Int { lo: 0, hi: 12 }), max_card: 13 };
    assert!(inner_set.cardinality().unwrap() > tlx_layout::shape::MAX_BITSET_UNIVERSE);
    let outer_set = Shape::Set { elem: Box::new(inner_set), max_card: 3 };
    let s14 = Value::set_from(vec![Value::Int(1), Value::Int(4)]).unwrap();
    let s23 = Value::set_from(vec![Value::Int(2), Value::Int(3)]).unwrap();
    let s0 = Value::set_from(vec![Value::Int(0)]).unwrap();
    let outer_vals: Vec<Value> = [
        vec![],
        vec![s14.clone()],
        vec![s23.clone()],
        vec![s14.clone(), s23.clone()],
        vec![s0.clone(), s23.clone()],
        vec![s0.clone(), s14.clone()],
    ]
    .into_iter()
    .map(|xs| Value::set_from(xs).unwrap())
    .collect();
    check_all(&outer_set, &outer_vals, true);

    // 4. Dynamic-witness Fcn and Map (trailing witness word must not affect TLC order).
    let dyn_fcn = Shape::Fcn {
        dom: Arc::from(vec![Value::Int(1), Value::Int(2)]),
        range: Box::new(Shape::Int { lo: 0, hi: 2 }),
        witness: FcnWitness::Dynamic,
        key_variants: Arc::from([]),
    };
    let fcn_vals = vec![
        Value::tuple(vec![Value::Int(0), Value::Int(1)]),
        Value::fcn_rcd_from_pairs(vec![(Value::Int(1), Value::Int(0)), (Value::Int(2), Value::Int(1))]).unwrap(),
        Value::tuple(vec![Value::Int(1), Value::Int(0)]),
        Value::fcn_rcd_from_pairs(vec![(Value::Int(1), Value::Int(1)), (Value::Int(2), Value::Int(0))]).unwrap(),
    ];
    check_all(&dyn_fcn, &fcn_vals, true);

    let dyn_map = Shape::Map {
        key: Box::new(Shape::Int { lo: 1, hi: 3 }),
        range: Box::new(Shape::Int { lo: 0, hi: 2 }),
        witness: FcnWitness::Dynamic,
    };
    let map_vals = vec![
        Value::tuple(vec![]),
        Value::empty_fcn(),
        Value::tuple(vec![Value::Int(1)]),
        Value::fcn_rcd_from_pairs(vec![(Value::Int(1), Value::Int(1))]).unwrap(),
        Value::fcn_rcd_from_pairs(vec![(Value::Int(2), Value::Int(0))]).unwrap(),
        Value::tuple(vec![Value::Int(0), Value::Int(2)]),
        Value::fcn_rcd_from_pairs(vec![(Value::Int(1), Value::Int(0)), (Value::Int(3), Value::Int(1))]).unwrap(),
    ];
    check_all(&dyn_map, &map_vals, true);

    // 5. Unions: reversed arm order ([Bool, Atom(untyped MV)]), [Record, Tuple], [Record, Seq], [Bool, Int].
    let bool_or_mv = Shape::Bool.join(&Shape::Atom(Arc::from(vec![Value::model_value("none")])));
    check_all(&bool_or_mv, &[Value::FALSE, Value::TRUE, Value::model_value("none")], true);

    let rec1 = Shape::Record(Arc::from(vec![(Sym::new("a"), Shape::Int { lo: 0, hi: 1 })]));
    let tup1 = Shape::Tuple(Arc::from(vec![Shape::Int { lo: 0, hi: 1 }]));
    let rec_or_tup = rec1.join(&tup1);
    check_all(
        &rec_or_tup,
        &[
            Value::record(vec![(Sym::new("a"), Value::Int(0))]),
            Value::record(vec![(Sym::new("a"), Value::Int(1))]),
            Value::tuple(vec![Value::Int(0)]),
            Value::tuple(vec![Value::Int(1)]),
        ],
        true,
    );

    let seq2 = Shape::Seq { elem: Box::new(Shape::Int { lo: 0, hi: 1 }), max_len: 2 };
    let rec_or_seq = rec1.join(&seq2);
    check_all(
        &rec_or_seq,
        &[
            Value::record(vec![(Sym::new("a"), Value::Int(0))]),
            Value::tuple(vec![]),
            Value::tuple(vec![Value::Int(0)]),
            Value::tuple(vec![Value::Int(0), Value::Int(1)]),
        ],
        true,
    );

    let bool_or_int = Shape::Bool.join(&Shape::Int { lo: 0, hi: 1 });
    check_all(&bool_or_int, &[Value::FALSE, Value::TRUE, Value::Int(0), Value::Int(1)], true);

    // 6. Store Ref handles.
    let store = StoreRef::new(usize::MAX);
    let ref_shape = Shape::Ref(store);
    check_all(
        &ref_shape,
        &[
            Value::Int(-5),
            Value::Int(7),
            Value::model_value("mv"),
            Value::set_from(vec![Value::Int(1), Value::Int(4)]).unwrap(),
            Value::set_from(vec![Value::Int(2), Value::Int(3)]).unwrap(),
        ],
        true,
    );

    // 6b. Mixed-key Map admitting incomparable key pairs (e.g. <<p1, t_A>> vs <<p1, "x">>)
    // must return None so SYMMETRY falls back to TLC's key-comparison semantics.
    let mut procs = vec![Value::model_value("p1"), Value::model_value("p2")];
    procs.sort();
    let mut mixed_tag = vec![Value::model_value("t_A"), Value::str("x")];
    mixed_tag.sort();
    let mixed_key_map = Shape::Map {
        key: Box::new(Shape::Tuple(Arc::from(vec![Shape::Atom(Arc::from(procs)), Shape::Atom(Arc::from(mixed_tag))]))),
        range: Box::new(Shape::Bool),
        witness: FcnWitness::Enumerated,
    };
    let mixed_map_node = LayoutNode::new(&mixed_key_map);
    let m1 = Value::fcn_rcd_from_pairs(vec![
        (Value::tuple(vec![Value::model_value("p1"), Value::model_value("t_A")]), Value::TRUE),
        (Value::tuple(vec![Value::model_value("p2"), Value::str("x")]), Value::TRUE),
    ])
    .unwrap();
    let m2 = Value::fcn_rcd_from_pairs(vec![
        (Value::tuple(vec![Value::model_value("p1"), Value::str("x")]), Value::TRUE),
        (Value::tuple(vec![Value::model_value("p2"), Value::model_value("t_A")]), Value::TRUE),
    ])
    .unwrap();
    let (mut w1, mut w2) = (vec![0u64; mixed_map_node.words()], vec![0u64; mixed_map_node.words()]);
    mixed_map_node.encode(&m1, &mut w1).unwrap();
    mixed_map_node.encode(&m2, &mut w2).unwrap();
    assert_eq!(mixed_map_node.cmp_tlc_words(&w1, &w2), None);

    // 7. Short/malformed slices return None without panicking.
    let seq_node = LayoutNode::new(&seq2);
    assert_eq!(seq_node.cmp_tlc_words(&[], &[]), None);
    assert_eq!(seq_node.cmp_tlc_words(&[99, 0], &[0, 0]), None);
    assert_eq!(LayoutNode::new(&Shape::Never).cmp_tlc_words(&[], &[]), None);
    assert_eq!(LayoutNode::new(&Shape::Bool).cmp_tlc_words(&[0], &[1]), Some(Ordering::Less));
}

/// `LayoutNode::encode_ref_digested` writes the same words as `encode` outside
/// `Ref` positions and the semantic digest of the interned image at each `Ref`
/// position: exactly the canonical words a fingerprint builds from a handle
/// encoding, without interning the value.
#[test]
fn encode_ref_digested_matches_handle_digests() {
    use tlx_layout::store::StoreRef;

    let store = StoreRef::new(usize::MAX);
    let bag = Value::set_from(vec![Value::Int(1), Value::Int(4)]).unwrap();
    let shape = Shape::Tuple(Arc::from(vec![Shape::Int { lo: 0, hi: 10 }, Shape::Ref(store.clone())]));
    let node = LayoutNode::new(&shape);
    let value = Value::tuple(vec![Value::Int(3), bag.clone()]);
    let mut encoded = vec![0u64; node.words()];
    node.encode(&value, &mut encoded).unwrap();
    let mut digested = vec![0u64; node.words()];
    node.encode_ref_digested(&value, &mut digested).unwrap();
    assert_eq!(digested[0], encoded[0]);
    assert_eq!(digested[1], store.digest(encoded[1]));
    assert_eq!(digested[1], tlx_layout::store::digest_of_value(&bag).unwrap());
    // Long pressure-mode searches digest one Ref value per state/permutation:
    // more operations than the process-wide 16-bit store-id space must not
    // create (or exhaust) any store.
    let ref_node = LayoutNode::new(&Shape::Ref(StoreRef::new(usize::MAX)));
    let mut ref_words = [0u64];
    for i in 0..70_000 {
        ref_node.encode_ref_digested(&Value::Int(i), &mut ref_words).unwrap();
    }
}
