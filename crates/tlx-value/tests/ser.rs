//! Binary serialization (`tlx_value::ser`): property-style round trips on
//! random values, malformed input and intern table restore.

use std::sync::Arc;
use std::time::Instant;

use tlx_base::frame;
use tlx_value::fingerprint::fingerprint;
use tlx_value::ser::{decode_value, encode_value, Reader, Writer};
use tlx_value::{LazySet, Sym, Value};

use tlx_testkit::XorShift64Star as Rng;

const WORDS: &[&str] = &["a", "b", "", "ser_x", "ser_long_field_name", "ñ", "αβγ", "with space", "c_1", "q_w"];

fn int(r: &mut Rng) -> i64 {
    match r.below(6) {
        0 => i64::MIN,
        1 => i64::MAX,
        2 => r.next_u64() as i64,
        3 => -(r.below(1000) as i64),
        _ => r.below(200) as i64,
    }
}

fn word(r: &mut Rng) -> String {
    if r.chance(20, 100) {
        format!("ser_rand_{}", r.below(50))
    } else {
        WORDS[r.below(WORDS.len() as u64) as usize].to_string()
    }
}

/// A random value whose sets are homogeneous (so they can be normalized).
fn value(r: &mut Rng, depth: u32) -> Value {
    let leaf = depth == 0 || r.chance(35, 100);
    if leaf {
        return match r.below(6) {
            0 => Value::Bool(r.chance(50, 100)),
            1 | 2 => Value::Int(int(r)),
            3 => Value::str(&word(r)),
            4 => Value::model_value(&word(r)),
            _ => {
                let lo = r.below(20) as i64 - 10;
                Value::Interval(lo, lo + r.below(15) as i64 - 3)
            }
        };
    }
    let d = depth - 1;
    let n = r.below(6) as usize;
    match r.below(7) {
        0 | 1 => {
            // Elements comparable with the first one (TLC cannot compare
            // e.g. integers with strings).
            let first = value(r, d);
            let mut elems = vec![first.clone()];
            for _ in 1..n {
                let e = value(r, d);
                if Value::set_from(vec![first.clone(), e.clone()]).is_ok() {
                    elems.push(e);
                }
            }
            Value::set_from(elems).unwrap_or_else(|_| Value::set_from(vec![first]).unwrap())
        }
        2 => Value::tuple((0..n).map(|_| value(r, d)).collect()),
        3 => Value::record((0..n.max(1)).map(|_| (Sym::new(&word(r)), value(r, d))).collect()),
        4 => {
            // Functions with int, model-value or tuple keys.
            let mut keys: Vec<Value> = match r.below(3) {
                0 => (0..n).map(|_| Value::Int(r.below(10) as i64 - 3)).collect(),
                1 => (0..n).map(|_| Value::model_value(&word(r))).collect(),
                _ => (0..n).map(|_| Value::tuple(vec![Value::Int(r.below(4) as i64), Value::Bool(r.chance(50, 100))])).collect(),
            };
            keys.sort();
            keys.dedup();
            Value::fcn_from_pairs(keys.into_iter().map(|k| (k, value(r, d))).collect()).unwrap_or_else(|_| Value::empty_set())
        }
        5 => match r.below(4) {
            0 => Value::LazySet(Arc::new(LazySet::Nat)),
            1 => Value::LazySet(Arc::new(LazySet::Int)),
            2 => Value::LazySet(Arc::new(LazySet::StringSet)),
            _ => Value::LazySet(Arc::new(LazySet::Seq(Value::set_from(vec![Value::Int(1), Value::Int(2)]).unwrap()))),
        },
        _ => Value::Interval(int(r), int(r)),
    }
}

/// Contains an infinite built-in set (not comparable with `==`).
fn has_builtin(v: &Value) -> bool {
    match v {
        Value::LazySet(_) => true,
        Value::Set(es) | Value::Tuple(es) => es.iter().any(has_builtin),
        Value::Record(fs) => fs.iter().any(|f| has_builtin(&f.1)),
        Value::Fcn(ps, _) => ps.iter().any(|(k, x)| has_builtin(k) || has_builtin(x)),
        _ => false,
    }
}

fn reencode(v: &Value) -> Vec<u8> {
    encode_value(v).expect("encode")
}

#[test]
fn random_values_round_trip() {
    let mut r = Rng::new(0x5eed_1234_abcd_ef01);
    let mut seen = [0usize; 256];
    // Miri runs ~1000x slower; shrink the sample, keeping the generator depth
    // cycling and the round-trip assertions identical.
    let n = if cfg!(miri) { 100 } else { 20_000 };
    for i in 0..n {
        let v = value(&mut r, 1 + (i % 5));
        let bytes = reencode(&v);
        for &b in &bytes {
            seen[b as usize] += 1;
        }
        let back = decode_value(&bytes).unwrap_or_else(|e| panic!("decode {v}: {e}"));
        // Identical representation (re-encoding gives the same bytes), equal
        // value, equal fingerprint.
        assert_eq!(reencode(&back), bytes, "{v}");
        if !has_builtin(&v) {
            assert!(back == v, "{v} != {back}");
            if let Ok(f) = fingerprint(&v) {
                assert_eq!(fingerprint(&back).unwrap(), f, "{v}");
            }
        }
        assert_eq!(format!("{back}"), format!("{v}"));
    }
    // Generator coverage: nested compound values of every kind occur (tag
    // bytes also appear inside payloads, so this is a lower bound check).
    let nested_sets = (0..n as u64)
        .map(|i| value(&mut Rng::new(i * 2 + 1), 4))
        .filter(|v| matches!(v, Value::Set(es) if es.iter().any(|e| matches!(e, Value::Set(_) | Value::Record(_) | Value::Fcn(..)))))
        .count();
    assert!(nested_sets > n as usize / 200, "{nested_sets}");
    assert!((0..=14).all(|t| seen[t] > n as usize / 400), "{:?}", &seen[..15]);
}

#[test]
fn stream_of_values_shares_symbols() {
    let vals: Vec<Value> = (0..100)
        .map(|i| Value::record(vec![(Sym::new("ser_name"), Value::str("ser_shared")), (Sym::new("ser_i"), Value::Int(i))]))
        .collect();
    let mut w = Writer::new();
    for v in &vals {
        w.value(v).unwrap();
    }
    let one = encode_value(&vals[0]).unwrap().len();
    // Texts are written once; later records take about 9 bytes each.
    assert!(w.len() < one + 99 * 10, "{} bytes", w.len());
    let bytes = w.into_bytes();
    let mut r = Reader::new(&bytes);
    for v in &vals {
        assert!(r.value().unwrap() == *v);
    }
    r.finish().unwrap();
}

#[test]
fn lazy_values_are_normalized() {
    let s = Value::set_from(vec![Value::Int(1), Value::Int(2)]).unwrap();
    let subset = Value::LazySet(Arc::new(LazySet::Subset(s.clone())));
    let back = decode_value(&encode_value(&subset).unwrap()).unwrap();
    assert!(matches!(back, Value::Set(_)));
    assert!(back == subset);
    // Infinite sets that are not built in cannot be written.
    let inf = Value::LazySet(Arc::new(LazySet::Subset(Value::LazySet(Arc::new(LazySet::Nat)))));
    assert!(encode_value(&inf).is_err());
}

#[test]
fn malformed_input_is_rejected() {
    let mut r = Rng::new(42);
    let mut samples = Vec::new();
    // Miri runs ~1000x slower; each sample decodes every proper prefix, so
    // a smaller sample still covers the rejection paths.
    let samples_n = if cfg!(miri) { 8 } else { 300 };
    for _ in 0..samples_n {
        samples.push(reencode(&value(&mut r, 4)));
    }
    for bytes in &samples {
        // Every proper prefix fails (no panic, no hang).
        for cut in 0..bytes.len() {
            assert!(decode_value(&bytes[..cut]).is_err());
        }
        // Random corruption: may decode to something else, must not panic.
        for _ in 0..5 {
            let mut b = bytes.clone();
            let i = r.below(b.len() as u64) as usize;
            b[i] = r.next_u64() as u8;
            let _ = decode_value(&b);
        }
    }
    assert!(decode_value(&[200]).is_err());
    // Huge counts are rejected before allocating.
    assert!(decode_value(&[5, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0x7f]).is_err());
    // Deep nesting is rejected, not a stack overflow. Decoding recurses to
    // MAX_DEPTH, so run it on a thread with a stack the default test thread
    // does not provide in debug builds.
    std::thread::Builder::new()
        .stack_size(64 << 20)
        .spawn(|| {
            let mut deep = [7u8, 1].repeat(100_000);
            deep.push(0);
            assert!(decode_value(&deep).is_err());
        })
        .unwrap()
        .join()
        .unwrap();
    // Trailing bytes.
    assert!(decode_value(&[1, 1]).is_err());
}

/// Tags: 2 `Int` (zigzag varint), 5 `Set`, 7 `Tuple`, 9 `Fcn`, 0 `FALSE`,
/// 1 `TRUE`. A `Value` cannot hold a set or a function domain that is not
/// sorted, so these streams are written by hand; only debug builds check
/// them (release builds trust the encoder and decode them as they are).
#[test]
#[cfg(debug_assertions)]
fn non_canonical_set_and_function_are_rejected() {
    // {2, 1}: elements out of order.
    assert!(decode_value(&[5, 2, 2, 4, 2, 2]).is_err());
    // {1, 1}: duplicate element.
    assert!(decode_value(&[5, 2, 2, 2, 2, 2]).is_err());
    // {1, 2}: canonical.
    assert!(decode_value(&[5, 2, 2, 2, 2, 4]).is_ok());
    // [2 |-> TRUE, 1 |-> FALSE]: domain out of order.
    assert!(decode_value(&[9, 2, 2, 4, 1, 2, 2, 0]).is_err());
    // [1 |-> FALSE, 2 |-> TRUE]: canonical.
    assert!(decode_value(&[9, 2, 2, 2, 0, 2, 4, 1]).is_ok());
    // A tuple may repeat and reorder: <<2, 1>> is fine.
    assert!(decode_value(&[7, 2, 2, 4, 2, 2]).is_ok());
}

#[test]
fn intern_table_snapshot_restores_in_place() {
    // Within one process the table is trivially a prefix of its snapshot;
    // the cross-process case is covered by tlx-layout's ser_recover test.
    Sym::new("ser_intern_probe");
    let mut w = Writer::new();
    tlx_value::ser::write_intern_table(&mut w);
    let bytes = w.into_bytes();
    let mut r = Reader::new(&bytes);
    let texts = tlx_value::ser::read_intern_table(&mut r).unwrap();
    r.finish().unwrap();
    assert!(texts.contains(&"ser_intern_probe"));
    tlx_value::intern::restore(&texts).unwrap();
    // A conflicting order is refused.
    let mut bad: Vec<&str> = texts.clone();
    let i = bad.iter().position(|t| *t == "ser_intern_probe").unwrap();
    bad.swap(0, i);
    if i != 0 {
        let e = tlx_value::intern::restore(&bad).unwrap_err();
        assert!(e.contains("intern order"), "{e}");
    }
}

/// Light throughput measurement (run with `--ignored --nocapture`).
#[test]
#[ignore]
fn bench_large_values() {
    // A large set of records (typical state component) and a deep function.
    let recs: Vec<Value> = (0..200_000)
        .map(|i| {
            Value::record(vec![
                (Sym::new("ser_src"), Value::model_value(&format!("ser_n{}", i % 16))),
                (Sym::new("ser_seq"), Value::tuple((0..4).map(|j| Value::Int(i * 4 + j)).collect())),
                (Sym::new("ser_ok"), Value::Bool(i % 3 == 0)),
            ])
        })
        .collect();
    let big = Value::set_from(recs).unwrap();
    let ints = Value::tuple((0..2_000_000).map(Value::Int).collect());
    for (name, v) in [("set of 200k records", &big), ("tuple of 2M ints", &ints)] {
        let reps = 5;
        let t = Instant::now();
        let mut bytes = Vec::new();
        for _ in 0..reps {
            bytes = encode_value(v).unwrap();
        }
        let enc = t.elapsed().as_secs_f64() / reps as f64;
        let t = Instant::now();
        for _ in 0..reps {
            std::hint::black_box(decode_value(&bytes).unwrap());
        }
        let dec = t.elapsed().as_secs_f64() / reps as f64;
        let t = Instant::now();
        for _ in 0..reps {
            std::hint::black_box(frame::checksum(0, &bytes));
        }
        let sum = t.elapsed().as_secs_f64() / reps as f64;
        let mb = bytes.len() as f64 / 1e6;
        println!(
            "{name}: {mb:.1} MB; encode {:.1} ms ({:.0} MB/s), decode {:.1} ms ({:.0} MB/s), checksum {:.0} MB/s",
            enc * 1e3,
            mb / enc,
            dec * 1e3,
            mb / dec,
            mb / sum
        );
    }
}
