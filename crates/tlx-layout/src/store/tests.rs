//! Differential tests of the store against the interpreter's values and
//! operations (`tlx_value`), on random finite values with aliases.

use std::cell::Cell;
use std::sync::Arc;

use tlx_base::rng::SplitMix64;
use tlx_value::{ops, order, FcnDom, Sym, Value};

use super::*;

thread_local! {
    static TINY: Cell<bool> = const { Cell::new(false) };
}

/// Under `with_tiny_hashes`, exact hashes keep 3 bits: nearly every
/// interning compares structurally against colliding nodes.
pub(super) fn tiny_hash(h: u64) -> u64 {
    if TINY.with(|t| t.get()) {
        h & (7 << 61)
    } else {
        h
    }
}

fn with_tiny_hashes<T>(f: impl FnOnce() -> T) -> T {
    TINY.with(|t| t.set(true));
    let r = f();
    TINY.with(|t| t.set(false));
    r
}

struct Gen(SplitMix64);

impl Gen {
    fn new(seed: u64) -> Gen {
        Gen(SplitMix64::new(seed))
    }
    fn below(&mut self, n: usize) -> usize {
        self.0.below(n)
    }
    fn scalar(&mut self) -> Value {
        match self.below(9) {
            0 => Value::Bool(self.below(2) == 1),
            1..=3 => Value::Int(self.below(5) as i64),
            4 => Value::Int((1i64 << 61) + self.below(2) as i64),
            5 | 6 => Value::str(["a", "b", "c"][self.below(3)]),
            _ => Value::model_value(["m1", "m2"][self.below(2)]),
        }
    }
    /// A random finite value of depth at most `d` (sets of comparable
    /// elements: one kind per set).
    fn value(&mut self, d: u32) -> Value {
        if d == 0 {
            return self.scalar();
        }
        match self.below(10) {
            0 | 1 => self.scalar(),
            2 => {
                let lo = self.below(3) as i64;
                Value::Interval(lo, lo + self.below(4) as i64 - 1)
            }
            3 => {
                let kind = self.below(3);
                let es: Vec<Value> = (0..self.below(4))
                    .map(|_| match kind {
                        0 => Value::Int(self.below(6) as i64),
                        1 => Value::str(["a", "b", "c", "d"][self.below(4)]),
                        _ => Value::tuple((0..self.below(2)).map(|_| Value::Int(self.below(3) as i64)).collect()),
                    })
                    .collect();
                Value::set_from(es).unwrap()
            }
            4 => Value::tuple((0..self.below(4)).map(|_| self.value(d - 1)).collect()),
            5 => {
                let names = ["a", "b", "c"];
                let fs: Vec<(Sym, Value)> = (0..1 + self.below(3)).map(|i| (Sym::new(names[i]), self.value(d - 1))).collect();
                Value::record(fs)
            }
            6 => {
                // A function over an enumerated domain of comparable keys.
                let n = self.below(4);
                let keys: Vec<Value> = match self.below(3) {
                    0 => (0..n).map(|i| Value::Int(i as i64 + self.below(2) as i64)).collect(),
                    1 => (0..n).map(|i| Value::str(["a", "b", "c", "d"][i])).collect(),
                    _ => (0..n).map(|i| Value::record(vec![(Sym::new("k"), Value::Int(i as i64))])).collect(),
                };
                let mut keys = keys;
                keys.dedup();
                let pairs = keys.into_iter().map(|k| (k, self.value(d - 1))).collect();
                Value::fcn_rcd_from_pairs(pairs).unwrap()
            }
            7 => {
                let lo = self.below(3) as i64;
                let n = self.below(3) as i64;
                let pairs = (lo..lo + n).map(|k| (Value::Int(k), self.value(d - 1))).collect();
                Value::fcn_over(&Value::Interval(lo, lo + n - 1), pairs).unwrap()
            }
            _ => {
                // An alias: a tuple or record as a function over an
                // enumerated domain.
                let v = self.value(d - 1);
                match v {
                    Value::Tuple(_) | Value::Record(_) => v.into_fcn_rcd(),
                    v => v,
                }
            }
        }
    }
}

/// Equality of representations: the same variants, domains and children.
fn exact(a: &Value, b: &Value) -> bool {
    match (a, b) {
        (Value::Set(x), Value::Set(y)) | (Value::Tuple(x), Value::Tuple(y)) => {
            x.len() == y.len() && x.iter().zip(y.iter()).all(|(p, q)| exact(p, q))
        }
        (Value::Record(x), Value::Record(y)) => x.len() == y.len() && x.iter().zip(y.iter()).all(|(p, q)| p.0 == q.0 && exact(&p.1, &q.1)),
        (Value::Fcn(x, d), Value::Fcn(y, e)) => {
            d == e && x.len() == y.len() && x.iter().zip(y.iter()).all(|(p, q)| exact(&p.0, &q.0) && exact(&p.1, &q.1))
        }
        (Value::Interval(a, b), Value::Interval(c, d)) => a == c && b == d,
        (Value::Int(x), Value::Int(y)) => x == y,
        (Value::Bool(x), Value::Bool(y)) => x == y,
        (Value::Str(x), Value::Str(y)) | (Value::ModelValue(x), Value::ModelValue(y)) => x == y,
        _ => false,
    }
}

fn values(seed: u64, n: usize) -> Vec<Value> {
    let mut g = Gen::new(seed);
    let mut vs: Vec<Value> = (0..n).map(|_| g.value(3)).collect();
    // The alias pairs the contract names, explicitly.
    let one_two = Value::tuple(vec![Value::Int(1), Value::Int(2)]);
    vs.push(one_two.clone());
    vs.push(
        Value::fcn_over(
            &Value::set_from(vec![Value::Int(1), Value::Int(2)]).unwrap(),
            vec![(Value::Int(1), Value::Int(1)), (Value::Int(2), Value::Int(2))],
        )
        .unwrap(),
    );
    vs.push(one_two.into_fcn_rcd());
    let rec = Value::record(vec![(Sym::new("a"), Value::Int(1))]);
    vs.push(rec.clone());
    vs.push(rec.into_fcn_rcd());
    vs.push(Value::tuple(vec![]));
    vs.push(Value::empty_fcn());
    vs.push(Value::empty_set());
    vs.push(Value::Interval(1, 0));
    vs.push(Value::Interval(1, 3));
    vs.push(Value::set_from(vec![Value::Int(1), Value::Int(2), Value::Int(3)]).unwrap());
    vs
}

#[test]
fn freeze_thaw_is_exact_and_interning_is_by_representation() {
    for tiny in [false, true] {
        let run = || {
            let s = Store::new(usize::MAX);
            let vs = values(1, 400);
            let hs: Vec<u64> = vs.iter().map(|v| s.freeze(v).unwrap()).collect();
            for (v, h) in vs.iter().zip(&hs) {
                assert!(exact(&s.thaw(*h), v), "{v} thawed as {}", s.thaw(*h));
                assert_eq!(s.freeze(v).unwrap(), *h);
                assert!(s.is_valid(*h));
            }
            for (i, a) in vs.iter().enumerate() {
                for (j, b) in vs.iter().enumerate() {
                    assert_eq!(hs[i] == hs[j], exact(a, b), "{a} / {b}");
                }
            }
        };
        if tiny {
            with_tiny_hashes(run)
        } else {
            run()
        }
    }
}

/// Digests follow the interpreter's equality, aliases included, and so
/// does `same_value`.
#[test]
fn digests_follow_value_equality() {
    let s = Store::new(usize::MAX);
    let vs = values(2, 400);
    let hs: Vec<u64> = vs.iter().map(|v| s.freeze(v).unwrap()).collect();
    for (i, a) in vs.iter().enumerate() {
        for (j, b) in vs.iter().enumerate() {
            let eq = a == b;
            assert_eq!(s.digest(hs[i]) == s.digest(hs[j]), eq, "{a} / {b}");
            assert_eq!(s.same_value(hs[i], hs[j]), eq, "{a} / {b}");
        }
        assert_eq!(digest_of_value(a).unwrap(), s.digest(hs[i]));
    }
    // A digest does not depend on the store or on the order of interning.
    let t = Store::new(usize::MAX);
    for (v, h) in vs.iter().zip(&hs).rev() {
        assert_eq!(t.digest(t.freeze(v).unwrap()), s.digest(*h));
    }
}

/// The comparisons agree with `tlx_value::order` exactly (results and
/// errors), on every pair.
#[test]
fn comparisons_match_the_interpreter() {
    let s = Store::new(usize::MAX);
    let mut vs = values(3, 250);
    vs.push(Value::model_value("m_typed"));
    vs.push(Value::model_value("n_other"));
    let hs: Vec<u64> = vs.iter().map(|v| s.freeze(v).unwrap()).collect();
    for (i, a) in vs.iter().enumerate() {
        for (j, b) in vs.iter().enumerate() {
            let want = order::eq_tlc(a, b).ok();
            assert_eq!(eq_tlc(&s, hs[i], hs[j]).ok(), want, "{a} = {b}");
            let want = order::cmp_tlc(a, b).ok();
            assert_eq!(cmp_tlc(&s, hs[i], hs[j]).ok(), want, "compare {a} with {b}");
        }
    }
}

/// `got` (a store operation) against `want` (the interpreter's): equal
/// representations on success; an interpreter error is a store error. A
/// store error where the interpreter succeeds is counted (a fallback).
fn check(s: &Store, what: &str, got: Result<u64, RefOpError>, want: tlx_value::Result<Value>, fallbacks: &mut usize) {
    match (got, want) {
        (Ok(h), Ok(v)) => assert!(exact(&s.thaw(h), &v), "{what}: store {} interpreter {v}", s.thaw(h)),
        (Err(_), Err(_)) => {}
        (Ok(h), Err(e)) => panic!("{what}: store {} where the interpreter fails: {e}", s.thaw(h)),
        (Err(_), Ok(v)) => {
            eprintln!("FALLBACK {what} -> {v}");
            *fallbacks += 1
        }
    }
}

#[test]
fn operations_match_the_interpreter() {
    let s = Store::new(usize::MAX);
    let vs = values(4, 160);
    let hs: Vec<u64> = vs.iter().map(|v| s.freeze(v).unwrap()).collect();
    let mut fallbacks = 0;
    let int = |b: bool| s.freeze(&Value::Bool(b)).unwrap();
    for (f, hf) in vs.iter().zip(&hs) {
        check(&s, &format!("DOMAIN {f}"), s.domain(*hf), ops::domain(f), &mut fallbacks);
        check(&s, &format!("Len({f})"), s.len(*hf).map(|n| s.freeze(&Value::Int(n)).unwrap()), ops::len(f).map(Value::Int), &mut fallbacks);
        check(&s, &format!("Head({f})"), s.head(*hf), ops::head(f), &mut fallbacks);
        // (Tail of a string makes a string: left to the interpreter, which
        // keeps the strings' creation order.)
        if !matches!(f, Value::Str(_)) {
            check(&s, &format!("Tail({f})"), s.tail(*hf), ops::tail(f), &mut fallbacks);
        }
        if f.is_set() {
            check(
                &s,
                &format!("Cardinality({f})"),
                s.cardinality(*hf).map(|n| s.freeze(&Value::Int(n)).unwrap()),
                ops::cardinality(f).map(Value::Int),
                &mut fallbacks,
            );
        }
        for (k, hk) in vs.iter().zip(&hs).step_by(3) {
            check(&s, &format!("{f}[{k}]"), s.apply(*hf, *hk), ops::apply(f, k), &mut fallbacks);
            let sel = s.select(*hf, *hk);
            match (sel, ops::select(f, k)) {
                (Ok(Some(i)), Ok(Some(v))) => assert!(exact(&s.thaw(s.value_at(*hf, i)), &v)),
                (Ok(None), Ok(None)) | (Err(_), Err(_)) | (Err(_), Ok(_)) => {}
                (got, want) => panic!("select {f} [{k}]: {got:?} / {want:?}"),
            }
            // EXCEPT ![k] = TRUE (after the select).
            if let (Ok(Some(i)), Ok(Some(_))) = (s.select(*hf, *hk), ops::select(f, k)) {
                check(
                    &s,
                    &format!("[{f} EXCEPT ![{k}]]"),
                    s.set_at(*hf, i, int(true)),
                    ops::except(f, k, Value::Bool(true)),
                    &mut fallbacks,
                );
            }
            check(&s, &format!("{k} :> {f}"), s.single(*hk, *hf), ops::single_fcn(k.clone(), f.clone()), &mut fallbacks);
            check(&s, &format!("{f} @@ {k}"), s.merge(*hf, *hk), ops::fcn_merge(f, k), &mut fallbacks);
            check(&s, &format!("Append({f}, {k})"), s.append(*hf, *hk), ops::append(f, k.clone()), &mut fallbacks);
            let as_bool = |r: Result<bool, RefOpError>| r.map(int);
            check(&s, &format!("{k} \\in {f}"), as_bool(s.member(*hk, *hf)), ops::member(k, f).map(Value::Bool), &mut fallbacks);
            let dom = ops::domain(f).and_then(|d| ops::member(k, &d));
            check(&s, &format!("{k} \\in DOMAIN {f}"), as_bool(s.in_domain(*hk, *hf)), dom.map(Value::Bool), &mut fallbacks);
        }
    }
    assert_eq!(fallbacks, 0, "operations left to the interpreter");
}

/// Functions of 31/32/33 and 255/256/257 entries (TLC switches from a
/// linear to a binary key search at 32): lookups of present, absent and
/// ill-typed keys, updates and merges agree with the interpreter.
#[test]
fn growth_across_the_search_schedules() {
    let s = Store::new(usize::MAX);
    let mut fallbacks = 0;
    for n in [31usize, 32, 33, 255, 256, 257] {
        let keysets: [Vec<Value>; 3] = [
            (0..n)
                .map(|i| {
                    Value::record(vec![
                        (Sym::new("id"), Value::Int(i as i64)),
                        (Sym::new("seq"), Value::tuple(vec![Value::Int(i as i64 % 3)])),
                    ])
                })
                .collect(),
            (0..n).map(|i| Value::Int(2 * i as i64)).collect(),
            (0..n).map(|i| Value::str(&format!("k{i:03}"))).collect(),
        ];
        for keys in keysets {
            let f = Value::fcn_rcd_from_pairs(keys.iter().map(|k| (k.clone(), Value::Int(0))).collect()).unwrap();
            let hf = s.freeze(&f).unwrap();
            let mut probes: Vec<Value> = vec![keys[0].clone(), keys[n / 2].clone(), keys[n - 1].clone()];
            probes.extend([Value::Int(1), Value::Int(-1), Value::model_value("m1"), Value::str("zz"), Value::empty_set()]);
            probes.push(Value::record(vec![(Sym::new("id"), Value::Int(n as i64))]));
            for k in &probes {
                let hk = s.freeze(k).unwrap();
                check(&s, &format!("n={n} f[{k}]"), s.apply(hf, hk), ops::apply(&f, k), &mut fallbacks);
                let g = Value::fcn_rcd_from_pairs(vec![(k.clone(), Value::Int(1))]);
                if let Ok(g) = g {
                    let hg = s.freeze(&g).unwrap();
                    check(&s, &format!("n={n} f @@ ({k} :> 1)"), s.merge(hf, hg), ops::fcn_merge(&f, &g), &mut fallbacks);
                    check(&s, &format!("n={n} ({k} :> 1) @@ f"), s.merge(hg, hf), ops::fcn_merge(&g, &f), &mut fallbacks);
                }
                if let (Ok(Some(i)), Ok(Some(_))) = (s.select(hf, hk), ops::select(&f, k)) {
                    let one = s.freeze(&Value::Int(1)).unwrap();
                    check(&s, &format!("n={n} EXCEPT ![{k}]"), s.set_at(hf, i, one), ops::except(&f, k, Value::Int(1)), &mut fallbacks);
                }
                let dom = ops::domain(&f).and_then(|d| ops::member(k, &d));
                let got = s.in_domain(hk, hf).map(|b| s.freeze(&Value::Bool(b)).unwrap());
                check(&s, &format!("n={n} {k} \\in DOMAIN f"), got, dom.map(Value::Bool), &mut fallbacks);
            }
        }
    }
    assert_eq!(fallbacks, 0);
}

/// An operation that fails part-way (incomparable keys in `@@`) publishes
/// nothing; the store keeps working.
#[test]
fn failed_operations_publish_nothing() {
    let s = Store::new(usize::MAX);
    let f = s.freeze(&Value::fcn_rcd_from_pairs(vec![(Value::Int(1), Value::Int(0)), (Value::Int(5), Value::Int(0))]).unwrap()).unwrap();
    let g = s.freeze(&Value::fcn_rcd_from_pairs(vec![(Value::str("x"), Value::Int(0))]).unwrap()).unwrap();
    let before = s.stats().nodes;
    assert_eq!(s.merge(f, g), Err(RefOpError::Eval));
    assert_eq!(s.stats().nodes, before);
    assert!(s.merge(f, f).is_ok());
}

#[test]
fn the_budget_is_a_hard_limit() {
    let s = Store::new(4096);
    let big = Value::tuple((0..10_000).map(Value::Int).collect());
    assert_eq!(s.freeze(&big), Err(StoreError::Full));
    assert!(s.is_full());
    assert!(s.stats().node_bytes <= 4096);
}

#[test]
fn handles_of_another_store_are_rejected() {
    let (a, b) = (Store::new(usize::MAX), Store::new(usize::MAX));
    let h = a.freeze(&Value::tuple(vec![Value::Int(1)])).unwrap();
    assert!(a.node(h).is_some());
    assert!(b.node(h).is_none());
    assert!(!b.is_valid(h));
    assert!(b.try_thaw(h).is_none());
    assert!(a.try_thaw(h ^ (1 << 40)).is_none());
    assert!(!a.is_valid(0));
}

#[test]
fn store_ids_never_wrap_or_reuse() {
    let next = AtomicU64::new((1 << STORE_BITS) - 1);
    assert_eq!(allocate_uid(&next), (1 << STORE_BITS) - 1);
    for _ in 0..2 {
        assert!(std::panic::catch_unwind(|| allocate_uid(&next)).is_err());
        assert_eq!(next.load(Ordering::Relaxed), 1 << STORE_BITS);
    }
}

/// `Shape::Ref` is one shape per store: shapes of one store are equal (and
/// hash alike), of two stores differ, and print alike (generated code does
/// not depend on the store); a layout mixing two stores is refused.
#[test]
fn shapes_identify_their_store() {
    use std::hash::{BuildHasher, BuildHasherDefault};
    let (a, b) = (StoreRef::new(usize::MAX), StoreRef::new(usize::MAX));
    let hash = |s: &crate::Shape| BuildHasherDefault::<std::collections::hash_map::DefaultHasher>::default().hash_one(s);
    let (ra, ra2, rb) = (crate::Shape::Ref(a.clone()), crate::Shape::Ref(a.clone()), crate::Shape::Ref(b.clone()));
    assert_eq!(ra, ra2);
    assert_eq!(hash(&ra), hash(&ra2));
    assert_ne!(ra, rb);
    assert_eq!(format!("{ra:?}"), format!("{rb:?}"));
    assert_ne!(a.uid(), b.uid());
    let pair = |x: &crate::Shape, y: &crate::Shape| crate::Shape::Tuple(vec![x.clone(), y.clone()].into());
    assert_eq!(crate::layout::store_of([&pair(&crate::Shape::Bool, &ra)]), Some(a.clone()));
    assert_eq!(crate::layout::store_of([&ra, &ra2]), Some(a.clone()));
    assert_eq!(crate::layout::store_of([&crate::Shape::Bool]), None);
    let mixed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| crate::layout::store_of([&pair(&ra, &rb)])));
    assert!(mixed.is_err(), "a layout of two stores");
}

#[test]
fn concurrent_interning_agrees() {
    let s = Store::new(usize::MAX);
    let vs = Arc::new(values(5, 200));
    let all: Vec<Vec<u64>> = std::thread::scope(|sc| {
        let hs: Vec<_> = (0..8)
            .map(|t| {
                let (s, vs) = (&s, vs.clone());
                sc.spawn(move || {
                    let mut out: Vec<u64> = vec![0; vs.len()];
                    for i in 0..vs.len() {
                        let j = (i + t * 37) % vs.len();
                        out[j] = s.freeze(&vs[j]).unwrap();
                    }
                    out
                })
            })
            .collect();
        hs.into_iter().map(|h| h.join().unwrap()).collect()
    });
    assert!(all.windows(2).all(|w| w[0] == w[1]));
    for (v, h) in vs.iter().zip(&all[0]) {
        assert!(exact(&s.thaw(*h), v));
    }
}

#[test]
fn intervals_and_big_integers_keep_their_representation() {
    let s = Store::new(usize::MAX);
    let iv = s.freeze(&Value::Interval(2, 4)).unwrap();
    let set = s.freeze(&Value::set_from(vec![Value::Int(2), Value::Int(3), Value::Int(4)]).unwrap()).unwrap();
    assert_ne!(iv, set);
    assert_eq!(s.digest(iv), s.digest(set));
    assert_eq!(s.set_elems(iv).unwrap(), s.set_elems(set).unwrap());
    let big = s.freeze(&Value::Int(1 << 62)).unwrap();
    assert!(matches!(s.thaw(big), Value::Int(x) if x == 1 << 62));
    assert_eq!(s.member(big, iv), Ok(false));
    let f = s.freeze(&Value::Fcn(Arc::from(vec![(Value::Int(0), Value::Int(1))]), FcnDom::Interval)).unwrap();
    assert_eq!(s.select(f, s.freeze(&Value::str("a")).unwrap()), Err(RefOpError::Eval));
}

#[test]
fn snapshot_round_trip_preserves_values_digests_witnesses_and_stats() {
    use tlx_value::ser::{Reader, Writer};

    for tiny in [false, true] {
        let run = || {
            let orig = Store::new(usize::MAX);
            let vs = values(7, 400);
            let hs: Vec<u64> = vs.iter().map(|v| orig.freeze(v).unwrap()).collect();

            let mut w = Writer::new();
            orig.write_snapshot(&mut w).unwrap();
            let bytes = w.into_bytes();

            // Determinism: writing again produces byte-for-byte identical output.
            let mut w2 = Writer::new();
            orig.write_snapshot(&mut w2).unwrap();
            assert_eq!(bytes, w2.into_bytes());

            let mut r = Reader::new(&bytes);
            let restored = Store::read_snapshot(&mut r, usize::MAX).unwrap();
            assert_ne!(restored.uid(), orig.uid(), "restored store must allocate a fresh uid");
            assert_eq!(restored.stats(), orig.stats(), "restored stats must match");

            for (v, &oh) in vs.iter().zip(&hs) {
                let ck = orig.checkpoint_handle(oh);
                let rh = restored.recover_handle(ck).unwrap();
                if tag(oh) == TAG_NODE {
                    assert_ne!(rh, oh, "node handle store_id must be rewritten to fresh store");
                    assert!(!restored.is_valid(oh), "foreign store handle must remain invalid");
                } else {
                    assert_eq!(rh, oh);
                }
                assert!(exact(&restored.thaw(rh), v), "thaw mismatch for {v}");
                assert_eq!(restored.digest(rh), orig.digest(oh), "digest mismatch for {v}");
                // Re-freezing must hit the restored shard intern index without allocating a new node.
                assert_eq!(restored.freeze(v).unwrap(), rh);
            }
            assert_eq!(restored.stats().nodes, orig.stats().nodes, "re-freezing allocated duplicate nodes");
        };
        if tiny {
            with_tiny_hashes(run);
        } else {
            run();
        }
    }
}

#[test]
fn snapshot_restore_rejects_corrupt_and_invalid_inputs() {
    use tlx_base::bytes::zigzag;
    use tlx_value::ser::{Reader, Writer};

    let restore = |bytes: &[u8], budget: usize| -> Result<Arc<Store>, String> {
        let mut r = Reader::new(bytes);
        Store::read_snapshot(&mut r, budget)
    };

    // Valid snapshot with several nodes for truncation / trailing-byte / budget tests.
    let orig = Store::new(usize::MAX);
    let big_tuple = Value::tuple(vec![
        Value::Int(1 << 62),
        Value::Interval(2, 5),
        Value::record(vec![(Sym::new("store_ser_a"), Value::str("store_ser_v"))]),
        Value::fcn_over(&Value::Interval(0, 1), vec![(Value::Int(0), Value::TRUE), (Value::Int(1), Value::FALSE)]).unwrap(),
    ]);
    let root = orig.freeze(&big_tuple).unwrap();
    let mut w = Writer::new();
    orig.write_snapshot(&mut w).unwrap();
    let valid = w.into_bytes();

    // Every strict prefix is rejected as truncated.
    for cut in 0..valid.len() {
        assert!(restore(&valid[..cut], usize::MAX).is_err(), "truncated at {cut} was accepted");
    }

    // Trailing garbage rejected.
    let mut trailing = valid.clone();
    trailing.push(0);
    assert!(restore(&trailing, usize::MAX).unwrap_err().contains("trailing"));

    // Budget overflow rejected cleanly.
    let need = orig.stats().node_bytes as usize;
    let err = restore(&valid, need - 1).unwrap_err();
    assert!(err.contains("exceeds its budget"), "{err}");
    assert!(restore(&valid, need).is_ok());

    // Unsupported version rejected.
    let mut w = Writer::new();
    w.uvar(99);
    w.usize(0);
    assert!(restore(&w.into_bytes(), usize::MAX).unwrap_err().contains("version 99"));

    // Unknown body tag rejected.
    let mut w = Writer::new();
    w.uvar(1);
    w.usize(1);
    w.u8(99);
    assert!(restore(&w.into_bytes(), usize::MAX).unwrap_err().contains("unknown body tag"));

    // Self / forward / out-of-range node reference rejected (node 0 referencing node 0).
    let mut w = Writer::new();
    w.uvar(1);
    w.usize(1);
    w.u8(4); // Body::Tuple
    w.usize(1);
    w.uvar((0u64 << TAG_BITS) | TAG_NODE);
    assert!(restore(&w.into_bytes(), usize::MAX).unwrap_err().contains("out-of-range/forward"));

    // Forward reference: node 0 referencing node 1.
    let mut w = Writer::new();
    w.uvar(1);
    w.usize(2);
    w.u8(4); // Tuple [node 1]
    w.usize(1);
    w.uvar((1u64 << TAG_BITS) | TAG_NODE);
    w.u8(4); // Tuple []
    w.usize(0);
    assert!(restore(&w.into_bytes(), usize::MAX).unwrap_err().contains("out-of-range/forward"));

    // Invalid child handle tag (0) and non-canonical boolean payload.
    for bad_child in [0u64, (2u64 << TAG_BITS) | TAG_BOOL, 6u64] {
        let mut w = Writer::new();
        w.uvar(1);
        w.usize(1);
        w.u8(4);
        w.usize(1);
        w.uvar(bad_child);
        assert!(restore(&w.into_bytes(), usize::MAX).is_err(), "bad child {bad_child:#x} accepted");
    }

    // Unpublished Sym ID in immediate string handle and in Record field key.
    let bad_sym: u64 = 0x7fff_ffff;
    let mut w = Writer::new();
    w.uvar(1);
    w.usize(1);
    w.u8(4); // Tuple [Str(bad_sym)]
    w.usize(1);
    w.uvar((bad_sym << TAG_BITS) | TAG_STR);
    assert!(restore(&w.into_bytes(), usize::MAX).unwrap_err().contains("unpublished symbol"));

    let mut w = Writer::new();
    w.uvar(1);
    w.usize(1);
    w.u8(5); // Record [(bad_sym, TRUE)]
    w.usize(1);
    w.uvar(bad_sym);
    w.uvar(bool_handle(true));
    assert!(restore(&w.into_bytes(), usize::MAX).unwrap_err().contains("unpublished symbol"));

    // Immediate integer encoded as Body::Int rejected.
    let mut w = Writer::new();
    w.uvar(1);
    w.usize(1);
    w.u8(1); // Body::Int
    w.ivar(42);
    assert!(restore(&w.into_bytes(), usize::MAX).unwrap_err().contains("immediate integer"));

    // Empty record and unsorted record fields rejected.
    let mut w = Writer::new();
    w.uvar(1);
    w.usize(1);
    w.u8(5);
    w.usize(0);
    assert!(restore(&w.into_bytes(), usize::MAX).unwrap_err().contains("empty record"));

    let s1 = Sym::new("store_ser_order_first");
    let s2 = Sym::new("store_ser_order_second");
    let (lo_sym, hi_sym) = if s1 < s2 { (s1, s2) } else { (s2, s1) };
    let mut w = Writer::new();
    w.uvar(1);
    w.usize(1);
    w.u8(5);
    w.usize(2);
    w.uvar(hi_sym.id() as u64);
    w.uvar(bool_handle(false));
    w.uvar(lo_sym.id() as u64);
    w.uvar(bool_handle(true));
    assert!(restore(&w.into_bytes(), usize::MAX).unwrap_err().contains("strict symbol order"));

    // Unsorted set elements rejected.
    let mut w = Writer::new();
    w.uvar(1);
    w.usize(1);
    w.u8(2); // Body::Set
    w.usize(2);
    w.uvar((zigzag(2) << TAG_BITS) | TAG_INT);
    w.uvar((zigzag(1) << TAG_BITS) | TAG_INT);
    assert!(restore(&w.into_bytes(), usize::MAX).unwrap_err().contains("canonical order"));

    // Non-contiguous FcnDom::Interval keys rejected.
    let mut w = Writer::new();
    w.uvar(1);
    w.usize(1);
    w.u8(7); // Body::Fcn(_, Interval)
    w.usize(2);
    w.uvar((zigzag(0) << TAG_BITS) | TAG_INT);
    w.uvar((zigzag(2) << TAG_BITS) | TAG_INT);
    w.uvar(bool_handle(false));
    w.uvar(bool_handle(true));
    assert!(restore(&w.into_bytes(), usize::MAX).unwrap_err().contains("contiguous"));

    // Oversized interval rejected.
    let mut w = Writer::new();
    w.uvar(1);
    w.usize(1);
    w.u8(3); // Body::Interval
    w.ivar(0);
    w.ivar(i32::MAX as i64 + 10);
    assert!(restore(&w.into_bytes(), usize::MAX).unwrap_err().contains("32-bit"));

    // Duplicate node body rejected.
    let mut w = Writer::new();
    w.uvar(1);
    w.usize(2);
    w.u8(4);
    w.usize(0);
    w.u8(4);
    w.usize(0);
    assert!(restore(&w.into_bytes(), usize::MAX).unwrap_err().contains("duplicate node body"));

    // `recover_handle` rejects non-zero store_id, out-of-range node index, zero, and unpublished symbol.
    let restored = restore(&valid, usize::MAX).unwrap();
    let ck_root = orig.checkpoint_handle(root);
    assert!(restored.recover_handle(ck_root).is_ok());
    assert!(restored.recover_handle(root).unwrap_err().contains("non-zero checkpoint store id"));
    assert!(restored.recover_handle((999_999u64 << INDEX_SHIFT) | TAG_NODE).unwrap_err().contains("node out of range"));
    assert!(restored.recover_handle(0).unwrap_err().contains("invalid immediate"));
    assert!(restored.recover_handle((bad_sym << TAG_BITS) | TAG_STR).unwrap_err().contains("invalid immediate"));
}

/// Restoring or comparing a set containing a large compact interval (e.g.
/// `{{0}, 1..8000000}`) compares cardinalities first and walks equal-length
/// intervals lazily, never materializing `Node::elems`.
#[test]
fn snapshot_restore_and_comparisons_keep_intervals_compact() {
    use tlx_value::ser::{Reader, Writer};

    let orig = Store::new(usize::MAX);
    let zero_set = Value::set_from(vec![Value::Int(0)]).unwrap();
    let big_iv = Value::Interval(1, 8_000_000);
    let outer = Value::set_from(vec![zero_set.clone(), big_iv.clone()]).unwrap();
    let h_outer = orig.freeze(&outer).unwrap();
    let h_iv = orig.freeze(&big_iv).unwrap();
    assert!(orig.get(h_iv).elems.get().is_none(), "freeze must not materialize interval elems");

    let mut w = Writer::new();
    orig.write_snapshot(&mut w).unwrap();
    let bytes = w.into_bytes();

    let mut r = Reader::new(&bytes);
    let restored = Store::read_snapshot(&mut r, usize::MAX).unwrap();
    let r_iv = restored.recover_handle(orig.checkpoint_handle(h_iv)).unwrap();
    let r_outer = restored.recover_handle(orig.checkpoint_handle(h_outer)).unwrap();
    assert!(restored.get(r_iv).elems.get().is_none(), "restore order validation materialized interval elems");
    assert!(exact(&restored.thaw(r_outer), &outer));

    // Equal-length set vs interval comparisons also stay lazy without populating `elems`.
    let r_zero = restored.recover_handle(orig.checkpoint_handle(orig.freeze(&zero_set).unwrap())).unwrap();
    assert_eq!(cmp_tlc(&restored, r_zero, r_iv), Ok(std::cmp::Ordering::Less));
    assert_eq!(cmp_tlc(&restored, r_iv, r_zero), Ok(std::cmp::Ordering::Greater));
    assert_eq!(eq_tlc(&restored, r_zero, r_iv), Ok(false));
    assert_eq!(eq_tlc(&restored, r_iv, r_zero), Ok(false));
    assert!(restored.get(r_iv).elems.get().is_none(), "different-length comparisons materialized interval elems");

    let small_iv = restored.freeze(&Value::Interval(1, 3)).unwrap();
    let eq_set = restored.freeze(&Value::set_from(vec![Value::Int(1), Value::Int(2), Value::Int(3)]).unwrap()).unwrap();
    let gt_set = restored.freeze(&Value::set_from(vec![Value::Int(1), Value::Int(2), Value::Int(4)]).unwrap()).unwrap();
    assert_eq!(eq_tlc(&restored, eq_set, small_iv), Ok(true));
    assert_eq!(eq_tlc(&restored, small_iv, eq_set), Ok(true));
    assert_eq!(cmp_tlc(&restored, eq_set, small_iv), Ok(std::cmp::Ordering::Equal));
    assert_eq!(cmp_tlc(&restored, small_iv, eq_set), Ok(std::cmp::Ordering::Equal));
    assert_eq!(cmp_tlc(&restored, small_iv, gt_set), Ok(std::cmp::Ordering::Less));
    assert_eq!(cmp_tlc(&restored, gt_set, small_iv), Ok(std::cmp::Ordering::Greater));
    assert!(restored.get(small_iv).elems.get().is_none(), "equal-length comparisons materialized interval elems");
}

/// An oversized node exceeding the remaining budget is rejected immediately
/// after decoding its count, before allocating or scanning its body.
#[test]
fn snapshot_restore_rejects_oversized_node_before_allocating() {
    use tlx_value::ser::{Reader, Writer};

    let count = 200_000usize;
    let budget = 4096usize;
    let bool_byte = bool_handle(false) as u8;
    let sym_id = Sym::new("budget_precheck_sym").id() as u64;

    // Tuple, Set, Record, and Fcn payloads whose element count alone exceeds `budget`.
    let cases: [(&str, Vec<u8>); 4] = [
        ("tuple", {
            let mut w = Writer::with_capacity(count + 16);
            w.uvar(1);
            w.usize(1);
            w.u8(4);
            w.usize(count);
            let mut b = w.into_bytes();
            b.resize(b.len() + count, bool_byte);
            b
        }),
        ("set", {
            let mut w = Writer::with_capacity(count + 16);
            w.uvar(1);
            w.usize(1);
            w.u8(2);
            w.usize(count);
            let mut b = w.into_bytes();
            b.resize(b.len() + count, bool_byte);
            b
        }),
        ("record", {
            let mut w = Writer::with_capacity(count * 2 + 16);
            w.uvar(1);
            w.usize(1);
            w.u8(5);
            w.usize(count);
            w.uvar(sym_id);
            let mut b = w.into_bytes();
            b.resize(b.len() + count * 2, bool_byte);
            b
        }),
        ("fcn", {
            let mut w = Writer::with_capacity(count * 2 + 16);
            w.uvar(1);
            w.usize(1);
            w.u8(6);
            w.usize(count);
            let mut b = w.into_bytes();
            b.resize(b.len() + count * 2, bool_byte);
            b
        }),
    ];

    for (kind, bytes) in cases {
        let mut r = Reader::new(&bytes);
        let err = Store::read_snapshot(&mut r, budget).unwrap_err();
        assert!(err.contains("exceeds its budget"), "{kind}: {err}");
        assert!(r.pos() < 32, "{kind}: reader scanned {} bytes before rejecting budget overflow", r.pos());
    }
}

/// 64-bit interval endpoints (`> IMM_INT`) and interval-backed functions with
/// node-backed `Body::Int` keys (including ranges straddling `IMM_INT`) round-trip
/// cleanly, compare lazily without populating `Node::elems`, and still reject
/// non-contiguous keys.
#[test]
fn snapshot_restore_preserves_64bit_intervals_and_interval_function_keys() {
    use tlx_value::ser::{Reader, Writer};

    let ns_lo: i64 = 1_735_689_600_000_000_000;
    let ns_hi: i64 = ns_lo + 3;
    let straddle_lo: i64 = crate::scalar::IMM_INT - 2;
    let straddle_hi: i64 = crate::scalar::IMM_INT + 1;

    let orig = Store::new(usize::MAX);
    let ns_iv = Value::Interval(ns_lo, ns_hi);
    let ns_set = Value::set_from((ns_lo..=ns_hi).map(Value::Int).collect()).unwrap();
    let ns_set_gt = Value::set_from(vec![Value::Int(ns_lo), Value::Int(ns_lo + 1), Value::Int(ns_lo + 2), Value::Int(ns_hi + 1)]).unwrap();
    let ns_fcn = Value::fcn_over(&ns_iv, (ns_lo..=ns_hi).map(|k| (Value::Int(k), Value::TRUE)).collect()).unwrap();
    let straddle_iv = Value::Interval(straddle_lo, straddle_hi);
    let straddle_fcn =
        Value::fcn_over(&straddle_iv, (straddle_lo..=straddle_hi).map(|k| (Value::Int(k), Value::Int(k - straddle_lo))).collect()).unwrap();
    let empty_64 = Value::Interval(ns_hi, ns_lo);
    let outer = Value::set_from(vec![Value::set_from(vec![Value::Int(0)]).unwrap(), ns_iv.clone()]).unwrap();
    let all = [ns_iv.clone(), ns_set.clone(), ns_set_gt.clone(), ns_fcn, straddle_iv, straddle_fcn, empty_64, outer];
    let hs: Vec<u64> = all.iter().map(|v| orig.freeze(v).unwrap()).collect();

    let mut w = Writer::new();
    orig.write_snapshot(&mut w).unwrap();
    let bytes = w.into_bytes();

    let mut r = Reader::new(&bytes);
    let restored = Store::read_snapshot(&mut r, usize::MAX).unwrap();
    assert_eq!(restored.stats(), orig.stats());

    let rhs: Vec<u64> = hs.iter().map(|&h| restored.recover_handle(orig.checkpoint_handle(h)).unwrap()).collect();
    for (v, &rh) in all.iter().zip(&rhs) {
        assert!(exact(&restored.thaw(rh), v), "thaw mismatch for {v}");
        assert_eq!(restored.freeze(v).unwrap(), rh);
    }

    // Equal-length set vs 64-bit interval comparisons stay lazy and exact.
    let (r_iv, r_set, r_gt, r_straddle_iv, r_empty_64) = (rhs[0], rhs[1], rhs[2], rhs[4], rhs[6]);
    assert_eq!(eq_tlc(&restored, r_iv, r_set), Ok(true));
    assert_eq!(eq_tlc(&restored, r_set, r_iv), Ok(true));
    assert_eq!(cmp_tlc(&restored, r_iv, r_set), Ok(std::cmp::Ordering::Equal));
    assert_eq!(cmp_tlc(&restored, r_set, r_iv), Ok(std::cmp::Ordering::Equal));
    assert_eq!(cmp_tlc(&restored, r_iv, r_gt), Ok(std::cmp::Ordering::Less));
    assert_eq!(cmp_tlc(&restored, r_gt, r_iv), Ok(std::cmp::Ordering::Greater));
    assert!(restored.get(r_iv).elems.get().is_none());

    // Non-empty intervals with non-immediate endpoints return None from
    // `set_elems` (routing compiled iteration through the interpreter fallback)
    // without populating `Node::elems`; empty 64-bit intervals return `&[]`.
    assert_eq!(restored.set_elems(r_iv), None);
    assert!(restored.get(r_iv).elems.get().is_none());
    assert_eq!(restored.set_elems(r_straddle_iv), None);
    assert!(restored.get(r_straddle_iv).elems.get().is_none());
    assert_eq!(restored.set_elems(r_empty_64), Some(&[][..]));
    assert!(restored.get(r_empty_64).elems.get().is_none());

    // Non-contiguous 64-bit interval function keys are still rejected.
    let mut w = Writer::new();
    w.uvar(1);
    w.usize(3);
    // node 0: Body::Int(ns_lo)
    w.u8(1);
    w.ivar(ns_lo);
    // node 1: Body::Int(ns_lo + 2) (gap!)
    w.u8(1);
    w.ivar(ns_lo + 2);
    // node 2: Body::Fcn([node 0, node 1], Interval)
    w.u8(7);
    w.usize(2);
    w.uvar((0u64 << TAG_BITS) | TAG_NODE);
    w.uvar((1u64 << TAG_BITS) | TAG_NODE);
    w.uvar(bool_handle(true));
    w.uvar(bool_handle(true));
    let bad = w.into_bytes();
    let mut r = Reader::new(&bad);
    assert!(Store::read_snapshot(&mut r, usize::MAX).unwrap_err().contains("contiguous"));
}
