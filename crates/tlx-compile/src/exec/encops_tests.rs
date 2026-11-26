use std::collections::BTreeSet;

use super::*;

/// The sorted-array encoding of `set` (elements of `k` words) with room
/// for `max_card` elements.
fn enc(set: &BTreeSet<Vec<u64>>, k: usize, max_card: usize) -> Vec<u64> {
    let mut w = vec![0; 1 + max_card * k];
    w[0] = set.len() as u64;
    for (i, e) in set.iter().enumerate() {
        w[1 + i * k..1 + (i + 1) * k].copy_from_slice(e);
    }
    w
}

/// Small random sets of 2-word elements (a deterministic LCG).
struct Gen(u64);

impl Gen {
    fn next(&mut self, m: u64) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (self.0 >> 33) % m
    }
    fn elem(&mut self) -> Vec<u64> {
        vec![self.next(3), self.next(4)]
    }
    fn set(&mut self, max: usize) -> BTreeSet<Vec<u64>> {
        let n = self.next(max as u64 + 1) as usize;
        (0..n).map(|_| self.elem()).collect()
    }
}

const K: usize = 2;
const MAX: usize = 6;

#[test]
fn membership() {
    let mut g = Gen(1);
    for _ in 0..500 {
        let s = g.set(MAX);
        let x = g.elem();
        assert_eq!(sorted_member(&enc(&s, K, MAX), &x, K), s.contains(&x), "{s:?} {x:?}");
    }
    assert!(!sorted_member(&enc(&BTreeSet::new(), K, 0), &[0, 0], K));
}

#[test]
fn insertion_in_and_out_of_place() {
    let mut g = Gen(2);
    for _ in 0..500 {
        let s = g.set(MAX);
        let x = g.elem();
        let mut want = s.clone();
        want.insert(x.clone());
        let fits = want.len() <= MAX;
        let w = enc(&s, K, MAX);
        let mut out = vec![u64::MAX; w.len()];
        assert_eq!(sorted_insert(&mut out, &w, &x, K, MAX as u64), fits, "{s:?} + {x:?}");
        let mut inplace = w.clone();
        assert_eq!(sorted_add(&mut inplace, &x, K, MAX as u64), fits, "{s:?} + {x:?}");
        if fits {
            assert_eq!(out, enc(&want, K, MAX));
            assert_eq!(inplace, enc(&want, K, MAX));
        }
    }
    // A full set: adding a present element is fine, a new one is not.
    let full: BTreeSet<Vec<u64>> = (0..MAX as u64).map(|i| vec![i / 4, i % 4]).collect();
    let w = enc(&full, K, MAX);
    let mut out = vec![0; w.len()];
    assert!(sorted_insert(&mut out, &w, &[0, 1], K, MAX as u64) && out == w);
    assert!(!sorted_insert(&mut out, &w, &[2, 3], K, MAX as u64));
    assert!(!sorted_add(&mut w.clone(), &[2, 3], K, MAX as u64));
}

#[test]
fn union_intersection_difference() {
    let mut g = Gen(3);
    for _ in 0..500 {
        let (a, b) = (g.set(MAX), g.set(MAX));
        let max_card = g.next(2 * MAX as u64 + 1) as usize;
        for op in [SetOp::Union, SetOp::Inter, SetOp::Diff] {
            let want: BTreeSet<Vec<u64>> = match op {
                SetOp::Union => a.union(&b).cloned().collect(),
                SetOp::Inter => a.intersection(&b).cloned().collect(),
                SetOp::Diff => a.difference(&b).cloned().collect(),
            };
            let mut out = vec![u64::MAX; 1 + max_card * K];
            let ok = sorted_op(op, &enc(&a, K, MAX), &enc(&b, K, MAX), K, max_card as u64, &mut out);
            assert_eq!(ok, want.len() <= max_card, "{op:?} {a:?} {b:?} max {max_card}");
            if ok {
                assert_eq!(out, enc(&want, K, max_card), "{op:?} {a:?} {b:?}");
            }
        }
    }
}

/// `SUBSET` order: by size, then lexicographically.
#[test]
fn combinations() {
    let mut all = Vec::new();
    for_each_combination(4, |idx| all.push(idx.to_vec()));
    assert_eq!(all.len(), 16);
    assert_eq!(all[..7], [vec![], vec![0], vec![1], vec![2], vec![3], vec![0, 1], vec![0, 2]]);
    assert_eq!(all[15], [0, 1, 2, 3]);
    for w in all.windows(2) {
        assert!((w[0].len(), &w[0]) < (w[1].len(), &w[1]), "{w:?}");
    }
    let mut seen = 0;
    for_each_combination(0, |idx| {
        assert!(idx.is_empty());
        seen += 1;
    });
    assert_eq!(seen, 1);
    let mut last = [1, 2, 3];
    assert!(!next_combination(&mut last, 4) && last == [1, 2, 3]);

    // Streaming early-stop on 2^31 combinations without allocating them all.
    let mut head = Vec::new();
    let completed = try_for_each_combination::<()>(31, |idx| {
        head.push(idx.to_vec());
        Ok(head.len() < 3)
    })
    .unwrap();
    assert!(!completed);
    assert_eq!(head, [vec![], vec![0], vec![1]]);

    // Error propagation stops immediately.
    let mut steps = 0;
    let err = try_for_each_combination(31, |_| {
        steps += 1;
        if steps == 2 {
            Err("boom")
        } else {
            Ok(true)
        }
    });
    assert_eq!(err, Err("boom"));
    assert_eq!(steps, 2);
}
