//! Operations on encoded sets shared by the Rust executors: the closure
//! executor (`exec::fast`) calls them directly, the JIT through the thin
//! `extern "C"` wrappers of `jit::rt`. They mirror the C helpers of
//! `cgen/runtime.h` (which stay C: the generated code inlines them), and
//! the executors are cross-checked against each other (`TLX_PARANOID`,
//! `TLX_JIT_VERIFY` with the testkit's `exec_vs_native`).
//!
//! A sorted-array set (`Shape::Set` without a bitset universe) is
//! `[len, e_0, ..., e_{len-1}, 0...]`: its `len` elements of `k` words each
//! (k >= 1) in ascending order (word-wise lexicographic: the order of the
//! encodings), then zeros up to its `max_card` elements.

use std::cmp::Ordering;

use crate::ir::SetOp;

/// Element `i` of the sorted-array set `s` (elements of `k` words).
#[inline]
fn elem(s: &[u64], i: usize, k: usize) -> &[u64] {
    &s[1 + i * k..1 + (i + 1) * k]
}

/// Where `x` is in the sorted-array set `s`: `Ok(i)` if it is element
/// `i`, else `Err(i)` with `i` the number of smaller elements. A linear
/// scan, as `tlx_sorted_insert`/`tlx_sorted_add` (an insertion shifts the
/// larger elements anyway).
#[inline]
fn position(s: &[u64], x: &[u64], k: usize) -> Result<usize, usize> {
    let len = s[0] as usize;
    let mut pos = 0;
    while pos < len {
        match elem(s, pos, k).cmp(x) {
            Ordering::Equal => return Ok(pos),
            Ordering::Greater => break,
            Ordering::Less => pos += 1,
        }
    }
    Err(pos)
}

/// `x \in s` (`tlx_sorted_member`: binary search).
pub fn sorted_member(s: &[u64], x: &[u64], k: usize) -> bool {
    let (mut lo, mut hi) = (0i64, s[0] as i64 - 1);
    while lo <= hi {
        let mid = (lo + hi) >> 1;
        match elem(s, mid as usize, k).cmp(x) {
            Ordering::Equal => return true,
            Ordering::Less => lo = mid + 1,
            Ordering::Greater => hi = mid - 1,
        }
    }
    false
}

/// `s \cup {x}` into `out` (`s.len()` words, as `out`;
/// `tlx_sorted_insert`); false if it would have more than `max_card`
/// elements.
pub fn sorted_insert(out: &mut [u64], s: &[u64], x: &[u64], k: usize, max_card: u64) -> bool {
    let len = s[0] as usize;
    let pos = match position(s, x, k) {
        Ok(_) => {
            out.copy_from_slice(s);
            return true;
        }
        Err(pos) => pos,
    };
    if len as u64 + 1 > max_card {
        return false;
    }
    out.fill(0);
    out[0] = len as u64 + 1;
    out[1..1 + pos * k].copy_from_slice(&s[1..1 + pos * k]);
    out[1 + pos * k..1 + (pos + 1) * k].copy_from_slice(x);
    out[1 + (pos + 1) * k..1 + (len + 1) * k].copy_from_slice(&s[1 + pos * k..1 + len * k]);
    true
}

/// `s \cup {x}` in place (`tlx_sorted_add`; `s` has room for one more
/// element unless it has `max_card` elements); false if it would have more
/// than `max_card` elements.
pub fn sorted_add(s: &mut [u64], x: &[u64], k: usize, max_card: u64) -> bool {
    let len = s[0] as usize;
    let Err(pos) = position(s, x, k) else { return true };
    if len as u64 + 1 > max_card {
        return false;
    }
    s.copy_within(1 + pos * k..1 + len * k, 1 + (pos + 1) * k);
    s[1 + pos * k..1 + (pos + 1) * k].copy_from_slice(x);
    s[0] = len as u64 + 1;
    true
}

/// Union / intersection / difference of the sorted-array sets `a` and `b`
/// into `out` (`tlx_sorted_op`; zero-filled first); false if the result has
/// more than `max_card` elements.
pub fn sorted_op(op: SetOp, a: &[u64], b: &[u64], k: usize, max_card: u64, out: &mut [u64]) -> bool {
    let (la, lb) = (a[0] as usize, b[0] as usize);
    let (mut i, mut j, mut len) = (0, 0, 0usize);
    out.fill(0);
    while i < la || j < lb {
        let (x, fa, fb) = if i < la && j < lb {
            let (xa, xb) = (elem(a, i, k), elem(b, j, k));
            match xa.cmp(xb) {
                Ordering::Equal => (xa, true, true),
                Ordering::Less => (xa, true, false),
                Ordering::Greater => (xb, false, true),
            }
        } else if i < la {
            (elem(a, i, k), true, false)
        } else {
            (elem(b, j, k), false, true)
        };
        let keep = match op {
            SetOp::Union => true,
            SetOp::Inter => fa && fb,
            SetOp::Diff => fa && !fb,
        };
        if keep {
            if len as u64 == max_card {
                return false;
            }
            out[1 + len * k..1 + (len + 1) * k].copy_from_slice(x);
            len += 1;
        }
        i += fa as usize;
        j += fb as usize;
    }
    out[0] = len as u64;
    true
}

/// Advance `idx` (a strictly increasing k-combination of `0..n`) to the
/// next one in lexicographic order; false (and `idx` unchanged) after the
/// last one.
#[inline]
pub fn next_combination(idx: &mut [u32], n: u32) -> bool {
    let k = idx.len();
    let mut i = k;
    while i > 0 && idx[i - 1] == n - k as u32 + i as u32 - 1 {
        i -= 1;
    }
    if i == 0 {
        return false;
    }
    idx[i - 1] += 1;
    for j in i..k {
        idx[j] = idx[j - 1] + 1;
    }
    true
}

/// Call `f` on the index sets of the subsets of `0..n`, by size, then in
/// lexicographic order (the order of `SUBSET`).
pub fn for_each_combination(n: u32, mut f: impl FnMut(&[u32])) {
    let _ = try_for_each_combination(n, |idx| {
        f(idx);
        Ok::<_, std::convert::Infallible>(true)
    });
}

/// Fallible, early-stopping version of [`for_each_combination`]: yields each
/// combination on demand and stops as soon as `f` returns `Ok(false)` (then
/// returning `Ok(false)`) or `Err(e)`.
pub fn try_for_each_combination<E>(n: u32, mut f: impl FnMut(&[u32]) -> Result<bool, E>) -> Result<bool, E> {
    for k in 0..=n {
        let mut idx: Vec<u32> = (0..k).collect();
        loop {
            if !f(&idx)? {
                return Ok(false);
            }
            if !next_combination(&mut idx, n) {
                break;
            }
        }
    }
    Ok(true)
}

#[cfg(test)]
#[path = "encops_tests.rs"]
mod tests;
