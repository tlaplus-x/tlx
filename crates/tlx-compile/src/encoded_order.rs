//! TLC ordering of encoded elements, without decoding or allocating Values.
//!
//! The prefix plan is shared by the IR executor, JIT runtime and generated C:
//! each node is [opcode, encoding words, plan words, child count, children...].
//! `schema` owns the wire constants. C declarations are checked against it by
//! the independent Rust/C vector test; the JIT calls this Rust implementation.

use std::cmp::Ordering;
use std::sync::Arc;

use tlx_layout::{layout, Shape};
use tlx_value::Value;

/// Prefix-node ABI. Keep C's representation-specific loops, but check every
/// declaration against this schema rather than maintaining numeric accesses.
pub(crate) mod schema {
    macro_rules! schema {
        ($($name:ident: $ty:ty = $value:expr),* $(,)?) => {
            $(pub(crate) const $name: $ty = $value;)*

            #[cfg(test)]
            #[test]
            fn c_declarations_match_schema() {
                let assertions = [$(format!("_Static_assert(TLXC_ORDER_{} == {}, \"ordered schema: {}\");\n",
                    stringify!($name), $name, stringify!($name))),*].concat();
                let dir = tlx_testkit::TempDir::new("ordered-schema");
                let c = include_str!("cgen/runtime.h");
                for (header, valid) in [(c.to_owned(), true), (c.replace("TLXC_ORDER_SPAN = 2", "TLXC_ORDER_SPAN = 99"), false)] {
                    let source = dir.write("schema.c", &format!("#include <stdint.h>\n#include <string.h>\n{header}\n{assertions}"));
                    let result = std::process::Command::new("cc").args(["-std=c11", "-fsyntax-only"]).arg(source).output().unwrap();
                    assert_eq!(result.status.success(), valid, "{}", String::from_utf8_lossy(&result.stderr));
                    if !valid {
                        assert!(String::from_utf8_lossy(&result.stderr).contains("ordered schema: SPAN"));
                    }
                }
            }
        };
    }

    schema! {
        WORDS: u64 = 0,
        SET: u64 = 1,
        PRODUCT: u64 = 2,
        UNION: u64 = 3,
        OPCODE: usize = 0,
        WIDTH: usize = 1,
        SPAN: usize = 2,
        CHILDREN: usize = 3,
        HEADER: usize = 4,
    }
}

use schema::*;

pub(crate) fn order_safe(s: &Shape) -> bool {
    match s {
        _ if s.is_scalar() => true,
        // One value only: every comparison is equal whatever the encoding
        // (an empty set of an unobserved element, a fixed record of them).
        _ if s.cardinality() == Some(1) => true,
        Shape::Record(fs) => fs.iter().all(|(_, f)| order_safe(f)),
        Shape::Tuple(es) => es.iter().all(order_safe),
        // A function of a fixed domain: every value of the shape has that
        // domain, so TLC's comparison (domains first, then the values in
        // domain order) is the one of its range's slots in that order.
        Shape::Fcn { range, .. } => order_safe(range),
        // A sequence is a function on `1..n`: TLC compares the lengths first
        // and then the elements in order (`tlx_value::order::cmp_tuples`,
        // reached through `fcn_cmp`'s `length_order`), which is the word order
        // of the encoding (`len`, then `max_len` element slots, zero-padded
        // past the length): two sequences of different lengths differ in the
        // first word, and equal lengths compare their slots in order.
        Shape::Seq { elem, .. } => order_safe(elem),
        Shape::Union(arms) => homogeneous(arms) && arms.iter().all(order_safe),
        _ => false,
    }
}

fn homogeneous(arms: &[Shape]) -> bool {
    arms.iter().all(|a| matches!(a, Shape::Record(_))) || arms.iter().all(|a| matches!(a, Shape::Tuple(_)))
}

// Untyped model values sort before every non-model value. The shape
// registry puts that atom arm first; other heterogeneous unions may
// contain incomparable kinds and must use the interpreter.
fn model_union(arms: &[Shape]) -> bool {
    matches!(arms, [Shape::Atom(vs), rest] if vs.iter().all(|v| matches!(v, Value::ModelValue(m) if m.model_value_type().is_none()))
        && !matches!(rest, Shape::Atom(_) | Shape::Union(_) | Shape::Dyn | Shape::Never))
}

/// Word-aligned child of a `PRODUCT` or `UNION` ordering plan.
#[derive(Clone, Copy)]
enum Part<'a> {
    /// A single `u64` word of packed MSB-first scalars (compared directly via `WORDS`).
    PackedWord,
    /// A word-aligned child shape.
    Shape(&'a Shape),
}

fn product_parts<'a>(shapes: impl IntoIterator<Item = &'a Shape>) -> Vec<Part<'a>> {
    let shapes: Vec<&'a Shape> = shapes.into_iter().collect();
    let fl = layout::FieldLayout::of_shapes(shapes.iter().copied());
    fl.word_groups()
        .iter()
        .map(|g| match g {
            layout::FieldGroup::Word { index, .. } => Part::Shape(shapes[*index]),
            layout::FieldGroup::Packed { .. } => Part::PackedWord,
        })
        .collect()
}

/// The wire opcode and children, shared by construction and validation.
fn node_parts(s: &Shape) -> Option<(u64, Vec<Part<'_>>)> {
    Some(match s {
        _ if order_safe(s) => (WORDS, vec![]),
        Shape::Set { elem, .. } if elem.is_scalar() && layout::bitset_universe(elem).is_some_and(|n| n <= 64) => (SET, vec![]),
        Shape::Record(fs) => (PRODUCT, product_parts(fs.iter().map(|(_, s)| s))),
        Shape::Tuple(es) => (PRODUCT, product_parts(es.iter())),
        // One slot per domain element, in the shape's domain order.
        Shape::Fcn { dom, range } => (PRODUCT, product_parts(std::iter::repeat_n(&**range, dom.len()))),
        Shape::Union(arms) if homogeneous(arms) || model_union(arms) => (UNION, arms.iter().map(Part::Shape).collect()),
        _ => return None,
    })
}

/// Only plans whose comparisons cannot raise a TLC incomparable-value error.
/// Collections with unknown element order stay boxed.
pub(crate) fn plan(s: &Shape) -> Option<Arc<[u64]>> {
    fn node(p: Part<'_>, out: &mut Vec<u64>) -> Option<()> {
        match p {
            Part::PackedWord => {
                out.extend([WORDS, 1, HEADER as u64, 0]);
                Some(())
            }
            Part::Shape(s) => {
                let start = out.len();
                let (op, children) = node_parts(s)?;
                out.extend([op, layout::words(s) as u64, 0, children.len() as u64]);
                for c in children {
                    node(c, out)?;
                }
                out[start + SPAN] = (out.len() - start) as u64;
                Some(())
            }
        }
    }
    let mut out = vec![];
    node(Part::Shape(s), &mut out)?;
    Some(out.into())
}

/// Borrowed plan whose complete tree and optional rank table match the shape.
/// Checking happens at the IR boundary; execution keeps the existing wire ABI.
pub(crate) struct CheckedPlan<'a> {
    tree: &'a [u64],
}

impl<'a> CheckedPlan<'a> {
    pub(crate) fn new(plan: &'a [u64], elem: &Shape) -> Result<Self, &'static str> {
        fn node(plan: &[u64], part: Part<'_>) -> Result<usize, &'static str> {
            let header = plan.get(..HEADER).ok_or("ordered iteration plan too short")?;
            let span = usize::try_from(header[SPAN]).map_err(|_| "ordered iteration plan length overflow")?;
            let plan = plan.get(..span).filter(|_| span >= HEADER).ok_or("ordered iteration plan length mismatch")?;
            let (opcode, expected_width, children) = match part {
                Part::PackedWord => (WORDS, 1usize, Vec::new()),
                Part::Shape(shape) => {
                    let (op, ch) = node_parts(shape).ok_or("ordered iteration shape has no ordering plan")?;
                    (op, layout::words(shape), ch)
                }
            };
            if header[OPCODE] != opcode {
                return Err("ordered iteration plan opcode mismatch");
            }
            if header[WIDTH] != expected_width as u64 {
                return Err("ordered iteration plan width mismatch");
            }
            if header[CHILDREN] != children.len() as u64 {
                return Err("ordered iteration plan child count mismatch");
            }
            let (mut offset, mut sum, mut max) = (HEADER, 0u64, 0u64);
            for child in children {
                let rest = plan.get(offset..).ok_or("ordered iteration child span out of range")?;
                let size = node(rest, child)?;
                // The recursive check established a complete child header and
                // a span contained in this parent, before any trusted access.
                sum = sum.checked_add(rest[WIDTH]).ok_or("ordered iteration child width overflow")?;
                max = max.max(rest[WIDTH]);
                offset = offset.checked_add(size).ok_or("ordered iteration child span overflow")?;
            }
            if offset != span {
                return Err("ordered iteration plan child spans do not fill node");
            }
            let width = match opcode {
                WORDS => header[WIDTH],
                SET => 1,
                PRODUCT => sum,
                UNION => max.checked_add(1).ok_or("ordered iteration union width overflow")?,
                _ => unreachable!("node_parts returned an unknown opcode"),
            };
            if header[WIDTH] != width {
                return Err("ordered iteration plan child width mismatch");
            }
            Ok(span)
        }
        let root = node(plan, Part::Shape(elem))?;
        let keys = &plan[root..];
        let ranks = layout::bitset_universe(elem).unwrap_or(0);
        if keys.len() as u64 != ranks {
            return Err("ordered iteration rank key count mismatch");
        }
        let mut seen = vec![false; keys.len()];
        for &key in keys {
            if key >= ranks {
                return Err("ordered iteration rank key out of range");
            }
            // key < ranks == keys.len(), so the index fits usize.
            if std::mem::replace(&mut seen[key as usize], true) {
                return Err("ordered iteration rank keys are not a permutation");
            }
        }
        Ok(Self { tree: &plan[..root] })
    }

    pub(crate) fn width(&self) -> usize {
        // Validation equated this word to layout::words(elem), a usize.
        self.tree[WIDTH] as usize
    }
}

pub(crate) fn compare(p: &[u64], a: &[u64], b: &[u64]) -> Ordering {
    match p[OPCODE] {
        WORDS => a[..p[WIDTH] as usize].cmp(&b[..p[WIDTH] as usize]),
        SET => {
            // SetEnumValue.compareTo compares cardinality, then the sorted
            // elements. At equal cardinality the least differing bit tells
            // which set has the smaller next element (numeric bitset order
            // does not: {1,4} sorts before {2,3}).
            let c = a[0].count_ones().cmp(&b[0].count_ones());
            if c != Ordering::Equal || a[0] == b[0] {
                return c;
            }
            let bit = 1u64 << (a[0] ^ b[0]).trailing_zeros();
            if a[0] & bit != 0 {
                Ordering::Less
            } else {
                Ordering::Greater
            }
        }
        PRODUCT => {
            let (mut child, mut off) = (HEADER, 0);
            for _ in 0..p[CHILDREN] {
                let c = compare(&p[child..], &a[off..], &b[off..]);
                if c != Ordering::Equal {
                    return c;
                }
                off += p[child + WIDTH] as usize;
                child += p[child + SPAN] as usize;
            }
            Ordering::Equal
        }
        UNION => {
            let c = a[0].cmp(&b[0]);
            if c != Ordering::Equal {
                return c;
            }
            let mut child = HEADER;
            for _ in 0..a[0] {
                child += p[child + SPAN] as usize;
            }
            compare(&p[child..], &a[1..], &b[1..])
        }
        _ => unreachable!("invalid encoded order plan"),
    }
}

/// Sort element indices, retaining the canonical encoding of the original set.
pub(crate) fn indices(p: &[u64], set: &[u64], out: &mut [u64]) {
    // SAFETY: MaybeUninit<u64> has the same layout as u64. The exclusive
    // borrow is retained, and indices_uninit only writes initialized words,
    // so this slice remains initialized even if an input causes a panic.
    let out = unsafe { std::slice::from_raw_parts_mut(out.as_mut_ptr().cast(), out.len()) };
    indices_uninit(p, set, out);
}

/// Initialize the cardinality-sized output prefix without clearing its storage.
pub(crate) fn indices_uninit(p: &[u64], set: &[u64], out: &mut [std::mem::MaybeUninit<u64>]) {
    let k = p[WIDTH] as usize;
    for i in 0..set[0] as usize {
        let mut j = i;
        let x = &set[1 + i * k..];
        while j > 0 {
            // SAFETY: iterations 0..i initialized that prefix; shifts only
            // copy initialized words, and 0 <= j - 1 < i throughout this loop.
            let prev = unsafe { out[j - 1].assume_init() };
            if !compare(p, x, &set[1 + prev as usize * k..]).is_lt() {
                break;
            }
            out[j].write(prev);
            j -= 1;
        }
        out[j].write(i as u64);
    }
}

/// Append rank -> TLC-order keys for a finite bitset universe. Only the
/// present ranks are sorted during a call; no scan of the whole universe.
pub(crate) fn with_rank_keys(p: Arc<[u64]>, elem: &Shape, n: u64) -> Arc<[u64]> {
    let k = layout::words(elem);
    let mut ws = vec![0; n as usize * k];
    for i in 0..n as usize {
        layout::encode(elem, &layout::unrank(elem, i as u64), &mut ws[i * k..(i + 1) * k]).expect("unrank fits");
    }
    let mut ranks: Vec<usize> = (0..n as usize).collect();
    ranks.sort_unstable_by(|a, b| compare(&p, &ws[a * k..], &ws[b * k..]));
    let mut out = p.to_vec();
    let off = out.len();
    out.resize(off + n as usize, 0);
    for (key, rank) in ranks.into_iter().enumerate() {
        out[off + rank] = key as u64;
    }
    out.into()
}

pub(crate) fn bit_indices(keys: &[u64], set: &[u64], out: &mut [u64]) -> usize {
    // SAFETY: equal layouts and the original exclusive borrow are retained;
    // bit_indices_uninit writes initialized words only, including on panic.
    let out = unsafe { std::slice::from_raw_parts_mut(out.as_mut_ptr().cast(), out.len()) };
    bit_indices_uninit(keys, set, out)
}

/// Initialize and return only the present-rank prefix of the output storage.
pub(crate) fn bit_indices_uninit(keys: &[u64], set: &[u64], out: &mut [std::mem::MaybeUninit<u64>]) -> usize {
    let mut n = 0;
    for (i, word) in set.iter().enumerate() {
        let mut b = *word;
        while b != 0 {
            let r = i * 64 + b.trailing_zeros() as usize;
            b &= b - 1;
            let mut j = n;
            while j > 0 {
                // SAFETY: previous ranks initialized 0..n. Shifts preserve
                // initialization, and j - 1 is strictly within that prefix.
                let prev = unsafe { out[j - 1].assume_init() };
                if keys[r] >= keys[prev as usize] {
                    break;
                }
                out[j].write(prev);
                j -= 1;
            }
            out[j].write(r as u64);
            n += 1;
        }
    }
    n
}

#[cfg(test)]
mod tests {
    use super::*;
    use tlx_value::intern::Sym;

    #[test]
    fn encoded_records_and_nullable_sets_follow_tlc() {
        let set = Shape::Set { elem: Box::new(Shape::Int { lo: 1, hi: 4 }), max_card: 4 };
        let nullable = Shape::Union(Arc::from(vec![Shape::Atom(Arc::from(vec![Value::model_value("NULL")])), set.clone()]));
        let shape = Shape::Record(Arc::from(vec![(Sym::new("members"), set), (Sym::new("newMembers"), nullable)]));
        let p = plan(&shape).unwrap();
        assert!(!order_safe(&shape));
        let n = layout::words(&shape);
        let mut samples = vec![];
        for r in 0..shape.cardinality().unwrap() {
            let v = layout::unrank(&shape, r);
            let mut w = vec![0; n];
            layout::encode(&shape, &v, &mut w).unwrap();
            samples.push((v, w));
        }
        for (a, aw) in &samples {
            for (b, bw) in &samples {
                assert_eq!(compare(&p, aw, bw), tlx_value::order::cmp_tlc(a, b).unwrap(), "{a} vs {b}");
            }
        }
    }

    /// The plan of every shape that holds a sequence must order like the
    /// interpreter: `compare` over all encoded pairs, sequences of every
    /// length included.
    fn assert_plan_matches_tlc(shape: &Shape) {
        let p = plan(shape).expect("plan");
        let n = layout::words(shape);
        let mut samples = vec![];
        for r in 0..shape.cardinality().expect("cardinality") {
            let v = layout::unrank(shape, r);
            let mut w = vec![0; n];
            layout::encode(shape, &v, &mut w).unwrap();
            samples.push((v, w));
        }
        for (a, aw) in &samples {
            for (b, bw) in &samples {
                assert_eq!(compare(&p, aw, bw), tlx_value::order::cmp_tlc(a, b).unwrap(), "{a} vs {b}");
            }
        }
    }

    #[test]
    fn sequences_of_every_length_follow_tlc_order() {
        let seq = Shape::Seq { elem: Box::new(Shape::Int { lo: 0, hi: 3 }), max_len: 2 };
        assert!(order_safe(&seq));
        assert_plan_matches_tlc(&seq);
        // Nested in a record, as CCF's `history` entries hold their
        // `observed` sequence.
        let rec =
            |name: &str| Shape::Record(Arc::from(vec![(Sym::new(name), Shape::Int { lo: 0, hi: 1 }), (Sym::new("observed"), seq.clone())]));
        assert_plan_matches_tlc(&rec("i"));
        // And in the arms of a union of records (`{history[i] : ...}`).
        let union = Shape::Union(Arc::from(vec![rec("i"), rec("j")]));
        assert!(order_safe(&union));
        assert_plan_matches_tlc(&union);
    }

    #[test]
    fn mixed_packed_scalars_and_sets_follow_tlc_order() {
        let set = Shape::Set { elem: Box::new(Shape::Int { lo: 1, hi: 3 }), max_card: 3 };
        let shape = Shape::Record(Arc::from(vec![
            (Sym::new("a"), Shape::Bool),
            (Sym::new("b"), Shape::Int { lo: 0, hi: 2 }),
            (Sym::new("s"), set),
            (Sym::new("c"), Shape::Bool),
        ]));
        assert!(!order_safe(&shape));
        assert_eq!(layout::words(&shape), 3);
        assert_plan_matches_tlc(&shape);
    }

    #[test]
    fn incomparable_union_and_wide_set_stay_boxed() {
        let union = Shape::Union(Arc::from(vec![Shape::Bool, Shape::Int { lo: 0, hi: 1 }]));
        assert!(plan(&union).is_none());
        let typed = Shape::Union(Arc::from(vec![Shape::Atom(Arc::from(vec![Value::model_value("m_NULL")])), Shape::Bool]));
        assert!(plan(&typed).is_none());
        assert!(plan(&Shape::Set { elem: Box::new(Shape::Int { lo: 0, hi: 64 }), max_card: 65 }).is_none());
    }
}
