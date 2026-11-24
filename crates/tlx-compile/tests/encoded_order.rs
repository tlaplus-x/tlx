//! Fixed wire fixtures executed independently by Rust and generated C.

// Exercise private runtime helpers without adding a public testing ABI.
#[allow(clippy::module_inception, reason = "test module wraps private src/encoded_order.rs")]
#[path = "../src/encoded_order.rs"]
mod encoded_order;

use std::fmt::Write;
use std::process::Command;

use tlx_layout::{layout, Shape};
use tlx_testkit::TempDir;
use tlx_value::{Sym, Value};

struct Vector {
    name: &'static str,
    shape: Shape,
    tree: Vec<u64>,
    values: Vec<Vec<u64>>,
    sorted: Vec<u64>,
    order: Vec<u64>,
}

fn vectors() -> Vec<Vector> {
    let scalar = Shape::Int { lo: 0, hi: 10000 };
    let set = Shape::Set { elem: Box::new(Shape::Int { lo: 1, hi: 4 }), max_card: 4 };
    vec![
        Vector {
            name: "empty",
            shape: Shape::Tuple(vec![].into()),
            tree: vec![0, 0, 4, 0],
            values: vec![vec![999], vec![0]],
            sorted: vec![0, 1],
            order: vec![0, 0],
        },
        Vector {
            name: "scalar with trailing storage",
            shape: scalar.clone(),
            tree: vec![0, 1, 4, 0],
            values: vec![vec![2, 999], vec![0, 8], vec![2, 0], vec![1, 3]],
            sorted: vec![1, 3, 0, 2],
            order: vec![2, 0, 2, 1],
        },
        Vector {
            name: "set cardinality then elements",
            shape: set.clone(),
            tree: vec![1, 1, 4, 0],
            values: vec![vec![6], vec![0], vec![9], vec![1], vec![15], vec![3]],
            sorted: vec![1, 3, 5, 2, 0, 4],
            order: vec![4, 0, 3, 1, 5, 2],
        },
        Vector {
            name: "product child widths and spans",
            shape: Shape::Tuple(vec![set.clone(), scalar].into()),
            tree: vec![2, 2, 12, 2, 1, 1, 4, 0, 0, 1, 4, 0],
            values: vec![vec![6, 0], vec![9, 9], vec![9, 1], vec![0, 999]],
            sorted: vec![3, 2, 1, 0],
            order: vec![3, 2, 1, 0],
        },
        Vector {
            name: "nullable set union",
            shape: Shape::Union(vec![Shape::Atom(vec![Value::model_value("NULL")].into()), set.clone()].into()),
            tree: vec![3, 2, 12, 2, 0, 1, 4, 0, 1, 1, 4, 0],
            values: vec![vec![1, 6], vec![0, 0], vec![1, 9], vec![1, 0]],
            sorted: vec![1, 3, 2, 0],
            order: vec![3, 0, 2, 1],
        },
        Vector {
            name: "union with empty padded arm",
            shape: Shape::Union(vec![Shape::Tuple(vec![].into()), Shape::Tuple(vec![set].into())].into()),
            tree: vec![3, 2, 16, 2, 0, 0, 4, 0, 2, 1, 8, 1, 1, 1, 4, 0],
            values: vec![vec![0, 999], vec![1, 9], vec![0, 0], vec![1, 6]],
            sorted: vec![0, 2, 1, 3],
            order: vec![0, 1, 0, 2],
        },
    ]
}

fn array(c: &mut String, name: &str, words: &[u64]) {
    // C needs one addressable word even for a zero-width element or empty set.
    write!(c, "uint64_t {name}[] = {{").unwrap();
    for word in words {
        write!(c, "{word}ULL,").unwrap();
    }
    c.push_str("0};\n");
}

fn run_c(c: &str) {
    let dir = TempDir::new("ordered-vectors");
    let source = dir.write("vectors.c", c);
    let binary = dir.path().join("vectors");
    let result = Command::new("cc").args(["-std=c11", "-O2"]).arg(source).arg("-o").arg(&binary).output().unwrap();
    assert!(result.status.success(), "{}", String::from_utf8_lossy(&result.stderr));
    let result = Command::new(binary).output().unwrap();
    assert!(result.status.success(), "C vectors failed: {:?}\n{}", result.status, String::from_utf8_lossy(&result.stderr));
}

#[test]
fn common_comparison_and_index_vectors() {
    let mut c = format!(
        "#include <stdint.h>\n#include <string.h>\n#include <assert.h>\n{}\nint main(void) {{\n",
        include_str!("../src/cgen/runtime.h")
    );
    let mut comparisons = 0;
    for v in vectors() {
        let tree = encoded_order::plan(&v.shape).unwrap();
        // These numeric fixtures predate the schema refactor: do not derive
        // their words or expected order from the implementation under test.
        assert_eq!(&*tree, v.tree, "{} wire words", v.name);
        let bytes: Vec<u8> = tree.iter().flat_map(|w| w.to_le_bytes()).collect();
        let fixture: Vec<u8> = v.tree.iter().flat_map(|w| w.to_le_bytes()).collect();
        assert_eq!(bytes, fixture, "{} serialized plan bytes", v.name);
        let plan = match layout::bitset_universe(&v.shape) {
            Some(n) => encoded_order::with_rank_keys(tree, &v.shape, n),
            None => tree,
        };
        let width = encoded_order::CheckedPlan::new(&plan, &v.shape).unwrap().width();
        c.push_str("{\n");
        array(&mut c, "p", &plan);
        for (i, a) in v.values.iter().enumerate() {
            for (j, b) in v.values.iter().enumerate() {
                let expected = v.order[i].cmp(&v.order[j]);
                assert_eq!(encoded_order::compare(&plan, a, b), expected, "{}: {i} vs {j}", v.name);
                c.push_str("{\n");
                array(&mut c, "a", a);
                array(&mut c, "b", b);
                writeln!(c, "assert(tlx_order_compare(p, a, b) == {}); }}", expected as i8).unwrap();
                comparisons += 1;
            }
        }
        let mut set = vec![v.values.len() as u64];
        for value in &v.values {
            set.extend_from_slice(&value[..width]);
        }
        let mut out = vec![u64::MAX; v.values.len()];
        encoded_order::indices(&plan, &set, &mut out);
        assert_eq!(out, v.sorted, "{} sorted indices", v.name);
        array(&mut c, "s", &set);
        array(&mut c, "out", &vec![u64::MAX; out.len()]);
        writeln!(c, "tlx_order_indices(p, s, out);").unwrap();
        for (i, rank) in v.sorted.iter().enumerate() {
            writeln!(c, "assert(out[{i}] == {rank});").unwrap();
        }
        c.push_str("}\n");
    }
    c.push_str("return 0; }\n");
    run_c(&c);
    assert_eq!(comparisons, 104);
    eprintln!("ordered vectors: 104 pair comparisons and 6 stable index sorts per Rust/C backend");
}

#[test]
fn common_rank_key_vectors() {
    let elem = Shape::Set { elem: Box::new(Shape::Int { lo: 1, hi: 4 }), max_card: 4 };
    let plan = encoded_order::with_rank_keys(encoded_order::plan(&elem).unwrap(), &elem, 16);
    let expected = [1, 1, 4, 0, 0, 1, 2, 5, 3, 6, 8, 11, 4, 7, 9, 12, 10, 13, 14, 15];
    assert_eq!(&*plan, expected, "rank-key wire words");
    encoded_order::CheckedPlan::new(&plan, &elem).unwrap();
    let mut c = format!(
        "#include <stdint.h>\n#include <string.h>\n#include <assert.h>\n{}\nint main(void) {{\n",
        include_str!("../src/cgen/runtime.h")
    );
    // Rank keys are compared directly, including empty input and ranks on
    // both sides of a word boundary. The order is intentionally nonnumeric.
    let elem = Shape::Set { elem: Box::new(Shape::Int { lo: 1, hi: 7 }), max_card: 7 };
    let plan = encoded_order::with_rank_keys(encoded_order::plan(&elem).unwrap(), &elem, 128);
    encoded_order::CheckedPlan::new(&plan, &elem).unwrap();
    let keys = &plan[4..];
    for (rank, key) in [(0, 0), (1, 1), (3, 8), (63, 120), (64, 7), (65, 13), (127, 127)] {
        assert_eq!(keys[rank], key);
    }
    for (set, expected) in [([0, 0], vec![]), ([(1 << 63) | (1 << 3), 3], vec![64, 3, 65, 63])] {
        let mut out = vec![u64::MAX; 4];
        let n = encoded_order::bit_indices(keys, &set, &mut out);
        assert_eq!(&out[..n], expected);
        c.push_str("{\n");
        array(&mut c, "keys", keys);
        array(&mut c, "s", &set);
        array(&mut c, "out", &vec![u64::MAX; out.len()]);
        writeln!(c, "assert(tlx_order_bit_indices(keys, s, 2, out) == {});", expected.len()).unwrap();
        for (i, rank) in expected.iter().enumerate() {
            writeln!(c, "assert(out[{i}] == {rank});").unwrap();
        }
        c.push_str("}\n");
    }
    c.push_str("return 0; }\n");
    run_c(&c);
}

#[test]
fn heterogeneous_function_shapes_keep_the_boxed_comparison_policy() {
    // D-31 compares function domains before values. A word/tag comparison
    // cannot implement that for heterogeneous tuple/record/function arms.
    let record = Shape::Record(vec![(Sym::new("a"), Shape::Bool)].into());
    let tuple = Shape::Tuple(vec![Shape::Bool].into());
    let mixed = Shape::Union(vec![record, tuple].into());
    assert!(encoded_order::plan(&mixed).is_none());
    let a = Value::record(vec![(Sym::new("a"), Value::Bool(false))]);
    let b = Value::tuple(vec![Value::Bool(false)]);
    let ab = tlx_value::order::cmp_tlc(&a, &b).unwrap();
    assert_eq!(ab, tlx_value::order::cmp_tlc(&b, &a).unwrap().reverse());
}

/// A function of a fixed domain is a product of its range's slots in domain
/// order. TLC compares the domains before the values, but every value of one
/// shape carries that shape's domain, so the domain comparison is always
/// equal and the slot order decides — including for a range the plain word
/// comparison cannot order (a set, a nested record) and for the empty set.
#[test]
fn function_and_nested_record_orders_follow_tlc() {
    let mut dom = vec![Value::model_value("ord_a"), Value::model_value("ord_b")];
    dom.sort();
    let dom: std::sync::Arc<[Value]> = dom.into();
    let record = Shape::Record(
        vec![
            (Sym::new("fn"), Shape::Fcn { dom: dom.clone(), range: Box::new(Shape::Int { lo: 0, hi: 2 }) }),
            (Sym::new("set"), Shape::Set { elem: Box::new(Shape::Int { lo: 1, hi: 3 }), max_card: 3 }),
        ]
        .into(),
    );
    let nested = Shape::Record(
        vec![
            (Sym::new("inner"), record.clone()),
            (
                Sym::new("dom"),
                Shape::Fcn { dom: dom.clone(), range: Box::new(Shape::Set { elem: Box::new(Shape::Int { lo: 1, hi: 2 }), max_card: 2 }) },
            ),
        ]
        .into(),
    );
    for shape in [record.clone(), nested] {
        assert!(!encoded_order::order_safe(&shape), "the shape must exercise the plan, not the word order: {shape:?}");
        let p = encoded_order::plan(&shape).expect("a plan for a function/record/set product");
        let n = layout::words(&shape);
        let mut samples = vec![];
        for r in 0..shape.cardinality().unwrap() {
            let v = layout::unrank(&shape, r);
            let mut w = vec![0; n];
            layout::encode(&shape, &v, &mut w).unwrap();
            samples.push((v, w));
        }
        // Exhaustive in Rust, against the interpreter's own comparison.
        for (a, aw) in &samples {
            for (b, bw) in &samples {
                assert_eq!(encoded_order::compare(&p, aw, bw), tlx_value::order::cmp_tlc(a, b).unwrap(), "{a} vs {b}");
            }
        }
        // The empty set (the third slot of the set range is 0) is reached.
        assert!(samples.iter().any(|(v, _)| format!("{v}").contains("|-> {}")), "{shape:?}");
        // The same pairs through generated C and its static plan.
        let mut c = format!(
            "#include <stdint.h>\n#include <string.h>\n#include <assert.h>\n{}\nint main(void) {{\n",
            include_str!("../src/cgen/runtime.h")
        );
        array(&mut c, "p", &p);
        for (a, aw) in samples.iter().take(12) {
            for (b, bw) in samples.iter().take(12) {
                let expected = tlx_value::order::cmp_tlc(a, b).unwrap() as i8;
                c.push_str("{\n");
                array(&mut c, "a", aw);
                array(&mut c, "b", bw);
                writeln!(c, "assert(tlx_order_compare(p, a, b) == {expected}); }}").unwrap();
            }
        }
        c.push_str("return 0; }\n");
        run_c(&c);
    }
}
