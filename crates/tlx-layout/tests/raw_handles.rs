fn catch<T>(f: impl FnOnce() -> T) -> std::thread::Result<T> {
    std::panic::catch_unwind(std::panic::AssertUnwindSafe(f))
}

use tlx_layout::dynval;
use tlx_value::{Sym, Value};

#[test]
fn checked_store_handles_reject_noncanonical_booleans() {
    let s = tlx_layout::store::Store::new(usize::MAX);
    assert!(!s.is_valid(19));
    assert!(s.try_thaw(19).is_none());
}

#[test]
fn checked_store_raw_boundary() {
    use tlx_layout::store::{cmp_tlc, eq_tlc, RefOpError, Store};
    let s = Store::new(usize::MAX);
    let other = Store::new(usize::MAX);
    let foreign = other.freeze(&Value::tuple(vec![Value::Int(1)])).unwrap();
    let record = s.freeze(&Value::record(vec![(Sym::new("raw-field"), Value::Int(2))])).unwrap();
    let tuple = s.freeze(&Value::tuple(vec![Value::Int(1)])).unwrap();
    // Only checked APIs see these words. In particular, never pass them
    // to an unsafe decoder or construct an invalid Sym to test publication.
    for bad in [19, 0, 6, 7, 5, u64::MAX, (u32::MAX as u64) << 3 | 1, (u32::MAX as u64) << 3 | 2, (1u64 << 40) | 1, foreign] {
        assert!(!s.is_valid(bad));
        assert!(s.try_thaw(bad).is_none());
        assert!(catch(|| s.thaw(bad)).is_err());
        assert!(catch(|| s.digest(bad)).is_err());
        if bad != 0 {
            assert!(catch(|| s.thaw_slot(bad)).is_err());
        }
        assert_eq!(s.select(record, bad), Err(RefOpError::Eval));
        assert_eq!(s.single(bad, 4), Err(RefOpError::Eval));
        assert_eq!(s.tuple(&[bad]), Err(RefOpError::Eval));
        assert_eq!(s.record(&[(Sym::new("raw-field"), bad)]), Err(RefOpError::Eval));
        assert_eq!(s.set_at(tuple, 0, bad), Err(RefOpError::Eval));
        assert_eq!(s.append(tuple, bad), Err(RefOpError::Eval));
        assert_eq!(s.len(bad), Err(RefOpError::Eval));
        assert_eq!(s.member(bad, s.domain(tuple).unwrap()), Err(RefOpError::Eval));
        assert_eq!(eq_tlc(&s, bad, bad), Err(RefOpError::Eval));
        assert_eq!(cmp_tlc(&s, bad, bad), Err(RefOpError::Eval));
    }
    assert_eq!(s.thaw_slot(0), Value::Bool(false));
}

#[test]
fn checked_store_round_trip_and_publication() {
    let s = tlx_layout::store::Store::new(usize::MAX);
    for v in [
        Value::str("store-raw-string"),
        Value::ModelValue(Sym::new("store_raw_model")),
        Value::Bool(false),
        Value::Bool(true),
        Value::Int(i64::MIN),
        Value::Int(i64::MAX),
        Value::Int(-42),
        Value::tuple(vec![Value::str("store-child"), Value::Int(3)]),
        Value::record(vec![(Sym::new("store-field"), Value::Int(7))]),
        Value::fcn_rcd_from_pairs(vec![(Value::str("store-field"), Value::Int(7))]).unwrap(),
        Value::set_from(vec![Value::Int(1), Value::Int(2)]).unwrap(),
        Value::Interval(1, 3),
    ] {
        let h = s.freeze(&v).unwrap();
        assert!(s.is_valid(h));
        assert_eq!(s.try_thaw(h), Some(v.clone()));
        assert_eq!(s.thaw_slot(h), v);
        assert_eq!(s.digest(h), tlx_layout::store::digest_of_value(&v).unwrap());
        let s = s.clone();
        std::thread::spawn(move || assert_eq!(s.thaw(h), v)).join().unwrap();
    }
    let first = tlx_value::intern::len() as u32;
    std::thread::scope(|scope| {
        scope.spawn(|| {
            for i in 0..32 {
                Sym::new(&format!("store-publish-{i}"));
            }
        });
        for id in first..first + 32 {
            if let Some(Value::Str(sym)) = s.try_thaw((id as u64) << 3 | 1) {
                assert!(!sym.as_str().is_empty());
            }
        }
    });
}

#[test]
fn checked_raw_handles_reject_invalid_symbols_and_tags() {
    Sym::new("raw-handle-live");
    let invalid_id = u32::MAX as u64;
    for h in [0, (invalid_id << 3) | 1, (invalid_id << 3) | 2, u64::MAX, 5, 6, 7, 19] {
        assert!(dynval::try_lookup(h).is_none(), "accepted invalid handle {h}");
    }
}

#[test]
fn checked_raw_handles_round_trip() {
    for v in [
        Value::str("raw-handle-string"),
        Value::ModelValue(Sym::new("raw_handle_model")),
        Value::Bool(false),
        Value::Bool(true),
        Value::Int(i64::MIN),
        Value::Int(i64::MAX),
        Value::Int(-42),
        Value::tuple(vec![Value::Int(3)]),
    ] {
        assert_eq!(dynval::try_lookup(dynval::intern(&v)), Some(v));
    }
}

#[test]
fn checked_layouts_reject_nested_invalid_handles() {
    use tlx_layout::{FcnWitness, Layout, LayoutNode, Shape};
    let bad = (u32::MAX as u64) << 3 | 1;
    let cases = [
        (Shape::Dyn, vec![bad]),
        (Shape::Tuple(vec![Shape::Dyn].into()), vec![bad]),
        (Shape::Record(vec![(Sym::new("field"), Shape::Dyn)].into()), vec![bad]),
        (
            Shape::Fcn {
                dom: vec![Value::Bool(false)].into(),
                range: Box::new(Shape::Dyn),
                witness: FcnWitness::Enumerated,
                key_variants: std::sync::Arc::from([]),
            },
            vec![bad],
        ),
        (Shape::Seq { elem: Box::new(Shape::Dyn), max_len: 2 }, vec![1, bad, 0]),
        (Shape::Set { elem: Box::new(Shape::Dyn), max_card: 2 }, vec![1, bad, 0]),
        (Shape::Map { key: Box::new(Shape::Bool), range: Box::new(Shape::Dyn), witness: FcnWitness::Enumerated }, vec![1, bad, 0]),
        (Shape::Union(vec![Shape::Dyn].into()), vec![0, bad]),
    ];
    for (shape, words) in cases {
        let node = LayoutNode::new(&shape);
        assert!(node.validate_words(&words).is_err());
        assert!(catch(|| node.decode(&words)).is_err());
        assert!(catch(|| tlx_layout::layout::decode(&shape, &words)).is_err());
        let layout = Layout::new(vec![shape]);
        assert!(layout.validate_words(&words).is_err());
        assert!(catch(|| layout.decode_state(&words)).is_err());
    }
    // Inactive slots are padding, not handles (empty sequences and maps).
    let seq = LayoutNode::new(&Shape::Seq { elem: Box::new(Shape::Dyn), max_len: 1 });
    assert_eq!(seq.decode(&[0, bad]), Value::tuple(vec![]));
    let map = LayoutNode::new(&Shape::Map { key: Box::new(Shape::Bool), range: Box::new(Shape::Dyn), witness: FcnWitness::Enumerated });
    assert!(map.validate_words(&[0, bad, bad]).is_ok());
}

#[test]
fn checked_transcode_and_permutation_reject_invalid_handles() {
    use tlx_layout::{LayoutNode, Shape};
    let bad = (u32::MAX as u64) << 3 | 2;
    let node = LayoutNode::new(&Shape::Dyn);
    let integer = LayoutNode::new(&Shape::Int { lo: 0, hi: 3 });
    assert!(catch(|| {
        tlx_layout::layout_tree::transcode(&node, &integer, &[bad], &mut [0]);
    })
    .is_err());
    let perm: tlx_layout::permute::AtomPerm = std::sync::Arc::new(Clone::clone);
    let plan = tlx_layout::permute::PermPlan::compile(&Shape::Dyn, &perm).unwrap();
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| plan.apply(&[bad], &mut [0]))).is_err());
}

#[test]
fn checked_handles_publish_across_threads_and_restore() {
    let count = if cfg!(miri) { 4 } else { 32 };
    let first = tlx_value::intern::len() as u32;
    std::thread::scope(|scope| {
        scope.spawn(|| {
            for i in 0..count {
                Sym::new(&format!("raw-publish-{i}"));
            }
        });
        // These ids may be allocated but not yet published. Any symbol
        // returned by the checked constructor must already have valid text.
        for id in first..first + count {
            if let Some(s) = Sym::try_from_id(id) {
                assert!(!s.as_str().is_empty());
                assert_eq!(dynval::try_lookup((id as u64) << 3 | 1), Some(Value::Str(s)));
            }
        }
    });
    let v = Value::tuple(vec![Value::str("raw-restore")]);
    let h = dynval::intern(&v);
    let symbols = tlx_value::intern::snapshot();
    let values = dynval::snapshot();
    tlx_value::intern::restore(&symbols).unwrap();
    dynval::restore(&values).unwrap();
    std::thread::spawn(move || {
        assert_eq!(dynval::try_lookup(h), Some(v));
    })
    .join()
    .unwrap();
}

#[test]
fn scalar_schema_bits_range_and_encoding_are_pinned() {
    use tlx_layout::scalar;
    // The C and JIT backends emit these numbers as literals derived from
    // these constants (ARCH-07): pin the values, so any change to the
    // schema is loud instead of silently diverging from generated code.
    assert_eq!((scalar::TAG_BITS, scalar::TAG_MASK), (3, 7));
    assert_eq!((scalar::TAG_STR, scalar::TAG_MODEL_VALUE, scalar::TAG_BOOL, scalar::TAG_INT), (1, 2, 3, 4));
    assert_eq!(scalar::IMM_INT_BITS, 60);
    assert_eq!(scalar::IMM_INT, 1 << 60);
    for i in [-scalar::IMM_INT, -1, 0, 1, 42, scalar::IMM_INT - 1] {
        let h = scalar::int_handle(i).unwrap();
        assert_eq!(h, (i as u64) << scalar::TAG_BITS | scalar::TAG_INT);
        assert_eq!(scalar::tag(h), scalar::TAG_INT);
        // `payload` and `encode` are inverse on a handle, and the checked
        // decode sign-extends the 60 payload bits back to `i`.
        assert_eq!(scalar::encode(scalar::payload(h), scalar::tag(h)), h);
        assert_eq!(scalar::as_int(h), Some(i));
        assert_eq!(scalar::immediate(&Value::Int(i)), Some(h));
        assert!(scalar::is_immediate(h));
    }
    // The range is closed below and open above: exactly what the emitted
    // `i < -(1LL << 60) || i >= (1LL << 60)` check of FromInt accepts.
    for i in [scalar::IMM_INT, -scalar::IMM_INT - 1, i64::MIN, i64::MAX] {
        assert_eq!(scalar::int_handle(i), None);
        assert_eq!(scalar::immediate(&Value::Int(i)), None);
    }
    assert_eq!(scalar::bool_handle(false), 3);
    assert_eq!(scalar::bool_handle(true), 1 << scalar::TAG_BITS | scalar::TAG_BOOL);
    assert_eq!(scalar::as_bool(0 << scalar::TAG_BITS | scalar::TAG_BOOL), Some(false));
    assert_eq!(scalar::as_bool(2 << scalar::TAG_BITS | scalar::TAG_BOOL), None);
    let s = Sym::new("scalar-schema-string");
    assert_eq!(scalar::str_handle(s), (s.id() as u64) << scalar::TAG_BITS | scalar::TAG_STR);
    assert_eq!(scalar::immediate(&Value::Str(s)), Some(scalar::str_handle(s)));
    let mv_sym = Sym::new("scalar_schema_model");
    let mv = Value::ModelValue(mv_sym);
    assert_eq!(scalar::immediate(&mv), Some(scalar::encode(mv_sym.id() as u64, scalar::TAG_MODEL_VALUE)));
    // Table and node tags are not scalar tags: the checked decode refuses
    // them, and the composite formats stay with their tables.
    for t in [0u64, 5, 6, 7] {
        assert!(!scalar::is_scalar_tag(t));
        assert!(!scalar::is_immediate(t));
        assert_eq!(scalar::scalar_value(t, |_| None), None);
    }
}

#[test]
fn scalar_handles_agree_across_the_two_tables() {
    use tlx_layout::scalar;
    let s = tlx_layout::store::Store::new(usize::MAX);
    for v in [
        Value::str("scalar-agree-string"),
        Value::ModelValue(Sym::new("scalar_agree_model")),
        Value::Bool(false),
        Value::Bool(true),
        Value::Int(-42),
        Value::Int(0),
        Value::Int(scalar::IMM_INT - 1),
        Value::Int(-scalar::IMM_INT),
    ] {
        // One owner of the schema: the `Dyn` interner, the store's freeze
        // path and the store's checked boundary all agree bit for bit.
        let h = dynval::intern(&v);
        assert_eq!(scalar::immediate(&v), Some(h));
        assert_eq!(tlx_layout::store::immediate(&v), Some(h));
        assert_eq!(s.freeze(&v).unwrap(), h);
        assert!(scalar::is_immediate(h));
        assert_eq!(dynval::try_lookup(h), Some(v.clone()));
        assert_eq!(s.try_thaw(h), Some(v.clone()));
    }
    // Integers outside the immediate range and composite values go to a
    // table, with a tag the scalar schema does not own: a `Dyn` table
    // handle is not a store handle.
    for v in [Value::Int(scalar::IMM_INT), Value::Int(-scalar::IMM_INT - 1), Value::Int(i64::MAX), Value::tuple(vec![Value::Int(1)])] {
        assert!(!scalar::is_immediate(dynval::intern(&v)));
        assert!(!scalar::is_immediate(s.freeze(&v).unwrap()));
    }
}
