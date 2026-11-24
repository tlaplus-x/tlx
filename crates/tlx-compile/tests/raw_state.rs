//! Safe codec boundaries must not manufacture process-local symbol handles.
use std::sync::Arc;
use tlx_compile::enc::EncModel;
use tlx_compile::settings::Settings;
use tlx_layout::{Layout, Shape};
#[cfg(debug_assertions)]
use tlx_runtime::Model;
use tlx_runtime::StateCodec;
use tlx_value::Value;

fn model(shape: Shape) -> EncModel {
    let base = tlx_testkit::spec::load(
        "---- MODULE RawState ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == UNCHANGED x\n====\n",
        "INIT Init\nNEXT Next\n",
    );
    let settings = Settings::from_lookup(|k| (k == "TLX_NO_NATIVE").then(|| "1".to_string())).unwrap();
    EncModel::new(Arc::new(base), Arc::new(Layout::new(vec![shape])), vec![], &settings)
}

#[test]
fn safe_state_codec_rejects_forged_dyn_words() {
    let m = model(Shape::Dyn);
    let bad = ((u32::MAX as u64) << 3) | 1;
    assert!(m.validate(&[bad]).is_err());
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| StateCodec::decode(&m, &[bad], 1, 0))).is_err());
    let good = tlx_layout::dynval::intern(&Value::str("raw-state"));
    let s = StateCodec::decode(&m, &[good], 1, 0);
    assert_eq!(&*m.values(&s), &[Value::str("raw-state")]);
    assert_eq!(s.words(), &[good]);
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| StateCodec::decode_into(&m, &[bad], 1, 0, s))).is_err());
}

#[cfg(debug_assertions)]
#[test]
fn debug_rejects_states_from_another_model() {
    let a = model(Shape::Int { lo: 0, hi: i64::MAX });
    let b = model(Shape::Dyn);
    let s = StateCodec::decode(&a, &[((u32::MAX as u64) << 3) | 1], 1, 0);
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| b.render(&s))).is_err());
}

#[test]
fn safe_state_codec_rejects_corrupted_packed_scalars_and_padding() {
    use tlx_layout::pack::{FieldLayout, FieldLoc, SlotLayout};
    use tlx_value::Sym;

    let atoms = Shape::Atom(Arc::from(vec![Value::str("a"), Value::str("b"), Value::str("c")]));
    let rec_shape =
        Shape::Record(Arc::from(vec![(Sym::new("a"), atoms), (Sym::new("b"), Shape::Bool), (Sym::new("n"), Shape::Int { lo: -1, hi: 1 })]));
    let m = model(rec_shape.clone());
    let fl = FieldLayout::of_shape(&rec_shape).unwrap();
    assert_eq!(fl.words, 1);

    let mut good = [0u64; 1];
    tlx_layout::layout::encode(
        &rec_shape,
        &Value::record(vec![(Sym::new("a"), Value::str("c")), (Sym::new("b"), Value::TRUE), (Sym::new("n"), Value::Int(0))]),
        &mut good,
    )
    .unwrap();
    assert!(m.validate(&good).is_ok());
    let decoded = StateCodec::decode(&m, &good, 1, 0);
    assert_eq!(decoded.words(), &good);

    // 1. Non-zero unused tail padding bit in packed record word.
    let bad_pad = [good[0] | 1];
    assert!(m.validate(&bad_pad).is_err());
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| StateCodec::decode(&m, &bad_pad, 1, 0))).is_err());

    // 2. Out-of-range 2-bit Atom code (3 >= 3) and 2-bit Int code (3 > 2).
    for idx in [0usize, 2usize] {
        let FieldLoc::Bits(pos) = fl.locs[idx] else { panic!("expected packed field") };
        let mut bad = good;
        pos.insert(&mut bad, 3);
        assert!(m.validate(&bad).is_err());
        assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| StateCodec::decode(&m, &bad, 1, 0))).is_err());
    }

    // 3. Packed Map with non-zero bits in an absent slot.
    let map_shape = Shape::Map {
        key: Box::new(Shape::Int { lo: 1, hi: 4 }),
        range: Box::new(Shape::Int { lo: 0, hi: 2 }),
        witness: tlx_layout::FcnWitness::Interval,
    };
    let map_m = model(map_shape.clone());
    let mut map_good = [0u64; 2];
    tlx_layout::layout::encode(&map_shape, &Value::fcn_from_pairs(vec![(Value::Int(1), Value::Int(2))]).unwrap(), &mut map_good).unwrap();
    assert!(map_m.validate(&map_good).is_ok());
    let mut map_bad = map_good;
    SlotLayout::insert(2, &mut map_bad[1..], 2, 1);
    assert!(map_m.validate(&map_bad).is_err());
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| StateCodec::decode(&map_m, &map_bad, 1, 0))).is_err());

    // 4. Packed Seq with non-zero bits in an inactive slot past `len`.
    let seq_shape = Shape::Seq { elem: Box::new(Shape::Int { lo: 0, hi: 2 }), max_len: 4 };
    let seq_m = model(seq_shape.clone());
    let mut seq_good = [0u64; 2];
    tlx_layout::layout::encode(&seq_shape, &Value::tuple(vec![Value::Int(1)]), &mut seq_good).unwrap();
    assert!(seq_m.validate(&seq_good).is_ok());
    let mut seq_bad = seq_good;
    SlotLayout::insert(2, &mut seq_bad[1..], 1, 2);
    assert!(seq_m.validate(&seq_bad).is_err());
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| StateCodec::decode(&seq_m, &seq_bad, 1, 0))).is_err());

    // 5. Word-aligned packed composite elements (tuple of two Bools = 1 word):
    //    inactive sequence suffix and absent map slots must be zero at the checkpoint boundary.
    let pair_bool = Shape::Tuple(Arc::from(vec![Shape::Bool, Shape::Bool]));
    let pair_seq = model(Shape::Seq { elem: Box::new(pair_bool.clone()), max_len: 1 });
    assert!(pair_seq.validate(&[0, 0]).is_ok());
    assert!(pair_seq.validate(&[0, 1]).is_err());
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| StateCodec::decode(&pair_seq, &[0, 1], 1, 0))).is_err());

    let pair_map =
        model(Shape::Map { key: Box::new(Shape::Bool), range: Box::new(pair_bool), witness: tlx_layout::FcnWitness::Enumerated });
    assert!(pair_map.validate(&[0, 0, 0]).is_ok());
    assert!(pair_map.validate(&[0, 1, 0]).is_err());
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| StateCodec::decode(&pair_map, &[0, 1, 0], 1, 0))).is_err());
}
