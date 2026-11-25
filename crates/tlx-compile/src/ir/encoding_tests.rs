use super::*;

#[test]
fn mixed_radix_order_and_empty_products() {
    assert_eq!(rank(&[], &[]), 0);
    for first in 0..2 {
        for second in 0..3 {
            for third in 0..5 {
                assert_eq!(rank(&[2, 3, 5], &[first, second, third]), first * 15 + second * 5 + third);
                assert_eq!(rank_with(&[2, 3, 5], |index| [first, second, third][index]), first * 15 + second * 5 + third);
            }
        }
    }
    assert_eq!(rank(&[2, 3], &[1, 2, 999]), 5);
    assert_eq!(rank(&[2, 3], &[1]), 1);
    assert_eq!(rank_with(&[], |_| panic!("empty rank read a digit")), 0);
}

#[test]
#[cfg(debug_assertions)]
#[should_panic(expected = "attempt to multiply with overflow")]
fn rank_multiplication_precedes_indexed_word_access() {
    rank_with(&[2, 2], |index| match index {
        0 => u64::MAX,
        _ => panic!("digit evaluated before multiplication"),
    });
}

#[test]
fn union_offsets_include_empty_and_zero_cardinality_arms() {
    let arms: Vec<Arc<[u64]>> = vec![Arc::from([]), Arc::from([2, 3]), Arc::from([0]), Arc::from([4])];
    let bases: Vec<u64> = UnionArms::new(&arms).map(|(base, _)| base).collect();
    assert_eq!(bases, [0, 1, 7, 7]);
    for (tag, base) in bases.into_iter().enumerate() {
        assert_eq!(UnionArms::new(&arms[..tag]).total(), base);
    }
    assert_eq!(UnionArms::new(&arms).total(), 11);
    assert_eq!(UnionArms::new(&[]).total(), 0);
}

#[test]
fn recode_checks_tags_ranges_and_missing_entries() {
    let words = [3, 4, u64::MAX, 0, 5, 6];
    let scalar = RecodeTable { arm_base: &[], table: &words, words: 2 };
    assert_eq!(scalar.codes(), 3);
    assert_eq!(
        scalar.lookup(|index| {
            assert_eq!(index, 0);
            0
        }),
        Some(&words[..2])
    );
    assert_eq!(scalar.lookup(|_| 1), None);
    assert_eq!(scalar.lookup(|_| 2), Some(&words[4..]));
    assert_eq!(scalar.lookup(|_| 3), None);
    assert_eq!(scalar.lookup(|_| u64::MAX), None);
    let union = RecodeTable { arm_base: &[0, 2], ..scalar };
    assert_eq!(union.lookup(|index| [1, 0][index]), Some(&words[4..]));
    assert_eq!(
        union.lookup(|index| {
            assert_eq!(index, 0);
            2
        }),
        None
    );
    let wrapping = RecodeTable { arm_base: &[u64::MAX], ..scalar };
    assert_eq!(wrapping.lookup(|index| [0, 1][index]), Some(&words[..2]));
    let partial = RecodeTable { table: &[0, 1, 2], ..scalar };
    assert_eq!(partial.lookup(|_| 1), None);
    let empty = RecodeTable { table: &[], ..scalar };
    assert_eq!(empty.lookup(|_| 0), None);
}

#[test]
fn union_loc_descriptor_encodes_missing_word_and_packed_fields() {
    use tlx_layout::pack::{BitPos, FieldLoc};

    assert_eq!(union_loc_desc(None), Some(UNION_DESC_MISSING));
    // Whole word at arm offset 0 sits at union payload word 1, shift 0, trim 0.
    assert_eq!(union_loc_desc(Some(FieldLoc::Words(0))), Some(1 << UNION_DESC_WORD_SHIFT));
    // Packed bitfield at word 0 and shift 0 (e.g. 5 low bits): non-negative, word 1, shift 0, trim 59.
    let zero_shift = union_loc_desc(Some(FieldLoc::Bits(BitPos::new(0, 0, 5)))).unwrap();
    assert_eq!(zero_shift, (1 << UNION_DESC_WORD_SHIFT) | (64 - 5));
    assert!(zero_shift >= 0);
    // Packed bitfield at non-zero word and shift: word 3, shift 60, trim 60 (4 bits).
    let packed = union_loc_desc(Some(FieldLoc::Bits(BitPos::new(2, 60, 4)))).unwrap();
    assert_eq!(packed, (3 << UNION_DESC_WORD_SHIFT) | (60 << UNION_DESC_BIT_SHIFT) | (64 - 4));
    // Decoding mirrors the C and JIT extraction formulas.
    let decode = |u: &[u64], d: i64| -> u64 {
        let w = u[(d as u64 >> UNION_DESC_WORD_SHIFT) as usize];
        let sh = ((d >> UNION_DESC_BIT_SHIFT) & UNION_DESC_FIELD_MASK) as u32;
        let trim = (d & UNION_DESC_FIELD_MASK) as u32;
        (w >> sh) & (u64::MAX >> trim)
    };
    assert_eq!(decode(&[0, 0xdead_beef_cafe_babe], union_loc_desc(Some(FieldLoc::Words(0))).unwrap()), 0xdead_beef_cafe_babe);
    assert_eq!(decode(&[0, 0xffff_ffff_ffff_ff15], zero_shift), 0x15);
    assert_eq!(decode(&[0, 0, 0, 0x9000_0000_0000_0000], packed), 0x9);
    // Out-of-range word offset is rejected rather than silently wrapped.
    let too_wide = (i64::MAX >> UNION_DESC_WORD_SHIFT) as usize;
    assert_eq!(union_loc_desc(Some(FieldLoc::Words(too_wide))), None);
    assert_eq!(union_loc_desc(Some(FieldLoc::Bits(BitPos::new(too_wide, 0, 1)))), None);
}
