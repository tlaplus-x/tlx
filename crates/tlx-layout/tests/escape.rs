//! Stable slots retain their original encoding when a different value escapes.
use std::sync::Arc;
use tlx_layout::{escape::EscapeLayout, Layout, Shape};
use tlx_value::Value;

#[test]
fn escaped_and_inline_forms_have_the_same_canonical_key() {
    let layout = EscapeLayout::new(Arc::new(Layout::new(vec![Shape::Int { lo: 0, hi: 3 }])));
    let vals = [Value::Int(2)];
    let inline = layout.encode(&vals).unwrap();
    let escaped = layout.force_escape(&vals).unwrap();
    assert_ne!(inline, escaped);
    assert_eq!(layout.decode(&inline), vals);
    assert_eq!(layout.decode(&escaped), vals);
    assert_eq!(layout.key(&inline), layout.key(&escaped));
}

#[test]
fn outliers_never_change_old_slots_and_returning_values_reuse_their_key() {
    let layout = EscapeLayout::new(Arc::new(Layout::new(vec![Shape::Int { lo: 0, hi: 3 }, Shape::Bool])));
    let old = layout.encode(&[Value::Int(1), Value::Bool(true)]).unwrap();
    for n in [4, 100, i64::MAX] {
        let vals = [Value::Int(n), Value::Bool(false)];
        let escaped = layout.encode(&vals).unwrap();
        assert!(layout.is_escaped(&escaped));
        assert_eq!(layout.decode(&escaped), vals);
        assert_eq!(layout.key(&escaped), layout.key(&layout.force_escape(&vals).unwrap()));
        assert_eq!(layout.decode(&old), [Value::Int(1), Value::Bool(true)]);
    }
    assert_eq!(old, layout.encode(&[Value::Int(1), Value::Bool(true)]).unwrap());
    let mut queued = vec![0; layout.words()];
    layout.queue_words(&old, &mut queued);
    assert_eq!(layout.compact(&queued), old);
}

#[test]
fn invalid_escape_handles_are_rejected_before_decoding() {
    let layout = EscapeLayout::new(Arc::new(Layout::new(vec![Shape::Bool])));
    let mut bad = vec![0; layout.words()];
    bad[1] = u64::MAX;
    assert!(layout.validate(&bad).is_err());
}

#[test]
fn equal_functions_with_different_witnesses_share_escape_key() {
    use tlx_layout::FcnWitness;
    use tlx_value::{FcnDom, Sym};

    // Tuple slot: `<<1>>` fits inline while `[i \in {1} |-> 1]` escapes to
    // preserve its enumerated witness, yet both must share one visited key.
    let tuple_layout = EscapeLayout::new(Arc::new(Layout::new(vec![Shape::Tuple(Arc::from([Shape::Int { lo: 1, hi: 1 }]))])));
    let tuple = Value::tuple(vec![Value::Int(1)]);
    let enum_one = Value::fcn_with_dom(vec![(Value::Int(1), Value::Int(1))], FcnDom::Enumerated);
    let w_tuple = tuple_layout.encode(std::slice::from_ref(&tuple)).unwrap();
    let w_enum = tuple_layout.encode(std::slice::from_ref(&enum_one)).unwrap();
    assert!(!tuple_layout.is_escaped(&w_tuple));
    assert!(tuple_layout.is_escaped(&w_enum));
    assert_eq!(tuple_layout.decode(&w_tuple), vec![tuple]);
    assert_eq!(tuple_layout.decode(&w_enum), vec![enum_one]);
    assert_eq!(tuple_layout.key(&w_tuple), tuple_layout.key(&w_enum));

    // Record slot: `[a |-> 1]` vs `[k \in {"a"} |-> 1]`.
    let sym_a = Sym::new("a");
    let rec_layout = EscapeLayout::new(Arc::new(Layout::new(vec![Shape::Record(Arc::from([(sym_a, Shape::Int { lo: 1, hi: 1 })]))])));
    let rec = Value::record(vec![(sym_a, Value::Int(1))]);
    let enum_rec = Value::fcn_with_dom(vec![(Value::Str(sym_a), Value::Int(1))], FcnDom::Enumerated);
    let w_rec = rec_layout.encode(std::slice::from_ref(&rec)).unwrap();
    let w_erec = rec_layout.encode(std::slice::from_ref(&enum_rec)).unwrap();
    assert!(!rec_layout.is_escaped(&w_rec));
    assert!(rec_layout.is_escaped(&w_erec));
    assert_eq!(rec_layout.key(&w_rec), rec_layout.key(&w_erec));

    // Fixed-domain interval function slot: `[k \in 0..1 |-> k]` vs `[k \in {0, 1} |-> k]`.
    let fcn_layout = EscapeLayout::new(Arc::new(Layout::new(vec![Shape::Fcn {
        dom: Arc::from([Value::Int(0), Value::Int(1)]),
        range: Box::new(Shape::Int { lo: 0, hi: 1 }),
        witness: FcnWitness::Interval,
        key_variants: Arc::from([]),
    }])));
    let pairs = vec![(Value::Int(0), Value::Int(0)), (Value::Int(1), Value::Int(1))];
    let intv = Value::fcn_with_dom(pairs.clone(), FcnDom::Interval);
    let enum_f = Value::fcn_with_dom(pairs, FcnDom::Enumerated);
    let w_intv = fcn_layout.encode(std::slice::from_ref(&intv)).unwrap();
    let w_enum_f = fcn_layout.encode(std::slice::from_ref(&enum_f)).unwrap();
    assert!(!fcn_layout.is_escaped(&w_intv));
    assert!(fcn_layout.is_escaped(&w_enum_f));
    assert_eq!(fcn_layout.key(&w_intv), fcn_layout.key(&w_enum_f));
}

#[test]
fn inferred_union_of_record_and_function_shares_escape_key_with_alias() {
    use tlx_value::{FcnDom, Sym};

    let sym_a = Sym::new("a");
    let rec = Value::record(vec![(sym_a, Value::Int(1))]);
    let int_fcn = Value::fcn_with_dom(vec![(Value::Int(0), Value::Int(1))], FcnDom::Enumerated);
    let rec_alias = Value::fcn_with_dom(vec![(Value::Str(sym_a), Value::Int(1))], FcnDom::Enumerated);

    // Join `[a |-> 1]` and `[i \in {0} |-> 1]`: a `Union` with both a `Fcn`
    // arm (integer domain) and a `Record` arm. `[i \in {"a"} |-> 1]` must pick
    // the `Record` arm semantically, matching `[a |-> 1]`'s key and encoding.
    let union = Shape::of(&rec).join(&Shape::of(&int_fcn));
    assert!(matches!(union, Shape::Union(_)), "expected union, got {union:?}");
    assert!(union.contains_semantic(&rec_alias));
    let mut w_sem_rec = vec![0u64; tlx_layout::layout::words(&union)];
    let mut w_sem_alias = vec![0u64; tlx_layout::layout::words(&union)];
    tlx_layout::layout::encode_semantic(&union, &rec, &mut w_sem_rec).unwrap();
    tlx_layout::layout::encode_semantic(&union, &rec_alias, &mut w_sem_alias).unwrap();
    assert_eq!(w_sem_rec, w_sem_alias);

    let layout = EscapeLayout::new(Arc::new(Layout::new(vec![union])));
    let w_rec = layout.encode(std::slice::from_ref(&rec)).unwrap();
    let w_alias = layout.encode(std::slice::from_ref(&rec_alias)).unwrap();
    assert!(!layout.is_escaped(&w_rec));
    assert!(layout.is_escaped(&w_alias));
    assert_eq!(layout.decode(&w_rec), vec![rec.clone()]);
    assert_eq!(layout.decode(&w_alias), vec![rec_alias.clone()]);
    assert_eq!(layout.key(&w_rec), layout.key(&w_alias));

    // Also cover a `Union` of a `Map` (int keys) and a `Record` (string keys),
    // and a `Union` of a string-domain `Fcn` and a non-empty `Tuple`.
    let int_fcn2 = Value::fcn_with_dom(vec![(Value::Int(0), Value::Int(1)), (Value::Int(2), Value::Int(1))], FcnDom::Enumerated);
    let map_union = Shape::of(&rec).join(&Shape::of(&int_fcn)).join(&Shape::of(&int_fcn2));
    assert!(matches!(map_union, Shape::Union(_)), "expected union with Map, got {map_union:?}");
    assert!(map_union.contains_semantic(&rec_alias));
    let map_layout = EscapeLayout::new(Arc::new(Layout::new(vec![map_union])));
    let mw_rec = map_layout.encode(std::slice::from_ref(&rec)).unwrap();
    let mw_alias = map_layout.encode(std::slice::from_ref(&rec_alias)).unwrap();
    assert_eq!(map_layout.key(&mw_rec), map_layout.key(&mw_alias));

    let tup = Value::tuple(vec![Value::Int(1)]);
    let str_fcn = Value::fcn_with_dom(vec![(Value::Str(Sym::new("x")), Value::Int(1))], FcnDom::Enumerated);
    let tup_alias = Value::fcn_with_dom(vec![(Value::Int(1), Value::Int(1))], FcnDom::Enumerated);
    let tup_union = Shape::of(&tup).join(&Shape::of(&str_fcn));
    assert!(matches!(tup_union, Shape::Union(_)), "expected union with Tuple, got {tup_union:?}");
    assert!(tup_union.contains_semantic(&tup_alias));
    let tup_layout = EscapeLayout::new(Arc::new(Layout::new(vec![tup_union])));
    let tw_tup = tup_layout.encode(std::slice::from_ref(&tup)).unwrap();
    let tw_alias = tup_layout.encode(std::slice::from_ref(&tup_alias)).unwrap();
    assert_eq!(tup_layout.key(&tw_tup), tup_layout.key(&tw_alias));
}

#[test]
fn function_domain_key_witness_variants_preserve_decode_and_share_escape_key() {
    use tlx_layout::layout::{decode, encode, encode_semantic, words};
    use tlx_layout::layout_tree::{transcode, LayoutNode};
    use tlx_value::FcnDom;

    let tup_key = Value::tuple(vec![Value::Int(0)]);
    let enum_key = Value::fcn_with_dom(vec![(Value::Int(1), Value::Int(0))], FcnDom::Enumerated);
    assert_eq!(tup_key, enum_key);
    assert!(!tup_key.exact_eq(&enum_key));

    let f_tup = Value::fcn_with_dom(vec![(tup_key.clone(), Value::Int(0))], FcnDom::Enumerated);
    let f_enum = Value::fcn_with_dom(vec![(enum_key.clone(), Value::Int(0))], FcnDom::Enumerated);
    assert_eq!(f_tup, f_enum);
    assert!(!f_tup.exact_eq(&f_enum));

    // Single-key shape rejects the other key witness in exact mode, accepts in semantic mode.
    let s_tup = Shape::of(&f_tup);
    let s_enum = Shape::of(&f_enum);
    assert_ne!(s_tup, s_enum);
    assert!(s_tup.contains(&f_tup));
    assert!(!s_tup.contains(&f_enum));
    assert!(s_tup.contains_semantic(&f_enum));

    // Escape mode with single-key shape: `f_enum` escapes to keep its key witness,
    // yet both produce identical canonical visited keys.
    let single_escape = EscapeLayout::new(Arc::new(Layout::new(vec![s_tup.clone()])));
    let ew_tup = single_escape.encode(std::slice::from_ref(&f_tup)).unwrap();
    let ew_enum = single_escape.encode(std::slice::from_ref(&f_enum)).unwrap();
    assert!(!single_escape.is_escaped(&ew_tup));
    assert!(single_escape.is_escaped(&ew_enum));
    assert!(single_escape.decode(&ew_tup)[0].exact_eq(&f_tup));
    assert!(single_escape.decode(&ew_enum)[0].exact_eq(&f_enum));
    assert_eq!(single_escape.key(&ew_tup), single_escape.key(&ew_enum));

    // Joining the two shapes is commutative and idempotent, and encodes both inline
    // with exact round-trip decoding and identical canonical/semantic words.
    let joined_ab = s_tup.join(&s_enum);
    let joined_ba = s_enum.join(&s_tup);
    assert_eq!(joined_ab, joined_ba);
    assert_eq!(joined_ab.join(&s_tup), joined_ab);
    assert_eq!(joined_ab.join(&s_enum), joined_ab);
    assert!(joined_ab.has_dynamic_witness());
    assert_eq!(joined_ab.cardinality(), None);

    let mut w_tup = vec![0u64; words(&joined_ab)];
    let mut w_enum = vec![0u64; words(&joined_ab)];
    encode(&joined_ab, &f_tup, &mut w_tup).unwrap();
    encode(&joined_ab, &f_enum, &mut w_enum).unwrap();
    assert_ne!(w_tup, w_enum);
    assert!(decode(&joined_ab, &w_tup).exact_eq(&f_tup));
    assert!(decode(&joined_ab, &w_enum).exact_eq(&f_enum));

    let node = LayoutNode::new(&joined_ab);
    assert!(node.decode(&w_tup).exact_eq(&f_tup));
    assert!(node.decode(&w_enum).exact_eq(&f_enum));

    let mut bad = w_tup.clone();
    *bad.last_mut().unwrap() = 2;
    assert!(node.validate_words(&bad).is_err());

    let mut sem_tup = vec![0u64; words(&joined_ab)];
    let mut sem_enum = vec![0u64; words(&joined_ab)];
    encode_semantic(&joined_ab, &f_tup, &mut sem_tup).unwrap();
    encode_semantic(&joined_ab, &f_enum, &mut sem_enum).unwrap();
    assert_eq!(sem_tup, sem_enum);

    let mut can_tup = w_tup.clone();
    let mut can_enum = w_enum.clone();
    node.canonicalize_words(&mut can_tup);
    node.canonicalize_words(&mut can_enum);
    assert_eq!(can_tup, sem_tup);
    assert_eq!(can_enum, sem_enum);

    // Transcoding from a single-key layout into the widened key-variant layout
    // preserves the original key witness.
    let old_node = LayoutNode::new(&s_enum);
    let mut old_w = vec![0u64; old_node.words()];
    old_node.encode(&f_enum, &mut old_w).unwrap();
    let mut new_w = vec![0u64; node.words()];
    assert!(transcode(&old_node, &node, &old_w, &mut new_w));
    assert!(node.decode(&new_w).exact_eq(&f_enum));

    // Escape mode with the widened shape keeps both inline and gives identical keys.
    let widened_escape = EscapeLayout::new(Arc::new(Layout::new(vec![joined_ab])));
    let ww_tup = widened_escape.encode(std::slice::from_ref(&f_tup)).unwrap();
    let ww_enum = widened_escape.encode(std::slice::from_ref(&f_enum)).unwrap();
    assert!(!widened_escape.is_escaped(&ww_tup));
    assert!(!widened_escape.is_escaped(&ww_enum));
    assert!(widened_escape.decode(&ww_tup)[0].exact_eq(&f_tup));
    assert!(widened_escape.decode(&ww_enum)[0].exact_eq(&f_enum));
    assert_eq!(widened_escape.key(&ww_tup), widened_escape.key(&ww_enum));

    // Nested dynamic witness inside a static-witness `Shape::Fcn` range must
    // still propagate `has_dynamic_witness()` and canonicalize inner slots.
    let outer_tup = Value::fcn_with_dom(vec![(Value::Int(3), tup_key.clone())], FcnDom::Enumerated);
    let outer_enum = Value::fcn_with_dom(vec![(Value::Int(3), enum_key.clone())], FcnDom::Enumerated);
    let outer_shape = Shape::of(&outer_tup).join(&Shape::of(&outer_enum));
    assert!(outer_shape.has_dynamic_witness());
    let outer_node = LayoutNode::new(&outer_shape);
    assert!(outer_node.has_dynamic_witness());
    let mut ow_tup = vec![0u64; outer_node.words()];
    let mut ow_enum = vec![0u64; outer_node.words()];
    outer_node.encode(&outer_tup, &mut ow_tup).unwrap();
    outer_node.encode(&outer_enum, &mut ow_enum).unwrap();
    assert_ne!(ow_tup, ow_enum);
    outer_node.canonicalize_words(&mut ow_tup);
    outer_node.canonicalize_words(&mut ow_enum);
    assert_eq!(ow_tup, ow_enum);

    // `Shape::Dyn` (used when sets hold dynamic-witness elements) preserves
    // exact element witnesses on encode/decode while canonicalizing handles
    // for state fingerprints and escape keys.
    let s_enum_set = Value::set_from(vec![enum_key.clone()]).unwrap();
    let s_tup_set = Value::set_from(vec![tup_key.clone()]).unwrap();
    assert_eq!(s_enum_set, s_tup_set);
    assert!(!s_enum_set.exact_eq(&s_tup_set));

    let dyn_node = LayoutNode::new(&Shape::Dyn);
    assert!(dyn_node.has_dynamic_witness());
    let mut dw_enum = [0u64];
    let mut dw_tup = [0u64];
    dyn_node.encode(&s_enum_set, &mut dw_enum).unwrap();
    dyn_node.encode(&s_tup_set, &mut dw_tup).unwrap();
    assert_ne!(dw_enum, dw_tup);
    assert!(dyn_node.decode(&dw_enum).exact_eq(&s_enum_set));
    assert!(dyn_node.decode(&dw_tup).exact_eq(&s_tup_set));

    let mut dsem_enum = [0u64];
    let mut dsem_tup = [0u64];
    dyn_node.encode_semantic(&s_enum_set, &mut dsem_enum).unwrap();
    dyn_node.encode_semantic(&s_tup_set, &mut dsem_tup).unwrap();
    assert_eq!(dsem_enum, dsem_tup);

    let mut dcan_enum = dw_enum;
    let mut dcan_tup = dw_tup;
    dyn_node.canonicalize_words(&mut dcan_enum);
    dyn_node.canonicalize_words(&mut dcan_tup);
    assert_eq!(dcan_enum, dsem_enum);
    assert_eq!(dcan_tup, dsem_tup);

    let dyn_escape = EscapeLayout::new(Arc::new(Layout::new(vec![Shape::Dyn])));
    let de_enum = dyn_escape.encode(std::slice::from_ref(&s_enum_set)).unwrap();
    let de_tup = dyn_escape.encode(std::slice::from_ref(&s_tup_set)).unwrap();
    assert!(dyn_escape.decode(&de_enum)[0].exact_eq(&s_enum_set));
    assert!(dyn_escape.decode(&de_tup)[0].exact_eq(&s_tup_set));
    assert_eq!(dyn_escape.key(&de_enum), dyn_escape.key(&de_tup));
    assert_eq!(dyn_escape.key(&de_enum), dyn_escape.key(&dyn_escape.force_escape(std::slice::from_ref(&s_tup_set)).unwrap()));

    // Stored intervals vs equal enumerated sets: `Shape::Set` rejects intervals
    // in exact mode (so escape mode escapes them and widening joins to `Dyn`),
    // preserving `Value::Interval` on decode while keeping visited keys equal.
    let enum_set = Value::set_from(vec![Value::Int(0), Value::Int(1)]).unwrap();
    let iv_set = Value::Interval(0, 1);
    let set_layout = EscapeLayout::new(Arc::new(Layout::new(vec![Shape::of(&enum_set)])));
    let w_es = set_layout.encode(std::slice::from_ref(&enum_set)).unwrap();
    let w_iv = set_layout.encode(std::slice::from_ref(&iv_set)).unwrap();
    assert!(!set_layout.is_escaped(&w_es));
    assert!(set_layout.is_escaped(&w_iv));
    assert!(set_layout.decode(&w_es)[0].exact_eq(&enum_set));
    assert!(set_layout.decode(&w_iv)[0].exact_eq(&iv_set));
    assert_eq!(set_layout.key(&w_es), set_layout.key(&w_iv));

    assert_eq!(Shape::of(&enum_set).join(&Shape::of(&iv_set)), Shape::Dyn);
    let d_es = dyn_escape.encode(std::slice::from_ref(&enum_set)).unwrap();
    let d_iv = dyn_escape.encode(std::slice::from_ref(&iv_set)).unwrap();
    assert!(dyn_escape.decode(&d_es)[0].exact_eq(&enum_set));
    assert!(dyn_escape.decode(&d_iv)[0].exact_eq(&iv_set));
    assert_eq!(dyn_escape.key(&d_es), dyn_escape.key(&d_iv));
}
