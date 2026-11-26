use std::sync::Arc;

use super::*;
use tlx_testkit::spec::load;

#[test]
fn fingerprints_match_inline_and_escaped_forms() {
    let src = "---- MODULE EscapeFp ----\nEXTENDS Integers\nVARIABLE x\nInit == x = 0\nNext == UNCHANGED x\n====";
    let base = Arc::new(load(src, "INIT Init\nNEXT Next\n"));
    let settings = Settings::from_lookup(|k| match k {
        "TLX_ESCAPE" | "TLX_NO_NATIVE" => Some("1".into()),
        _ => None,
    })
    .unwrap();
    let model = EncModel::new(base, Arc::new(Layout::new(vec![Shape::Int { lo: -2, hi: 2 }])), Vec::new(), &settings);
    let codec = &model.escape.as_ref().unwrap().codec;
    for x in [-2, 0, 2, 3, i64::MAX] {
        let vals = [Value::Int(x)];
        let inline = codec.encode(&vals).unwrap();
        let escaped = codec.force_escape(&vals).unwrap();
        assert_eq!(codec.decode(&inline), codec.decode(&escaped));
        assert_eq!(model.words_fp(&inline, 1).unwrap(), model.words_fp(&escaped, 1).unwrap());
    }
}

#[test]
fn collection_and_view_fingerprints_match_both_physical_forms() {
    let src = "---- MODULE EscapeFp ----\nEXTENDS Integers, Sequences\nVARIABLE x\nInit == x = <<1, 2>>\nNext == UNCHANGED x\nV == x\n====";
    let settings = Settings::from_lookup(|k| match k {
        "TLX_ESCAPE" | "TLX_NO_NATIVE" => Some("1".into()),
        _ => None,
    })
    .unwrap();
    let cases = [
        Value::tuple(vec![Value::Int(1), Value::Int(2)]),
        Value::set_from(vec![Value::Int(1), Value::Int(2)]).unwrap(),
        Value::fcn_rcd_from_pairs(vec![(Value::Int(1), Value::Int(3)), (Value::Int(2), Value::Int(4))]).unwrap(),
    ];
    for value in cases {
        for view in ["", "VIEW V\n"] {
            let base = Arc::new(load(src, &format!("INIT Init\nNEXT Next\n{view}")));
            let defs = super::super::speculate::view_def(&base).map(|d| vec![(d, Shape::of(&value))]).unwrap_or_default();
            let model = EncModel::new(base, Arc::new(Layout::new(vec![Shape::of(&value)])), defs, &settings);
            let codec = &model.escape.as_ref().unwrap().codec;
            let vals = [value.clone()];
            let inline = codec.encode(&vals).unwrap();
            let escaped = codec.force_escape(&vals).unwrap();
            assert_eq!(codec.decode(&inline), codec.decode(&escaped));
            let state = model.encode(&VState::new(vals.to_vec().into(), 1, 0)).unwrap();
            assert_eq!(state.fp, model.words_fp(&escaped, 1).unwrap(), "value {value:?}, config {view:?}");
        }
    }
}

#[test]
fn print_only_actions_deoptimize_without_repeating_output() {
    let src = "---- MODULE EscapePrint ----\nEXTENDS Naturals, TLC\nVARIABLE x\nInit == x = 0\nNext == PrintT(x) /\\ x' = x + 1\n====";
    let base = Arc::new(load(src, "INIT Init\nNEXT Next\n"));
    let settings = Settings::from_lookup(|k| match k {
        "TLX_ESCAPE" | "TLX_NATIVE_SYNC" => Some("1".into()),
        "TLX_JIT" => Some("0".into()),
        _ => None,
    })
    .unwrap();
    let model = EncModel::new(base, Arc::new(Layout::new(vec![Shape::Int { lo: 0, hi: 0 }])), Vec::new(), &settings);
    assert!(model.prints[0]);
    assert!(model.compiled_path(0, true).is_some());
    let state = model.encode(&VState::new(vec![Value::Int(0)].into(), 1, 0)).unwrap();
    let mut next = Vec::new();
    let (result, lines) = tlx_eval::Interp::hold_output(|| {
        model.action_successors(&state, 0, &mut |s, _| {
            next.push(model.values(&s));
            true
        })
    });
    assert!(result.unwrap());
    assert_eq!(next, vec![Arc::<[Value]>::from(vec![Value::Int(1)])]);
    assert_eq!(lines, vec!["0"]);
    assert!(model.escape.as_ref().unwrap().deopts.get() > 0, "printing alone must not force the action into the interpreter");
}

#[test]
fn anonymous_projection_compiles_and_preserves_observed_distinctions() {
    let src = r#"---- MODULE Projected ----
EXTENDS Integers
VARIABLE r, tag
Init == tag = 0 /\ r = [mode |-> "idle", data |-> 0]
Step == \/ \E x \in {0, 1}: /\ r.mode = "idle"
                              /\ r' = [r EXCEPT !.mode = "busy", !.data = x]
        \/ /\ r.mode = "busy" /\ r.data >= 0
           /\ r' = [r EXCEPT !.mode = "idle"]
Next == tag' = 1 /\ Step
Inv == r \in [mode: {"idle", "busy"}, data: {0, 1}]
===="#;
    for mapped in [false, true] {
        let source = if mapped {
            src.replace("VARIABLE r", "CONSTANT Actors\nVARIABLE r")
                .replace("r = [mode |-> \"idle\", data |-> 0]", "r = [s \\in Actors |-> [mode |-> \"idle\", data |-> 0]]")
                .replace("Step ==", "Step == \\E s \\in Actors:")
                .replace("r.mode", "r[s].mode")
                .replace("r.data", "r[s].data")
                .replace("!.", "![s].")
                .replace(
                    "r \\in [mode: {\"idle\", \"busy\"}, data: {0, 1}]",
                    "r \\in [Actors -> [mode: {\"idle\", \"busy\"}, data: {0, 1}]]",
                )
        } else {
            src.to_owned()
        };
        let value = |mode, data| {
            let record = Value::record(vec![
                (tlx_value::Sym::new("mode"), Value::Str(tlx_value::Sym::new(mode))),
                (tlx_value::Sym::new("data"), Value::Int(data)),
            ]);
            if mapped {
                Value::fcn_rcd_from_pairs(["a", "b"].iter().map(|s| (Value::ModelValue(tlx_value::Sym::new(s)), record.clone())).collect())
                    .unwrap()
            } else {
                record
            }
        };
        let shape = Shape::of(&value("idle", 0)).join(&Shape::of(&value("busy", 1)));
        for no_native in [true, false] {
            let cfg = format!("INIT Init\nNEXT Next\nINVARIANT Inv\n{}", if mapped { "CONSTANT Actors = {a, b}\n" } else { "" });
            let mut base = load(&source, &cfg);
            assert!(base.project_state().is_some());
            let settings = Settings::from_lookup(|key| match key {
                "TLX_PARANOID" => Some("1".into()),
                "TLX_NO_NATIVE" if no_native => Some("1".into()),
                "TLX_JIT" => Some("0".into()),
                _ => None,
            })
            .unwrap();
            let model =
                EncModel::new(Arc::new(base), Arc::new(Layout::new(vec![shape.clone(), Shape::Int { lo: 0, hi: 1 }])), vec![], &settings);
            let Fingerprint::View(view) = &model.fp else { panic!("anonymous VIEW was not compiled") };
            assert!(view.def.is_none());
            assert!(view.fast.is_some() || view.native.is_some());
            let fingerprint =
                |mode, data, tag| model.encode(&VState::new(vec![value(mode, data), Value::Int(tag)].into(), 1, 0)).unwrap().fp;
            assert_eq!(fingerprint("idle", 0, 0), fingerprint("idle", 0, 1));
            assert_ne!(fingerprint("idle", 0, 0), fingerprint("idle", 1, 0));
            assert_ne!(fingerprint("busy", 0, 0), fingerprint("busy", 1, 0));
            assert_ne!(fingerprint("idle", 0, 0), fingerprint("busy", 0, 0));
        }
    }
}

#[test]
fn refused_projection_retains_declared_symmetry_multiset_classes() {
    let src = r#"---- MODULE Orbit ----
EXTENDS Integers, TLC
CONSTANT Actors
VARIABLE r
Init == r = [s \in Actors |-> [mode |-> "idle", data |-> 0]]
Next == \E s \in Actors:
          \/ \E n \in {0, 1}: /\ r[s].mode = "idle"
                                /\ r' = [r EXCEPT ![s].mode = "busy", ![s].data = n]
          \/ /\ r[s].mode = "busy" /\ r[s].data >= 0
             /\ r' = [r EXCEPT ![s].mode = "idle"]
Inv == r \in [Actors -> [mode: {"idle", "busy"}, data: {0, 1}]]
Sym == Permutations(Actors)
===="#;
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\nCONSTANT Actors = {a, b}\nSYMMETRY Sym\n";
    let local = |i: usize| {
        Value::record(vec![
            (tlx_value::Sym::new("data"), Value::Int((i % 2) as i64)),
            (tlx_value::Sym::new("mode"), Value::Str(tlx_value::Sym::new(if i < 2 { "idle" } else { "busy" }))),
        ])
    };
    let value = |i, j| {
        Value::fcn_rcd_from_pairs(vec![
            (Value::ModelValue(tlx_value::Sym::new("a")), local(i)),
            (Value::ModelValue(tlx_value::Sym::new("b")), local(j)),
        ])
        .unwrap()
    };
    let shape = Shape::of(&value(0, 0)).join(&Shape::of(&value(3, 3)));
    for (no_native, escape) in [(true, false), (false, false), (true, true)] {
        let mut base = load(src, cfg);
        assert!(base.project_state().is_none());
        let fingerprints: Vec<_> = (0..4)
            .flat_map(|i| (0..4).map(move |j| (i, j)))
            .map(|(i, j)| base.make_state(&[Some(value(i, j))], 1, "test").unwrap().fp)
            .collect();
        let settings = Settings::from_lookup(|key| match key {
            "TLX_NO_NATIVE" if no_native => Some("1".into()),
            "TLX_ESCAPE" if escape => Some("1".into()),
            "TLX_PARANOID" | "TLX_NATIVE_SYNC" => Some("1".into()),
            "TLX_JIT" => Some("0".into()),
            _ => None,
        })
        .unwrap();
        let model = EncModel::new(Arc::new(base), Arc::new(Layout::new(vec![shape.clone()])), vec![], &settings);
        assert!(matches!(model.fp, Fingerprint::Symmetry { .. }));
        let mut compiled = Vec::new();
        let mut classes = Vec::new();
        for i in 0..4 {
            for j in 0..4 {
                let mut class = [i, j];
                class.sort();
                classes.push(class);
                let vals = vec![value(i, j)];
                let state = model.encode(&VState::new(vals.clone().into(), 1, 0)).unwrap();
                compiled.push(state.fp);
                if let Some(escape) = &model.escape {
                    assert_eq!(state.fp, model.words_fp(&escape.codec.force_escape(&vals).unwrap(), 1).unwrap());
                }
            }
        }
        for i in 0..16 {
            for j in 0..16 {
                assert_eq!(fingerprints[i] == fingerprints[j], classes[i] == classes[j]);
                assert_eq!(compiled[i] == compiled[j], classes[i] == classes[j]);
            }
        }
    }
}

#[test]
fn witness_only_view_miss_matches_canonical_view_in_escape_mode() {
    let src = r#"---- MODULE EscapeViewWitness ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == UNCHANGED x
V == IF x = 0 THEN <<1>> ELSE [i \in {1} |-> 1]
===="#;
    let settings = Settings::from_lookup(|k| match k {
        "TLX_ESCAPE" | "TLX_NO_NATIVE" => Some("1".into()),
        _ => None,
    })
    .unwrap();
    let base = Arc::new(load(src, "INIT Init\nNEXT Next\nVIEW V\n"));
    let view_shape = Shape::Tuple(Arc::from([Shape::Int { lo: 1, hi: 1 }]));
    let defs = vec![(super::super::speculate::view_def(&base).unwrap(), view_shape)];
    let model = EncModel::new(base, Arc::new(Layout::new(vec![Shape::Int { lo: 0, hi: 1 }])), defs, &settings);
    let codec = &model.escape.as_ref().unwrap().codec;

    // `x = 0` produces `<<1>>` (fits Tuple VIEW); `x = 1` produces `[i \in {1} |-> 1]`
    // (witness-only VIEW miss on both inline and escaped states). All must match.
    let s0_inline = codec.encode(&[Value::Int(0)]).unwrap();
    let s0_escaped = codec.force_escape(&[Value::Int(0)]).unwrap();
    let s1_inline = codec.encode(&[Value::Int(1)]).unwrap();
    let s1_escaped = codec.force_escape(&[Value::Int(1)]).unwrap();
    let fp0 = model.words_fp(&s0_inline, 1).unwrap();
    assert_eq!(fp0, model.words_fp(&s0_escaped, 1).unwrap());
    assert_eq!(fp0, model.words_fp(&s1_inline, 1).unwrap());
    assert_eq!(fp0, model.words_fp(&s1_escaped, 1).unwrap());
}

#[test]
fn out_of_layout_view_on_dynamic_witness_shape_does_not_panic() {
    let src = r#"---- MODULE EscapeViewDynOutlier ----
EXTENDS Integers
VARIABLE x
Init == x = 0
Next == UNCHANGED x
V == IF x = 0 THEN <<0, 1>> ELSE IF x = 1 THEN [i \in {1, 2} |-> i - 1] ELSE "outlier"
===="#;
    let settings = Settings::from_lookup(|k| match k {
        "TLX_ESCAPE" | "TLX_NO_NATIVE" => Some("1".into()),
        _ => None,
    })
    .unwrap();
    let base = Arc::new(load(src, "INIT Init\nNEXT Next\nVIEW V\n"));
    // 3-word VIEW shape (2 slots + 1 dynamic witness word): an out-of-layout
    // VIEW produces a digest that must not be walked as a 3-word buffer.
    let view_shape = Shape::Fcn {
        dom: Arc::from([Value::Int(1), Value::Int(2)]),
        range: Box::new(Shape::Int { lo: 0, hi: 1 }),
        witness: tlx_layout::FcnWitness::Dynamic,
        key_variants: Arc::from([]),
    };
    let defs = vec![(super::super::speculate::view_def(&base).unwrap(), view_shape)];
    let model = EncModel::new(base, Arc::new(Layout::new(vec![Shape::Int { lo: 0, hi: 2 }])), defs, &settings);
    let codec = &model.escape.as_ref().unwrap().codec;

    // `x = 0` (`<<0, 1>>`) and `x = 1` (`[i \in {1, 2} |-> i - 1]`) share one VIEW fp.
    let fp0 = model.words_fp(&codec.encode(&[Value::Int(0)]).unwrap(), 1).unwrap();
    let fp1 = model.words_fp(&codec.encode(&[Value::Int(1)]).unwrap(), 1).unwrap();
    assert_eq!(fp0, fp1);

    // `x = 2` (`"outlier"`) is out-of-layout on an inline state and on an escaped state.
    let s2_inline = codec.encode(&[Value::Int(2)]).unwrap();
    let s2_escaped = codec.force_escape(&[Value::Int(2)]).unwrap();
    let fp2_inline = model.words_fp(&s2_inline, 1).unwrap();
    let fp2_escaped = model.words_fp(&s2_escaped, 1).unwrap();
    assert_eq!(fp2_inline, fp2_escaped);
    assert_ne!(fp0, fp2_inline);
}

#[test]
fn escape_fp_large_factorized_symmetry_matches_inline_and_outliers() {
    let src = r#"---- MODULE EscapeLargeSym ----
EXTENDS Integers, TLC
CONSTANT N
VARIABLES x, y
Sym == Permutations(N)
V == <<x, y>>
Init == x = 0 /\ y \in N
Next == UNCHANGED <<x, y>>
===="#;
    let cfg_noview = "CONSTANT N = {n1, n2, n3, n4, n5, n6, n7}\nINIT Init\nNEXT Next\nSYMMETRY Sym\n";
    let cfg_view = format!("{cfg_noview}VIEW V\n");
    let mut n_vals: Vec<Value> = (1..=7).map(|i| Value::ModelValue(tlx_value::Sym::new(&format!("n{i}")))).collect();
    n_vals.sort();
    let x_shape = Shape::Int { lo: 0, hi: 1 };
    let y_shape = Shape::Atom(n_vals.clone().into());
    let settings = Settings::from_lookup(|k| match k {
        "TLX_ESCAPE" | "TLX_NO_NATIVE" => Some("1".into()),
        _ => None,
    })
    .unwrap();

    // No-VIEW: inline, force-escaped, and genuine outlier states across S_7 (order 5040 > 720).
    let base_nv = Arc::new(load(src, cfg_noview));
    assert!(base_nv.symmetry_maps().is_empty());
    let model_nv = EncModel::new(base_nv, Arc::new(Layout::new(vec![x_shape.clone(), y_shape.clone()])), vec![], &settings);
    assert!(matches!(model_nv.fp, Fingerprint::Symmetry { .. }));
    let codec = &model_nv.escape.as_ref().unwrap().codec;
    let fp_inline_0 = model_nv.words_fp(&codec.encode(&[Value::Int(0), n_vals[0].clone()]).unwrap(), 1).unwrap();
    let fp_outlier_0 = model_nv.words_fp(&codec.encode(&[Value::Int(999), n_vals[0].clone()]).unwrap(), 1).unwrap();
    assert_ne!(fp_inline_0, fp_outlier_0);
    for v in &n_vals {
        let inline = codec.encode(&[Value::Int(0), v.clone()]).unwrap();
        let forced = codec.force_escape(&[Value::Int(0), v.clone()]).unwrap();
        let outlier = codec.encode(&[Value::Int(999), v.clone()]).unwrap();
        assert_eq!(model_nv.words_fp(&inline, 1).unwrap(), fp_inline_0);
        assert_eq!(model_nv.words_fp(&forced, 1).unwrap(), fp_inline_0);
        assert_eq!(model_nv.words_fp(&outlier, 1).unwrap(), fp_outlier_0);
    }

    // With VIEW: SymView on S_7 handles both force-escaped and genuine outliers.
    let base_v = Arc::new(load(src, &cfg_view));
    let view_def = super::super::speculate::view_def(&base_v).unwrap();
    let view_shape = Shape::Tuple(vec![x_shape.clone(), y_shape.clone()].into());
    let model_v = EncModel::new(base_v, Arc::new(Layout::new(vec![x_shape, y_shape])), vec![(view_def, view_shape)], &settings);
    assert!(matches!(model_v.fp, Fingerprint::SymView { .. }));
    let codec_v = &model_v.escape.as_ref().unwrap().codec;
    let vfp_inline = model_v.words_fp(&codec_v.encode(&[Value::Int(0), n_vals[0].clone()]).unwrap(), 1).unwrap();
    let vfp_outlier = model_v.words_fp(&codec_v.encode(&[Value::Int(999), n_vals[0].clone()]).unwrap(), 1).unwrap();
    for v in &n_vals {
        let forced = codec_v.force_escape(&[Value::Int(0), v.clone()]).unwrap();
        let outlier = codec_v.encode(&[Value::Int(999), v.clone()]).unwrap();
        assert_eq!(model_v.words_fp(&forced, 1).unwrap(), vfp_inline);
        assert_eq!(model_v.words_fp(&outlier, 1).unwrap(), vfp_outlier);
    }
}
