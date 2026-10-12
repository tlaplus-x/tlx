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
