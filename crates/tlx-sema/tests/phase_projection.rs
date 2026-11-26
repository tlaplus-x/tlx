use tlx_front::cfg::parse_cfg;
use tlx_sema::hir::{Expr, ExprKind, OpRef, RootSymbol};
use tlx_sema::{optimize::phase_projection, Program};

const BODY: &str = r#"
VARIABLE r
Init == r = [mode |-> "idle", data |-> 0]
Start == \E n \in {0, 1}: /\ r.mode = "idle"
                              /\ r' = [r EXCEPT !.mode = "busy", !.data = n]
Finish == /\ r.mode = "busy"
          /\ r.data >= 0
          /\ r' = [r EXCEPT !.mode = "idle"]
Next == Start \/ Finish
Inv == r \in [mode: {"idle", "busy"}, data: {0, 1}]
"#;

fn projection(body: &str) -> Vec<String> {
    configured_projection(body, "")
}

fn configured_projection(body: &str, constants: &str) -> Vec<String> {
    let dir = tlx_testkit::TempDir::new("phase-sema");
    let path = dir.write("Phase.tla", &format!("---- MODULE Phase ----\nEXTENDS Integers, Sequences, TLC\n{body}\n====\n"));
    let mut p = Program::load(&path, &[]).unwrap();
    p.resolve_all_root();
    let roots = ["Init", "Next", "Inv"].map(|name| {
        let Some(RootSymbol::Def(id)) = p.lookup_root(name) else { panic!("missing {name}") };
        Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
    });
    let cfg = parse_cfg(&format!("INIT Init\nNEXT Next\nINVARIANT Inv\n{constants}")).unwrap();
    phase_projection(&p, &cfg, &roots[0], &roots[1], &roots[2..])
        .map(|a| {
            assert!(a.certificate.as_ref().is_some_and(|s| s.contains("namespace TlxOptimization.GeneratedField")), "missing certificate");
            a.fields
        })
        .unwrap_or_default()
}

#[test]
fn derives_fields_from_structure_and_proves_type_observations() {
    assert_eq!(projection(BODY), ["r.data"]);
    assert_eq!(projection(&BODY.replace("data", "payload").replace("mode", "phase").replace("idle", "done")), ["r.payload"]);
    let helpers = format!("Control(record) == record.mode\n{}", BODY.replace("r.mode", "Control(r)"));
    // By-name inlining observes only the field used by the helper.
    assert_eq!(projection(&helpers), ["r.data"]);
}

#[test]
fn configured_phases_and_structural_numeric_domains() {
    let body = r#"
CONSTANTS Workers, Idle, Busy
VARIABLES r, n, history, entries
Init == /\ r = [w \in Workers |-> [mode |-> Idle, cached |-> <<>>, epoch |-> -1,
                                   entry |-> [id |-> 0, valid |-> TRUE]]]
        /\ n = 0 /\ history = <<>> /\ entries = <<>>
Collect(w) == /\ r[w].mode = Idle
              /\ n' = n + 1
              /\ history' = Append(history, n)
              /\ entries' = entries @@ (n :> [id |-> n, valid |-> TRUE])
              /\ r' = [r EXCEPT ![w].mode = Busy, ![w].cached = history,
                               ![w].epoch = n, ![w].entry = entries'[n]]
Use(w) == /\ r[w].mode = Busy
          /\ Len(r[w].cached) >= 0 /\ r[w].epoch >= -1 /\ r[w].entry.valid
          /\ r' = [r EXCEPT ![w].mode = Idle]
          /\ UNCHANGED <<n, history, entries>>
Next == \E w \in Workers: Collect(w) \/ Use(w)
Inv == r \in [Workers -> [mode: {Idle, Busy}, cached: Seq(Nat), epoch: Nat \cup {-1},
                          entry: [id: Nat, valid: BOOLEAN]]]
"#;
    let cfg = "CONSTANTS Workers = {a, b} Idle = Idle Busy = Busy\n";
    assert_eq!(configured_projection(body, cfg), ["r[*].cached", "r[*].entry", "r[*].epoch"]);
    for invalid in [
        body.replace("history' = Append(history, n)", "history' = Append(history, -1)"),
        body.replace("epoch |-> -1", "epoch |-> -2"),
        body.replace("cached: Seq(Nat)", "cached: Seq(3)"),
        body.replace("epoch: Nat \\cup {-1}", "epoch: Nat \\cup {\"bad\"}"),
        body.replace("id |-> n, valid |-> TRUE", "id |-> -1, valid |-> TRUE"),
    ] {
        assert!(configured_projection(&invalid, cfg).is_empty(), "{invalid}");
    }
    assert!(configured_projection(body, "CONSTANTS Workers = {a, b} Idle = p_Idle Busy = p_Busy\n").is_empty());
}

#[test]
fn except_old_values_and_by_name_reads_retain_their_context() {
    let body = format!("IsBusy(x) == x.mode = \"busy\"\n{}", BODY.replace("r.mode = \"busy\"", "IsBusy(r)"));
    assert_eq!(projection(&body), ["r.data"]);
    let before_guard =
        body.replace("Finish == /\\ IsBusy(r)\n          /\\ r.data >= 0", "Finish == /\\ r.data >= 0\n          /\\ IsBusy(r)");
    assert!(projection(&before_guard).is_empty());
    assert!(projection(&BODY.replace("!.data = n", "!.data = @")).is_empty());
    let effect = format!("Unused(x) == TRUE\n{}", BODY.replace("Inv ==", "Inv == Unused(PrintT(r)) /\\"));
    assert!(projection(&effect).is_empty());
    // A later @ sees the preceding update, including through a LET. Decline
    // uncertain overlap rather than substituting the old original point.
    let overlap = BODY
        .replace("VARIABLE r", "VARIABLES r, s")
        .replace("Init ==", "Init == s = [x |-> 0] /\\")
        .replace("Next == Start \\/ Finish", "Next == (Start \\/ Finish) /\\ s' = [s EXCEPT !.x = -2, !.x = LET old == @ IN old + 1]");
    assert!(projection(&overlap).is_empty());
}

#[test]
fn chooses_more_useful_control_field_instead_of_first_valid_candidate() {
    let body = BODY
        .replace("mode |->", "flag |-> FALSE, mode |->")
        .replace("!.mode = \"busy\"", "!.flag = TRUE, !.mode = \"busy\"")
        .replace("!.mode = \"idle\"", "!.flag = FALSE, !.mode = \"idle\"")
        .replace("mode:", "flag: BOOLEAN, mode:");
    assert!(projection(&body).contains(&"r.data".to_string()));
}

#[test]
fn observations_and_reads_before_guards_keep_values_live() {
    for body in [
        BODY.replace("Inv ==", "Inv == r.data = 0 /\\"),
        BODY.replace("r.mode = \"busy\"\n          /\\ r.data >= 0", "r.data >= 0\n          /\\ r.mode = \"busy\""),
        BODY.replace("Next == Start \\/ Finish", "Next == Start \\/ Finish \\/ (r.data >= 0 /\\ UNCHANGED r)"),
        BODY.replace("Inv ==", "Inv == PrintT(r) /\\"),
    ] {
        assert!(projection(&body).is_empty(), "{body}");
    }
}

#[test]
fn type_invariants_are_proved_never_assumed() {
    for body in [
        BODY.replace("n \\in {0, 1}", "n \\in {0, 1, 2}"),
        BODY.replace("data |-> 0", "data |-> 2"),
        BODY.replace("data: {0, 1}", "data: {0}"),
        BODY.replace("!.data = n", "!.data = r.data + 1"),
    ] {
        assert!(projection(&body).is_empty(), "{body}");
    }
}

#[test]
fn carry_edges_propagate_liveness_across_phases() {
    let body =
        BODY.replace("Next == Start \\/ Finish", "Next == Start \\/ Finish \\/ (r.mode = \"idle\" /\\ r' = [r EXCEPT !.mode = \"busy\"])");
    // The extra edge exposes the old value without overwriting it.
    assert!(projection(&body).is_empty());
}

#[test]
fn uncertain_and_duplicate_transfers_decline() {
    for body in [
        BODY.replace("!.data = n", "!.data = n, !.data = 0"),
        BODY.replace("Next == Start \\/ Finish", "Next == (Start /\\ UNCHANGED r) \\/ Finish"),
        BODY.replace("!.data = n", "!.data = @ + 1"),
        BODY.replace("r' = [r EXCEPT !.mode = \"idle\"]", "r' = [mode |-> \"idle\", data |-> 0, extra |-> 1]"),
    ] {
        assert!(projection(&body).is_empty(), "{body}");
    }
    // Whole-record writes preserving the exact field set are certified.
    assert_eq!(projection(&BODY.replace("r' = [r EXCEPT !.mode = \"idle\"]", "r' = [mode |-> \"idle\", data |-> r.data]")), ["r.data"]);
}

fn map_body() -> String {
    BODY.replace("r = [mode |-> \"idle\", data |-> 0]", "r = [s \\in {1, 2} |-> [mode |-> \"idle\", data |-> 0]]")
        .replace("Start ==", "Start(s) ==")
        .replace("Finish ==", "Finish(s) ==")
        .replace("r.mode", "r[s].mode")
        .replace("r.data", "r[s].data")
        .replace("!.", "![s].")
        .replace("Next == Start \\/ Finish", "Next == \\E s \\in {1, 2}: Start(s) \\/ Finish(s)")
        .replace("r \\in [mode: {\"idle\", \"busy\"}, data: {0, 1}]", "r \\in [{1, 2} -> [mode: {\"idle\", \"busy\"}, data: {0, 1}]]")
}

#[test]
fn fixed_maps_require_valid_keys_and_keep_cross_actor_reads() {
    let body = map_body();
    assert_eq!(projection(&body), ["r[*].data"]);
    assert!(projection(&body.replace("Next == \\E s \\in {1, 2}", "Next == \\E s \\in {1, 2, 3}")).is_empty());
    assert!(projection(&body.replace("r[s].data >= 0", "\\A t \\in {1, 2}: r[t].data >= 0")).is_empty());
}

#[test]
fn certificate_keeps_global_observations_and_noop_branches() {
    let body = BODY
        .replace("mode |->", "always |-> 7, mode |->")
        .replace("mode:", "always: {7}, mode:")
        .replace("Inv ==", "Inv == r.always = 7 /\\")
        .replace("Start \\/ Finish", "Start \\/ Finish \\/ UNCHANGED r");
    assert_eq!(projection(&body), ["r.data"]);
}

#[test]
fn whole_record_and_singleton_fn_construct_writes_certify() {
    // Whole-record scalar transitions on both Start and Finish.
    let whole_scalar = r#"
VARIABLE r
Init == r = [mode |-> "idle", data |-> 0]
Start == \E n \in {0, 1}: /\ r.mode = "idle"
                          /\ r' = [mode |-> "busy", data |-> n]
Finish == /\ r.mode = "busy"
          /\ r.data >= 0
          /\ r' = [mode |-> "idle", data |-> r.data]
Next == Start \/ Finish
Inv == r \in [mode: {"idle", "busy"}, data: {0, 1}]
"#;
    assert_eq!(projection(whole_scalar), ["r.data"]);

    // Whole-entry EXCEPT ![s] = [...] on a record map.
    let whole_map = r#"
VARIABLE r
Init == r = [s \in {1, 2} |-> [mode |-> "idle", data |-> 0]]
Start(s) == \E n \in {0, 1}: /\ r[s].mode = "idle"
                             /\ r' = [r EXCEPT ![s] = [mode |-> "busy", data |-> n]]
Finish(s) == /\ r[s].mode = "busy"
             /\ r[s].data >= 0
             /\ r' = [r EXCEPT ![s] = [mode |-> "idle", data |-> r[s].data]]
Next == \E s \in {1, 2}: Start(s) \/ Finish(s)
Inv == r \in [{1, 2} -> [mode: {"idle", "busy"}, data: {0, 1}]]
"#;
    assert_eq!(projection(whole_map), ["r[*].data"]);

    // Uniform FnConstruct reset is certified for |K| = 1 and refused for |K| > 1.
    let fn_reset_one = r#"
VARIABLE r
Init == r = [s \in {1} |-> [mode |-> "idle", data |-> 0]]
Start(s) == \E n \in {0, 1}: /\ r[s].mode = "idle"
                             /\ r' = [r EXCEPT ![s] = [mode |-> "busy", data |-> n]]
Finish(s) == /\ r[s].mode = "busy"
             /\ r[s].data >= 0
             /\ r' = [k \in {1} |-> [mode |-> "idle", data |-> 0]]
Next == \E s \in {1}: Start(s) \/ Finish(s)
Inv == r \in [{1} -> [mode: {"idle", "busy"}, data: {0, 1}]]
"#;
    assert_eq!(projection(fn_reset_one), ["r[*].data"]);
    assert!(projection(&fn_reset_one.replace("{1}", "{1, 2}")).is_empty());
}

#[test]
fn parallel_maps_scalar_companions_and_phase_guarded_observations() {
    // Scalar control variable governing scalar companion variable with phase-guarded Inv.
    let scalar_comp = r#"
VARIABLES pc, buf
Init == pc = "idle" /\ buf = 0
Start == \E n \in {0, 1, 2}: /\ pc = "idle" /\ pc' = "busy" /\ buf' = n
Finish == /\ pc = "busy" /\ buf >= 0 /\ pc' = "idle" /\ UNCHANGED buf
Next == Start \/ Finish
Inv == /\ pc \in {"idle", "busy"}
       /\ buf \in {0, 1, 2}
       /\ (pc = "busy" => buf >= 0)
"#;
    assert_eq!(projection(scalar_comp), ["buf"]);

    // Parallel fixed-domain maps over the same key set K with phase-guarded Inv
    // and an all-live shared map that stays untouched in C.
    let parallel_maps = r#"
VARIABLES pc, buf, shared
Init == /\ pc = [k \in {1, 2} |-> "idle"]
        /\ buf = [k \in {1, 2} |-> 0]
        /\ shared = [k \in {1, 2} |-> 0]
Start(k) == \E n \in {0, 1, 2}:
              /\ pc[k] = "idle"
              /\ pc' = [pc EXCEPT ![k] = "busy"]
              /\ buf' = [buf EXCEPT ![k] = n]
              /\ UNCHANGED shared
Finish(k) == /\ pc[k] = "busy"
             /\ buf[k] >= 0
             /\ pc' = [pc EXCEPT ![k] = "idle"]
             /\ shared' = [shared EXCEPT ![k] = buf[k]]
             /\ UNCHANGED buf
Next == \E k \in {1, 2}: Start(k) \/ Finish(k)
Inv == /\ pc \in [{1, 2} -> {"idle", "busy"}]
       /\ buf \in [{1, 2} -> {0, 1, 2}]
       /\ \A k \in {1, 2}: pc[k] = "busy" => buf[k] >= 0
       /\ \A k \in {1, 2}: shared[k] \in {0, 1, 2}
"#;
    assert_eq!(projection(parallel_maps), ["buf[*]"]);

    // IF-guarded and conjunction-guarded state observations also preserve deadness.
    let if_guarded = parallel_maps.replace("pc[k] = \"busy\" => buf[k] >= 0", "IF pc[k] = \"busy\" THEN buf[k] >= 0 ELSE TRUE");
    assert_eq!(projection(&if_guarded), ["buf[*]"]);

    // Unguarded cross-actor read in Inv or Next refuses projection.
    assert!(projection(&parallel_maps.replace("pc[k] = \"busy\" => buf[k] >= 0", "buf[k] >= 0")).is_empty());
    assert!(
        projection(&parallel_maps.replace("buf[k] >= 0\n             /\\", "\\A j \\in {1, 2}: buf[j] >= 0\n             /\\")).is_empty()
    );

    // Mismatched actors across control/companion maps refuse projection.
    let mismatched_ctrl = r#"
VARIABLES pc, buf
Init == pc = [k \in {1, 2} |-> "idle"] /\ buf = [k \in {1, 2} |-> 0]
Start(a, b) == \E n \in {0, 1}:
                 /\ pc[a] = "idle"
                 /\ pc' = [pc EXCEPT ![a] = "busy"]
                 /\ buf' = [buf EXCEPT ![b] = n]
Finish(a) == /\ pc[a] = "busy" /\ buf[a] >= 0
             /\ pc' = [pc EXCEPT ![a] = "idle"] /\ UNCHANGED buf
Next == (\E a, b \in {1, 2}: Start(a, b)) \/ (\E a \in {1, 2}: Finish(a))
Inv == pc \in [{1, 2} -> {"idle", "busy"}] /\ buf \in [{1, 2} -> {0, 1}]
"#;
    assert!(projection(mismatched_ctrl).is_empty());

    // Mismatched actors across two companions on an UNCHANGED-pc branch refuse both.
    let mismatched_companions = r#"
VARIABLES pc, m1, m2
Init == /\ pc = [k \in {1, 2} |-> "idle"]
        /\ m1 = [k \in {1, 2} |-> 0]
        /\ m2 = [k \in {1, 2} |-> 0]
Start(a) == \E n \in {0, 1}:
              /\ pc[a] = "idle"
              /\ pc' = [pc EXCEPT ![a] = "busy"]
              /\ m1' = [m1 EXCEPT ![a] = n]
              /\ m2' = [m2 EXCEPT ![a] = n]
Cross(a, b) == /\ a # b
               /\ UNCHANGED pc
               /\ m1' = [m1 EXCEPT ![a] = 1]
               /\ m2' = [m2 EXCEPT ![b] = 1]
Finish(a) == /\ pc[a] = "busy" /\ m1[a] + m2[a] >= 0
             /\ pc' = [pc EXCEPT ![a] = "idle"] /\ UNCHANGED <<m1, m2>>
Next == (\E a \in {1, 2}: Start(a) \/ Finish(a)) \/ (\E a, b \in {1, 2}: Cross(a, b))
Inv == pc \in [{1, 2} -> {"idle", "busy"}]
"#;
    assert!(projection(mismatched_companions).is_empty());

    // Singleton-only dead field or companion is refused (zero state reduction).
    assert!(projection(&BODY.replace("n \\in {0, 1}", "n \\in {0}")).is_empty());
    assert!(projection(&scalar_comp.replace("n \\in {0, 1, 2}", "n \\in {0}")).is_empty());

    // Un-overwritten dead-to-live transition is refused.
    let unoverwritten = scalar_comp
        .replace("Next == Start \\/ Finish", "Next == Start \\/ Finish \\/ (pc = \"idle\" /\\ pc' = \"busy\" /\\ UNCHANGED buf)");
    assert!(projection(&unoverwritten).is_empty());

    // Action property `[A]_sub` mentioning a projected companion refuses projection.
    let dir = tlx_testkit::TempDir::new("phase-sema-action-sub");
    let spec_src = format!(
        "---- MODULE Phase ----\nEXTENDS Integers\n{scalar_comp}\nActProp == [][pc' = pc \\/ pc' = \"busy\" \\/ pc' = \"idle\"]_<<pc, buf>>\n====\n"
    );
    let path = dir.write("Phase.tla", &spec_src);
    let mut p = Program::load(&path, &[]).unwrap();
    p.resolve_all_root();
    let [init, next, inv, act_prop] = ["Init", "Next", "Inv", "ActProp"].map(|name| {
        let Some(RootSymbol::Def(id)) = p.lookup_root(name) else { panic!("missing {name}") };
        Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p.defs[id.idx()].span)
    });
    let cfg = parse_cfg("INIT Init\nNEXT Next\nINVARIANT Inv\nPROPERTY ActProp\n").unwrap();
    let invs = [inv];
    let action_props = [act_prop];
    let spec = tlx_sema::optimize::CheckSpec { invariants: &invs, action_props: &action_props, ..Default::default() };
    assert!(tlx_sema::optimize::phase_projection_with_spec(&p, &cfg, &init, &next, spec).is_none());

    // Action constraint reading `DOMAIN buf` on a fixed-domain parallel map uses
    // the shared action-read classifier and keeps `buf[*]` certifiable.
    let dir_dom = tlx_testkit::TempDir::new("phase-sema-action-domain");
    let dom_src = r#"---- MODULE Phase ----
EXTENDS Integers
VARIABLES pc, buf
Init == pc = [k \in {1, 2} |-> "idle"] /\ buf = [k \in {1, 2} |-> 0]
Start(k) == \E n \in {0, 1, 2}: pc[k] = "idle" /\ pc' = [pc EXCEPT ![k] = "busy"] /\ buf' = [buf EXCEPT ![k] = n]
Finish(k) == pc[k] = "busy" /\ buf[k] >= 0 /\ pc' = [pc EXCEPT ![k] = "idle"] /\ UNCHANGED buf
Next == \E k \in {1, 2}: Start(k) \/ Finish(k)
Inv == pc \in [{1, 2} -> {"idle", "busy"}] /\ (\A k \in {1, 2}: pc[k] = "busy" => buf[k] \in {0, 1, 2})
ActDom == DOMAIN buf = {1, 2}
====
"#;
    let path_dom = dir_dom.write("Phase.tla", dom_src);
    let mut p_dom = Program::load(&path_dom, &[]).unwrap();
    p_dom.resolve_all_root();
    let [init_d, next_d, inv_d, act_dom] = ["Init", "Next", "Inv", "ActDom"].map(|name| {
        let Some(RootSymbol::Def(id)) = p_dom.lookup_root(name) else { panic!("missing {name}") };
        Expr::new(ExprKind::Apply { op: OpRef::Def(id), args: vec![] }, p_dom.defs[id.idx()].span)
    });
    let cfg_dom = parse_cfg("INIT Init\nNEXT Next\nINVARIANT Inv\nACTION_CONSTRAINT ActDom\n").unwrap();
    let invs_d = [inv_d];
    let act_cons = [act_dom];
    let spec_d = tlx_sema::optimize::CheckSpec { invariants: &invs_d, action_constraints: &act_cons, ..Default::default() };
    let proj_d = tlx_sema::optimize::phase_projection_with_spec(&p_dom, &cfg_dom, &init_d, &next_d, spec_d)
        .expect("DOMAIN buf in ACTION_CONSTRAINT must not drop parallel companion");
    assert_eq!(proj_d.fields, vec!["buf[*]"]);
    assert!(proj_d.certificate.is_some());

    // Provable empty-set (`Set(Bottom)`) and empty-sequence (`Seq(Bottom)`)
    // singleton companions are refused in both scalar and map forms.
    for (label, init_v, check_v) in [("empty-set", "{}", "buf = {}"), ("empty-seq", "<<>>", "buf = <<>>")] {
        let empty_scalar = format!(
            r#"VARIABLES pc, buf
Init == pc = "idle" /\ buf = {init_v}
Start == pc = "idle" /\ pc' = "busy" /\ buf' = {init_v}
Finish == pc = "busy" /\ {check_v} /\ pc' = "idle" /\ UNCHANGED buf
Next == Start \/ Finish
Inv == pc \in {{"idle", "busy"}}"#
        );
        assert!(projection(&empty_scalar).is_empty(), "{label} scalar singleton must be refused");
    }
    for (label, init_v, check_v) in [("empty-set-map", "{}", "buf[k] = {}"), ("empty-seq-map", "<<>>", "buf[k] = <<>>")] {
        let empty_map = format!(
            r#"VARIABLES pc, buf
Init == pc = [k \in {{1, 2}} |-> "idle"] /\ buf = [k \in {{1, 2}} |-> {init_v}]
Start(k) == pc[k] = "idle" /\ pc' = [pc EXCEPT ![k] = "busy"] /\ buf' = [buf EXCEPT ![k] = {init_v}]
Finish(k) == pc[k] = "busy" /\ {check_v} /\ pc' = [pc EXCEPT ![k] = "idle"] /\ UNCHANGED buf
Next == \E k \in {{1, 2}}: Start(k) \/ Finish(k)
Inv == pc \in [{{1, 2}} -> {{"idle", "busy"}}]"#
        );
        assert!(projection(&empty_map).is_empty(), "{label} map singleton must be refused");
    }
}
