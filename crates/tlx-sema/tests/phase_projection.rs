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
        BODY.replace("r' = [r EXCEPT !.mode = \"idle\"]", "r' = [mode |-> \"idle\", data |-> r.data]"),
    ] {
        assert!(projection(&body).is_empty(), "{body}");
    }
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
