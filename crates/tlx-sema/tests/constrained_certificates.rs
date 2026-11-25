//! Connected constrained-certificate tests across all rule families and refusal gates.

use tlx_front::cfg::{parse_cfg, Config};
use tlx_sema::{
    hir::{DefKind, Expr},
    optimize::{
        age_projection_with_spec, cfg_constants_supported, choose_symmetry_certificate_with_spec, equiv_symmetry_certificate_with_spec,
        history_projection_with_spec, ordered_projection_with_spec, phase_projection_with_spec, sequence_length_projection_with_spec,
        symmetry_certificate_with_spec, symmetry_projection_certificate_with_spec, unobserved_projection_with_spec, CheckSpec,
        FieldProjection,
    },
    Program,
};

fn load(name: &str, tla: &str, cfg_src: &str) -> (Program, Config) {
    let dir = tlx_testkit::TempDir::with_spec(name, tla, cfg_src);
    let program = Program::load(&dir.join(format!("{name}.tla")), &[]).unwrap();
    let cfg = parse_cfg(cfg_src).unwrap();
    (program, cfg)
}

fn def_expr(program: &Program, name: &str) -> Expr {
    let def = program.defs.iter().find(|d| &*d.name == name).unwrap_or_else(|| panic!("missing def {name}"));
    let DefKind::Op(e) = &def.kind else { panic!("{name} is not an operator") };
    e.clone()
}

/// Mirror `tlx_eval::model::spec::classify`: unwrap outer `[]` from `[][A]_sub`.
fn action_prop_expr(program: &Program, name: &str) -> Expr {
    let e = def_expr(program, name);
    match &*e.kind {
        tlx_sema::hir::ExprKind::Builtin { op: tlx_sema::builtins::Builtin::Always, args } if args.len() == 1 => args[0].clone(),
        _ => e,
    }
}

fn assert_constrained_lean(cert: &str, namespace: &str) {
    assert!(cert.contains(&format!("namespace TlxOptimization.{namespace}\n")), "missing namespace {namespace}");
    assert!(cert.contains("def constrainedAfter := (model sem).constrainedReduced"));
    assert!(cert.contains("theorem constrained_certificate :"));
    assert!(cert.contains("theorem constrained_optimization_correct :"));
    assert!(cert.contains("theorem constrained_init_counterexample_lifts"));
    assert!(cert.contains("theorem constrained_step_counterexample_lifts"));
    assert!(cert.contains("theorem admitted_deadlock_preserved"));
    assert!(cert.contains("#print axioms constrained_certificate"));
    assert!(!cert.contains("sorry"));
}

fn node_groups() -> Vec<Vec<String>> {
    vec![vec!["n1".into(), "n2".into(), "n3".into()]]
}

fn fixture_keyed_constrained() -> String {
    let tla = r#"---- MODULE KeyedConstrained ----
EXTENDS Naturals
CONSTANT Nodes, Limit, n1, n2, n3
VARIABLE state, count
DefaultNodes == {n1, n2, n3}
DefaultLimit == 3
Init == state = [n \in Nodes |-> 0] /\ count = 0
Next == /\ \E n \in Nodes :
            /\ state' = [state EXCEPT ![n] = (@ + 1) % 2]
            /\ count' = IF count < Limit THEN count + 1 ELSE count
Inv == count <= Limit /\ \A n \in Nodes : state[n] \in {0, 1}
InitProp == count = 0
StateLimit == count < Limit
ActLimit == count' >= count
ActProp == [][count' >= count]_<<state, count>>
====
"#;
    let cfg_src = "INIT Init\nNEXT Next\nCONSTANTS\n  n1 = n1\n  n2 = n2\n  n3 = n3\n  Nodes <- DefaultNodes\n  Limit <- DefaultLimit\nINVARIANT Inv\nCONSTRAINT StateLimit\nACTION_CONSTRAINT ActLimit\n";
    let (p, cfg) = load("KeyedConstrained", tla, cfg_src);
    assert!(cfg_constants_supported(&p, &cfg));
    let (inv, ip, c, ac, ap) = (
        [def_expr(&p, "Inv")],
        [def_expr(&p, "InitProp")],
        [def_expr(&p, "StateLimit")],
        [def_expr(&p, "ActLimit")],
        [action_prop_expr(&p, "ActProp")],
    );
    let spec = CheckSpec { invariants: &inv, init_props: &ip, constraints: &c, action_constraints: &ac, action_props: &ap };
    symmetry_certificate_with_spec(&p, &cfg, &def_expr(&p, "Init"), &def_expr(&p, "Next"), spec, &node_groups())
        .expect("keyed symmetry should certify constrained model with const subst")
}

fn fixture_equiv_constrained() -> String {
    let tla = r#"---- MODULE EquivConstrained ----
EXTENDS Naturals, Sequences
CONSTANT Nodes
VARIABLE log, count
Init == log = <<>> /\ count = 0
Next == /\ Len(log) < 2
        /\ count < 2
        /\ \E n \in Nodes :
            /\ log' = Append(log, n)
            /\ count' = count + 1
Inv == count \in 0..2
InitProp == Len(log) = 0
StateLimit == count <= 1
ActLimit == count' >= count
ActProp == [][count' >= count]_<<log, count>>
====
"#;
    let (p, cfg) = load("EquivConstrained", tla, "INIT Init\nNEXT Next\nCONSTANT Nodes = {n1, n2, n3}\nINVARIANT Inv\n");
    let (inv, ip, c, ac, ap) = (
        [def_expr(&p, "Inv")],
        [def_expr(&p, "InitProp")],
        [def_expr(&p, "StateLimit")],
        [def_expr(&p, "ActLimit")],
        [action_prop_expr(&p, "ActProp")],
    );
    let spec = CheckSpec { invariants: &inv, init_props: &ip, constraints: &c, action_constraints: &ac, action_props: &ap };
    equiv_symmetry_certificate_with_spec(&p, &cfg, &def_expr(&p, "Init"), &def_expr(&p, "Next"), spec, &node_groups())
        .expect("equiv symmetry should certify constrained model")
}

fn fixture_choose_constrained() -> String {
    let tla = r#"---- MODULE ChooseConstrained ----
EXTENDS Naturals
CONSTANT Nodes
VARIABLE active, done, count
Init == active = {} /\ done = [n \in Nodes |-> FALSE] /\ count = 0
Next == \/ /\ active = {}
           /\ \E n \in Nodes :
                /\ active' = {n}
                /\ UNCHANGED <<done, count>>
        \/ /\ active # {}
           /\ LET p == CHOOSE x \in active : TRUE
              IN /\ done' = [done EXCEPT ![p] = TRUE]
                 /\ active' = {}
                 /\ count' = IF count < 3 THEN count + 1 ELSE count
Inv == count <= 3
InitProp == active = {}
StateLimit == count < 3
ActLimit == count' >= count
ActProp == [][count' >= count]_<<active, done, count>>
====
"#;
    let (p, cfg) = load("ChooseConstrained", tla, "INIT Init\nNEXT Next\nCONSTANT Nodes = {n1, n2, n3}\nINVARIANT Inv\n");
    let (inv, ip, c, ac, ap) = (
        [def_expr(&p, "Inv")],
        [def_expr(&p, "InitProp")],
        [def_expr(&p, "StateLimit")],
        [def_expr(&p, "ActLimit")],
        [action_prop_expr(&p, "ActProp")],
    );
    let spec = CheckSpec { invariants: &inv, init_props: &ip, constraints: &c, action_constraints: &ac, action_props: &ap };
    choose_symmetry_certificate_with_spec(&p, &cfg, &def_expr(&p, "Init"), &def_expr(&p, "Next"), spec, &node_groups())
        .expect("choose symmetry should certify constrained model")
}

fn fixture_erased_constrained() -> (Program, Config, FieldProjection, String) {
    let tla = r#"---- MODULE ErasedConstrained ----
EXTENDS Naturals
CONSTANT Nodes
VARIABLE state, tag
Init == state = [n \in Nodes |-> 0] /\ tag = 0
Next == \E n \in Nodes :
          /\ state' = [state EXCEPT ![n] = 1 - @]
          /\ tag' = 1
Inv == \A n \in Nodes : state[n] \in {0, 1}
InitProp == \A n \in Nodes : state[n] = 0
StateLimit == \E n \in Nodes : state[n] \in {0, 1}
ActLimit == \E n \in Nodes : state'[n] \in {0, 1}
ActPropSafe == [][\A n \in Nodes : state'[n] \in {0, 1}]_state
ActPropMentionsTag == [][\A n \in Nodes : state'[n] \in {0, 1}]_<<state, tag>>
====
"#;
    let (p, cfg) = load("ErasedConstrained", tla, "INIT Init\nNEXT Next\nCONSTANT Nodes = {n1, n2, n3}\nINVARIANT Inv\n");
    let (inv, ip, c, ac, ap) = (
        [def_expr(&p, "Inv")],
        [def_expr(&p, "InitProp")],
        [def_expr(&p, "StateLimit")],
        [def_expr(&p, "ActLimit")],
        [action_prop_expr(&p, "ActPropSafe")],
    );
    let spec = CheckSpec { invariants: &inv, init_props: &ip, constraints: &c, action_constraints: &ac, action_props: &ap };
    let proj = unobserved_projection_with_spec(&p, &cfg, &def_expr(&p, "Init"), &def_expr(&p, "Next"), spec)
        .expect("erasure should drop tag when [][A]_state does not mention tag");
    let composed =
        symmetry_projection_certificate_with_spec(&p, &cfg, &def_expr(&p, "Init"), &def_expr(&p, "Next"), spec, &node_groups(), &proj.view)
            .expect("erased keyed symmetry should compose with constrained erasure");
    (p, cfg, proj, composed)
}

fn fixture_erased_equiv_constrained() -> (Program, Config, FieldProjection, String) {
    let tla = r#"---- MODULE ErasedEquivConstrained ----
EXTENDS Naturals, FiniteSets
CONSTANT Nodes, Cap, n1, n2, n3
DefaultNodes == {n1, n2, n3}
DefaultCap == 2
VARIABLE msgs, audit
Init == msgs = {} /\ audit = [kind |-> "init", count |-> 0]
Next == \E p, q \in Nodes :
          /\ p # q
          /\ Cardinality(msgs) < Cap
          /\ [src |-> p, dst |-> q] \notin msgs
          /\ msgs' = msgs \cup {[src |-> p, dst |-> q]}
          /\ audit' = [kind |-> "send", count |-> Cardinality(msgs)]
Inv == Cardinality(msgs) <= Cap
InitProp == msgs = {}
StateLimit == Cardinality(msgs) < Cap
ActLimit == Cardinality(msgs') >= Cardinality(msgs)
ActPropSafe == [][Cardinality(msgs') >= Cardinality(msgs)]_msgs
ActPropMentionsAudit == [][Cardinality(msgs') >= Cardinality(msgs)]_<<msgs, audit>>
====
"#;
    let cfg_src =
        "INIT Init\nNEXT Next\nCONSTANTS\n  n1 = n1\n  n2 = n2\n  n3 = n3\n  Nodes <- DefaultNodes\n  Cap <- DefaultCap\nINVARIANT Inv\n";
    let (p, cfg) = load("ErasedEquivConstrained", tla, cfg_src);
    assert!(cfg_constants_supported(&p, &cfg));
    let (inv, ip, c, ac, ap) = (
        [def_expr(&p, "Inv")],
        [def_expr(&p, "InitProp")],
        [def_expr(&p, "StateLimit")],
        [def_expr(&p, "ActLimit")],
        [action_prop_expr(&p, "ActPropSafe")],
    );
    let spec = CheckSpec { invariants: &inv, init_props: &ip, constraints: &c, action_constraints: &ac, action_props: &ap };
    let proj = unobserved_projection_with_spec(&p, &cfg, &def_expr(&p, "Init"), &def_expr(&p, "Next"), spec)
        .expect("erasure should drop structured audit when [][A]_msgs does not mention audit");
    let composed =
        symmetry_projection_certificate_with_spec(&p, &cfg, &def_expr(&p, "Init"), &def_expr(&p, "Next"), spec, &node_groups(), &proj.view)
            .expect("erased equiv symmetry should compose with constrained erasure");
    (p, cfg, proj, composed)
}

fn fixture_field_constrained() -> (Program, Config, FieldProjection) {
    let tla = r#"---- MODULE FieldConstrained ----
EXTENDS Naturals
VARIABLE r
Init == r = [pc |-> "idle", buf |-> 0]
Next == \/ /\ r.pc = "idle"
           /\ \E v \in {1, 2} : r' = [r EXCEPT !.pc = "busy", !.buf = v]
        \/ /\ r.pc = "busy"
           /\ r.buf > 0
           /\ r' = [r EXCEPT !.pc = "idle"]
Inv == r.pc \in {"idle", "busy"}
StateLimit == r.pc \in {"idle", "busy"}
ConstraintReadsBuf == r.buf <= 2
ActLimit == r'.pc \in {"idle", "busy"}
====
"#;
    let (p, cfg) = load("FieldConstrained", tla, "INIT Init\nNEXT Next\nINVARIANT Inv\n");
    let (inv, lim) = ([def_expr(&p, "Inv")], [def_expr(&p, "StateLimit")]);
    let proj = phase_projection_with_spec(
        &p,
        &cfg,
        &def_expr(&p, "Init"),
        &def_expr(&p, "Next"),
        CheckSpec { invariants: &inv, constraints: &lim, ..CheckSpec::default() },
    )
    .expect("field projection with state CONSTRAINT");
    (p, cfg, proj)
}

fn fixture_sequence_constrained() -> (Program, Config, FieldProjection) {
    let tla = r#"---- MODULE SeqConstrained ----
EXTENDS Naturals, Sequences
VARIABLE s
Init == s = <<>>
Next == Len(s) < 3 /\ \E v \in {1, 2} : s' = Append(s, v)
Inv == s \in Seq({1, 2})
StateLimit == Len(s) <= 2
ActLimit == Len(s') >= Len(s)
====
"#;
    let (p, cfg) = load("SeqConstrained", tla, "INIT Init\nNEXT Next\nINVARIANT Inv\n");
    let (inv, lim) = ([def_expr(&p, "Inv")], [def_expr(&p, "StateLimit")]);
    let proj = sequence_length_projection_with_spec(
        &p,
        &cfg,
        &def_expr(&p, "Init"),
        &def_expr(&p, "Next"),
        CheckSpec { invariants: &inv, constraints: &lim, ..CheckSpec::default() },
    )
    .expect("sequence length projection with state CONSTRAINT");
    (p, cfg, proj)
}

fn fixture_history_constrained() -> String {
    let tla = r#"---- MODULE HistConstrained ----
EXTENDS Naturals, Sequences
VARIABLE h, x
Init == h = <<0>> /\ x = 0
Next == x' = 1 - x /\ h' = IF x = 0 THEN Append(h, x) ELSE <<x>>
Inv == h \in Seq({0, 1}) /\ x \in {0, 1}
StateLimit == \A i \in 1..Len(h) : h[i] = 0 \/ h[i] = 1
====
"#;
    let (p, cfg) = load("HistConstrained", tla, "INIT Init\nNEXT Next\nINVARIANT Inv\n");
    let (inv, lim) = ([def_expr(&p, "Inv")], [def_expr(&p, "StateLimit")]);
    history_projection_with_spec(
        &p,
        &cfg,
        &def_expr(&p, "Init"),
        &def_expr(&p, "Next"),
        CheckSpec { invariants: &inv, constraints: &lim, ..CheckSpec::default() },
    )
    .expect("history projection with monitor in CONSTRAINT")
    .certificate
    .unwrap()
}

fn fixture_age_constrained() -> FieldProjection {
    let tla = r#"---- MODULE AgeConstrained ----
EXTENDS Naturals
VARIABLE clock, rec
Init == clock = 0 /\ rec = [k \in {1} |-> [created |-> 0, ok |-> TRUE]]
Next == \/ /\ clock' = clock + 1 /\ UNCHANGED rec
        \/ /\ rec[1].created + 1 <= clock
           /\ rec' = [rec EXCEPT ![1] = [created |-> clock, ok |-> TRUE]]
           /\ UNCHANGED clock
Inv == clock \in Nat /\ rec \in [{1} -> [created: Nat, ok: BOOLEAN]]
StateLimit == rec[1].created + 2 >= clock
====
"#;
    let (p, cfg) = load("AgeConstrained", tla, "INIT Init\nNEXT Next\nINVARIANT Inv\n");
    let (inv, lim) = ([def_expr(&p, "Inv")], [def_expr(&p, "StateLimit")]);
    age_projection_with_spec(
        &p,
        &cfg,
        &def_expr(&p, "Init"),
        &def_expr(&p, "Next"),
        CheckSpec { invariants: &inv, constraints: &lim, ..CheckSpec::default() },
    )
    .expect("age projection with deadline in CONSTRAINT")
}

fn fixture_ordered_constrained() -> String {
    let tla = r#"---- MODULE OrdConstrained ----
EXTENDS Naturals
CONSTANT Step
VARIABLE frontier, bit
DefaultStep == 1
Init == frontier = 1 /\ bit = FALSE
Next == frontier' = frontier + Step /\ bit' = IF frontier = 1 THEN bit ELSE ~bit
Inv == frontier \in Nat /\ bit \in BOOLEAN
StateLimit == bit \in BOOLEAN
====
"#;
    let (p, cfg) = load("OrdConstrained", tla, "INIT Init\nNEXT Next\nCONSTANT Step <- DefaultStep\nINVARIANT Inv\n");
    let (inv, lim) = ([def_expr(&p, "Inv")], [def_expr(&p, "StateLimit")]);
    ordered_projection_with_spec(
        &p,
        &cfg,
        &def_expr(&p, "Init"),
        &def_expr(&p, "Next"),
        CheckSpec { invariants: &inv, constraints: &lim, ..CheckSpec::default() },
    )
    .expect("ordered projection with CONSTANT <- and CONSTRAINT")
    .certificate
    .unwrap()
}

fn fixture_age_history_constrained() -> String {
    let tla = include_str!("../../../proofs/age/AgeHistory.tla")
        .replace("====", "Lim == \\A k \\in {1} : records[k] = Empty \\/ records[k].created + 3 >= clock\n====");
    let (p, cfg) = load("AgeHistory", &tla, "INIT Init\nNEXT Next\nINVARIANT Inv\n");
    let inv = [def_expr(&p, "Inv"), def_expr(&p, "Past"), def_expr(&p, "Ordered")];
    let lim = [def_expr(&p, "Lim")];
    age_projection_with_spec(
        &p,
        &cfg,
        &def_expr(&p, "Init"),
        &def_expr(&p, "Next"),
        CheckSpec { invariants: &inv, constraints: &lim, ..CheckSpec::default() },
    )
    .expect("age-history projection with state CONSTRAINT")
    .certificate
    .unwrap()
}

fn fixture_nested_constrained() -> String {
    let tla = include_str!("../../../proofs/ordered/Nested.tla")
        .replace("CONSTANT Actors", "CONSTANT Actors, a1, a2\nDefaultActors == {a1, a2}")
        .replace(
            "=============================================================================",
            "Lim == \\A a \\in Actors : records[a].ready \\in BOOLEAN\n=============================================================================",
        );
    let cfg_src = "INIT Init\nNEXT Next\nCONSTANTS\n  a1 = a1\n  a2 = a2\n  Actors <- DefaultActors\nINVARIANT Inv\n";
    let (p, cfg) = load("Nested", &tla, cfg_src);
    let (inv, lim) = ([def_expr(&p, "Inv")], [def_expr(&p, "Lim")]);
    ordered_projection_with_spec(
        &p,
        &cfg,
        &def_expr(&p, "Init"),
        &def_expr(&p, "Next"),
        CheckSpec { invariants: &inv, constraints: &lim, ..CheckSpec::default() },
    )
    .expect("nested projection with CONSTANT <- and CONSTRAINT")
    .certificate
    .unwrap()
}

fn fixture_live_constrained() -> String {
    let tla = include_str!("../../../proofs/ordered/LiveVersions.tla").replace(
        "=============================================================================",
        "Lim == observed \\in BOOLEAN\n=============================================================================",
    );
    let (p, cfg) = load("LiveVersions", &tla, "INIT Init\nNEXT Next\nCONSTANT Actors = {a1, a2}\nINVARIANT Inv\n");
    let (inv, lim) = ([def_expr(&p, "Inv")], [def_expr(&p, "Lim")]);
    ordered_projection_with_spec(
        &p,
        &cfg,
        &def_expr(&p, "Init"),
        &def_expr(&p, "Next"),
        CheckSpec { invariants: &inv, constraints: &lim, ..CheckSpec::default() },
    )
    .expect("live versions projection with CONSTRAINT")
    .certificate
    .unwrap()
}

fn fixture_field_action_certificate() -> String {
    let (p, cfg) = fixture_field_action_constrained();
    let (inv, c, ac, ap) =
        ([def_expr(&p, "Inv")], [def_expr(&p, "StateLimit")], [def_expr(&p, "ActLimit")], [action_prop_expr(&p, "ActProp")]);
    let spec = CheckSpec { invariants: &inv, constraints: &c, action_constraints: &ac, action_props: &ap, ..CheckSpec::default() };
    phase_projection_with_spec(&p, &cfg, &def_expr(&p, "Init"), &def_expr(&p, "Next"), spec)
        .expect("field projection with action checks")
        .certificate
        .unwrap()
}

fn fixture_field_action_constrained() -> (Program, Config) {
    let tla = r#"---- MODULE FieldAction ----
EXTENDS Integers
VARIABLE r, count
Init == r = [pc |-> "idle", buf |-> 0] /\ count = 0
Next == \/ /\ r.pc = "idle"
           /\ \E v \in {1, 2} : /\ r' = [r EXCEPT !.pc = "busy", !.buf = v]
                               /\ count' = count + 1
        \/ /\ r.pc = "busy"
           /\ r.buf > 0
           /\ r' = [r EXCEPT !.pc = "idle"]
           /\ count' = count + 1
Inv == r.pc \in {"idle", "busy"} /\ count <= 2
StateLimit == count <= 2
ActLimit == r.pc = "idle" => r'.pc = "busy"
ActProp == [][ (r.pc = "busy") => (r'.pc = "idle") ]_<<count>>
ActUnsupported == [][ r' = r ]_<<count>>
====
"#;
    load("FieldAction", tla, "INIT Init\nNEXT Next\nINVARIANT Inv\n")
}

fn fixture_ordered_action_constrained() -> String {
    let tla = r#"---- MODULE OrdAction ----
EXTENDS Naturals
VARIABLE frontier, bit
Init == frontier = 1 /\ bit = FALSE
Next == frontier' = frontier + 1 /\ bit' = IF frontier = 1 THEN bit ELSE ~bit
Inv == frontier \in Nat /\ bit \in BOOLEAN
StateLimit == bit \in BOOLEAN
ActLimit == bit' \in BOOLEAN
ActProp == [][ bit' \in BOOLEAN ]_bit
====
"#;
    let (p, cfg) = load("OrdAction", tla, "INIT Init\nNEXT Next\nINVARIANT Inv\n");
    let (inv, c, ac, ap) =
        ([def_expr(&p, "Inv")], [def_expr(&p, "StateLimit")], [def_expr(&p, "ActLimit")], [action_prop_expr(&p, "ActProp")]);
    let spec = CheckSpec { invariants: &inv, constraints: &c, action_constraints: &ac, action_props: &ap, ..CheckSpec::default() };
    ordered_projection_with_spec(&p, &cfg, &def_expr(&p, "Init"), &def_expr(&p, "Next"), spec)
        .expect("ordered projection should certify core-only action checks")
        .certificate
        .unwrap()
}

fn fixture_nested_action_constrained() -> String {
    let tla = include_str!("../../../proofs/ordered/Nested.tla")
        .replace("CONSTANT Actors", "CONSTANT Actors, a1, a2\nDefaultActors == {a1, a2}")
        .replace("VARIABLES frontier, serial, records", "VARIABLES frontier, serial, records, mode")
        .replace("Init == /\\ frontier = 1", "Init == /\\ mode = FALSE\n        /\\ frontier = 1")
        .replace("![a].ready = TRUE]", "![a].ready = TRUE]\n              /\\ mode' = mode")
        .replace("/\\ UNCHANGED <<frontier, serial>>", "/\\ UNCHANGED <<frontier, serial, mode>>")
        .replace(
            "=============================================================================",
            "Lim == mode \\in BOOLEAN\nActLimit == mode' \\in BOOLEAN\nActProp == [][mode' \\in BOOLEAN]_mode\n=============================================================================",
        );
    let cfg_src = "INIT Init\nNEXT Next\nCONSTANTS\n  a1 = a1\n  a2 = a2\n  Actors <- DefaultActors\nINVARIANT Inv\n";
    let (p, cfg) = load("Nested", &tla, cfg_src);
    let (inv, lim, ac, ap) = ([def_expr(&p, "Inv")], [def_expr(&p, "Lim")], [def_expr(&p, "ActLimit")], [action_prop_expr(&p, "ActProp")]);
    let spec = CheckSpec { invariants: &inv, constraints: &lim, action_constraints: &ac, action_props: &ap, ..CheckSpec::default() };
    ordered_projection_with_spec(&p, &cfg, &def_expr(&p, "Init"), &def_expr(&p, "Next"), spec)
        .expect("nested projection should certify retained-only action checks")
        .certificate
        .unwrap()
}

fn fixture_live_action_constrained() -> String {
    let tla = include_str!("../../../proofs/ordered/LiveVersions.tla")
        .replace("VARIABLES frontier, held, versions, flag, observed", "VARIABLES frontier, held, versions, flag, observed, mode")
        .replace("Init == /\\ frontier = 1", "Init == /\\ mode = FALSE\n        /\\ frontier = 1")
        .replace("/\\ UNCHANGED <<held, observed>>", "/\\ UNCHANGED <<held, observed, mode>>")
        .replace("/\\ UNCHANGED <<frontier, versions, flag>>", "/\\ UNCHANGED <<frontier, versions, flag, mode>>")
        .replace("/\\ UNCHANGED <<frontier, versions, flag, observed>>", "/\\ UNCHANGED <<frontier, versions, flag, observed, mode>>")
        .replace(
            "=============================================================================",
            "Lim == mode \\in BOOLEAN\nActLimit == mode' \\in BOOLEAN\nActProp == [][mode' \\in BOOLEAN]_mode\n=============================================================================",
        );
    let cfg_src = "INIT Init\nNEXT Next\nCONSTANT Actors = {a1, a2}\nINVARIANT Inv\n";
    let (p, cfg) = load("LiveVersions", &tla, cfg_src);
    let (inv, lim, ac, ap) = ([def_expr(&p, "Inv")], [def_expr(&p, "Lim")], [def_expr(&p, "ActLimit")], [action_prop_expr(&p, "ActProp")]);
    let spec = CheckSpec { invariants: &inv, constraints: &lim, action_constraints: &ac, action_props: &ap, ..CheckSpec::default() };
    ordered_projection_with_spec(&p, &cfg, &def_expr(&p, "Init"), &def_expr(&p, "Next"), spec)
        .expect("live-version projection should certify retained-only action checks")
        .certificate
        .unwrap()
}

const ACTOR_KEY_TLA: &str = r#"---- MODULE ActKey ----
EXTENDS Naturals
CONSTANT Actors
VARIABLE r, count
Init == r = [k \in Actors |-> [id |-> k, mode |-> "idle", buf |-> 0]] /\ count = 0
Start == \E k \in Actors :
           /\ r[k].mode = "idle"
           /\ r' = [r EXCEPT ![k].mode = "busy", ![k].buf = 1]
           /\ count' = IF count < 1 THEN count + 1 ELSE count
Finish == \E k \in Actors :
            /\ r[k].mode = "busy"
            /\ r[k].buf > 0
            /\ r' = [r EXCEPT ![k].mode = "idle"]
            /\ count' = count
Next == Start \/ Finish
Inv == /\ \A k \in Actors : r[k].mode \in {"idle", "busy"}
       /\ count <= 1
StateLimit == \A k \in Actors : r[k].mode \in {"idle", "busy"} /\ count <= 1
ActTwo == \A i, j \in Actors : r[i].mode = r[j].mode
ActSame == \A i, j \in Actors : r[i].mode = r[i].mode
ActProp == [][ \A i \in Actors : r'[i].mode \in {"idle", "busy"} ]_<<count>>
ActData == \A i, j \in Actors : r[i].id = r[j].id
ActDataSame == \A i, j \in Actors : r[i].id = r[i].id
====
"#;

/// Bound-key locals recorded in the emitted action-check hole descriptions.
fn action_read_keys(cert: &str) -> Vec<u32> {
    let mut keys = Vec::new();
    for line in cert.lines().filter(|l| l.contains("actionConstraint HIR")) {
        for key in line.split("source key").skip(1) {
            let Some(idx) = key.find("LocalId(") else { continue };
            // The Lean string literal escapes the debug text, so the identifier
            // follows the escaped newline and indentation.
            let digits: String = key[idx + 8..].chars().skip_while(|c| !c.is_ascii_digit()).take_while(char::is_ascii_digit).collect();
            if let Ok(id) = digits.parse() {
                keys.push(id);
            }
        }
    }
    keys
}

fn fixture_field_actor_key(constraint: &str) -> Option<String> {
    let (p, cfg) = load("ActKey", ACTOR_KEY_TLA, "INIT Init\nNEXT Next\nCONSTANT Actors = {n1, n2}\nINVARIANT Inv\n");
    let (inv, lim, ac, ap) =
        ([def_expr(&p, "Inv")], [def_expr(&p, "StateLimit")], [def_expr(&p, constraint)], [action_prop_expr(&p, "ActProp")]);
    let spec = CheckSpec { invariants: &inv, constraints: &lim, action_constraints: &ac, action_props: &ap, ..CheckSpec::default() };
    phase_projection_with_spec(&p, &cfg, &def_expr(&p, "Init"), &def_expr(&p, "Next"), spec)
        .expect("keyed field action checks should keep the projection applicable")
        .certificate
}

#[test]
fn field_action_reads_record_the_bound_key() {
    let two = fixture_field_actor_key("ActTwo").expect("two-key action constraint certificate");
    let same = fixture_field_actor_key("ActSame").expect("single-key action constraint certificate");
    assert_constrained_lean(&two, "GeneratedField");
    assert_constrained_lean(&same, "GeneratedField");

    // `r[i].mode = r[j].mode` reads the phase at two different bound keys, while
    // `r[i].mode = r[i].mode` reads the same key twice. The projection retains
    // the field for every key, so both certificates prove the endpoint theorem;
    // only the recorded key distinguishes the generated instance.
    let two_keys = action_read_keys(&two);
    let same_keys = action_read_keys(&same);
    assert_eq!(two_keys.len(), 2, "two-key predicate must record both reads: {two_keys:?}");
    assert_ne!(two_keys[0], two_keys[1], "distinct bound keys must be recorded distinctly: {two_keys:?}");
    assert_eq!(same_keys.len(), 2, "single-key predicate must record both reads: {same_keys:?}");
    assert_eq!(same_keys[0], same_keys[1], "the same bound key must be recorded twice: {same_keys:?}");
    assert_ne!(two_keys, same_keys, "the two predicates must not lower to interchangeable certificates");

    // The primed keyed action property reads the target endpoint's phase map.
    let observe_atoms: Vec<&str> = two.lines().filter(|l| l.contains("actionObserve HIR")).collect();
    assert_eq!(observe_atoms.len(), 1, "the primed action property must lower to one atom");
    let atom = observe_atoms[0];
    assert!(atom.contains("= phase'"), "primed keyed reads must address the target endpoint: {atom:.300}");
    assert!(atom.contains("source key"), "primed keyed reads must record their bound key: {atom:.300}");

    // The same distinction holds for a data field read through the bound key.
    let data_two = fixture_field_actor_key("ActData").expect("two-key data action constraint certificate");
    let data_same = fixture_field_actor_key("ActDataSame").expect("single-key data action constraint certificate");
    let two_data = action_read_keys(&data_two);
    let same_data = action_read_keys(&data_same);
    assert_eq!(two_data.len(), 2, "{two_data:?}");
    assert_ne!(two_data[0], two_data[1], "distinct bound keys must stay distinct on data reads: {two_data:?}");
    assert_eq!(same_data[0], same_data[1], "the same bound key must stay one read: {same_data:?}");
    assert!(data_two.lines().any(|l| l.contains("data field")), "data-field reads keep their slot");
}

const PRIME_SCOPE_TLA: &str = r#"---- MODULE PrimeScope ----
EXTENDS Naturals
CONSTANT Actors
VARIABLE r, idx, count
Init == r = [k \in Actors |-> [id |-> k, mode |-> "idle", buf |-> 0]] /\ idx = 1 /\ count = 0
Start == \E k \in Actors :
           /\ r[k].mode = "idle"
           /\ r' = [r EXCEPT ![k].mode = "busy", ![k].buf = 1]
           /\ UNCHANGED <<idx>>
           /\ count' = IF count < 1 THEN count + 1 ELSE count
Finish == \E k \in Actors :
            /\ r[k].mode = "busy"
            /\ r[k].buf > 0
            /\ r' = [r EXCEPT ![k].mode = "idle"]
            /\ UNCHANGED <<idx>>
            /\ count' = count
Advance == /\ idx = 1
           /\ idx' = 2
           /\ UNCHANGED <<r, count>>
Next == Start \/ Finish \/ Advance
Inv == /\ \A k \in Actors : r[k].mode \in {"idle", "busy"}
       /\ count <= 1
StateLimit == \A k \in Actors : r[k].mode \in {"idle", "busy"} /\ count <= 1
ActOuterKey == r'[idx].id = 1
ActWholeLookup == r[idx]'.id = 1
====
"#;

fn fixture_prime_scope(constraint: &str) -> Option<String> {
    let (p, cfg) = load("PrimeScope", PRIME_SCOPE_TLA, "INIT Init\nNEXT Next\nCONSTANT Actors = {1, 2}\nINVARIANT Inv\n");
    let (inv, lim, ac) = ([def_expr(&p, "Inv")], [def_expr(&p, "StateLimit")], [def_expr(&p, constraint)]);
    let spec = CheckSpec { invariants: &inv, constraints: &lim, action_constraints: &ac, ..CheckSpec::default() };
    phase_projection_with_spec(&p, &cfg, &def_expr(&p, "Init"), &def_expr(&p, "Next"), spec)
        .expect("prime-scoped keyed action checks should keep the projection applicable")
        .certificate
}

#[test]
fn field_action_keys_record_their_prime_scope() {
    // `r'[idx].id` reads the target map at the source index, while
    // `r[idx]'.id` primes the whole lookup and reads the target map at the
    // target index. When `Advance` changes `idx` from 1 to 2 the two
    // predicates disagree, so they must not lower to the same instance.
    let outer = fixture_prime_scope("ActOuterKey").expect("source-key certificate");
    let whole = fixture_prime_scope("ActWholeLookup").expect("whole-lookup certificate");
    assert_constrained_lean(&outer, "GeneratedField");
    assert_constrained_lean(&whole, "GeneratedField");
    let outer_atoms: Vec<&str> = outer.lines().filter(|l| l.contains("actionConstraint HIR")).collect();
    let whole_atoms: Vec<&str> = whole.lines().filter(|l| l.contains("actionConstraint HIR")).collect();
    assert_eq!(outer_atoms.len(), 1, "one action atom");
    assert_eq!(whole_atoms.len(), 1, "one action atom");
    for atom in [outer_atoms[0], whole_atoms[0]] {
        assert!(atom.contains("source key"), "the key is recorded: {atom:.300}");
    }
    assert!(outer_atoms[0].contains("primed=true; key primed=false"), "r'[idx] keeps the source index: {:.300}", outer_atoms[0]);
    assert!(whole_atoms[0].contains("primed=true; key primed=true"), "r[idx]' reads the target index: {:.300}", whole_atoms[0]);
    assert_ne!(outer_atoms[0], whole_atoms[0], "the two prime scopes must not lower to one instance");
}

#[test]
fn field_projection_certifies_action_checks_and_refuses_whole_record_reads() {
    let (p, cfg) = fixture_field_action_constrained();
    let (inv, c, ac, ap) =
        ([def_expr(&p, "Inv")], [def_expr(&p, "StateLimit")], [def_expr(&p, "ActLimit")], [action_prop_expr(&p, "ActProp")]);
    let spec = CheckSpec { invariants: &inv, constraints: &c, action_constraints: &ac, action_props: &ap, ..CheckSpec::default() };
    let proj = phase_projection_with_spec(&p, &cfg, &def_expr(&p, "Init"), &def_expr(&p, "Next"), spec)
        .expect("field projection should certify endpoint action checks");
    assert_eq!(proj.fields, vec!["r.buf".to_string()]);
    let cert = proj.certificate.expect("constrained field certificate");
    assert_constrained_lean(&cert, "GeneratedField");
    assert!(cert.contains("def actionConstraint"));
    assert!(cert.contains("def actionObserve"));
    assert!(cert.contains("actionConstraint := actionConstraint sem"));
    assert!(cert.contains("actionObserve := actionObserve sem"));

    // A whole-record primed read cannot be certified: it would observe the
    // erased buffer value at an arbitrary phase.
    let bad = [action_prop_expr(&p, "ActUnsupported")];
    let bad_spec = CheckSpec { invariants: &inv, constraints: &c, action_constraints: &ac, action_props: &bad, ..CheckSpec::default() };
    assert!(phase_projection_with_spec(&p, &cfg, &def_expr(&p, "Init"), &def_expr(&p, "Next"), bad_spec).is_none());
}

#[test]
fn ordered_nested_and_live_projections_certify_retained_core_action_checks() {
    let ordered = fixture_ordered_action_constrained();
    assert_constrained_lean(&ordered, "GeneratedOrdered");
    assert!(ordered.contains("def actionConstraint"));
    assert!(ordered.contains("sem.actionTest"));
    assert!(ordered.contains("actionObserve := actionObserve sem"));

    let nested = fixture_nested_action_constrained();
    assert_constrained_lean(&nested, "GeneratedNested");
    assert!(nested.contains("def actionConstraint"));
    assert!(nested.contains("actionConstraint := actionConstraint sem"));
    assert!(nested.contains("actionObserve := actionObserve sem"));

    let live = fixture_live_action_constrained();
    assert_constrained_lean(&live, "GeneratedLive");
    assert!(live.contains("def actionConstraint"));
    assert!(live.contains("actionConstraint := actionConstraint sem"));
    assert!(live.contains("actionObserve := actionObserve sem"));
}

fn fixture_erasure_const_nat() -> (Program, Config, String) {
    let tla = r#"---- MODULE ConstSubstNat ----
EXTENDS Naturals
CONSTANT C
VARIABLE x, tag
Init == x = 0 /\ tag = 0
Next == x' = 1 /\ tag' = 1
Inv == x \in {0, 1}
GoodLimit == 1 \in C
BadQuantLimit == \A i \in C : i >= 0
====
"#;
    let (p, cfg) = load("ConstSubstNat", tla, "INIT Init\nNEXT Next\nCONSTANT C <- Nat\nINVARIANT Inv\n");
    let (inv, good) = ([def_expr(&p, "Inv")], [def_expr(&p, "GoodLimit")]);
    let cert = unobserved_projection_with_spec(
        &p,
        &cfg,
        &def_expr(&p, "Init"),
        &def_expr(&p, "Next"),
        CheckSpec { invariants: &inv, constraints: &good, ..CheckSpec::default() },
    )
    .expect("C <- Nat with `1 \\in C` should certify faithfully as Builtin(Nat)")
    .certificate
    .unwrap();
    (p, cfg, cert)
}

fn build_large_bindings_spec(count: usize) -> (Program, Config) {
    let names: Vec<String> = (0..count).map(|i| format!("C{i}")).collect();
    let mut tla = String::from("---- MODULE LargeBindings ----\nEXTENDS Naturals\nCONSTANT ");
    tla.push_str(&names.join(", "));
    tla.push_str(
        "\nVARIABLE x, tag\nSharedPure == 1\nInit == x = 0 /\\ tag = 0\nNext == x' = 1 /\\ tag' = 1\nInv == x \\in {0, 1}\nLim == ",
    );
    tla.push_str(&names.iter().map(|c| format!("{c} = 1")).collect::<Vec<_>>().join(" /\\ "));
    tla.push_str("\n====\n");
    let mut cfg_src = String::from("INIT Init\nNEXT Next\nCONSTANTS\n");
    for c in &names {
        cfg_src.push_str(&format!("  {c} <- SharedPure\n"));
    }
    cfg_src.push_str("INVARIANT Inv\nCONSTRAINT Lim\n");
    load("LargeBindings", &tla, &cfg_src)
}

fn fixture_large_const_subst_512() -> String {
    let (p, cfg) = build_large_bindings_spec(512);
    let (inv, lim) = ([def_expr(&p, "Inv")], [def_expr(&p, "Lim")]);
    unobserved_projection_with_spec(
        &p,
        &cfg,
        &def_expr(&p, "Init"),
        &def_expr(&p, "Next"),
        CheckSpec { invariants: &inv, constraints: &lim, ..CheckSpec::default() },
    )
    .expect("512 constant substitutions should certify with scalable proof")
    .certificate
    .unwrap()
}

fn fixture_marker_strings_in_model_data() -> (String, String) {
    let marker_payload = "def constSubstDeclared (i : Fin ConstSubstCount) : String := | def constSubstExpanded (i : Fin ConstSubstCount) : String := | def constrainedAfter := (model sem).constrainedReduced | def after := (model sem).reduced | (hModel : sys (fun i => eval (constSubstExpanded i)) = before sem) :";
    let uncons_tla = format!(
        "---- MODULE LabelsPlain ----\nEXTENDS Naturals\nVARIABLE x, tag\nInit == x = 0 /\\ tag = {marker_payload:?}\nNext == x' = 1 /\\ tag' = \"step\"\nInv == x \\in {{0, 1}}\n====\n"
    );
    let (p1, c1) = load("LabelsPlain", &uncons_tla, "INIT Init\nNEXT Next\nINVARIANT Inv\n");
    let plain_cert = unobserved_projection_with_spec(
        &p1,
        &c1,
        &def_expr(&p1, "Init"),
        &def_expr(&p1, "Next"),
        CheckSpec::invariants_only(&[def_expr(&p1, "Inv")]),
    )
    .expect("unconstrained erasure with marker text in model data")
    .certificate
    .unwrap();

    let cons_tla = format!(
        "---- MODULE LabelsConstrained ----\nEXTENDS Naturals\nCONSTANT Cap\nVARIABLE x, tag\nTwo == 2\nInit == x = 0 /\\ tag = {marker_payload:?}\nNext == x' = 1 /\\ tag' = \"step\"\nInv == x <= Cap\nLim == x < Cap\n====\n"
    );
    let (p2, c2) = load("LabelsConstrained", &cons_tla, "INIT Init\nNEXT Next\nCONSTANT Cap <- Two\nINVARIANT Inv\nCONSTRAINT Lim\n");
    let (inv2, lim2) = ([def_expr(&p2, "Inv")], [def_expr(&p2, "Lim")]);
    let cons_cert = unobserved_projection_with_spec(
        &p2,
        &c2,
        &def_expr(&p2, "Init"),
        &def_expr(&p2, "Next"),
        CheckSpec { invariants: &inv2, constraints: &lim2, ..CheckSpec::default() },
    )
    .expect("constrained erasure with substitution and marker text in model data")
    .certificate
    .unwrap();
    (plain_cert, cons_cert)
}

#[test]
fn keyed_symmetry_certifies_constraints_actions_init_props_and_const_subst() {
    let cert = fixture_keyed_constrained();
    assert_constrained_lean(&cert, "GeneratedSymmetry");
    assert!(cert.contains("def constSubstDeclared"));
    assert!(cert.contains("def constSubstExpanded"));
    assert!(cert.contains("\"Num(3)\""));
    assert!(!cert.contains("(hSubst :"));
}

#[test]
fn equiv_and_choose_symmetry_certify_constraints_and_action_props() {
    assert_constrained_lean(&fixture_equiv_constrained(), "GeneratedEquivSymmetry");
    assert_constrained_lean(&fixture_choose_constrained(), "GeneratedChooseSymmetry");
}

#[test]
fn erasure_and_erased_keyed_certify_constrained_and_refuse_observed_subscript() {
    let (p, cfg, proj, composed) = fixture_erased_constrained();
    assert_eq!(proj.fields, vec!["tag"]);
    assert_constrained_lean(proj.certificate.as_deref().unwrap(), "GeneratedErasure");
    assert_constrained_lean(&composed, "GeneratedErasedSymmetry");
    assert!(composed.contains("theorem erasure_constrained_certificate :"));

    let (inv, ip, c, ac, ap_bad) = (
        [def_expr(&p, "Inv")],
        [def_expr(&p, "InitProp")],
        [def_expr(&p, "StateLimit")],
        [def_expr(&p, "ActLimit")],
        [action_prop_expr(&p, "ActPropMentionsTag")],
    );
    let bad_spec = CheckSpec { invariants: &inv, init_props: &ip, constraints: &c, action_constraints: &ac, action_props: &ap_bad };
    assert!(unobserved_projection_with_spec(&p, &cfg, &def_expr(&p, "Init"), &def_expr(&p, "Next"), bad_spec).is_none());
    assert!(symmetry_projection_certificate_with_spec(
        &p,
        &cfg,
        &def_expr(&p, "Init"),
        &def_expr(&p, "Next"),
        bad_spec,
        &node_groups(),
        &proj.view,
    )
    .is_none());

    let (ep, ecfg, eproj, ecomposed) = fixture_erased_equiv_constrained();
    assert_eq!(eproj.fields, vec!["audit"]);
    assert_constrained_lean(eproj.certificate.as_deref().unwrap(), "GeneratedErasure");
    assert_constrained_lean(&ecomposed, "GeneratedErasedEquivSymmetry");
    assert!(ecomposed.contains("theorem erasure_constrained_certificate :"));

    let (einv, eip, ec, eac, eap_bad) = (
        [def_expr(&ep, "Inv")],
        [def_expr(&ep, "InitProp")],
        [def_expr(&ep, "StateLimit")],
        [def_expr(&ep, "ActLimit")],
        [action_prop_expr(&ep, "ActPropMentionsAudit")],
    );
    let ebad_spec = CheckSpec { invariants: &einv, init_props: &eip, constraints: &ec, action_constraints: &eac, action_props: &eap_bad };
    assert!(unobserved_projection_with_spec(&ep, &ecfg, &def_expr(&ep, "Init"), &def_expr(&ep, "Next"), ebad_spec).is_none());
    assert!(symmetry_projection_certificate_with_spec(
        &ep,
        &ecfg,
        &def_expr(&ep, "Init"),
        &def_expr(&ep, "Next"),
        ebad_spec,
        &node_groups(),
        &eproj.view,
    )
    .is_none());
}

#[test]
fn state_constraints_certify_and_sequence_projection_still_refuses_action_checks() {
    let (fp, fcfg, field_proj) = fixture_field_constrained();
    assert_constrained_lean(field_proj.certificate.as_deref().unwrap(), "GeneratedField");
    let (finv, reads_buf, fact) = ([def_expr(&fp, "Inv")], [def_expr(&fp, "ConstraintReadsBuf")], [def_expr(&fp, "ActLimit")]);
    assert!(phase_projection_with_spec(
        &fp,
        &fcfg,
        &def_expr(&fp, "Init"),
        &def_expr(&fp, "Next"),
        CheckSpec { invariants: &finv, constraints: &reads_buf, ..CheckSpec::default() },
    )
    .is_none());
    // An endpoint action check over the retained control field is now certified.
    let action_proj = phase_projection_with_spec(
        &fp,
        &fcfg,
        &def_expr(&fp, "Init"),
        &def_expr(&fp, "Next"),
        CheckSpec { invariants: &finv, action_constraints: &fact, ..CheckSpec::default() },
    )
    .expect("field projection with a control-field action constraint");
    let action_cert = action_proj.certificate.as_deref().unwrap();
    assert_constrained_lean(action_cert, "GeneratedField");
    assert!(action_cert.contains("def actionConstraint"));

    let (sp, scfg, seq_proj) = fixture_sequence_constrained();
    assert_constrained_lean(seq_proj.certificate.as_deref().unwrap(), "GeneratedLength");
    let (sinv, sact) = ([def_expr(&sp, "Inv")], [def_expr(&sp, "ActLimit")]);
    assert!(sequence_length_projection_with_spec(
        &sp,
        &scfg,
        &def_expr(&sp, "Init"),
        &def_expr(&sp, "Next"),
        CheckSpec { invariants: &sinv, action_constraints: &sact, ..CheckSpec::default() },
    )
    .is_none());

    assert_constrained_lean(&fixture_history_constrained(), "GeneratedHistory");

    let age_proj = fixture_age_constrained();
    assert!(age_proj.fields.iter().any(|f| f.contains("age<=3")), "CONSTRAINT deadline must raise cap: {:?}", age_proj.fields);
    assert_constrained_lean(age_proj.certificate.as_deref().unwrap(), "GeneratedAge");

    let ord_cert = fixture_ordered_constrained();
    assert_constrained_lean(&ord_cert, "GeneratedOrdered");
    assert!(ord_cert.contains("theorem const_subst_bindings_match"));

    assert_constrained_lean(&fixture_age_history_constrained(), "GeneratedAgeHistory");

    let nested_cert = fixture_nested_constrained();
    assert_constrained_lean(&nested_cert, "GeneratedNested");
    assert!(nested_cert.contains("theorem const_subst_bindings_match"));

    assert_constrained_lean(&fixture_live_constrained(), "GeneratedLive");
}

#[test]
fn refuses_builtin_override_and_impure_unused_const_subst() {
    let override_tla = r#"---- MODULE OverrideRefuse ----
EXTENDS Naturals
CONSTANT Nodes
VARIABLE state
SmallNat == 0..2
Init == state = [n \in Nodes |-> 0]
Next == \E n \in Nodes : state' = [state EXCEPT ![n] = 1 - @]
Inv == \A n \in Nodes : state[n] \in Nat
====
"#;
    let (p, cfg) =
        load("OverrideRefuse", override_tla, "INIT Init\nNEXT Next\nCONSTANTS\n  Nodes = {n1, n2}\n  Nat <- SmallNat\nINVARIANT Inv\n");
    assert!(!cfg_constants_supported(&p, &cfg));
    assert!(symmetry_certificate_with_spec(
        &p,
        &cfg,
        &def_expr(&p, "Init"),
        &def_expr(&p, "Next"),
        CheckSpec::invariants_only(&[def_expr(&p, "Inv")]),
        &[vec!["n1".into(), "n2".into()]],
    )
    .is_none());

    let effect_tla = r#"---- MODULE UnusedEffectSubst ----
EXTENDS Naturals, TLC
CONSTANT C
VARIABLE x, tag
DoPrint == PrintT("binding")
Wrapper == DoPrint
PureHelper(n) == n + 1
PureWrapper == PureHelper(1)
Init == x = 0 /\ tag = 0
Next == x' = 1 /\ tag' = 1
Inv == x \in {0, 1}
====
"#;
    for target in ["DoPrint", "Wrapper"] {
        let cfg_src = format!("INIT Init\nNEXT Next\nCONSTANT C <- {target}\nINVARIANT Inv\n");
        let (p, cfg) = load("UnusedEffectSubst", effect_tla, &cfg_src);
        assert!(!cfg_constants_supported(&p, &cfg), "{target} must be rejected as impure");
        assert!(unobserved_projection_with_spec(
            &p,
            &cfg,
            &def_expr(&p, "Init"),
            &def_expr(&p, "Next"),
            CheckSpec::invariants_only(&[def_expr(&p, "Inv")]),
        )
        .is_none());
    }
    let (p, cfg) = load("UnusedEffectSubst", effect_tla, "INIT Init\nNEXT Next\nCONSTANT C <- PureWrapper\nINVARIANT Inv\n");
    assert!(cfg_constants_supported(&p, &cfg), "PureWrapper must be accepted as pure");
    let proj = unobserved_projection_with_spec(
        &p,
        &cfg,
        &def_expr(&p, "Init"),
        &def_expr(&p, "Next"),
        CheckSpec::invariants_only(&[def_expr(&p, "Inv")]),
    )
    .expect("pure unused substitution target should still certify erasure");
    assert_eq!(proj.fields, vec!["tag"]);
}

#[test]
fn refuses_partial_symmetry_and_erasure_observations() {
    let partial_tla = r#"---- MODULE PartialConstraint ----
EXTENDS Naturals
CONSTANT Nodes
VARIABLE state, d
Init == state = [n \in Nodes |-> 0] /\ d = 0
Next == \E n \in Nodes : state' = [state EXCEPT ![n] = 1 - @] /\ d' \in {0, 1}
Inv == \A n \in Nodes : state[n] \in {0, 1}
BadConstraint == \A n \in Nodes : (state[n] \div d) >= 0
BadActionConstraint == \A n \in Nodes : (state'[n] \div d') >= 0
====
"#;
    let (p, cfg) = load("PartialConstraint", partial_tla, "INIT Init\nNEXT Next\nCONSTANT Nodes = {n1, n2}\nINVARIANT Inv\n");
    let (inv, bad_c, bad_ac) = ([def_expr(&p, "Inv")], [def_expr(&p, "BadConstraint")], [def_expr(&p, "BadActionConstraint")]);
    let groups = vec![vec!["n1".into(), "n2".into()]];
    for spec in [
        CheckSpec { invariants: &inv, constraints: &bad_c, ..CheckSpec::default() },
        CheckSpec { invariants: &inv, action_constraints: &bad_ac, ..CheckSpec::default() },
    ] {
        assert!(symmetry_certificate_with_spec(&p, &cfg, &def_expr(&p, "Init"), &def_expr(&p, "Next"), spec, &groups).is_none());
    }

    let erase_partial_tla = r#"---- MODULE ErasePartial ----
EXTENDS Naturals
VARIABLE x, tag
Init == x = 0 /\ tag = 0
Next == x' \in {0, 1} /\ tag' = 1
Inv == x \in {0, 1}
BadLimit == \A i \in {0} : (x \div i) >= 0
BadInitProp == \A i \in {0} : (x \div i) >= 0
BadActLimitDivZero == \A i \in {0} : (x' \div i) >= 0
BadActLimitPrimed == (1 \div x') >= 0
BadActProp == [][(1 \div x') >= 0]_x
====
"#;
    let (p, cfg) = load("ErasePartial", erase_partial_tla, "INIT Init\nNEXT Next\nINVARIANT Inv\n");
    let inv = [def_expr(&p, "Inv")];
    let bad_lim = [def_expr(&p, "BadLimit")];
    let bad_ip = [def_expr(&p, "BadInitProp")];
    let bad_ac1 = [def_expr(&p, "BadActLimitDivZero")];
    let bad_ac2 = [def_expr(&p, "BadActLimitPrimed")];
    let bad_ap = [action_prop_expr(&p, "BadActProp")];
    for spec in [
        CheckSpec { invariants: &inv, constraints: &bad_lim, ..CheckSpec::default() },
        CheckSpec { invariants: &inv, init_props: &bad_ip, ..CheckSpec::default() },
        CheckSpec { invariants: &inv, action_constraints: &bad_ac1, ..CheckSpec::default() },
        CheckSpec { invariants: &inv, action_constraints: &bad_ac2, ..CheckSpec::default() },
        CheckSpec { invariants: &inv, action_props: &bad_ap, ..CheckSpec::default() },
    ] {
        assert!(unobserved_projection_with_spec(&p, &cfg, &def_expr(&p, "Init"), &def_expr(&p, "Next"), spec).is_none());
    }
}

#[test]
fn refuses_partial_and_overflowing_state_projection_constraints() {
    type ProjFn = fn(&Program, &Config, &Expr, &Expr, CheckSpec<'_>) -> Option<FieldProjection>;
    let cases: [(&str, &str, ProjFn); 7] = [
        (
            "SeqPartial",
            "---- MODULE SeqPartial ----\nEXTENDS Naturals, Sequences\nVARIABLE s\nInit == s = <<>>\nNext == Len(s) < 3 /\\ \\E v \\in {1, 2} : s' = Append(s, v)\nInv == s \\in Seq({1, 2})\nLimit == \\A i \\in {0} : (Len(s) \\div i) >= 0\n====\n",
            sequence_length_projection_with_spec,
        ),
        (
            "FieldPartial",
            "---- MODULE FieldPartial ----\nEXTENDS Naturals\nVARIABLE r\nInit == r = [pc |-> \"idle\", buf |-> 0]\nNext == (r.pc = \"idle\" /\\ \\E v \\in {1, 2} : r' = [r EXCEPT !.pc = \"busy\", !.buf = v]) \\/ (r.pc = \"busy\" /\\ r' = [r EXCEPT !.pc = \"idle\"])\nInv == r.pc \\in {\"idle\", \"busy\"}\nLimit == \\A i \\in {0} : (1 \\div i) >= 0\n====\n",
            phase_projection_with_spec,
        ),
        (
            "HistPartial",
            "---- MODULE HistPartial ----\nEXTENDS Naturals, Sequences\nVARIABLE h, x\nInit == h = <<0>> /\\ x = 0\nNext == x' = 1 - x /\\ h' = IF x = 0 THEN Append(h, x) ELSE <<x>>\nInv == h \\in Seq({0, 1}) /\\ x \\in {0, 1}\nLimit == \\A i \\in {0} : (Len(h) \\div i) >= 0\n====\n",
            history_projection_with_spec,
        ),
        (
            "AgePartial",
            "---- MODULE AgePartial ----\nEXTENDS Naturals\nVARIABLE clock, rec\nInit == clock = 0 /\\ rec = [k \\in {1} |-> [created |-> 0, ok |-> TRUE]]\nNext == (clock' = clock + 1 /\\ UNCHANGED rec) \\/ (rec[1].created + 1 <= clock /\\ rec' = [rec EXCEPT ![1] = [created |-> clock, ok |-> TRUE]] /\\ UNCHANGED clock)\nInv == clock \\in Nat /\\ rec \\in [{1} -> [created: Nat, ok: BOOLEAN]]\nLimit == \\A i \\in {0} : (clock \\div i) >= 0\n====\n",
            age_projection_with_spec,
        ),
        (
            "OrdPartial",
            "---- MODULE OrdPartial ----\nEXTENDS Naturals\nVARIABLE frontier, bit\nInit == frontier = 1 /\\ bit = FALSE\nNext == frontier' = frontier + 1 /\\ bit' = IF frontier = 1 THEN bit ELSE ~bit\nInv == frontier \\in Nat /\\ bit \\in BOOLEAN\nLimit == \\A i \\in {0} : (frontier \\div i) >= 0\n====\n",
            ordered_projection_with_spec,
        ),
        (
            "SeqOverflow",
            "---- MODULE SeqOverflow ----\nEXTENDS Naturals, Sequences\nVARIABLE s\nInit == s = <<>>\nNext == Len(s) < 3 /\\ \\E v \\in {1, 2} : s' = Append(s, v)\nInv == s \\in Seq({1, 2})\nLimit == \\A i \\in {0} : (2147483647 + Len(s)) >= 0\n====\n",
            sequence_length_projection_with_spec,
        ),
        (
            "AgeOverflow",
            "---- MODULE AgeOverflow ----\nEXTENDS Naturals\nVARIABLE clock, rec\nInit == clock = 0 /\\ rec = [k \\in {1} |-> [created |-> 0, ok |-> TRUE]]\nNext == (clock' = clock + 1 /\\ UNCHANGED rec) \\/ (rec[1].created + 1 <= clock /\\ rec' = [rec EXCEPT ![1] = [created |-> clock, ok |-> TRUE]] /\\ UNCHANGED clock)\nInv == clock \\in Nat /\\ rec \\in [{1} -> [created: Nat, ok: BOOLEAN]]\nLimit == (2147483647 + 1) >= 0\n====\n",
            age_projection_with_spec,
        ),
    ];
    for (name, tla, derive) in cases {
        let (p, cfg) = load(name, tla, "INIT Init\nNEXT Next\nINVARIANT Inv\n");
        let (inv, lim) = ([def_expr(&p, "Inv")], [def_expr(&p, "Limit")]);
        assert!(
            derive(
                &p,
                &cfg,
                &def_expr(&p, "Init"),
                &def_expr(&p, "Next"),
                CheckSpec { invariants: &inv, constraints: &lim, ..CheckSpec::default() }
            )
            .is_none(),
            "{name} must refuse partial or overflowing constraint"
        );
    }
}

#[test]
fn certifies_builtin_nat_and_distinguishes_tuple_vs_many_const_substs() {
    let (p, cfg, cert) = fixture_erasure_const_nat();
    assert_constrained_lean(&cert, "GeneratedErasure");
    assert!(cert.contains("\"Builtin(Nat)\""), "expected Builtin(Nat), got:\n{cert}");
    assert!(!cert.contains("\"SetEnum()\""), "Nat must never lower to placeholder SetEnum()");
    let (inv, bad) = ([def_expr(&p, "Inv")], [def_expr(&p, "BadQuantLimit")]);
    assert!(unobserved_projection_with_spec(
        &p,
        &cfg,
        &def_expr(&p, "Init"),
        &def_expr(&p, "Next"),
        CheckSpec { invariants: &inv, constraints: &bad, ..CheckSpec::default() },
    )
    .is_none());

    let binder_tla = r#"---- MODULE BinderConstCert ----
EXTENDS Naturals
CONSTANT C
VARIABLE x, tag
S == {<<1, 2>>}
TruthMany == \E a, b \in S : a = b
TruthTuple == \E <<a, b>> \in S : a = b
Init == x = 0 /\ tag = 0
Next == x' = 1 /\ tag' = 1
Inv == x \in {0, 1}
Lim == C
====
"#;
    let (pm, cm) = load("BinderConstCert", binder_tla, "INIT Init\nNEXT Next\nCONSTANT C <- TruthMany\nINVARIANT Inv\n");
    let (pt, ct) = load("BinderConstCert", binder_tla, "INIT Init\nNEXT Next\nCONSTANT C <- TruthTuple\nINVARIANT Inv\n");
    let cert_many = unobserved_projection_with_spec(
        &pm,
        &cm,
        &def_expr(&pm, "Init"),
        &def_expr(&pm, "Next"),
        CheckSpec { invariants: &[def_expr(&pm, "Inv")], constraints: &[def_expr(&pm, "Lim")], ..CheckSpec::default() },
    )
    .unwrap()
    .certificate
    .unwrap();
    let cert_tuple = unobserved_projection_with_spec(
        &pt,
        &ct,
        &def_expr(&pt, "Init"),
        &def_expr(&pt, "Next"),
        CheckSpec { invariants: &[def_expr(&pt, "Inv")], constraints: &[def_expr(&pt, "Lim")], ..CheckSpec::default() },
    )
    .unwrap()
    .certificate
    .unwrap();
    assert!(cert_many.contains("Many(") && !cert_many.contains("Tuple(L"));
    assert!(cert_tuple.contains("Tuple(L"));
    assert_ne!(cert_many, cert_tuple);
}

#[test]
fn large_const_subst_scales_to_512_and_refuses_above_cap_and_handles_marker_literals() {
    let cert_512 = fixture_large_const_subst_512();
    assert_constrained_lean(&cert_512, "GeneratedErasure");
    assert!(cert_512.contains("abbrev ConstSubstCount : Nat := 512"));
    assert!(cert_512.contains("intro i; rfl"));

    // Above MAX_CERT_CONST_SUBSTS (1024), erasure must refuse cleanly before installing any reduction.
    let (p_over, cfg_over) = build_large_bindings_spec(1025);
    let (inv, lim) = ([def_expr(&p_over, "Inv")], [def_expr(&p_over, "Lim")]);
    assert!(unobserved_projection_with_spec(
        &p_over,
        &cfg_over,
        &def_expr(&p_over, "Init"),
        &def_expr(&p_over, "Next"),
        CheckSpec { invariants: &inv, constraints: &lim, ..CheckSpec::default() },
    )
    .is_none());

    let (plain_markers, cons_markers) = fixture_marker_strings_in_model_data();
    assert!(plain_markers.contains("def constSubstDeclared"));
    assert!(!plain_markers.contains("\ndef constSubstDeclared (i : Fin ConstSubstCount) : String :=\n"));
    assert!(!plain_markers.contains("\ndef constrainedAfter := (model sem).constrainedReduced\n"));
    assert_constrained_lean(&cons_markers, "GeneratedErasure");
    assert!(cons_markers.contains("\ndef constSubstDeclared (i : Fin ConstSubstCount) : String :=\n"));
}

/// The shipped `proofs/field/ActionChecks.tla` certificate, so the published
/// example's negative audit is part of the regression instead of a manual step.
fn fixture_shipped_action_checks() -> String {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../..");
    let cfg_src = std::fs::read_to_string(root.join("proofs/field/ActionChecks.cfg")).unwrap();
    let program = Program::load(&root.join("proofs/field/ActionChecks.tla"), &[]).unwrap();
    let cfg = parse_cfg(&cfg_src).unwrap();
    let (inv, lim, ac, ap) = (
        [def_expr(&program, "Inv")],
        [def_expr(&program, "StateLimit")],
        [def_expr(&program, "ActLimit")],
        [action_prop_expr(&program, "ActProp")],
    );
    let spec = CheckSpec { invariants: &inv, constraints: &lim, action_constraints: &ac, action_props: &ap, ..CheckSpec::default() };
    phase_projection_with_spec(&program, &cfg, &def_expr(&program, "Init"), &def_expr(&program, "Next"), spec)
        .expect("the shipped ActionChecks projection")
        .certificate
        .expect("the shipped ActionChecks certificate")
}

/// A certificate whose only data field is dead in every phase, so clearing the
/// write table is sound and the audit's frame mutation must be scoped out.
const INIT_MERGE_TLA: &str = r#"---- MODULE InitMerge ----
EXTENDS Naturals
VARIABLE r, tag
Init == \E a,b,c \in 0..7:
          \E n \in {0,1}: /\ tag = <<a,b,c>> /\ r = [mode |-> "idle", buf |-> n]
Start == /\ r.mode = "idle"
         /\ r' = [r EXCEPT !.mode = "busy", !.buf = 0]
         /\ UNCHANGED tag
Finish == /\ r.mode = "busy"
          /\ r' = [r EXCEPT !.mode = "idle"]
          /\ UNCHANGED tag
Next == Start \/ Finish
Inv == /\ \E a,b,c \in 0..7 : tag = <<a,b,c>>
       /\ r.mode \in {"idle", "busy"}
Edge == r'.mode \in {"busy", "idle"}
====
"#;

fn fixture_init_merge_certificate() -> String {
    let cfg = "INIT Init\nNEXT Next\nINVARIANT Inv\nACTION_CONSTRAINT Edge\nCHECK_DEADLOCK FALSE\n";
    let (p, cfg) = load("InitMerge", INIT_MERGE_TLA, cfg);
    let (inv, ac) = ([def_expr(&p, "Inv")], [def_expr(&p, "Edge")]);
    let spec = CheckSpec { invariants: &inv, action_constraints: &ac, ..CheckSpec::default() };
    phase_projection_with_spec(&p, &cfg, &def_expr(&p, "Init"), &def_expr(&p, "Next"), spec)
        .expect("initial-state merge keeps the projection applicable")
        .certificate
        .expect("initial-state merge certificate")
}

#[test]
#[ignore = "requires lean on PATH; verifies all constrained certificate families sequentially with proofs/check_generated.py --negative"]
fn verify_all_constrained_certificate_families_with_lean_negative() {
    let (_, _, erased_proj, erased_keyed_cert) = fixture_erased_constrained();
    let (_, _, _, erased_equiv_cert) = fixture_erased_equiv_constrained();
    let (_, _, field_proj) = fixture_field_constrained();
    let (_, _, seq_proj) = fixture_sequence_constrained();
    let (_, _, nat_cert) = fixture_erasure_const_nat();
    let (labels_plain_cert, labels_cons_cert) = fixture_marker_strings_in_model_data();

    let certificates = [
        ("Keyed", fixture_keyed_constrained()),
        ("EquivSym", fixture_equiv_constrained()),
        ("ChooseSym", fixture_choose_constrained()),
        ("Erasure", erased_proj.certificate.unwrap()),
        ("ErasedKeyed", erased_keyed_cert),
        ("ErasedEquiv", erased_equiv_cert),
        ("Field", field_proj.certificate.unwrap()),
        ("Length", seq_proj.certificate.unwrap()),
        ("History", fixture_history_constrained()),
        ("Age", fixture_age_constrained().certificate.unwrap()),
        ("Ordered", fixture_ordered_constrained()),
        ("FieldAction", fixture_field_action_certificate()),
        ("ActionChecks", fixture_shipped_action_checks()),
        ("InitMerge", fixture_init_merge_certificate()),
        ("FieldActorKey", fixture_field_actor_key("ActTwo").unwrap()),
        ("OrderedAction", fixture_ordered_action_constrained()),
        ("NestedAction", fixture_nested_action_constrained()),
        ("LiveAction", fixture_live_action_constrained()),
        ("AgeHistory", fixture_age_history_constrained()),
        ("Nested", fixture_nested_constrained()),
        ("Live", fixture_live_constrained()),
        ("ErasureConstNat", nat_cert),
        ("LargeBindings512", fixture_large_const_subst_512()),
        ("LabelsPlain", labels_plain_cert),
        ("LabelsConstrained", labels_cons_cert),
    ];

    let dir = tlx_testkit::TempDir::new("lean-constrained-audit");
    let rules = include_str!("../src/optimize/Rules.lean");
    let mut files = Vec::with_capacity(certificates.len());
    for (name, cert) in certificates {
        let path = dir.join(format!("{name}.lean"));
        std::fs::write(&path, format!("{rules}\n{cert}")).unwrap();
        files.push(path);
    }

    let script = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../proofs/check_generated.py");
    let out = std::process::Command::new("python3")
        .arg(&script)
        .args(["--lean", "lean", "--negative"])
        .args(&files)
        .output()
        .expect("run check_generated.py");
    let stdout = String::from_utf8_lossy(&out.stdout);
    let stderr = String::from_utf8_lossy(&out.stderr);
    eprint!("{stdout}{stderr}");
    assert!(out.status.success(), "check_generated.py --negative failed ({}):\n{stdout}{stderr}", out.status);
}
