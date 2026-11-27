//! End-to-end CLI regression tests for `.cfg` constant bindings, overrides,
//! arity checks, and evaluator static analysis (S-2, S-4, S-5, E-4, E-8).

fn run_spec(tag: &str, name: &str, tla: &str, cfg: &str, extra_args: &[&str]) -> (i32, String, String) {
    let dir = tlx_testkit::TempDir::new(tag);
    let tla_path = dir.write(&format!("{name}.tla"), tla);
    let _cfg_path = dir.write(&format!("{name}.cfg"), cfg);
    let mut cmd = tlx_testkit::tlx!();
    cmd.arg("check").arg(&tla_path).args(extra_args);
    let out = cmd.run();
    (out.code, out.stdout, out.stderr)
}

#[test]
fn dup_const_age_optimize_finds_violation() {
    let tla = r#"---- MODULE DupConstAge ----
EXTENDS Naturals
CONSTANT Delay
VARIABLES clock, records, dropped
Empty == [status |-> "empty", payload |-> ""]
Init == clock = 0 /\ records = [k \in {1} |-> Empty] /\ dropped = FALSE
Tick == clock' = clock + 1 /\ UNCHANGED <<records, dropped>>
Put  == records' = [records EXCEPT ![1] = [created |-> clock, payload |-> "x"]]
        /\ UNCHANGED <<clock, dropped>>
Drop == records[1] # Empty /\ records[1].created + Delay <= clock
        /\ records' = [records EXCEPT ![1] = Empty]
        /\ dropped' = TRUE /\ UNCHANGED clock
Next == Tick \/ Put \/ Drop
Inv  == ~dropped
====
"#;
    let cfg = "\
INIT Init
NEXT Next
INVARIANT Inv
CONSTANT Delay = 0
CONSTANT Delay = 2
";
    for extra in [&["-tlc"][..], &["-optimize"][..]] {
        let (code, stdout, stderr) = run_spec("dup-const-age", "DupConstAge", tla, cfg, extra);
        assert_eq!(code, 12, "mode {extra:?}: stdout={stdout}\nstderr={stderr}");
        assert!(stdout.contains("Invariant Inv is violated"), "mode {extra:?}: stdout={stdout}");
    }
}

#[test]
fn const_act_memo_finds_action_property_violation() {
    let tla = r#"---- MODULE ConstActMemo ----
CONSTANT Act(_)
VARIABLE x
MyAct(n) == x' = n
StepOk == Act(1)
Init == x = 0
Next == x = 0 /\ x' \in {1, 2}
Prop == [][StepOk]_x
====
"#;
    let cfg = "\
CONSTANT Act <- MyAct
INIT Init
NEXT Next
PROPERTY Prop
CHECK_DEADLOCK FALSE
";
    for extra in [&[][..], &["-tlc"][..]] {
        let (code, stdout, stderr) = run_spec("const-act-memo", "ConstActMemo", tla, cfg, extra);
        assert_eq!(code, 13, "mode {extra:?}: stdout={stdout}\nstderr={stderr}");
        assert!(stdout.contains("Action property Prop is violated"), "mode {extra:?}: stdout={stdout}");
    }
}

#[test]
fn const_act_by_name_and_higher_order_and_recursion() {
    // Wrap(v) == Act(v) must be marked def_by_name so Wrap(x) passes `x` by name
    // when MyAct primes its argument (`v' = 1`). Higher-order ApplyOp(Act) must
    // also not be cached as constant or state-level.
    let tla = r#"---- MODULE ConstActHo ----
CONSTANT Act(_)
VARIABLE x
MyAct(v) == v' = 1
Wrap(v) == Act(v)
ApplyOp(F(_)) == F(x)
StepOk == ApplyOp(Act)
Init == x = 0
Next == (x = 0 /\ Wrap(x)) \/ (x = 0 /\ x' = 2)
Prop == [][StepOk]_x
====
"#;
    let cfg = "\
CONSTANT Act <- MyAct
INIT Init
NEXT Next
PROPERTY Prop
CHECK_DEADLOCK FALSE
";
    let (code, stdout, stderr) = run_spec("const-act-ho", "ConstActHo", tla, cfg, &["-tlc"]);
    assert_eq!(code, 13, "stdout={stdout}\nstderr={stderr}");
    assert!(stdout.contains("Action property Prop is violated"), "stdout={stdout}");

    // Recursion through `CONSTANT Rec(_) <- F` must be detected by `collect_def_refs`
    // so the depth guard triggers cleanly instead of overflowing the stack.
    let rec_tla = r#"---- MODULE ConstRecCycle ----
EXTENDS Naturals
CONSTANT Rec(_)
VARIABLE x
F(n) == Rec(n + 1)
Init == x = F(0)
Next == UNCHANGED x
====
"#;
    let rec_cfg = "CONSTANT Rec <- F\nINIT Init\nNEXT Next\n";
    let (code, stdout, stderr) = run_spec("const-rec-cycle", "ConstRecCycle", rec_tla, rec_cfg, &["-tlc"]);
    assert_ne!(code, 0, "infinite recursion via <- must fail cleanly, stdout={stdout}\nstderr={stderr}");
    assert_ne!(code, 101, "must not panic/overflow: stdout={stdout}\nstderr={stderr}");
}

#[test]
fn def_value_var_and_alias_override() {
    let tla = r#"---- MODULE DefValueVar ----
VARIABLE x
V == x
A == [x |-> x]
Init == V = 0 /\ x = 1
Next == UNCHANGED x
Inv  == x = 0
====
"#;
    let cfg = "\
CONSTANT V = 0
INIT Init
NEXT Next
INVARIANT Inv
";
    for extra in [&[][..], &["-tlc"][..]] {
        let (code, stdout, stderr) = run_spec("def-value-var", "DefValueVar", tla, cfg, extra);
        assert_eq!(code, 12, "mode {extra:?}: stdout={stdout}\nstderr={stderr}");
        assert!(stdout.contains("Invariant Inv is violated"), "mode {extra:?}: stdout={stdout}");
    }

    // Value-overriding ALIAS must not bypass def_value via alias_record.
    let alias_cfg = "\
CONSTANT V = 0
CONSTANT A = 99
INIT Init
NEXT Next
INVARIANT Inv
ALIAS A
";
    let (code, stdout, stderr) = run_spec("def-value-alias", "DefValueVar", tla, alias_cfg, &["-tlc"]);
    assert_eq!(code, 12, "stdout={stdout}\nstderr={stderr}");
    assert!(stdout.contains("Invariant Inv is violated"), "stdout={stdout}");
}

#[test]
fn const_subst_arity_and_section_targets() {
    let tla = r#"---- MODULE ConstSubstArity ----
CONSTANT F(_, _)
VARIABLE x
G(a) == a
Init == x = F(10, 20)
Next == UNCHANGED x
====
"#;
    let cfg = "\
CONSTANT F <- G
INIT Init
NEXT Next
";
    let (code, stdout, stderr) = run_spec("const-subst-arity", "ConstSubstArity", tla, cfg, &["-tlc"]);
    assert_eq!(code, 151, "stdout={stdout}\nstderr={stderr}");
    assert!(stdout.contains("different number of arguments"), "stdout={stdout}");

    // `_POSSIBLE` and `POSTCONDITION` targeting a `CONSTANT` substituted via `<-`
    // (must follow `subst_target` rather than failing `root_def` lookup).
    let post_tla = r#"---- MODULE SubstPossiblePost ----
EXTENDS TLC
CONSTANT Poss, Post
VARIABLE x
RealPoss == TRUE \/ (x = 1)
RealPost == TRUE \/ (TLCGet("distinct") = 2)
Init == x = 0
Next == x = 0 /\ x' = 1
====
"#;
    let post_cfg = "\
CONSTANT Poss <- RealPoss
CONSTANT Post <- RealPost
INIT Init
NEXT Next
_POSSIBLE Poss
POSTCONDITION Post
CHECK_DEADLOCK FALSE
";
    let (code, stdout, stderr) = run_spec("subst-poss-post", "SubstPossiblePost", post_tla, post_cfg, &["-tlc"]);
    assert_eq!(code, 0, "stdout={stdout}\nstderr={stderr}");

    // `INVARIANT` targeting a 1-arg constant substituted by a 1-arg operator -> exit 151.
    let inv_tla = r#"---- MODULE SubstInvArity ----
CONSTANT P(_)
VARIABLE x
G(a) == a = 0
Init == x = 0
Next == UNCHANGED x
====
"#;
    let inv_cfg = "CONSTANT P <- G\nINIT Init\nNEXT Next\nINVARIANT P\n";
    let (code, stdout, stderr) = run_spec("subst-inv-arity", "SubstInvArity", inv_tla, inv_cfg, &["-tlc"]);
    assert_eq!(code, 151, "stdout={stdout}\nstderr={stderr}");
    assert!(stdout.contains("requires arguments"), "stdout={stdout}");
}

#[test]
fn fold_redirect_respects_subst_override() {
    let tla = r#"---- MODULE FoldRedirect ----
EXTENDS Naturals, Sequences, Folds
VARIABLE x
Pick(T) == CHOOSE v \in T : TRUE
PickMax(T) == CHOOSE v \in T : \A u \in T : v >= u
Init == x = MapThenFoldSet(LAMBDA a, b : Append(b, a), <<>>, LAMBDA v : v, Pick, {1, 2})
Next == UNCHANGED x
Inv  == x = <<2, 1>>
====
"#;
    let cfg = "\
CONSTANT Pick <- PickMax
INIT Init
NEXT Next
INVARIANT Inv
";
    for extra in [&[][..], &["-tlc"][..]] {
        let (code, stdout, stderr) = run_spec("fold-redirect", "FoldRedirect", tla, cfg, extra);
        assert_eq!(code, 12, "mode {extra:?}: stdout={stdout}\nstderr={stderr}");
        assert!(stdout.contains("Invariant Inv is violated"), "mode {extra:?}: stdout={stdout}");
    }
}

#[test]
fn pure_operator_override_certifies_optimize_and_symmetry() {
    let tla = r#"---- MODULE OverrideCertify ----
EXTENDS Naturals
CONSTANT Nodes, Limit
VARIABLE state, tag
Ok(n) == state[n] < Limit
Bound(n) == state[n] < Limit + 1
Init == state = [n \in Nodes |-> 0] /\ tag = 0
Next == \E n \in Nodes : Ok(n) /\ state' = [state EXCEPT ![n] = state[n] + 1] /\ tag' = tag
Inv == \A n \in Nodes : state[n] <= Limit + 1
====
"#;
    let cfg = "INIT Init\nNEXT Next\nCONSTANTS\n  Nodes = {n1, n2}\n  Limit = 2\n  Ok <- Bound\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
    let dir = tlx_testkit::TempDir::new("override-certify");
    let tla_path = dir.write("OverrideCertify.tla", tla);
    dir.write("OverrideCertify.cfg", cfg);

    let mut counts = Vec::new();
    for (tier, args) in
        [("baseline", &["-tlc", "-interp"][..]), ("interp", &["-interp", "-optimize"][..]), ("compiled", &["-compile", "-optimize"][..])]
    {
        let mut cmd = tlx_testkit::tlx_default!();
        cmd.check(&tla_path)
            .args(args)
            .env("TLX_PROOF_DIR", dir.join(format!("proofs-{tier}")))
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(std::time::Duration::from_secs(60));
        let out = cmd.run();
        assert_eq!(out.code, 0, "{tier}: {}", out.text());
        let line = out.stdout.lines().find(|l| l.contains(" distinct states found")).unwrap_or_default().to_string();
        counts.push((tier, line));
        let cert = std::fs::read_dir(dir.join(format!("proofs-{tier}")))
            .into_iter()
            .flatten()
            .flatten()
            .map(|e| std::fs::read_to_string(e.path().join("Optimization.lean")).unwrap_or_default())
            .collect::<Vec<_>>()
            .join("\n");
        if tier != "baseline" {
            assert!(cert.contains("def_subst_model_slice"), "{tier}: override obligation missing");
        }
    }
    let distinct = |tier: &str| {
        let line = &counts.iter().find(|(t, _)| *t == tier).unwrap().1;
        line.split(" distinct states found").next().unwrap().rsplit(' ').next().unwrap().parse::<u64>().unwrap()
    };
    let base = distinct("baseline");
    assert_eq!(distinct("interp"), base, "interp -optimize changed the distinct count: {counts:?}");
    assert_eq!(distinct("compiled"), base, "compiled -optimize changed the distinct count: {counts:?}");
}
