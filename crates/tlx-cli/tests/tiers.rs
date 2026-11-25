//! Every execution tier (interpreter, `-compile` with and without
//! native code) reports the same result as the interpreter, also where the
//! compiled tiers fall back to it: evaluation errors in invariants and
//! action properties keep their context, an Init the IR cannot run is
//! computed by the interpreter, and side effects of a failed IR run are not
//! repeated by the fallback.

use tlx_testkit::cli::{result_lines, tests_specs, TIERS};

/// Check spec `name` in each tier: (tier, exit code, output).
fn run_tiers(name: &str) -> Vec<(&'static str, i32, String)> {
    TIERS
        .iter()
        .map(|(tier, args, env)| {
            let out = tlx_testkit::tlx!()
                .check(format!("{name}.tla"))
                .cfg(format!("{name}.cfg"))
                .args(["-workers", "1"])
                .args(*args)
                .dir(tests_specs())
                .envs(env.iter().copied())
                .run();
            (*tier, out.code, out.text())
        })
        .collect()
}

/// Every tier reports what the interpreter does; its exit code and output.
fn check_tiers_agree(name: &str) -> (i32, String) {
    let runs = run_tiers(name);
    let (_, code, out) = &runs[0];
    for (tier, c, o) in &runs[1..] {
        assert_eq!(
            (c, result_lines(o)),
            (code, result_lines(out)),
            "{name}: {tier} differs from the interpreter:\n{o}\n--- interpreter:\n{out}"
        );
    }
    (*code, out.clone())
}

#[test]
fn invariant_evaluation_error() {
    let (code, out) = check_tiers_agree("EK5");
    assert_eq!(code, 76, "{out}");
    assert!(out.contains("Error: Evaluating invariant Inv failed.\nAttempted to access index 3 of tuple"), "{out}");
    assert!(out.contains("The average outdegree of the complete state graph is 1 "), "{out}");
}

#[test]
fn action_property_evaluation_error() {
    let (code, out) = check_tiers_agree("EK6");
    assert_eq!(code, 75, "{out}");
    assert!(out.contains("Error: Evaluating action property AP failed.\nAttempted to access index 3 of tuple"), "{out}");
    // The trace ends with the successor of the step.
    assert!(out.contains("State 3: <Next line 8, col 9 to line 8, col 24 of module EK6>\nx = 2\n"), "{out}");
}

#[test]
fn init_falls_back_to_the_interpreter() {
    let (code, out) = check_tiers_agree("IR1");
    assert_eq!(code, 0, "{out}");
    assert!(out.contains("8 states generated, 8 distinct states found, 0 states left on queue."), "{out}");
}

#[test]
fn side_effects_of_a_failed_ir_action_happen_once() {
    let (code, out) = check_tiers_agree("IR2");
    assert_eq!(code, 0, "{out}");
}

#[test]
fn side_effects_of_a_failed_ir_init_happen_once() {
    let (code, out) = check_tiers_agree("IR3");
    assert_eq!(code, 0, "{out}");
}

/// The `compile:` lines of output `out`.
fn compile_lines(out: &str) -> Vec<&str> {
    out.lines().filter(|l| l.starts_with("compile:")).collect()
}

/// Check IR1 with `args` and `env` and the default tier (no tier flag
/// added): (exit code, output).
fn run_default(args: &[&str], env: &[(&str, &str)]) -> (i32, String) {
    let out = tlx_testkit::tlx_default!().check("IR1.tla").cfg("IR1.cfg").args(args).dir(tests_specs()).envs(env.iter().copied()).run();
    (out.code, out.text())
}

#[test]
fn the_default_tier_is_the_compiled_tier() {
    let (code, interp) = run_default(&["-interp"], &[]);
    assert_eq!(code, 0, "{interp}");
    assert!(compile_lines(&interp).is_empty(), "-interp must not compile:\n{interp}");
    for args in [&[][..], &["-compile"], &["-interp", "-compile"]] {
        let (code, out) = run_default(args, &[]);
        assert_eq!(code, 0, "{args:?}: {out}");
        assert!(!compile_lines(&out).is_empty(), "{args:?} must run the compiled tier:\n{out}");
        assert_eq!(result_lines(&out), result_lines(&interp), "{args:?}");
    }
    // (The last tier flag wins.)
    let (_, out) = run_default(&["-compile", "-interp"], &[]);
    assert!(compile_lines(&out).is_empty(), "{out}");
}

/// Without a C compiler the default tier keeps the JIT code, or, with no
/// JIT either, checks with the interpreter: one line says so.
#[test]
fn the_default_tier_without_a_c_compiler() {
    let cache = std::env::temp_dir().join(format!("tlx-tiers-nocc-{}", std::process::id()));
    let cache = cache.to_str().unwrap();
    let (_, interp) = run_default(&["-interp"], &[]);
    let no_cc = [("CC", "/nonexistent/cc"), ("TLX_CACHE", cache), ("TLX_NATIVE_SYNC", "1")];
    let (code, out) = run_default(&[], &no_cc);
    assert_eq!(code, 0, "{out}");
    assert_eq!(result_lines(&out), result_lines(&interp));
    let failed: Vec<_> = compile_lines(&out).into_iter().filter(|l| l.contains("C compiler")).collect();
    assert_eq!(failed, ["compile: C build failed, using the JIT code: no C compiler (/nonexistent/cc not found)"], "{out}");
    let (code, out) = run_default(&[], &[("TLX_JIT", "0"), no_cc[0], no_cc[1]]);
    assert_eq!(code, 0, "{out}");
    assert_eq!(result_lines(&out), result_lines(&interp));
    assert_eq!(
        compile_lines(&out),
        ["compile: no JIT and no C compiler (/nonexistent/cc not found): checking with the interpreter"],
        "{out}"
    );
    // (Nothing was written into the cache.)
    assert!(std::fs::read_dir(cache).map_or(true, |mut d| d.next().is_none()), "files in {cache}");
    let _ = std::fs::remove_dir_all(cache);
}

#[test]
fn large_symmetry_with_view_agrees_across_tiers() {
    let spec = r#"---- MODULE LargeView ----
EXTENDS TLC
CONSTANT N
VARIABLE x
Sym == Permutations(N)
V == x
Init == x \in N
Next == x' \in N
====
"#;
    for (n, want_gen) in [(7usize, 14usize), (8usize, 16usize)] {
        let elems = (1..=n).map(|i| format!("n{i}")).collect::<Vec<_>>().join(", ");
        let cfg = format!("CONSTANT N = {{{elems}}}\nINIT Init\nNEXT Next\nSYMMETRY Sym\nVIEW V\n");
        let dir = tlx_testkit::TempDir::with_spec(&format!("large-view-{n}"), spec, &cfg);
        let interp = tlx_testkit::tlx!()
            .check("LargeView.tla")
            .cfg("LargeView.cfg")
            .args(["-tlc", "-workers", "1", "-interp"])
            .dir(dir.path())
            .env("TLX_PRERUN_REUSE", "0")
            .run();
        let compile = tlx_testkit::tlx!()
            .check("LargeView.tla")
            .cfg("LargeView.cfg")
            .args(["-tlc", "-workers", "1", "-compile"])
            .dir(dir.path())
            .env("TLX_PRERUN_REUSE", "0")
            .run();
        assert_eq!(interp.code, 0, "interp n={n}:\n{}", interp.text());
        assert_eq!(compile.code, 0, "compile n={n}:\n{}", compile.text());
        let expected = format!("{want_gen} states generated, 1 distinct states found, 0 states left on queue.");
        assert!(interp.text().contains(&expected), "interp n={n}:\n{}", interp.text());
        assert!(compile.text().contains(&expected), "compile n={n}:\n{}", compile.text());
        assert_eq!(result_lines(&compile.text()), result_lines(&interp.text()), "n={n}");
    }
}

#[test]
fn row_deadlock_and_set_prefix_agree_across_tiers() {
    // Prefix pruning with unknown unpinned candidates must preserve the
    // reachable deadlock under VIEW in both -interp and -compile.
    let deadlock_spec = r#"---- MODULE RowDeadlock ----
EXTENDS TLC
CONSTANTS a,b,c,u,v,y,z,w
VARIABLE rows
Keys == {a,b,c}
Peers == {u,v}
Sym == Permutations(Keys) \cup Permutations(Peers)
V == rows[a]
Init == \E p \in Permutations(Keys) :
           rows = (p[a] :> z) @@ (p[b] :> w) @@ (p[c] :> y)
Next == \E k \in Keys, peer \in Peers :
            /\ rows[k] = w
            /\ rows' = [rows EXCEPT ![k] = peer]
====
"#;
    let deadlock_cfg = "CONSTANTS a = a b = b c = c u = u v = v y = y z = z w = w\nINIT Init\nNEXT Next\nSYMMETRY Sym\nVIEW V\n";
    let dir = tlx_testkit::TempDir::with_spec("row-deadlock", deadlock_spec, deadlock_cfg);
    let interp = tlx_testkit::tlx!()
        .check("RowDeadlock.tla")
        .cfg("RowDeadlock.cfg")
        .args(["-tlc", "-workers", "1", "-interp"])
        .dir(dir.path())
        .run();
    let compile = tlx_testkit::tlx!()
        .check("RowDeadlock.tla")
        .cfg("RowDeadlock.cfg")
        .args(["-tlc", "-workers", "1", "-compile"])
        .dir(dir.path())
        .run();
    assert_eq!(interp.code, 11, "interp:\n{}", interp.text());
    assert_eq!(compile.code, 11, "compile:\n{}", compile.text());
    assert!(interp.text().contains("8 states generated, 2 distinct states found"), "interp:\n{}", interp.text());
    assert!(compile.text().contains("8 states generated, 2 distinct states found"), "compile:\n{}", compile.text());
    assert_eq!(result_lines(&compile.text()), result_lines(&interp.text()));

    // Heterogeneous payloads that can trigger a TLC comparison error on a
    // permutation fixing a leading set must report the same exit-75 error.
    let set_prefix_spec = r#"---- MODULE SetPrefix ----
EXTENDS TLC
CONSTANTS a, b, c
VARIABLE v
Sym == Permutations({a, b, c})
Init == v = <<{b,c}, (a :> ((b :> 0) @@ (c :> FALSE))) @@ (b :> 0) @@ (c :> 1)>>
Next == UNCHANGED v
====
"#;
    let set_prefix_cfg = "CONSTANTS a = a b = b c = c\nINIT Init\nNEXT Next\nSYMMETRY Sym\n";
    let sp_dir = tlx_testkit::TempDir::with_spec("set-prefix", set_prefix_spec, set_prefix_cfg);
    let sp_interp =
        tlx_testkit::tlx!().check("SetPrefix.tla").cfg("SetPrefix.cfg").args(["-tlc", "-workers", "1", "-interp"]).dir(sp_dir.path()).run();
    assert_eq!(sp_interp.code, 75, "SetPrefix interp:\n{}", sp_interp.text());

    // SetPrefixSize above and below order 720 (S_6 vs S_7) with VIEW must both
    // report exit 75 in -interp and -compile.
    let sps_spec = r#"---- MODULE SetPrefixSize ----
EXTENDS TLC
CONSTANTS N, a, b, c
VARIABLE v
Sym == Permutations(N)
V == v
Init == v = <<{b,c}, (a :> ((b :> 0) @@ (c :> FALSE))) @@ (b :> 0) @@ (c :> 1)>>
Next == UNCHANGED v
====
"#;
    for (label, cfg) in [
        ("n6", "CONSTANTS N = {a, n0, n1, n2, b, c} a = a b = b c = c\nINIT Init\nNEXT Next\nSYMMETRY Sym\nVIEW V\n"),
        ("n7", "CONSTANTS N = {a, n0, n1, n2, n3, b, c} a = a b = b c = c\nINIT Init\nNEXT Next\nSYMMETRY Sym\nVIEW V\n"),
    ] {
        let dir = tlx_testkit::TempDir::with_spec(&format!("set-prefix-size-{label}"), sps_spec, cfg);
        for tier in ["-interp", "-compile"] {
            let res = tlx_testkit::tlx!()
                .check("SetPrefixSize.tla")
                .cfg("SetPrefixSize.cfg")
                .args(["-tlc", "-workers", "1", tier])
                .dir(dir.path())
                .run();
            assert_eq!(res.code, 75, "SetPrefixSize {label} {tier}:\n{}", res.text());
        }
    }

    // ProductOrder (S_2 x S_3) succeeds under both union spellings in both tiers.
    let po_spec = r#"---- MODULE ProductOrder ----
EXTENDS TLC
CONSTANTS b0, b1, b2, a0, a1
VARIABLE v
A == {a0, a1}
B == {b0, b1, b2}
AB == Permutations(A) \cup Permutations(B)
BA == Permutations(B) \cup Permutations(A)
Init == v = <<a1, (a0 :> ((b1 :> 0) @@ (b2 :> FALSE))) @@ (a1 :> b1)>>
Next == UNCHANGED v
====
"#;
    for sym in ["AB", "BA"] {
        let cfg = format!("CONSTANTS b0 = b0 b1 = b1 b2 = b2 a0 = a0 a1 = a1\nINIT Init\nNEXT Next\nSYMMETRY {sym}\n");
        let dir = tlx_testkit::TempDir::with_spec(&format!("product-order-{sym}"), po_spec, &cfg);
        for tier in ["-interp", "-compile"] {
            let res = tlx_testkit::tlx!()
                .check("ProductOrder.tla")
                .cfg("ProductOrder.cfg")
                .args(["-tlc", "-workers", "1", tier])
                .dir(dir.path())
                .run();
            assert_eq!(res.code, 0, "ProductOrder {sym} {tier}:\n{}", res.text());
            assert!(res.text().contains("2 states generated, 1 distinct states found"), "ProductOrder {sym} {tier}:\n{}", res.text());
        }
    }

    // SevenPrefix (S_7, order 5040 > 720, no VIEW) must report exit 75 in both
    // -interp and -compile without materializing 7! permutations.
    let seven_spec = r#"---- MODULE SevenPrefix ----
EXTENDS TLC
CONSTANTS a, b, c, d, e, f, g
VARIABLE v
Sym == Permutations({a, b, c, d, e, f, g})
Init == v = <<{f,g}, (a :> ((f :> 0) @@ (g :> FALSE))) @@ (f :> 0) @@ (g :> 1)>>
Next == UNCHANGED v
====
"#;
    let seven_cfg = "CONSTANTS a = a b = b c = c d = d e = e f = f g = g\nINIT Init\nNEXT Next\nSYMMETRY Sym\n";
    let seven_dir = tlx_testkit::TempDir::with_spec("seven-prefix", seven_spec, seven_cfg);
    for tier in ["-interp", "-compile"] {
        let res = tlx_testkit::tlx!()
            .check("SevenPrefix.tla")
            .cfg("SevenPrefix.cfg")
            .args(["-tlc", "-workers", "1", tier])
            .dir(seven_dir.path())
            .run();
        assert_eq!(res.code, 75, "SevenPrefix {tier}:\n{}", res.text());
    }

    // TaggedProduct (S_3 x S_2) exits 75 under both union spellings in -interp
    // and (with VIEW routing through SymView) across both -interp and -compile.
    let tp_spec = r#"---- MODULE TaggedProduct ----
EXTENDS TLC
CONSTANTS A, B, a, d
VARIABLE rows
OuterFirst == Permutations(A) \cup Permutations(B)
InnerFirst == Permutations(B) \cup Permutations(A)
V == rows
Init == rows = [k \in A |-> IF k = a
                  THEN <<1, [j \in B |-> IF j = d THEN TRUE ELSE 1]>>
                  ELSE <<0, [j \in B |-> IF j = d THEN 0 ELSE 1]>>]
Next == UNCHANGED rows
====
"#;
    for sym in ["OuterFirst", "InnerFirst"] {
        let cfg = format!("CONSTANTS A = {{a,b,c}} B = {{d,e}} a = a d = d\nINIT Init\nNEXT Next\nSYMMETRY {sym}\n");
        let dir = tlx_testkit::TempDir::with_spec(&format!("tagged-product-{sym}"), tp_spec, &cfg);
        let res = tlx_testkit::tlx!()
            .check("TaggedProduct.tla")
            .cfg("TaggedProduct.cfg")
            .args(["-tlc", "-workers", "1", "-interp"])
            .dir(dir.path())
            .run();
        assert_eq!(res.code, 75, "TaggedProduct {sym} -interp:\n{}", res.text());

        let view_cfg = format!("{cfg}VIEW V\n");
        let vdir = tlx_testkit::TempDir::with_spec(&format!("tagged-product-view-{sym}"), tp_spec, &view_cfg);
        for tier in ["-interp", "-compile"] {
            let vres = tlx_testkit::tlx!()
                .check("TaggedProduct.tla")
                .cfg("TaggedProduct.cfg")
                .args(["-tlc", "-workers", "1", tier])
                .dir(vdir.path())
                .run();
            assert_eq!(vres.code, 75, "TaggedProduct+VIEW {sym} {tier}:\n{}", vres.text());
        }
    }

    // Nine disjoint two-node pairs (order 512 <= 720, 18 moved keys > 16) with
    // VIEW must not panic in compiled SymView ranking.
    let rep_spec = r#"---- MODULE Replicas ----
EXTENDS TLC
CONSTANTS P1, P2, P3, P4, P5, P6, P7, P8, P9
VARIABLE node
Nodes == P1 \cup P2 \cup P3 \cup P4 \cup P5 \cup P6 \cup P7 \cup P8 \cup P9
Sym == Permutations(P1) \cup Permutations(P2) \cup Permutations(P3) \cup Permutations(P4) \cup Permutations(P5) \cup Permutations(P6) \cup Permutations(P7) \cup Permutations(P8) \cup Permutations(P9)
V == node
Init == node \in Nodes
Next == node' \in Nodes
====
"#;
    let rep_cfg = "CONSTANTS P1={n1a,n1b} P2={n2a,n2b} P3={n3a,n3b} P4={n4a,n4b} P5={n5a,n5b} P6={n6a,n6b} P7={n7a,n7b} P8={n8a,n8b} P9={n9a,n9b}\nINIT Init\nNEXT Next\nVIEW V\nSYMMETRY Sym\n";
    let rep_dir = tlx_testkit::TempDir::with_spec("nine-replicas", rep_spec, rep_cfg);
    for tier in ["-interp", "-compile"] {
        let res = tlx_testkit::tlx!()
            .check("Replicas.tla")
            .cfg("Replicas.cfg")
            .args(["-tlc", "-workers", "1", tier])
            .dir(rep_dir.path())
            .env("TLX_PRERUN_REUSE", "0")
            .run();
        assert_eq!(res.code, 0, "Replicas {tier}:\n{}", res.text());
        assert!(res.text().contains("180 states generated, 9 distinct states found"), "Replicas {tier}:\n{}", res.text());
    }

    // Overlapping declarations (`Permutations({a,b}) \cup Permutations({b,c})`)
    // must preserve their generator order on fallible comparisons in both tiers.
    let ov_spec = r#"---- MODULE Overlapping ----
EXTENDS TLC
CONSTANTS a,b,c
VARIABLE x
Full == Permutations({a,b,c})
Overlap == Permutations({a,b}) \cup Permutations({b,c})
V == x
Init == x = <<c, (a :> 0) @@ (b :> FALSE) @@ (c :> a)>>
SetInit == x = <<{b,c}, (a :> ((b :> 0) @@ (c :> FALSE))) @@ (b :> 0) @@ (c :> 1)>>
Next == UNCHANGED x
====
"#;
    for (label, init, sym, want_code) in [
        ("ov-init", "Init", "Overlap", 75),
        ("ov-set", "SetInit", "Overlap", 0),
        ("full-init", "Init", "Full", 0),
        ("full-set", "SetInit", "Full", 75),
    ] {
        let cfg = format!("CONSTANTS a = a b = b c = c\nINIT {init}\nNEXT Next\nSYMMETRY {sym}\nVIEW V\n");
        let dir = tlx_testkit::TempDir::with_spec(&format!("overlapping-{label}"), ov_spec, &cfg);
        for tier in ["-interp", "-compile"] {
            let res = tlx_testkit::tlx!()
                .check("Overlapping.tla")
                .cfg("Overlapping.cfg")
                .args(["-tlc", "-workers", "1", tier])
                .dir(dir.path())
                .run();
            assert_eq!(res.code, want_code, "Overlapping {label} {tier}:\n{}", res.text());
        }
    }

    // Tagged status map on S_9 must stay on the refinement fast path.
    let st_spec = r#"---- MODULE StatusRows ----
EXTENDS TLC
CONSTANTS Nodes, Down, Leader
VARIABLE status
Sym == Permutations(Nodes)
V == status
Init == status = [k \in Nodes \ {Down} |-> IF k = Leader THEN <<0, FALSE>> ELSE <<1, 42>>]
Next == UNCHANGED status
====
"#;
    let st_cfg = "CONSTANTS Nodes = {n0,n1,n2,n3,n4,n5,n6,n7,n8} Down = n0 Leader = n1\nINIT Init\nNEXT Next\nVIEW V\nSYMMETRY Sym\n";
    let st_dir = tlx_testkit::TempDir::with_spec("status-rows-9", st_spec, st_cfg);
    for tier in ["-interp", "-compile"] {
        let res = tlx_testkit::tlx!()
            .check("StatusRows.tla")
            .cfg("StatusRows.cfg")
            .args(["-tlc", "-workers", "1", tier])
            .dir(st_dir.path())
            .run();
        assert_eq!(res.code, 0, "StatusRows {tier}:\n{}", res.text());
        assert!(res.text().contains("2 states generated, 1 distinct states found"), "StatusRows {tier}:\n{}", res.text());
    }

    // Overlapping RoleMap (`Subset7` and `Roles7Any`), fixed-domain `WorkerStatus`
    // (`Workers8`), and invariant record-key bag `Heartbeats` (`Heartbeat9`).
    let role_spec = r#"---- MODULE RoleMap ----
EXTENDS TLC
CONSTANTS Nodes, Voters, Learners, Leader, Peer
VARIABLE msg
Roles == Permutations(Voters) \cup Permutations(Learners)
V == msg
Init == msg = <<Leader, (Leader :> TRUE) @@ (Peer :> 0)>>
AnyInit == \E sender \in Nodes : \E peer \in Nodes \ {sender} : msg = <<sender, (sender :> TRUE) @@ (peer :> 0)>>
Next == UNCHANGED msg
====
"#;
    for (label, cfg, want) in [
        (
            "subset7",
            "CONSTANTS Nodes = {n0,n1,n2,n3,n4,n5,n6} Voters = {n0,n1,n2,n3,n4,n5,n6} Learners = {n5,n6} Leader = n0 Peer = n1\nINIT Init\nNEXT Next\nSYMMETRY Roles\nVIEW V\n",
            "2 states generated, 1 distinct states found",
        ),
        (
            "roles7any",
            "CONSTANTS Nodes = {n0,n1,n2,n3,n4,n5,n6} Voters = {n0,n1,n2,n3,n4,n5} Learners = {n5,n6} Leader = n0 Peer = n1\nINIT AnyInit\nNEXT Next\nSYMMETRY Roles\nVIEW V\n",
            "43 states generated, 1 distinct states found",
        ),
    ] {
        let dir = tlx_testkit::TempDir::with_spec(&format!("role-map-{label}"), role_spec, cfg);
        let res = tlx_testkit::tlx!()
            .check("RoleMap.tla")
            .cfg("RoleMap.cfg")
            .args(["-tlc", "-workers", "1", "-interp"])
            .dir(dir.path())
            .run();
        assert_eq!(res.code, 0, "RoleMap {label}:\n{}", res.text());
        assert!(res.text().contains(want), "RoleMap {label}:\n{}", res.text());
    }

    let ws_spec = r#"---- MODULE WorkerStatus ----
EXTENDS TLC
CONSTANTS Workers, First, Last, enabled, epoch
VARIABLE status
Overlap == Permutations(Workers \ {Last}) \cup Permutations({First,Last})
Init == \E primary \in Workers :
          status = [n \in Workers |-> (enabled :> (n = primary)) @@ (epoch :> 0)]
Next == UNCHANGED status
====
"#;
    let ws_cfg = "CONSTANTS Workers = {a,b,c,d,e,f,g,h} First = a Last = h enabled = enabled epoch = epoch\nINIT Init\nNEXT Next\nSYMMETRY Overlap\n";
    let ws_dir = tlx_testkit::TempDir::with_spec("worker-status-8", ws_spec, ws_cfg);
    let ws_res = tlx_testkit::tlx!()
        .check("WorkerStatus.tla")
        .cfg("WorkerStatus.cfg")
        .args(["-tlc", "-workers", "1", "-interp"])
        .dir(ws_dir.path())
        .run();
    assert_eq!(ws_res.code, 0, "WorkerStatus:\n{}", ws_res.text());
    assert!(ws_res.text().contains("9 states generated, 1 distinct states found"), "WorkerStatus:\n{}", ws_res.text());

    let hb_spec = r#"---- MODULE Heartbeats ----
EXTENDS TLC
CONSTANT Nodes
VARIABLE inbox
Sym == Permutations(Nodes)
Init == inbox = [msg \in {[src |-> n, kind |-> "heartbeat"] : n \in Nodes} |-> 1]
Next == UNCHANGED inbox
V == inbox
====
"#;
    let hb_cfg = "CONSTANT Nodes = {a,b,c,d,e,f,g,h,i}\nINIT Init\nNEXT Next\nSYMMETRY Sym\nVIEW V\n";
    let hb_dir = tlx_testkit::TempDir::with_spec("heartbeats-9", hb_spec, hb_cfg);
    let hb_res = tlx_testkit::tlx!()
        .check("Heartbeats.tla")
        .cfg("Heartbeats.cfg")
        .args(["-tlc", "-workers", "1", "-interp"])
        .dir(hb_dir.path())
        .run();
    assert_eq!(hb_res.code, 0, "Heartbeats:\n{}", hb_res.text());
    assert!(hb_res.text().contains("2 states generated, 1 distinct states found"), "Heartbeats:\n{}", hb_res.text());
}
