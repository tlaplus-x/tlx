//! Value-contract litmus specs (docs/value-store.md §9):
//! function aliases, the empty function, EXCEPT on missing paths, CHOOSE
//! order over records with set-valued fields and sets of sets, and lazy
//! union duplicates. Each runs on the interpreter and on the three compiled
//! executors (closure IR, C, JIT) under `TLX_PARANOID`, which compares every
//! compiled result with the interpreter's; all must report TLC's counts
//! (cached in tests/specs/tlc/, checked against TLC by scripts/spectest.py).

use tlx_testkit::cli::{counts, tests_specs};

/// (name, extra `-compile` environment, column of the actions table that
/// must show calls: the executor under test ran).
const BACKENDS: [(&str, &[(&str, &str)], &str); 3] =
    [("closure IR", &[("TLX_NO_NATIVE", "1")], "ir"), ("C", &[("TLX_JIT", "0")], "native"), ("JIT", &[("TLX_JIT", "1")], "native")];

/// The litmus specs and TLC's counts for them.
const SPECS: [(&str, &str, &str); 6] = [
    (
        "ReprAlias",
        "10 states generated, 8 distinct states found, 0 states left on queue.",
        "The depth of the complete state graph search is 5.",
    ),
    (
        "ReprEmptyFcn",
        "11 states generated, 10 distinct states found, 0 states left on queue.",
        "The depth of the complete state graph search is 5.",
    ),
    (
        "ReprMissingPath",
        "10 states generated, 10 distinct states found, 0 states left on queue.",
        "The depth of the complete state graph search is 3.",
    ),
    (
        "ReprChooseOrder",
        "5 states generated, 5 distinct states found, 0 states left on queue.",
        "The depth of the complete state graph search is 5.",
    ),
    (
        "ReprLazyUnion",
        "13 states generated, 3 distinct states found, 0 states left on queue.",
        "The depth of the complete state graph search is 2.",
    ),
    (
        "ReprExceptEffects",
        "7 states generated, 7 distinct states found, 0 states left on queue.",
        "The depth of the complete state graph search is 3.",
    ),
];

/// The value store modes (`TLX_VALUE_STORE`): the slots that would be
/// `Dyn` (ReprExceptEffects' bag), every slot.
const STORES: [&str; 2] = ["1", "all"];

/// The calls in column `col` of the `-stats` actions table, summed over
/// the actions (also the mixed column for `native`: mixed calls run native
/// code with host regions).
fn calls(out: &str, col: &str) -> u64 {
    let mut lines = out.lines().skip_while(|l| !l.starts_with("actions "));
    let Some(head) = lines.next() else { return 0 };
    let cols: Vec<&str> = head.split_whitespace().skip(1).collect();
    let want: Vec<usize> =
        cols.iter().enumerate().filter(|(_, c)| **c == col || (col == "native" && **c == "mixed")).map(|(i, _)| i).collect();
    let mut total = 0;
    for l in lines.take_while(|l| l.starts_with("  ")) {
        // The name may contain spaces: the numbers are the last columns.
        let words: Vec<&str> = l.split_whitespace().collect();
        let nums = &words[words.len() - (cols.len() - 1)..];
        for &i in &want {
            total += nums.get(i).map_or(0, |n| n.replace(',', "").parse::<u64>().unwrap_or(0));
        }
    }
    total
}

/// TLC prints `<<"present", 0>>` once for ReprExceptEffects (the present
/// key's replacement), and nothing for the absent keys.
fn check_effects(name: &str, what: &str, text: &str) {
    if name == "ReprExceptEffects" {
        assert_eq!(text.matches("<<\"present\", 0>>").count(), 1, "{what}\n{text}");
        assert!(!text.contains("\"absent\""), "{what}\n{text}");
    }
}

fn run(name: &str, compile: bool, env: &[(&str, &str)]) -> tlx_testkit::cli::Run {
    let mut cmd = tlx_testkit::tlx!();
    cmd.check(format!("{name}.tla")).cfg(format!("{name}.cfg")).args(["-workers", "1", "-stats"]).dir(tests_specs());
    if compile {
        cmd.arg("-compile").env("TLX_PARANOID", "1").envs(env.iter().copied());
    }
    cmd.run()
}

#[test]
fn litmus_specs_agree_with_tlc_on_every_executor() {
    for (name, generated, depth) in SPECS {
        let interp = run(name, false, &[]);
        assert_eq!(counts(&interp.text()), [generated, depth], "{name}: interpreter\n{}", interp.text());
        check_effects(name, "interpreter", &interp.text());
        for (backend, env, col) in BACKENDS {
            let out = run(name, true, env);
            let text = out.text();
            assert_eq!(out.code, 0, "{name}: {backend}\n{text}");
            assert_eq!(counts(&text), [generated, depth], "{name}: {backend}\n{text}");
            assert!(calls(&text, col) > 0, "{name}: {backend} did not run ({col} calls)\n{text}");
            assert_eq!(text.contains("native code (JIT) ready"), backend == "JIT", "{name}: {backend}\n{text}");
            check_effects(name, backend, &text);
        }
    }
}

/// The same with value store slots (`TLX_VALUE_STORE`, design batch 1):
/// the operations on handles in every executor, against TLC's counts and
/// output, with the store's statistics showing that it was used.
#[test]
fn litmus_specs_agree_with_tlc_with_value_store_slots() {
    for store in STORES {
        for (name, generated, depth) in SPECS {
            for (backend, env, _) in BACKENDS {
                let mut env = env.to_vec();
                env.push(("TLX_VALUE_STORE", store));
                let out = run(name, true, &env);
                let (what, text) = (format!("{name}: {backend}, TLX_VALUE_STORE={store}"), out.text());
                assert_eq!(out.code, 0, "{what}\n{text}");
                assert_eq!(counts(&text), [generated, depth], "{what}\n{text}");
                check_effects(name, &what, &text);
                if store == "all" || name == "ReprExceptEffects" {
                    assert!(text.contains("value store nodes"), "{what}: no value store\n{text}");
                }
            }
        }
        // A replacement that fails on a present key is the run's error.
        for (backend, env, _) in BACKENDS {
            let mut env = env.to_vec();
            env.push(("TLX_VALUE_STORE", store));
            let out = run("ReprExceptError", true, &env);
            let text = out.text();
            assert_ne!(out.code, 0, "{backend}, TLX_VALUE_STORE={store}\n{text}");
            assert!(text.contains("2 states generated, 2 distinct states found"), "{backend}, TLX_VALUE_STORE={store}\n{text}");
        }
    }
}

/// compat.md D-13 (resolved): fixed encodings (`Shape::Fcn` / `Shape::Map`)
/// now preserve how a function's domain was built via `FcnWitness`, while
/// keeping semantic equality and canonical state/`VIEW` fingerprints.
/// `[i \in {1, 2} |-> i]` is equal to the tuple `<<1, 2>>`, so reaching
/// `pc = 1` from `pc = 0` (`[i \in {1, 2} |-> i]`) and from `pc = 5`
/// (`<<1, 2>>`) deduplicates to one state, and EXCEPT with a model-value key
/// leaves the enumerated function unchanged (6 generated / 5 distinct / depth 4)
/// across closure IR, C, and JIT with `TLX_VALUE_STORE` off, `1`, and `all`
/// under `TLX_PARANOID=1`.
#[test]
fn function_witness_is_preserved_in_fixed_encodings() {
    const SPEC: &str = r#"---- MODULE Witness ----
EXTENDS Naturals
CONSTANT m
VARIABLES x, pc
Init == x = <<1, 2>> /\ pc = 0
Next == \/ pc = 0 /\ x' = [i \in {1, 2} |-> i] /\ pc' = 1
        \/ pc = 0 /\ x' = x /\ pc' = 5
        \/ pc = 5 /\ x' = <<1, 2>> /\ pc' = 1
        \/ pc = 1 /\ x' = [x EXCEPT ![m] = 0] /\ pc' = 2
        \/ pc = 2 /\ x' = [x EXCEPT ![1] = 3] /\ pc' = 3
Inv == x \in {<<1, 2>>, <<3, 2>>}
====
"#;
    const CFG: &str = "CONSTANT m = m\nINIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
    let dir = tlx_testkit::TempDir::with_spec("repr-witness", SPEC, CFG);
    let check = |compile: bool, env: &[(&str, &str)]| {
        let mut cmd = tlx_testkit::tlx!();
        cmd.check("Witness.tla").cfg("Witness.cfg").args(["-workers", "1"]).dir(dir.path());
        if compile {
            cmd.arg("-compile").env("TLX_PARANOID", "1").envs(env.iter().copied());
        }
        cmd.run()
    };
    let want =
        ["6 states generated, 5 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 4."];
    let interp = check(false, &[]);
    assert_eq!(counts(&interp.text()), want, "{}", interp.text());
    for (backend, env, _) in BACKENDS {
        for store in ["0", "1", "all"] {
            let mut env = env.to_vec();
            env.push(("TLX_VALUE_STORE", store));
            let out = check(true, &env);
            let text = out.text();
            assert_eq!(out.code, 0, "{backend}, TLX_VALUE_STORE={store}\n{text}");
            assert_eq!(counts(&text), want, "{backend}, TLX_VALUE_STORE={store}\n{text}");
        }
    }
}

/// Enumerated-domain functions (`[k \in {0, 1} |-> 0]`, `[x \in {} |-> ""]`)
/// in state and `VIEW` slots preserve EXCEPT semantics across closure IR, C,
/// and JIT while keeping semantic equality and canonical state/`VIEW`
/// fingerprints (`<<>> = [x \in {} |-> ""]`, `[k \in {0, 1} |-> 0] = [k \in 0..1 |-> 0]`).
#[test]
fn enumerated_domain_functions_in_state_and_view_preserve_except_and_fingerprints() {
    // 1. State variable `[k \in {0, 1} |-> 0]` accepts a model-value EXCEPT
    //    key unchanged, while `[k \in 0..1 |-> 0]` stays equal to it.
    const ENUM_ZERO_ONE: &str = r#"---- MODULE EnumZeroOne ----
EXTENDS Naturals
CONSTANT M
VARIABLES f, n
Init == f = [k \in {0, 1} |-> 0] /\ n = 0
Next == \/ n = 0 /\ n' = 1 /\ f' = [f EXCEPT ![M] = 1]
        \/ n = 1 /\ n' = 2 /\ f' = [f EXCEPT ![0] = 1]
Inv == (n < 2 => f = [k \in 0..1 |-> 0]) /\ (n = 2 => f[0] = 1 /\ f[1] = 0)
====
"#;
    const ENUM_CFG: &str = "CONSTANT M = M\nINIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
    let dir1 = tlx_testkit::TempDir::with_spec("repr-enum-01", ENUM_ZERO_ONE, ENUM_CFG);
    let run_dir = |dir: &std::path::Path, tla: &str, cfg: &str, compile: bool, env: &[(&str, &str)]| {
        let mut cmd = tlx_testkit::tlx!();
        cmd.check(tla).cfg(cfg).args(["-workers", "1"]).dir(dir);
        if compile {
            cmd.arg("-compile").env("TLX_PARANOID", "1").envs(env.iter().copied());
        }
        cmd.run()
    };
    let want1 =
        ["3 states generated, 3 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 3."];
    let interp1 = run_dir(dir1.path(), "EnumZeroOne.tla", "EnumZeroOne.cfg", false, &[]);
    assert_eq!(counts(&interp1.text()), want1, "{}", interp1.text());
    for (backend, env, _) in BACKENDS {
        let out = run_dir(dir1.path(), "EnumZeroOne.tla", "EnumZeroOne.cfg", true, env);
        assert_eq!(out.code, 0, "EnumZeroOne {backend}\n{}", out.text());
        assert_eq!(counts(&out.text()), want1, "EnumZeroOne {backend}\n{}", out.text());
    }

    // 2. Empty enumerated function `[x \in {} |-> ""]` and `("x" :> "a")` with
    //    string-key EXCEPT in VIEW (the FzEmptyFcnExcept pattern) plus mixed
    //    `<<>>` / `[x \in {} |-> ""]` VIEW canonicality.
    const EMPTY_VIEW: &str = r#"---- MODULE EmptyView ----
EXTENDS Naturals, TLC
VARIABLES v1, pc
Init == v1 = [x1 \in {} |-> ""] /\ pc = 0
Next == \/ pc = 0 /\ v1' = ("x" :> "a") /\ pc' = 1
        \/ pc = 0 /\ v1' = <<>> /\ pc' = 2
        \/ pc = 1 /\ v1' = [v1 EXCEPT !["c"] = "c"] /\ pc' = 1
        \/ pc = 2 /\ v1' = [x1 \in {} |-> ""] /\ pc' = 0
View == IF pc = 2 THEN v1 ELSE [v1 EXCEPT !["c"] = "c", ![""] = ""]
Inv == (pc \in {0, 2} => v1 = <<>> /\ v1 = [x1 \in {} |-> ""]) /\ (pc = 1 => v1 = ("x" :> "a"))
====
"#;
    const EMPTY_VIEW_CFG: &str = "INIT Init\nNEXT Next\nVIEW View\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
    let dir2 = tlx_testkit::TempDir::with_spec("repr-empty-view", EMPTY_VIEW, EMPTY_VIEW_CFG);
    let interp2 = run_dir(dir2.path(), "EmptyView.tla", "EmptyView.cfg", false, &[]);
    assert_eq!(interp2.code, 0, "EmptyView interp\n{}", interp2.text());
    let interp2_text = interp2.text();
    let want2 = counts(&interp2_text);
    // `pc = 0` (`[x \in {} |-> ""]`) and `pc = 2` (`<<>>`) share the exact
    // same canonical VIEW fingerprint, so only 2 distinct VIEW classes exist!
    assert_eq!(
        want2,
        ["4 states generated, 2 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 2."],
        "{interp2_text}"
    );
    for (backend, env, _) in BACKENDS {
        for store in ["0", "1", "all"] {
            let mut env = env.to_vec();
            env.push(("TLX_VALUE_STORE", store));
            let out = run_dir(dir2.path(), "EmptyView.tla", "EmptyView.cfg", true, &env);
            assert_eq!(out.code, 0, "EmptyView {backend} store={store}\n{}", out.text());
            assert_eq!(counts(&out.text()), want2, "EmptyView {backend} store={store}\n{}", out.text());
        }
    }

    // 3. Union domains with an empty left operand (`{} \cup (0..1)` and a
    //    runtime `(IF b THEN {} ELSE {0}) \cup (0..1)`) preserve the interval
    //    witness when the evaluator returns the right interval unchanged.
    const UNION_DOM: &str = r#"---- MODULE UnionDom ----
EXTENDS Naturals
CONSTANT M
VARIABLES f, step
Init == f = [k \in {0, 1} |-> 0] /\ step = 0
Next == \/ step = 0 /\ step' = 1 /\ f' = [k \in {} \cup (0..1) |-> 0]
        \/ step = 1 /\ step' = 2 /\ f' = [f EXCEPT ![M] = 1]
====
"#;
    const UNION_DOM_CFG: &str = "CONSTANT M = M\nINIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";
    let dir3 = tlx_testkit::TempDir::with_spec("repr-union-dom", UNION_DOM, UNION_DOM_CFG);
    let interp3 = run_dir(dir3.path(), "UnionDom.tla", "UnionDom.cfg", false, &[]);
    assert_ne!(interp3.code, 0, "UnionDom interp must fail on interval EXCEPT\n{}", interp3.text());
    for (backend, env, _) in BACKENDS {
        let out = run_dir(dir3.path(), "UnionDom.tla", "UnionDom.cfg", true, env);
        let text = out.text();
        assert!(!text.contains("using Dyn layout"), "UnionDom {backend} fell back to Dyn\n{text}");
        assert_eq!(out.code, interp3.code, "UnionDom {backend}\n{text}");
        assert_eq!(counts(&text), counts(&interp3.text()), "UnionDom {backend}\n{text}");
    }

    const RUNTIME_UNION_DOM: &str = r#"---- MODULE RuntimeUnionDom ----
EXTENDS Naturals
CONSTANT M
VARIABLES f, b, step
Init == f = [k \in {0, 1} |-> 0] /\ b \in {FALSE, TRUE} /\ step = 0
Next == \/ step = 0 /\ step' = 1 /\ b' = b /\ f' = [k \in (IF b THEN {} ELSE {0}) \cup (0..1) |-> 0]
        \/ step = 1 /\ step' = 2 /\ b' = b /\ f' = [f EXCEPT ![M] = 1]
====
"#;
    let dir4 = tlx_testkit::TempDir::with_spec("repr-runtime-union-dom", RUNTIME_UNION_DOM, UNION_DOM_CFG);
    let interp4 = run_dir(dir4.path(), "RuntimeUnionDom.tla", "RuntimeUnionDom.cfg", false, &[]);
    assert_ne!(interp4.code, 0, "RuntimeUnionDom interp must fail when b=TRUE\n{}", interp4.text());
    for (backend, env, _) in BACKENDS {
        let out = run_dir(dir4.path(), "RuntimeUnionDom.tla", "RuntimeUnionDom.cfg", true, env);
        let text = out.text();
        assert!(!text.contains("using Dyn layout"), "RuntimeUnionDom {backend} fell back to Dyn\n{text}");
        assert_eq!(out.code, interp4.code, "RuntimeUnionDom {backend}\n{text}");
        assert_eq!(counts(&text), counts(&interp4.text()), "RuntimeUnionDom {backend}\n{text}");
    }

    // 4. `DOMAIN f` on dynamic-witness `Fcn` and `Map` slots preserves the
    //    runtime `Value::Interval` (tuple) vs `Value::Set` (enumerated)
    //    representation when fed into `[k \in DOMAIN f |-> ...]`.
    const DOMAIN_WITNESS_CASES: [(&str, &str, bool); 4] = [
        (
            "DomainFcnTuple",
            r#"---- MODULE DomainFcnTuple ----
EXTENDS Naturals
CONSTANT M
VARIABLES f, pc
Init == f = <<0, 0>> /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ f' = [i \in {1, 2} |-> 0]
        \/ /\ pc = 1 /\ pc' = 2 /\ f' = <<0, 0>>
        \/ /\ pc = 2 /\ pc' = 3 /\ f' = [[k \in DOMAIN f |-> pc] EXCEPT ![M] = 1]
====
"#,
            true,
        ),
        (
            "DomainFcnEnum",
            r#"---- MODULE DomainFcnEnum ----
EXTENDS Naturals
CONSTANT M
VARIABLES f, pc
Init == f = <<0, 0>> /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ f' = [i \in {1, 2} |-> 0]
        \/ /\ pc = 1 /\ pc' = 2 /\ f' = f
        \/ /\ pc = 2 /\ pc' = 3 /\ f' = [[k \in DOMAIN f |-> pc] EXCEPT ![M] = 1]
====
"#,
            false,
        ),
        (
            "DomainMapTuple",
            r#"---- MODULE DomainMapTuple ----
EXTENDS Naturals, TLC
CONSTANT M
VARIABLES f, pc
Init == f = <<>> /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ f' = (1 :> 0)
        \/ /\ pc = 1 /\ pc' = 2 /\ f' = <<>>
        \/ /\ pc = 2 /\ pc' = 3 /\ f' = [[k \in DOMAIN f |-> pc] EXCEPT ![M] = 1]
====
"#,
            true,
        ),
        (
            "DomainMapEnum",
            r#"---- MODULE DomainMapEnum ----
EXTENDS Naturals, TLC
CONSTANT M
VARIABLES f, pc
Init == f = <<>> /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ f' = (1 :> 0)
        \/ /\ pc = 1 /\ pc' = 2 /\ f' = [x \in {} |-> 0]
        \/ /\ pc = 2 /\ pc' = 3 /\ f' = [[k \in DOMAIN f |-> pc] EXCEPT ![M] = 1]
====
"#,
            false,
        ),
    ];
    for (name, spec, expect_err) in DOMAIN_WITNESS_CASES {
        let dir = tlx_testkit::TempDir::with_spec(&format!("repr-{name}"), spec, UNION_DOM_CFG);
        let tla = format!("{name}.tla");
        let cfg = format!("{name}.cfg");
        let interp = run_dir(dir.path(), &tla, &cfg, false, &[]);
        assert_eq!(interp.code != 0, expect_err, "{name} interp\n{}", interp.text());
        for (backend, env, _) in BACKENDS {
            for store in ["0", "1"] {
                let mut env = env.to_vec();
                env.push(("TLX_VALUE_STORE", store));
                let out = run_dir(dir.path(), &tla, &cfg, true, &env);
                let text = out.text();
                assert!(!text.contains("using Dyn layout"), "{name} {backend} store={store} fell back to Dyn\n{text}");
                assert_eq!(out.code, interp.code, "{name} {backend} store={store}\n{text}");
                assert_eq!(counts(&text), counts(&interp.text()), "{name} {backend} store={store}\n{text}");
            }
        }
    }
}

/// Functions used as domain keys preserve their own construction witnesses
/// (`<<0>>` vs `[i \in {1} |-> 0]`) across fixed-domain `Shape::Fcn` widening,
/// decoding, `DOMAIN` extraction, and compiled constructors, while equal
/// functions with differently-witnessed keys still deduplicate to one state
/// and one `VIEW` fingerprint.
#[test]
fn function_domain_key_witnesses_are_preserved_and_canonicalized() {
    const CFG: &str = "CONSTANT M = M\nINIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";
    let run_dir = |dir: &std::path::Path, tla: &str, cfg: &str, compile: bool, env: &[(&str, &str)]| {
        let mut cmd = tlx_testkit::tlx!();
        cmd.check(tla).cfg(cfg).args(["-workers", "1"]).dir(dir);
        if compile {
            cmd.arg("-compile").env("TLX_PARANOID", "1").envs(env.iter().copied());
        }
        cmd.run()
    };

    const CASES: [(&str, &str, bool); 4] = [
        (
            "Key",
            r#"---- MODULE Key ----
EXTENDS Naturals
CONSTANT M
VARIABLES f, pc
Init == f = [k \in {<<0>>} |-> 0] /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ f' = [k \in {[i \in {1} |-> pc]} |-> pc]
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in DOMAIN f : TRUE
                                      IN [k EXCEPT ![M] = 1] = <<0>>
                              /\ UNCHANGED f
====
"#,
            false,
        ),
        (
            "KeyReverse",
            r#"---- MODULE KeyReverse ----
EXTENDS Naturals
CONSTANT M
VARIABLES f, pc
Init == f = [k \in {[i \in {1} |-> 0]} |-> 0] /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ f' = [k \in {<<pc>>} |-> pc]
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in DOMAIN f : TRUE
                                      IN [k EXCEPT ![M] = 1] = <<0>>
                              /\ UNCHANGED f
====
"#,
            true,
        ),
        (
            "KeyConstDom",
            r#"---- MODULE KeyConstDom ----
EXTENDS Naturals
CONSTANT M
VARIABLES f, pc
Init == f = [k \in {<<0>>} |-> 0] /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ f' = [k \in {[i \in {1} |-> 0]} |-> pc]
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in DOMAIN f : TRUE
                                      IN [k EXCEPT ![M] = 1] = <<0>>
                              /\ UNCHANGED f
====
"#,
            false,
        ),
        (
            "KeyConstDomReverse",
            r#"---- MODULE KeyConstDomReverse ----
EXTENDS Naturals
CONSTANT M
VARIABLES f, pc
Init == f = [k \in {[i \in {1} |-> 0]} |-> 0] /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ f' = [k \in {<<0>>} |-> pc]
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in DOMAIN f : TRUE
                                      IN [k EXCEPT ![M] = 1] = <<0>>
                              /\ UNCHANGED f
====
"#,
            true,
        ),
    ];

    for (name, spec, expect_err) in CASES {
        let dir = tlx_testkit::TempDir::with_spec(&format!("repr-{name}"), spec, CFG);
        let tla = format!("{name}.tla");
        let cfg = format!("{name}.cfg");
        let interp = run_dir(dir.path(), &tla, &cfg, false, &[]);
        assert_eq!(interp.code != 0, expect_err, "{name} interp\n{}", interp.text());
        for (backend, env, _) in BACKENDS {
            for store in ["0", "1", "all"] {
                let mut env = env.to_vec();
                env.push(("TLX_VALUE_STORE", store));
                let out = run_dir(dir.path(), &tla, &cfg, true, &env);
                let text = out.text();
                assert!(!text.contains("using Dyn layout"), "{name} {backend} store={store} fell back to Dyn\n{text}");
                assert_eq!(out.code, interp.code, "{name} {backend} store={store}\n{text}");
                assert_eq!(counts(&text), counts(&interp.text()), "{name} {backend} store={store}\n{text}");
            }
        }
    }

    // Equal functions whose keys differ only in construction witness must
    // deduplicate to one distinct state and one VIEW class (both normal and
    // escape mode), while semantic equality `f = [k \in {<<0>>} |-> 0]` holds.
    const KEY_CANON: &str = r#"---- MODULE KeyCanon ----
EXTENDS Naturals
CONSTANT M
VARIABLES f, pc
Init == f = [k \in {<<0>>} |-> 0] /\ pc = 0
Next == \/ pc = 0 /\ pc' = 1 /\ f' = [k \in {[i \in {1} |-> 0]} |-> 0]
        \/ pc = 0 /\ pc' = 2 /\ f' = f
        \/ pc = 2 /\ pc' = 1 /\ f' = [k \in {<<0>>} |-> 0]
        \/ pc = 1 /\ pc' = 3 /\ LET k == CHOOSE x \in DOMAIN f : TRUE
                                IN [k EXCEPT ![M] = 1] = <<0>>
                              /\ UNCHANGED f
Inv == f = [k \in {<<0>>} |-> 0] /\ f = [k \in {[i \in {1} |-> 0]} |-> 0]
====
"#;
    const KEY_CANON_CFG: &str = "CONSTANT M = M\nINIT Init\nNEXT Next\nINVARIANT Inv\nCHECK_DEADLOCK FALSE\n";
    let dir = tlx_testkit::TempDir::with_spec("repr-key-canon", KEY_CANON, KEY_CANON_CFG);
    let interp = run_dir(dir.path(), "KeyCanon.tla", "KeyCanon.cfg", false, &[]);
    assert_eq!(interp.code, 0, "KeyCanon interp\n{}", interp.text());
    let want =
        ["5 states generated, 4 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 3."];
    assert_eq!(counts(&interp.text()), want, "KeyCanon interp\n{}", interp.text());
    for (backend, env, _) in BACKENDS {
        for escape in ["0", "1"] {
            let mut env = env.to_vec();
            env.push(("TLX_ESCAPE", escape));
            let out = run_dir(dir.path(), "KeyCanon.tla", "KeyCanon.cfg", true, &env);
            let text = out.text();
            assert!(!text.contains("using Dyn layout"), "KeyCanon {backend} escape={escape} fell back to Dyn\n{text}");
            assert_eq!(out.code, 0, "KeyCanon {backend} escape={escape}\n{text}");
            assert_eq!(counts(&text), want, "KeyCanon {backend} escape={escape}\n{text}");
        }
    }

    // Shared 3-backend x 4-configuration matrix runner: runs the interpreter
    // once, validates it via `check_interp`, and asserts that every compiled
    // configuration (`store={0,1,all}` and `escape=1`) matches exit code and
    // state counts while satisfying `check_compiled`.
    let check_matrix = |name: &str, spec: &str, cfg: &str, check_interp: &dyn Fn(&str, i32, &str), check_compiled: &dyn Fn(&str, &str)| {
        const CONFIGS: [(&str, (&str, &str)); 4] = [
            ("store=0", ("TLX_VALUE_STORE", "0")),
            ("store=1", ("TLX_VALUE_STORE", "1")),
            ("store=all", ("TLX_VALUE_STORE", "all")),
            ("escape=1", ("TLX_ESCAPE", "1")),
        ];
        let dir = tlx_testkit::TempDir::with_spec(&format!("repr-{name}"), spec, cfg);
        let tla = format!("{name}.tla");
        let cfg_name = format!("{name}.cfg");
        let interp = run_dir(dir.path(), &tla, &cfg_name, false, &[]);
        let interp_text = interp.text();
        let interp_counts = counts(&interp_text);
        check_interp(name, interp.code, &interp_text);
        for (backend, env, _) in BACKENDS {
            for (cfg_label, extra) in CONFIGS {
                let mut env = env.to_vec();
                env.push(extra);
                let out = run_dir(dir.path(), &tla, &cfg_name, true, &env);
                let text = out.text();
                let label = format!("{name} {backend} {cfg_label}");
                assert_eq!(out.code, interp.code, "{label}\n{text}");
                assert_eq!(counts(&text), interp_counts, "{label}\n{text}");
                check_compiled(&label, &text);
            }
        }
    };

    // Nested dynamic witness in a fixed-domain function's range (both in a
    // state variable and in a VIEW): the outer `Shape::Fcn` has a static
    // witness and empty `key_variants`, yet must still canonicalize its range
    // so `[i \in {3} |-> <<0>>]` and `[i \in {3} |-> [k \in {1} |-> 0]]`
    // produce one distinct state / VIEW fingerprint.
    const NESTED_SPECS: [(&str, &str, &str); 2] = [
        (
            "Nested",
            r#"---- MODULE Nested ----
VARIABLE f
Init == f = [i \in {3} |-> <<0>>]
Next == f' = [i \in {3} |-> [k \in {1} |-> 0]]
====
"#,
            "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n",
        ),
        (
            "NestedView",
            r#"---- MODULE NestedView ----
VARIABLE b
Init == b = FALSE
Next == b' = TRUE
V == [i \in {3} |-> IF b THEN [k \in {1} |-> 0] ELSE <<0>>]
====
"#,
            "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\nVIEW V\n",
        ),
    ];
    let want_nested =
        ["2 states generated, 1 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 1."];
    for (name, spec, cfg) in NESTED_SPECS {
        check_matrix(
            name,
            spec,
            cfg,
            &|name, code, text| {
                assert_eq!(code, 0, "{name} interp\n{text}");
                assert_eq!(counts(text), want_nested, "{name} interp\n{text}");
            },
            &|label, text| {
                assert!(!text.contains("using Dyn layout"), "{label} fell back to Dyn\n{text}");
            },
        );
    }

    // Sets whose elements carry dynamic witnesses (falling back to `Shape::Dyn`
    // under `TLX_VALUE_STORE=0`), stored integer intervals, and set operations
    // over constants preserve exact witnesses on surviving elements while
    // keeping visited-state keys semantic.
    const SET_WITNESS_CASES: [(&str, &str); 10] = [
        (
            "SetMember",
            r#"---- MODULE SetMember ----
CONSTANT M
VARIABLES s, pc
Init == s = {[i \in {1} |-> 0]} /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ s' = {<<0>>}
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in s : TRUE
                                      IN [k EXCEPT ![M] = 1] = <<0>>
                              /\ UNCHANGED s
====
"#,
        ),
        (
            "SetRange",
            r#"---- MODULE SetRange ----
CONSTANT M
VARIABLES s, pc
Init == s = {[j \in {3} |-> [i \in {1} |-> 0]]} /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ s' = {[j \in {3} |-> <<0>>]}
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in s : TRUE
                                      IN [k[3] EXCEPT ![M] = 1] = <<0>>
                              /\ UNCHANGED s
====
"#,
        ),
        (
            "StoredDomain",
            r#"---- MODULE StoredDomain ----
EXTENDS Naturals
CONSTANT M
VARIABLES s, f, pc
Init == s = {0,1} /\ f = [k \in {0,1} |-> 0] /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ s' = 0..1 /\ UNCHANGED f
        \/ /\ pc = 1 /\ pc' = 2 /\ f' = [k \in s |-> pc] /\ UNCHANGED s
        \/ /\ pc = 2 /\ pc' = 3 /\ f' = [f EXCEPT ![M] = 1] /\ UNCHANGED s
====
"#,
        ),
        (
            "StoredDomainCup",
            r#"---- MODULE StoredDomainCup ----
EXTENDS Naturals
CONSTANT M
VARIABLES s, f, pc
Init == s = {0,1} /\ f = [k \in {0,1} |-> 0] /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ s' = {} \cup (0..1) /\ UNCHANGED f
        \/ /\ pc = 1 /\ pc' = 2 /\ f' = [k \in s |-> pc] /\ UNCHANGED s
        \/ /\ pc = 2 /\ pc' = 3 /\ f' = [f EXCEPT ![M] = 1] /\ UNCHANGED s
====
"#,
        ),
        (
            "InterKey",
            r#"---- MODULE InterKey ----
CONSTANT M
VARIABLES s, pc
Init == s = {[i \in {1} |-> 0]} /\ pc = 0
Next == /\ pc = 0 /\ pc' = 1
        /\ LET k == CHOOSE x \in ({<<0>>} \cap s) : TRUE
            IN [k EXCEPT ![M] = 1] = <<0>>
        /\ UNCHANGED s
====
"#,
        ),
        (
            "UnionKeyRight",
            r#"---- MODULE UnionKeyRight ----
CONSTANT M
VARIABLES s, pc
Init == s = {[i \in {1} |-> 0]} /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ s' = {}
        \/ /\ pc = 1 /\ pc' = 2
           /\ LET k == CHOOSE x \in (s \cup {<<0>>}) : TRUE
               IN [k EXCEPT ![M] = 1] = <<0>>
           /\ UNCHANGED s
====
"#,
        ),
        (
            "UnionKeyLeft",
            r#"---- MODULE UnionKeyLeft ----
CONSTANT M
VARIABLES s, pc
Init == s = {[i \in {1} |-> 0]} /\ pc = 0
Next == /\ pc = 0 /\ pc' = 1
        /\ LET k == CHOOSE x \in ({<<0>>} \cup s) : TRUE
            IN [k EXCEPT ![M] = 1] = <<0>>
        /\ UNCHANGED s
====
"#,
        ),
        (
            "DiffKey",
            r#"---- MODULE DiffKey ----
CONSTANT M
VARIABLES s, pc
Init == s = {[i \in {1} |-> 0]} /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ s' = {}
        \/ /\ pc = 1 /\ pc' = 2
           /\ LET k == CHOOSE x \in ({<<0>>} \ s) : TRUE
               IN [k EXCEPT ![M] = 1] = <<0>>
           /\ UNCHANGED s
====
"#,
        ),
        (
            "BitSetConstEnum",
            r#"---- MODULE BitSetConstEnum ----
CONSTANT M
VARIABLES s, f, pc
Init == s = {[i \in {1} |-> 0], [i \in {1} |-> 1]} /\ f = [i \in {1} |-> 1] /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ s' = {CHOOSE g \in {<<0>>} : TRUE, f} /\ UNCHANGED f
        \/ /\ pc = 1 /\ pc' = 2
           /\ LET k == CHOOSE x \in s : x[1] = 0
               IN [k EXCEPT ![M] = 1] = <<0>>
           /\ UNCHANGED <<s, f>>
====
"#,
        ),
        (
            "MapInsertConstKey",
            r#"---- MODULE MapInsertConstKey ----
EXTENDS TLC
CONSTANT M
VARIABLES m, pc
Init == m = ([i \in {1} |-> 0] :> 0) @@ ([i \in {1} |-> 1] :> 1) /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ m' = ((CHOOSE g \in {<<0>>} : TRUE) :> pc)
        \/ /\ pc = 1 /\ pc' = 2
           /\ LET k == CHOOSE x \in DOMAIN m : TRUE
               IN [k EXCEPT ![M] = 1] = <<0>>
           /\ UNCHANGED m
====
"#,
        ),
    ];
    for (name, spec) in SET_WITNESS_CASES {
        check_matrix(
            name,
            spec,
            CFG,
            &|name, code, text| {
                assert_ne!(code, 0, "{name} interp must fail on tuple/interval EXCEPT\n{text}");
            },
            &|_, _| {},
        );
    }

    // Semantic deduplication for `Shape::Dyn` sets and intervals: equal sets
    // differing only in element or interval witness must collapse to 1 distinct state.
    const SET_CANON_CASES: [(&str, &str); 2] = [
        (
            "SetCanon",
            r#"---- MODULE SetCanon ----
VARIABLE s
Init == s = {[i \in {1} |-> 0]}
Next == s' = {<<0>>}
====
"#,
        ),
        (
            "IntervalCanon",
            r#"---- MODULE IntervalCanon ----
EXTENDS Naturals
VARIABLE s
Init == s = {0, 1}
Next == s' = 0..1
====
"#,
        ),
    ];
    for (name, spec) in SET_CANON_CASES {
        check_matrix(
            name,
            spec,
            "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n",
            &|name, code, text| {
                assert_eq!(code, 0, "{name} interp\n{text}");
                assert_eq!(counts(text), want_nested, "{name} interp\n{text}");
            },
            &|_, _| {},
        );
    }

    // Set enumeration and set comprehension over dynamic-witness elements must
    // deduplicate semantically (e.g. `Cardinality({<<0>>, [i \in {1} |-> 0]}) = 1`).
    const DUP_CFG: &str = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\nINVARIANT Safe\n";
    const DUP_CASES: [(&str, &str); 2] = [
        (
            "Dup",
            r#"---- MODULE Dup ----
EXTENDS FiniteSets
VARIABLES x,y,pc
Init == x = <<0>> /\ y = [i \in {1} |-> 0] /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ x' = y /\ y' = x
        \/ /\ pc = 1 /\ pc' = 2 /\ Cardinality({x,y}) = 1 /\ UNCHANGED <<x,y>>
Safe == pc # 2
====
"#,
        ),
        (
            "DupMap",
            r#"---- MODULE DupMap ----
EXTENDS FiniteSets
VARIABLES x,y,pc
Init == x = <<0>> /\ y = [i \in {1} |-> 0] /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ x' = y /\ y' = x
        \/ /\ pc = 1 /\ pc' = 2 /\ Cardinality({IF b THEN x ELSE y : b \in BOOLEAN}) = 1 /\ UNCHANGED <<x,y>>
Safe == pc # 2
====
"#,
        ),
    ];
    for (name, spec) in DUP_CASES {
        check_matrix(
            name,
            spec,
            DUP_CFG,
            &|name, code, text| {
                assert_ne!(code, 0, "{name} interp must violate Safe\n{text}");
                assert!(text.contains("Invariant Safe is violated"), "{name} interp\n{text}");
            },
            &|label, text| {
                assert!(text.contains("Invariant Safe is violated"), "{label}\n{text}");
            },
        );
    }

    // Intersection with a non-reducible left operand (`[D -> R]` or `A \X B`,
    // constant, dynamic, behind conditionals, passed through operators, or
    // bound from iterating a conditional set) filters the reducible right
    // operand in TLC, so the surviving element must retain the right operand's
    // witness.
    const LAZY_CAP_CFG: &str = "CONSTANT M = M\nINIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\nINVARIANT Safe\n";
    const LAZY_CAP_CASES: [(&str, &str, bool); 15] = [
        (
            "FcnSetCap",
            r#"---- MODULE FcnSetCap ----
CONSTANT M
VARIABLES s,z,pc
Init == s = {<<0,0>>} /\ z = {[i \in {1,2} |-> 0]} /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ z' = [{1,2} -> {0}] \cap s /\ UNCHANGED <<s>>
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in z : TRUE IN [k EXCEPT ![M] = 1] = <<0,0>> /\ UNCHANGED <<s,z>>
Safe == pc # 2
====
"#,
            false,
        ),
        (
            "ProductCap",
            r#"---- MODULE ProductCap ----
CONSTANT M
VARIABLES s,z,pc
Init == s = {[i \in {1,2} |-> 0]} /\ z = {<<0,0>>} /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ z' = ({0} \X {0}) \cap s /\ UNCHANGED <<s>>
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in z : TRUE IN [k EXCEPT ![M] = 1] = <<0,0>> /\ UNCHANGED <<s,z>>
Safe == pc # 2
====
"#,
            true,
        ),
        (
            "DynProductCap",
            r#"---- MODULE DynProductCap ----
CONSTANT M
VARIABLES a,s,z,pc
Init == a = {0} /\ s = {[i \in {1,2} |-> 0]} /\ z = {<<0,0>>} /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ z' = (a \X a) \cap s /\ UNCHANGED <<a,s>>
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in z : TRUE IN [k EXCEPT ![M] = 1] = <<0,0>> /\ UNCHANGED <<a,s,z>>
Safe == pc # 2
====
"#,
            true,
        ),
        (
            "ConditionalCap",
            r#"---- MODULE ConditionalCap ----
CONSTANT M
VARIABLES a,s,z,pc
Init == a = {0} /\ s = {[i \in {1,2} |-> 0]} /\ z = {<<0,0>>} /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ z' = (IF pc = 0 THEN a \X a ELSE z) \cap s /\ UNCHANGED <<a,s>>
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in z : TRUE IN [k EXCEPT ![M] = 1] = <<0,0>> /\ UNCHANGED <<a,s,z>>
Safe == pc # 2
====
"#,
            true,
        ),
        (
            "ConditionalRevConstCap",
            r#"---- MODULE ConditionalRevConstCap ----
CONSTANT M
VARIABLES s,z,pc
Init == s = {[i \in {1,2} |-> 0]} /\ z = {<<0,0>>} /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ z' = (IF pc # 0 THEN z ELSE ({0} \X {0})) \cap s /\ UNCHANGED <<s>>
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in z : TRUE IN [k EXCEPT ![M] = 1] = <<0,0>> /\ UNCHANGED <<s,z>>
Safe == pc # 2
====
"#,
            true,
        ),
        (
            "IdCap",
            r#"---- MODULE IdCap ----
CONSTANT M
VARIABLES a,s,z,pc
Id(x) == x
Init == a = {0} /\ s = {[i \in {1,2} |-> 0]} /\ z = {<<0,0>>} /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ z' = (Id(a \X a)) \cap s /\ UNCHANGED <<a,s>>
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in z : TRUE IN [k EXCEPT ![M] = 1] = <<0,0>> /\ UNCHANGED <<a,s,z>>
Safe == pc # 2
====
"#,
            true,
        ),
        (
            "RecordBranch",
            r#"---- MODULE RecordBranch ----
CONSTANT M
VARIABLES b,a,s,z,pc
Init == b = [q |-> {<<0,0>>}] /\ a = {0} /\ s = {[i \in {1,2} |-> 0]} /\ z = {<<0,0>>} /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ z' = (IF pc = 0 THEN [q |-> a \X a] ELSE b).q \cap s /\ UNCHANGED <<b,a,s>>
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in z : TRUE IN [k EXCEPT ![M] = 1] = <<0,0>> /\ UNCHANGED <<b,a,s,z>>
Safe == pc # 2
====
"#,
            true,
        ),
        (
            "TupleBranch",
            r#"---- MODULE TupleBranch ----
CONSTANT M
VARIABLES b,a,s,z,pc
Init == b = <<{<<0,0>>}>> /\ a = {0} /\ s = {[i \in {1,2} |-> 0]} /\ z = {<<0,0>>} /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ z' = (IF pc = 0 THEN <<a \X a>> ELSE b)[1] \cap s /\ UNCHANGED <<b,a,s>>
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in z : TRUE IN [k EXCEPT ![M] = 1] = <<0,0>> /\ UNCHANGED <<b,a,s,z>>
Safe == pc # 2
====
"#,
            true,
        ),
        (
            "TupleConstThenBranch",
            r#"---- MODULE TupleConstThenBranch ----
CONSTANT M
VARIABLES b,s,z,pc
Init == b = <<{<<0,0>>}>> /\ s = {[i \in {1,2} |-> 0]} /\ z = {<<0,0>>} /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ z' = (IF pc = 0 THEN <<{0} \X {0}>> ELSE b)[1] \cap s /\ UNCHANGED <<b,s>>
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in z : TRUE IN [k EXCEPT ![M] = 1] = <<0,0>> /\ UNCHANGED <<b,s,z>>
Safe == pc # 2
====
"#,
            true,
        ),
        (
            "UnionOfProducts",
            r#"---- MODULE UnionOfProducts ----
CONSTANT M
VARIABLES b,a,s,z,pc
Init == b = {<<0,0>>} /\ a = {0} /\ s = {[i \in {1,2} |-> 0]} /\ z = {<<0,0>>} /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ z' = (IF pc = 0 THEN UNION {a \X a : i \in a} ELSE b) \cap s /\ UNCHANGED <<b,a,s>>
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in z : TRUE IN [k EXCEPT ![M] = 1] = <<0,0>> /\ UNCHANGED <<b,a,s,z>>
Safe == pc # 2
====
"#,
            true,
        ),
        (
            "RecursiveLazyCap",
            r#"---- MODULE RecursiveLazyCap ----
EXTENDS Naturals
CONSTANT M
VARIABLES a,s,z,pc
RECURSIVE R(_)
R(n) == IF n = 0 THEN {<<0,0>>} ELSE IF n = 1 THEN a \X a ELSE R(n - 1)
Init == a = {0} /\ s = {[i \in {1,2} |-> 0]} /\ z = {<<0,0>>} /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ z' = R(pc + 2) \cap s /\ UNCHANGED <<a,s>>
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in z : TRUE IN [k EXCEPT ![M] = 1] = <<0,0>> /\ UNCHANGED <<a,s,z>>
Safe == pc # 2
====
"#,
            true,
        ),
        (
            "RecursiveEagerArmCap",
            r#"---- MODULE RecursiveEagerArmCap ----
EXTENDS Naturals
CONSTANT M
VARIABLES s,z,pc
RECURSIVE R(_)
R(n) == IF n = 0 THEN {<<n,n>>} ELSE R(n - 1)
Init == s = {<<0,0>>} /\ z = {[i \in {1,2} |-> 0]} /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ z' = (z \cap R(pc + 1)) /\ UNCHANGED <<s>>
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in z : TRUE IN [k EXCEPT ![M] = 1] = <<0,0>> /\ UNCHANGED <<s,z>>
Safe == pc # 2
====
"#,
            true,
        ),
        (
            "ChooseNested",
            r#"---- MODULE ChooseNested ----
CONSTANT M
VARIABLES b,a,s,z,pc
Init == b = {{<<0,0>>}} /\ a = {0} /\ s = {[i \in {1,2} |-> 0]} /\ z = {<<0,0>>} /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ z' = (CHOOSE q \in (IF pc = 0 THEN {a \X a} ELSE b) : TRUE) \cap s /\ UNCHANGED <<b,a,s>>
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in z : TRUE IN [k EXCEPT ![M] = 1] = <<0,0>> /\ UNCHANGED <<b,a,s,z>>
Safe == pc # 2
====
"#,
            true,
        ),
        (
            "ChooseNestedConst",
            r#"---- MODULE ChooseNestedConst ----
CONSTANT M
VARIABLES b,s,z,pc
Init == b = {{<<0,0>>}} /\ s = {[i \in {1,2} |-> 0]} /\ z = {<<0,0>>} /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ z' = (CHOOSE q \in (IF pc = 0 THEN {{0} \X {0}} ELSE b) : TRUE) \cap s /\ UNCHANGED <<b,s>>
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in z : TRUE IN [k EXCEPT ![M] = 1] = <<0,0>> /\ UNCHANGED <<b,s,z>>
Safe == pc # 2
====
"#,
            true,
        ),
        (
            "ExistsNested",
            r#"---- MODULE ExistsNested ----
CONSTANT M
VARIABLES b,a,s,z,pc
Init == b = {{<<0,0>>}} /\ a = {0} /\ s = {[i \in {1,2} |-> 0]} /\ z = {<<0,0>>} /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ (\E q \in (IF pc = 0 THEN {a \X a} ELSE b) : z' = q \cap s) /\ UNCHANGED <<b,a,s>>
        \/ /\ pc = 1 /\ pc' = 2 /\ LET k == CHOOSE x \in z : TRUE IN [k EXCEPT ![M] = 1] = <<0,0>> /\ UNCHANGED <<b,a,s,z>>
Safe == pc # 2
====
"#,
            true,
        ),
    ];
    for (name, spec, expect_safe_violated) in LAZY_CAP_CASES {
        check_matrix(
            name,
            spec,
            LAZY_CAP_CFG,
            &|name, code, text| {
                assert_ne!(code, 0, "{name} interp\n{text}");
                assert_eq!(text.contains("Invariant Safe is violated"), expect_safe_violated, "{name} interp\n{text}");
            },
            &|label, text| {
                assert_eq!(text.contains("Invariant Safe is violated"), expect_safe_violated, "{label}\n{text}");
            },
        );
    }

    // Assignment from a lazy union must preserve enumeration multiplicity
    // (11 generated, 7 distinct) rather than deduplicating overlapping products.
    const OVERLAP: &str = r#"---- MODULE Overlap ----
VARIABLES a, b, pc, x
Init == a = {0,2} /\ b = {0,1,2} /\ pc = 0 /\ x = <<0,0>>
Next == /\ pc = 0 /\ pc' = 1
        /\ x' \in UNION {a \X a, a \X b}
        /\ UNCHANGED <<a,b>>
====
"#;
    let want_overlap =
        ["11 states generated, 7 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 2."];
    check_matrix(
        "Overlap",
        OVERLAP,
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n",
        &|name, code, text| {
            assert_eq!(code, 0, "{name} interp\n{text}");
            assert_eq!(counts(text), want_overlap, "{name} interp\n{text}");
        },
        &|_, _| {},
    );

    // `IsFiniteSet` on a lazy filter over a finite Cartesian product establishes
    // finiteness from the product alone without executing the filter predicate.
    const FINITE_FILTER: &str = r#"---- MODULE FiniteFilter ----
EXTENDS TLC, FiniteSets
VARIABLES a, pc
Init == a = {0,1} /\ pc = 0
Next == pc = 0 /\ IsFiniteSet({q \in a \X a : PrintT(<<"predicate",q>> )}) /\ pc' = 1 /\ a' = a
====
"#;
    let want_finite =
        ["2 states generated, 2 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 2."];
    check_matrix(
        "FiniteFilter",
        FINITE_FILTER,
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n",
        &|name, code, text| {
            assert_eq!(code, 0, "{name} interp\n{text}");
            assert_eq!(counts(text), want_finite, "{name} interp\n{text}");
            assert!(!text.contains("predicate"), "{name} interp executed lazy predicate\n{text}");
        },
        &|label, text| assert!(!text.contains("predicate"), "{label} executed lazy predicate\n{text}"),
    );

    // Assignment over a Cartesian product whose factor is a lazy union must
    // preserve the factor's enumeration multiplicity (21 generated, 13 distinct).
    const PRODUCT_OVERLAP: &str = r#"---- MODULE ProductOverlap ----
VARIABLES a, b, pc, x
Init == a = {0,2} /\ b = {0,1,2} /\ pc = 0 /\ x = <<<<0,0>>,0>>
Next == /\ pc = 0 /\ pc' = 1
        /\ x' \in (UNION {a \X a, a \X b}) \X a
        /\ UNCHANGED <<a,b>>
====
"#;
    let want_prod_overlap =
        ["21 states generated, 13 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 2."];
    check_matrix(
        "ProductOverlap",
        PRODUCT_OVERLAP,
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n",
        &|name, code, text| {
            assert_eq!(code, 0, "{name} interp\n{text}");
            assert_eq!(counts(text), want_prod_overlap, "{name} interp\n{text}");
        },
        &|_, _| {},
    );

    // Membership in a conditional lazy filter over a Cartesian product must
    // evaluate the filter predicate only for the queried element (once), not
    // materialize the whole filter into the other branch's bitset encoding.
    const GUARDED_PRINT: &str = r#"---- MODULE GuardedPrint ----
EXTENDS TLC
VARIABLES a, b, pc
Init == a = {0,1} /\ b = {<<0,0>>,<<0,1>>,<<1,0>>,<<1,1>>} /\ pc = 0
Next == /\ pc = 0
        /\ <<0,0>> \in (IF pc = 0 THEN {q \in a \X a : PrintT(<<"predicate", q>>)} ELSE b)
        /\ pc' = 1 /\ UNCHANGED <<a,b>>
====
"#;
    check_matrix(
        "GuardedPrint",
        GUARDED_PRINT,
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n",
        &|name, code, text| {
            assert_eq!(code, 0, "{name} interp\n{text}");
            assert_eq!(counts(text), want_finite, "{name} interp\n{text}");
            assert_eq!(text.matches("predicate").count(), 1, "{name} interp predicate count\n{text}");
        },
        &|label, text| assert_eq!(text.matches("predicate").count(), 1, "{label} predicate count\n{text}"),
    );

    // Unparenthesized n-ary Cartesian products (`a \X b \X c`) emit a single
    // `Times` node with all factors; the binary bitset specialization must
    // leave wider products to the general path rather than dropping factors.
    const NARY_PRODUCT_CFG: &str = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\nINVARIANT Safe\n";
    const NARY_PRODUCT_CASES: [(&str, &str); 2] = [
        (
            "ThreeFactors",
            r#"---- MODULE ThreeFactors ----
EXTENDS FiniteSets
VARIABLES a, pc
Init == a = {0,1} /\ pc = 0
Next == /\ pc = 0
        /\ Cardinality(a \X a \X a) = 8
        /\ pc' = 1
        /\ UNCHANGED a
Safe == pc = 0
====
"#,
        ),
        (
            "TripleCard",
            r#"---- MODULE TripleCard ----
EXTENDS FiniteSets, Sequences
VARIABLES a,b,pc
Init == a = {0,2} /\ b = {0,1,2} /\ pc = 0
Next == pc = 0 /\ Cardinality(a \X b \X a) = 12 /\ pc' = 1 /\ UNCHANGED <<a,b>>
Safe == pc = 0
====
"#,
        ),
    ];
    for (name, spec) in NARY_PRODUCT_CASES {
        check_matrix(
            name,
            spec,
            NARY_PRODUCT_CFG,
            &|name, code, text| {
                assert_ne!(code, 0, "{name} interp must violate Safe\n{text}");
                assert!(text.contains("Invariant Safe is violated"), "{name} interp\n{text}");
            },
            &|label, text| assert!(text.contains("Invariant Safe is violated"), "{label}\n{text}"),
        );
    }

    // `DOMAIN f` preserves interval vs. enumerated witness: `[DOMAIN f -> {0}]`
    // inherits an interval domain from `[0..1 -> {0}]` (rejecting non-integer
    // EXCEPT key `M` like Java TLC), whereas `[{0,1} -> {0}]` yields an
    // enumerated domain (leaving `g` unchanged and succeeding with 3 distinct
    // states). A mixed dynamic-witness slot reflects its runtime witness.
    const INTERVAL_DOMAIN_CFG: &str = "CONSTANT M = M\nINIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";
    const INTERVAL_DOMAIN: &str = r#"---- MODULE IntervalDomain ----
EXTENDS Naturals
CONSTANT M
VARIABLES f, g, pc
Init == /\ f \in [0..1 -> {0}] /\ g = <<>> /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ g' \in [DOMAIN f -> {0}] /\ UNCHANGED f
        \/ /\ pc = 1 /\ pc' = 2 /\ g' = [g EXCEPT ![M] = 1] /\ UNCHANGED f
====
"#;
    check_matrix(
        "IntervalDomain",
        INTERVAL_DOMAIN,
        INTERVAL_DOMAIN_CFG,
        &|name, code, text| assert_ne!(code, 0, "{name} interp must reject non-integer EXCEPT key M\n{text}"),
        &|_, _| {},
    );

    const ENUM_DOMAIN: &str = r#"---- MODULE EnumDomain ----
EXTENDS Naturals
CONSTANT M
VARIABLES f, g, pc
Init == /\ f \in [{0,1} -> {0}] /\ g = <<>> /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ g' \in [DOMAIN f -> {0}] /\ UNCHANGED f
        \/ /\ pc = 1 /\ pc' = 2 /\ g' = [g EXCEPT ![M] = 1] /\ UNCHANGED f
====
"#;
    let want_enum_domain =
        ["3 states generated, 3 distinct states found, 0 states left on queue.", "The depth of the complete state graph search is 3."];
    check_matrix(
        "EnumDomain",
        ENUM_DOMAIN,
        INTERVAL_DOMAIN_CFG,
        &|name, code, text| {
            assert_eq!(code, 0, "{name} interp must succeed\n{text}");
            assert_eq!(counts(text), want_enum_domain, "{name} interp\n{text}");
        },
        &|_, _| {},
    );

    const MIXED_DOMAIN: &str = r#"---- MODULE MixedDomain ----
EXTENDS Naturals
CONSTANT M
VARIABLES f, g, pc
Init == /\ f = [k \in {0,1} |-> 0] /\ g = <<>> /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ f' = [k \in 0..1 |-> 0] /\ UNCHANGED g
        \/ /\ pc = 1 /\ pc' = 2 /\ g' \in [DOMAIN f -> {0}] /\ UNCHANGED f
        \/ /\ pc = 2 /\ pc' = 3 /\ g' = [g EXCEPT ![M] = 1] /\ UNCHANGED f
====
"#;
    check_matrix(
        "MixedDomain",
        MIXED_DOMAIN,
        INTERVAL_DOMAIN_CFG,
        &|name, code, text| assert_ne!(code, 0, "{name} interp must reject non-integer EXCEPT key M\n{text}"),
        &|_, _| {},
    );

    // Intersecting or differencing a sorted-array set with a non-reducible lazy
    // right operand (e.g. a Cartesian product larger than the left set's layout
    // capacity) must test membership lazily without coercing the product into
    // the sorted-array layout.
    const SORTED_RIGHT_LAZY: &str = r#"---- MODULE SortedRightLazy ----
EXTENDS Naturals
VARIABLES s, a, pc
Init == s = {<<[i \in 1..3 |-> 0], [i \in 1..3 |-> 0]>>}
     /\ a = {[i \in 1..3 |-> 0], [i \in 1..3 |-> 1]}
     /\ pc = 0
Next == \/ /\ pc = 0 /\ pc' = 1 /\ s' = s \cap (a \X a) /\ UNCHANGED a
        \/ /\ pc = 1 /\ pc' = 2 /\ s' = s \ (a \X a) /\ UNCHANGED a
====
"#;
    let dir_srl =
        tlx_testkit::TempDir::with_spec("repr-SortedRightLazy", SORTED_RIGHT_LAZY, "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n");
    let interp_srl = run_dir(dir_srl.path(), "SortedRightLazy.tla", "SortedRightLazy.cfg", false, &[]);
    assert_eq!(interp_srl.code, 0, "SortedRightLazy interp\n{}", interp_srl.text());
    for (backend, env, _) in BACKENDS {
        let out = run_dir(dir_srl.path(), "SortedRightLazy.tla", "SortedRightLazy.cfg", true, env);
        assert_eq!(out.code, 0, "SortedRightLazy {backend}\n{}", out.text());
        assert_eq!(counts(&out.text()), counts(&interp_srl.text()), "SortedRightLazy {backend}\n{}", out.text());
    }
}
