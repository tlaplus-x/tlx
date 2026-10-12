//! Unbounded histories can have finite, observation-preserving summaries.

use std::time::Duration;

const SPEC: &str = r#"---- MODULE History ----
EXTENDS Naturals, Sequences
VARIABLE h, value
Event == [kind: {"W", "R"}, data: {0, 1}]
Init == /\ h = <<[kind |-> "W", data |-> 0]>> /\ value = 0
Write == \E x \in {0, 1}:
           /\ value' = x
           /\ h' = Append(h, [kind |-> "W", data |-> x])
Read == /\ h' = Append(h, [kind |-> "R", data |-> value])
        /\ UNCHANGED value
Next == Write \/ Read
TypeOK == /\ h \in Seq(Event) /\ value \in {0, 1}
Consistent == \A i \in 1..Len(h):
                h[i].kind = "W" \/
                \E j \in 1..i: h[j].kind = "W" /\ h[j].data = h[i].data
Spec == Init /\ [][Next]_<<h, value>>
====
"#;
const CFG: &str = "SPECIFICATION Spec\nINVARIANTS TypeOK Consistent\n";

// A witness is permanent even though appending W makes the same predicate
// false when evaluated against the *final* element set instead of its prefix.
const EXISTENTIAL: &str = r#"---- MODULE History ----
EXTENDS Naturals, Sequences
VARIABLE h, witnessed
Seen == \E i \in 1..Len(h):
          h[i] = "R" /\ \A j \in 1..i: h[j] # "W"
Init == /\ h = <<>> /\ witnessed = FALSE
Next == \E event \in {"R", "W"}:
          /\ h' = Append(h, event) /\ witnessed' = Seen
TypeOK == /\ h \in Seq({"R", "W"}) /\ witnessed \in BOOLEAN
Safe == ~(witnessed /\ \E i \in 1..Len(h): h[i] = "W")
====
"#;

#[test]
fn unproved_history_transfer_is_refused_and_preserves_old_witnesses() {
    for (invariants, code) in [("TypeOK Safe", 12)] {
        let cfg = format!("INIT Init\nNEXT Next\nINVARIANTS {invariants}\n");
        let dir = tlx_testkit::TempDir::with_spec("history-existential", EXISTENTIAL, &cfg);
        for (tier, args, env) in tlx_testkit::cli::TIERS {
            let run = tlx_testkit::tlx_default!()
                .check("History.tla")
                .args(args)
                .args(["-optimize", "-noautosymmetry"])
                .envs(env.iter().copied())
                .env("TLX_PARANOID", "1")
                .dir(&dir)
                .timeout(Duration::from_secs(60))
                .run();
            assert_eq!(run.code, code, "{tier}: {}", run.text());
            assert!(!run.stdout.contains("history-summary-projection"), "{tier}: {}", run.text());
            if code == 0 {
                assert!(run.stdout.contains("6 distinct states found"), "{tier}: {}", run.text());
            } else {
                assert!(run.stdout.contains("Invariant Safe is violated"), "{tier}: {}", run.text());
                assert!(run.stdout.contains("<<\"R\", \"W\">>"), "{tier}: {}", run.text());
            }
        }
    }
}

#[test]
fn unproved_history_transfer_keeps_a_finite_prefix_and_refusal_boundaries() {
    let spec = EXISTENTIAL
        .replace("VARIABLE h, witnessed", "VARIABLE h, witnessed, budget")
        .replace("witnessed = FALSE", "witnessed = FALSE /\\ budget = 0")
        .replace("Next ==", "Next == /\\ budget < 4 /\\ budget' = budget + 1 /\\");
    let cfg = "INIT Init\nNEXT Next\nINVARIANT TypeOK\nCHECK_DEADLOCK FALSE\n";
    for (flags, count) in [(vec![], 31), (vec!["-optimize"], 31), (vec!["-optimize", "-tlc"], 31)] {
        let dir = tlx_testkit::TempDir::with_spec("history-existential-bounded", &spec, cfg);
        let run = tlx_testkit::tlx_default!()
            .check("History.tla")
            .args(["-interp", "-noautosymmetry"])
            .args(flags)
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{}", run.text());
        assert!(run.stdout.contains(&format!("{count} distinct states found")), "{}", run.text());
        assert!(!run.stdout.contains("history-summary-projection"), "{}", run.text());
    }
    for spec in [
        spec.replace("h[i] = \"R\"", "i = 1 /\\ h[i] = \"R\""),
        spec.replace("h[i] = \"R\"", "~witnessed /\\ h[i] = \"R\""),
        spec.replace("1..i:", "i..Len(h):"),
    ] {
        let dir = tlx_testkit::TempDir::with_spec("history-existential-refusal", &spec, cfg);
        let run = tlx_testkit::tlx_default!()
            .check("History.tla")
            .args(["-interp", "-optimize", "-noautosymmetry"])
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{}", run.text());
        assert!(!run.stdout.contains("history-summary-projection"), "{}", run.text());
    }
}

#[test]
fn unbounded_history_finishes_in_all_tiers() {
    let dir = tlx_testkit::TempDir::with_spec("history-finite", SPEC, CFG);
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("History.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{tier}: {}", run.text());
        assert!(run.stdout.contains("history-summary-projection"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("10 distinct states found"), "{tier}: {}", run.text());
    }
}

#[test]
fn history_failure_has_a_concrete_counterexample() {
    let spec = SPEC.replace("data |-> value])", "data |-> 1])");
    let dir = tlx_testkit::TempDir::with_spec("history-failure", &spec, CFG);
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("History.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 12, "{tier}: {}", run.text());
        assert!(run.stdout.contains("history-summary-projection"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("Invariant Consistent is violated"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("kind |-> \"R\""), "{tier}: {}", run.text());
    }
}

#[test]
fn equal_element_sets_retain_different_prefix_verdicts() {
    let spec = r#"---- MODULE History ----
EXTENDS Naturals, Sequences
VARIABLE h, pc, result
Init == /\ h = <<>> /\ pc = "start" /\ result = ""
PrefixOK == \A i \in 1..Len(h): h[i] = "W" \/ \E j \in 1..i: h[j] = "W"
Step(from, to, event) == /\ pc = from /\ pc' = to
                         /\ h' = Append(h, event) /\ UNCHANGED result
Next == \/ Step("start", "aGood", "W")
        \/ Step("start", "bBad", "R")
        \/ Step("aGood", "done", "R")
        \/ Step("bBad", "done", "W")
        \/ /\ pc = "done" /\ result' = IF PrefixOK THEN "good" ELSE "bad"
           /\ UNCHANGED <<h, pc>>
Safe == result # "bad"
====
"#;
    let dir = tlx_testkit::TempDir::with_spec("history-prefix-bit", spec, "INIT Init\nNEXT Next\nINVARIANT Safe\n");
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("History.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 12, "{tier}: {}", run.text());
        assert!(!run.stdout.contains("history-summary-projection"), "{tier}: {}", run.text());
        assert!(run.stdout.contains("<<\"R\", \"W\">>"), "{tier}: {}", run.text());
    }
}

// A separate finite control bound allows refusal and compatibility checks to
// finish without constraining history length in the observation language.
fn bounded() -> String {
    SPEC.replace("VARIABLE h, value", "VARIABLE h, value, budget")
        .replace("value = 0\n", "value = 0 /\\ budget = 0\n")
        .replace("Next == Write \\/ Read", "Next == /\\ budget < 3 /\\ budget' = budget + 1 /\\ (Write \\/ Read)")
        .replace("<<h, value>>", "<<h, value, budget>>")
}

#[test]
fn unsupported_history_observations_and_transfers_refuse() {
    for (spec, code) in [
        (bounded().replace("1..i:", "i..Len(h):"), 12),
        (bounded().replace("h[i].kind = \"W\" \\/", "i = 1 \\/ h[i].kind = \"W\" \\/"), 0),
        (bounded().replace("h[j].data = h[i].data", "h[j].data = value"), 12),
        (bounded().replace("h[j].data = h[i].data", "h[j].missing = h[i].data"), 76),
        (bounded().replace("Append(h, [kind |-> \"R\", data |-> value])", "Tail(h)"), 255),
        (
            bounded()
                .replace("h' = Append(h, [kind |-> \"R\", data |-> value])", "h' = h /\\ h' = Append(h, [kind |-> \"R\", data |-> value])"),
            0,
        ),
        (bounded().replace("data: {0, 1}", "data: {0}"), 12),
    ] {
        let dir = tlx_testkit::TempDir::with_spec("history-refusal", &spec, &format!("{CFG}CHECK_DEADLOCK FALSE\n"));
        let run = tlx_testkit::tlx_default!()
            .check("History.tla")
            .args(["-interp", "-optimize", "-noautosymmetry"])
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert!(!run.stdout.contains("history-summary-projection"), "{}", run.text());
        assert_eq!(run.code, code, "{}", run.text());
    }
}

#[test]
fn history_projection_preserves_deadlock() {
    let dir = tlx_testkit::TempDir::with_spec("history-deadlock", &bounded(), CFG);
    for (tier, args, env) in tlx_testkit::cli::TIERS {
        let run = tlx_testkit::tlx_default!()
            .check("History.tla")
            .args(args)
            .args(["-optimize", "-noautosymmetry"])
            .envs(env.iter().copied())
            .env("TLX_PARANOID", "1")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 11, "{tier}: {}", run.text());
        assert!(run.stdout.contains("history-summary-projection"), "{tier}: {}", run.text());
    }
}

#[test]
fn exact_length_and_tlc_mode_keep_the_concrete_history() {
    let spec = format!("{}\n", bounded());
    for (cfg, flags) in [
        (format!("{CFG}CHECK_DEADLOCK FALSE\n"), vec!["-optimize", "-tlc"]),
        (format!("{CFG}CHECK_DEADLOCK FALSE\nCONSTRAINT Limit\n"), vec!["-optimize"]),
    ] {
        let spec = spec.replace("====", "Limit == Len(h) <= 3\n====");
        let dir = tlx_testkit::TempDir::with_spec("history-exact", &spec, &cfg);
        let run = tlx_testkit::tlx_default!()
            .check("History.tla")
            .arg("-interp")
            .args(flags)
            .arg("-noautosymmetry")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{}", run.text());
        assert!(!run.stdout.contains("history-summary-projection"), "{}", run.text());
    }
}

#[test]
fn finite_control_prefix_reduces_states_and_tlc_bypasses() {
    let dir = tlx_testkit::TempDir::with_spec("history-bounded", &bounded(), &format!("{CFG}CHECK_DEADLOCK FALSE\n"));
    for (flags, count) in [(vec![], 40), (vec!["-optimize"], 19), (vec!["-optimize", "-tlc"], 40)] {
        let run = tlx_testkit::tlx_default!()
            .check("History.tla")
            .arg("-interp")
            .args(flags)
            .arg("-noautosymmetry")
            .dir(&dir)
            .timeout(Duration::from_secs(60))
            .run();
        assert_eq!(run.code, 0, "{}", run.text());
        assert!(run.stdout.contains(&format!("{count} distinct states found")), "{}", run.text());
        assert_eq!(run.stdout.contains("history-summary-projection"), count == 19, "{}", run.text());
    }
}
