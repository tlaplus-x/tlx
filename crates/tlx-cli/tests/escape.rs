//! Local deoptimization must not restart or duplicate the search.
use tlx_testkit::cli::counts;

const GROWING_SPEC: &str = r#"---- MODULE Escape ----
EXTENDS Naturals, Sequences, TLC
VARIABLES x, s
Init == x = 0 /\ s = "n0"
Next == \/ x < 79 /\ x' = x + 1 /\ s' = "n" \o ToString(x')
        \/ x = 79 /\ x' = 0 /\ s' = "n0"
===="#;

#[test]
fn growing_shapes_do_not_restart_or_duplicate_states() {
    let cfg = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";
    let dir = tlx_testkit::TempDir::with_spec("escape", GROWING_SPEC, cfg);
    for (backend, no_native) in [("0", "0"), ("1", "0"), ("only", "0"), ("0", "1")] {
        let mut cmd = tlx_testkit::tlx!();
        let r = cmd
            .args(["check", "Escape.tla", "-config", "Escape.cfg", "-tlc", "-compile", "-workers", "1", "-stats", "json"])
            .dir(&dir)
            .envs([("TLX_ESCAPE", "1"), ("TLX_PRERUN", "1"), ("TLX_PRERUN_REUSE", "0"), ("TLX_PARANOID", "1"), ("TLX_JIT", backend)])
            .env("TLX_NO_NATIVE", no_native)
            .run();
        let text = r.text();
        assert_eq!(r.code, 0, "{text}");
        assert_eq!(
            counts(&text),
            [
                "81 states generated, 80 distinct states found, 0 states left on queue.",
                "The depth of the complete state graph search is 80."
            ],
            "{text}"
        );
        assert!(!text.contains("compile: layout miss"), "{text}");
        assert!(text.contains("escape deoptimizations"), "{text}");
        assert!(text.contains("escape recompilations"), "{text}");
        let stats = text.lines().find(|l| l.starts_with("{\"sample_every\"")).expect("stats JSON");
        let metric = |name: &str| -> u64 {
            let marker = format!("\"{name}\":");
            stats.split_once(&marker).expect("metric present").1.split([',', '}']).next().unwrap().parse().unwrap()
        };
        assert!((1..=3).contains(&metric("escape recompilations")), "{text}");
        assert_eq!(metric("escape states reencoded"), 0, "{text}");
        assert!(metric("escape deoptimizations") > 0, "{text}");
    }
}

#[test]
fn adaptive_rows_are_bounded_across_escape_model_reentry() {
    let dir = tlx_testkit::TempDir::with_spec(
        "escape-stats",
        &GROWING_SPEC.replace("79", "4000"),
        "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n",
    );
    let result = tlx_testkit::tlx!()
        .args(["check", "Escape.tla", "-config", "Escape.cfg", "-tlc", "-compile", "-workers", "1", "-stats", "json"])
        .dir(&dir)
        .envs([("TLX_ESCAPE", "1"), ("TLX_PRERUN", "1"), ("TLX_PRERUN_REUSE", "0"), ("TLX_JIT", "only")])
        .run();
    let text = result.text();
    assert_eq!(result.code, 0, "{text}");
    assert!(text.contains("4001 distinct states found"), "{text}");
    let stats = text.lines().find(|l| l.starts_with("{\"sample_every\"")).expect("stats JSON");
    let models: usize = stats.split_once("\"escape recompilations\":").unwrap().1.split([',', '}']).next().unwrap().parse().unwrap();
    let rows = stats.matches("\"library\":").count();
    assert!(rows > 0 && rows <= 2 * (models + 1), "{rows} rows for {} models", models + 1);
}
