//! Consolidated integration test binary for `tlx-cli`.
//!
//! `Cargo.toml` sets `autotests = false` so the 50 CLI test modules compile and
//! link into one binary instead of 50 separate executables. `optimization.rs`
//! remains its own `[[test]]` target so `cargo test -p tlx-cli --test
//! optimization` keeps working.

mod common;

mod age_projection;
mod atom_type_widening;
mod autosym;
mod bitset_card;
mod bundled_modules;
mod call_semantics;
mod cardinality_stream;
mod cc_at_exit;
mod cfg_overrides;
#[cfg(unix)]
mod checkpoint;
mod choose_soundness;
mod classpath;
mod compile_point_bugs;
mod config;
mod constrained_reductions;
mod coverage;
mod diagnostics;
mod dump_trace;
mod equiv_bags;
mod equiv_folds;
mod equiv_soundness;
mod escape;
mod fpset_full;
mod history_projection;
mod java_only;
mod live_coverage;
mod live_edges;
mod live_mem;
mod live_miss;
mod max_set_size;
mod maxmem;
mod optimization_composition;
mod optimization_lean;
mod optimization_live_versions;
mod optimization_nested;
mod optimization_ordered;
mod output;
mod paranoid;
mod parse_only;
mod phase_projection;
mod prerun;
mod repr_litmus;
mod resume_effects;
mod sema_value_fixes;
mod sequence_projection;
mod set_comparison;
#[cfg(unix)]
mod signals;
mod symcheck;
mod temporal_probes;
mod threshold_counter_projection;
mod tiers;
mod tlc_equality;
mod value_store;
mod view_trace;
mod widening;

#[test]
fn all_test_files_registered() {
    const REGISTERED: &[&str] = &[
        "age_projection",
        "archive_elision",
        "atom_type_widening",
        "autosym",
        "bitset_card",
        "bundled_modules",
        "call_semantics",
        "cardinality_stream",
        "cc_at_exit",
        "cfg_overrides",
        "checkpoint",
        "choose_soundness",
        "classpath",
        "compile_point_bugs",
        "config",
        "constrained_reductions",
        "coverage",
        "diagnostics",
        "dump_trace",
        "equiv_bags",
        "equiv_folds",
        "equiv_soundness",
        "escape",
        "fpset_full",
        "history_projection",
        "integration",
        "java_only",
        "live_coverage",
        "live_edges",
        "live_mem",
        "live_miss",
        "max_set_size",
        "maxmem",
        "optimization",
        "optimization_composition",
        "optimization_lean",
        "optimization_live_versions",
        "optimization_nested",
        "optimization_ordered",
        "output",
        "paranoid",
        "parse_only",
        "phase_projection",
        "prerun",
        "repr_litmus",
        "resume_effects",
        "sema_value_fixes",
        "sequence_projection",
        "set_comparison",
        "signals",
        "symcheck",
        "temporal_probes",
        "threshold_counter_projection",
        "tiers",
        "tlc_equality",
        "value_store",
        "view_trace",
        "widening",
    ];
    let dir = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("tests");
    let mut found: Vec<String> = std::fs::read_dir(&dir)
        .unwrap()
        .filter_map(|e| {
            let path = e.ok()?.path();
            (path.extension()?.to_str()? == "rs").then(|| path.file_stem()?.to_str().map(String::from)).flatten()
        })
        .collect();
    found.sort();
    let expected: Vec<String> = REGISTERED.iter().map(|s| (*s).to_string()).collect();
    assert_eq!(found, expected, "every crates/tlx-cli/tests/*.rs file must be registered in tests/integration.rs or Cargo.toml");
}
