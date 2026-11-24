//! Consolidated integration test binary for `tlx-sema`.

mod age_projection;
mod call_semantics;
mod cfg_overrides;
mod choose_symmetry;
mod constrained_certificates;
mod equiv_symmetry;
mod erased_symmetry;
mod keyed_symmetry;
mod live_versions;
mod modules;
mod nested_allocation;
mod optimization;
mod phase_projection;
mod projection;
mod resolve;
mod sany;
mod sequence_projection;
mod sym_norm;

#[test]
fn all_test_files_registered() {
    const REGISTERED: &[&str] = &[
        "age_projection",
        "call_semantics",
        "cfg_overrides",
        "choose_symmetry",
        "constrained_certificates",
        "equiv_symmetry",
        "erased_symmetry",
        "integration",
        "keyed_symmetry",
        "live_versions",
        "modules",
        "nested_allocation",
        "optimization",
        "phase_projection",
        "projection",
        "resolve",
        "sany",
        "sequence_projection",
        "sym_norm",
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
    assert_eq!(found, expected, "every crates/tlx-sema/tests/*.rs file must be registered in tests/integration.rs");
}
