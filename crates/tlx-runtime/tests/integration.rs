//! Consolidated integration test binary for `tlx-runtime`.

mod checkpoint;
mod coarse_order;
mod dump;
mod explore;
mod fpset_disk;
mod liveness;
mod observer;
mod ordered_edges;
mod queue;
mod safepoint;
mod spill;
mod view_trace;

#[test]
fn all_test_files_registered() {
    const REGISTERED: &[&str] = &[
        "checkpoint",
        "coarse_order",
        "dump",
        "explore",
        "fpset_disk",
        "integration",
        "liveness",
        "observer",
        "ordered_edges",
        "queue",
        "safepoint",
        "spill",
        "view_trace",
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
    assert_eq!(found, expected, "every crates/tlx-runtime/tests/*.rs file must be registered in tests/integration.rs");
}
