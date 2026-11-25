//! Consolidated integration test binary for `tlx-compile`.
//!
//! `Cargo.toml` sets `autotests = false` so the 33 stateless test modules
//! compile and link into one binary. `value_store_runs.rs` and
//! `value_store_switch.rs` stay in their own binaries because they mutate
//! process-wide environment variables.

mod atom_equality;
mod composition;
mod const_set_shapes;
mod encoded_order;
mod except_union;
mod exec_errors;
mod exec_fast;
mod exec_memo;
mod exec_region;
mod exec_vs_native;
mod exec_vs_native_random;
mod field_comparability;
mod industrial_lowering;
mod interp_capture;
#[cfg(feature = "jit")]
mod jit_mixed;
mod map_family;
mod mixed_cgen;
mod mixed_regions;
mod operation_matrix;
mod ordered_function_sets;
mod raw_state;
mod recursive_ops;
mod region_formation;
mod regions;
mod repr_native;
mod seq_family;
mod set_comparison;
mod set_family;
mod structural_member;
mod union_construction;
mod union_of_ranges;
mod union_record_except_lowering;
mod union_scalar_fields;
mod volatile;

#[test]
fn all_test_files_registered() {
    const REGISTERED: &[&str] = &[
        "atom_equality",
        "composition",
        "const_set_shapes",
        "encoded_order",
        "except_union",
        "exec_errors",
        "exec_fast",
        "exec_memo",
        "exec_region",
        "exec_vs_native",
        "exec_vs_native_random",
        "field_comparability",
        "industrial_lowering",
        "integration",
        "interp_capture",
        "jit_mixed",
        "map_family",
        "mixed_cgen",
        "mixed_regions",
        "operation_matrix",
        "ordered_function_sets",
        "raw_state",
        "recursive_ops",
        "region_formation",
        "regions",
        "repr_native",
        "seq_family",
        "set_comparison",
        "set_family",
        "structural_member",
        "union_construction",
        "union_of_ranges",
        "union_record_except_lowering",
        "union_scalar_fields",
        "value_store_runs",
        "value_store_switch",
        "volatile",
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
    assert_eq!(found, expected, "every crates/tlx-compile/tests/*.rs file must be registered in tests/integration.rs or Cargo.toml");
}
