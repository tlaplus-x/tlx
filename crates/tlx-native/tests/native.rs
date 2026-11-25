//! End-to-end: hand-written C model -> build (cached) -> dlopen -> explore.

mod common;

use common::{NativeModel, COUNTERS};
use tlx_native::build::{build, BuildOptions};
use tlx_native::native::NativeLib;
use tlx_runtime::{explore, Options, Outcome};

fn model(bad: bool) -> NativeModel {
    let dir = std::env::temp_dir().join(format!("tlx-native-test-{}", std::process::id()));
    let opts = BuildOptions { cache_dir: dir, ..Default::default() };
    let src = COUNTERS.replace("BAD", if bad { "1" } else { "0" });
    let lib = build(&src, &opts).expect("build");
    // SAFETY: COUNTERS has static metadata, two-word buffers and ABI entry points;
    // no host regions/refops or mutable globals. The test compiler/cache are trusted.
    NativeModel { lib: unsafe { NativeLib::load(&lib) }.expect("load") }
}

#[test]
fn native_counters() {
    for workers in [1, 4] {
        let m = model(false);
        let r = explore(&m, &Options { workers, check_deadlock: false, ..Default::default() });
        assert_eq!(r.outcome, Outcome::Ok);
        assert_eq!(r.stats.distinct, 31 * 31);
        assert_eq!(r.stats.generated, 1 + 2 * 30 * 31);
    }
    let m = model(true);
    let r = explore(&m, &Options { check_deadlock: false, ..Default::default() });
    assert_eq!(r.outcome, Outcome::InvariantViolated("NotBad".into()));
    assert_eq!(r.trace.len(), 8);
    assert_eq!(&*r.trace.last().unwrap().state, &[3, 4]);
}

/// A state of the wrong length is refused before generated code could read
/// past its end (also in release builds).
#[test]
#[should_panic(expected = "native library of 2-word states")]
fn short_state_is_refused() {
    let m = model(false);
    m.lib.invariant_raw(&[1], 0);
}

/// A panic in the host's emit callback does not unwind through the C frames
/// (which would abort the process): it is caught, the generated function
/// is stopped, and the panic resumes in the caller.
#[test]
fn panic_in_emit_propagates() {
    use tlx_runtime::Model;
    let m = model(false);
    let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = m.successors(&vec![0u64, 0].into_boxed_slice(), &mut |_, _| panic!("emit failed"));
    }));
    let msg = r.expect_err("the panic must propagate");
    assert_eq!(msg.downcast_ref::<&str>(), Some(&"emit failed"));
    // The library is still usable afterwards.
    let mut n = 0;
    m.successors(&vec![0u64, 0].into_boxed_slice(), &mut |_, _| {
        n += 1;
        true
    })
    .unwrap();
    assert_eq!(n, 2);
}

/// Mismatched tables are refused using well-formed, inert metadata only.
#[test]
fn refop_table_mismatch_is_refused() {
    use std::sync::Arc;
    use tlx_native::mixed::{RefOps, RefOpsScope};

    struct Table(u32, u64);
    impl RefOps for Table {
        fn len(&self) -> u32 {
            self.0
        }
        fn hash(&self) -> u64 {
            self.1
        }
        fn with_scope(&self, _: &mut dyn FnMut(&dyn RefOpsScope)) {
            panic!("the loader must not invoke refops")
        }
    }
    let src = COUNTERS.replace("BAD", "0");
    let path = build(&src, &BuildOptions::default()).expect("build");
    for table in [Table(1, 0), Table(0, 1)] {
        // SAFETY: reviewed COUNTERS has valid immutable ABI metadata and no
        // refops. The mismatched host tables are rejected before model calls.
        // The test compiler/cache are trusted.
        let err = unsafe { NativeLib::load_with(&path, None, Some(Arc::new(table))) }.err().expect("refop count/hash mismatch");
        assert!(err.contains("value store operation table mismatch"), "{err}");
    }
    // A library declaring refops cannot be loaded without its table, either.
    let src = src.replace("1, errs};", "1, errs, 0, 0, 1, 7};");
    let path = build(&src, &BuildOptions::default()).expect("build");
    // SAFETY: only the reviewed fixture's refop metadata differs; missing
    // refops are rejected before entry points are called. Compiler/cache trusted.
    let err = unsafe { NativeLib::load(&path) }.err().expect("missing refop table");
    assert!(err.contains("value store operation table mismatch"), "{err}");
}

#[test]
fn loaded_library_keeps_code_and_metadata_alive() {
    let dir = std::env::temp_dir().join(format!("tlx-native-keepalive-{}", std::process::id()));
    let opts = BuildOptions { cache_dir: dir.clone(), ..Default::default() };
    let src = COUNTERS.replace("BAD", "0");
    let path = build(&src, &opts).expect("build");
    // SAFETY: reviewed COUNTERS implements the ABI with static metadata and
    // two-word state buffers, without regions/refops; compiler/cache trusted.
    let lib = unsafe { NativeLib::load(&path) }.expect("load");
    std::fs::remove_dir_all(&dir).expect("remove backing files while loaded");
    drop((path, src, opts));
    // Move the sole owner to another thread after all build inputs are gone.
    std::thread::spawn(move || {
        assert_eq!(lib.action_names(), &["IncX", "IncY"]);
        assert_eq!(lib.invariant_names(), &["NotBad"]);
        let mut states = Vec::new();
        assert_eq!(lib.init_into(&mut states), tlx_native::native::OK);
        assert_eq!(&*states[0], &[0, 0]);
        let mut next = Vec::new();
        assert_eq!(lib.next_into(&states[0], 0, &mut next), tlx_native::native::OK);
        assert_eq!(&*next[0], &[1, 0]);
        assert_eq!(lib.invariant_raw(&next[0], 0), 1);
    })
    .join()
    .expect("loaded code remains callable");
}

/// `tlx_abi.h` declares the same host table the Rust descriptor
/// (`native::HostFn`) reports. The probe below is generated from the
/// descriptor and compiled with the same C compiler the generated code is
/// built with, so an offset, a signature, the size or the alignment that
/// either side changes alone fails this test.
#[test]
fn abi_header_matches_the_rust_descriptor() {
    use std::collections::BTreeMap;
    use tlx_native::native::{HostArg, HostFn, HOST_ALIGN, HOST_SIZE};

    /// The descriptor's `HostArg` as `tlx_abi.h` spells it.
    fn c_type(a: HostArg) -> &'static str {
        match a {
            HostArg::Ctx => "tlx_ctx *",
            HostArg::State => "const uint64_t *",
            HostArg::WordOut => "uint64_t *",
            HostArg::Args => "const tlx_arg *",
            HostArg::ElemsOut => "const uint64_t **",
            HostArg::U64 => "uint64_t",
            HostArg::U32 => "uint32_t",
            HostArg::I32 => "int",
        }
    }

    /// The callback's field in `tlx_host`.
    fn c_field(f: HostFn) -> &'static str {
        match f {
            HostFn::Emit => "emit",
            HostFn::Error => "error",
            HostFn::Miss => "miss",
            HostFn::Eval => "eval",
            HostFn::Elems => "elems",
            HostFn::Mark => "mark",
            HostFn::Release => "release",
            HostFn::RefOp => "ref_op",
            HostFn::RefElems => "ref_elems",
        }
    }

    let opts = BuildOptions::default();
    assert!(tlx_native::build::compiler_available(&opts.cc), "the ABI cross-check needs the C compiler {}", opts.cc);
    let dir = std::env::temp_dir().join(format!("tlx-native-abi-{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create the probe directory");
    std::fs::write(dir.join("tlx_abi.h"), tlx_native::ABI_HEADER).expect("write the header");

    let mut probe = String::from(
        "/* generated by tests/native.rs from native::HostFn */\n#include \"tlx_abi.h\"\n#include <limits.h>\n#include <stddef.h>\n",
    );
    probe.push_str(&format!("_Static_assert(TLX_ABI_VERSION == {}, \"the ABI version\");\n", tlx_native::ABI_VERSION));
    probe.push_str(&format!("_Static_assert(sizeof(tlx_host) == {HOST_SIZE}, \"sizeof(tlx_host)\");\n"));
    probe.push_str(&format!("_Static_assert(_Alignof(tlx_host) == {HOST_ALIGN}, \"_Alignof(tlx_host)\");\n"));
    let mut widths: BTreeMap<&str, u32> = BTreeMap::new();
    for f in HostFn::ALL {
        let sig = f.abi();
        for a in sig.params.iter().chain(sig.ret.iter()) {
            widths.insert(c_type(*a), a.bits());
        }
        let params: Vec<&str> = sig.params.iter().map(|a| c_type(*a)).collect();
        let proto = format!("{} (*)({})", sig.ret.map_or("void", c_type), params.join(", "));
        let field = c_field(f);
        probe.push_str(&format!("_Static_assert(offsetof(tlx_host, {field}) == {}, \"offset of {field}\");\n", f.offset()));
        probe.push_str(&format!("_Static_assert(_Generic(((tlx_host *)0)->{field}, {proto}: 1, default: 0), \"prototype of {field}\");\n"));
    }
    for (t, bits) in widths {
        probe.push_str(&format!("_Static_assert(sizeof({t}) * CHAR_BIT == {bits}, \"width of {t}\");\n"));
    }
    let probe_path = dir.join("probe.c");
    std::fs::write(&probe_path, probe).expect("write the probe");
    let out = std::process::Command::new(&opts.cc)
        .args(["-std=c11", "-fsyntax-only", "-I"])
        .arg(&dir)
        .arg(&probe_path)
        .output()
        .expect("run the C compiler");
    assert!(out.status.success(), "tlx_abi.h and native::HostFn disagree:\n{}", String::from_utf8_lossy(&out.stderr));
    std::fs::remove_dir_all(&dir).expect("remove the probe directory");
}
