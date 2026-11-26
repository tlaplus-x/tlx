//! Negative self-test of the generated-C sanitizer build: a C defect must halt
//! the process that `SANITIZER_CFLAGS` instrumented. `TLX_CC_SANITIZE=1` builds
//! generated C through `tlx_native::build`, so a regression that stops the
//! production builder from selecting or forwarding `-fsanitize` would leave the
//! sanitizer workflow green without inspecting anything. This test builds its
//! probe through that same builder (`BuildOptions { debug: true, .. }`), loads
//! it into a child with the runtime preloaded exactly as `tlx` does, and fails
//! if either defect goes unreported.
//!
//! The child is an ordinary uninstrumented executable that `dlopen`s the
//! library, so the instrumented library's runtime comes from the preload, as in
//! the checker. It is `#[ignore]`d so the ordinary `cargo test` matrix does not
//! require the compiler-rt development package; `.github/workflows/sanitizers.yml`
//! runs it explicitly with `--ignored`. Where the C compiler cannot build or
//! load a sanitized library the test skips, unless `CI` is set (as it is for
//! that job, which must never pass by skipping).

use std::path::{Path, PathBuf};
use std::process::{Command, Output};

use tlx_native::build::{build, BuildOptions};

/// The runtime options the sanitizer workflow sets (docs/testing.md section 11).
const ASAN_OPTIONS: &str = "detect_leaks=0:halt_on_error=1:disable_coredump=1:allow_user_segv_handler=1:print_stacktrace=1";
const UBSAN_OPTIONS: &str = "halt_on_error=1:disable_coredump=1:print_stacktrace=1";

/// The probe library. `probe_out_of_bounds` reads one past the four integers
/// the driver allocates for it (ASan heap-buffer-overflow); the allocation is
/// made outside this library, so the read can only be reported by this
/// library's own address instrumentation -- the preloaded runtime's allocator
/// and interceptors alone never see it. `probe_signed_overflow` multiplies
/// INT_MAX by itself (UBSan signed-integer-overflow); `probe_benign` exercises
/// the same library without a defect.
const PROBE: &str = r#"
int probe_benign(void) { return 0; }

int probe_out_of_bounds(int *p) {
    /* A direct volatile read one past the driver's four integers. The size is
       not visible here (p is a parameter), so the -fsanitize=undefined
       object-size check cannot report it first. */
    volatile int v = p[4];
    return v;
}

int probe_signed_overflow(void) {
    volatile int n = 2147483647;
    return n * n;
}
"#;

/// The uninstrumented child that loads the probe library the way the checker
/// does: `dlopen` (with the sanitizer runtime preloaded into this process) and
/// call the requested entry point. Its `malloc` is the runtime's, so the
/// instrumented library's load sees the redzone the runtime placed after the
/// allocation.
const DRIVER: &str = r#"
#include <dlfcn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef int (*probe)(void);
typedef int (*probe_at)(int *);

int main(int argc, char **argv) {
    if (argc != 3) return 2;
    void *lib = dlopen(argv[1], RTLD_NOW);
    if (lib == NULL) {
        fprintf(stderr, "dlopen: %s\n", dlerror());
        return 2;
    }
    if (strcmp(argv[2], "probe_out_of_bounds") == 0) {
        probe_at fn = (probe_at)dlsym(lib, argv[2]);
        if (fn == NULL) {
            fprintf(stderr, "dlsym: %s\n", dlerror());
            return 2;
        }
        int *p = malloc(4 * sizeof *p);
        if (p == NULL) return 2;
        for (int i = 0; i < 4; i++) p[i] = i;
        return fn(p);
    }
    probe fn = (probe)dlsym(lib, argv[2]);
    if (fn == NULL) {
        fprintf(stderr, "dlsym: %s\n", dlerror());
        return 2;
    }
    return fn();
}
"#;

/// A sanitized build is required in CI: the sanitizer job must fail rather than
/// skip the only test that proves its build settings do anything.
fn require_sanitizers() -> bool {
    std::env::var_os("CI").is_some()
}

fn runtime_options(name: &str, default: &str) -> String {
    std::env::var(name).ok().filter(|value| !value.is_empty()).unwrap_or_else(|| default.to_string())
}

/// The sanitizer runtime `cc` links generated C for, when it ships the shared
/// runtime that `tlx` must preload (Clang does; GCC's runtime is a `DT_NEEDED`
/// of the library instead and needs no preload).
fn asan_runtime(cc: &str) -> Option<PathBuf> {
    let name = if cfg!(target_os = "macos") {
        "libclang_rt.asan_osx_dynamic.dylib".to_string()
    } else {
        format!("libclang_rt.asan-{}.so", std::env::consts::ARCH)
    };
    let out = Command::new(cc).arg(format!("-print-file-name={name}")).output().ok()?;
    let path = PathBuf::from(String::from_utf8_lossy(&out.stdout).trim());
    (path.is_file()).then_some(path)
}

fn preload_var() -> &'static str {
    if cfg!(target_os = "macos") {
        "DYLD_INSERT_LIBRARIES"
    } else {
        "LD_PRELOAD"
    }
}

fn skip_or_fail(what: &str, detail: &str) -> bool {
    assert!(!require_sanitizers(), "{what}:\n{detail}");
    eprintln!("skipping the sanitizer self-test: {what}\n{detail}");
    false
}

fn run(driver: &Path, library: &Path, runtime: &Path, entry: &str) -> Output {
    Command::new(driver)
        .arg(library)
        .arg(entry)
        .env(preload_var(), runtime)
        .env("ASAN_OPTIONS", runtime_options("ASAN_OPTIONS", ASAN_OPTIONS))
        .env("UBSAN_OPTIONS", runtime_options("UBSAN_OPTIONS", UBSAN_OPTIONS))
        .output()
        .unwrap()
}

#[test]
#[ignore = "run by the sanitizers workflow: cargo test --test sanitizer_selftest -- --ignored"]
fn sanitizer_build_halts_on_address_and_undefined_behavior() {
    let dir = std::env::temp_dir().join(format!("tlx-sanitizer-selftest-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&dir);
    std::fs::create_dir_all(&dir).unwrap();

    // Build the probe through the production builder, with a fresh cache so the
    // sanitized library is built here (not reused from an earlier run).
    let opts = BuildOptions { debug: true, cache_dir: dir.join("cache"), ..Default::default() };
    let library = match build(PROBE, &opts) {
        Ok(library) => library,
        Err(e) => {
            skip_or_fail(&format!("{} cannot build a sanitized library: {e}", opts.cc), "");
            let _ = std::fs::remove_dir_all(&dir);
            return;
        }
    };
    let Some(runtime) = asan_runtime(&opts.cc) else {
        skip_or_fail(&format!("{} does not ship the shared Clang sanitizer runtime to preload", opts.cc), "");
        let _ = std::fs::remove_dir_all(&dir);
        return;
    };

    let source = dir.join("driver.c");
    let driver = dir.join("driver");
    std::fs::write(&source, DRIVER).unwrap();
    let mut command = Command::new(&opts.cc);
    command.args(["-O2", "-o"]).arg(&driver).arg(&source);
    if cfg!(target_os = "linux") {
        command.arg("-ldl");
    }
    let compiled = command.output().unwrap();
    if !compiled.status.success() {
        let stderr = String::from_utf8_lossy(&compiled.stderr);
        skip_or_fail(&format!("{} cannot build the probe driver", opts.cc), &stderr);
        let _ = std::fs::remove_dir_all(&dir);
        return;
    }

    // Positive control: without a defect the library loads in the preloaded
    // child and exits zero, so a failure below means the sanitizer fired rather
    // than the binary failing.
    let benign = run(&driver, &library, &runtime, "probe_benign");
    assert!(benign.status.success(), "the probe library must load and run: {benign:?}");

    let asan = run(&driver, &library, &runtime, "probe_out_of_bounds");
    let asan_out = format!("{}{}", String::from_utf8_lossy(&asan.stdout), String::from_utf8_lossy(&asan.stderr));
    assert!(!asan.status.success(), "the out-of-bounds read must not exit zero:\n{asan_out}");
    assert!(asan_out.contains("AddressSanitizer"), "no AddressSanitizer diagnostic:\n{asan_out}");

    let ubsan = run(&driver, &library, &runtime, "probe_signed_overflow");
    let ubsan_out = format!("{}{}", String::from_utf8_lossy(&ubsan.stdout), String::from_utf8_lossy(&ubsan.stderr));
    assert!(!ubsan.status.success(), "the signed overflow must not exit zero:\n{ubsan_out}");
    assert!(ubsan_out.contains("runtime error:"), "no UndefinedBehaviorSanitizer diagnostic:\n{ubsan_out}");

    let _ = std::fs::remove_dir_all(&dir);
}
