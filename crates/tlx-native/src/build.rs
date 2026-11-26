//! Compile generated C into a shared library, cached by content hash.

use std::fs::{File, TryLockError};
use std::os::unix::process::CommandExt;
use std::path::{Path, PathBuf};
use std::process::{Child, Command, Stdio};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::time::{Duration, SystemTime};

/// How often `Build::wait_or_cancel` checks whether the build finished (a C
/// compilation runs for seconds to minutes; the poll is negligible beside
/// it) and whether it must be stopped.
const CANCEL_POLL: Duration = Duration::from_millis(20);

/// How long a killed compiler group may take to be reaped.
const CANCEL_REAP: Duration = Duration::from_millis(500);

/// The compiler flags of a sanitized build (`BuildOptions::debug`): generated
/// C compiled at a debug-friendly optimization level with the address and
/// undefined-behavior sanitizers. Part of the cache key (`cache_slot`), so a
/// sanitized library never stands in for a normal one.
const SANITIZER_CFLAGS: &str = "-O1 -g -fsanitize=address,undefined";

/// Options for the C compiler.
#[derive(Clone, Debug)]
pub struct BuildOptions {
    /// Compiler executable (default: `$CC` or `cc`).
    pub cc: String,
    /// Optimization flags (default `-O2`).
    pub opt: String,
    /// Debug build with sanitizers (default: whether `$TLX_CC_SANITIZE` is
    /// set). The host process must then load the sanitizer runtimes, e.g.
    /// on macOS `DYLD_INSERT_LIBRARIES=$(cc -print-file-name=libclang_rt.asan_osx_dynamic.dylib)`.
    pub debug: bool,
    /// Cache directory (default: `$TLX_CACHE` or `~/.cache/tlx`).
    pub cache_dir: PathBuf,
}

impl Default for BuildOptions {
    fn default() -> BuildOptions {
        let env = tlx_base::knobs::Env::process();
        let cache_dir = env.path("TLX_CACHE").unwrap_or_else(|| {
            let home = std::env::var_os("HOME").map(PathBuf::from).unwrap_or_else(std::env::temp_dir);
            home.join(".cache").join("tlx")
        });
        BuildOptions { cc: env.string_or_default("CC"), opt: "-O2".into(), debug: env.flag("TLX_CC_SANITIZE"), cache_dir }
    }
}

/// FNV-1a over the inputs that determine the build output.
fn content_hash(parts: &[&[u8]]) -> u64 {
    let mut h: u64 = 0xcbf29ce484222325;
    for p in parts {
        for b in p.iter() {
            h ^= *b as u64;
            h = h.wrapping_mul(0x100000001b3);
        }
        h ^= 0xff;
        h = h.wrapping_mul(0x100000001b3);
    }
    h
}

fn dylib_ext() -> &'static str {
    if cfg!(target_os = "macos") {
        "dylib"
    } else {
        "so"
    }
}

/// Where the build of `source` with `opts` is cached: (directory, library
/// path, compiler flags).
fn cache_slot<'a>(source: &str, opts: &'a BuildOptions) -> (PathBuf, PathBuf, &'a str) {
    let flags = if opts.debug { SANITIZER_CFLAGS } else { opts.opt.as_str() };
    let key = content_hash(&[source.as_bytes(), crate::ABI_HEADER.as_bytes(), opts.cc.as_bytes(), flags.as_bytes()]);
    let dir = opts.cache_dir.join(format!("{key:016x}"));
    let lib = dir.join(format!("model.{}", dylib_ext()));
    (dir, lib, flags)
}

/// The cached library of `source` built with `opts`, if there is one.
pub fn cached(source: &str, opts: &BuildOptions) -> Option<PathBuf> {
    let (_, lib, _) = cache_slot(source, opts);
    lib.exists().then_some(lib)
}

/// Whether C compiler `cc` exists: a file if it is a path, else a program
/// in a `PATH` directory.
pub fn compiler_available(cc: &str) -> bool {
    let p = Path::new(cc);
    if p.components().count() > 1 {
        return p.is_file();
    }
    std::env::var_os("PATH").is_some_and(|path| std::env::split_paths(&path).any(|d| d.join(cc).is_file()))
}

/// The compiler's diagnostics in one line: the first line that reports an
/// error (else the first nonempty one), and how many lines follow.
fn first_error(diagnostics: &str) -> String {
    let lines: Vec<&str> = diagnostics.lines().map(str::trim).filter(|l| !l.is_empty()).collect();
    let Some(first) = lines.iter().find(|l| l.contains("error")).or(lines.first()) else {
        return "no diagnostics".into();
    };
    match lines.len() - 1 {
        0 => first.to_string(),
        n => format!("{first} (and {n} more lines)"),
    }
}

/// Mark cache slot `dir` as used now (the least recently used slots are
/// pruned first, see `prune`).
fn touch(dir: &Path) {
    let _ = File::open(dir).and_then(|f| f.set_modified(SystemTime::now()));
}

/// Slots used more recently than this are never pruned (another run may be
/// about to load their library).
const PRUNE_KEEP_RECENT: Duration = Duration::from_secs(600);

/// Keep the cache within `TLX_CACHE_MB` (0: no limit): remove the least
/// recently used slots (by the modification time of their directory, see
/// `touch`) until the rest fits, except `keep` (the slot being built),
/// slots used in the last `PRUNE_KEEP_RECENT` and slots whose build is
/// running (their lock is held). Runs in the background: a new library is
/// being built, which takes much longer.
fn prune(opts: &BuildOptions, keep: &Path) {
    let limit = tlx_base::knobs::Env::process().num("TLX_CACHE_MB").unwrap_or(0) << 20;
    if limit == 0 {
        return;
    }
    let (cache, keep) = (opts.cache_dir.clone(), keep.to_path_buf());
    // Best effort: missing a prune affects cache size, not child ownership.
    let _ = std::thread::Builder::new().name("tlx-cache-prune".into()).spawn(move || prune_cache(&cache, &keep, limit));
}

/// `prune` (synchronously): the number of slots removed.
pub fn prune_cache(cache: &Path, keep: &Path, limit: u64) -> usize {
    let Ok(entries) = std::fs::read_dir(cache) else { return 0 };
    let now = SystemTime::now();
    let mut slots = Vec::new();
    let mut total = 0;
    for e in entries.flatten() {
        let path = e.path();
        let Ok(meta) = e.metadata() else { continue };
        // (Only the slots: directories named by a 16-digit hash.)
        let name = e.file_name();
        let name = name.to_string_lossy();
        if !meta.is_dir() || name.len() != 16 || !name.bytes().all(|b| b.is_ascii_hexdigit()) {
            continue;
        }
        let size: u64 = std::fs::read_dir(&path).map_or(0, |fs| fs.flatten().filter_map(|f| f.metadata().ok()).map(|m| m.len()).sum());
        total += size;
        let used = meta.modified().unwrap_or(now);
        slots.push((used, size, path));
    }
    if total <= limit {
        return 0;
    }
    slots.sort();
    let mut removed = 0;
    for (used, size, path) in slots {
        if total <= limit {
            break;
        }
        if path == keep || now.duration_since(used).unwrap_or_default() < PRUNE_KEEP_RECENT {
            continue;
        }
        // (Not while a build of the slot runs: it holds the lock.)
        let Ok(lock) = File::options().create(true).truncate(false).write(true).open(path.join("build.lock")) else { continue };
        if lock.try_lock().is_err() {
            continue;
        }
        if std::fs::remove_dir_all(&path).is_ok() {
            total = total.saturating_sub(size);
            removed += 1;
        }
    }
    removed
}

/// Compile `source` (a complete C translation unit that may `#include
/// "tlx_abi.h"`) and return the path of the shared library. Reuses a cached
/// build when the source, flags and ABI are unchanged; waits for a build of
/// the same library that another process (or thread) is running.
pub fn build(source: &str, opts: &BuildOptions) -> Result<PathBuf, String> {
    start(source, opts)?.wait()
}

/// A build of a library started by `start`.
pub struct Build {
    lib: PathBuf,
    state: State,
}

enum State {
    /// The library is in the cache.
    Done,
    /// Our compiler process, with the files of its build (see `Files`).
    Running(Child, Files),
    /// Another build of the library holds its lock (the lock file, the
    /// source and options to build it ourselves if that build fails).
    Elsewhere(File, String, BuildOptions),
}

/// The files of one build in progress: what the shell of `start` renames
/// into the cache on success, and removes on failure.
struct Files {
    /// The generated source the compiler reads.
    src: PathBuf,
    /// The library the compiler writes.
    tmp: PathBuf,
    /// The compiler's diagnostics.
    log: PathBuf,
}

impl Files {
    /// Remove the files of a build that will not complete (a cancelled one;
    /// the shell's own cleanup cannot run after it is killed).
    fn remove(&self) {
        for p in [&self.src, &self.tmp, &self.log] {
            let _ = std::fs::remove_file(p);
        }
    }
}

/// Keep a sanitizer runtime that was preloaded into `tlx` out of `cmd` and its
/// descendants. tlx itself is not instrumented: it loads the ASan runtime with
/// `LD_PRELOAD`/`DYLD_INSERT_LIBRARIES` to `dlopen` a sanitized model
/// (`BuildOptions::debug`), and the preload would otherwise instrument the C
/// compiler too -- every child `clang` would initialize ASan's shadow memory
/// for a compilation that runs once per model (see docs/testing.md section 11).
fn without_sanitizer_preload(cmd: &mut Command) {
    cmd.env_remove("LD_PRELOAD").env_remove("DYLD_INSERT_LIBRARIES");
}

/// Start building `source` with `opts` in the background (see `build`);
/// `Build::wait` waits for the library.
///
/// The compiler runs in a shell that moves the library into the cache
/// itself, writes its diagnostics to a file and holds the lock of the
/// library: a build still running when tlx exits (builds run in the
/// background) completes into the cache, and a concurrent tlx run waits for
/// it instead of compiling the same library again.
pub fn start(source: &str, opts: &BuildOptions) -> Result<Build, String> {
    let (dir, lib, flags) = cache_slot(source, opts);
    if lib.exists() {
        touch(&dir);
        return Ok(Build { lib, state: State::Done });
    }
    if !compiler_available(&opts.cc) {
        return Err(format!("no C compiler ({} not found)", opts.cc));
    }
    std::fs::create_dir_all(&dir).map_err(|e| format!("cannot create {}: {e}", dir.display()))?;
    // One build of the library at a time: its compiler process holds the
    // lock (an advisory lock on `build.lock`, released when the processes
    // holding it exit, however they end).
    let lock = File::options()
        .create(true)
        .truncate(false)
        .write(true)
        .open(dir.join("build.lock"))
        .map_err(|e| format!("cannot open the build lock in {}: {e}", dir.display()))?;
    match lock.try_lock() {
        Ok(()) => {}
        Err(TryLockError::WouldBlock) => return Ok(Build { lib, state: State::Elsewhere(lock, source.to_string(), opts.clone()) }),
        Err(TryLockError::Error(e)) => return Err(format!("cannot lock the build in {}: {e}", dir.display())),
    }
    // (Built by the previous holder of the lock.)
    if lib.exists() {
        return Ok(Build { lib, state: State::Done });
    }
    // Build from and into names unique to this call, then rename, so that
    // concurrent builds (from other processes or threads) are safe. The
    // renames are done by the shell that runs the compiler: a build still
    // running when tlx exits completes into the cache instead of leaving
    // temporary files behind. A failed build removes its temporary files
    // there too, for the same reason (its log is read and removed here).
    static SEQ: AtomicU64 = AtomicU64::new(0);
    let stem = format!("model.{}.{}", std::process::id(), SEQ.fetch_add(1, Ordering::Relaxed));
    // (The header too: rewriting it in place would let a concurrent build
    // of the same source read it half written.)
    let header = dir.join(format!("{stem}.h"));
    std::fs::write(&header, crate::ABI_HEADER).map_err(|e| e.to_string())?;
    std::fs::rename(&header, dir.join("tlx_abi.h")).map_err(|e| e.to_string())?;
    let c_path = dir.join(format!("{stem}.c"));
    std::fs::write(&c_path, source).map_err(|e| e.to_string())?;
    let tmp = dir.join(format!("{stem}.{}", dylib_ext()));
    let log = dir.join(format!("{stem}.log"));
    let mut cmd = Command::new("sh");
    without_sanitizer_preload(&mut cmd);
    cmd.arg("-c")
        .arg(r#"cc="$1"; shift; "$cc" "$@" 2>"$TLX_LOG" && mv -f "$TLX_TMP" "$TLX_LIB" && { mv -f "$TLX_SRC" "$TLX_KEEP" || true; rm -f "$TLX_LOG"; } || { rm -f "$TLX_TMP" "$TLX_SRC"; exit 1; }"#)
        .arg("sh")
        .arg(&opts.cc)
        .args(flags.split_whitespace())
        .args(["-std=c11", "-fPIC", "-shared", "-fno-strict-aliasing", "-Wno-unused"])
        .arg("-I")
        .arg(&dir)
        .arg("-o")
        .arg(&tmp)
        .arg(&c_path)
        .env("TLX_TMP", &tmp)
        .env("TLX_LIB", &lib)
        .env("TLX_SRC", &c_path)
        .env("TLX_LOG", &log)
        // Keep the source next to the library for inspection.
        .env("TLX_KEEP", dir.join("model.c"))
        // The shell and the compiler hold the lock through their standard
        // input, and have no pipes to tlx (which may exit first).
        .stdin(Stdio::from(lock))
        .stdout(Stdio::null())
        .stderr(Stdio::null());
    // The build gets its own process group, so that `Build::wait_or_cancel`
    // can stop the shell and everything it started with one signal to `-pgid`.
    match cmd.process_group(0).spawn() {
        Ok(child) => {
            prune(opts, &dir);
            let files = Files { src: c_path, tmp, log };
            Ok(Build { lib, state: State::Running(child, files) })
        }
        Err(e) => {
            let _ = std::fs::remove_file(&c_path);
            Err(format!("cannot run {}: {e}", opts.cc))
        }
    }
}

impl Build {
    /// Wait for the build: the path of the library.
    pub fn wait(mut self) -> Result<PathBuf, String> {
        let lib = std::mem::take(&mut self.lib);
        match std::mem::replace(&mut self.state, State::Done) {
            State::Done => Ok(lib),
            State::Running(mut child, files) => match child.wait() {
                Ok(status) => finished(&lib, status, &files),
                Err(e) => Err(format!("C compilation ({}): {e}", files.src.display())),
            },
            State::Elsewhere(lock, source, opts) => {
                lock.lock().map_err(|e| format!("cannot lock the build of {}: {e}", lib.display()))?;
                drop(lock);
                if lib.exists() {
                    return Ok(lib);
                }
                // (The other build failed: ours says why.)
                build(&source, &opts)
            }
        }
    }

    /// Wait for the build, but stop it when `cancel` is set: the compiled
    /// tier discards a model whose layout a miss widens, so the library
    /// being built for it can never be loaded, and a machine running a
    /// model-checker must not keep compiling one translation unit per
    /// discarded attempt beside the search. The compiler's process group
    /// (the shell of `start` and everything it started) is killed and the
    /// build's temporary files are removed; Err then says it was cancelled.
    ///
    /// A build that ends by itself reports as `wait` does. A build of
    /// another process is not touched: while it holds the lock the wait
    /// polls it (never blocks on it, so a slow or hung holder cannot make
    /// the cancellation wait), and if it goes away without a library the
    /// build is started here — and is then cancellable like any other.
    pub fn wait_or_cancel(mut self, cancel: &AtomicBool) -> Result<PathBuf, String> {
        loop {
            let lib = std::mem::take(&mut self.lib);
            let (mut child, files) = match std::mem::replace(&mut self.state, State::Done) {
                State::Done => return Ok(lib),
                State::Running(child, files) => (child, files),
                State::Elsewhere(lock, source, opts) => {
                    match wait_for_holder(&lib, lock, cancel)? {
                        // The other build finished: its library is ours too.
                        Holder::Built => return Ok(lib),
                        // The other build failed: start ours, and wait for it
                        // with this same cancellation in the next round.
                        Holder::Failed => {
                            self = start(&source, &opts)?;
                            continue;
                        }
                    }
                }
            };
            loop {
                match child.try_wait() {
                    Ok(Some(status)) => return finished(&lib, status, &files),
                    Ok(None) => {}
                    Err(e) => {
                        files.remove();
                        return Err(format!("C compilation ({}): {e}", files.src.display()));
                    }
                }
                if cancel.load(Ordering::Acquire) {
                    cancel_build(child, &files);
                    return Err(cancelled(&files.src));
                }
                std::thread::sleep(CANCEL_POLL);
            }
        }
    }
}

/// How the wait for another process's build ended.
enum Holder {
    /// The library is in the cache.
    Built,
    /// The lock was released without a library (the other build failed): the
    /// caller builds it.
    Failed,
}

/// Wait for the build of another process (holding `lock`) without ever
/// blocking on it: the wait polls the lock, so `cancel` ends it at once, and
/// the holder — which is not ours to stop — is left alone. Ok(Built) when
/// its library appears, Ok(Failed) when the lock was taken without one (the
/// caller's own build starts then).
fn wait_for_holder(lib: &Path, lock: File, cancel: &AtomicBool) -> Result<Holder, String> {
    loop {
        if lib.exists() {
            return Ok(Holder::Built);
        }
        if cancel.load(Ordering::Acquire) {
            return Err(cancelled(lib));
        }
        match lock.try_lock() {
            // (Only this library's slot: the holder exited without one.)
            Ok(()) => return Ok(Holder::Failed),
            Err(TryLockError::WouldBlock) => std::thread::sleep(CANCEL_POLL),
            Err(TryLockError::Error(e)) => return Err(format!("cannot lock the build of {}: {e}", lib.display())),
        }
    }
}

/// Why a cancelled build returns.
fn cancelled(what: &Path) -> String {
    format!("C compilation cancelled ({}): the layout was discarded", what.display())
}

/// Stop the build of `child` and remove its files: the compiler's process
/// group is killed, and a child that resists SIGKILL beyond `CANCEL_REAP` is
/// left with the background reaper instead of being forgotten (a dropped
/// `Child` stays a zombie on Unix).
fn cancel_build(mut child: Child, files: &Files) {
    let Ok(pgid) = i32::try_from(child.id()) else {
        files.remove();
        return;
    };
    if pgid > 1 {
        // SAFETY: spawn used process_group(0), so -pgid addresses only the
        // group of this build. The leader stays unreaped until after the
        // signal, so its PID (the group ID) cannot be reused meanwhile.
        // `kill` takes no pointer.
        unsafe { libc::kill(-pgid, libc::SIGKILL) };
        // The leader can leave its group; kill its still-owned PID as well,
        // never a group it may have joined since.
        let _ = child.kill();
    }
    let start = std::time::Instant::now();
    while start.elapsed() < CANCEL_REAP {
        match child.try_wait() {
            Ok(Some(_)) | Err(_) => {
                files.remove();
                return;
            }
            Ok(None) => std::thread::sleep(CANCEL_POLL),
        }
    }
    // (A kernel task can resist SIGKILL; reap it in the background rather
    // than wait longer for the cancellation or leave a zombie.)
    let log = files.log.clone();
    files.remove();
    if let Err(e) = reap_child(child, log, |reap| tlx_base::stack::spawn(std::thread::Builder::new().name("tlx-cc-reap".into()), reap)) {
        eprintln!("cannot start C compiler reaper after a cancellation: {e}");
    }
}

/// The result of a build that ended: its library, or its diagnostics.
fn finished(lib: &Path, status: std::process::ExitStatus, files: &Files) -> Result<PathBuf, String> {
    let diagnostics = std::fs::read_to_string(&files.log).unwrap_or_default();
    let _ = std::fs::remove_file(&files.log);
    if !status.success() || !lib.exists() {
        return Err(format!("C compilation failed ({}): {}", files.src.display(), first_error(&diagnostics)));
    }
    Ok(lib.to_path_buf())
}

/// A build dropped while its compiler runs completes into the cache in the
/// background (a thread reaps the process). If that thread cannot start,
/// dropping the build waits synchronously; it never kills the compiler (a
/// caller that knows the library can no longer be used stops it explicitly:
/// `Build::wait_or_cancel`).
impl Drop for Build {
    fn drop(&mut self) {
        if let State::Running(child, files) = std::mem::replace(&mut self.state, State::Done) {
            if let Err(e) =
                reap_child(child, files.log, |reap| tlx_base::stack::spawn(std::thread::Builder::new().name("tlx-cc-reap".into()), reap))
            {
                eprintln!("cannot start C compiler reaper: {e}; synchronous reap attempted");
            }
        }
    }
}

/// The closure owns this guard as a whole: a failed spawn drops the closure
/// and reaps synchronously, including when the thread wrapper never calls it.
struct CompilerReaper {
    child: Child,
    log: PathBuf,
}

impl Drop for CompilerReaper {
    fn drop(&mut self) {
        match self.child.wait() {
            Ok(_) => {
                // No caller will consume these diagnostics. Cleanup after a
                // successful reap is best effort (the shell may remove it too).
                let _ = std::fs::remove_file(&self.log);
            }
            Err(e) => eprintln!("cannot reap C compiler {}: {e}; preserving diagnostics at {}", self.child.id(), self.log.display()),
        }
    }
}

fn reap_child(
    child: Child,
    log: PathBuf,
    spawn: impl FnOnce(Box<dyn FnOnce() + Send>) -> std::io::Result<std::thread::JoinHandle<()>>,
) -> std::io::Result<std::thread::JoinHandle<()>> {
    let reaper = CompilerReaper { child, log };
    spawn(Box::new(move || drop(reaper)))
}

#[cfg(all(test, unix))]
mod tests {
    use std::sync::Arc;

    use super::*;

    unsafe extern "C" {
        fn waitpid(pid: i32, status: *mut i32, options: i32) -> i32;
    }

    /// Whether `pid` still exists (`ESRCH` means it is gone).
    fn alive(pid: i32) -> bool {
        // SAFETY: signal 0 checks the process without touching it; a PID
        // recorded by our own fixture is a live or dead process, never a
        // pointer.
        unsafe { libc::kill(pid, 0) == 0 }
    }

    /// A scratch directory of this test, empty at the start.
    fn scratch(name: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!("tlx-{name}-{}", std::process::id()));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    /// A "compiler" that never finishes: it starts a helper process, records
    /// the helper's PID beside itself and sleeps. Compiling an actual
    /// translation unit is not needed to see whether a cancelled build is
    /// left running.
    fn sleep_compiler(dir: &Path) -> String {
        let cc = dir.join("slow-cc.sh");
        std::fs::write(
            &cc,
            "#!/bin/sh\n\
             sleep 60 &\n\
             helper=$!\n\
             d=$(dirname \"$0\")\n\
             echo $helper > \"$d/helper.pid\"\n\
             sleep 60\n",
        )
        .unwrap();
        use std::os::unix::fs::PermissionsExt;
        let mut perm = std::fs::metadata(&cc).unwrap().permissions();
        perm.set_mode(0o755);
        std::fs::set_permissions(&cc, perm).unwrap();
        cc.to_string_lossy().into_owned()
    }

    fn wait_for(path: &Path) -> String {
        let until = std::time::Instant::now() + Duration::from_secs(10);
        while std::time::Instant::now() < until {
            if let Ok(s) = std::fs::read_to_string(path) {
                let s = s.trim().to_string();
                if !s.is_empty() {
                    return s;
                }
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        panic!("the fixture compiler did not start ({} not written)", path.display());
    }

    /// A build the compiled tier discards (a layout miss widened the model)
    /// must be stopped: the compiler and the processes it started are killed
    /// and its temporary files are removed, and nothing lands in the cache.
    #[test]
    fn a_cancelled_build_kills_the_compiler_group_and_removes_its_files() {
        let dir = scratch("cancel-build");
        let cache = dir.join("cache");
        let opts = BuildOptions { cc: sleep_compiler(&dir), opt: "-O2".into(), debug: false, cache_dir: cache.clone() };
        let source = "/* fixture: never compiled */\n";
        let cancel = AtomicBool::new(false);
        let build = start(source, &opts).unwrap();
        let helper: i32 = wait_for(&dir.join("helper.pid")).parse().unwrap();
        assert!(alive(helper), "the fixture compiler must run before it is cancelled");

        cancel.store(true, Ordering::Release);
        let err = build.wait_or_cancel(&cancel).unwrap_err();
        assert!(err.contains("cancelled"), "{err}");

        // The compiler's own child is gone: the signal reached the group, not
        // only the shell we spawned.
        let until = std::time::Instant::now() + Duration::from_secs(10);
        while alive(helper) && std::time::Instant::now() < until {
            std::thread::sleep(Duration::from_millis(10));
        }
        assert!(!alive(helper), "cancelling must kill the compiler group (helper {helper})");
        // No temporary file survives, and the cancelled build is not cached.
        let leftovers: Vec<String> = std::fs::read_dir(&cache)
            .map(|d| {
                d.flatten()
                    .flat_map(|e| std::fs::read_dir(e.path()).into_iter().flatten())
                    .flatten()
                    .map(|e| e.file_name().to_string_lossy().into_owned())
                    .collect()
            })
            .unwrap_or_default();
        // (The slot keeps its lock file and the ABI header: the source, the
        // log and any library of the cancelled build are gone.)
        assert!(leftovers.iter().all(|n| n == "build.lock" || n == "tlx_abi.h"), "leftovers: {leftovers:?}");
        assert!(cached(source, &opts).is_none());
        let _ = std::fs::remove_file(dir.join("helper.pid"));
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// A holder of the build lock: this process takes the lock and hands its
    /// open file description to a child (the way `start` passes the lock to
    /// the compiler shell), so that the child's exit is what releases it.
    fn lock_holder(lock: &Path, seconds: u32) -> Child {
        let file = File::options().create(true).truncate(false).write(true).open(lock).unwrap();
        file.lock().unwrap();
        let child = Command::new("sh")
            .args(["-c", &format!("sleep {seconds}")])
            .stdin(Stdio::from(file.try_clone().unwrap()))
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .spawn()
            .unwrap();
        // (The lock lives on the description the child inherited; dropping
        // ours leaves the child as its only holder.)
        drop(file);
        child
    }

    /// Waiting for another process's build must not block the cancellation:
    /// a slow or hung holder leaves the waiter able to give up at once, and
    /// the holder (which is not ours) survives.
    #[test]
    fn cancelling_a_waiter_leaves_the_holder_alone() {
        let dir = scratch("cancel-waiter");
        let cache = dir.join("cache");
        let opts = BuildOptions { cc: sleep_compiler(&dir), opt: "-O2".into(), debug: false, cache_dir: cache.clone() };
        let source = "/* fixture: built elsewhere */\n";
        let (slot, _lib, _) = cache_slot(source, &opts);
        std::fs::create_dir_all(&slot).unwrap();
        let mut holder = lock_holder(&slot.join("build.lock"), 30);
        let build = start(source, &opts).unwrap();
        // (The holder has the lock: this process starts no compiler of its
        // own here, it waits for the holder's build.)
        assert!(!dir.join("helper.pid").exists(), "the waiter must not start a second compiler beside the holder");
        let cancel = Arc::new(AtomicBool::new(false));
        let waiter_cancel = cancel.clone();
        let waiting = std::thread::spawn(move || build.wait_or_cancel(&cancel));
        // (The waiter polls the holder's lock while it is held.)
        std::thread::sleep(Duration::from_millis(200));
        let t0 = std::time::Instant::now();
        waiter_cancel.store(true, Ordering::Release);
        let err = waiting.join().unwrap().unwrap_err();
        let waited = t0.elapsed();
        assert!(err.contains("cancelled"), "{err}");
        assert!(waited < Duration::from_secs(5), "a cancelled wait must not block on the holder ({waited:?})");
        // (The holder is another process's build: untouched.)
        assert!(holder.try_wait().unwrap().is_none(), "the holder must survive a cancelled wait");
        assert!(cached(source, &opts).is_none());
        let _ = holder.kill();
        let _ = holder.wait();
        let _ = std::fs::remove_dir_all(&dir);
    }

    /// When the holder of the lock goes away without a library, the waiter
    /// starts the build itself — and that build is cancellable like any
    /// other (it is the case a layout miss hits after a concurrent run
    /// failed to build the same library).
    #[test]
    fn a_build_started_after_a_failed_holder_can_still_be_cancelled() {
        let dir = scratch("cancel-after-holder");
        let cache = dir.join("cache");
        let opts = BuildOptions { cc: sleep_compiler(&dir), opt: "-O2".into(), debug: false, cache_dir: cache.clone() };
        let source = "/* fixture: the holder fails, ours starts */\n";
        let (slot, _lib, _) = cache_slot(source, &opts);
        std::fs::create_dir_all(&slot).unwrap();
        let mut holder = lock_holder(&slot.join("build.lock"), 1);
        let build = start(source, &opts).unwrap();
        let cancel = Arc::new(AtomicBool::new(false));
        let waiter_cancel = cancel.clone();
        let waiting = std::thread::spawn(move || build.wait_or_cancel(&cancel));
        // The holder exits after a second without a library: the wait takes
        // the lock and starts this build's own compiler.
        let helper = dir.join("helper.pid");
        let until = std::time::Instant::now() + Duration::from_secs(10);
        let mut pid = None;
        while std::time::Instant::now() < until {
            if let Ok(s) = std::fs::read_to_string(&helper) {
                if let Ok(p) = s.trim().parse::<i32>() {
                    pid = Some(p);
                    break;
                }
            }
            std::thread::sleep(Duration::from_millis(10));
        }
        let pid = pid.expect("our build must start once the holder is gone");
        assert!(alive(pid));
        waiter_cancel.store(true, Ordering::Release);
        let err = waiting.join().unwrap().unwrap_err();
        assert!(err.contains("cancelled"), "{err}");
        let until = std::time::Instant::now() + Duration::from_secs(10);
        while alive(pid) && std::time::Instant::now() < until {
            std::thread::sleep(Duration::from_millis(10));
        }
        assert!(!alive(pid), "the build that took over the lock must be cancelled too (helper {pid})");
        let _ = holder.kill();
        let _ = holder.wait();
        let _ = std::fs::remove_file(&helper);
        let _ = std::fs::remove_dir_all(&dir);
    }

    fn child_and_log(name: &str, exit: i32) -> (Child, PathBuf) {
        let log = std::env::temp_dir().join(format!("tlx-reaper-{name}-{}.log", std::process::id()));
        std::fs::write(&log, "compiler diagnostics").unwrap();
        let child = Command::new("sh").args(["-c", &format!("exit {exit}")]).current_dir(std::env::temp_dir()).env_clear().spawn().unwrap();
        (child, log)
    }

    fn assert_reaped(pid: u32) {
        let mut status = 0;
        // SAFETY: pid identifies our child, status is writable, and options=0
        // waits only for that child. This also cleans up the negative fixture.
        let result = unsafe { waitpid(pid as i32, &mut status, 0) };
        assert_eq!(result, -1, "the reaper left child {pid} waitable");
        assert_eq!(std::io::Error::last_os_error().raw_os_error(), Some(10), "expected ECHILD");
    }

    #[test]
    fn rejected_reaper_spawn_reaps_child_and_removes_log() {
        for exit in [0, 7] {
            let (child, log) = child_and_log(&format!("rejected-{exit}"), exit);
            let pid = child.id();
            let result = reap_child(child, log.clone(), |_reap| Err(std::io::Error::other("injected spawn failure")));
            assert!(result.is_err());
            let cleaned = !log.exists();
            let _ = std::fs::remove_file(log);
            assert_reaped(pid);
            assert!(cleaned, "successful synchronous reap must remove the log");
        }
    }

    #[test]
    fn background_reaper_reaps_child_and_removes_log() {
        let (child, log) = child_and_log("background", 7);
        let pid = child.id();
        reap_child(child, log.clone(), |reap| std::thread::Builder::new().spawn(reap)).unwrap().join().unwrap();
        assert_reaped(pid);
        assert!(!log.exists());
    }

    #[test]
    fn failed_reap_preserves_diagnostics() {
        let (child, log) = child_and_log("wait-failed", 7);
        let mut status = 0;
        // SAFETY: this is our child; consuming its status injects ECHILD into
        // the reaper's wait without replacing the process implementation.
        assert_eq!(unsafe { waitpid(child.id() as i32, &mut status, 0) }, child.id() as i32);
        reap_child(child, log.clone(), |reap| std::thread::Builder::new().spawn(reap)).unwrap().join().unwrap();
        let diagnostics = std::fs::read_to_string(&log);
        let _ = std::fs::remove_file(log);
        assert_eq!(diagnostics.unwrap(), "compiler diagnostics");
    }

    /// A sanitizer runtime preloaded into tlx (as the generated-C ASan run
    /// needs, docs/testing.md section 11) must not be inherited by the
    /// compiler the build spawns: every child `clang` would initialize ASan
    /// for a compilation that does not need it, at a large cost per build.
    #[test]
    fn the_compiler_child_drops_preloaded_sanitizer_runtimes() {
        let mut cmd = Command::new("sh");
        // (Set on this command only: the test process keeps its environment.)
        cmd.env("LD_PRELOAD", "/nonexistent/libasan.so")
            .env("DYLD_INSERT_LIBRARIES", "/nonexistent/libasan.dylib")
            .args(["-c", r#"printf '%s|%s' "${LD_PRELOAD-unset}" "${DYLD_INSERT_LIBRARIES-unset}""#]);
        without_sanitizer_preload(&mut cmd);
        let out = cmd.output().unwrap();
        assert!(out.status.success(), "the fixture shell failed: {out:?}");
        assert_eq!(String::from_utf8_lossy(&out.stdout), "unset|unset");
    }
}
