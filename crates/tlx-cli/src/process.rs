//! Process-level setup for the `tlx` binary: the global allocator and its
//! tuning, the transparent-huge-page policy, panic reporting and the signal
//! dispositions (`SIGPIPE`, `SIGINT`/`SIGTERM`). The crate root's `main`
//! installs the stack-overflow fallback and the progress sink and then calls
//! `init` before dispatching to `check`; nothing here depends on the model or
//! the configuration.

// The interpreter is allocation-heavy; mimalloc scales far better than the
// system allocator across worker threads.
#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

extern "C" {
    /// mimalloc (linked for `GLOBAL`): collect the calling thread's heap and,
    /// with `force`, purge the memory freed in its arenas now.
    fn mi_collect(force: bool);
    /// mimalloc: set an option (`mi_option_t`, a C enum).
    fn mi_option_set(option: std::ffi::c_int, value: std::ffi::c_long);
    // mimalloc's C allocation functions (for the parser's C library).
    fn mi_malloc(size: usize) -> *mut std::ffi::c_void;
    fn mi_calloc(n: usize, size: usize) -> *mut std::ffi::c_void;
    fn mi_realloc(p: *mut std::ffi::c_void, size: usize) -> *mut std::ffi::c_void;
    fn mi_free(p: *mut std::ffi::c_void);
}

/// mimalloc's `mi_option_purge_delay` (stable index in v2 and v3).
const MI_OPTION_PURGE_DELAY: std::ffi::c_int = 15;

/// How long (ms) mimalloc keeps freed memory committed before returning it
/// to the OS (`set_purge_delay`).
const PURGE_DELAY_MS: std::ffi::c_long = 100_000;

/// mimalloc returns freed memory to the OS after 1 s (v3's default); the
/// interpreter frees and reallocates the same memory all the time, and
/// each return costs a decommit and later page faults (MCCheckpointCoordinationFailure:
/// a few % of the instructions, more of the system time). A long delay keeps
/// it; under memory-budget pressure the budget purges explicitly
/// (`purge_allocator`, forced, which ignores the delay). (Not -1, "never
/// purge": that disables the forced purge too.) `MIMALLOC_PURGE_DELAY`
/// decides when set.
fn set_purge_delay() {
    if std::env::var_os("MIMALLOC_PURGE_DELAY").is_none() {
        // SAFETY: mi_option_set has no preconditions (an option is a plain
        // integer read at its next use).
        unsafe { mi_option_set(MI_OPTION_PURGE_DELAY, PURGE_DELAY_MS) }
    }
}

/// The memory budget's purge (`tlx_runtime::mem::purge`).
fn purge_allocator() {
    // SAFETY: mi_collect has no preconditions.
    unsafe { mi_collect(true) }
}

/// Below this memory budget plus `THP_BUDGET_PER_WORKER` per worker,
/// transparent huge pages are off (`set_huge_pages`).
const THP_BUDGET_BASE: usize = 512 << 20;
const THP_BUDGET_PER_WORKER: usize = 64 << 20;

/// Whether the process uses transparent huge pages (Linux; `TLX_THP`: `on`,
/// `off`, or by default by the memory budget). mimalloc asks for them for
/// its arenas, which costs some tens of MiB of resident memory more (about
/// 15-30 MiB with 1 worker, 25-55 MiB with 8, 10-20% on large runs) and
/// saves 1-10% of the time (measured 2026-10): off under an
/// explicit budget of which that baseline would take a noticeable share
/// (starting the pressure stages early), on otherwise. When
/// `MIMALLOC_ALLOW_THP` is set, it decides.
pub(crate) fn set_huge_pages(thp: Option<bool>, maxmem: Option<usize>, workers: usize) {
    let off = huge_pages_off(thp, maxmem, workers);
    #[cfg(target_os = "linux")]
    if off && std::env::var_os("MIMALLOC_ALLOW_THP").is_none() {
        // SAFETY: PR_SET_THP_DISABLE only sets a flag of the process (new
        // page faults are then served with small pages); it touches no
        // memory.
        unsafe { libc::prctl(libc::PR_SET_THP_DISABLE, 1, 0, 0, 0) };
    }
    #[cfg(not(target_os = "linux"))]
    let _ = off;
}

/// `set_huge_pages`'s choice: whether transparent huge pages are off.
fn huge_pages_off(thp: Option<bool>, maxmem: Option<usize>, workers: usize) -> bool {
    let small = maxmem.is_some_and(|m| m < THP_BUDGET_BASE.saturating_add(THP_BUDGET_PER_WORKER.saturating_mul(workers)));
    thp.map_or(small, |on| !on)
}

/// The signal, panic and allocator setup of the process, in the order it
/// needs: the signal dispositions before any other thread exists, the panic
/// hook before the first panic, and mimalloc as the parser's allocator before
/// any parse.
pub(crate) fn init() {
    // A closed stdout (`tlx check Spec.tla | head -3`) ends the process with
    // SIGPIPE instead of panicking on the failed write (the Rust runtime
    // ignores it).
    #[cfg(unix)]
    // SAFETY: setting a signal disposition has no preconditions.
    unsafe {
        libc::signal(libc::SIGPIPE, libc::SIG_DFL);
    }
    // (Blocked before any thread exists: the evaluation, spill IO and
    // compiled-tier threads all inherit the mask.)
    #[cfg(unix)]
    {
        let signals = block_termination_signals();
        spawn_signal_thread(signals);
    }
    install_panic_hook();
    tlx_runtime::mem::set_purge(purge_allocator);
    set_purge_delay();
    // SAFETY: mimalloc's malloc family (aligned as malloc, null only when
    // out of memory, as tree-sitter's default), installed before any parse
    // and before the threads that parse exist.
    unsafe {
        tlx_front::parse::set_allocator(tlx_front::parse::Allocator {
            malloc: mi_malloc,
            calloc: mi_calloc,
            realloc: mi_realloc,
            free: mi_free,
        });
    }
}

/// Report a panic as one clean line: a panic in tlx is an internal error, and
/// the default hook's "note: run with `RUST_BACKTRACE=1`" hint is noise (a
/// Rust backtrace does not help the user; it is only useful to a developer,
/// who can still ask for it with RUST_BACKTRACE).
fn install_panic_hook() {
    std::panic::set_hook(Box::new(|info| {
        let payload = match info.payload().downcast_ref::<&str>() {
            Some(s) => (*s).to_string(),
            None => match info.payload().downcast_ref::<String>() {
                Some(s) => s.clone(),
                None => "<non-string panic payload>".to_string(),
            },
        };
        match info.location() {
            Some(l) => eprintln!("tlx: internal error: {payload} ({l})"),
            None => eprintln!("tlx: internal error: {payload}"),
        }
        if std::env::var_os("RUST_BACKTRACE").is_some_and(|v| v.to_str() != Some("0")) {
            eprint!("{}", std::backtrace::Backtrace::force_capture());
        }
    }));
}

/// Block SIGINT and SIGTERM in this thread. Called before any other thread
/// is spawned, so every thread inherits the mask and the signals are only
/// delivered to the `sigwait` of `spawn_signal_thread` (never to a default
/// disposition). Returns the set to wait for.
#[cfg(unix)]
fn block_termination_signals() -> libc::sigset_t {
    // SAFETY: `sigemptyset`/`sigaddset`/`pthread_sigmask` only touch the set
    // they are given, which is initialized first.
    unsafe {
        let mut set: libc::sigset_t = std::mem::zeroed();
        libc::sigemptyset(&mut set);
        libc::sigaddset(&mut set, libc::SIGINT);
        libc::sigaddset(&mut set, libc::SIGTERM);
        libc::pthread_sigmask(libc::SIG_BLOCK, &set, std::ptr::null_mut());
        set
    }
}

// Exit ownership is claimed before signal reporting can block on the normal
// writer. Normal termination commits only after reporting and the eval-thread
// join; if sigwait already claimed a signal, that thread owns cleanup and exit.
#[cfg(unix)]
static EXIT_OWNER: std::sync::atomic::AtomicI32 = std::sync::atomic::AtomicI32::new(0);

/// Commit normal process termination, or let an already claimed signal finish.
pub(crate) fn finish_exit() {
    #[cfg(unix)]
    {
        use std::sync::atomic::Ordering;
        if let Err(signal) = EXIT_OWNER.compare_exchange(0, -1, Ordering::AcqRel, Ordering::Acquire) {
            if signal > 0 {
                // The signal thread calls _exit after reporting and cleanup.
                loop {
                    std::thread::park();
                }
            }
        }
    }
}

/// Wait for SIGINT/SIGTERM on a dedicated thread and, on one, report partial
/// statistics if requested and remove the
/// spill directory this process created (the normal end of a run removes
/// the same directory) and exit with the conventional status (128 +
/// signal). With no spill directory the cleanup is a no-op.
#[cfg(unix)]
fn spawn_signal_thread(set: libc::sigset_t) {
    tlx_base::stack::spawn(std::thread::Builder::new().name("tlx-signals".into()), move || loop {
        let mut sig: libc::c_int = 0;
        // SAFETY: `sigwait` writes the signal number into `sig`.
        if unsafe { libc::sigwait(&set, &mut sig) } == 0 {
            use std::sync::atomic::Ordering;
            if EXIT_OWNER.compare_exchange(0, sig, Ordering::AcqRel, Ordering::Acquire).is_err() {
                // Normal exit has already committed; no report/cleanup is pending.
                return;
            }
            // Darwin sends a pipe-write SIGPIPE to the process, so masking
            // only the writer cannot protect other threads. Once shutdown is
            // claimed, ignore it process-wide until _exit completes cleanup.
            // SAFETY: setting a signal disposition has no preconditions; this
            // path never returns to normal execution or restores SIGPIPE.
            unsafe { libc::signal(libc::SIGPIPE, libc::SIG_IGN) };
            bounded_output(crate::stats::interrupted);
            let kept = tlx_runtime::io::cleanup_dir_on_signal();
            if !kept.is_empty() {
                bounded_output(move || {
                    use std::io::Write;
                    for d in kept {
                        let _ = writeln!(
                            std::io::stderr().lock(),
                            "tlx: the checkpoint in {} is kept; continue the run with -recover {}",
                            d.display(),
                            d.display()
                        );
                    }
                });
            }
            // SAFETY: `_exit` ends the process at once; the cleanup is
            // done and no other thread is relied on.
            unsafe { libc::_exit(128 + sig) };
        }
    })
    .expect("failed to spawn the signal thread");
}

/// Reporting must not hold shutdown hostage to a lock or a full pipe. The
/// helper may remain blocked; _exit ends it after the signal thread cleans up.
#[cfg(unix)]
fn bounded_output(f: impl FnOnce() + Send + 'static) {
    let (done, wait) = std::sync::mpsc::channel();
    let writer = tlx_base::stack::spawn(std::thread::Builder::new().name("tlx-final-output".into()), move || {
        f();
        let _ = done.send(());
    });
    if writer.is_ok() {
        let _ = wait.recv_timeout(std::time::Duration::from_secs(1));
    }
}

/// Used by the exiting evaluation thread. No caller resumes search. Claimed
/// signal shutdown separately ignores SIGPIPE process-wide for Darwin.
pub(crate) fn block_report_sigpipe() {
    #[cfg(unix)]
    // SAFETY: the initialized set is live for each call; pthread_sigmask
    // changes only this thread's mask. The thread exits without restoring it,
    // so a pending write-generated SIGPIPE cannot escape during shutdown.
    unsafe {
        let mut pipes: libc::sigset_t = std::mem::zeroed();
        libc::sigemptyset(&mut pipes);
        libc::sigaddset(&mut pipes, libc::SIGPIPE);
        libc::pthread_sigmask(libc::SIG_BLOCK, &pipes, std::ptr::null_mut());
    }
}

#[cfg(test)]
mod tests {
    use super::huge_pages_off;

    #[test]
    fn huge_pages_off_under_small_budgets() {
        const MIB: usize = 1 << 20;
        // The default budget (none given): on.
        assert!(!huge_pages_off(None, None, 8));
        // 512 MiB + 64 MiB per worker.
        assert!(huge_pages_off(None, Some(128 * MIB), 1));
        assert!(!huge_pages_off(None, Some(576 * MIB), 1));
        assert!(huge_pages_off(None, Some(1023 * MIB), 8));
        assert!(!huge_pages_off(None, Some(1024 * MIB), 8));
        assert!(huge_pages_off(None, Some(4 << 30), 64));
        // TLX_THP decides.
        assert!(!huge_pages_off(Some(true), Some(128 * MIB), 8));
        assert!(huge_pages_off(Some(false), None, 1));
    }
}
