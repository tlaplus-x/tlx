//! The native stack of the current thread: how much of it is left.
//!
//! Deep recursion (the interpreter's recursion through operator and function
//! applications) must stop with an evaluation error before the stack
//! overflows. A fixed nesting limit cannot guarantee that: the native stack
//! one nesting level takes differs by recursion kind, compiler and platform
//! (it took 320–384 MiB on macOS and more than 512 MiB on Linux arm64 for
//! 100,000 levels of a recursion through a function application). So the
//! recursion guards also ask [`low`] whether the stack is nearly used up.

use std::cell::Cell;

#[cfg(any(target_os = "macos", target_os = "linux", target_os = "android"))]
mod overflow;

/// TLC-style explanation shared by the depth guard and the fatal fallback.
pub const OVERFLOW_MESSAGE: &str = "This was a stack overflow. It was probably the result of an incorrect \
recursive operator or function definition that caused tlx to enter an infinite loop when trying \
to compute the function or its application to an element in its putative domain.";

/// Evaluation-error exit status used when a stack fault cannot be unwound.
pub const OVERFLOW_EXIT: u8 = 75;

/// Install the fatal overflow fallback for the calling thread, once. Call
/// this before work on a foreign thread; tlx's spawn helpers do it for you.
/// Unsupported platforms keep their existing stack-overflow behavior.
pub fn install_current() -> std::io::Result<()> {
    #[cfg(any(target_os = "macos", target_os = "linux", target_os = "android"))]
    overflow::install()?;
    Ok(())
}

/// Spawn an ordinary thread with the overflow fallback installed before `f`.
pub fn spawn<F, T>(builder: std::thread::Builder, f: F) -> std::io::Result<std::thread::JoinHandle<T>>
where
    F: FnOnce() -> T + Send + 'static,
    T: Send + 'static,
{
    builder.spawn(move || {
        install_current().expect("failed to install stack-overflow fallback");
        f()
    })
}

/// Spawn a scoped thread with the overflow fallback installed before `f`.
pub fn spawn_scoped<'scope, 'env, F, T>(
    builder: std::thread::Builder,
    scope: &'scope std::thread::Scope<'scope, 'env>,
    f: F,
) -> std::io::Result<std::thread::ScopedJoinHandle<'scope, T>>
where
    F: FnOnce() -> T + Send + 'scope,
    T: Send + 'scope,
{
    builder.spawn_scoped(scope, move || {
        install_current().expect("failed to install stack-overflow fallback");
        f()
    })
}

/// Scoped spawn with the platform's default stack size.
pub fn spawn_default<'scope, 'env, F, T>(scope: &'scope std::thread::Scope<'scope, 'env>, f: F) -> std::thread::ScopedJoinHandle<'scope, T>
where
    F: FnOnce() -> T + Send + 'scope,
    T: Send + 'scope,
{
    spawn_scoped(std::thread::Builder::new(), scope, f).expect("failed to spawn thread")
}

/// Bounds of the current thread's stack: (lowest usable address, size), or
/// `None` where the platform does not tell.
#[cfg(miri)]
fn bounds() -> Option<(usize, usize)> {
    // Miri cannot query a thread's stack bounds (`pthread_getattr_np`), and
    // cannot provide the alternate signal stack the fatal fallback needs (see
    // `overflow`). Reporting unknown keeps the depth guards on their fixed
    // nesting caps; the guard itself is covered by the native tests.
    None
}

/// Bounds of the current thread's stack: (lowest usable address, size), or
/// `None` where the platform does not tell.
#[cfg(all(not(miri), target_vendor = "apple"))]
fn bounds() -> Option<(usize, usize)> {
    // SAFETY: plain queries about the calling thread.
    unsafe {
        let me = libc::pthread_self();
        let top = libc::pthread_get_stackaddr_np(me) as usize;
        let size = libc::pthread_get_stacksize_np(me);
        (top > size && size > 0).then(|| (top - size, size))
    }
}

/// Bounds of the current thread's stack: (lowest usable address, size), or
/// `None` where the platform does not tell.
#[cfg(all(not(miri), any(target_os = "linux", target_os = "android")))]
fn bounds() -> Option<(usize, usize)> {
    // SAFETY: `attr` is initialized by `pthread_getattr_np` before it is
    // read and destroyed afterwards.
    unsafe {
        let mut attr: libc::pthread_attr_t = std::mem::zeroed();
        if libc::pthread_getattr_np(libc::pthread_self(), &mut attr) != 0 {
            return None;
        }
        let mut addr: *mut libc::c_void = std::ptr::null_mut();
        let mut size: libc::size_t = 0;
        let ok = libc::pthread_attr_getstack(&attr, &mut addr, &mut size) == 0;
        libc::pthread_attr_destroy(&mut attr);
        // glibc < 2.27 included the guard in this range; newer glibc and
        // musl put it below. The fatal fallback handles both conventions.
        (ok && size > 0).then_some((addr as usize, size))
    }
}

#[cfg(all(not(miri), not(any(target_vendor = "apple", target_os = "linux", target_os = "android"))))]
fn bounds() -> Option<(usize, usize)> {
    None
}

/// Stack left unused when [`low`] starts reporting a low stack: an eighth of
/// the stack, at least 64 KiB and at most 32 MiB. It must cover what is used
/// between two checks (one level of the checked recursion with everything it
/// evaluates on the way) and the unwinding and error reporting after one.
fn reserve(size: usize) -> usize {
    (size / 8).clamp(64 << 10, 32 << 20)
}

thread_local! {
    /// Address below which the current thread's stack counts as low:
    /// `usize::MAX` before the first query, 0 when unknown.
    static LIMIT: Cell<usize> = const { Cell::new(usize::MAX) };
}

#[cold]
fn init_limit() -> usize {
    let limit = bounds().map_or(0, |(lo, size)| lo + reserve(size));
    LIMIT.with(|l| l.set(limit));
    limit
}

/// Whether the current thread has used its stack up to the reserve, so a
/// recursion should stop with an error now. Cheap: one thread-local read
/// and a compare after the first call on a thread.
#[inline]
pub fn low() -> bool {
    let mut limit = LIMIT.with(|l| l.get());
    if limit == usize::MAX {
        limit = init_limit();
    }
    let marker = 0u8;
    let sp = std::ptr::addr_of!(marker) as usize;
    sp < limit
}

/// Stack size of every thread that evaluates TLA+ (the main thread included).
/// The interpreter recurses on operator/function application and uses a few
/// KiB of native stack per level, so its recursion guard
/// (crates/tlx-eval/src/depth.rs) can allow a deep nesting only if the stack
/// is large (where the stack runs out first, the guard stops at
/// [`low`]). 512 MiB is virtual address space; only the pages a deep
/// recursion actually touches are committed.
pub const EVAL_STACK_SIZE: usize = 512 << 20;

/// Spawn a thread in `scope` with [`EVAL_STACK_SIZE`] (a plain
/// `Scope::spawn` would use the 2 MiB default, too little for deep
/// recursion).
pub fn spawn_eval<'scope, 'env, F, T>(scope: &'scope std::thread::Scope<'scope, 'env>, f: F) -> std::thread::ScopedJoinHandle<'scope, T>
where
    F: FnOnce() -> T + Send + 'scope,
    T: Send + 'scope,
{
    spawn_with(scope, EVAL_STACK_SIZE, f)
}

fn spawn_with<'scope, 'env, F, T>(
    scope: &'scope std::thread::Scope<'scope, 'env>,
    size: usize,
    f: F,
) -> std::thread::ScopedJoinHandle<'scope, T>
where
    F: FnOnce() -> T + Send + 'scope,
    T: Send + 'scope,
{
    spawn_named_with(scope, size, None, f).expect("failed to spawn evaluation thread")
}

fn spawn_named_with<'scope, 'env, F, T>(
    scope: &'scope std::thread::Scope<'scope, 'env>,
    size: usize,
    name: Option<&str>,
    f: F,
) -> std::io::Result<std::thread::ScopedJoinHandle<'scope, T>>
where
    F: FnOnce() -> T + Send + 'scope,
    T: Send + 'scope,
{
    let mut builder = std::thread::Builder::new().stack_size(size);
    if let Some(name) = name {
        builder = builder.name(name.into());
    }
    spawn_scoped(builder, scope, f)
}

pub fn run_on_big_stack<R: Send>(size: usize, f: impl FnOnce() -> R + Send) -> R {
    run_on_named_stack(size, None, f)
}

pub fn run_on_named_stack<R: Send>(size: usize, name: Option<&str>, f: impl FnOnce() -> R + Send) -> R {
    std::thread::scope(|scope| {
        spawn_named_with(scope, size, name, f)
            .expect("failed to spawn the evaluation thread")
            .join()
            .unwrap_or_else(|payload| std::panic::resume_unwind(payload))
    })
}

#[inline]
pub fn too_deep(depth: u32, max: u32) -> bool {
    depth >= max || low()
}

#[cfg(test)]
mod tests {
    #[test]
    fn borrowed_work_and_panics_cross_the_stack_thread() {
        let mut value = 0;
        super::run_on_big_stack(4 << 20, || value = 42);
        assert_eq!(value, 42);
        let result = std::panic::catch_unwind(|| super::run_on_big_stack(4 << 20, || std::panic::panic_any(17usize)));
        assert_eq!(*result.unwrap_err().downcast::<usize>().unwrap(), 17);
        super::run_on_named_stack(4 << 20, Some("tlx"), || {
            assert_eq!(std::thread::current().name(), Some("tlx"));
            assert!(super::too_deep(3, 3));
            assert!(!super::too_deep(0, 3));
        });
    }

    #[test]
    fn deep_recursion_reports_low_stack() {
        fn dive(n: u64) -> u64 {
            if super::low() {
                return n;
            }
            let pad = std::hint::black_box([n; 64]);
            dive(n + 1) + pad[3] % 2
        }
        let t = std::thread::Builder::new().stack_size(4 << 20).spawn(|| dive(0)).unwrap();
        let n = t.join().expect("the recursion stopped before the stack overflowed");
        if cfg!(any(target_vendor = "apple", target_os = "linux")) {
            assert!(n > 100, "stopped at {n}");
        }
    }
}
