//! Fatal stack-fault reporting. All OS queries, mapping and registration
//! happen before work starts, never in the signal handler.

use std::cell::RefCell;
use std::io;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::OnceLock;

// Do not use Rust TLS in the handler: even a const TLS access can enter the
// dynamic loader on macOS. Instead identify the current thread by the local
// handler frame's address on its unique alternate stack. All records live
// forever and contain only lock-free native-word atomics; slots are reused
// after a thread restores its old alternate stack. Refuse excess threads
// loudly rather than silently leaving them unprotected.
struct Record {
    alt_lo: AtomicUsize,
    alt_hi: AtomicUsize,
    guard_lo: AtomicUsize,
    guard_hi: AtomicUsize,
}

static RECORDS: [Record; 4096] = [const {
    Record { alt_lo: AtomicUsize::new(0), alt_hi: AtomicUsize::new(0), guard_lo: AtomicUsize::new(0), guard_hi: AtomicUsize::new(0) }
}; 4096];

const ALT_SIZE: usize = 64 << 10;

struct Registration {
    slot: &'static Record,
    old: libc::stack_t,
    mapping: *mut libc::c_void,
    size: usize,
}

impl Drop for Registration {
    fn drop(&mut self) {
        // SAFETY: this registration owns the mapping, is dropped on its
        // creating thread, and is not itself a signal-handler frame.
        unsafe {
            if libc::sigaltstack(&self.old, std::ptr::null_mut()) == 0 {
                self.slot.alt_lo.store(0, Ordering::Release);
                libc::munmap(self.mapping, self.size);
            }
            // If restoring fails, retain the mapping and slot: freeing an
            // active signal stack would be unsafe.
        }
    }
}

thread_local! {
    static REGISTRATION: RefCell<Option<Registration>> = const { RefCell::new(None) };
}

#[cfg(miri)]
pub(super) fn install() -> io::Result<()> {
    // Miri cannot emulate the alternate signal stack, `sigaction` or `mmap`;
    // the fallback is exercised by the native tests (docs/unsafe-audit.md).
    Ok(())
}

#[cfg(not(miri))]
pub(super) fn install() -> io::Result<()> {
    REGISTRATION.with(|registration| {
        let mut registration = registration.borrow_mut();
        if registration.is_some() {
            return Ok(());
        }
        // SAFETY: queries of this thread's stack and the process page size.
        let page = unsafe { libc::sysconf(libc::_SC_PAGESIZE) };
        if page <= 0 {
            return Err(io::Error::last_os_error());
        }
        let page = page as usize;
        let (lo, _) = super::bounds().ok_or_else(|| io::Error::other("cannot query stack bounds"))?;
        let (guard_lo, guard_hi) = guard(lo, page)?;
        let slot = RECORDS
            .iter()
            .find(|r| r.alt_lo.compare_exchange(0, usize::MAX, Ordering::Acquire, Ordering::Relaxed).is_ok())
            .ok_or_else(|| io::Error::other("too many threads for stack-overflow fallback"))?;
        // SAFETY: anonymous private mapping with a positive page-multiple
        // length and no backing descriptor. Check MAP_FAILED before use;
        // the registration owns this mapping until successful stack restore.
        let mapping = unsafe {
            libc::mmap(std::ptr::null_mut(), ALT_SIZE + page, libc::PROT_READ | libc::PROT_WRITE, libc::MAP_PRIVATE | libc::MAP_ANON, -1, 0)
        };
        if mapping == libc::MAP_FAILED {
            slot.alt_lo.store(0, Ordering::Release);
            return Err(io::Error::last_os_error());
        }
        // SAFETY: the page-aligned mapping spans ALT_SIZE + page bytes;
        // mprotect covers only its first page. The remaining live writable
        // bytes form this thread's stack. Zeroed stack_t is a valid output
        // object, and sigaltstack copies alt/old without retaining references.
        unsafe {
            let mut old: libc::stack_t = std::mem::zeroed();
            let alt = libc::stack_t { ss_sp: mapping.cast::<u8>().add(page).cast(), ss_size: ALT_SIZE, ss_flags: 0 };
            if libc::mprotect(mapping, page, libc::PROT_NONE) != 0 || libc::sigaltstack(&alt, &mut old) != 0 {
                let error = io::Error::last_os_error();
                slot.alt_lo.store(0, Ordering::Release);
                libc::munmap(mapping, ALT_SIZE + page);
                return Err(error);
            }
            // macOS requires at least MINSIGSTKSZ even when disabling an
            // alternate stack (POSIX says ss_size is ignored in that case).
            if old.ss_flags & libc::SS_DISABLE != 0 {
                old.ss_size = ALT_SIZE;
            }
            let lo = alt.ss_sp as usize;
            slot.alt_hi.store(lo + ALT_SIZE, Ordering::Relaxed);
            slot.guard_lo.store(guard_lo, Ordering::Relaxed);
            slot.guard_hi.store(guard_hi, Ordering::Relaxed);
            slot.alt_lo.store(lo, Ordering::Release);
            *registration = Some(Registration { slot, old, mapping, size: ALT_SIZE + page });
        }
        static HANDLERS: OnceLock<Result<(), i32>> = OnceLock::new();
        let result = HANDLERS.get_or_init(install_handlers).map_err(io::Error::from_raw_os_error);
        if result.is_err() {
            registration.take();
        }
        result
    })
}

#[cfg(target_os = "macos")]
fn guard(lo: usize, page: usize) -> io::Result<(usize, usize)> {
    // Rust protects the first stack page of the main thread at startup;
    // pthread-created stacks have the OS guard immediately below the base.
    // SAFETY: plain query about the calling thread.
    Ok(if unsafe { libc::pthread_main_np() } != 0 { (lo, lo + page) } else { (lo - page, lo) })
}

#[cfg(any(target_os = "linux", target_os = "android"))]
fn guard(lo: usize, page: usize) -> io::Result<(usize, usize)> {
    // SAFETY: initialize/query/destroy attributes of the calling thread.
    unsafe {
        let mut attr = std::mem::zeroed();
        let code = libc::pthread_getattr_np(libc::pthread_self(), &mut attr);
        if code != 0 {
            return Err(io::Error::from_raw_os_error(code));
        }
        let mut size = 0;
        let code = libc::pthread_attr_getguardsize(&attr, &mut size);
        libc::pthread_attr_destroy(&mut attr);
        if code != 0 {
            return Err(io::Error::from_raw_os_error(code));
        }
        // A zero-sized main-thread guard is the kernel's stack limit. musl
        // and modern glibc guards are below the base; glibc < 2.27 included
        // the guard inside the reported stack. Like std's overflow handler,
        // accept both glibc conventions, but never a null/synthetic fault.
        let hi = if cfg!(target_env = "gnu") && size > 0 { lo + size } else { lo };
        let size = size.max(page);
        Ok((lo.saturating_sub(size), hi))
    }
}

fn install_handlers() -> Result<(), i32> {
    // SAFETY: initialized sigaction with a matching SA_SIGINFO C callback;
    // sigemptyset initializes its mask. The kernel copies the struct, and
    // the callback code and atomic registry live for the entire process.
    unsafe {
        let mut action: libc::sigaction = std::mem::zeroed();
        libc::sigemptyset(&mut action.sa_mask);
        action.sa_flags = libc::SA_SIGINFO | libc::SA_ONSTACK;
        action.sa_sigaction = handler as *const () as libc::sighandler_t;
        for sig in [libc::SIGSEGV, libc::SIGBUS] {
            if libc::sigaction(sig, &action, std::ptr::null_mut()) != 0 {
                return Err(io::Error::last_os_error().raw_os_error().unwrap_or(libc::EINVAL));
            }
        }
    }
    Ok(())
}

/// # Safety
/// Only the kernel invokes this SA_SIGINFO callback for SIGSEGV/SIGBUS;
/// info is aligned, initialized and readable for this invocation. No Rust
/// allocation, TLS, locking, formatting or unwinding is allowed here.
unsafe extern "C" fn handler(sig: libc::c_int, info: *mut libc::siginfo_t, _: *mut libc::c_void) {
    let marker = 0u8;
    let sp = std::ptr::addr_of!(marker) as usize;
    // SAFETY: the kernel passes a valid siginfo for our SA_SIGINFO handler.
    let fault = unsafe { (*info).si_addr() as usize };
    // SAFETY: the same live siginfo contains the initialized signal code.
    if fault != 0 && unsafe { (*info).si_code } > 0 {
        for record in &RECORDS {
            let lo = record.alt_lo.load(Ordering::Acquire);
            if lo != 0 && lo != usize::MAX && sp >= lo && sp < record.alt_hi.load(Ordering::Relaxed) {
                if fault >= record.guard_lo.load(Ordering::Relaxed) && fault < record.guard_hi.load(Ordering::Relaxed) {
                    // SAFETY: static byte strings, no allocation, TLS,
                    // formatting, locking, unwinding or Rust IO. Only the
                    // async-signal-safe write and _exit syscalls are used.
                    unsafe {
                        write_all(b"Error: ");
                        write_all(super::OVERFLOW_MESSAGE.as_bytes());
                        write_all(b"\n");
                        libc::_exit(super::OVERFLOW_EXIT.into());
                    }
                }
                break;
            }
        }
    }
    // Unrelated faults retain the default signal death (including a core
    // dump where enabled). sigaction and raise are async-signal-safe; raise
    // also handles synthetic signals which would not fault again on return.
    // SAFETY: sig is one of our registered signals; the initialized local
    // action is copied by sigaction. Neither syscall unwinds into Rust.
    unsafe {
        let mut action: libc::sigaction = std::mem::zeroed();
        action.sa_sigaction = libc::SIG_DFL;
        libc::sigaction(sig, &action, std::ptr::null_mut());
        libc::raise(sig);
    }
}

/// # Safety
/// Called only with live static diagnostic bytes from the signal handler;
/// must remain allocation-, TLS-, lock- and panic-free even on write failure.
unsafe fn write_all(mut bytes: &[u8]) {
    while !bytes.is_empty() {
        // SAFETY: bytes is a live static string. Avoid errno/TLS on failure;
        // error reporting is best effort, termination must still happen.
        let n = unsafe { libc::write(libc::STDERR_FILENO, bytes.as_ptr().cast(), bytes.len()) };
        if n <= 0 {
            break;
        }
        bytes = &bytes[n as usize..];
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn restores_alternate_stack_and_reuses_registration_slots() {
        // More registrations than the entire registry can hold: sequential
        // work must release slots, including when a thread initially has no
        // alternate stack. Each installation is also idempotent.
        // SAFETY: query/change only this test thread's alternate stack,
        // outside a handler. All stack_t objects are initialized and live;
        // old's original backing stack is retained until restored below.
        unsafe {
            let mut old: libc::stack_t = std::mem::zeroed();
            assert_eq!(libc::sigaltstack(std::ptr::null(), &mut old), 0);
            let disabled = libc::stack_t { ss_sp: std::ptr::null_mut(), ss_flags: libc::SS_DISABLE, ss_size: ALT_SIZE };
            for _ in 0..=RECORDS.len() {
                assert_eq!(libc::sigaltstack(&disabled, std::ptr::null_mut()), 0);
                install().unwrap();
                install().unwrap();
                REGISTRATION.with(|r| r.borrow_mut().take());
                let mut restored: libc::stack_t = std::mem::zeroed();
                assert_eq!(libc::sigaltstack(std::ptr::null(), &mut restored), 0);
                assert_ne!(restored.ss_flags & libc::SS_DISABLE, 0);
            }
            assert_eq!(libc::sigaltstack(&old, std::ptr::null_mut()), 0);
        }
    }
}
