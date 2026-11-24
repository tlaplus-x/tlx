//! A run ended by SIGINT or SIGTERM removes the spill directory tlx
//! created and exits with the conventional status `128 + signal`;
//! a normal run removes the same directory, so a killed one leaves no
//! `states/` behind. A `-metadir` that already existed is never removed:
//! only the files tlx created in it (the lock file, the spill files).
//!
//! The spec is a counter with a bound far larger than the run needs: it is
//! still searching when the signal arrives, so the spill directory (created
//! by `-spill always` from the start) exists and must be gone afterwards.

use std::path::{Path, PathBuf};
use std::process::{Child, ExitStatus, Stdio};
use std::time::{Duration, Instant};

/// 10^9 states: never finishes within the test, so the signal always arrives
/// while the search is running.
const SPEC: &str = "---- MODULE SigSpec ----\nEXTENDS Naturals\nVARIABLE x\nInit == x = 0\nNext == x < 1000000000 /\\ x' = x + 1\n====\n";
const CFG: &str = "INIT Init\nNEXT Next\nCHECK_DEADLOCK FALSE\n";

/// A fresh directory holding the spec.
fn spec_dir(_tag: &str) -> tlx_testkit::TempDir {
    tlx_testkit::TempDir::with_spec("signals", SPEC, CFG)
}

/// Run tlx from `dir` with `args`: a `-spill always` run whose small
/// segments make the spill files appear early even for a small model.
fn spawn(dir: &Path, args: &[&str]) -> Child {
    use std::os::unix::process::CommandExt;
    let mut cmd = tlx_testkit::tlx!();
    cmd.args(["check", "SigSpec.tla", "-config", "SigSpec.cfg", "-spill", "always"])
        .args(args)
        .dir(dir)
        // The default metadir (a `states/<time>` next to the spec) is the
        // one tlx removes.
        .env("TLX_SEG_BYTES", "4096")
        .command()
        .stdout(Stdio::null())
        .stderr(Stdio::null());
    // A test run in the background (`cargo test &`, a script) inherits
    // SIGINT ignored, and so would tlx, which keeps an ignored signal
    // ignored: restore the default dispositions in the child.
    // SAFETY: `signal` is async-signal-safe (allowed between fork and exec).
    unsafe {
        cmd.command().pre_exec(|| {
            libc::signal(libc::SIGINT, libc::SIG_DFL);
            libc::signal(libc::SIGTERM, libc::SIG_DFL);
            Ok(())
        });
    }
    cmd.command().spawn().expect("spawn tlx")
}

/// Wait (up to `timeout`) for an entry under `dir` matching `want`; the
/// child is killed first if none appears.
fn wait_for(dir: &Path, want: impl Fn(&Path) -> bool, child: &mut Child, timeout: Duration) -> Option<PathBuf> {
    let deadline = Instant::now() + timeout;
    loop {
        if let Ok(rd) = std::fs::read_dir(dir) {
            if let Some(e) = rd.flatten().find(|e| want(&e.path())) {
                return Some(e.path());
            }
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            let _ = child.wait();
            return None;
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

/// Wait (up to `timeout`) for the child; kills it if it does not end.
fn wait_timeout(child: &mut Child, timeout: Duration) -> Option<ExitStatus> {
    let deadline = Instant::now() + timeout;
    loop {
        if let Some(s) = child.try_wait().unwrap() {
            return Some(s);
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            let _ = child.wait();
            return None;
        }
        std::thread::sleep(Duration::from_millis(10));
    }
}

/// Send `sig` to a run whose spill directory appeared, and check it exits
/// with `128 + sig`.
fn kill_and_check(child: &mut Child, sig: libc::c_int) {
    // SAFETY: `child` is alive (not yet waited on); a valid pid.
    unsafe { libc::kill(child.id() as libc::pid_t, sig) };
    let status = wait_timeout(child, Duration::from_secs(30)).expect("tlx did not exit after the signal");
    assert_eq!(status.code(), Some(128 + sig), "exit status for signal {sig}");
}

/// The default `states/<time>` directory tlx created is removed on SIGINT
/// and SIGTERM.
fn signal_case(tag: &str, sig: libc::c_int) {
    let dir = spec_dir(tag);
    let mut child = spawn(&dir, &[]);
    let states = dir.join("states");
    let spill = wait_for(&states, |p| p.is_dir(), &mut child, Duration::from_secs(30)).expect("no spill directory appeared");
    kill_and_check(&mut child, sig);
    assert!(!spill.exists(), "the spill directory {} was left behind", spill.display());
    // (tlx created the `states` directory too: it is removed when empty.)
    assert!(!states.exists(), "the states directory {} was left behind", states.display());
}

/// A `-metadir` that already existed is kept; only the files tlx created
/// in it (the lock file, the spill files) are removed.
#[test]
fn sigterm_keeps_an_existing_metadir() {
    let dir = spec_dir("metadir");
    let meta = dir.join("user-dir");
    std::fs::create_dir_all(&meta).unwrap();
    let mut child = spawn(&dir, &["-metadir", meta.to_str().unwrap()]);
    wait_for(&meta, |p| p.extension().is_some_and(|e| e == "spill"), &mut child, Duration::from_secs(30)).expect("no spill file appeared");
    kill_and_check(&mut child, libc::SIGTERM);
    assert!(meta.is_dir(), "a given -metadir was removed");
    assert!(!meta.join("LOCK").exists(), "the lock file was left behind");
    let stray: Vec<_> =
        std::fs::read_dir(&meta).unwrap().flatten().map(|e| e.path()).filter(|p| p.extension().is_some_and(|e| e == "spill")).collect();
    assert!(stray.is_empty(), "spill files were left behind: {stray:?}");
}

#[test]
fn sigterm_removes_the_spill_directory() {
    signal_case("term", libc::SIGTERM);
}

#[test]
fn sigint_removes_the_spill_directory() {
    signal_case("int", libc::SIGINT);
}
