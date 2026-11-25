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
    spawn_with_stderr(dir, args, Stdio::null())
}

fn spawn_with_stderr(dir: &Path, args: &[&str], stderr: Stdio) -> Child {
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
        .stderr(stderr);
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
    assert_eq!(status.code(), Some(128 + sig), "exit status for signal {sig}: {status}");
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

/// Both termination signals preserve a partial report in the requested file,
/// including counters published by a still-running worker.
#[test]
fn signals_write_partial_json_stats() {
    for sig in [libc::SIGTERM, libc::SIGINT] {
        let dir = spec_dir("stats");
        let meta = dir.join("spill");
        let mut child = spawn(&dir, &["-interp", "-workers", "2", "-metadir", meta.to_str().unwrap(), "-stats", "json=partial.json"]);
        wait_for(&meta, |p| p.extension().is_some_and(|e| e == "spill"), &mut child, Duration::from_secs(30))
            .expect("no spill file appeared");
        kill_and_check(&mut child, sig);
        let report = std::fs::read_to_string(dir.join("partial.json")).expect("missing partial stats");
        assert!(report.contains("\"interrupted\":true"), "{report}");
        assert!(report.contains("\"units\":"), "{report}");
        assert!(!report.contains("\"units\":0,"), "{report}");
        assert!(!meta.exists());
    }
}

#[test]
fn signals_respect_stderr_stats_format_and_opt_in() {
    for args in [vec![], vec!["-stats"], vec!["-stats", "json"]] {
        let dir = spec_dir("stderr-stats");
        let stderr = std::fs::File::create(dir.join("stderr")).unwrap();
        let mut child = spawn_with_stderr(&dir, &args, stderr.into());
        wait_for(&dir.join("states"), |p| p.is_dir(), &mut child, Duration::from_secs(30)).expect("no spill directory");
        kill_and_check(&mut child, libc::SIGTERM);
        let report = std::fs::read_to_string(dir.join("stderr")).unwrap();
        if args.is_empty() {
            assert!(!report.contains("interrupted"), "{report}");
        } else if args.len() == 1 {
            assert!(report.contains("Partial statistics"), "{report}");
        } else {
            assert!(report.contains("\"interrupted\":true"), "{report}");
        }
    }
}

// Linux supplies both CLOEXEC pipe creation and an adjustable pipe capacity.
#[cfg(target_os = "linux")]
fn stats_pipe() -> (std::fs::File, std::fs::File) {
    use std::os::fd::FromRawFd;
    let mut fds = [-1; 2];
    // SAFETY: pipe2 initializes both descriptors on success. CLOEXEC keeps
    // retained ends out of the child, except the descriptor duped to stderr.
    assert_eq!(unsafe { libc::pipe2(fds.as_mut_ptr(), libc::O_CLOEXEC) }, 0);
    // SAFETY: each fresh descriptor acquires exactly one owning File.
    unsafe { (std::fs::File::from_raw_fd(fds[0]), std::fs::File::from_raw_fd(fds[1])) }
}

#[cfg(target_os = "linux")]
struct Reap(Child);
#[cfg(target_os = "linux")]
impl Drop for Reap {
    fn drop(&mut self) {
        let _ = self.0.kill();
        let _ = self.0.wait();
    }
}

/// Hold a normal JSON report in a full pipe, deliver a signal, then let the
/// writer finish. The main thread must not exit while the signal thread waits
/// for that writer; the final report and exit code belong to the signal.
#[cfg(target_os = "linux")]
#[test]
fn signals_during_normal_reporting_own_the_final_report_and_exit() {
    use std::io::Read;
    use std::os::fd::AsRawFd;
    use std::sync::mpsc;
    for (signal, reader_action) in
        [libc::SIGINT, libc::SIGTERM].into_iter().flat_map(|sig| ["drain", "close", "idle"].map(|action| (sig, action)))
    {
        let dir = spec_dir("report-race");
        let (mut stderr, writer) = stats_pipe();
        // SAFETY: writer owns this pipe. Linux rounds the requested minimum
        // up to a page; use the returned capacity, never an assumed page size.
        let capacity = unsafe { libc::fcntl(writer.as_raw_fd(), libc::F_SETPIPE_SZ, 1) };
        assert!(capacity > 0);
        // Each depth contributes at least one JSON byte. Even after reading
        // the short prefix, the full report cannot fit and finish before kill.
        let steps = (capacity as usize * 2 + 1000).to_string();
        std::fs::write(dir.join("SigSpec.tla"), SPEC.replace("1000000000", &steps)).unwrap();
        let mut child = Reap(spawn_with_stderr(&dir, &["-interp", "-maxmem", "128", "-stats", "json"], writer.into()));
        let (ready_tx, ready_rx) = mpsc::channel();
        let (drain_tx, drain_rx) = mpsc::channel();
        let reader = std::thread::spawn(move || {
            let mut output = Vec::new();
            let mut byte = [0];
            while stderr.read_exact(&mut byte).is_ok() {
                output.push(byte[0]);
                if output.ends_with(b"{\"sample_every\":") {
                    ready_tx.send(()).unwrap();
                    let _ = drain_rx.recv();
                    if reader_action == "drain" {
                        stderr.read_to_end(&mut output).unwrap();
                    }
                    break;
                }
            }
            String::from_utf8(output).unwrap()
        });
        if ready_rx.recv_timeout(Duration::from_secs(30)).is_err() {
            let _ = child.0.kill();
            let _ = child.0.wait();
            let _ = drain_tx.send(());
            panic!("normal JSON report did not start: {}", reader.join().unwrap());
        }
        // SAFETY: this is our unreaped child, blocked writing its normal report.
        assert_eq!(unsafe { libc::kill(child.0.id() as libc::pid_t, signal) }, 0);
        // Allow sigwait to claim the signal while normal reporting is blocked.
        std::thread::sleep(Duration::from_millis(100));
        if reader_action != "idle" {
            drain_tx.send(()).unwrap();
        }
        let status = wait_timeout(&mut child.0, Duration::from_secs(3));
        if reader_action == "idle" {
            drain_tx.send(()).unwrap();
        }
        let output = reader.join().unwrap();
        assert_eq!(status.and_then(|s| s.code()), Some(128 + signal), "{output}");
        if reader_action != "drain" {
            continue;
        }
        let reports: Vec<_> = output.lines().filter(|line| line.starts_with("{\"sample_every\":")).collect();
        assert!(reports.first().is_some_and(|r| r.contains("\"interrupted\":false")), "normal report not exercised");
        assert!(reports.last().is_some_and(|r| r.contains("\"interrupted\":true")), "{output}");
    }
}

/// A broken report destination must not bypass spill cleanup or signal exit.
/// Exercise both stderr formats and the failed-file diagnostic on stderr.
fn failed_report_case(format: &str, stderr: Stdio, close_reader: bool, sig: libc::c_int) {
    let dir = spec_dir("failed-report");
    let meta = dir.join("spill");
    let mut child = spawn_with_stderr(
        &dir,
        &["-interp", "-workers", "2", "-maxmem", "128", "-metadir", meta.to_str().unwrap(), "-stats", format],
        stderr,
    );
    wait_for(&meta, |p| p.extension().is_some_and(|e| e == "spill"), &mut child, Duration::from_secs(30)).expect("no spill file appeared");
    if close_reader {
        drop(child.stderr.take().expect("piped stderr"));
    }
    kill_and_check(&mut child, sig);
    assert!(!meta.exists(), "failed reporting left spill data behind");
}

#[test]
fn signals_clean_up_when_stats_pipe_is_closed() {
    for sig in [libc::SIGINT, libc::SIGTERM] {
        for format in ["text", "json", "json=missing/report.json"] {
            failed_report_case(format, Stdio::piped(), true, sig);
        }
    }
}

#[cfg(target_os = "linux")]
#[test]
fn signals_clean_up_when_stats_output_is_full() {
    for sig in [libc::SIGINT, libc::SIGTERM] {
        for format in ["text", "json", "json=/dev/full"] {
            let full = std::fs::OpenOptions::new().write(true).open("/dev/full").unwrap();
            failed_report_case(format, full.into(), false, sig);
        }
    }
}

// Keep the reader open without draining until the child exits: reporting must
// time out while search is active, then clean up before the supervisor kills it.
#[cfg(target_os = "linux")]
#[test]
fn signals_clean_up_without_draining_stats() {
    use std::io::{ErrorKind, Write};
    use std::os::fd::AsRawFd;

    for sig in [libc::SIGINT, libc::SIGTERM] {
        let dir = spec_dir("idle-reader");
        let meta = dir.join("spill");
        let (_reader, mut writer) = stats_pipe();
        let mut child = Reap(spawn_with_stderr(
            &dir,
            &["-interp", "-workers", "1", "-maxmem", "128", "-metadir", meta.to_str().unwrap(), "-stats", "json"],
            writer.try_clone().unwrap().into(),
        ));
        wait_for(&meta, |p| p.extension().is_some_and(|e| e == "spill"), &mut child.0, Duration::from_secs(30))
            .expect("no spill file appeared");
        // SAFETY: writer owns the live pipe descriptor. Its file status flags
        // are shared with child stderr; restore blocking before signaling.
        let flags = unsafe { libc::fcntl(writer.as_raw_fd(), libc::F_GETFL) };
        assert!(flags >= 0);
        // SAFETY: writer still owns this descriptor; only O_NONBLOCK changes.
        assert_eq!(unsafe { libc::fcntl(writer.as_raw_fd(), libc::F_SETFL, flags | libc::O_NONBLOCK) }, 0);
        // Single bytes fill even the last available slot, independent of page
        // size, pipe capacity, search speed, and stats snapshot publication.
        loop {
            match writer.write(&[0]) {
                Ok(1) => {}
                Err(e) if e.kind() == ErrorKind::Interrupted => continue,
                Err(e) if e.kind() == ErrorKind::WouldBlock => break,
                result => panic!("could not fill stderr pipe: {result:?}"),
            }
        }
        // SAFETY: the owned descriptor is still live; restore its saved flags.
        assert_eq!(unsafe { libc::fcntl(writer.as_raw_fd(), libc::F_SETFL, flags) }, 0);
        // SAFETY: child is our live, unreaped subprocess.
        assert_eq!(unsafe { libc::kill(child.0.id() as libc::pid_t, sig) }, 0);
        let status = wait_timeout(&mut child.0, Duration::from_secs(3)).expect("reporting blocked shutdown");
        assert_eq!(status.code(), Some(128 + sig));
        assert!(!meta.exists(), "spill data survived shutdown");
        // _reader stays open and idle until after the child has exited.
    }
}
