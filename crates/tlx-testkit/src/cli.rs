use std::ffi::OsStr;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
use std::time::Duration;

pub fn scrub(command: &mut Command) {
    for (name, _) in std::env::vars_os() {
        if name.to_string_lossy().starts_with("TLX_") && name != "TLX_CACHE" {
            command.env_remove(name);
        }
    }
}

/// `tlx` in TLC-compatibility mode with the interpreter unless the test asks
/// for `-compile`: a `check` command gets `-tlc -interp` right after `check`
/// (a later `-compile` wins), so that the tests without a tier flag test
/// the interpreter, tlx's semantic reference, as before the compiled tier
/// became the default, and all of them test TLC's results.
/// `tlx_default!()` runs the default mode and tier (no flag added).
#[macro_export]
macro_rules! tlx {
    () => {
        $crate::cli::Tlx::new(env!("CARGO_BIN_EXE_tlx"))
    };
}

/// `tlx` with the default tier (no tier flag added).
#[macro_export]
macro_rules! tlx_default {
    () => {
        $crate::cli::Tlx::with_default_tier(env!("CARGO_BIN_EXE_tlx"))
    };
}

pub struct Tlx {
    command: Command,
    timeout: Option<Duration>,
    /// Add `-tlc -interp` after a first argument `check` (see `tlx!`).
    parity: bool,
    /// No argument was added yet.
    first: bool,
}

impl Tlx {
    pub fn new(binary: impl AsRef<OsStr>) -> Self {
        let mut command = Command::new(binary);
        scrub(&mut command);
        Self { command, timeout: None, parity: true, first: true }
    }

    pub fn with_default_tier(binary: impl AsRef<OsStr>) -> Self {
        Self { parity: false, ..Self::new(binary) }
    }

    pub fn check(&mut self, spec: impl AsRef<OsStr>) -> &mut Self {
        self.arg("check").arg(spec)
    }
    pub fn cfg(&mut self, cfg: impl AsRef<OsStr>) -> &mut Self {
        self.arg("-config").arg(cfg)
    }
    pub fn arg(&mut self, arg: impl AsRef<OsStr>) -> &mut Self {
        let check = std::mem::take(&mut self.first) && arg.as_ref() == "check";
        self.command.arg(arg);
        if check && self.parity {
            self.command.args(["-tlc", "-interp"]);
        }
        self
    }
    pub fn args(&mut self, args: impl IntoIterator<Item = impl AsRef<OsStr>>) -> &mut Self {
        for arg in args {
            self.arg(arg);
        }
        self
    }
    pub fn env(&mut self, name: impl AsRef<OsStr>, value: impl AsRef<OsStr>) -> &mut Self {
        self.command.env(name, value);
        self
    }
    pub fn env_remove(&mut self, name: impl AsRef<OsStr>) -> &mut Self {
        self.command.env_remove(name);
        self
    }
    pub fn envs(&mut self, env: impl IntoIterator<Item = (impl AsRef<OsStr>, impl AsRef<OsStr>)>) -> &mut Self {
        self.command.envs(env);
        self
    }
    pub fn dir(&mut self, dir: impl AsRef<Path>) -> &mut Self {
        self.command.current_dir(dir);
        self
    }
    pub fn includes(&mut self, paths: impl IntoIterator<Item = impl AsRef<OsStr>>) -> &mut Self {
        for path in paths {
            self.arg("-I").arg(path);
        }
        self
    }
    pub fn timeout(&mut self, timeout: Duration) -> &mut Self {
        self.timeout = Some(timeout);
        self
    }
    pub fn command(&mut self) -> &mut Command {
        &mut self.command
    }

    pub fn run(&mut self) -> Run {
        let Some(timeout) = self.timeout else {
            return self.command.output().expect("run tlx").into();
        };
        #[cfg(unix)]
        return deadline::run(&mut self.command, timeout).into();
        #[cfg(not(unix))]
        panic!("subprocess deadlines require Unix process groups ({timeout:?})");
    }
}

#[cfg(unix)]
mod deadline {
    use super::*;
    use std::io::{self, Read};
    use std::os::fd::AsRawFd;
    use std::os::unix::process::CommandExt;
    use std::process::{Child, Stdio};
    use std::time::Instant;

    const TICK: Duration = Duration::from_millis(1);
    const CLEANUP: Duration = Duration::from_millis(100);

    struct OwnedGroup {
        child: Child,
        disarmed: bool,
    }

    impl OwnedGroup {
        fn stop(&mut self) -> io::Result<()> {
            self.disarmed = true;
            // Keep the leader unreaped while streams are open: even if it exited,
            // its PID cannot be reused as an unrelated process group's ID.
            let pgid = i32::try_from(self.child.id()).expect("child PID fits pid_t");
            assert!(pgid > 1, "refuse non-owned process group");
            // SAFETY: spawn used process_group(0), so -pgid addresses only our
            // owned group. No pointers or caller-supplied process IDs are used.
            let signal_error = if unsafe { libc::kill(-pgid, libc::SIGKILL) } == -1 {
                let error = io::Error::last_os_error();
                // ESRCH also covers an exited leader with no remaining members.
                (error.raw_os_error() != Some(libc::ESRCH)).then_some(error)
            } else {
                None
            };
            // The leader can deliberately leave its original group. Kill only
            // its still-owned PID as well, never its new (possibly external) group.
            let child_error = self.child.kill().err().filter(|error| error.raw_os_error() != Some(libc::ESRCH));
            let start = Instant::now();
            loop {
                if self.child.try_wait()?.is_some() {
                    return signal_error.or(child_error).map_or(Ok(()), Err);
                }
                if start.elapsed() >= CLEANUP {
                    // A kernel task can resist SIGKILL; report failed reaping
                    // explicitly rather than waiting beyond the cleanup budget.
                    return Err(io::Error::new(
                        io::ErrorKind::TimedOut,
                        format!("owned child {pgid} was not reaped within {CLEANUP:?}: group={signal_error:?}, child={child_error:?}"),
                    ));
                }
                std::thread::sleep(TICK);
            }
        }
    }

    impl Drop for OwnedGroup {
        fn drop(&mut self) {
            if !self.disarmed {
                if let Err(error) = self.stop() {
                    eprintln!("subprocess cleanup failed: {error}");
                }
            }
        }
    }

    struct Capture<P> {
        pipe: P,
        bytes: Vec<u8>,
        eof: bool,
    }

    impl<P: Read + AsRawFd> Capture<P> {
        fn new(pipe: P) -> io::Result<Self> {
            // SAFETY: pipe owns a live descriptor; F_GETFL takes no third argument.
            let flags = unsafe { libc::fcntl(pipe.as_raw_fd(), libc::F_GETFL) };
            if flags == -1 {
                return Err(io::Error::last_os_error());
            }
            // SAFETY: the descriptor is live and F_SETFL receives integer flags.
            if unsafe { libc::fcntl(pipe.as_raw_fd(), libc::F_SETFL, flags | libc::O_NONBLOCK) } == -1 {
                return Err(io::Error::last_os_error());
            }
            Ok(Self { pipe, bytes: Vec::new(), eof: false })
        }

        fn read_once(&mut self) -> io::Result<bool> {
            if !self.eof {
                // One bounded read per stream per tick prevents a noisy child
                // from starving the other stream or the deadline check.
                let mut bytes = [0; 8192];
                match self.pipe.read(&mut bytes) {
                    Ok(0) => {
                        self.eof = true;
                        return Ok(true);
                    }
                    Ok(n) => {
                        self.bytes.extend_from_slice(&bytes[..n]);
                        return Ok(true);
                    }
                    Err(error) if matches!(error.kind(), io::ErrorKind::WouldBlock | io::ErrorKind::Interrupted) => {}
                    Err(error) => return Err(error),
                }
            }
            Ok(false)
        }
    }

    pub(super) fn run(command: &mut Command, timeout: Duration) -> Output {
        // Spawn itself is an OS operation with no interruptible std API. All
        // subsequent polling, stream reads and cleanup have explicit bounds.
        // Timeout cancels members of this new group; descendants that explicitly
        // leave it are not signalled, and cannot hold up our nonblocking readers.
        let start = Instant::now();
        let (owned, stdout, stderr) = spawn(command);
        capture(owned, stdout, stderr, start, timeout)
    }

    fn spawn(command: &mut Command) -> (OwnedGroup, Capture<std::process::ChildStdout>, Capture<std::process::ChildStderr>) {
        let child = command.process_group(0).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().expect("run tlx");
        let mut owned = OwnedGroup { child, disarmed: false };
        let stdout = Capture::new(owned.child.stdout.take().unwrap()).expect("nonblocking stdout");
        let stderr = Capture::new(owned.child.stderr.take().unwrap()).expect("nonblocking stderr");
        (owned, stdout, stderr)
    }

    // These cleanup fixtures must actually create their descendants before
    // testing a 20 ms cancellation deadline. Process startup has no such
    // latency guarantee, especially on the shared development machine.
    #[cfg(test)]
    pub(super) fn when_ready(command: &mut Command, marker: &[u8]) -> impl FnOnce(Duration) -> Output {
        let (owned, mut stdout, mut stderr) = spawn(command);
        let start = Instant::now();
        loop {
            stdout.read_once().expect("read fixture readiness");
            stderr.read_once().expect("read fixture stderr");
            if stdout.bytes.split_inclusive(|b| *b == b'\n').any(|line| line.starts_with(marker) && line.ends_with(b"\n")) {
                break;
            }
            assert!(start.elapsed() < Duration::from_secs(5), "fixture never became ready");
            std::thread::sleep(TICK);
        }
        move |timeout| capture(owned, stdout, stderr, Instant::now(), timeout)
    }

    fn capture(
        mut owned: OwnedGroup,
        mut stdout: Capture<std::process::ChildStdout>,
        mut stderr: Capture<std::process::ChildStderr>,
        start: Instant,
        timeout: Duration,
    ) -> Output {
        while start.elapsed() < timeout {
            let stdout_progress = stdout.read_once().expect("read tlx stdout");
            let stderr_progress = stderr.read_once().expect("read tlx stderr");
            // Reap only once both readers finish, preserving group identity
            // until there is no longer a pipe descendant to cancel.
            if stdout.eof && stderr.eof {
                if let Some(status) = owned.child.try_wait().expect("poll tlx") {
                    owned.disarmed = true;
                    return Output { status, stdout: stdout.bytes, stderr: stderr.bytes };
                }
            }
            if !(stdout_progress || stderr_progress) {
                std::thread::sleep(TICK.min(timeout.saturating_sub(start.elapsed())));
            }
        }
        let cleanup = owned.stop();
        let drain = Instant::now();
        while !(stdout.eof && stderr.eof) && drain.elapsed() < CLEANUP {
            let stdout_progress = stdout.read_once().expect("drain tlx stdout");
            let stderr_progress = stderr.read_once().expect("drain tlx stderr");
            if !(stdout_progress || stderr_progress) {
                std::thread::sleep(TICK);
            }
        }
        panic!(
            "tlx timed out after {timeout:?}; cleanup: {cleanup:?}\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&stdout.bytes),
            String::from_utf8_lossy(&stderr.bytes)
        );
    }
}

pub struct Run {
    pub code: i32,
    pub stdout: String,
    pub stderr: String,
}

impl From<Output> for Run {
    fn from(output: Output) -> Self {
        Self {
            code: output.status.code().unwrap_or(-1),
            stdout: String::from_utf8_lossy(&output.stdout).into_owned(),
            stderr: String::from_utf8_lossy(&output.stderr).into_owned(),
        }
    }
}

impl Run {
    pub fn text(&self) -> String {
        self.stdout.clone() + &self.stderr
    }
}

pub fn counts(out: &str) -> Vec<&str> {
    out.lines()
        .filter(|line| {
            let stats = line.ends_with("states left on queue.") || line.contains("states left on queue (") && line.ends_with("-reduced).");
            !line.starts_with("Progress(") && (stats || line.starts_with("The depth"))
        })
        .collect()
}

pub fn result_lines(out: &str) -> Vec<&str> {
    out.lines()
        .filter(|line| {
            !line.starts_with("Progress(")
                && (line.starts_with("Error:")
                    || line.starts_with("Evaluating ")
                    || line.starts_with("State ")
                    || line.starts_with("/\\ ")
                    || line.ends_with("states left on queue.")
                    || line.starts_with("The depth")
                    || line.starts_with("The average outdegree"))
        })
        .collect()
}

pub type Tier = (&'static str, &'static [&'static str], &'static [(&'static str, &'static str)]);
pub const TIERS: [Tier; 3] = [
    ("interpreter", &["-interp"], &[]),
    ("compiled IR", &["-compile"], &[("TLX_NO_NATIVE", "1")]),
    ("native", &["-compile"], &[("TLX_NATIVE_SYNC", "1")]),
];

pub fn tests_specs() -> PathBuf {
    crate::workspace_root().join("tests/specs")
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::time::Instant;

    #[test]
    fn result_filters_ignore_progress() {
        let out = "Progress(1) 2 states generated, 1 states left on queue.\n2 states generated, 0 states left on queue.\nThe depth is 2\nError: bad\nEvaluating Inv\nState 1:\n/\\ x = 1\nThe average outdegree is 1\nFinished in 0s\n";
        assert_eq!(counts(out), ["2 states generated, 0 states left on queue.", "The depth is 2"]);
        assert_eq!(result_lines(out).len(), 7);
    }

    #[test]
    fn builder_preserves_explicit_environment_and_arguments() {
        let mut runner = Tlx::new("tlx");
        runner.check("A.tla").cfg("A.cfg").args(["-workers", "1"]).includes(["lib"]).dir("specs").env("TLX_PARANOID", "1");
        // (`tlx!()` tests TLC-compatible results with the interpreter unless asked otherwise.)
        let args = ["check", "-tlc", "-interp", "A.tla", "-config", "A.cfg", "-workers", "1", "-I", "lib"];
        assert_eq!(runner.command.get_args().collect::<Vec<_>>(), args);
        let mut default = Tlx::with_default_tier("tlx");
        default.args(["check", "A.tla"]);
        assert_eq!(default.command.get_args().collect::<Vec<_>>(), ["check", "A.tla"]);
        assert_eq!(runner.command.get_current_dir(), Some(Path::new("specs")));
        assert!(runner.command.get_envs().any(|(name, value)| name == "TLX_PARANOID" && value == Some(OsStr::new("1"))));
        let clean = Tlx::new("tlx");
        for (name, _) in std::env::vars_os().filter(|(name, _)| name.to_string_lossy().starts_with("TLX_") && name != "TLX_CACHE") {
            assert!(clean.command.get_envs().any(|(key, value)| key == name && value.is_none()));
        }
    }

    #[cfg(unix)]
    #[test]
    fn captures_streams_exit_code_and_lossy_utf8() {
        for timeout in [None, Some(Duration::from_secs(5))] {
            let mut runner = Tlx::new("sh");
            runner.timeout = timeout;
            let run = runner.args(["-c", "printf 'out\\377'; printf err >&2; exit 7"]).run();
            assert_eq!(run.code, 7);
            assert_eq!(run.stdout, "out�");
            assert_eq!(run.stderr, "err");
            assert_eq!(run.text(), "out�err");
        }
    }

    #[cfg(unix)]
    #[test]
    #[should_panic(expected = "tlx timed out")]
    fn timeout_reaps_the_child() {
        Tlx::new("sh").args(["-c", "exec sleep 0.4"]).timeout(Duration::from_millis(20)).run();
    }

    #[cfg(unix)]
    #[test]
    fn timeout_diagnostics_keep_both_streams() {
        let mut command = Command::new("/bin/sh");
        command.args(["-c", "echo partial-err >&2; echo partial-out; exec sleep 30"]);
        let ready = deadline::when_ready(&mut command, b"partial-out");
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| ready(Duration::from_millis(20)))).expect_err("must time out");
        let text = panic.downcast_ref::<String>().cloned().unwrap_or_default();
        assert!(text.contains("partial-out") && text.contains("partial-err"), "{text}");
    }

    #[cfg(unix)]
    #[test]
    fn deadline_includes_descendant_streams_after_parent_exit() {
        for parent in ["exit 0", "wait"] {
            // This sibling deliberately shares the test runner's group, not the
            // new child's group. Cancellation must leave it alone.
            let mut command = Command::new("/bin/sh");
            command.args(["-c", &format!("sleep 30 & child=$!; echo partial-err >&2; echo parent=$$ child=$child; {parent}")]);
            let ready = deadline::when_ready(&mut command, b"parent=");
            let mut sibling = Command::new("sleep").arg("30").spawn().unwrap();
            let start = Instant::now();
            let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| ready(Duration::from_millis(20))));
            let elapsed = start.elapsed();
            let sibling_status = sibling.try_wait().unwrap();
            sibling.kill().unwrap();
            sibling.wait().unwrap();
            assert!(sibling_status.is_none(), "timeout killed an unrelated process: {sibling_status:?}");
            assert!(elapsed < Duration::from_millis(250), "descendant bypassed deadline: {elapsed:?}");
            let panic = panic.expect_err("open descendant streams must time out even after the parent exits");
            let text = panic.downcast_ref::<String>().expect("timeout diagnostic");
            assert!(text.contains("partial-err"), "{text}");
            for line in text.lines().filter(|line| line.starts_with("parent=")) {
                for (index, pid) in line.split_whitespace().enumerate() {
                    let pid = pid.split_once('=').unwrap().1;
                    let status = Command::new("ps").args(["-o", "stat=", "-p", pid]).output().unwrap();
                    let status = String::from_utf8_lossy(&status.stdout);
                    // Only the direct child can be waited by this process. A killed
                    // orphan may briefly remain a zombie pending its adopter's wait.
                    assert!(status.trim().is_empty() || index == 1 && status.trim().starts_with('Z'), "process {pid}: {status}");
                }
            }
            assert!(text.contains("parent="), "missing owned process IDs: {text}");
            assert!(text.contains("cleanup: Ok(())"), "cleanup failed: {text}");
            eprintln!("descendant fixture ({parent}): deadline=20ms elapsed={elapsed:?}");
        }
    }

    #[cfg(unix)]
    #[test]
    fn deadline_captures_more_than_pipe_capacity() {
        let run = Tlx::new("/bin/sh")
            .args(["-c", "head -c 131072 /dev/zero; head -c 131072 /dev/zero >&2"])
            .timeout(Duration::from_secs(5))
            .run();
        assert_eq!(run.code, 0);
        for stream in [run.stdout, run.stderr] {
            assert_eq!(stream.len(), 131072);
            assert!(stream.bytes().all(|byte| byte == 0));
        }
    }

    #[cfg(unix)]
    #[test]
    fn deadline_reaps_a_leader_that_changes_group() {
        use std::os::unix::process::CommandExt;
        let mut command = Command::new("/bin/sh");
        command.args(["-c", "sleep 30 & echo escaped-parent=$$ escaped-child=$!; wait"]);
        // SAFETY: this pre-exec hook only calls async-signal-safe process
        // syscalls, deliberately moving our child into the inherited group.
        unsafe {
            command.pre_exec(|| {
                if libc::setpgid(0, libc::getpgid(libc::getppid())) == -1 {
                    Err(std::io::Error::last_os_error())
                } else {
                    Ok(())
                }
            });
        }
        let ready = deadline::when_ready(&mut command, b"escaped-parent=");
        let start = Instant::now();
        let panic = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| ready(Duration::from_millis(20)))).expect_err("must time out");
        let elapsed = start.elapsed();
        let text = panic.downcast_ref::<String>().expect("timeout diagnostic");
        assert!(text.contains("escaped-parent=") && text.contains("cleanup: Ok(())"), "{text}");
        let ids = text.lines().find(|line| line.starts_with("escaped-parent=")).unwrap();
        let child: i32 = ids.split_whitespace().nth(1).unwrap().split_once('=').unwrap().1.parse().unwrap();
        assert!(child > 1);
        // SAFETY: this PID was emitted by our private fixture immediately after
        // it spawned the fixture descendant. We signal that owned PID only,
        // never the external group it joined. Clean up before any assertions.
        let (alive, cleanup) = unsafe { (libc::kill(child, 0), libc::kill(child, libc::SIGKILL)) };
        assert_eq!(alive, 0, "must not kill a descendant outside the original owned group");
        assert_eq!(cleanup, 0, "clean up the fixture's escaped descendant");
        assert!(elapsed < Duration::from_millis(250), "escaped pipe blocked cancellation: {elapsed:?}");
        eprintln!("escaped-group fixture: deadline=20ms elapsed={elapsed:?}");
    }
}
