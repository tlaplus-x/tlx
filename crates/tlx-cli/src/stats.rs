//! `-stats [json[=FILE]]`: performance statistics of the run (see
//! `tlx_runtime::stats`), reported when tlx exits: as text on stderr, or as
//! JSON reports on stderr or in FILE. Without `-stats` nothing is
//! collected and the output is unchanged.

use std::io::Write;
use std::path::PathBuf;
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

use tlx_runtime::stats::{self, Metric};

/// Where the report goes.
#[derive(Clone, Debug)]
pub enum Out {
    Text,
    Json(Option<PathBuf>),
}

static REPORT: Mutex<bool> = Mutex::new(false);

static OUT: OnceLock<Out> = OnceLock::new();

/// The report format given after `-stats` (`next`, the following
/// argument), and whether that argument was consumed.
pub fn parse(next: Option<&String>) -> (Out, bool) {
    match next.map(|s| s.as_str()) {
        Some("json") => (Out::Json(None), true),
        Some(s) if s.starts_with("json=") => (Out::Json(Some(PathBuf::from(&s[5..]))), true),
        Some("text") => (Out::Text, true),
        _ => (Out::Text, false),
    }
}

/// Collect statistics from now on, reported by `finish`. One state
/// expansion (or simulation step) in `TLX_STATS_SAMPLE` (default 8) is
/// timed in detail.
pub fn enable(out: Out) {
    let _ = OUT.set(out);
    // (A bad value is reported at startup, `settings::Env::from_env`.)
    let sample =
        tlx_base::knobs::Env::process().num("TLX_STATS_SAMPLE").unwrap_or_else(|_| tlx_base::knobs::default_num("TLX_STATS_SAMPLE"));
    let sample = u32::try_from(sample).unwrap_or(u32::MAX);
    stats::enable(sample);
}

/// Run `f`, recording its time as phase `key`.
pub fn timed<R>(key: &str, f: impl FnOnce() -> R) -> R {
    if !stats::on() {
        return f();
    }
    let t0 = Instant::now();
    let r = f();
    stats::add_secs(key, t0.elapsed());
    r
}

/// Record the time `d` of phase `key`.
pub fn phase(key: &str, d: Duration) {
    stats::add_secs(key, d);
}

/// The peak resident set size of the process, in bytes.
fn peak_rss() -> Option<u64> {
    // SAFETY: getrusage only writes the struct it is given.
    let ru = unsafe {
        let mut ru: libc::rusage = std::mem::zeroed();
        if libc::getrusage(libc::RUSAGE_SELF, &mut ru) != 0 {
            return None;
        }
        ru
    };
    let max = ru.ru_maxrss as u64;
    // (Bytes on macOS, KiB elsewhere.)
    Some(if cfg!(target_os = "macos") { max } else { max * 1024 })
}

/// Record the peak RSS so far as memory metric `key` (if on).
pub fn record_peak_rss(key: &str) {
    if stats::on() {
        if let Some(rss) = peak_rss() {
            stats::set(&format!("{}{key}", stats::MEMORY), Metric::Bytes(rss));
        }
    }
}

/// Report the statistics (if enabled), at the end of the run.
pub fn finish(started: Instant) {
    crate::process::block_report_sigpipe();
    report(started.elapsed(), false);
}

/// Called on the shutdown output thread, not from an asynchronous signal handler.
/// Live worker snapshots may lag; end-of-search-only metrics may be absent.
pub fn interrupted() {
    report(stats::since_start(), true);
}

fn report(elapsed: Duration, interrupted: bool) {
    let Some(out) = OUT.get() else { return };
    // Serialize normal completion and interruption so JSON file writes cannot
    // interleave. The signal report is last if normal reporting was underway.
    let mut was_interrupted = REPORT.lock().unwrap_or_else(|e| e.into_inner());
    if *was_interrupted && !interrupted {
        return;
    }
    *was_interrupted |= interrupted;
    stats::set("total", Metric::Secs(elapsed.as_secs_f64()));
    stats::set_json("interrupted", interrupted.to_string());
    if interrupted {
        stats::set_section("interrupted", "  Partial statistics; active workers and phases may be incomplete.\n".into());
    }
    record_peak_rss("peak RSS");
    match out {
        // Reporting is best effort: an output error must not prevent the
        // signal thread from cleaning up spill files and exiting.
        Out::Text => {
            let _ = write!(std::io::stderr().lock(), "{}", stats::text());
        }
        Out::Json(None) => {
            let _ = writeln!(std::io::stderr().lock(), "{}", stats::json());
        }
        Out::Json(Some(p)) => {
            if let Err(e) = std::fs::write(p, stats::json() + "\n") {
                let _ = writeln!(std::io::stderr().lock(), "cannot write {}: {e}", p.display());
            }
        }
    }
}
