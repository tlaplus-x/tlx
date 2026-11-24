//! The `TLX_*` environment variables: one declaration table, one parser,
//! the `-h` text (docs/configuration.md).
//!
//! Every variable tlx (or its tests and scripts) reads is a row of `KNOBS`:
//! name, type and default, documentation, audience, and the crate that
//! reads it. The typed accessors of `Env` are the only place where the
//! syntax of a value (booleans, numbers, choices) is decided, and the only
//! place that formats the "invalid value" error. Reading a variable that is
//! not declared, or with an accessor of the wrong kind, is a programming
//! error and panics. `help_text` renders the environment section of
//! `tlx check -h`, and a test of `tlx-cli` checks docs/configuration.md
//! lists exactly the declared variables.

use std::ffi::OsString;
use std::path::PathBuf;
use std::time::Duration;

/// Who the variable is for.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Audience {
    /// Documented for users of `tlx check`.
    User,
    /// Tuning and debugging switches; not stable.
    Developer,
    /// Used by tests and test tooling.
    Test,
    /// Set by tlx for its own child processes; not configuration.
    Internal,
}

/// The type of a variable, with its default.
#[derive(Clone, Copy, Debug)]
pub enum Kind {
    /// Off when unset; otherwise on unless `""`, `0`, `false`, `no`, `off`.
    Flag,
    /// As `Flag`, but on when unset.
    FlagOn,
    /// A number of at least `min`; `default` when unset.
    Num { default: u64, min: u64 },
    /// A number of at least `min`; absent when unset.
    OptNum { min: u64 },
    /// A number of milliseconds, fractions allowed.
    Millis { default_ms: f64 },
    /// Free text (a consumer may parse it further); `default` ("" for
    /// none) is what the consumer uses when unset.
    Text { default: &'static str },
    /// One of `values` (ASCII case-insensitive when `fold`); the consumer
    /// maps it, and decides what unset means.
    Choice { values: &'static [&'static str], fold: bool },
    /// A path list, separated like `PATH`.
    Paths,
    /// One path.
    Path,
}

/// One declared variable.
#[derive(Clone, Copy, Debug)]
pub struct Knob {
    pub name: &'static str,
    pub kind: Kind,
    pub audience: Audience,
    /// The crate (or `scripts`, `tests`) that reads it.
    pub reader: &'static str,
    /// `-h`: the value's placeholder (`TLX_PRERUN=N`).
    pub meta: &'static str,
    /// What the value must be, for the "invalid value" message.
    pub what: &'static str,
    /// `-h`: what it does, in one paragraph (the default is appended).
    pub doc: &'static str,
    /// An empty or blank value counts as unset instead of being invalid.
    pub blank_unset: bool,
}

impl Knob {
    const fn new(name: &'static str, kind: Kind, audience: Audience, reader: &'static str, doc: &'static str) -> Knob {
        Knob { name, kind, audience, reader, meta: "", what: "", doc, blank_unset: false }
    }
    const fn meta(mut self, meta: &'static str) -> Knob {
        self.meta = meta;
        self
    }
    const fn what(mut self, what: &'static str) -> Knob {
        self.what = what;
        self
    }
    const fn blank_unset(mut self) -> Knob {
        self.blank_unset = true;
        self
    }

    /// Whether a product crate reads it (so that `-h` lists it and a bad
    /// value is reported at startup), as opposed to scripts and tests.
    pub fn product(&self) -> bool {
        self.reader.starts_with("tlx-") && self.audience != Audience::Internal && self.reader != "tlx-testkit"
    }

    /// The default as text a user could set it to ("" if none).
    #[cfg(test)]
    fn default_text(&self) -> String {
        match self.kind {
            Kind::FlagOn => "1".into(),
            Kind::Num { default, .. } => default.to_string(),
            Kind::Millis { default_ms } => default_ms.to_string(),
            Kind::Text { default } => default.to_string(),
            _ => String::new(),
        }
    }
}

use Audience::{Developer as D, Internal as I, Test as T, User as U};

const fn flag(name: &'static str, a: Audience, reader: &'static str, doc: &'static str) -> Knob {
    Knob::new(name, Kind::Flag, a, reader, doc)
}
const fn flag_on(name: &'static str, a: Audience, reader: &'static str, doc: &'static str) -> Knob {
    Knob::new(name, Kind::FlagOn, a, reader, doc)
}
const fn num(name: &'static str, a: Audience, reader: &'static str, default: u64, what: &'static str, doc: &'static str) -> Knob {
    Knob::new(name, Kind::Num { default, min: 0 }, a, reader, doc).what(what).meta("N")
}
const fn opt_num(name: &'static str, a: Audience, reader: &'static str, what: &'static str, doc: &'static str) -> Knob {
    Knob::new(name, Kind::OptNum { min: 0 }, a, reader, doc).what(what).meta("N").blank_unset()
}
const fn text(name: &'static str, a: Audience, reader: &'static str, default: &'static str, doc: &'static str) -> Knob {
    Knob::new(name, Kind::Text { default }, a, reader, doc)
}

const COMPILE: &str = "tlx-compile";
const CLI: &str = "tlx-cli";

/// Every `TLX_*` variable (and `CC`), in the order `-h` lists them. Rows
/// whose reader is not a product crate are for tests and scripts: they are
/// declared so that the table and docs/configuration.md stay complete.
pub static KNOBS: &[Knob] = &[
    // ---- user
    Knob::new("TLX_PATH", Kind::Paths, U, CLI, "more module directories (separated like PATH), searched after the -I directories"),
    Knob::new("TLX_CLASSPATH", Kind::Paths, U, CLI, "more module directories (separated like PATH), searched after the built-in modules (TLC's classpath)"),
    text("CC", U, "tlx-native", "cc", "C compiler of the compiled tier").meta("PROGRAM"),
    Knob::new("TLX_CACHE", Kind::Path, U, "tlx-native", "cache of compiled native code (default: ~/.cache/tlx)").meta("DIR"),
    num(
        "TLX_CACHE_MB",
        U,
        "tlx-native",
        1024,
        "MiB",
        "the most the native-code cache may hold: after a new library is built, the least recently used ones beyond it are removed (0: no limit)",
    ),
    text("TLX_MAXMEM", U, CLI, "", "as -maxmem (the command line wins)")
        .meta("X")
        .what("a fraction in (0,1) of the physical memory, or MiB")
        .blank_unset(),
    text("TLX_SPILL", U, CLI, "", "as -spill (the command line wins)").meta("MODE").what("auto, off or always").blank_unset(),
    Knob::new("TLX_METADIR", Kind::Path, U, CLI, "as -metadir (the command line wins)").meta("DIR").blank_unset(),
    Knob::new("TLX_PROOF_DIR", Kind::Path, U, CLI, "as -proofdir (the command line wins)").meta("DIR").blank_unset(),
    text("TLX_MAXDISK", U, CLI, "", "as -maxdisk (the command line wins)").meta("X").what("MiB, or a size with K/M/G/T").blank_unset(),
    Knob::new("TLX_THP", Kind::Choice { values: &["auto", "on", "off"], fold: true }, D, CLI, "Linux: transparent huge pages for the process (default auto: on, off under a -maxmem below 512 MiB + 64 MiB per worker; MIMALLOC_ALLOW_THP, when set, decides instead)")
        .meta("auto|on|off")
        .what("auto, on or off")
        .blank_unset(),
    // ---- developer: the compiled tier
    flag("TLX_PARANOID", D, COMPILE, "-compile: cross-check every compiled result against the interpreter, fail at the first difference (implies TLX_NATIVE_SYNC)"),
    flag("TLX_NO_NATIVE", D, COMPILE, "-compile: run lowered IR only, no generated C"),
    flag("TLX_NATIVE_SYNC", D, COMPILE, "-compile: build the native code before exploring"),
    Knob::new("TLX_JIT", Kind::Choice { values: &["tier", "1", "only", "0", "off"], fold: false }, D, COMPILE, "-compile: native code tiers: tier (default: the Cranelift JIT, replaced by the C -O2 library built in the background), 1 (JIT only), 0 (C only)")
        .meta("MODE")
        .what("tier, 1, only or 0")
        .blank_unset(),
    num("TLX_CC_DELAY_MS", D, COMPILE, 1500, "a number of milliseconds", "with TLX_JIT=tier: search time before the C build starts"),
    Knob::new("TLX_CC_AT_EXIT_MS", Kind::Millis { default_ms: 200.0 }, D, COMPILE, "with TLX_JIT=tier: a run that ends before the delayed C build starts still starts it (without waiting) when the JIT compilation took at least N ms (0: never)")
        .meta("N")
        .what("a number of milliseconds"),
    flag("TLX_NO_MATERIALIZE", D, COMPILE, "-compile: do not materialize state-level definitions"),
    Knob::new("TLX_VALUE_STORE", Kind::Choice { values: &["0", "off", "1", "on", "all"], fold: true }, D, COMPILE, "-compile, experimental: keep the values of slots that would be Dyn in a run-owned value store (Ref slots), with native DOMAIN, lookup, EXCEPT, :> and @@ on them; all (testing): every slot")
        .meta("MODE")
        .what("0, 1 or all")
        .blank_unset(),
    flag("TLX_ESCAPE", D, COMPILE, "-compile, experimental: stable inline slots with overflow handles and bounded action-local recompilation"),
    flag_on("TLX_MIXED", D, COMPILE, "-compile: mixed-mode native code (host regions for what C cannot compile)"),
    num("TLX_MIXED_FORCE", D, COMPILE, 0, "a number of expressions", "-compile, testing: also make every K-th expression C can compile a host region (implies TLX_MIXED; 0: none)").meta("K"),
    flag_on("TLX_MIXED_ADAPT", D, COMPILE, "with TLX_MIXED: per function, run mixed code or its fallback, whichever is faster"),
    num("TLX_PRERUN", D, COMPILE, 20_000, "a number of states", "-compile: states of the shape pre-run"),
    num("TLX_PRERUN_MS", D, COMPILE, 1000, "a number of milliseconds", "-compile: time budget of the pre-run"),
    num("TLX_PRERUN_SETTLE", D, COMPILE, 2000, "a number of states", "-compile: end the pre-run once N states (and twice as many as before), or N/4 states for at least 50 ms of CPU time (and twice the CPU time before), fit the layout chosen so far (0: never)"),
    flag_on("TLX_PRERUN_REUSE", D, COMPILE, "-compile: a pre-run that is the search (it may create strings) and explores the whole state space gives the run's result (off with TLX_PARANOID)"),
    opt_num("TLX_RETAIN_MB", D, COMPILE, "a number of MiB", "-compile: archive memory limit (default -maxmem / 4, 1024 MiB without a budget); spill beyond it (0: always start over)"),
    opt_num("TLX_MAX_RESTARTS", D, COMPILE, "a number of restarts", "-compile: layout-miss restarts before the rest of the run uses dynamic values (default 16)").no_blank_unset(),
    flag("TLX_COVERAGE", D, COMPILE, "-compile: log typed-IR coverage and widenings"),
    flag("TLX_CGEN_DEBUG", D, COMPILE, "-compile: log why functions are not native"),
    flag("TLX_EQ_DEBUG", D, COMPILE, "-compile: log the types/shapes of boxed equalities"),
    text("TLX_IR_DUMP", D, COMPILE, "", "-compile: print the IR of action/predicate NAME (*: all)").meta("NAME"),
    flag("TLX_IR_DUMP_RAW", D, COMPILE, "with TLX_IR_DUMP: print the Debug form"),
    num("TLX_MEMO_SLOTS", D, COMPILE, 1 << 16, "a number of slots", "-compile: memo table slots per thread (rounded up to a power of two)"),
    num("TLX_MEMO_MB", D, COMPILE, 128, "a number of MiB", "-compile: memory of the memo tables of all threads"),
    flag("TLX_MEMO_STATS", D, COMPILE, "-compile, with -stats: add the memo hit rates per expression to the report (timing has a cost)"),
    text("TLX_JIT_OPT", D, COMPILE, "speed", "JIT: Cranelift optimization level (none, speed)").meta("LEVEL"),
    flag("TLX_IR_VERIFY_HARD", D, COMPILE, "typed IR verification failures are hard errors instead of interpreter fallback (verification is always enabled)"),
    flag("TLX_JIT_VERIFY", D, COMPILE, "JIT: turn the Cranelift IR verifier on (slower compiles)"),
    flag("TLX_JIT_DISASM", D, COMPILE, "JIT: print the machine code of every JIT function to stderr"),
    flag("TLX_CC_SANITIZE", D, "tlx-native", "-compile: build the C code with sanitizers (debug build)"),
    text("TLX_INJECT_MISMATCH", T, COMPILE, "", "testing: corrupt one compiled result (drop, dup, stale, init, inv, miss) to test TLX_PARANOID")
        .meta("KIND[:N]")
        .what("drop|dup|stale|init|inv|miss, optionally followed by :N"),
    Knob::new("TLX_BAILOUT_DEBUG", Kind::Num { default: 0, min: 0 }, D, COMPILE, "-compile: report the first N errors of the IR executor")
        .what("a number of errors")
        .meta("N")
        .blank_unset(),
    // ---- developer: the interpreter, the front end
    Knob::new("TLX_MAX_DEPTH", Kind::Num { default: 100_000, min: 1 }, D, "tlx-eval", "nesting of operator and function applications at which the interpreter reports a stack overflow")
        .what("a positive integer")
        .meta("N")
        .blank_unset(),
    opt_num("TLX_SYMMETRY_PARANOID", D, "tlx-eval", "a number of states", "check a symmetry tlx applies without a declaration at one expanded state in N: every generator must map the state's successors, invariants and constraints to its image's; a mismatch exits with 101").meta("N"),
    text("TLX_AUTOSYM_FORCE", T, CLI, "", "testing: mark these sets of model values (constants, comma-separated) as candidate symmetric sets despite static-analysis rejection (still requires a connected Lean certificate to apply)").meta("NAMES"),
    Knob::new("TLX_STATS_SAMPLE", Kind::Num { default: 8, min: 1 }, D, CLI, "-stats: time one state expansion in N")
        .what("a positive integer")
        .meta("N")
        .blank_unset(),
    // ---- testing: the search and its storage
    opt_num("TLX_QUEUE_COMPRESS_MB", T, CLI, "a number of MiB", "testing: queue size above which auto compresses (default 64, at most a 16th of -maxmem)"),
    Knob::new("TLX_SEG_BYTES", Kind::OptNum { min: 64 }, T, CLI, "testing: segment size of compressed blocks (default 1048576)")
        .what("a number of bytes, at least 64")
        .meta("N")
        .blank_unset(),
    opt_num("TLX_FP_TABLE_MIN", T, CLI, "a number of slots", "testing: the first fingerprint table has N slots (at least 1024; default 1048576) and grows from there"),
    opt_num("TLX_FP_SPILL_SLOTS", T, CLI, "a number of slots", "testing: with -spill always, the fingerprint table has at most N slots (at least 1024; default 262144) and rotates to disk when full"),
    opt_num("TLX_CHECKPOINT_SECS", T, CLI, "a number of seconds", "testing: a checkpoint every N seconds (with -checkpoint)"),
    opt_num("TLX_CHECKPOINT_STATES", T, CLI, "a number of states", "testing: a checkpoint whenever N more distinct states were found (with -checkpoint)"),
    opt_num("TLX_CHECKPOINT_ABORT", T, CLI, "a number of checkpoints", "testing: end the process right after the N-th checkpoint (exit 134, no cleanup: as if killed)"),
    // ---- scripts and tests
    text("TLX_TLC_XMX", D, "scripts", "4g", "maximum JVM heap for TLC launches (Java -Xmx syntax)").meta("SIZE"),
    flag("TLX_CLOUD_HOST", D, "scripts", "set to 1 by cloud_verify on the remote host to permit heavy verification"),
    text("TLX_JAVA", D, "scripts", "/opt/homebrew/opt/openjdk@21/bin/java", "java that the scripts run TLC and SANY with").meta("PROGRAM"),
    text("TLX_BENCH_MACHINE", D, "scripts", "", "appended to the machine description that bench.py records").meta("TEXT"),
    text("TLX_MAIN", D, "scripts", "", "the main checkout, for scripts run from a worktree").meta("DIR"),
    text("TLX_BUILD_PROFILE", D, "scripts", "test-release", "cargo profile of the tlx binary the test scripts build and run (target/<profile>/tlx)").meta("PROFILE"),
    text("TLX_CLOUD_CONFIG", D, "scripts", "~/.config/tlx/cloud.json", "local file with the cloud identities the cloud scripts may use (they refuse to run without it)").meta("PATH"),
    text("TLX_SPEC_TIMEOUT", D, "scripts", "120", "per-spec time limit in seconds for scripts/spectest.py; a spec that exceeds it fails with status timeout").meta("SECONDS"),
    num("TLX_LIVE_SCALE", T, "tests", 200_000, "a number of states", "number of states of the tlx-live scale test"),
    flag("TLX_TRACE", T, "tests", "tlx-sema resolve test: print each model as it is processed"),
    opt_num("TLX_SEED", T, "tests", "a number", "seed of the property tests (they print it on failure)"),
    opt_num("TLX_PROP_STATES", T, "tests", "a number of states", "exec_vs_native_random: states per family and seed"),
    num("TLX_PROP_SEEDS", T, "tests", 20, "a number of seeds", "exec_vs_native_random: seeds of the ignored many-seeds test"),
    flag("TLX_DIFF_VERBOSE", T, "tests", "exec_vs_native tests: print each case's tallies"),
    flag("TLX_DIFF_STRICT", T, "tests", "exec_vs_native: also fail when the IR executor and native code differ in error cases"),
    text("TLX_DIFF_DUMP", T, "tests", "", "exec_vs_native: print the IR of the functions called NAME").meta("NAME"),
    Knob::new("TLX_THIRD_PARTY", Kind::Path, T, "tlx-testkit", "location of third_party/ for tests"),
    Knob::new("TLX_CORPUS_OUT", Kind::Path, T, "tlx-testkit", "location of corpus/out/ for tests"),
    flag("TLX_REQUIRE_THIRD_PARTY", T, "tlx-testkit", "tests that need third_party/ panic instead of skipping (also with CI set)"),
    flag("TLX_KEEP_TMP", T, "tlx-testkit", "keep the temporary directories of tests"),
    text("TLX_SER_RECOVER_MODE", T, "tests", "", "ser_recover test: the mode a child process runs in (set by the test itself)"),
    text("TLX_SER_RECOVER_FILE", T, "tests", "", "ser_recover test: the file a child process works on (set by the test itself)"),
    Knob::new("TLX_RUSTC_SLOTS", Kind::OptNum { min: 1 }, D, "scripts", "machine-wide compiler slots (default: max(4, logical cores - 6)); metadata queries bypass slots").what("a positive slot count").meta("N"),
    text("TLX_HOOKS", D, "scripts/hooks", "", "off bypasses versioned Git hooks with a warning"),

    // ---- set by tlx for the C compiler's shell wrapper
    text("TLX_TMP", I, "tlx-native", "", "the library the C compiler writes, before it is moved into the cache"),
    text("TLX_LIB", I, "tlx-native", "", "the library's final path in the cache"),
    text("TLX_SRC", I, "tlx-native", "", "the generated C source"),
    text("TLX_KEEP", I, "tlx-native", "", "where the C source is kept after a successful build"),
    text("TLX_LOG", I, "tlx-native", "", "the C compiler's error log"),
];

impl Knob {
    const fn no_blank_unset(mut self) -> Knob {
        self.blank_unset = false;
        self
    }
}

/// The declaration of `name`. Panics if it is not declared.
pub fn decl(name: &str) -> &'static Knob {
    KNOBS.iter().find(|k| k.name == name).unwrap_or_else(|| panic!("{name} is not declared in tlx_base::knobs::KNOBS"))
}

/// The declared default of a `Kind::Num` variable.
pub fn default_num(name: &str) -> u64 {
    match decl(name).kind {
        Kind::Num { default, .. } => default,
        k => panic!("{name} has no numeric default ({k:?})"),
    }
}

/// Whether `text` is false in the syntax of boolean variables.
fn is_off(text: &str) -> bool {
    matches!(text.trim(), "" | "0" | "false" | "no" | "off")
}

/// A lookup of variables by name.
pub type Lookup<'a> = dyn Fn(&str) -> Option<String> + 'a;

/// A source of variables: the process environment, or a lookup (tests).
#[derive(Clone, Copy)]
pub struct Env<'a> {
    lookup: Option<&'a Lookup<'a>>,
}

impl Env<'static> {
    /// The environment of the process.
    pub fn process() -> Env<'static> {
        Env { lookup: None }
    }
}

impl<'a> Env<'a> {
    /// Variables from `get` instead of the process environment.
    pub fn lookup(get: &'a Lookup<'a>) -> Env<'a> {
        Env { lookup: Some(get) }
    }

    fn os(&self, name: &str) -> Option<OsString> {
        match self.lookup {
            None => std::env::var_os(name),
            Some(get) => get(name).map(OsString::from),
        }
    }

    /// The value, if set and valid unicode.
    fn var(&self, name: &str) -> Option<String> {
        self.os(name).and_then(|v| v.into_string().ok())
    }

    fn kind(name: &str, ok: impl Fn(&Kind) -> bool) -> &'static Knob {
        let k = decl(name);
        assert!(ok(&k.kind), "{name}: read with an accessor of the wrong kind ({:?})", k.kind);
        k
    }

    fn invalid(k: &Knob, v: &str) -> String {
        format!("invalid value of {}: {v:?} (expected {})", k.name, k.what)
    }

    /// The text of a variable that is set (and unicode), as it is, for
    /// `Kind::Text`.
    pub fn string(&self, name: &str) -> Option<String> {
        Self::kind(name, |k| matches!(k, Kind::Text { .. }));
        self.var(name)
    }

    /// `string`, or the declared default.
    pub fn string_or_default(&self, name: &str) -> String {
        let Kind::Text { default } = Self::kind(name, |k| matches!(k, Kind::Text { .. })).kind else { unreachable!() };
        self.var(name).unwrap_or_else(|| default.to_string())
    }

    /// The trimmed value parsed by `parse`; `None` from `parse` is an
    /// invalid value. Unset is `None`, and so is a blank value for a
    /// `blank_unset` variable.
    pub fn parsed<T>(&self, name: &str, parse: impl FnOnce(&str) -> Option<T>) -> Result<Option<T>, String> {
        let k = Self::kind(name, |k| matches!(k, Kind::Text { .. }));
        let Some(v) = self.var(name) else { return Ok(None) };
        let v = v.trim();
        if v.is_empty() && k.blank_unset {
            return Ok(None);
        }
        parse(v).map(Some).ok_or_else(|| Self::invalid(k, v))
    }

    /// A boolean variable (`Flag`, or `FlagOn`: on when unset).
    pub fn flag(&self, name: &str) -> bool {
        let k = Self::kind(name, |k| matches!(k, Kind::Flag | Kind::FlagOn));
        match self.var(name) {
            None => matches!(k.kind, Kind::FlagOn),
            Some(v) => !is_off(&v),
        }
    }

    /// Whether the variable is set at all (even to an off value).
    pub fn is_set(&self, name: &str) -> bool {
        decl(name);
        self.os(name).is_some()
    }

    /// A `Kind::Num`: the default when unset.
    pub fn num(&self, name: &str) -> Result<u64, String> {
        let Kind::Num { default, .. } = Self::kind(name, |k| matches!(k, Kind::Num { .. })).kind else { unreachable!() };
        Ok(self.number(name)?.unwrap_or(default))
    }

    /// A `Kind::OptNum`: `None` when unset.
    pub fn opt_num(&self, name: &str) -> Result<Option<u64>, String> {
        Self::kind(name, |k| matches!(k, Kind::OptNum { .. }));
        self.number(name)
    }

    fn number(&self, name: &str) -> Result<Option<u64>, String> {
        let k = decl(name);
        let min = match k.kind {
            Kind::Num { min, .. } | Kind::OptNum { min } => min,
            _ => unreachable!(),
        };
        let Some(v) = self.var(name) else { return Ok(None) };
        if k.blank_unset && v.trim().is_empty() {
            return Ok(None);
        }
        // (Blank is invalid, and shown as it is, where it is not unset.)
        let shown = if k.blank_unset { v.trim() } else { &v };
        v.trim().parse::<u64>().ok().filter(|&n| n >= min).map(Some).ok_or_else(|| Self::invalid(k, shown))
    }

    /// A `Kind::Millis`.
    pub fn millis(&self, name: &str) -> Result<Duration, String> {
        let Kind::Millis { default_ms } = Self::kind(name, |k| matches!(k, Kind::Millis { .. })).kind else { unreachable!() };
        match self.var(name) {
            None => Ok(Duration::from_secs_f64(default_ms / 1000.0)),
            Some(v) => v
                .trim()
                .parse::<f64>()
                .ok()
                .filter(|ms| ms.is_finite() && *ms >= 0.0)
                // A finite value can still be too large for a `Duration`
                // (`1e308` ms); that is an invalid value, not a panic.
                .and_then(|ms| Duration::try_from_secs_f64(ms / 1000.0).ok())
                .ok_or_else(|| Self::invalid(decl(name), &v)),
        }
    }

    /// A `Kind::Choice`: the matching entry of the declared values, or
    /// `None` when unset (or blank, for `blank_unset`).
    pub fn choice(&self, name: &str) -> Result<Option<&'static str>, String> {
        let k = Self::kind(name, |k| matches!(k, Kind::Choice { .. }));
        let Kind::Choice { values, fold } = k.kind else { unreachable!() };
        let Some(v) = self.var(name) else { return Ok(None) };
        let v = v.trim();
        if v.is_empty() && k.blank_unset {
            return Ok(None);
        }
        values.iter().copied().find(|c| if fold { c.eq_ignore_ascii_case(v) } else { *c == v }).map(Some).ok_or_else(|| Self::invalid(k, v))
    }

    /// A `Kind::Paths` variable (separated like `PATH`); empty when unset.
    pub fn paths(&self, name: &str) -> Vec<PathBuf> {
        Self::kind(name, |k| matches!(k, Kind::Paths));
        self.os(name).map(|p| std::env::split_paths(&p).collect()).unwrap_or_default()
    }

    /// A `Kind::Path` variable: `None` when unset (or blank, for
    /// `blank_unset`).
    pub fn path(&self, name: &str) -> Option<PathBuf> {
        let k = Self::kind(name, |k| matches!(k, Kind::Path));
        if k.blank_unset {
            return self.var(name).map(|v| v.trim().to_string()).filter(|v| !v.is_empty()).map(PathBuf::from);
        }
        self.os(name).map(PathBuf::from)
    }

    /// Check every variable a product crate reads, so that a bad value is
    /// reported before the work starts. (Text variables the consumer
    /// parses itself are checked there.)
    pub fn validate(&self) -> Result<(), String> {
        for k in KNOBS.iter().filter(|k| k.product()) {
            match k.kind {
                Kind::Num { .. } => drop(self.num(k.name)?),
                Kind::OptNum { .. } => drop(self.opt_num(k.name)?),
                Kind::Millis { .. } => drop(self.millis(k.name)?),
                Kind::Choice { .. } => drop(self.choice(k.name)?),
                _ => {}
            }
        }
        Ok(())
    }
}

/// The text that wraps `words` at `width`, the first line after `first`
/// columns, the rest indented by `indent` columns.
fn wrap(out: &mut String, head: &str, indent: usize, width: usize, doc: &str) {
    let mut line = format!("{head:<indent$}");
    if head.len() + 1 > indent {
        out.push_str(head.trim_end());
        out.push('\n');
        line = " ".repeat(indent);
    }
    let mut blank = true;
    for word in doc.split_whitespace() {
        if !blank && line.len() + 1 + word.len() > width {
            out.push_str(line.trim_end());
            out.push('\n');
            line = " ".repeat(indent);
            blank = true;
        }
        if !blank {
            line.push(' ');
        }
        line.push_str(word);
        blank = false;
    }
    out.push_str(line.trim_end());
    out.push('\n');
}

/// The environment sections of `tlx check -h`, from the table.
pub fn help_text() -> String {
    let mut out = String::new();
    for (title, audiences) in [
        ("Environment (user):", &[Audience::User][..]),
        ("Environment (developer and debugging; see docs/configuration.md):", &[Audience::Developer, Audience::Test][..]),
    ] {
        if !out.is_empty() {
            out.push('\n');
        }
        out.push_str(title);
        out.push('\n');
        for k in KNOBS.iter().filter(|k| k.product() && audiences.contains(&k.audience)) {
            let head = if k.meta.is_empty() || matches!(k.kind, Kind::Flag | Kind::FlagOn) {
                format!("  {}", k.name)
            } else {
                format!("  {}={}", k.name, k.meta)
            };
            let default = match k.kind {
                Kind::FlagOn => " (default on; 0: off)".to_string(),
                Kind::Num { default, .. } if default != 0 => format!(" (default {default})"),
                Kind::Millis { default_ms } => format!(" (default {default_ms})"),
                Kind::Text { default } if !default.is_empty() => format!(" (default: {default})"),
                _ => String::new(),
            };
            wrap(&mut out, &head, 23, 78, &format!("{}{default}", k.doc));
        }
    }
    out.push_str("Boolean variables are on unless unset, empty, 0, false, no or off.\n");
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn with<R>(vars: &[(&str, &str)], f: impl FnOnce(Env) -> R) -> R {
        let get = |n: &str| vars.iter().find(|(k, _)| *k == n).map(|(_, v)| v.to_string());
        f(Env::lookup(&get))
    }

    #[test]
    fn table_is_well_formed() {
        let mut seen = std::collections::BTreeSet::new();
        for k in KNOBS {
            assert!(seen.insert(k.name), "{} declared twice", k.name);
            assert!(k.name.starts_with("TLX_") || k.name == "CC", "{}", k.name);
            assert!(!k.doc.is_empty(), "{} has no documentation", k.name);
            assert!(k.name.bytes().all(|b| b.is_ascii_uppercase() || b.is_ascii_digit() || b == b'_'), "{}", k.name);
            match k.kind {
                Kind::Num { .. } | Kind::OptNum { .. } | Kind::Millis { .. } | Kind::Choice { .. } => {
                    assert!(!k.what.is_empty(), "{} has no `what`", k.name)
                }
                _ => {}
            }
            assert!(!k.product() || k.reader.starts_with("tlx-"));
        }
    }

    #[test]
    fn every_knob_parses_its_default() {
        // Unset: every accessor succeeds.
        with(&[], |e| e.validate().unwrap());
        // Set to the default's own text: it parses too, and to the same value.
        for k in KNOBS {
            let text = k.default_text();
            let get = |n: &str| (n == k.name && !text.is_empty()).then(|| text.clone());
            let e = Env::lookup(&get);
            match k.kind {
                Kind::Flag => assert!(!e.flag(k.name)),
                Kind::FlagOn => assert!(e.flag(k.name), "{}", k.name),
                Kind::Num { default, .. } => assert_eq!(e.num(k.name).unwrap(), default, "{}", k.name),
                Kind::Millis { default_ms } => assert_eq!(e.millis(k.name).unwrap(), Duration::from_secs_f64(default_ms / 1000.0)),
                Kind::Text { default } => assert_eq!(e.string_or_default(k.name), default),
                Kind::OptNum { .. } | Kind::Choice { .. } | Kind::Paths | Kind::Path => {}
            }
            if k.product() {
                e.validate().unwrap_or_else(|m| panic!("{}: {m}", k.name));
            }
        }
        // A declared default is at least the minimum.
        for k in KNOBS {
            if let Kind::Num { default, min } = k.kind {
                assert!(default >= min || default == 0, "{}", k.name);
            }
        }
    }

    #[test]
    fn booleans() {
        with(
            &[("TLX_PARANOID", "1"), ("TLX_NO_NATIVE", "0"), ("TLX_COVERAGE", " off "), ("TLX_EQ_DEBUG", ""), ("TLX_CGEN_DEBUG", "yes")],
            |e| {
                assert!(e.flag("TLX_PARANOID") && e.flag("TLX_CGEN_DEBUG"));
                assert!(!e.flag("TLX_NO_NATIVE") && !e.flag("TLX_COVERAGE") && !e.flag("TLX_EQ_DEBUG") && !e.flag("TLX_NATIVE_SYNC"));
            },
        );
        // Default on: unset is on, anything off-ish is off.
        assert!(with(&[], |e| e.flag("TLX_MIXED")));
        assert!(!with(&[("TLX_MIXED", "0")], |e| e.flag("TLX_MIXED")));
        assert!(!with(&[("TLX_MIXED", "")], |e| e.flag("TLX_MIXED")));
        assert!(with(&[("TLX_MIXED", "1")], |e| e.flag("TLX_MIXED")));
        // `=0` is off for the switches that used to test only "is set".
        with(&[("TLX_JIT_VERIFY", "0"), ("TLX_JIT_DISASM", "0"), ("TLX_CC_SANITIZE", "0")], |e| {
            assert!(!e.flag("TLX_JIT_VERIFY") && !e.flag("TLX_JIT_DISASM") && !e.flag("TLX_CC_SANITIZE"));
            assert!(e.is_set("TLX_JIT_VERIFY"));
        });
        with(&[("TLX_JIT_VERIFY", "1")], |e| assert!(e.flag("TLX_JIT_VERIFY")));
    }

    #[test]
    fn numbers_and_their_errors() {
        with(&[("TLX_PRERUN", "3"), ("TLX_PRERUN_MS", "1s"), ("TLX_MAX_RESTARTS", "x"), ("TLX_RETAIN_MB", " 7 ")], |e| {
            assert_eq!(e.num("TLX_PRERUN"), Ok(3));
            assert_eq!(e.num("TLX_PRERUN_SETTLE"), Ok(2000));
            assert_eq!(e.opt_num("TLX_RETAIN_MB"), Ok(Some(7)));
            assert_eq!(e.num("TLX_PRERUN_MS").unwrap_err(), "invalid value of TLX_PRERUN_MS: \"1s\" (expected a number of milliseconds)");
            assert_eq!(
                e.opt_num("TLX_MAX_RESTARTS").unwrap_err(),
                "invalid value of TLX_MAX_RESTARTS: \"x\" (expected a number of restarts)"
            );
            assert_eq!(e.opt_num("TLX_FP_TABLE_MIN"), Ok(None));
        });
        // Blank: invalid where declared so, unset where `blank_unset`.
        with(&[("TLX_PRERUN", ""), ("TLX_FP_TABLE_MIN", "  "), ("TLX_MAX_DEPTH", ""), ("TLX_SEG_BYTES", "63")], |e| {
            assert!(e.num("TLX_PRERUN").is_err());
            assert_eq!(e.opt_num("TLX_FP_TABLE_MIN"), Ok(None));
            assert_eq!(e.num("TLX_MAX_DEPTH"), Ok(100_000));
            assert!(e.opt_num("TLX_SEG_BYTES").unwrap_err().contains("at least 64"));
        });
        with(&[("TLX_MAX_DEPTH", "0"), ("TLX_STATS_SAMPLE", "abc"), ("TLX_BAILOUT_DEBUG", "-1")], |e| {
            assert!(e.num("TLX_MAX_DEPTH").unwrap_err().contains("positive integer"));
            assert!(e.validate().is_err());
        });
        with(&[("TLX_CC_AT_EXIT_MS", "0.001")], |e| assert_eq!(e.millis("TLX_CC_AT_EXIT_MS"), Ok(Duration::from_micros(1))));
        with(&[("TLX_CC_AT_EXIT_MS", "-1")], |e| assert!(e.millis("TLX_CC_AT_EXIT_MS").is_err()));
        with(&[], |e| assert_eq!(e.millis("TLX_CC_AT_EXIT_MS"), Ok(Duration::from_millis(200))));
    }

    #[test]
    fn millis_rejects_values_a_duration_cannot_hold() {
        // A finite, non-negative number of milliseconds can still be far past
        // `Duration`'s range (`1e308` ms is about `1e305` seconds): that is an
        // invalid value like any other, not a panic.
        for v in ["1e308", "1e300", "1e23", "inf", "-inf", "NaN", "-1", "1s", ""] {
            with(&[("TLX_CC_AT_EXIT_MS", v)], |e| {
                assert!(e.millis("TLX_CC_AT_EXIT_MS").is_err(), "{v:?} must be rejected");
                assert!(e.validate().is_err(), "{v:?} is reported by validate()");
            });
        }
        with(&[("TLX_CC_AT_EXIT_MS", "1e308")], |e| {
            assert_eq!(
                e.millis("TLX_CC_AT_EXIT_MS").unwrap_err(),
                "invalid value of TLX_CC_AT_EXIT_MS: \"1e308\" (expected a number of milliseconds)"
            );
        });
        // A large but representable number of seconds still converts, and the
        // rounding of ordinary values is unchanged.
        with(&[("TLX_CC_AT_EXIT_MS", "1e22")], |e| assert!(e.millis("TLX_CC_AT_EXIT_MS").is_ok()));
        with(&[("TLX_CC_AT_EXIT_MS", "1.5")], |e| assert_eq!(e.millis("TLX_CC_AT_EXIT_MS"), Ok(Duration::from_micros(1500))));
        with(&[("TLX_CC_AT_EXIT_MS", " 200 ")], |e| assert_eq!(e.millis("TLX_CC_AT_EXIT_MS"), Ok(Duration::from_millis(200))));
    }

    #[test]
    fn choices_text_and_paths() {
        with(&[("TLX_JIT", "only"), ("TLX_THP", "ON")], |e| {
            assert_eq!(e.choice("TLX_JIT"), Ok(Some("only")));
            assert_eq!(e.choice("TLX_THP"), Ok(Some("on")));
        });
        with(&[("TLX_JIT", "yes"), ("TLX_THP", "")], |e| {
            assert_eq!(e.choice("TLX_JIT").unwrap_err(), "invalid value of TLX_JIT: \"yes\" (expected tier, 1, only or 0)");
            assert_eq!(e.choice("TLX_THP"), Ok(None));
        });
        with(&[("TLX_JIT", "Tier")], |e| assert!(e.choice("TLX_JIT").is_err()));
        with(&[("TLX_SPILL", " always "), ("TLX_MAXDISK", "")], |e| {
            assert_eq!(e.parsed("TLX_SPILL", |s| (s == "always").then_some(1)), Ok(Some(1)));
            assert_eq!(e.parsed("TLX_MAXDISK", |_| None::<u8>), Ok(None));
            assert_eq!(
                e.parsed("TLX_SPILL", |_| None::<u8>).unwrap_err(),
                "invalid value of TLX_SPILL: \"always\" (expected auto, off or always)"
            );
        });
        with(&[("TLX_PATH", "a:b"), ("CC", "clang"), ("TLX_IR_DUMP", "")], |e| {
            assert_eq!(e.paths("TLX_PATH"), [PathBuf::from("a"), PathBuf::from("b")]);
            assert!(e.paths("TLX_CLASSPATH").is_empty());
            assert_eq!(e.string_or_default("CC"), "clang");
            assert_eq!(e.string("TLX_IR_DUMP"), Some(String::new()));
            assert_eq!(e.path("TLX_CACHE"), None);
        });
        with(&[("TLX_METADIR", " ")], |e| assert_eq!(e.path("TLX_METADIR"), None));
        with(&[("TLX_METADIR", " d ")], |e| assert_eq!(e.path("TLX_METADIR"), Some(PathBuf::from("d"))));
        assert_eq!(with(&[], |e| e.string_or_default("CC")), "cc");
    }

    #[test]
    #[should_panic(expected = "not declared")]
    fn undeclared_is_a_bug() {
        with(&[], |e| e.flag("TLX_NO_SUCH_KNOB"));
    }

    #[test]
    #[should_panic(expected = "wrong kind")]
    fn wrong_accessor_is_a_bug() {
        with(&[], |e| e.flag("TLX_PRERUN"));
    }

    #[test]
    fn help_lists_every_product_knob_within_79_columns() {
        let help = help_text();
        for k in KNOBS.iter().filter(|k| k.product()) {
            assert!(help.contains(k.name), "{} missing from the help", k.name);
        }
        for k in KNOBS.iter().filter(|k| !k.product()) {
            assert!(!help.contains(&format!("  {}", k.name)), "{} is not for the help", k.name);
        }
        assert!(help.lines().all(|l| l.len() <= 79), "{help}");
        assert!(help.contains("  TLX_PRERUN=N         "), "{help}");
    }
}
