//! TLC-style messages: printed plainly, or, with `-tool`, wrapped as TLC
//! does for the Toolbox and other tools:
//!
//! ```text
//! @!@!@STARTMSG <code>:<class> @!@!@
//! <text>
//! @!@!@ENDMSG <code> @!@!@
//! ```
//!
//! The codes are TLC's (tlc2.output.EC), the classes those of
//! tlc2.output.MPRecorder (0 none, 1 error, 3 warning, 4 state).

use std::fmt::Write as _;
use std::io::Write as _;
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::Duration;

use tlx_runtime::{ErrorKind, ModelError};

static TOOL: AtomicBool = AtomicBool::new(false);

/// What reduced the search (a count-changing optimization of the default
/// mode), named in the final statistics line.
static REDUCED: std::sync::Mutex<Option<&'static str>> = std::sync::Mutex::new(None);

/// The search is reduced by `what` (`symmetry`): the final statistics line
/// says so (`... states left on queue (symmetry-reduced).`).
pub fn set_reduced(what: &'static str) {
    *REDUCED.lock().unwrap() = Some(what);
}

/// What reduced the search, if anything (`set_reduced`).
pub fn reduced() -> Option<&'static str> {
    *REDUCED.lock().unwrap()
}

/// The suffix of the final statistics line (empty when nothing reduced the
/// search).
pub fn reduced_suffix() -> String {
    reduced().map_or_else(String::new, |w| format!(" ({w}-reduced)"))
}

/// Wrap messages for tools from now on.
pub fn set_tool(on: bool) {
    TOOL.store(on, Ordering::Relaxed);
}

pub fn tool() -> bool {
    TOOL.load(Ordering::Relaxed)
}

/// TLC's message codes (tlc2.output.EC).
pub mod code {
    pub const GENERAL: u32 = 1000;
    /// tlx's own: the optimizations of the default mode (not a TLC code).
    pub const OPTIMIZATIONS_USED: u32 = 9100;
    pub const TLC_INITIAL_STATE: u32 = 2102;
    pub const TLC_INVARIANT_EVALUATION_FAILED: u32 = 2111;
    pub const TLC_MODULE_ARGUMENT_ERROR: u32 = 2169;
    pub const TLC_MODULE_OVERFLOW: u32 = 2178;
    pub const TLC_MODULE_NULL_POWER_NULL: u32 = 2180;
    pub const TLC_MODULE_APPLY_EMPTY_SEQ: u32 = 2184;
    pub const TLC_ASSUMPTION_FALSE: u32 = 2104;
    pub const TLC_ASSUMPTION_EVALUATION_ERROR: u32 = 2105;
    pub const TLC_STATE_NOT_COMPLETELY_SPECIFIED_INITIAL: u32 = 2106;
    pub const TLC_INVARIANT_VIOLATED_INITIAL: u32 = 2107;
    pub const TLC_STATE_NOT_COMPLETELY_SPECIFIED_NEXT: u32 = 2109;
    pub const TLC_PROPERTY_VIOLATED_INITIAL: u32 = 2108;
    pub const TLC_INVARIANT_VIOLATED_BEHAVIOR: u32 = 2110;
    pub const TLC_ACTION_PROPERTY_VIOLATED_BEHAVIOR: u32 = 2112;
    pub const TLC_ACTION_PROPERTY_EVALUATION_FAILED: u32 = 2113;
    pub const TLC_DEADLOCK_REACHED: u32 = 2114;
    /// No next-state action to generate successors from (the initial states
    /// were computed, so there are states to expand).
    pub const TLC_STATES_AND_NO_NEXT_ACTION: u32 = 2115;
    pub const TLC_TEMPORAL_PROPERTY_VIOLATED: u32 = 2116;
    pub const TLC_BEHAVIOR_UP_TO_THIS_POINT: u32 = 2121;
    pub const TLC_BACK_TO_STATE: u32 = 2122;
    pub const TLC_VALUE_ASSERT_FAILED: u32 = 2132;
    pub const TLC_MODULE_DIVISION_BY_ZERO: u32 = 2179;
    pub const TLC_SUBSCRIPT_CONTAIN_NO_STATE_VAR: u32 = 2140;
    pub const TLC_LIVE_FORMULA_STATE_LEVEL: u32 = 2255;
    /// A temporal property is trivially true.
    pub const TLC_LIVE_FORMULA_TAUTOLOGY: u32 = 2253;
    pub const TLC_SANY_END: u32 = 2219;
    pub const TLC_SANY_START: u32 = 2220;
    pub const TLC_CONFIG_VALUE_NOT_ASSIGNED_TO_CONSTANT_PARAM: u32 = 2222;
    /// The right-hand side of a `<-` appears on the left-hand side of another.
    pub const TLC_CONFIG_RHS_ID_APPEARED_AFTER_LHS_ID: u32 = 2223;
    /// The right-hand side of a `<-` is not defined by the spec.
    pub const TLC_CONFIG_WRONG_SUBSTITUTION: u32 = 2224;
    /// The two sides of a `<-` have a different number of arguments.
    pub const TLC_CONFIG_WRONG_SUBSTITUTION_NUMBER_OF_ARGS: u32 = 2225;
    /// The left-hand side of a `<-` does not appear in the spec.
    pub const TLC_CONFIG_ID_DOES_NOT_APPEAR_IN_SPEC: u32 = 2226;
    /// Both a SPECIFICATION and an INIT/NEXT (or a section it belongs to).
    pub const TLC_CONFIG_NOT_BOTH_SPEC_AND_INIT: u32 = 2227;
    /// A name the configuration refers to takes arguments.
    pub const TLC_CONFIG_ID_REQUIRES_NO_ARG: u32 = 2228;
    /// A name the configuration refers to is not defined by the spec.
    pub const TLC_CONFIG_SPECIFIED_NOT_DEFINED: u32 = 2229;
    /// A name the configuration refers to is a constant with a value.
    pub const TLC_CONFIG_ID_HAS_VALUE: u32 = 2230;
    /// The configuration specifies no initial state predicate.
    pub const TLC_CONFIG_MISSING_INIT: u32 = 2231;
    /// The configuration substitutes a definition that is not constant (and
    /// cannot be evaluated at startup) for a constant.
    pub const TLC_CONFIG_SUBSTITUTION_NON_CONSTANT: u32 = 2281;
    /// A conjunct of the SPECIFICATION is a definition valued FALSE.
    pub const TLC_CONFIG_SPEC_IS_TRIVIAL: u32 = 2237;
    /// The configuration specifies no next-state predicate.
    pub const TLC_CONFIG_MISSING_NEXT: u32 = 2232;
    /// A name the configuration refers to is a constant (not an operator).
    pub const TLC_CONFIG_ID_MUST_NOT_BE_CONSTANT: u32 = 2233;
    /// The configuration substitutes for a name in a module that is not part
    /// of the specification.
    pub const TLC_NO_MODULES: u32 = 2245;
    pub const TLC_STARTING: u32 = 2185;
    pub const TLC_FINISHED: u32 = 2186;
    pub const TLC_MODE_MC: u32 = 2187;
    pub const TLC_MODE_SIMU: u32 = 2188;
    pub const TLC_COMPUTING_INIT: u32 = 2189;
    pub const TLC_INIT_GENERATED1: u32 = 2190;
    pub const TLC_INIT_GENERATED2: u32 = 2191;
    pub const TLC_CHECKING_TEMPORAL_PROPS: u32 = 2192;
    pub const TLC_SUCCESS: u32 = 2193;
    pub const TLC_SEARCH_DEPTH: u32 = 2194;
    pub const TLC_CHECKPOINT_START: u32 = 2195;
    pub const TLC_CHECKPOINT_END: u32 = 2196;
    pub const TLC_CHECKPOINT_RECOVER_START: u32 = 2197;
    pub const TLC_CHECKPOINT_RECOVER_END: u32 = 2198;
    pub const TLC_STATS: u32 = 2199;
    pub const TLC_PROGRESS_STATS: u32 = 2200;
    pub const TLC_PROGRESS_SIMU: u32 = 2209;
    pub const TLC_STATS_SIMU: u32 = 2210;
    pub const TLC_LIVE_IMPLIED: u32 = 2212;
    pub const TLC_FEATURE_UNSUPPORTED_LIVENESS_SYMMETRY: u32 = 2279;
    pub const TLC_STATE_PRINT2: u32 = 2217;
    pub const TLC_STATE_PRINT3: u32 = 2218;
    pub const TLC_VERSION: u32 = 2262;
    pub const TLC_COUNTER_EXAMPLE: u32 = 2264;
    pub const TLC_INTEGER_TOO_BIG: u32 = 2265;
    pub const TLC_CANT_HANDLE_REAL_NUMBERS: u32 = 2244;
    pub const TLC_CHECKING_TEMPORAL_PROPS_END: u32 = 2267;
    pub const TLC_STATE_GRAPH_OUTDEGREE: u32 = 2268;
    pub const TLC_COMPUTING_INIT_PROGRESS: u32 = 2269;
    pub const TLC_NO_STATES_SATISFYING_INIT_AND_CONSTRAINT: u32 = 2256;
    pub const TLC_COVERAGE_START: u32 = 2201;
    pub const TLC_COVERAGE_END: u32 = 2202;
    pub const TLC_COVERAGE_NEXT: u32 = 2772;
    pub const TLC_COVERAGE_INIT: u32 = 2773;
    pub const TLC_COVERAGE_END_OVERHEAD: u32 = 2777;
    pub const TLC_POSTCONDITION_FALSE: u32 = 2404;
    pub const TLC_POSTCONDITION_EVALUATION_ERROR: u32 = 2405;
}

/// TLC's message classes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Class {
    None = 0,
    Error = 1,
    Warning = 3,
    State = 4,
}

/// Message `text`, as printed (with its final newline).
pub fn format(code: u32, class: Class, text: &str) -> String {
    if tool() {
        format!("@!@!@STARTMSG {code}:{} @!@!@\n{text}\n@!@!@ENDMSG {code} @!@!@\n", class as u8)
    } else {
        let prefix = match class {
            Class::Error => "Error: ",
            Class::Warning => "Warning: ",
            _ => "",
        };
        format!("{prefix}{text}\n")
    }
}

/// Print message `text` (as one write, so that messages printed from
/// several threads do not interleave).
pub fn print(code: u32, class: Class, text: &str) {
    let mut out = std::io::stdout().lock();
    let _ = out.write_all(format(code, class, text).as_bytes());
    let _ = out.flush();
}

pub fn info(code: u32, text: &str) {
    print(code, Class::None, text)
}

pub fn error(code: u32, text: &str) {
    print(code, Class::Error, text)
}

/// A warning.
pub fn warning(code: u32, text: &str) {
    if NOWARNING.load(Ordering::Relaxed) {
        return;
    }
    // TLC's plain output tells how to disable warnings (once).
    if tool() || HINTED.swap(true, Ordering::Relaxed) {
        print(code, Class::Warning, text)
    } else {
        print(code, Class::Warning, &format!("{text}\n(Use the -nowarning option to disable this warning.)"))
    }
}

static HINTED: AtomicBool = AtomicBool::new(false);

static NOWARNING: AtomicBool = AtomicBool::new(false);

/// `-nowarning`: do not print warnings.
pub fn set_nowarning(on: bool) {
    NOWARNING.store(on, Ordering::Relaxed);
}

/// State number `num` (1-based) of a trace, reached by `label`
/// (e.g. `<Next line ...>`).
pub fn state(num: usize, label: &str, state: &str) -> String {
    if tool() {
        format(code::TLC_STATE_PRINT2, Class::State, &format!("{num}: {label}\n{state}\n"))
    } else {
        format!("State {num}: {label}\n{state}\n\n")
    }
}

/// The end of a lasso: back to state `num` by `label`.
pub fn back_to_state(num: usize, label: &str) -> String {
    if tool() {
        format(code::TLC_BACK_TO_STATE, Class::State, &format!("{num}: Back to state: {label}\n"))
    } else {
        format!("Back to state {num}: {label}\n\n")
    }
}

/// The end of a lasso: stuttering after state `num - 1`.
pub fn stuttering(num: usize) -> String {
    if tool() {
        format(code::TLC_STATE_PRINT3, Class::State, &format!("{num}: Stuttering"))
    } else {
        format!("State {num}: Stuttering\n")
    }
}

/// The kind of an evaluation error: its own, or for errors without one
/// (raised by the compiled tier, which does not classify its errors), the
/// kind its message shows. (A layout miss, which is not an error of the
/// spec, is a general error.)
pub fn error_kind(e: &ModelError) -> ErrorKind {
    if !matches!(e.kind, ErrorKind::General | ErrorKind::LayoutMiss | ErrorKind::FunctionDomain) {
        return e.kind;
    }
    let msg = &e.message;
    if msg.starts_with("TLC can't handle a number this big") {
        ErrorKind::IntegerTooBig
    } else if msg.starts_with("The second argument of \\div is 0") {
        ErrorKind::DivisionByZero
    } else if msg.starts_with("The second argument of % should be a positive")
        || msg.starts_with("The second argument of ^ should be a natural")
    {
        ErrorKind::ArgumentError
    } else if msg.starts_with("Overflow when computing") {
        ErrorKind::Overflow
    } else if msg.starts_with("The first argument of Assert evaluated to FALSE") {
        ErrorKind::AssertFailed
    } else {
        ErrorKind::General
    }
}

/// The message code TLC reports an error of kind `kind` with.
pub fn kind_code(kind: ErrorKind) -> u32 {
    match kind {
        ErrorKind::General | ErrorKind::Unsupported | ErrorKind::LayoutMiss | ErrorKind::FunctionDomain => code::GENERAL,
        ErrorKind::AssertFailed => code::TLC_VALUE_ASSERT_FAILED,
        ErrorKind::DivisionByZero => code::TLC_MODULE_DIVISION_BY_ZERO,
        ErrorKind::ArgumentError => code::TLC_MODULE_ARGUMENT_ERROR,
        ErrorKind::Overflow => code::TLC_MODULE_OVERFLOW,
        ErrorKind::NullPowerNull => code::TLC_MODULE_NULL_POWER_NULL,
        ErrorKind::ApplyEmptySeq => code::TLC_MODULE_APPLY_EMPTY_SEQ,
        ErrorKind::IntegerTooBig => code::TLC_INTEGER_TOO_BIG,
    }
}

/// The code of an evaluation error with message `msg` (for errors reported
/// as text only).
pub fn error_code(msg: &str) -> u32 {
    kind_code(error_kind(&ModelError::new(msg)))
}

/// The text of an error of kind `kind` as part of another message: with
/// `-tool`, an error with its own code is a message of its own, nested
/// (TLC prints the exception's message, which is one).
pub fn nested(kind: ErrorKind, msg: &str) -> String {
    let c = kind_code(kind);
    if tool() && c != code::GENERAL {
        format!("@!@!@STARTMSG {c}:0 @!@!@\n{msg}\n@!@!@ENDMSG {c} @!@!@")
    } else {
        msg.to_string()
    }
}

/// TLC's report of an exception it did not expect: an error of kind
/// `kind` (its Java exception class) with message `msg`.
pub fn unexpected_exception(kind: ErrorKind, msg: &str) -> String {
    let class = match kind {
        ErrorKind::General => "java.lang.RuntimeException",
        ErrorKind::Unsupported => "java.lang.UnsupportedOperationException",
        _ => "tlc2.tool.EvalException",
    };
    format!(
        "TLC threw an unexpected exception.\nThis was probably caused by an error in the spec or model.\nSee the User Output or TLC Console for clues to what happened.\nThe exception was a {class}\n: {}",
        nested(kind, msg)
    )
}

/// `n` with thousands separators (TLC's progress reports).
pub use tlx_base::format::commas;

/// The local date and time as TLC prints it: `2024-01-31 13:45:00`.
pub fn now() -> String {
    let t = std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).map_or(0, |d| d.as_secs()) as libc::time_t;
    // SAFETY: an all-zero `tm` is valid (integers and a nullable `tm_zone`
    // pointer); `localtime_r` is thread-safe and only writes the `tm` it is
    // given, and `t` and `tm` outlive the call.
    let tm = unsafe {
        let mut tm: libc::tm = std::mem::zeroed();
        if libc::localtime_r(&t, &mut tm).is_null() {
            return String::new();
        }
        tm
    };
    format!("{:04}-{:02}-{:02} {:02}:{:02}:{:02}", tm.tm_year + 1900, tm.tm_mon + 1, tm.tm_mday, tm.tm_hour, tm.tm_min, tm.tm_sec)
}

/// A run time as TLC prints it: `05s`, `01min 05s`, `02h 01min`,
/// `1d 02h`; in milliseconds for tools.
pub fn duration(d: Duration) -> String {
    let ms = d.as_millis() as u64;
    if tool() {
        return format!("{ms}ms");
    }
    let (s, m, h) = ((ms / 1000) % 60, (ms / 60_000) % 60, (ms / 3_600_000) % 24);
    if ms > 86_400_000 {
        format!("{}d {h:02}h", ms / 86_400_000)
    } else if ms > 3_600_000 {
        format!("{h:02}h {m:02}min")
    } else if ms > 60_000 {
        format!("{m:02}min {s:02}s")
    } else {
        format!("{s:02}s")
    }
}

/// A probability as TLC prints it (Java's `Double.toString` of the value
/// rounded to two significant digits): `2.0E-17`, `0.0`, `0.012`.
pub fn probability(p: f64) -> String {
    if p == 0.0 || !p.is_finite() {
        return "0.0".into();
    }
    let e = p.abs().log10().floor() as i32;
    // Two significant digits.
    let mut m = (p / 10f64.powi(e) * 10.0).round() / 10.0;
    let mut e = e;
    if m >= 10.0 {
        m /= 10.0;
        e += 1;
    }
    if (-3..7).contains(&e) {
        let v = m * 10f64.powi(e);
        let mut s = String::new();
        let decimals = (1 - e).max(1) as usize;
        let _ = write!(s, "{v:.decimals$}");
        // Java prints the shortest form: no trailing zeros (but one decimal).
        while s.ends_with('0') && !s.ends_with(".0") {
            s.pop();
        }
        s
    } else {
        format!("{m:.1}E{e}")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn formats() {
        assert_eq!(probability(0.0), "0.0");
        assert_eq!(probability(1.9516e-17), "2.0E-17");
        assert_eq!(probability(1.648e-11), "1.6E-11");
        assert_eq!(probability(4.39e-4), "4.4E-4");
        assert_eq!(probability(0.0123), "0.012");
        assert_eq!(probability(0.5), "0.5");
        assert_eq!(duration(Duration::from_millis(213)), "00s");
        assert_eq!(duration(Duration::from_millis(65_000)), "01min 05s");
        assert_eq!(duration(Duration::from_millis(2 * 3_600_000 + 60_000)), "02h 01min");
        assert_eq!(duration(Duration::from_millis(26 * 3_600_000)), "1d 02h");
    }
}
