//! Command line and environment configuration: help text, invalid values,
//! and that every knob is documented.

use std::collections::BTreeSet;
use std::path::{Path, PathBuf};

use tlx_base::knobs::{self, Audience, Kind, KNOBS};

fn tlx(args: &[&str], env: &[(&str, &str)]) -> (i32, String, String) {
    let out = tlx_testkit::tlx!().args(args).envs(env.iter().copied()).run();
    (out.code, out.stdout, out.stderr)
}

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// The text of every file under `dir` whose name ends with one of `exts`.
fn sources(dir: &Path, exts: &[&str], out: &mut Vec<(PathBuf, String)>) {
    let Ok(entries) = std::fs::read_dir(dir) else { return };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            sources(&path, exts, out);
        } else if exts.iter().any(|e| path.to_string_lossy().ends_with(e)) {
            if let Ok(text) = std::fs::read_to_string(&path) {
                out.push((path, text));
            }
        }
    }
}

fn configuration_md() -> String {
    std::fs::read_to_string(root().join("docs/configuration.md")).expect("docs/configuration.md")
}

/// The `## ` section of `text` whose heading starts with `heading`.
fn section<'a>(text: &'a str, heading: &str) -> &'a str {
    text.split("\n## ").find(|s| s.starts_with(heading)).unwrap_or_else(|| panic!("no `## {heading}` section"))
}

/// The cells of a Markdown table row, split on the `|` that delimit them (a
/// `\|` is a literal pipe inside a cell). The outer empty cells are kept, so
/// in `| a | b |` the cells are at indices 1 and 2, and joining the cells
/// with `|` gives the line back.
fn split_cells(line: &str) -> Vec<String> {
    let mut cells = vec![String::new()];
    let mut chars = line.chars();
    while let Some(c) = chars.next() {
        if c == '\\' {
            let cell = cells.last_mut().expect("a cell");
            cell.push(c);
            if let Some(escaped) = chars.next() {
                cell.push(escaped);
            }
        } else if c == '|' {
            cells.push(String::new());
        } else {
            cells.last_mut().expect("a cell").push(c);
        }
    }
    cells
}

/// The data rows of the table of `section` (the header and the `|---|`
/// separator dropped), as cell vectors.
fn table_rows(section: &str) -> Vec<Vec<String>> {
    let mut rows = Vec::new();
    let mut header = true;
    for line in section.lines().filter(|line| line.starts_with('|')) {
        let cells = split_cells(line);
        if cells.len() < 4 {
            continue;
        }
        if header {
            header = false;
            continue;
        }
        if cells[1].trim().chars().all(|c| c == '-' || c == ' ') {
            continue;
        }
        rows.push(cells);
    }
    rows
}

/// The environment variable table rows of `text`, as `(name, cells)`.
fn env_rows(text: &str) -> Vec<(String, Vec<String>)> {
    table_rows(section(text, "Environment variables"))
        .into_iter()
        .map(|cells| (cells[1].trim().trim_matches('`').to_string(), cells))
        .filter(|(name, _)| !name.is_empty())
        .collect()
}

/// Rewrite cell `index` of the environment row `name` of `text` (a negative
/// fixture for the checks below).
fn set_cell(text: &str, name: &str, index: usize, value: &str) -> String {
    let mut out: Vec<String> = text
        .lines()
        .map(|line| {
            let mut cells = split_cells(line);
            if cells.len() > index && cells[1].trim().trim_matches('`') == name {
                cells[index] = format!(" {value} ");
                cells.join("|")
            } else {
                line.to_string()
            }
        })
        .collect();
    if text.ends_with('\n') {
        out.push(String::new());
    }
    out.join("\n")
}

/// Whether `token` appears in `text` as a whole option or label (so `-h` does
/// not match inside `-help`).
fn mentions(text: &str, token: &str) -> bool {
    let bytes = text.as_bytes();
    let boundary = |b: u8| !b.is_ascii_alphanumeric() && b != b'-' && b != b'_';
    let mut searched = 0;
    while let Some(offset) = text[searched..].find(token) {
        let start = searched + offset;
        let end = start + token.len();
        if (start == 0 || boundary(bytes[start - 1])) && (end == bytes.len() || boundary(bytes[end])) {
            return true;
        }
        searched = start + 1;
    }
    false
}

/// The `TLX_*` names (and `CC`) of the rows of the environment variable
/// table of docs/configuration.md.
fn documented_from(text: &str) -> BTreeSet<String> {
    // (Other programs' variables, such as MIMALLOC_*, are not declared.)
    env_rows(text).into_iter().map(|(name, _)| name).filter(|name| name.starts_with("TLX_") || name == "CC").collect()
}

fn documented() -> BTreeSet<String> {
    documented_from(&configuration_md())
}

/// The default of a declared kind as the Default column of
/// docs/configuration.md spells it ("" when the kind has no literal default
/// and the consumer decides what unset means).
fn default_text(kind: Kind) -> String {
    match kind {
        Kind::FlagOn => "on".into(),
        Kind::Num { default, .. } => default.to_string(),
        Kind::Millis { default_ms } => default_ms.to_string(),
        Kind::Text { default } => default.to_string(),
        Kind::Flag | Kind::OptNum { .. } | Kind::Choice { .. } | Kind::Paths | Kind::Path => String::new(),
    }
}

/// Every declared variable whose kind has a literal default, checked against
/// the Default column of its documentation row. Variables whose default is
/// computed (an unset `Flag`, `OptNum` or `Choice`, a `Path`, or an empty
/// `Text`) are not checked here: their row describes the unset behavior in
/// the Effect column instead.
fn env_default_problems(doc: &str) -> Vec<String> {
    let rows = env_rows(doc);
    let mut problems = Vec::new();
    for k in KNOBS.iter().filter(|k| k.audience != Audience::Internal) {
        let want = default_text(k.kind);
        if want.is_empty() {
            continue;
        }
        match rows.iter().find(|(name, _)| name == k.name) {
            None => problems.push(format!("{}: no row in docs/configuration.md", k.name)),
            Some((_, cells)) => {
                let got = cells[3].trim().trim_matches('`').trim();
                if got != want {
                    problems.push(format!("{}: documented default {got:?}, declared default {want:?}", k.name));
                }
            }
        }
    }
    problems
}

/// Rows whose Audience column is deliberately broader than the declared
/// audience: `TLX_THP` is declared for developers but documented for users,
/// because its value is a user-visible performance switch.
const DOCUMENTED_FOR_USERS: &[&str] = &["TLX_THP"];

/// The Audience column of every declared variable, checked against the
/// declared audience: a variable declared for users is documented for users,
/// and one that is not is not.
fn env_audience_problems(doc: &str) -> Vec<String> {
    let rows = env_rows(doc);
    let mut problems = Vec::new();
    for k in KNOBS.iter().filter(|k| k.audience != Audience::Internal) {
        let Some((_, cells)) = rows.iter().find(|(name, _)| name == k.name) else {
            problems.push(format!("{}: no row in docs/configuration.md", k.name));
            continue;
        };
        let cell = cells[5].trim();
        if !matches!(cell, "User" | "Developer" | "Test" | "User / Test") {
            problems.push(format!("{}: audience {cell:?} is not one of the declared audiences", k.name));
        } else if !DOCUMENTED_FOR_USERS.contains(&k.name) && cell.contains("User") != (k.audience == Audience::User) {
            problems.push(format!("{}: documented {cell:?}, declared {:?}", k.name, k.audience));
        }
    }
    problems
}

/// Every option spelling the `tlx check` parser accepts (`crates/tlx-cli/src/args.rs`
/// is the source of truth; this is the audited inventory). `-dumptrace`,
/// `-help` and `--help` are accepted aliases; `-ir` is deliberately rejected
/// with a message and is not accepted.
const ACCEPTED_CHECK_OPTIONS: &[&str] = &[
    "--help",
    "-I",
    "-checkpoint",
    "-checksymmetry",
    "-cleanup",
    "-compile",
    "-config",
    "-coverage",
    "-deadlock",
    "-depth",
    "-difftrace",
    "-dump",
    "-dumpTrace",
    "-dumptrace",
    "-fpbits",
    "-fpmem",
    "-generate",
    "-h",
    "-help",
    "-interp",
    "-maxdisk",
    "-maxSetSize",
    "-maxmem",
    "-metadir",
    "-noGenerateSpecTE",
    "-noautosymmetry",
    "-nowarning",
    "-optimize",
    "-progress",
    "-proofdir",
    "-recover",
    "-seed",
    "-simulate",
    "-spill",
    "-stats",
    "-suggest",
    "-symmetrydepth",
    "-symmetryedges",
    "-symmetryperms",
    "-symmetrystates",
    "-tlc",
    "-tool",
    "-view",
    "-workers",
];

/// The option spellings of the command-line table of docs/configuration.md,
/// checked against the parser's accepted spellings.
fn cli_alias_problems(doc: &str) -> Vec<String> {
    let table = section(doc, "Command-line options");
    ACCEPTED_CHECK_OPTIONS
        .iter()
        .filter(|option| !mentions(table, option))
        .map(|option| format!("{option} is accepted by the parser but not documented in the command-line table"))
        .collect()
}

#[test]
fn docs_list_exactly_the_declared_variables() {
    let declared: BTreeSet<String> = KNOBS.iter().filter(|k| k.audience != Audience::Internal).map(|k| k.name.to_string()).collect();
    let documented = documented();
    let undocumented: Vec<_> = declared.difference(&documented).collect();
    let unknown: Vec<_> = documented.difference(&declared).collect();
    assert!(undocumented.is_empty(), "declared in tlx_base::knobs but missing from docs/configuration.md: {undocumented:?}");
    assert!(unknown.is_empty(), "in docs/configuration.md but not declared in tlx_base::knobs: {unknown:?}");
}

#[test]
fn every_variable_literal_in_the_sources_is_declared_and_every_declaration_is_used() {
    let mut src = Vec::new();
    sources(&root().join("crates"), &[".rs"], &mut src);
    let mut scripts = Vec::new();
    sources(&root().join("scripts"), &[".py", ".sh"], &mut scripts);
    let table = std::path::Path::new("tlx-base/src/knobs.rs");
    let mut used = BTreeSet::new();
    for (path, text) in &src {
        if path.ends_with(table) {
            continue;
        }
        // `"TLX_NAME"`, as a whole string literal.
        for part in text.split('"').skip(1).step_by(2) {
            if part.starts_with("TLX_") && part.bytes().all(|b| b.is_ascii_uppercase() || b.is_ascii_digit() || b == b'_') && part.len() > 4
            {
                used.insert(part.to_string());
                if path.components().any(|c| c.as_os_str() == "src") {
                    assert!(KNOBS.iter().any(|k| k.name == part), "{part} (in {}) is not declared in tlx_base::knobs", path.display());
                }
            }
        }
        used.extend(KNOBS.iter().filter(|k| text.contains(&format!("\"{}\"", k.name))).map(|k| k.name.to_string()));
    }
    for k in KNOBS {
        let in_scripts = scripts.iter().any(|(_, text)| text.contains(k.name));
        assert!(
            used.contains(k.name) || in_scripts || HARNESS_READERS.contains(&k.name),
            "{} is declared in tlx_base::knobs but nothing reads it",
            k.name
        );
    }
}

/// Variables whose only reader is the agent harness, which the published
/// sources do not carry (`AGENTS.md`, `.githooks/`, `harness/`; docs/testing.md,
/// "The agent harness and the product's tooling"). They stay declared and
/// documented - `TLX_HOOKS` is read by `.githooks/pre-commit` and
/// `.githooks/commit-msg` - but no checkout that drops the harness carries the
/// reader, so "nothing reads it" cannot be asserted for them from the sources
/// this test can see. The list is explicit so a knob that stops being read
/// *by shipped code* still fails it.
const HARNESS_READERS: &[&str] = &["TLX_HOOKS"];

#[test]
fn help_lists_every_variable() {
    let (code, help, _) = tlx(&["check", "-h"], &[]);
    assert_eq!(code, 0);
    assert!(help.contains("-workers") && help.contains("-fpmem"), "{help}");
    assert!(help.ends_with(&knobs::help_text()), "the environment section is generated from the table");
    for k in KNOBS.iter().filter(|k| k.product()) {
        assert!(help.contains(k.name), "{} missing from tlx check -h", k.name);
    }
    let doc = std::fs::read_to_string(root().join("docs/configuration.md")).expect("docs/configuration.md");
    for opt in [
        "-config",
        "-workers",
        "-deadlock",
        "-simulate",
        "-generate",
        "-depth",
        "-seed",
        "-dump",
        "-fpmem",
        "-maxSetSize",
        "-maxmem",
        "-tool",
        "-nowarning",
        "-I",
        "-progress",
        "-compile",
    ] {
        assert!(doc.contains(&format!("`{opt}")), "{opt} missing from docs/configuration.md");
    }
}

#[test]
fn bad_values_of_every_kind_exit_2() {
    for (name, value, what) in [
        ("TLX_MAX_DEPTH", "deep", "positive integer"),
        ("TLX_STATS_SAMPLE", "0", "positive integer"),
        ("TLX_BAILOUT_DEBUG", "-1", "number of errors"),
        ("TLX_THP", "maybe", "auto, on or off"),
        ("TLX_SEG_BYTES", "8", "at least 64"),
        ("TLX_CHECKPOINT_SECS", "soon", "number of seconds"),
    ] {
        let (code, _, err) = tlx(&["check", "X.tla"], &[(name, value)]);
        assert_eq!(code, 2, "{name}={value}: {err}");
        assert!(err.contains(&format!("invalid value of {name}: \"{value}\"")) && err.contains(what), "{err}");
    }
}

#[test]
fn workers_zero_is_rejected() {
    let (code, _, err) = tlx(&["check", "X.tla", "-workers", "0"], &[]);
    assert_eq!(code, 2);
    assert!(err.contains("-workers must be at least 1"), "{err}");
    // `-workers auto` stays valid (the run then fails on the missing spec).
    let (code, _, err) = tlx(&["check", "X.tla", "-workers", "auto"], &[]);
    assert_ne!(code, 2, "{err}");
    assert!(!err.contains("-workers"), "{err}");
}

#[test]
fn invalid_values_are_reported() {
    let (code, _, err) = tlx(&["check", "X.tla"], &[("TLX_PRERUN_MS", "1s")]);
    assert_eq!(code, 2);
    assert!(err.contains("invalid value of TLX_PRERUN_MS: \"1s\""), "{err}");
    let (code, _, err) = tlx(&["check", "X.tla"], &[("TLX_INJECT_MISMATCH", "flip")]);
    assert_eq!(code, 2);
    assert!(err.contains("TLX_INJECT_MISMATCH"), "{err}");
    let (code, _, err) = tlx(&["check", "X.tla", "-workers", "many"], &[]);
    assert_eq!(code, 2);
    assert!(err.contains("invalid value of -workers: \"many\""), "{err}");
    let (code, _, err) = tlx(&["check", "X.tla", "-frobnicate"], &[]);
    assert_eq!(code, 2);
    assert!(err.contains("unknown option -frobnicate"), "{err}");
    // `-ir` (the lowered-IR mode) was removed.
    let (code, _, err) = tlx(&["check", "X.tla", "-ir"], &[]);
    assert_eq!(code, 2);
    assert!(err.contains("-ir was removed; use -compile"), "{err}");
    let (code, _, err) = tlx(&["check", "X.tla", "-fpmem", "1.5"], &[]);
    assert_eq!(code, 2);
    assert!(err.contains("-fpmem"), "{err}");
    for bad in ["1.5", "0", "12Q", "100K"] {
        let (code, _, err) = tlx(&["check", "X.tla", "-maxmem", bad], &[]);
        assert_eq!(code, 2);
        assert!(err.contains(&format!("invalid value of -maxmem: \"{bad}\"")), "{err}");
    }
    let (code, _, err) = tlx(&["check", "X.tla"], &[("TLX_MAXMEM", "lots")]);
    assert_eq!(code, 2);
    assert!(err.contains("invalid value of TLX_MAXMEM: \"lots\""), "{err}");
    for empty in ["", ".tla"] {
        let (code, _, err) = tlx(&["check", empty], &[]);
        assert_eq!(code, 2, "{empty:?}: {err}");
        assert!(err.contains("empty spec name"), "{empty:?}: {err}");
    }
    let (code, _, err) = tlx(&["check", "X.tla", "Y.tla"], &[]);
    assert_eq!(code, 2);
    assert!(err.contains("more than one spec: Y.tla"), "{err}");
}

#[test]
fn minute_intervals_reject_overflow() {
    for opt in ["-coverage", "-checkpoint"] {
        for minutes in [u64::MAX / 60 + 1, u64::MAX] {
            let value = minutes.to_string();
            let (code, _, err) = tlx(&["check", "X.tla", opt, &value], &[]);
            assert_eq!(code, 2, "{opt} {value}: {err}");
            assert!(err.contains(&format!("invalid value of {opt}: {value:?}")), "{err}");
            assert!(!err.contains("panicked"), "{err}");
        }
    }
}

#[test]
fn minute_intervals_accept_boundary_and_zero() {
    let spec = root().join("tests/specs/N1.tla");
    for opt in ["-coverage", "-checkpoint"] {
        for minutes in [0, 1, u64::MAX / 60] {
            let value = minutes.to_string();
            let (code, out, err) = tlx(&["check", spec.to_str().unwrap(), opt, &value], &[]);
            assert_eq!(code, 0, "{opt} {value}: {out}\n{err}");
            if opt == "-coverage" {
                assert!(out.contains("The coverage statistics"), "{out}");
            }
        }
    }
}

#[test]
fn checkpoint_seconds_override_wins_unless_minutes_are_zero() {
    let spec = root().join("tests/specs/N1.tla");
    for minutes in [u64::MAX / 60 + 1, u64::MAX] {
        for seconds in [0, u64::MAX] {
            let value = minutes.to_string();
            let seconds = seconds.to_string();
            let (code, out, err) = tlx(&["check", spec.to_str().unwrap(), "-checkpoint", &value], &[("TLX_CHECKPOINT_SECS", &seconds)]);
            assert_eq!(code, 0, "{value} minutes, {seconds} seconds: {out}\n{err}");
        }
    }
    // Zero disables both time- and state-triggered checkpoints, even with overrides.
    let (code, out, err) = tlx(
        &["check", spec.to_str().unwrap(), "-checkpoint", "0"],
        &[("TLX_CHECKPOINT_SECS", "0"), ("TLX_CHECKPOINT_STATES", "1"), ("TLX_CHECKPOINT_ABORT", "1")],
    );
    assert_eq!(code, 0, "{out}\n{err}");
    assert!(!out.contains("Checkpointing of run"), "{out}");
}

/// Every declared variable whose kind carries a literal default must document
/// exactly that value in the Default column of its row (a variable whose
/// default is computed describes the unset behavior in the Effect column
/// instead and is not checked here).
#[test]
fn docs_static_defaults_match_declarations() {
    let problems = env_default_problems(&configuration_md());
    assert!(problems.is_empty(), "{problems:#?}");
}

/// A row that contradicts its declaration (a changed default, or a row that
/// disappeared) is reported.
#[test]
fn docs_static_defaults_detect_a_changed_row() {
    let doc = configuration_md();
    assert!(env_default_problems(&doc).is_empty());

    let changed = set_cell(&doc, "TLX_CACHE_MB", 3, "2048");
    assert_ne!(changed, doc, "the fixture did not change docs/configuration.md");
    let problems = env_default_problems(&changed);
    assert_eq!(problems.len(), 1, "{problems:#?}");
    assert!(problems[0].contains("TLX_CACHE_MB"), "{problems:#?}");

    let missing: String = doc.lines().filter(|line| !line.starts_with("| `TLX_MEMO_SLOTS` |")).map(|line| format!("{line}\n")).collect();
    let problems = env_default_problems(&missing);
    assert_eq!(problems.len(), 1, "{problems:#?}");
    assert!(problems[0].contains("TLX_MEMO_SLOTS"), "{problems:#?}");
}

/// The Audience column of every declared variable must be one of the declared
/// audiences, and must name the user-facing one exactly for a variable
/// declared for users.
#[test]
fn docs_audience_matches_declarations() {
    let problems = env_audience_problems(&configuration_md());
    assert!(problems.is_empty(), "{problems:#?}");
}

/// A row whose audience contradicts the declaration, or that is not a
/// declared audience at all, is reported.
#[test]
fn docs_audience_detects_a_changed_row() {
    let doc = configuration_md();

    let narrowed = set_cell(&doc, "TLX_CLOUD_HOST", 5, "Internal");
    assert_ne!(narrowed, doc, "the fixture did not change docs/configuration.md");
    let problems = env_audience_problems(&narrowed);
    assert_eq!(problems.len(), 1, "{problems:#?}");
    assert!(problems[0].contains("TLX_CLOUD_HOST"), "{problems:#?}");

    let nonsense = set_cell(&doc, "TLX_CLOUD_HOST", 5, "Wizard");
    let problems = env_audience_problems(&nonsense);
    assert_eq!(problems.len(), 1, "{problems:#?}");
    assert!(problems[0].contains("TLX_CLOUD_HOST"), "{problems:#?}");
}

/// Every option spelling the parser accepts (the audited inventory in
/// `ACCEPTED_CHECK_OPTIONS`) appears in the command-line table.
#[test]
fn docs_cli_aliases_are_documented() {
    let problems = cli_alias_problems(&configuration_md());
    assert!(problems.is_empty(), "{problems:#?}");
}

/// An accepted spelling that disappears from the table is reported: the
/// lowercase `-dumptrace` alias only lives in the effect of the `-dumpTrace`
/// row, and dropping it must be caught.
#[test]
fn docs_cli_aliases_detect_a_removed_alias() {
    let doc = configuration_md();
    let without = doc.replace("The lowercase alias `-dumptrace` is accepted; ", "");
    assert_ne!(without, doc, "the fixture did not change docs/configuration.md");
    let problems = cli_alias_problems(&without);
    assert_eq!(problems.len(), 1, "{problems:#?}");
    assert!(problems[0].contains("-dumptrace"), "{problems:#?}");
}
