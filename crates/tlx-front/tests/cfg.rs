//! Tests for the TLC model-config (`.cfg`) parser.

use std::path::{Path, PathBuf};

use tlx_front::cfg::{parse_cfg, CfgValue, Config, ConstBinding};
use tlx_front::Diagnostic;

fn ok(src: &str) -> Config {
    match parse_cfg(src) {
        Ok(cfg) => cfg,
        Err(diags) => panic!("unexpected errors: {}", render(&diags)),
    }
}

fn err(src: &str) -> Vec<Diagnostic> {
    match parse_cfg(src) {
        Ok(cfg) => panic!("expected an error, got {cfg:?}"),
        Err(diags) => diags,
    }
}

fn render(diags: &[Diagnostic]) -> String {
    diags.iter().map(|d| d.to_string()).collect::<Vec<_>>().join("; ")
}

fn val(name: &str, value: CfgValue) -> ConstBinding {
    ConstBinding::Value { name: name.to_string(), value, module: None }
}

fn subst(name: &str, op: &str, module: Option<&str>) -> ConstBinding {
    ConstBinding::Subst { name: name.to_string(), op: op.to_string(), module: module.map(str::to_string) }
}

fn mv(s: &str) -> CfgValue {
    CfgValue::ModelValue(s.to_string())
}

fn strs(v: &[&str]) -> Vec<String> {
    v.iter().map(|s| s.to_string()).collect()
}

// ---------------------------------------------------------------------------
// Keywords
// ---------------------------------------------------------------------------

#[test]
fn empty_file() {
    assert_eq!(ok(""), Config::default());
    assert_eq!(ok("  \n\t\n"), Config::default());
    assert_eq!(ok("\\* only a comment"), Config::default());
}

#[test]
fn single_name_keywords() {
    let cfg = ok("INIT Init\nNEXT Next\nSYMMETRY Perms\nVIEW vw\nALIAS Al\nPOSTCONDITION Post\n");
    assert_eq!(cfg.init.as_deref(), Some("Init"));
    assert_eq!(cfg.next.as_deref(), Some("Next"));
    assert_eq!(cfg.symmetry.as_deref(), Some("Perms"));
    assert_eq!(cfg.view.as_deref(), Some("vw"));
    assert_eq!(cfg.alias.as_deref(), Some("Al"));
    assert_eq!(cfg.postconditions, strs(&["Post"]));
    assert_eq!(cfg.specification, None);

    let cfg = ok("SPECIFICATION Spec");
    assert_eq!(cfg.specification.as_deref(), Some("Spec"));
    let cfg = ok("POSTCONDITIONS Post");
    assert_eq!(cfg.postconditions, strs(&["Post"]));
}

#[test]
fn several_postconditions() {
    // (TLC checks them in order: tests/specs/TSFPost1.)
    let cfg = ok("POSTCONDITIONS Post1 Post2\nPOSTCONDITION Post3\n");
    assert_eq!(cfg.postconditions, strs(&["Post1", "Post2", "Post3"]));
}

#[test]
fn name_on_following_line() {
    let cfg = ok("SPECIFICATION\n    Spec\nINVARIANT\n  TypeOK\n  Safety\n");
    assert_eq!(cfg.specification.as_deref(), Some("Spec"));
    assert_eq!(cfg.invariants, strs(&["TypeOK", "Safety"]));
}

#[test]
fn list_keywords_singular_and_plural() {
    let cfg = ok("INVARIANT A B\nINVARIANTS C\nPROPERTY P1\nPROPERTIES P2 P3\n\
                  CONSTRAINT C1\nCONSTRAINTS C2 C3\nACTION_CONSTRAINT A1\nACTION_CONSTRAINTS A2\n");
    assert_eq!(cfg.invariants, strs(&["A", "B", "C"]));
    assert_eq!(cfg.properties, strs(&["P1", "P2", "P3"]));
    assert_eq!(cfg.constraints, strs(&["C1", "C2", "C3"]));
    assert_eq!(cfg.action_constraints, strs(&["A1", "A2"]));
}

#[test]
fn empty_list_section() {
    let cfg = ok("INVARIANT\nPROPERTY\nINIT I");
    assert!(cfg.invariants.is_empty());
    assert!(cfg.properties.is_empty());
    assert_eq!(cfg.init.as_deref(), Some("I"));
}

#[test]
fn check_deadlock() {
    assert_eq!(ok("CHECK_DEADLOCK FALSE").check_deadlock, Some(false));
    assert_eq!(ok("CHECK_DEADLOCK TRUE").check_deadlock, Some(true));
    assert_eq!(ok("INIT I").check_deadlock, None);
}

#[test]
fn internal_tlc_keywords() {
    let cfg = ok("_PERIODIC Per\n_RL_REWARD Rew\n_POSSIBLE A B\nINIT I\n_POSSIBLE C");
    assert_eq!(cfg.init.as_deref(), Some("I"));
    assert_eq!(cfg.possible, strs(&["A", "B", "C"]));
}

#[test]
fn operator_constant_values() {
    // TLC's ConstantOperatorConfiguration: F is given at some arguments.
    let cfg = ok("CONSTANT\n  F(0) = 1\n  F(1, \"a\") = {2}\n  G(_, _) <- H\n");
    assert_eq!(
        cfg.constants,
        vec![
            ConstBinding::OpValue { name: "F".into(), args: vec![CfgValue::Int(0)], value: CfgValue::Int(1) },
            ConstBinding::OpValue {
                name: "F".into(),
                args: vec![CfgValue::Int(1), CfgValue::Str("a".into())],
                value: CfgValue::Set(vec![CfgValue::Int(2)])
            },
            subst("G", "H", None),
        ]
    );
}

#[test]
fn operator_symbols_in_substitutions() {
    // TLC's test30: infix operators on both sides of `<-`, by their
    // canonical names (`(+)` would be `\oplus`; `\circ` is `\o`).
    let cfg = ok("CONSTANT\n  ++ <- PlusPlus\n  Plus <- +\n  \\o <- +\n  \\circ <- \\X\n  F <- (+)\n  -- <- [M] -\nINIT I");
    assert_eq!(
        cfg.constants,
        vec![
            subst("++", "PlusPlus", None),
            subst("Plus", "+", None),
            subst("\\o", "+", None),
            subst("\\o", "\\X", None),
            subst("F", "\\oplus", None),
            subst("--", "-", Some("M")),
        ]
    );
    assert_eq!(cfg.init.as_deref(), Some("I"));
    // Punctuation stays punctuation.
    assert_eq!(
        ok("CONSTANT N=-1 S={<<1, 2>>}").constants,
        vec![val("N", CfgValue::Int(-1)), val("S", CfgValue::Set(vec![CfgValue::Tuple(vec![CfgValue::Int(1), CfgValue::Int(2)])]))]
    );
}

#[test]
fn config_section_of_a_tla_file() {
    use tlx_front::cfg::config_section;
    let src = "---- MODULE M ----\nVARIABLE x\n====\n---- CONFIG Other ----\nINIT J\n====\n------- CONFIG M -----\nINIT I\n\\* trailing comment\n=====\nNEXT N\n";
    assert_eq!(config_section(src, "M"), "INIT I\n\\* trailing comment");
    assert_eq!(ok(&config_section(src, "M")).init.as_deref(), Some("I"));
    assert_eq!(config_section(src, "Other"), "INIT J");
    // No section (or a marker with more on its line): an empty configuration.
    assert_eq!(config_section(src, "N"), "");
    assert_eq!(config_section("---- CONFIG M ---- x\nINIT I\n", "M"), "");
}

#[test]
fn sections_on_one_line() {
    let cfg = ok("INIT Init NEXT Next INVARIANT Inv CONSTANT N = 3 CHECK_DEADLOCK FALSE");
    assert_eq!(cfg.init.as_deref(), Some("Init"));
    assert_eq!(cfg.next.as_deref(), Some("Next"));
    assert_eq!(cfg.invariants, strs(&["Inv"]));
    assert_eq!(cfg.constants, vec![val("N", CfgValue::Int(3))]);
    assert_eq!(cfg.check_deadlock, Some(false));
}

// ---------------------------------------------------------------------------
// Constant bindings
// ---------------------------------------------------------------------------

#[test]
fn constant_values() {
    let cfg = ok(r#"
CONSTANTS
    N = 3
    M = -1
    Big = 9223372036854775807
    S = {a, b, "x", 1, {2}}
    a = a
    Name = "hello"
    Esc = "q\"b\\s\n\t"
    T = TRUE
    F = FALSE
    Empty = {}
    Tup = <<1, "two", <<>>, {c}>>
"#);
    assert_eq!(
        cfg.constants,
        vec![
            val("N", CfgValue::Int(3)),
            val("M", CfgValue::Int(-1)),
            val("Big", CfgValue::Int(i64::MAX)),
            val(
                "S",
                CfgValue::Set(vec![mv("a"), mv("b"), CfgValue::Str("x".into()), CfgValue::Int(1), CfgValue::Set(vec![CfgValue::Int(2)]),])
            ),
            val("a", mv("a")),
            val("Name", CfgValue::Str("hello".into())),
            val("Esc", CfgValue::Str("q\"b\\s\n\t".into())),
            val("T", CfgValue::Bool(true)),
            val("F", CfgValue::Bool(false)),
            val("Empty", CfgValue::Set(vec![])),
            val(
                "Tup",
                CfgValue::Tuple(
                    vec![CfgValue::Int(1), CfgValue::Str("two".into()), CfgValue::Tuple(vec![]), CfgValue::Set(vec![mv("c")]),]
                )
            ),
        ]
    );
}

#[test]
fn constant_keyword_singular_and_repeated() {
    let cfg = ok("CONSTANT N = 1\nINIT I\nCONSTANTS M = 2 K = 3");
    assert_eq!(cfg.constants, vec![val("N", CfgValue::Int(1)), val("M", CfgValue::Int(2)), val("K", CfgValue::Int(3))]);
}

#[test]
fn substitutions() {
    let cfg = ok("CONSTANTS\n  F <- G\n  Ballot <-[Voting] MCBallot\n  Nat <- [ZSequences]ZSeqNat\n  Op(_, _) <- MCOp\n");
    assert_eq!(
        cfg.constants,
        vec![
            subst("F", "G", None),
            subst("Ballot", "MCBallot", Some("Voting")),
            subst("Nat", "ZSeqNat", Some("ZSequences")),
            subst("Op", "MCOp", None),
        ]
    );
}

#[test]
fn module_scoped_value() {
    let cfg = ok("CONSTANTS\n  NoHash = [Nano]NoHashVal\n");
    assert_eq!(
        cfg.constants,
        vec![ConstBinding::Value { name: "NoHash".to_string(), value: mv("NoHashVal"), module: Some("Nano".to_string()) }]
    );
}

#[test]
fn bang_qualified_lhs() {
    let cfg = ok("CONSTANT A!B!c = 1");
    assert_eq!(cfg.constants, vec![val("A!B!c", CfgValue::Int(1))]);
}

#[test]
fn mixed_bindings_without_newlines() {
    let cfg = ok("CONSTANTS a = a b = b F <- G S = {a, b}");
    assert_eq!(
        cfg.constants,
        vec![val("a", mv("a")), val("b", mv("b")), subst("F", "G", None), val("S", CfgValue::Set(vec![mv("a"), mv("b")])),]
    );
}

// ---------------------------------------------------------------------------
// Comments, BOM
// ---------------------------------------------------------------------------

#[test]
fn comments() {
    let cfg = ok(r#"
(***************************************************************************)
(* Header comment (* with a nested (* comment *) inside *)                 *)
(***************************************************************************)
\* line comment
INIT Init \* trailing comment
NEXT (* inline *) Next
CONSTANTS
    N = (* between *) 3 \* the bound
    S = {a, (* x *) b}
INVARIANT Inv (* multi
line
comment *) Inv2
"#);
    assert_eq!(cfg.init.as_deref(), Some("Init"));
    assert_eq!(cfg.next.as_deref(), Some("Next"));
    assert_eq!(cfg.constants, vec![val("N", CfgValue::Int(3)), val("S", CfgValue::Set(vec![mv("a"), mv("b")]))]);
    assert_eq!(cfg.invariants, strs(&["Inv", "Inv2"]));
}

#[test]
fn comment_at_eof_without_newline() {
    assert_eq!(ok("INIT I \\* no newline").init.as_deref(), Some("I"));
}

#[test]
fn comment_markers_inside_strings() {
    let cfg = ok(r#"CONSTANT S = "(* not a comment *) \\* nor this""#);
    assert_eq!(cfg.constants, vec![val("S", CfgValue::Str("(* not a comment *) \\* nor this".into()))]);
}

#[test]
fn leading_bom() {
    let cfg = ok("\u{feff}INIT Init\nNEXT Next");
    assert_eq!(cfg.init.as_deref(), Some("Init"));
    // Column numbers do not count the BOM.
    let diags = err("\u{feff}INIT 3");
    assert_eq!((diags[0].span.line, diags[0].span.col), (1, 6));
    assert_eq!(diags[0].span.start, 8);
}

#[test]
fn crlf_line_endings() {
    let cfg = ok("INIT Init\r\nNEXT Next\r\nCONSTANT N = 2\r\n");
    assert_eq!(cfg.next.as_deref(), Some("Next"));
    assert_eq!(cfg.constants, vec![val("N", CfgValue::Int(2))]);
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

fn single_err(src: &str) -> (u32, u32, String) {
    let diags = err(src);
    assert_eq!(diags.len(), 1, "expected exactly one error, got: {}", render(&diags));
    (diags[0].span.line, diags[0].span.col, diags[0].message.clone())
}

#[test]
fn error_not_a_keyword() {
    let (line, col, msg) = single_err("INIT Init\nFOO Bar\n");
    assert_eq!((line, col), (2, 1));
    assert!(msg.contains("expected a keyword") && msg.contains("`FOO`"), "{msg}");
}

#[test]
fn error_missing_name() {
    let (line, col, msg) = single_err("INIT\nNEXT Next");
    assert_eq!((line, col), (2, 1));
    assert!(msg.contains("expected a name after INIT") && msg.contains("keyword `NEXT`"), "{msg}");

    let (_, _, msg) = single_err("SPECIFICATION");
    assert!(msg.contains("end of file"), "{msg}");
}

#[test]
fn error_keyword_twice() {
    let (line, col, msg) = single_err("INIT A\nNEXT N\nINIT B");
    assert_eq!((line, col), (3, 1));
    assert!(msg.contains("INIT specified twice (first at 1:1)"), "{msg}");

    let (_, _, msg) = single_err("CHECK_DEADLOCK TRUE\nCHECK_DEADLOCK FALSE");
    assert!(msg.contains("CHECK_DEADLOCK specified twice"), "{msg}");
}

#[test]
fn error_single_takes_one_name() {
    let (line, col, msg) = single_err("INIT A B");
    assert_eq!((line, col), (1, 8));
    assert!(msg.contains("INIT takes a single name"), "{msg}");
}

#[test]
fn error_check_deadlock_value() {
    let (line, col, msg) = single_err("CHECK_DEADLOCK maybe");
    assert_eq!((line, col), (1, 16));
    assert!(msg.contains("expected TRUE or FALSE"), "{msg}");
}

#[test]
fn error_comma_in_name_list() {
    let (_, col, msg) = single_err("INVARIANT A, B");
    assert_eq!(col, 12);
    assert!(msg.contains("names are separated by whitespace"), "{msg}");
}

#[test]
fn error_bad_bindings() {
    let (line, col, msg) = single_err("CONSTANTS\n  N 3");
    assert_eq!((line, col), (2, 5));
    assert!(msg.contains("expected `=` or `<-` after `N`"), "{msg}");

    let (_, _, msg) = single_err("CONSTANT N =");
    assert!(msg.contains("expected a value, found end of file"), "{msg}");

    let (_, _, msg) = single_err("CONSTANT N =\nINIT I");
    assert!(msg.contains("expected a value, found keyword `INIT`"), "{msg}");

    let (_, _, msg) = single_err("CONSTANT S = {a, b");
    assert!(msg.contains("expected `}` or `,` in set"), "{msg}");

    let (_, _, msg) = single_err("CONSTANT S = {a, }");
    assert!(msg.contains("expected a value, found `}`"), "{msg}");

    let (_, _, msg) = single_err("CONSTANT T = <<1, 2");
    assert!(msg.contains("expected `>>` or `,` in tuple"), "{msg}");

    let (_, _, msg) = single_err("CONSTANT F <- ");
    assert!(msg.contains("expected an operator name after `F <-`"), "{msg}");

    let (_, _, msg) = single_err("CONSTANT F <- [M G");
    assert!(msg.contains("expected `]`"), "{msg}");

    let (_, _, msg) = single_err("CONSTANT N = - x");
    assert!(msg.contains("expected a number after `-`"), "{msg}");

    let (_, _, msg) = single_err("CONSTANT N = 99999999999999999999");
    assert!(msg.contains("out of range"), "{msg}");

    let (_, _, msg) = single_err("CONSTANT F(_ <- G");
    assert!(msg.contains("expected `)`"), "{msg}");

    let (_, _, msg) = single_err("CONSTANT F(");
    assert!(msg.contains("unclosed `(`"), "{msg}");
}

#[test]
fn error_lexical() {
    let (line, col, msg) = single_err("INIT Init\nNEXT Next ` oops\n");
    assert_eq!((line, col), (2, 11));
    assert!(msg.contains("unexpected character"), "{msg}");

    let (line, col, msg) = single_err("CONSTANT S = \"abc\nINIT I");
    assert_eq!((line, col), (1, 14));
    assert!(msg.contains("unterminated string literal"), "{msg}");

    let (_, _, msg) = single_err("CONSTANT S = \"a\\qb\"");
    assert!(msg.contains("invalid escape sequence"), "{msg}");

    let (line, col, msg) = single_err("INIT I\n(* open (* nested *) \n");
    assert_eq!((line, col), (2, 1));
    assert!(msg.contains("unterminated block comment"), "{msg}");
}

#[test]
fn error_recovery_reports_multiple() {
    let diags = err("INIT 1\nNEXT Next\nCONSTANT N 3\nINVARIANT A, B\nVIEW v\n");
    let lines: Vec<u32> = diags.iter().map(|d| d.span.line).collect();
    assert_eq!(lines, vec![1, 3, 4], "{}", render(&diags));
}

#[test]
fn error_span_offsets() {
    let diags = err("INIT Init\nNEXT 42");
    assert_eq!(diags[0].span.start, 15);
    assert_eq!(diags[0].span.end, 17);
    assert_eq!(diags[0].to_string(), "2:6: expected a name after NEXT, found number `42`");
}

// ---------------------------------------------------------------------------
// Corpus: every .cfg in tlaplus/Examples
// ---------------------------------------------------------------------------

/// Files that are not valid TLC config syntax and are expected to fail.
/// (Paths relative to `specifications/`.)
const CORPUS_ALLOWLIST: &[&str] = &[];

fn collect_cfgs(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return;
    };
    for entry in entries.flatten() {
        let path = entry.path();
        if path.is_dir() {
            collect_cfgs(&path, out);
        } else if path.extension().is_some_and(|e| e == "cfg") {
            out.push(path);
        }
    }
}

#[test]
fn examples_corpus() {
    let Some(root) = tlx_testkit::require_third_party("examples_corpus", "Examples") else {
        return;
    };
    let specs = root.join("specifications");
    let mut files = Vec::new();
    collect_cfgs(&specs, &mut files);
    files.sort();
    assert!(!files.is_empty(), "no .cfg files found under {}", specs.display());

    let mut failures = Vec::new();
    let mut parsed = 0;
    for path in &files {
        let rel = path.strip_prefix(&specs).unwrap().to_string_lossy().replace('\\', "/");
        let allowed = CORPUS_ALLOWLIST.contains(&rel.as_str());
        let src = match std::fs::read_to_string(path) {
            Ok(s) => s,
            Err(e) => {
                failures.push(format!("{rel}: read error: {e}"));
                continue;
            }
        };
        match parse_cfg(&src) {
            Ok(_) if allowed => failures.push(format!("{rel}: allowlisted but now parses; remove it")),
            Ok(_) => parsed += 1,
            Err(_) if allowed => {}
            Err(diags) => {
                for d in diags {
                    failures.push(format!("{rel}:{d}"));
                }
            }
        }
    }
    eprintln!("parsed {parsed} of {} .cfg files under {}", files.len(), specs.display());
    assert!(failures.is_empty(), "{} failure(s):\n{}", failures.len(), failures.join("\n"));
}

#[test]
fn effective_constant_last_wins_and_subst_precedence() {
    use tlx_front::cfg::EffectiveConst;

    let cfg = ok("
        CONSTANT Delay = 0
        CONSTANT Delay = 2
        CONSTANT S = {a, b}
        CONSTANT S = {}
        CONSTANT Op <- First
        CONSTANT Op <- Second
        CONSTANT Both <- SubstTarget
        CONSTANT Both = 99
        CONSTANT M = [Mod] 7
        CONSTANT Tbl = 1
        CONSTANT Tbl(1) = 2
    ");

    assert_eq!(cfg.last_constant_value("Delay"), Some(&CfgValue::Int(2)));
    assert_eq!(cfg.last_constant_subst("Delay"), None);

    assert_eq!(cfg.last_constant_value("S"), Some(&CfgValue::Set(vec![])));

    assert_eq!(cfg.effective_constant("Op"), Some(EffectiveConst::Subst("Second")));
    assert_eq!(cfg.last_constant_subst("Op"), Some("Second"));
    assert_eq!(cfg.last_constant_value("Op"), None);

    // Subst applies after Value in TLC / bind_cfg regardless of file order.
    assert_eq!(cfg.effective_constant("Both"), Some(EffectiveConst::Subst("SubstTarget")));
    assert_eq!(cfg.last_constant_value("Both"), None);
    assert_eq!(cfg.last_constant_subst("Both"), Some("SubstTarget"));

    // Module-scoped bindings do not bind unqualified constants.
    assert_eq!(cfg.effective_constant("M"), None);

    // An OpValue table overwrites an earlier Value.
    assert_eq!(cfg.effective_constant("Tbl"), None);
}
