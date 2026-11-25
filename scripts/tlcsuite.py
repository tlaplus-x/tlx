#!/usr/bin/env python3
"""TLC's own regression suite (tlaplus/tlaplus, tlatools test-model and its JUnit
model-checker tests) run against tlx.

usage: scripts/tlcsuite.py [--filter SUBSTR] [--ids NAME,...] [-j N] [--timeout S]
                           [--tlc-jobs N] [--oracle-timeout S] [--refresh-oracle]
                           [--release | --profile P] [--extra=ARGS] [--update-expected]
                           [--list] [-v]

The suite is fetched at the commit pinned in corpus/external.json ("suites",
third_party/external/tlaplus-tests, scripts/fetch-external.py). The cases are
the model-checker tests of its JUnit sources (ModelCheckerTestCase,
PCalModelCheckerTestCase, SuiteTestCase, SuiteETestCase): spec, command-line
arguments, whether deadlock checking is on. Their expectations (exit status,
state counts) are not used as the oracle; TLC itself is: each case is run with
TLC (`-workers 1`; cached in corpus/out/tlcsuite.json) and tlx's result is
compared by contract tiers 1 and 2 (docs/compat.md section 0), as difftest does:
result kind (every error is just "error"), the violated invariant/property name,
and for a successful run distinct/generated states and depth. Simulation cases
(-simulate/-generate) only compare the result kind. The JUnit expectations are
only cross-checked (a count of disagreements with the TLC run is printed: it
measures this script's extraction, not tlx).

Preparation, as the JUnit harness does it: `-deadlock` unless the test checks
deadlock; PlusCal tests are translated first with `pcal.trans` (with the test's
own arguments, in a private copy of the test directory: this only prepares the
input of both checkers); `-lncheck` is dropped; a `-config X.tla` (the config
is a `---- CONFIG name ----` section of the module) becomes a cfg file. Tests
that are @Ignore'd or take non-literal arguments are skipped.

Results: every case prints PASS, XFAIL (differs, listed in
tests/tlcsuite_expected_failures.json), FIXED (listed, but passes now: remove
the entry; always a failure), or FAIL (unexpected). Exit status 1 when
any FAIL, FIXED, execution error or missing oracle, or zero selected cases. --update-expected rewrites the expected-failures file from the
current results: entries that still match a failure are kept (with their
reasons), entries that match nothing are dropped, other failures get a new
entry with a reason derived from the difference (edit it afterwards).

  --filter S / --ids ...  cases whose name contains S / exactly these names
  -j N                    tlx runs in parallel (default 3); --tlc-jobs N: TLC runs (default 2)
  --timeout S             per tlx run (default 60); --oracle-timeout S: per TLC run (default 120);
                          a case whose TLC run times out stays selected with missing evidence (a failure);
                          a larger budget retries an earlier timeout
  --refresh-oracle        run TLC again for the selected cases
  --list                  print the cases and exit
  --extra=ARGS            extra tlx arguments, e.g. --extra=-compile
"""
import argparse, fnmatch, hashlib, importlib.util, json, os, re, shutil, subprocess, sys, threading, time
from concurrent.futures import ThreadPoolExecutor

from contract import compare as compare_contract
from tlxlib import CaseResult, add_result_args, finish_cases, case_summary, judge_case, expected_match, ROOT, TP, add_profile_args, build_tlx, json_update, profile_of, run_proc, parity_args, parity_env, tlx_env
from tlc import JAVA, CLASSPATH, JVM_OPTS, parse, run_tlc_raw

SUITE = "tlaplus-tests"
MANIFEST = os.path.join(ROOT, "corpus", "external.json")
EXPECTED = os.path.join(ROOT, "tests", "tlcsuite_expected_failures.json")
ORACLE = os.path.join(ROOT, "corpus", "out", "tlcsuite.json")
RESULTS = os.path.join(ROOT, "corpus", "out", "tlcsuite-tlx.json")
WORKDIR = os.path.join(ROOT, "target", "tlcsuite")
# (tlapm/library is not passed: its Bags.tla would shadow the standard Bags.)
INCLUDES = [a for d in ("community", "apalache") for a in ("-I", os.path.join(TP, d))]
TEST_BASES = ("ModelCheckerTestCase", "PCalModelCheckerTestCase", "SuiteTestCase", "SuiteETestCase")
# Command-line options of TLC's tools that tlx does not have (docs/compat.md section 2).
OUT_OF_CONTRACT = ("-continue", "-dfid", "-maxSetSize", "-invlevel", "-view")
SIMULATION = ("-simulate", "-generate")

JUNIT_EXIT = {"SUCCESS": 0, "VIOLATION_ASSUMPTION": 10, "VIOLATION_DEADLOCK": 11, "VIOLATION_SAFETY": 12, "VIOLATION_LIVENESS": 13,
              "VIOLATION_ASSERT": 14, "FAILURE_SPEC_EVAL": 75, "FAILURE_SAFETY_EVAL": 76, "FAILURE_LIVENESS_EVAL": 77,
              "ERROR_SPEC_PARSE": 150, "ERROR_CONFIG_PARSE": 151, "ERROR": 255}


def fetch_external():
    spec = importlib.util.spec_from_file_location("fetch_external", os.path.join(os.path.dirname(os.path.abspath(__file__)), "fetch-external.py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def suite_dir(fetch=True):
    """The unpacked suite (tlatools/org.lamport.tlatools of the pinned commit)."""
    fx = fetch_external()
    with open(MANIFEST) as source:
        spec = json.load(source)["suites"][SUITE]
    if fetch:
        os.makedirs(fx.DEST, exist_ok=True)
        fx.fetch_repo(SUITE, spec)
    return os.path.join(fx.DEST, SUITE), spec["commit"]


# ---- extracting the cases from the JUnit sources -------------------------------------------------

_JAVA_ESCAPES = {'"': '"', "\\": "\\", "'": "'", "n": "\n", "r": "\r", "t": "\t", "b": "\b", "f": "\f"}
_JAVA_SEPARATORS = frozenset({"File.separator", "FileUtil.separator", "java.io.File.separator"})
_JAVA_IDENT_RE = re.compile(r"[A-Za-z_$][\w$]*(?:\s*\.\s*[A-Za-z_$][\w$]*)*")
_JAVA_NEW_ARR_RE = re.compile(r"new\s+String\s*\[\s*\]\s*\{")
_JAVA_EXIT_RE = re.compile(r"((?:EC\.)?ExitStatus\.\w+|\d+)")
_JAVA_UNICODE_ESC_RE = re.compile(r"(?<!\\)(?:\\\\)*\\u+[0-9a-fA-F]{4}")


def _skip_java_ws(text, i):
    """Advance `i` past whitespace and `/* ... */` or `// ...` Java comments.
    Returns `(pos, ok)` where `ok=False` marks an unterminated block comment or
    a JLS §3.3 Unicode escape inside a comment whose token boundary is ambiguous."""
    n = len(text)
    while i < n:
        if text[i].isspace():
            i += 1
        elif text.startswith("/*", i):
            end = text.find("*/", i + 2)
            if end < 0 or _JAVA_UNICODE_ESC_RE.search(text[i + 2:end]):
                return n, False
            i = end + 2
        elif text.startswith("//", i):
            end = text.find("\n", i + 2)
            comment = text[i + 2:] if end < 0 else text[i + 2:end]
            if _JAVA_UNICODE_ESC_RE.search(comment):
                return n, False
            i = n if end < 0 else end + 1
        else:
            break
    return i, True


def _skip_java_quoted(text, i):
    """Advance `i` past a Java text block (`\"\"\"...\"\"\"`), string literal, or char
    literal. Returns `(pos, ok)`."""
    n = len(text)
    if text.startswith('"""', i):
        j = i + 3
        while j < n and text[j] in " \t\f":
            j += 1
        if j < n and text[j] in "\r\n":
            j += 2 if text.startswith("\r\n", j) else 1
            while j < n:
                if text[j] == "\\":
                    j += 2
                elif text.startswith('"""', j):
                    q = 3
                    while j + q < n and text[j + q] == '"' and q < 5:
                        q += 1
                    return j + q, True
                else:
                    j += 1
            return n, False
    quote = text[i]
    j = i + 1
    while j < n and text[j] != quote:
        if text[j] in "\r\n":
            return n, False
        j += 2 if text[j] == "\\" else 1
    if j >= n:
        return n, False
    return j + 1, True


def _scan_java_string_expr(text, i):
    """Scan one `+`-concatenated Java string literal / `File.separator` expression,
    stopping before a top-level `,`, `)`, or `}`. Returns `(val, ok, pos)`."""
    n = len(text)
    buf = []
    ok_lit = True
    has_val = expect_plus = False
    brace_depth = paren_depth = 0
    while i < n:
        i, ok = _skip_java_ws(text, i)
        if not ok or i >= n:
            return "", False, n
        ch = text[i]
        if ch in ",)}" and brace_depth == 0 and paren_depth == 0:
            break
        if ch == "{":
            ok_lit = False
            brace_depth += 1
            i += 1
        elif ch == "}":
            brace_depth -= 1
            i += 1
        elif ch == "(":
            ok_lit = False
            paren_depth += 1
            i += 1
        elif ch == ")":
            paren_depth -= 1
            i += 1
        elif ch == '"':
            if text.startswith('"""', i):
                j, ok = _skip_java_quoted(text, i)
                if not ok:
                    return "", False, n
                ok_lit = False
                i = j
                continue
            j = i + 1
            lit = []
            while j < n and text[j] != '"':
                if text[j] in "\r\n":
                    return "", False, n
                if text[j] == "\\":
                    j += 1
                    if j >= n or text[j] in "\r\n":
                        return "", False, n
                    esc = _JAVA_ESCAPES.get(text[j])
                    if esc is None:
                        ok_lit = False
                    else:
                        lit.append(esc)
                else:
                    lit.append(text[j])
                j += 1
            if j >= n:
                return "", False, n
            if brace_depth == 0 and paren_depth == 0:
                if expect_plus:
                    ok_lit = False
                buf.append("".join(lit))
                has_val = expect_plus = True
            i = j + 1
        elif ch == "'":
            ok_lit = False
            i, ok = _skip_java_quoted(text, i)
            if not ok:
                return "", False, n
        elif ch == "+" and brace_depth == 0 and paren_depth == 0:
            if not expect_plus:
                ok_lit = False
            expect_plus = False
            i += 1
        else:
            m = _JAVA_IDENT_RE.match(text, i)
            if m:
                ident = re.sub(r"\s+", "", m.group(0))
                nxt, ok = _skip_java_ws(text, m.end())
                if not ok:
                    return "", False, n
                if brace_depth == 0 and paren_depth == 0 and not expect_plus and ident in _JAVA_SEPARATORS and (nxt >= n or text[nxt] != "("):
                    buf.append("/")
                    has_val = expect_plus = True
                else:
                    ok_lit = False
                i = m.end()
            else:
                ok_lit = False
                i += 1
    if not has_val or not expect_plus or not ok_lit:
        return "", False, i
    return "".join(buf), True, i


def scan_java_string_array(text, i):
    """Scan a `new String[] { ... }` initializer starting just after `{`.

    Consumes quoted string literals and Java escapes, skips comments only between
    tokens, folds `+` concatenations of string literals and `File.separator` /
    `FileUtil.separator`, and stops at the matching unquoted `}`. Any unsupported
    escape or non-literal expression sets `nonlit=True`. Returns `(args, nonlit, pos)`.
    """
    n = len(text)
    args = []
    nonlit = False
    while i < n:
        i, ok = _skip_java_ws(text, i)
        if not ok or i >= n:
            return [], True, n
        if text[i] == "}":
            return ([] if nonlit else args), nonlit, i + 1
        val, ok_elem, i = _scan_java_string_expr(text, i)
        if not ok_elem:
            nonlit = True
        elif not nonlit:
            args.append(val)
        i, ok = _skip_java_ws(text, i)
        if not ok or i >= n:
            return [], True, n
        if text[i] == ",":
            i += 1
        elif text[i] != "}":
            return [], True, n
    return [], True, n


def parse_java_args(raw):
    """Extract literal CLI arguments from the body of a `new String[] { ... }` initializer."""
    if not raw:
        return [], False
    args, nonlit, pos = scan_java_string_array(raw + "}", 0)
    if pos != len(raw) + 1:
        return [], True
    return args, nonlit


def _starts_string_expr(text, i):
    if i < len(text) and text[i] == '"':
        return True
    m = _JAVA_IDENT_RE.match(text, i)
    return bool(m and re.sub(r"\s+", "", m.group(0)) in _JAVA_SEPARATORS)


def _next_java_ident(text, i):
    """Read an identifier starting at `i` (after skipping ws/comments). Returns `(ident, end, ok)`."""
    i, ok = _skip_java_ws(text, i)
    if not ok or i >= len(text) or not (text[i].isalpha() or text[i] in "_$"):
        return None, i, ok
    j = i + 1
    while j < len(text) and (text[j].isalnum() or text[j] in "_$"):
        j += 1
    return text[i:j], j, True


def _find_class_super_call(text, cls, body_start):
    """Locate `super(` inside a constructor of `cls` starting right after the
    class body's opening `{`. Skips comments, strings, text blocks, nested
    classes, and methods outside `cls`'s constructors. Returns `(pos, ok)` where
    `pos` is immediately after `(` (or `None` if no constructor calls `super(`)
    and `ok=False` if lexical ambiguity (e.g. a comment Unicode escape) occurred."""
    n = len(text)
    i = body_start
    depth = 1
    in_ctor = False
    ctor_depth = 0
    while i < n and depth > 0:
        i, ok = _skip_java_ws(text, i)
        if not ok or i >= n:
            return None, ok
        ch = text[i]
        if ch in ('"', "'"):
            i, ok = _skip_java_quoted(text, i)
            if not ok:
                return None, False
        elif ch == "{":
            depth += 1
            i += 1
        elif ch == "}":
            depth -= 1
            if in_ctor and depth < ctor_depth:
                in_ctor = False
            i += 1
        elif ch.isalpha() or ch in "_$":
            j = i + 1
            while j < n and (text[j].isalnum() or text[j] in "_$"):
                j += 1
            ident = text[i:j]
            if depth == 1 and ident == cls:
                k, ok = _skip_java_ws(text, j)
                if not ok:
                    return None, False
                if k < n and text[k] == "(":
                    # Advance past parameter list `(...)` and optional `throws ...` to `{`.
                    pdepth = 1
                    k += 1
                    while k < n and pdepth > 0:
                        k, ok = _skip_java_ws(text, k)
                        if not ok or k >= n:
                            return None, False
                        if text[k] in ('"', "'"):
                            k, ok = _skip_java_quoted(text, k)
                            if not ok:
                                return None, False
                        elif text[k] == "(":
                            pdepth += 1
                            k += 1
                        elif text[k] == ")":
                            pdepth -= 1
                            k += 1
                        else:
                            k += 1
                    while k < n:
                        k, ok = _skip_java_ws(text, k)
                        if not ok or k >= n:
                            return None, False
                        if text[k] == "{":
                            depth += 1
                            in_ctor = True
                            ctor_depth = depth
                            i = k + 1
                            break
                        if text[k] == ";":
                            i = k + 1
                            break
                        if text[k] in ('"', "'"):
                            k, ok = _skip_java_quoted(text, k)
                            if not ok:
                                return None, False
                        else:
                            k += 1
                    else:
                        return None, False
                    continue
            elif in_ctor and depth == ctor_depth and ident == "super":
                k, ok = _skip_java_ws(text, j)
                if not ok:
                    return None, False
                if k < n and text[k] == "(":
                    return k + 1, True
            i = j
        else:
            i += 1
    return None, True


def _find_test_class(text):
    """Find `class <cls> extends <base> ... {` outside comments and literals.
    Returns `(cls, base, body_start)` or `None`."""
    n = len(text)
    i = 0
    while i < n:
        i, ok = _skip_java_ws(text, i)
        if not ok or i >= n:
            return None
        ch = text[i]
        if ch in ('"', "'"):
            i, ok = _skip_java_quoted(text, i)
            if not ok:
                return None
        elif ch.isalpha() or ch in "_$":
            j = i + 1
            while j < n and (text[j].isalnum() or text[j] in "_$"):
                j += 1
            if text[i:j] == "class":
                cls, k, ok = _next_java_ident(text, j)
                if not ok or not cls:
                    i = j
                    continue
                ext, k2, ok = _next_java_ident(text, k)
                if ok and ext == "extends":
                    base, k3, ok = _next_java_ident(text, k2)
                    if ok and base in TEST_BASES:
                        while k3 < n:
                            k3, ok = _skip_java_ws(text, k3)
                            if not ok or k3 >= n:
                                return None
                            if text[k3] == "{":
                                return cls, base, k3 + 1
                            if text[k3] in ('"', "'"):
                                k3, ok = _skip_java_quoted(text, k3)
                                if not ok:
                                    return None
                            else:
                                k3 += 1
            i = j
        else:
            i += 1
    return None


def _is_java_int_str(val):
    return val.isdigit() or (val.startswith("-") and len(val) > 1 and val[1:].isdigit())


def _parse_suite_super_call(text, start, base):
    """Parse `SuiteTestCase`/`SuiteETestCase` `super(...)` arguments at `start`.
    Returns `(args, stats, exit_str, ok)` where `ok=False` marks an unsupported
    or non-literal `super(...)` call (distinct from a genuine `super()` default)."""
    i, ok = _skip_java_ws(text, start)
    if not ok or i >= len(text):
        return [], None, None, False
    if text[i] == ")":
        return [], None, None, True
    if base == "SuiteETestCase":
        args = []
        arr = _JAVA_NEW_ARR_RE.match(text, i)
        if arr:
            args, arr_nonlit, i = scan_java_string_array(text, arr.end())
            if arr_nonlit:
                return [], None, None, False
            i, ok = _skip_java_ws(text, i)
            if not ok or i >= len(text):
                return [], None, None, False
            if text[i] == ")":
                return args, None, None, True
            if text[i] != ",":
                return [], None, None, False
            i, ok = _skip_java_ws(text, i + 1)
            if not ok or i >= len(text):
                return [], None, None, False
        m_ex = _JAVA_EXIT_RE.match(text, i)
        if not m_ex:
            return [], None, None, False
        j, ok = _skip_java_ws(text, m_ex.end())
        if ok and j < len(text) and text[j] == ")":
            return args, None, m_ex.group(1), True
        return [], None, None, False
    vals = []
    for idx in range(5):
        val, ok_s, i = _scan_java_string_expr(text, i)
        if not ok_s:
            return [], None, None, False
        if idx < 4 and not _is_java_int_str(val):
            return [], None, None, False
        vals.append(val)
        i, ok = _skip_java_ws(text, i)
        if not ok or i >= len(text):
            return [], None, None, False
        if text[i] == ")":
            if len(vals) < 3:
                return [], None, None, False
            stats = [vals[:3]] if all(v.isdigit() for v in vals[:3]) else None
            return [], stats, None, True
        if idx == 4 or text[i] != ",":
            return [], None, None, False
        i, ok = _skip_java_ws(text, i + 1)
        if not ok or i >= len(text):
            return [], None, None, False
    return [], None, None, False


def _parse_super_call(text, start):
    """Parse `super(spec[, subdir][, new String[] { ... }][, ExitStatus])` at
    `start` and require the matching closing `)` so partial prefixes cannot run."""
    i, ok = _skip_java_ws(text, start)
    if not ok:
        return "", None, [], True, None
    if i >= len(text) or not _starts_string_expr(text, i):
        return None
    spec, spec_ok, i = _scan_java_string_expr(text, i)
    if not spec_ok:
        return "", None, [], True, None
    subdir, args, nonlit, ex = None, [], False, None
    i, ok = _skip_java_ws(text, i)
    if not ok:
        return spec, None, [], True, None
    if i < len(text) and text[i] == ",":
        i, ok = _skip_java_ws(text, i + 1)
        if not ok:
            nonlit = True
        if ok and i < len(text) and not _JAVA_NEW_ARR_RE.match(text, i) and not _JAVA_EXIT_RE.match(text, i):
            subdir, sub_ok, i = _scan_java_string_expr(text, i)
            if not sub_ok:
                nonlit = True
                subdir = ""
            i, ok = _skip_java_ws(text, i)
            if not ok:
                nonlit = True
            elif i < len(text) and text[i] == ",":
                i, ok = _skip_java_ws(text, i + 1)
                if not ok:
                    nonlit = True
        if ok and i < len(text):
            arr = _JAVA_NEW_ARR_RE.match(text, i)
            if arr:
                args, arr_nonlit, i = scan_java_string_array(text, arr.end())
                nonlit = nonlit or arr_nonlit
                i, ok = _skip_java_ws(text, i)
                if not ok:
                    nonlit = True
                elif i < len(text) and text[i] == ",":
                    i, ok = _skip_java_ws(text, i + 1)
                    m_ex = _JAVA_EXIT_RE.match(text, i) if ok else None
                    if m_ex:
                        ex = m_ex.group(1)
                        i = m_ex.end()
                    else:
                        nonlit = True
            elif text[i] != ")":
                m_ex = _JAVA_EXIT_RE.match(text, i)
                if m_ex:
                    ex = m_ex.group(1)
                    i = m_ex.end()
                else:
                    nonlit = True
    i, ok = _skip_java_ws(text, i)
    if not ok or i >= len(text) or text[i] != ")":
        nonlit = True
    if nonlit:
        args = []
    return spec, subdir, args, nonlit, ex


def _canon_exit(ex):
    return (ex or "SUCCESS").replace("EC.", "").replace("ExitStatus.", "")


def extract_cases(root):
    """The model-checker test cases of root/test/**/*.java: dicts with cls (the
    test class: the case's name), base, spec, path (below test-model), args,
    exit (JUnit's expected exit status), stats, deadlock (the test checks
    deadlock), ignored, nonlit, file."""
    out = []
    for base_dir, dirs, files in os.walk(os.path.join(root, "test")):
        dirs.sort()
        for name in sorted(files):
            if not name.endswith(".java"):
                continue
            path = os.path.join(base_dir, name)
            with open(path, errors="ignore") as source:
                text = source.read()
            found = _find_test_class(text)
            if not found:
                continue
            cls, base, body_start = found
            rel = os.path.relpath(path, root)
            super_start, scan_ok = _find_class_super_call(text, cls, body_start)
            if base in ("SuiteTestCase", "SuiteETestCase"):
                if not scan_ok:
                    args, st, ex, suite_ok = [], None, None, False
                elif super_start is not None:
                    args, st, ex, suite_ok = _parse_suite_super_call(text, super_start, base)
                else:
                    args, st, ex, suite_ok = [], None, None, True
                out.append(dict(cls=cls, base=base, spec=cls.lower(), path="suite", args=args, exit=_canon_exit(ex),
                                stats=st if st is not None else ([] if base == "SuiteETestCase" else [["2", "1", "0"]]),
                                deadlock=False, ignored="@Ignore" in text, nonlit=not suite_ok, file=rel))
                continue
            if not scan_ok:
                out.append(dict(cls=cls, base=base, spec="", path="", args=[], exit="SUCCESS", stats=[],
                                deadlock=False, ignored="@Ignore" in text, nonlit=True, file=rel))
                continue
            if super_start is None:
                continue
            parsed = _parse_super_call(text, super_start)
            if not parsed:
                continue
            spec, subdir, args, nonlit, ex = parsed
            stats = re.findall(r'EC\.TLC_STATS,\s*"([\d,]+)",\s*"([\d,]+)"(?:,\s*"([\d,]+)")?', text)
            deadlock = bool(re.search(r"checkDeadLock\(\)\s*\{\s*return\s+true", text))
            out.append(dict(cls=cls, base=base, spec=spec, path=subdir or "", args=args,
                            exit=_canon_exit(ex), stats=[list(s) for s in stats],
                            deadlock=deadlock, ignored="@Ignore" in text, nonlit=nonlit, file=rel))
    # (Test classes of different packages may share a name: qualified by the package then.)
    names = [c["cls"] for c in out]
    for c in out:
        if names.count(c["cls"]) > 1:
            c["cls"] = os.path.basename(os.path.dirname(c["file"])) + "." + c["cls"]
    return out


def prepare(case, tm, java_jar):
    """Make the case runnable in the working copy `tm` of test-model: the
    directory, the module file and the arguments both checkers get (the
    case's `skip` says why it is not run)."""
    d = os.path.join(tm, case["path"])
    spec = case["spec"] if case["spec"].endswith(".tla") else case["spec"] + ".tla"
    case = dict(case, dir=d, tla=spec, skip=None)
    if case["ignored"]:
        return dict(case, skip="ignored in the JUnit sources")
    if case["nonlit"]:
        return dict(case, skip="arguments are not literals")
    if not os.path.exists(os.path.join(d, spec)):
        return dict(case, skip="spec not found")
    args = list(case["args"])
    if case["base"] == "PCalModelCheckerTestCase":
        # Translated in a private copy of the directory (several tests translate one module with different options).
        private = os.path.join(tm, "_pcal", case["cls"])
        shutil.copytree(d, private)
        p = subprocess.run([JAVA, "-cp", java_jar, "pcal.trans", "-unixEOL", *args, spec], cwd=private, capture_output=True, text=True)
        if p.returncode != 0:
            return dict(case, skip="PlusCal translation failed")
        case["dir"], args = private, []
    if "-lncheck" in args:
        i = args.index("-lncheck")
        del args[i:i + 2]
    if "-config" in args and args[args.index("-config") + 1].endswith(".tla"):
        # The config is a `---- CONFIG name ----` section of the module.
        i = args.index("-config")
        with open(os.path.join(case["dir"], args[i + 1])) as source:
            section = re.search(r"^-{4,}\s*CONFIG\s+\w+\s*-{4,}\s*$(.*?)^={4,}", source.read(), re.M | re.S)
        if not section:
            return dict(case, skip="no CONFIG section")
        cfg = "_inline_" + case["cls"] + ".cfg"
        with open(os.path.join(case["dir"], cfg), "w") as out:
            out.write(section.group(1))
        args[i + 1] = cfg
    if not case["deadlock"]:
        args.append("-deadlock")
    return dict(case, run_args=args)


# ---- running and comparing -----------------------------------------------------------------------

def dependency_digest(root):
    """Conservative closure: all model/config/override inputs below the source root."""
    digest = hashlib.sha256()
    for base, dirs, files in os.walk(root):
        dirs.sort()
        for name in sorted(files):
            if name.endswith((".tla", ".cfg", ".class", ".jar", ".json")):
                path = os.path.join(base, name)
                digest.update(os.path.relpath(path, root).encode())
                with open(path, "rb") as source:
                    digest.update(source.read())
    return digest.hexdigest()


def tlc_identity():
    jars = {}
    for path in CLASSPATH.split(os.pathsep):
        if os.path.isfile(path):
            with open(path, "rb") as source:
                jars[os.path.basename(path)] = hashlib.sha256(source.read()).hexdigest()
        elif os.path.isdir(path):
            jars[os.path.basename(path)] = dependency_digest(path)
    version = run_proc([JAVA, "-version"])
    if version.returncode:
        raise RuntimeError("cannot identify TLC's Java runtime")
    return {"jars": jars, "java": version.stdout + version.stderr, "jvm_args": JVM_OPTS,
            "features": ["action composition"], "driver_version": 3}


def oracle_metadata(case, commit, identity, dependencies=None, inputs=None):
    return {"source_commit": commit, "input_digest": inputs or dependency_digest(case["dir"]),
            "dependency_digest": dependencies or dependency_digest(case["dir"]),
            "tlc_identity": identity, "args": ["-workers", "1", *case["run_args"]],
            "spec": case["tla"]}


def oracle_entry(metadata, result, timeout, case):
    complete = (result.get("result") not in (None, "unknown", "timeout", "collection error")
                and result.get("exit", 0) >= 0
                and not (result.get("result") == "success" and result.get("exit", 0) != 0))
    return {"metadata": metadata, "completion": "complete" if complete else "incomplete",
            "timeout": timeout, "tlc": result if complete else None,
            "collection": None if complete else result,
            "junit_agrees": junit_agrees(case, result) if complete else None}


def oracle_ready(entry, metadata):
    return bool(entry and entry.get("metadata") == metadata and entry.get("completion") == "complete"
                and entry.get("tlc"))


def oracle_retry(entry, metadata, timeout):
    if not entry or entry.get("metadata") != metadata:
        return True
    if oracle_ready(entry, metadata):
        return False
    # Collection errors are retryable; a timeout at the same budget stays missing.
    return entry.get("collection", {}).get("result") != "timeout" or timeout > entry.get("timeout", 0)


def run_oracle(case, timeout):
    """TLC's result on the case (a dict as tlc.parse), or {"result": "timeout"}."""
    try:
        out, rc, wall = run_tlc_raw(os.path.join(case["dir"], case["tla"]), ["-workers", "1", *case["run_args"]], timeout,
                                    features=("action composition",))
    except subprocess.TimeoutExpired:
        return {"result": "timeout", "wall_s": timeout}
    # These are Java launcher failures, before TLC can evaluate the spec.
    # tlc.parse would otherwise treat their "Error:" as a semantic verdict.
    launcher = "\n".join(line for line in out.splitlines()
                         if not line.startswith(("Picked up ", "NOTE: Picked up ")))
    if launcher.lstrip().startswith(("Error: Could not find or load main class", "Error: Unable to initialize main class",
                               "Error: A JNI error has occurred", "Error: LinkageError occurred while loading main class",
                               "Error occurred during initialization of VM")):
        return {"result": "collection error", "exit": rc, "wall_s": wall, "error": out[-1500:]}
    r = parse(out, wall, rc)
    r["tail"] = "\n".join(out.strip().splitlines()[-4:])[-400:]
    return r


def run_tlx(binary, case, timeout, extra):
    args = parity_args(binary, [*case["run_args"], *extra])
    cmd = [binary, "check", case["tla"], *INCLUDES, "-workers", "1", *args]
    t0 = time.time()
    try:
        p = run_proc(cmd, timeout, cwd=case["dir"], env=tlx_env(classpath=True, extra=parity_env(args)), grace=5)
    except subprocess.TimeoutExpired:
        return {"result": "timeout", "wall_s": timeout}
    out = p.stdout + p.stderr
    r = parse(out, time.time() - t0, p.returncode)
    r["tail"] = "\n".join(out.strip().splitlines()[-4:])[-400:]
    if r["result"] in ("error", "unknown"):
        r["error"] = out[-1500:]
    return r


def compare(case, tlc, tlx):
    """Tier 1/2 differences, including deterministic failures."""
    return comparison(case, tlc, tlx).differs


def comparison(case, tlc, tlx):
    # These TLC regression specs call RandomSubset in Next (compat D-4).
    # An explicit policy avoids treating every EXTENDS Randomization as random.
    return compare_contract(tlc, tlx, simulation=any(f in case["run_args"] for f in SIMULATION),
                            random_choices=case.get("spec") in ("RandomSubsetNext", "RandomSubsetNextTuples"))


def describe(r):
    return f'{r.get("result")}/{r.get("distinct")}/{r.get("generated")}/{r.get("depth")}'


def junit_agrees(case, tlc):
    """Whether the JUnit expectations (exit status, state counts) agree with the TLC run (a check of the extraction)."""
    kind = tlc.get("result")
    if kind == "timeout":
        return None
    expected = JUNIT_EXIT.get(case["exit"])
    exit_ok = tlc.get("exit") == expected if expected is not None else None
    stats_ok = None
    if case["stats"] and kind == "success":
        g, d = (int(x.replace(",", "")) for x in case["stats"][0][:2])
        stats_ok = (tlc.get("generated"), tlc.get("distinct")) == (g, d)
    return exit_ok is not False and stats_ok is not False


# ---- expected failures ---------------------------------------------------------------------------

def load_expected(path=EXPECTED):
    if not os.path.exists(path):
        return []
    with open(path) as source:
        return json.load(source)["expected_failures"]


def match_expected(entries, case_id, kind, *, match_result=True, suite="tlcsuite"):
    """The expected-failure entry for a failing case (`kind`: tlx's result), if any.

    `suite` is the --suite name the caller (verify.py) passes; it selects which
    expected-failure suite the entries belong to (default: this driver's own).
    """
    return expected_match([{"suite": suite, **e} for e in entries], suite, case_id, kind,
                          match_result=match_result)


# Known gaps, for the reason of a new expected failure: (regex, reason), tried in order against
# "<case name> <arguments>\n<tlx's output>". Keep the reasons short and about the cause.
KNOWN_GAPS = [
    (r'TLCGet\("all(:named)?"\)', 'TLCGet("all") and TLCGet("all:named") are not implemented'),
    (r"-dumpTrace \S+ states|more than one input files", "TLC's -dumpTrace formats of state files (outside the contract)"),
    (r"`\\cdot` cannot be evaluated|action composition does not determine", "`\\cdot` action composition with context is not supported"),
    (r"Cannot find the next-state relation", "SPECIFICATION through an operator application or LET is not split into Init and Next"),
    (r"`\[\]` cannot be evaluated", "a temporal formula under an operator or LET in a PROPERTY/SPECIFICATION is not recognized"),
    (r"multiple POSTCONDITIONs|Parsing the configuration failed", "cfg syntax tlx rejects (several POSTCONDITIONs, odd characters)"),
    (r"implemented by TLC in Java", "TLCExt operator implemented in Java is not supported"),
    (r"non-enumerable|unbounded CHOOSE|Overflow when computing the number of elements", "TLC evaluates this ASSUME/bound lazily, tlx needs an enumerable set"),
    (r"stack overflow", "unbounded recursion: tlx aborts with a stack overflow, TLC reports it as an error"),
    (r"cannot read \S+: No such file", "-config name without the .cfg extension is not resolved"),
    (r"ENABLED evaluated without a current state", "ENABLED outside a state context is rejected"),
    (r"^PossibleFail", "_POSSIBLE cfg items are ignored (TLC fails when the predicate is never satisfied)"),
    (r"UserModuleOverride", "Java module overrides are not supported"),
    (r"^Github1389", "tlx does not finish within the time limit on this liveness model (TLC does)"),
]


def reason_for(case, tlc, tlx, diffs):
    """A short reason for a new expected failure, from what differs."""
    for opt in OUT_OF_CONTRACT:
        if opt in case["args"]:
            return f"TLC command-line option {opt} (outside the contract)"
    text = f'{case["cls"]} {" ".join(case["args"])}\n{tlx.get("error") or tlx.get("tail") or ""}'
    for pattern, reason in KNOWN_GAPS:
        if re.search(pattern, text, re.M):
            return reason
    if tlx.get("result") == "timeout":
        return f"tlx did not finish in time (TLC: {tlc.get('result')})"
    if diffs == ["result"]:
        text = f"TLC {tlc.get('result')}, tlx {tlx.get('result')}"
        side = tlx if tlx.get("result") == "error" else tlc
        lines = [l.strip() for l in (side.get("error") or "").splitlines() if l.strip().startswith("Error:")]
        if side.get("result") == "error" and lines:
            text += f" ({lines[0][:90]})"
        return text
    if diffs == ["violated"]:
        return f"the violated name differs (TLC {tlc.get('violated')}, tlx {tlx.get('violated')})"
    return "differs in " + ", ".join(diffs) + f" (TLC {describe(tlc)}, tlx {describe(tlx)})"


def write_expected(path, entries):
    note = ["Differences between tlx and TLC on TLC's own regression suite (scripts/tlcsuite.py), by case name",
            "(the JUnit test class). `id` may be a glob, `result` restricts an entry to failures where tlx reported",
            "that result kind, `flaky` entries may pass too (timeouts under load). Regenerate with",
            "`scripts/tlcsuite.py --update-expected` and edit the new reasons."]
    with open(path, "w") as out:
        json.dump({"_comment": note, "expected_failures": entries}, out, indent=1)
        out.write("\n")


# ---- main ----------------------------------------------------------------------------------------

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--filter", default="")
    ap.add_argument("--ids", default="")
    ap.add_argument("-j", "--jobs", dest="j", type=int, default=3)
    ap.add_argument("--tlc-jobs", type=int, default=2)
    ap.add_argument("--timeout", type=int, default=60)
    ap.add_argument("--oracle-timeout", type=int, default=120)
    ap.add_argument("--refresh-oracle", action="store_true")
    ap.add_argument("--update-expected", action="store_true")
    ap.add_argument("--list", action="store_true")
    ap.add_argument("--extra", default="", help="extra tlx arguments, e.g. '-compile'")
    ap.add_argument("-v", action="store_true", help="print the skipped cases and the tail of unexpected failures")
    add_result_args(ap)
    ap.add_argument("--no-build", action="store_true", help="reuse the selected profile binary built by the caller")
    add_profile_args(ap)
    a = ap.parse_args()

    root, commit = suite_dir()
    wanted = {i for i in a.ids.split(",") if i}
    cases = [c for c in extract_cases(root) if a.filter in c["cls"] and (not wanted or c["cls"] in wanted)]
    names = [c["cls"] for c in cases]
    if len(set(names)) != len(names):
        sys.exit("duplicate test class names: " + ", ".join(sorted({n for n in names if names.count(n) > 1})))
    if a.list:
        for c in cases:
            print(f'{c["cls"]:50} {c["path"] or ".":12} {c["spec"]} {" ".join(c["args"])}')
        print(len(cases), "cases", file=sys.stderr)
        return

    if os.path.isdir(WORKDIR):
        shutil.rmtree(WORKDIR)
    tm = os.path.join(WORKDIR, "tm")
    shutil.copytree(os.path.join(root, "test-model"), tm)
    jar = os.path.join(TP, "tla2tools.jar")
    prepared = []
    preparation_errors = []
    for c in cases:
        try:
            prepared.append(prepare(c, tm, jar))
        except Exception as error:
            preparation_errors.append(CaseResult(c["cls"], "error", {"message": repr(error)}))
    cases = prepared
    skipped = [c for c in cases if c["skip"] in ("ignored in the JUnit sources", "arguments are not literals")]
    preparation_errors += [CaseResult(c["cls"], "error", {"message": c["skip"]})
                           for c in cases if c["skip"] and c not in skipped]
    cases = [c for c in cases if not c["skip"]]

    oracle = {}
    if os.path.exists(ORACLE):
        with open(ORACLE) as source:
            oracle = json.load(source)
    identity = tlc_identity()
    dependencies = dependency_digest(tm)
    inputs = {d: dependency_digest(d) for d in sorted({c["dir"] for c in cases})}
    metadata = {c["cls"]: oracle_metadata(c, commit, identity, dependencies, inputs[c["dir"]]) for c in cases}
    stale = [c for c in cases if c["cls"] in oracle and oracle[c["cls"]].get("metadata") != metadata[c["cls"]]]
    todo = [c for c in cases if a.refresh_oracle or oracle_retry(oracle.get(c["cls"]), metadata[c["cls"]], a.oracle_timeout)]
    lock = threading.Lock()

    def make_oracle(c):
        try:
            r = run_oracle(c, a.oracle_timeout)
        except Exception as error:
            r = {"result": "collection error", "error": repr(error)}
        entry = oracle_entry(metadata[c["cls"]], r, a.oracle_timeout, c)
        with lock:
            oracle[c["cls"]] = entry
            json_update(ORACLE, lambda data: data.update({c["cls"]: entry}))
        return c

    if todo:
        print(f"TLC oracle: {len(todo)} cases to run ({len(cases) - len(todo)} cached)", flush=True)
        with ThreadPoolExecutor(a.tlc_jobs) as ex:
            list(ex.map(make_oracle, todo))
    no_oracle = [c for c in cases if not oracle_ready(oracle.get(c["cls"]), metadata[c["cls"]])]
    runnable = [c for c in cases if c not in no_oracle]
    case_results = preparation_errors + [CaseResult(c["cls"], "skip", {"message": c["skip"]}) for c in skipped]
    case_results += [CaseResult(c["cls"], "error", {"message": "missing TLC oracle", "collection": oracle[c["cls"]].get("collection")})
                     for c in no_oracle]

    expected = load_expected()
    with build_tlx(profile=profile_of(a), build=not a.no_build, prefix="tlx-tlcsuite-") as binary:
        def one(c):
            tlc = oracle[c["cls"]]["tlc"]
            execution_error = None
            try:
                tlx = run_tlx(binary, c, a.timeout, a.extra.split())
            except Exception as error:
                execution_error = repr(error)
                tlx = {"result": "unknown", "error": execution_error}
            contract = comparison(c, tlc, tlx)
            diffs = contract.differs
            raw = "pass" if not diffs else "fail"
            if execution_error or tlx.get("result") in (None, "unknown") or tlx.get("exit", 0) < 0 or (tlx.get("result") == "success" and tlx.get("exit", 0) != 0):
                raw = "error"
            elif tlx.get("result") == "timeout":
                raw = "timeout"
            e = match_expected(expected, c["cls"], tlx.get("result"), match_result=raw != "pass",
                               suite=a.suite or "tlcsuite")
            judged = judge_case(CaseResult(c["cls"], raw, {"kind": tlx.get("result"), "differs": diffs,
                                                        "message": execution_error or ",".join(diffs), **contract.details()}), known=e)
            status = {"pass": "PASS", "xpass": "FIXED", "xfail": "XFAIL"}.get(judged.status, "FAIL")
            # Keep the familiar text format; verification consumes the JSON report.
            note = {"XFAIL": f' [expected: {e["reason"]}]' if e else "",
                    "FIXED": f' [FIXED: remove its expected failure ({e["reason"]})]' if e else ""}.get(status, "")
            print(f'{"PASS" if status in ("PASS", "FIXED") else "FAIL"} {c["cls"]:48} tlc={describe(tlc)} tlx={describe(tlx)} '
                  f'({tlc.get("wall_s")}s vs {tlx.get("wall_s", 0):.2f}s) differs: {",".join(diffs) or "-"}{note} checked={",".join(contract.checked)}', flush=True)
            if status == "FAIL" and a.v and tlx.get("tail"):
                print("    " + tlx["tail"].replace("\n", "\n    "))
            return c, tlc, tlx, diffs, status, e, judged
        with ThreadPoolExecutor(a.j) as ex:
            results = list(ex.map(one, runnable))
    case_results += [r[6] for r in results]

    # (Like difftest's tlx<tag>.json: the results of this run merged into the previous ones.)
    json_update(RESULTS, lambda data: data.update({c["cls"]: {"ok": not diffs, "differs": diffs, "tlx": tlx, "tlc": tlc}
                                                   for c, tlc, tlx, diffs, _, _, _ in results}))
    count = lambda s: sum(r[4] == s for r in results)
    agree = [junit_agrees(c, oracle[c["cls"]]["tlc"]) for c in runnable]
    print(f"\n{len(results)} cases run: {count('PASS') + count('FIXED')} passed, {count('XFAIL')} expected failures, {count('FAIL')} unexpected"
          f" ({count('FIXED')} of the passed are listed as expected failures: remove them)")
    print(f"{len(skipped)} skipped ({_tally(c['skip'] for c in skipped)}), {len(no_oracle)} without a TLC result in {a.oracle_timeout} s;"
          f" the JUnit expectations agree with TLC on {sum(x is True for x in agree)}/{sum(x is not None for x in agree)} cases")
    if a.v:
        for c in skipped:
            print(f'skipped {c["cls"]}: {c["skip"]}')
        for c in no_oracle:
            print(f'no oracle {c["cls"]}')

    coverage = {"to_test": len(names), "verified": sum(c.status in ("pass", "fail", "xpass", "xfail")
                                                    and c.details.get("kind") != "timeout" for c in case_results), "missing": len(no_oracle),
                "stale": sum(not oracle_ready(oracle.get(c["cls"]), metadata[c["cls"]]) for c in stale),
                "skipped": len(skipped), "preparation_errors": len(preparation_errors), "refreshed_stale": len(stale)}
    print("coverage: " + ", ".join(f"{k}={v}" for k, v in coverage.items()))
    report = finish_cases(case_results, names, a.results_json, coverage=coverage)
    print(case_summary(report))
    if a.update_expected:
        kept = []
        for c, tlc, tlx, diffs, status, e, _ in results:
            if status == "XFAIL" and e not in kept:
                kept.append(e)
        new = [{"id": c["cls"], "result": tlx.get("result"), "reason": reason_for(c, tlc, tlx, diffs),
                **({"flaky": True} if tlx.get("result") == "timeout" else {})}
               for c, tlc, tlx, diffs, status, e, judged in results
               if status == "FAIL" and judged.status in ("fail", "timeout")]
        # (An entry for a case this run did not cover stays, as does a flaky one that did not fail this time.)
        selected = [r[0]["cls"] for r in results]
        others = [e for e in expected if e not in kept and (e.get("flaky") or not any(fnmatch.fnmatchcase(n, e["id"]) for n in selected))]
        entries = sorted(kept + others + new, key=lambda e: e["id"])
        write_expected(EXPECTED, entries)
        print(f"{EXPECTED}: {len(entries)} entries ({len(new)} new)")
    sys.exit(report["exit_code"])


def _tally(items):
    counts = {}
    for item in items:
        counts[item] = counts.get(item, 0) + 1
    return ", ".join(f"{n} {k}" for k, n in sorted(counts.items())) or "none"


if __name__ == "__main__":
    main()
