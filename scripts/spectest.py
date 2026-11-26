#!/usr/bin/env python3
"""Conformance test: run every tests/specs/NAME.tla (+ NAME.cfg) through TLC
and tlx and compare them by the tiers of the contract (docs/compat.md §0).
Exact (tiers 1 and 2): the kind of result (an error only as "error": its
class and the exit code are not compared); the violated name (invariant,
action / initial property, POSTCONDITION); the distinct and generated
counts and the depth; the length of a safety counterexample (invariant,
deadlock, action / initial property). Valid (tier 3): which
counterexample. If tlx's differs from TLC's (states, order, action
labels), TLC checks it (scripts/tracecheck.py): it must be a behavior of
the spec that violates the reported property. For liveness, the reported
properties may differ from TLC's (tlx may name more): tlx must name at
least one (unless TLC names none either: then its lasso must violate some
property), and its lasso must violate every one it names (checked the same
way when the lasso or the names differ; under VIEW modulo the VIEW, see
docs/compat.md D-10). Output format and message texts are not compared.

A differing counterexample that TLC confirms passes as `PASS NAME ...
(trace differs, valid)`. When TLC cannot decide, it passes with the note
`(trace differs, unvalidated: WHY)`: without java (TLX_JAVA), or when TLC's
own counterexample fails the check too (VIEW / SYMMETRY lassos, run-time
string order: see scripts/tracecheck.py). TLC's checks are cached in
tests/specs/tlc/validated.json (by a hash of the spec, its cfg and the
trace), so that a normal run starts no JVM: commit new entries with the
change that made them.

TLC's output (with -tool, normalized) is cached in tests/specs/tlc/NAME.out
(refresh with --refresh); tests/specs/expected.json summarizes it.

An optional NAME.flags holds extra flags for both checkers (e.g.
`-simulate num=5 -depth 20`); simulations (also -generate) compare only the
verdict, unless the file has a `# deterministic` line:
then the generated states too. A `# xfail ID` line marks a known
difference (ID: its entry in docs/compat.md): the test then fails if the
difference is gone (XPASS), to have the mark removed. A `# env K=V ...`
line sets environment variables of the tlx run only (e.g. TLX_PRERUN=1 to
force layout misses in compiled mode). `# timeout S` caps the tlx wall time
and `# cpu-timeout S` caps its measured CPU time (user + system). Exceeding
either budget always fails, even for a spec expecting an error or an xfail.
Other lines starting with `#` are comments.

For a liveness violation TLC runs with several fingerprint functions (-fp):
its lasso often depends on them (docs/compat.md, D-1; `trace-random` in
NAME.out). tlx's lasso is checked by TLC unless it equals the first one.

With `-workers N` (N > 1, or auto) in --extra, tlx is compared only by what
a multi-worker run must match (as scripts/difftest.py --workers does): the
kind of result (an evaluation error TLC stops at may lose the race to
a violation) and the violated name; the distinct and generated counts and
the depth only for a run that explored everything (result success, not a
simulation: an early stop counts whatever the other workers had done by
then); no counterexample comparison. A spec that uses TLCSet or TLCGet
depends on the schedule: its result is not compared at all (only that tlx
produced one). TLC always runs with one worker (the cached .out).

Both run with -tool, only to delimit the counterexample's states.

tlx runs in a private temporary copy of tests/specs, so specs that write
files next to themselves (RS3-RS5 create RS<n>.csv) cannot race with another
spectest process in the same checkout.

usage: scripts/spectest.py [--refresh] [--extra=ARGS] [--timeout S] [--default-mode] [NAME...]

  NAME...       the specs to run (default: every NAME.tla with a NAME.cfg);
                whitespace splits a name ("A B" means A and B); every name
                must be a known spec or spectest exits 2 naming it
  --refresh     rerun TLC instead of using tests/specs/tlc/NAME.out
  --extra=ARGS  extra tlx arguments, e.g. --extra=-compile or --extra="-workers 8"
  --default-mode  run tlx in its default mode and tier (without the -tlc the
                parity runs pass) and compare by verdict: the result, the
                violated names, the validity of a differing counterexample
                (TLC checks it) and the fields the optimizations it used
                preserve (suite spectest-default)
  --require-native  fail a case whose tlx run reports that generated C was not
                used: native code disabled, a failed C build or load, or a
                whole-model compiler fallback. The sanitizer suites use it so
                an unavailable sanitizer runtime cannot pass as an interpreter
                run
Environment variables (e.g. TLX_PARANOID=1) are passed on to tlx; TLX_JAVA
selects the java of TLC (see scripts/tlc.py).
"""
import tempdirs

import argparse, concurrent.futures, difflib, itertools, json, os, re, shutil, subprocess, sys, tempfile, threading, time

from modelcheck.results import must, layout_free  # re-export for existing driver consumers
from contract import compare as compare_contract
from tlxlib import CaseResult, add_result_args, finish_cases, case_summary, judge_case, load_expected_cases, ROOT, add_profile_args, build_tlx, profile_of, run_proc, parity_args, parity_env, tlx_env, no_foreign_home
SPECS = os.path.join(ROOT, "tests", "specs")
NATIVE_MISSING = ("native code disabled:", "C build failed, keeping the JIT code:")


def native_missing(out):
    """Why `out` reports that generated C was not used (None when it was)."""
    return compile_fallback(out) or next((marker for marker in NATIVE_MISSING if marker in out), None)
TLC_OUT = os.path.join(SPECS, "tlc")
# The third_party directory whose jars and -I modules TLC names in its output.
# `third_party/` is a symlink to the shared copy (worktrees share one), so its
# real path lies outside the checkout and has to be normalized on its own - and
# first, so that a cache refreshed in the main checkout and one refreshed in a
# worktree come out identical.
THIRD_PARTY = os.path.realpath(os.path.join(ROOT, "third_party"))
from tlc import compile_fallback, parse, run_tlc_raw
import tracecheck
from tracecheck import trace_blocks as trace

# The fingerprint functions TLC runs with (its default is a random one).
FP = ("0", "1", "2", "3", "5")


def normalize(out, dirs):
    """TLC's or tlx's output without what varies between runs: dates,
    durations, rates, pids, directories, and the paths of the jars SANY read."""
    for d in dirs:
        out = out.replace(d, "<dir>")
    out = re.sub(r"\d{4}-\d\d-\d\d \d\d:\d\d:\d\d", "<date>", out)
    out = re.sub(r"Finished in \S+( \S+)? at", "Finished in <time> at", out)
    out = re.sub(r"Finished checking temporal properties in \S+( \S+)? at", "Finished checking temporal properties in <time> at", out)
    out = re.sub(r"\(([\d,]+) (d?s)/min\)", r"(<rate> \2/min)", out)
    out = re.sub(r"\[pid: \d+\]", "[pid: <pid>]", out)
    # The machine and the JVM (TLC_MODE_MC, TLC_MODE_SIMU).
    out = re.sub(r"(Running .* with \d+ workers?) on \d+ cores .*", r"\1 on <machine>", out)
    out = re.sub(r"\S*/tlc-\d+/", "<tmp>/", out)
    # Every jar SANY read, by its file name: the directory it sits in is the
    # recorder's (`third_party/` is a symlink to the shared copy, so its real
    # path is outside the checkout), and which jar a module came from is what
    # the line says. The name is kept so that two jars still compare unequal.
    out = re.sub(r"jar:file:\S*[/\\]([^/\\\s]+\.jar)!", r"jar:file:<\1>!", out)
    return out




def extra_workers(extra):
    """The number of tlx workers `extra` (a list of arguments) asks for:
    1 without -workers, 0 for `-workers auto` (several, unknown)."""
    for i, a in enumerate(extra[:-1]):
        if a == "-workers":
            return int(extra[i + 1]) if extra[i + 1].isdigit() else 0
    return 1


def schedule_dependent(n):
    """Whether spec `n` reads or sets TLC registers or statistics, whose
    values depend on the order several workers run in."""
    with open(os.path.join(SPECS, n + ".tla")) as f:
        return re.search(r"\bTLC(Set|Get)\s*\(", f.read()) is not None




def tlc_output(n, flags, refresh, timeout=120):
    """TLC's normalized -tool output for spec `n`: (output, exit code,
    whether its liveness counterexample is random)."""
    path = os.path.join(TLC_OUT, n + ".out")
    if not refresh and os.path.exists(path):
        with open(path) as stream:
            text = stream.read()
        head, out = text.split("\n", 1)
        m = re.match(r"# exit (\d+)( trace-random)?$", head)
        return out, int(m.group(1)), bool(m.group(2))
    spec = os.path.join(SPECS, n + ".tla")
    args = ["-config", n + ".cfg", "-workers", "1", "-tool", *flags]
    # (TLC evaluates action composition only with a JVM flag.)
    with open(spec) as stream:
        features = ["action composition"] if "\\cdot" in stream.read() else []
    runs = []
    deadline = time.monotonic() + timeout
    for fp in FP:
        out, rc, _ = run_tlc_raw(spec, ["-fp", fp, *args], timeout=max(0, deadline - time.monotonic()),
                               features=features, scratch=True)
        out = re.sub(r"[^\s:]*tlx-scratch-[^/\s]+/specs", "<specs>", out)
        runs.append((normalize(out, [THIRD_PARTY, os.path.realpath(ROOT), ROOT]), rc))
        if parse(out, 0, rc).get("result") != "liveness failure" or "-simulate" in flags or "-generate" in flags:
            break
    out, rc = runs[0]
    random = any(trace(o) != trace(runs[0][0]) for o, _ in runs[1:])
    os.makedirs(TLC_OUT, exist_ok=True)
    with open(path, "w") as f:
        f.write(f"# exit {rc}{' trace-random' if random else ''}\n"
                f"{no_foreign_home(out, path)}")
    return out, rc, random

# Library modules TLC finds on its classpath (scripts/tlc.py).
# As before the corpus rework: CommunityModules and Apalache via -I, tlapm/library not at
# all (with -I its Bags.tla would shadow the standard Bags; spec
# tests don't use TLAPS modules).
INCLUDES = [a for d in ("community", "apalache") for a in ("-I", os.path.join(ROOT, "third_party", d))]


def spec_names():
    """The known spec names: a NAME.tla with a NAME.cfg next to it (the rule
    that also picks the default set)."""
    return sorted(f[:-4] for f in os.listdir(SPECS)
                  if f.endswith(".tla") and os.path.exists(os.path.join(SPECS, f[:-4] + ".cfg")))


def resolve_names(names):
    """The specs named on the command line: each NAME is split on whitespace
    ("A B" means the specs A and B). Every part must be a known spec; an
    unknown name is printed to stderr with up to 3 close matches and exits 2
    before anything runs, so --refresh can never write a stray .out for it.
    No NAME means every spec."""
    if not names:
        return spec_names()
    known = spec_names()
    resolved, unknown = [], []
    for name in names:
        for part in name.split():
            (resolved if part in known else unknown).append(part)
    if unknown:
        for name in unknown:
            sys.stderr.write(f"spectest: unknown spec {name} (no tests/specs/{name}.tla)\n")
            matches = difflib.get_close_matches(name, known, n=3)
            if matches:
                sys.stderr.write(f"    did you mean: {', '.join(matches)}?\n")
        sys.exit(2)
    return resolved


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("names", nargs="*", metavar="NAME")
    ap.add_argument("--refresh", action="store_true")
    ap.add_argument("-j", "--jobs", type=int, default=1, help="number of parallel spec jobs (default 1)")
    ap.add_argument("--extra", default="", help="extra tlx arguments (write --extra=-compile)")
    ap.add_argument("--default-mode", action="store_true",
                    help="run tlx in its default mode and tier (no -tlc) and compare by verdict: the result, the violated "
                         "names, a valid counterexample and what the optimizations used preserve")
    ap.add_argument("--timeout", type=float, default=os.environ.get("TLX_SPEC_TIMEOUT", "120"),
                    help="per-case timeout in seconds (default 120, or TLX_SPEC_TIMEOUT)")
    add_result_args(ap)
    ap.add_argument("--no-build", action="store_true", help="reuse the selected profile binary built by the caller")
    ap.add_argument("--require-native", action="store_true",
                    help="fail a case whose tlx run reports that generated C was not used (native code disabled, "
                         "a failed C build or load, or a whole-model compiler fallback)")
    add_profile_args(ap)
    a = ap.parse_args()
    if a.jobs < 1:
        ap.error("-j must be positive")
    names = resolve_names(a.names)
    with build_tlx(profile=profile_of(a), build=not a.no_build, prefix="tlx-spectest-bin-") as binary:
        run_specs(a, names, binary)


def run_specs(a, names, binary):
    refresh = a.refresh
    extra = a.extra.split()
    workers = extra_workers(extra)
    jobs = max(1, getattr(a, "jobs", 1))
    exp_path = os.path.join(SPECS, "expected.json")
    expected = {}
    if os.path.exists(exp_path):
        with open(exp_path) as source:
            expected = json.load(source)
    # Each worker thread gets its own private copy of the spec directory so specs
    # that write files next to themselves (e.g. RS3-RS5) never race with another
    # worker or another spectest process in the same checkout.
    scratch = tempdirs.TemporaryDirectory(prefix="tlx-spectest-")
    worker_local = threading.local()
    worker_lock = threading.Lock()
    worker_ids = itertools.count()

    def worker_run_dir():
        run_dir = getattr(worker_local, "run_dir", None)
        if run_dir is None:
            with worker_lock:
                idx = next(worker_ids)
            run_dir = os.path.join(scratch.name, f"specs-{idx}")
            shutil.copytree(SPECS, run_dir)
            worker_local.run_dir = run_dir
        return run_dir

    validated = {}
    if os.path.exists(VALIDATED):
        with open(VALIDATED) as source:
            validated = json.load(source)
    validated_before = dict(validated)
    validated_lock = threading.Lock()
    results, notes = [], {}
    entries = load_expected_cases()
    suite = a.suite or ("spectest-default" if getattr(a, "default_mode", False) else "spectest-compile" if "-compile" in extra else "spectest")
    if not a.suite and workers != 1:
        suite += f"-w{workers}"

    def run_one(n):
        lines_out = []
        try:
            fpath = os.path.join(SPECS, n + ".flags")
            lines = []
            if os.path.exists(fpath):
                with open(fpath) as source:
                    lines = source.read().splitlines()
            flags = [f for line in lines if not line.startswith("#") for f in line.split() if f != "-tool"]
            deterministic = "# deterministic" in lines
            simulation = "-simulate" in flags or "-generate" in flags
            tlc_out, tlc_rc, random = tlc_output(n, flags, refresh, timeout=a.timeout)
            want = must(tlc_out, tlc_rc)
            expected_entry = {k: want[k] for k in ("result", "violated", "distinct", "generated", "exit", "depth")}
            if random:
                expected_entry["trace_random"] = True
            tlx_args = [*flags, *extra] if getattr(a, "default_mode", False) else parity_args(binary, [*flags, *extra])
            env = tlx_env(extra=parity_env(tlx_args))
            env.update(kv.split("=", 1) for line in lines if line.startswith("# env ") for kv in line.split()[2:])
            timeout = min([a.timeout, *[float(line.split()[2]) for line in lines if line.startswith("# timeout ")]])
            cpu_limit = next((float(line.split()[2]) for line in lines if line.startswith("# cpu-timeout ")), None)
            p = run_proc([binary, "check", n + ".tla", "-config", n + ".cfg", "-tool", *INCLUDES, *tlx_args],
                         timeout=timeout, cwd=worker_run_dir(), env=env, rusage=cpu_limit is not None)
            if cpu_limit is not None and p.rusage.ru_utime + p.rusage.ru_stime > cpu_limit:
                cpu = p.rusage.ru_utime + p.rusage.ru_stime
                raise subprocess.TimeoutExpired(f"{n} (CPU timeout: {cpu:.3f}s > {cpu_limit:g}s)", cpu_limit)
            out = p.stdout + p.stderr
            if getattr(a, "require_native", False) and (missing := native_missing(out)):
                raise RuntimeError(f"generated C was not used ({missing}): {out[-600:]}")
            got = must(out, p.returncode)
            if got["result"] in (None, "unknown") or p.returncode < 0 or (got["result"] == "success" and p.returncode != 0):
                raise RuntimeError(f"tlx did not complete: exit {p.returncode}: {out[-600:]}")
            if workers != 1:
                diff, note, detail = compare_workers(n, want, got, simulation, getattr(a, "default_mode", False))
            else:
                with validated_lock:
                    diff, note, detail = compare(n, want, got, simulation, deterministic, validated, getattr(a, "default_mode", False))
            contract = compare_contract(want, got, workers=workers, simulation=simulation,
                                        deterministic=deterministic, allow_unnamed_liveness=workers == 1,
                                        schedule_dependent=workers != 1 and schedule_dependent(n), optimized=getattr(a, "default_mode", False))
            if workers == 1 and not simulation and not contract.differs and got.get("trace"):
                if "unvalidated" not in note:
                    contract.skipped.pop("trace validity", None)
                    contract.checked.append("trace validity")
                else:
                    contract.skipped["trace validity"] = note
            # A known difference (docs/compat.md): `# xfail ID` in NAME.flags.
            xfail = next((line.split()[2] for line in lines if line.startswith("# xfail ")), None)
            known = {"reason": xfail} if xfail else None
            if known and workers != 1:
                # With several workers the comparator skips the fields a race
                # can change, so the marked difference may go unobserved: a
                # passing run does not mean the difference is gone (no XPASS).
                known["flaky"] = True
            case = judge_case(CaseResult(n, "fail" if diff else "pass", {"kind": got["result"], "differs": diff, "note": note, **contract.details()}),
                              entries, suite, known=known)
            status = case.status.upper()
            show = lambda r: {k: r[k] for k in ("result", "violated", "exit", "distinct", "generated", "depth")}
            lines_out.append(f'{status} {n:12} tlc={show(want)} tlx={show(got)}' + (f" differs: {diff}" if diff else "")
                             + (f" ({note})" if note else "") + (f" (known: {xfail})" if xfail else "") + f" checked={','.join(contract.checked)}")
            if detail:
                lines_out.append("    " + detail.replace("\n", "\n    "))
            if "trace" in diff or "trace length" in diff:
                lines_out.append(f"    tlc trace: {want['trace']} \n    tlx trace: {got['trace']}")
            return n, case, expected_entry, note, lines_out
        except Exception as error:
            status = "timeout" if isinstance(error, subprocess.TimeoutExpired) else "error"
            case = CaseResult(n, status, {"message": repr(error)})
            lines_out.append(f"FAIL {n:12} execution {status}: {error}")
            return n, case, None, None, lines_out

    try:
        if jobs == 1 or len(names) <= 1:
            outcomes = (run_one(n) for n in names)
        else:
            pool = concurrent.futures.ThreadPoolExecutor(max_workers=min(jobs, len(names)))
            try:
                futures = [pool.submit(run_one, n) for n in names]
                outcomes = [fut.result() for fut in futures]
            finally:
                pool.shutdown(wait=True)
        for n, case, expected_entry, note, lines_out in outcomes:
            if expected_entry is not None:
                expected[n] = expected_entry
            if note is not None:
                notes[note] = notes.get(note, 0) + 1
            results.append(case)
            for line in lines_out:
                print(line)
        if refresh or not a.names:
            with open(exp_path, "w") as output:
                json.dump(expected, output, indent=1, sort_keys=True)
    finally:
        scratch.cleanup()
    if validated != validated_before:
        with open(VALIDATED, "w") as f:
            json.dump(validated, f, indent=1, sort_keys=True)
            f.write("\n")
    counts = ", ".join(f"{v} {k}" for k, v in sorted(notes.items()) if k)
    report = finish_cases(results, names, a.results_json, suite=suite)
    fails = sum(c.status in ("fail", "xpass", "error", "timeout") for c in results)
    print(f"{len(names) - fails}/{len(names)} passed" + (f" ({counts})" if counts else ""))
    print(case_summary(report))
    sys.exit(report["exit_code"])


# TLC's checks of tlx's counterexamples (scripts/tracecheck.py): hash ->
# [verdict, detail].
VALIDATED = os.path.join(TLC_OUT, "validated.json")
SAFETY = ("safety failure", "deadlock", "property failure", "init property failure")


def compare_workers(n, want, got, simulation, optimized=False):
    """What a run with several workers must match: (differing fields, note,
    detail) as `compare` returns them."""
    comparison = compare_contract(want, got, workers=2, simulation=simulation,
                                  schedule_dependent=schedule_dependent(n), optimized=optimized)
    note = comparison.skipped.get("result", "")
    return comparison.differs, note, ""


def compare(n, want, got, simulation, deterministic, validated, optimized=False):
    """The differences between TLC's (`want`) and tlx's (`got`) results by
    the contract's tiers: (differing fields, note, detail). The note says
    how a differing counterexample passed ("trace differs, valid", "trace
    differs, unvalidated: ..."); the detail, why one failed. With
    `optimized`, a run of the default mode is compared by verdict
    (contract.compare); its counterexample must still be valid."""
    result = want["result"]
    comparison = compare_contract(want, got, simulation=simulation, deterministic=deterministic,
                                  allow_unnamed_liveness=True, optimized=optimized)
    diff = comparison.differs
    if diff or simulation:
        return diff, "", ""
    if result in SAFETY:
        if len(got["trace"]) != len(want["trace"]):
            return ["trace length"], "", ""
        if got["trace"] == want["trace"]:
            return [], "", ""
        names = [got["violated"]]
    elif result == "liveness failure":
        if (got["trace"], got["violated"]) == (want["trace"], want["violated"]):
            return [], "", ""
        names = tracecheck.property_names(got["violated"])
        if not names and want["violated"] is not None:
            return ["violated"], "", "tlx names no violated property"
        # (Neither names one: under VIEW or SYMMETRY, or LiveCheck1's
        # verdicts in simulation, TLC may report a lasso violating no
        # property in its concrete states. tlx's must violate some.)
        names = names or None
    else:
        return [], "", ""
    what = "trace differs" if got["trace"] != want["trace"] else "violated properties differ"
    cfg = tracecheck.read(os.path.join(SPECS, n + ".cfg"))
    want_names = tracecheck.property_names(want["violated"]) if result == "liveness failure" else [want["violated"]]
    verdict, why = tracecheck.check_against(SPECS, n, cfg, result, got["lasso"], names, want["lasso"], want_names,
                                            cache=validated)
    if verdict == "valid":
        return [], f"{what}, valid", ""
    if verdict == "unchecked":
        return [], f"{what}, unvalidated: {why}", ""
    return ["trace" if what == "trace differs" else "violated"], "", f"{what}: {verdict}: {why}"


if __name__ == "__main__":
    main()
