#!/usr/bin/env python3
"""Continuous performance tracking: the fixed benchmark suite (bench/suite.json),
its A/B runner, the committed history (bench/history/<rev>.json) and the canonical
report (docs/performance.md). Subcommands of scripts/bench.py:

  bench.py suite-check [--manifest F] [--oracle]
      Validate the manifest (and with --oracle compare its expected counts with
      the TLC oracle files under corpus/out).
  bench.py suite [--sizes small,medium,large] [--models a,b] [--base-bin PATH --base-rev REV]
                 [--bin PATH] [--repeat 3] [--max-minutes M] [--inject-slow MODEL=FACTOR] [--out FILE]
      Run the suite with the current release binary (built unless --bin) and,
      with --base-bin, the previous recorded revision's binary, interleaved
      per model and mode on this machine. Writes the history file, prints the
      verdict; exit 0 pass (or baseline), 1 regression or count mismatch,
      2 inconclusive/incomplete.
  bench.py suite-report [--history DIR]
      Re-ingest the suite histories under bench/history/*.json into the canonical
      records and regenerate docs/performance.md from them.
  bench.py track [--rev HEAD] [--base auto|REV|none] [--sizes ...] [--provider tencent]
      The coordinator's command after merges: the suite on one cloud instance
      (cloud_verify.py --bench), the history file copied into bench/, the
      verdict printed; same exit codes.

See docs/benchmarking.md, "Continuous performance tracking".

The suite manifest and current measurement records ship with the sources;
superseded evidence is archived separately. A missing
manifest is an incomplete checkout and is reported without a traceback.
"""

from benchmarking import models as bench_models, machine as bench_machine
from benchmarking.legacy import missing_input
from benchmarking import bench_budget
from cloud import cloud_common
import tempdirs

import contextlib, json, math, os, re, shutil, statistics, subprocess, sys, tempfile, time

from tlxlib import json_update, ROOT, git, geomean

SUITE = os.path.join(ROOT, "bench", "suite.json")
HISTORY = os.path.join(ROOT, "bench", "history")
# Where cloud_verify.py leaves the result directory (and its receipt) of a launch.
BENCH_RESULTS = os.path.join(ROOT, "target", "bench")
SIZES = ("small", "medium", "large", "huge")
DEFAULT_SIZES = "small,medium,large"
MODES = ("compile", "interp", "default", "tlc")
EXPECT_SOURCES = ("tlc-oracle", "tlc-bench", "tlx-pinned", "unpinned")
COUNT_FIELDS = ("distinct", "generated", "depth")
# Runs that produced no verdict at all: the runner's own timeout, the budget
# refusing to start one (`None` before a run, "skipped" when it is not started),
# and the parser's "unknown" (a killed or OOM'ed child). They have no counts of
# their own and are the incomplete-run gate's business — in the suite and in
# bench.py's repeated runs and scaling repeats, which import this; an "error" or
# "compile failure" is a verdict and stays a mismatch.
UNFINISHED = (None, "timeout", "killed", "unknown", "skipped")
# The fields of one sample kept in a run record's `samples`/`warmups` lists: the
# mode contract (result and counts), what explains it (the violated name, the
# error text, TLC compatibility, the optimizations applied) and its cost. The
# history's top-level `samples` array keeps the full parsed sample of every run.
SAMPLE_FIELDS = ("result", "violated", "error", "distinct", "generated", "depth",
                 "compatibility", "optimizations", "wall_s", "cpu_s", "maxrss_mib", "native_coverage")
# Exit statuses of `suite` and `track`: the verdict statuses a completed run
# produces, the one table `cloud_common` also reads before recording (HARNESS-12).
PASS, REGRESSION, INCONCLUSIVE = cloud_common.VERDICT_EXITS


# ---------------------------------------------------------------- manifest

# The refusal for a store input this checkout does not have (`missing_input`,
# with the sentence it ends with) is `benchmarking.legacy`'s: every reader of the
# store reaches it, so this reader's refusal and the report entrypoint's - which
# does not import this module - are the same sentence rather than two that drift.


def load_manifest(path=SUITE):
    """The manifest of the benchmark suite (bench/suite.json), validated.

    A checkout without the store has no manifest: the refusal names the file it
    needs rather than raising `FileNotFoundError` from `open`, and it is the
    first thing every reader of a store file reaches, so the whole class of
    missing store inputs reports the same way.
    """
    try:
        with open(path) as source:
            man = json.load(source)
    except FileNotFoundError:
        raise SystemExit(missing_input(path, ROOT))
    problems = validate_manifest(man)
    if problems:
        raise ValueError("invalid benchmark manifest:\n  " + "\n  ".join(problems))
    return man


def validate_manifest(man):
    """The problems of a manifest (empty if it is well-formed)."""
    problems = []
    if man.get("version") != 1:
        problems.append("version must be 1")
    seen = set()
    for i, m in enumerate(man.get("models") or []):
        mid = m.get("id")
        where = f"models[{i}] {mid!r}"
        if not isinstance(mid, str) or not mid:
            problems.append(f"{where}: missing id")
            continue
        if mid in seen:
            problems.append(f"{where}: duplicate id")
        seen.add(mid)
        if m.get("size") not in SIZES:
            problems.append(f"{where}: size must be one of {', '.join(SIZES)}")
        if not isinstance(m.get("timeout_s"), int) or m["timeout_s"] <= 0:
            problems.append(f"{where}: timeout_s must be a positive integer")
        runs = m.get("runs")
        if not runs:
            problems.append(f"{where}: no runs")
        pairs = set()
        for r in runs or []:
            if r.get("mode") not in MODES:
                problems.append(f"{where}: run mode must be one of {', '.join(MODES)}")
            if not isinstance(r.get("workers"), int) or r["workers"] < 1:
                problems.append(f"{where}: run workers must be a positive integer")
            extra_args = r.get("args", [])
            if not isinstance(extra_args, list) or not all(isinstance(a, str) for a in extra_args):
                problems.append(f"{where}: args must be a list of strings")
                extra_args = []
            env = r.get("env", {})
            if not isinstance(env, dict) or not all(isinstance(k, str) and isinstance(v, str) for k, v in env.items()):
                problems.append(f"{where}: env must be an object of string values")
                env = {}
            identity = (r.get("mode"), r.get("workers"), tuple(extra_args), repr(r.get("cgroup_mib")), tuple(sorted(env.items())))
            if identity in pairs:
                problems.append(f"{where}: duplicate run {r.get('mode')} {r.get('workers')}w")
            pairs.add(identity)
            if r.get("cgroup_mib") is not None and (type(r["cgroup_mib"]) is not int or r["cgroup_mib"] < 1):
                problems.append(f"{where}: cgroup_mib must be positive")
        ex = m.get("expect")
        if not isinstance(ex, dict) or not ex.get("result") and ex.get("source") != "unpinned":
            problems.append(f"{where}: expect.result is required")
            continue
        if ex.get("source") not in EXPECT_SOURCES:
            problems.append(f"{where}: expect.source must be one of {', '.join(EXPECT_SOURCES)}")
        if ex.get("source") != "unpinned" and ex.get("result") == "success" and not isinstance(ex.get("distinct"), int):
            problems.append(f"{where}: a pinned successful search needs expect.distinct")
        for f in COUNT_FIELDS:
            if f in ex and ex[f] is not None and not isinstance(ex[f], int):
                problems.append(f"{where}: expect.{f} must be an integer")
    return problems


# The adaptive tier chooser (TLX_MIXED_ADAPT) decides per function and per run
# which of two paths a mixed function takes, so a measurement of a model whose
# verdict it moves is not reproducible between runs. Pinning it makes the
# judgement reproducible, and because the pin is part of the run's environment
# it is part of the key: the pinned configuration sits beside the adaptive one
# instead of replacing it. `pin_adapt` in the manifest names the families whose
# verdict is tier-determined; a run pins them only when it is asked to.
PIN_ADAPT = {"TLX_MIXED_ADAPT": "0"}


def entries(man, sizes=DEFAULT_SIZES, models="", modes="", pin_adapt=""):
    """The runs to measure: [{key, model, size, mode, workers, timeout_s, expect, tlc_1w_s}].
    `key` has the form of bench.py's history keys (tier:model:mode:Nw, tier = size)."""
    sizes = [s for s in sizes.split(",") if s] if sizes != "all" else list(SIZES)
    bad = [s for s in sizes if s not in SIZES]
    if bad:
        raise ValueError(f"unknown size(s) {bad}; known: {', '.join(SIZES)}, all")
    only = [x for x in models.split(",") if x]
    modes = {x for x in modes.split(",") if x}
    if bad := modes - set(MODES):
        raise ValueError(f"unknown mode(s): {', '.join(sorted(bad))}")
    out = []
    for m in man["models"]:
        if m["size"] not in sizes or (only and not any(o == m["id"] or o in m["id"] for o in only)):
            continue
        for r in m["runs"]:
            if modes and r["mode"] not in modes:
                continue
            env = r.get("env") or None
            if pin_adapt and r["mode"] in ("compile", "default") and (pin_adapt == "all" or m.get("pin_adapt")):
                env = {**(env or {}), **PIN_ADAPT}
            r = {**r, "env": env}
            from benchmarking.records import digest
            # A run's own environment is part of its identity: a pinned adaptive
            # tier is a different measurement, not a silent replacement of the
            # adaptive one (docs/benchmarking.md 6.4).
            identity = [r.get("args"), r.get("cgroup_mib"), r.get("env")]
            suffix = ":" + digest(identity)[:8] if any(identity) else ""
            out.append({"key": f"{m['size']}:{m['id']}:{r['mode']}:{r['workers']}w" + suffix, "model": m["id"], "size": m["size"],
                        "mode": r["mode"], "workers": r["workers"], "timeout_s": m["timeout_s"], "expect": m["expect"],
                        "tlc_1w_s": m.get("tlc_1w_s"), "args": r.get("args", []),
                        "cgroup_mib": r.get("cgroup_mib"), "env": r.get("env") or None,
                        "category": r.get("category", m.get("category", []))})
    return out


def check_counts(rec, expect):
    """The mismatches of run record `rec` against the expected counts: a
    different kind of result always; for a pinned successful search also
    distinct, generated and depth (exact for a complete search under BFS)."""
    if not expect or expect.get("source") == "unpinned" and not expect.get("result"):
        return []
    out = []
    if rec.get("result") != expect.get("result"):
        out.append(f"result {rec.get('result')!r}, expected {expect.get('result')!r}")
        return out
    if rec.get("result") == "success" or expect.get("result") == "liveness failure":
        for f in COUNT_FIELDS:
            want = expect.get(f)
            if want is not None and rec.get(f) != want:
                out.append(f"{f} {rec.get(f)}, expected {want}")
    return out


def sample_record(r):
    """The mode-contract fields of one sample (a `bench.tlx` result dict)."""
    return {k: r.get(k) for k in SAMPLE_FIELDS if k == "result" or r.get(k) is not None}


def mode_expect(entry, sample):
    """The entry's expectation as the mode contract of one sample: the default
    mode and a run without TLC compatibility (no `-tlc`, so a reduced search)
    may change the state counts, which are then not part of its contract."""
    expect = entry["expect"]
    if entry["mode"] == "default" or sample.get("compatibility") is False:
        return {k: v for k, v in expect.items() if k not in COUNT_FIELDS}
    return expect


def problems_of(entry, sample):
    """The mode-contract problems of one completed sample or warm-up: a run that
    never finished has no counts to compare and is left to the incomplete-run
    gate (the entry is skipped), not reported as a mismatch."""
    if sample.get("result") in UNFINISHED:
        return []
    return check_counts(sample, mode_expect(entry, sample))


def sample_deviations(entry, rs, warmups, last):
    """Every measured sample or warm-up whose mode-contract problems differ from
    the aggregate's (`last`'s), named by its position, so the mismatch of an
    earlier run survives the aggregate of a later success; the aggregate's own
    problems are reported unprefixed by `record_of`."""
    aggregate = tuple(problems_of(entry, last)) if last is not None else ()
    out = []
    for label, runs in (("sample", rs), ("warmup", warmups)):
        for i, r in enumerate(runs, 1):
            if r is last:
                continue
            problems = problems_of(entry, r)
            if problems and tuple(problems) != aggregate:
                out.append(f"{label} {i}: " + "; ".join(problems))
    return out


def load_oracles(directory=None):
    """The TLC oracle results of corpus/out/tlc*.json merged: id -> record with "tlc"."""
    directory = directory or os.path.join(ROOT, "corpus", "out")
    out = {}
    for f in sorted(os.listdir(directory)) if os.path.isdir(directory) else []:
        if re.fullmatch(r"tlc(-[\w.-]+)?\.json", f) and f != "tlcsuite.json":
            try:
                with open(os.path.join(directory, f)) as source:
                    d = json.load(source)
            except (OSError, ValueError):
                continue
            for k, v in (d.items() if isinstance(d, dict) else []):
                if isinstance(v, dict) and (v.get("tlc") or {}).get("result"):
                    out.setdefault(k, v)
    return out


def oracle_problems(man, oracle):
    """Where the manifest's `tlc-oracle` expectations differ from the TLC
    oracle (corpus/out/*.json merged: id -> {"tlc": {...}})."""
    out = []
    for m in man["models"]:
        ex = m["expect"]
        if ex.get("source") != "tlc-oracle":
            continue
        t = (oracle.get(m["id"]) or {}).get("tlc")
        if not t:
            out.append(f"{m['id']}: tlc-oracle expectation but no oracle result")
            continue
        if t.get("result") != ex["result"]:
            out.append(f"{m['id']}: oracle result {t.get('result')!r}, manifest {ex['result']!r}")
        elif ex["result"] == "success":
            for f in COUNT_FIELDS:
                if ex.get(f) != t.get(f):
                    out.append(f"{m['id']}: oracle {f} {t.get(f)}, manifest {ex.get(f)}")
    return out


# ---------------------------------------------------------------- measuring

def perf_instructions_available():
    """Whether `perf stat -e instructions:u` works here (Linux, permitted)."""
    if not shutil.which("perf"):
        return False
    with tempfile.NamedTemporaryFile() as f:
        p = subprocess.run(["perf", "stat", "-x,", "-e", "instructions:u", "-o", f.name, "--", "true"], capture_output=True)
        with open(f.name) as perf:
            return p.returncode == 0 and instructions_of(perf.read()) is not None


def instructions_of(text):
    """The instruction count of `perf stat -x,` output, or None."""
    for line in text.splitlines():
        f = line.split(",")
        if len(f) > 2 and f[2].startswith("instructions") and f[0].strip().isdigit():
            return int(f[0])
    return None


def measure_once(bench, m, entry, exe, instr, env=None, slow=1.0, collect_native=False):
    """One run of tlx: the parsed result with wall/cpu/rss and instructions
    (None without perf). `slow` > 1 stretches the run by that factor (the
    forced-regression test hook: the extra time is slept and added to wall and
    cpu, as if the program were slower)."""
    args = bench.mode_args(entry["mode"], entry["workers"], m, exe=exe) + entry.get("args", [])
    wrap, path = (), None
    stats_tmp = tempdirs.TemporaryDirectory(prefix="tlx-native-stats-") if collect_native else None
    stats_path = os.path.join(stats_tmp.name, "stats.json") if stats_tmp else None
    if stats_path:
        args += ["-stats", f"json={stats_path}"]
    if instr:
        fd, path = tempfile.mkstemp(prefix="tlx-perf-")
        os.close(fd)
        wrap = ["perf", "stat", "-x,", "-e", "instructions:u", "-o", path, "--"]
    try:
        if entry.get("cgroup_mib"):
            from benchmarking.bench_disk import run_tlx
            r = run_tlx(m, exe, args, entry["timeout_s"], env or {}, cg_mib=entry["cgroup_mib"])
        else:
            r = bench.tlx(m, args, entry["timeout_s"], exe=exe, env=env, wrap=wrap)
        with open(path) if path else contextlib.nullcontext() as perf:
            r["instructions"] = instructions_of(perf.read()) if perf else None
        if stats_path and os.path.isfile(stats_path):
            from coverage import dynamic_report
            with open(stats_path) as f:
                native = dynamic_report(json.load(f))
            # Tracking needs bounded per-run summaries; the census driver owns
            # full function/region tables, which can be megabytes per model.
            fields = ('native_share', 'evaluations', 'fully_native', 'host_time_share',
                      'host_time_s', 'host_calls', 'search_thread_s_est')
            r['native_coverage'] = {k: native[k] for k in fields}
            r['native_coverage']['diagnostic'] = True
    finally:
        if stats_tmp:
            stats_tmp.cleanup()
        if path:
            os.unlink(path)
    if slow > 1 and r.get("result") != "timeout":
        extra = r["wall_s"] * (slow - 1)
        time.sleep(extra)
        r["wall_s"] = round(r["wall_s"] + extra, 3)
        r["cpu_s"] = round(r["cpu_s"] + extra, 3)
        if r.get("instructions"):
            r["instructions"] = int(r["instructions"] * slow)
    return r


def record_of(entry, rs, load, expect_check=True, warmups=()):
    """The history record (bench.py's format, plus rss/instructions) of the
    measured runs `rs` and the discarded warm-ups `warmups`: the aggregate (the
    times of `rs`, and the counts, result and compatibility of its last sample)
    plus `samples` and `warmups`, every completed run's own mode-contract fields.
    The mode contract is checked for each of them; a mismatch of an earlier run
    is reported next to the aggregate's, never erased by a later success."""
    walls = [r["wall_s"] for r in rs]
    last = rs[-1] if rs else {"result": "skipped"}
    rec = {
        "tool": "tlx", "tier": entry["size"], "model": entry["model"], "mode": entry["mode"], "workers": entry["workers"],
        "walls": walls, "min": min(walls) if walls else 0, "median": statistics.median(walls) if walls else 0,
        "cpu": [r.get("cpu_s") for r in rs], "rss_mib": [r.get("maxrss_mib") for r in rs],
        "instructions": [r.get("instructions") for r in rs],
        "distinct": last.get("distinct"), "generated": last.get("generated"), "depth": last.get("depth"),
        "compatibility": last.get("compatibility"),
        "result": last.get("result"), "load": load,
        "samples": [sample_record(r) for r in rs], "warmups": [sample_record(r) for r in warmups],
    }
    native = [r['native_coverage'] for r in warmups if r.get('native_coverage') and r.get('result') not in UNFINISHED]
    if native:
        rec['native_coverage'] = native[-1]
    if entry.get("tlc_1w_s"):
        rec["tlc_1w_s"] = entry["tlc_1w_s"]
    rec.update(args=entry.get("args", []), category=entry.get("category", []), cgroup_mib=entry.get("cgroup_mib"),
               env=entry.get("env"))
    if expect_check and (rs or warmups):
        rec["count_problems"] = (check_counts(rec, mode_expect(entry, rec)) if rs else []) \
            + sample_deviations(entry, rs, warmups, last if rs else None)
    return rec


def measure_entry(bench, m, entry, bins, repeat, instr, slow_for, *, budget=None, checkpoint=None):
    """Interleaved A/B samples; checkpoint each completed warmup or measured run."""
    budget = budget or bench_budget.current()
    # The entry's own environment (a pinned adaptive tier) is part of what is
    # measured, so the warm-up and every sample carry it.
    run_env = dict(entry.get("env") or {})
    warm_env = {"TLX_NATIVE_SYNC": "1", **run_env} if entry["mode"] != "interp" else (run_env or None)
    load0 = os.getloadavg()[0]
    res = {name: [] for name, _ in bins}
    warm = {name: [] for name, _ in bins}
    skipped = False
    stopped = None

    def sample(name, exe, round_number, warmup=False):
        nonlocal skipped, stopped
        key = entry['key'] + '#' + name
        if stopped:
            budget.skipped.append({'model': key, 'reason': stopped})
            print(f'SKIP {key}: {stopped}', flush=True)
            timeout = None
        else:
            timeout = budget.admit(key, entry['timeout_s'], estimate=entry.get('estimate_s') or entry.get('tlc_1w_s'))
        if timeout is None:
            skipped = True
            if checkpoint:
                checkpoint({'model': entry['model'], 'variant': name, 'round': round_number,
                            'warmup': warmup, 'result': 'skipped', 'reason': stopped or 'deadline'}, res)
            return
        limited = {**entry, 'timeout_s': timeout}
        try:
            r = measure_once(bench, m, limited, exe, False if warmup else instr,
                             env=warm_env if warmup else (run_env or None),
                             slow=slow_for(entry) if not warmup and name == bins[-1][0] else 1.0,
                             collect_native=warmup)
        except subprocess.TimeoutExpired as error:
            r = {'result': 'timeout', 'wall_s': timeout, 'cpu_s': 0, 'error': str(error)}
        if r.get('result') in ('timeout', 'skipped'):
            stopped = 'sample timeout' if r['result'] == 'timeout' else 'deadline'
            skipped = True
        budget.observe(key, r.get('wall_s', timeout))
        (warm if warmup else res)[name].append(r)
        print(f"sample {entry['model']} {name} {'warmup' if warmup else 'round ' + str(round_number)}: "
              f"{r.get('wall_s', 0):.3f}s {r.get('result')}", flush=True)
        if checkpoint:
            checkpoint({'model': entry['model'], 'variant': name, 'round': round_number,
                        'warmup': warmup, **r}, res)

    for name, exe in bins:
        sample(name, exe, 0, warmup=True)
    for i in range(repeat):
        for name, exe in bins if i % 2 == 0 else bins[::-1]:
            sample(name, exe, i + 1)
    load = [round(load0, 2), round(os.getloadavg()[0], 2)]
    records = {name: record_of(entry, rs, load, expect_check=(name == bins[-1][0]), warmups=warm[name])
               for name, rs in res.items()}
    if skipped:
        for rec in records.values():
            rec.update(result='skipped', skipped=stopped or 'deadline', completed_samples=len(rec['walls']))
    return records



# ---------------------------------------------------------------- verdict

def judge(base_runs, runs, entries_done, skipped, compare):
    """The verdict of a run: count problems and timing regressions (naming
    models), inconclusive timings, skipped runs. `compare(ra, rb)` is
    bench.compare_runs. Returns a dict; outcome in PASS/BASELINE/REGRESSION/INCONCLUSIVE."""
    v = {"count_failures": [], "regressions": [], "inconclusive": [], "skipped": list(skipped), "improvements": []}
    for k, rec in sorted(runs.items()):
        if rec.get("count_problems"):
            v["count_failures"].append({"key": k, "problems": rec["count_problems"]})
    if base_runs:
        c = compare(base_runs, runs)
        rows = {r["key"]: r for r in c["rows"]}
        for k in c["regress"]:
            r = rows.get(k, {})
            v["regressions"].append({"key": k, "ratio": r.get("ratio"), "a": r.get("a"), "b": r.get("b"),
                                     **({"distinct": list(r["distinct"])} if "distinct" in r else {})})
        v["inconclusive"] = [{"key": k, "reasons": rows[k].get("reasons", [])} for k in c["inconclusive"]]
        v["improvements"] = c["better"]
        for key, rec in sorted(runs.items()):
            old = base_runs.get(key, {}).get('native_coverage', {}).get('native_share')
            new = rec.get('native_coverage', {}).get('native_share')
            if old is None or rec.get('result') in UNFINISHED:
                continue
            if new is None:
                v['inconclusive'].append({'key': key, 'reasons': ['missing dynamic native-share measurement']})
            elif new < old - 1e-6:
                v['regressions'].append({'key': key, 'metric': 'native_share', 'a': old, 'b': new})
    if v["count_failures"] or v["regressions"]:
        v["outcome"] = "REGRESSION"
    elif v["inconclusive"] or v["skipped"]:
        v["outcome"] = "INCONCLUSIVE"
    else:
        v["outcome"] = "PASS" if base_runs else "BASELINE"
    return v


def exit_status(verdict):
    return {"REGRESSION": REGRESSION, "INCONCLUSIVE": INCONCLUSIVE}.get(verdict["outcome"], PASS)


def commit_range(base, rev):
    """Commit hashes in base..rev; private backlog names stay in git history."""
    try:
        out = git("log", "--format=%h", "--no-decorate", f"{base}..{rev.split('-dirty')[0]}", check=False)
    except Exception:
        return []
    # Commit subjects may name a private backlog task ID, which tracked files
    # must not contain (the pre-commit hook refused a history file, 2026-10-07).
    # The policy is the production owner's, not a test module's (HARNESS-03).
    from benchmarking.policy import redact
    return [redact(l) for l in (out or "").splitlines() if l][:60]


def print_verdict(h, v):
    base, rev = h.get("base", {}).get("commit"), h["commit"]
    print(f"\nverdict: {v['outcome']}  ({(base + '..') if base else 'baseline, '}{rev}; {len(h['runs'])} runs on {h['machine']})")
    for f in v["count_failures"]:
        print(f"  COUNT MISMATCH {f['key']}: {'; '.join(f['problems'])}")
    for r in v["regressions"]:
        if r.get('metric') == 'native_share':
            print(f"  NATIVE COVERAGE REGRESSION {r['key']}: {100*r['a']:.4f}% -> {100*r['b']:.4f}%")
        if r.get("ratio") is not None:
            print(f"  REGRESSION {r['key']}: {r['a']:.2f}s -> {r['b']:.2f}s (x{r['ratio']:.2f})"
                  + (f", distinct {r['distinct'][0]} -> {r['distinct'][1]}" if r.get("distinct") else ""))
    for r in v["inconclusive"]:
        print(f"  inconclusive {r['key']}: {'; '.join(r['reasons'])}")
    for k in v["skipped"]:
        print(f"  skipped (time budget) {k}")
    if v["regressions"] and h.get("range"):
        print(f"commit range {base}..{rev}:")
        for l in h["range"]:
            print(f"  {l}")


# ---------------------------------------------------------------- the run

def resolve_models(ids, *, stage):
    """Resolve a batch in oracle, scaling-config, then Examples order."""
    available = bench_models.oracle(ids, stage=stage)
    scaling = [mid for mid in ids if mid not in available and mid in bench_models.SCALE_CFGS]
    if scaling:
        available.update(bench_models.scale_models(scaling))
    missing = set(ids) - available.keys()
    if missing:
        import corpus
        # Explicit benchmark entries retain their historical inputs and expectations,
        # including invalid upstream configs excluded from ordinary corpus sweeps.
        for model in corpus.models(float("inf"), include_invalid=True):
            mid = model["id"]
            if mid in missing:
                available[mid] = {**model, **bench_models.declared_run_fields(mid), "tlc": {}}
    return available


def resolve_model(bench, mid):
    available = resolve_models([mid], stage=True)
    if mid not in available:
        sys.exit(f"unknown benchmark model {mid}")
    return available[mid]


def run_suite(a, bench=None, resolve=None, man=None):
    """`bench.py suite`. Returns the exit status. `bench` (the module), `resolve`
    (model id -> bench model dict) and `man` can be given by tests."""
    if bench is None:
        import bench
    man = man or load_manifest(a.manifest)
    es = entries(man, a.sizes, a.models, getattr(a, "modes", ""), getattr(a, "pin_adapt", ""))
    if not es:
        sys.exit("no benchmark runs selected")
    resolve = resolve or (lambda mid: resolve_model(bench, mid))
    slow = {}
    for s in a.inject_slow or []:
        k, _, f = s.rpartition("=")
        slow[k] = float(f)
    slow_for = lambda e: next((f for k, f in slow.items() if k in e["model"]), 1.0)
    cleanup = None
    if a.bin:
        binary = os.path.abspath(a.bin)
    else:
        cleanup = bench.build_release("tlx-bench-")
        binary = cleanup.__enter__()
    try:
        return _run_suite(a, bench, resolve, es, binary, slow_for)
    finally:
        if cleanup:
            cleanup.__exit__(None, None, None)


def _run_suite(a, bench, resolve, es, binary, slow_for):
    base_bin = os.path.abspath(a.base_bin) if a.base_bin else None
    bins = ([("base", base_bin)] if base_bin else []) + [("new", binary)]
    instr = perf_instructions_available() and not a.no_instructions
    rev = bench_machine.git_commit()
    out = a.out or os.path.join(HISTORY, f"{rev}.json")
    h = {"suite": True, "tla2tools": bench_machine.tla2tools_info(), "commit": rev, "date": time.strftime("%Y-%m-%d %H:%M:%S"), "machine": bench_machine.machine_desc(),
         "instructions": instr, "repeat": a.repeat, "sizes": a.sizes, "runs": {}}
    base = {"commit": a.base_rev or "unknown", "runs": {}} if base_bin else None
    if base:
        h["base"] = base
    deadline = time.time() + a.max_minutes * 60 if a.max_minutes else None
    inherited = bench_budget.current().remaining()
    limits = ([deadline] if deadline is not None else []) + ([time.time() + inherited] if math.isfinite(inherited) else [])
    budget = bench_budget.Budget(deadline_at=min(limits) if limits else None)
    h["samples"] = []
    skipped = []

    def save():
        h["budget"] = {"skipped": budget.skipped}
        os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
        json_update(out, lambda _: h)

    print(f"suite on {h['machine']}: {len(es)} runs, {a.repeat} repeats, "
          f"{'A/B against ' + base['commit'] if base else 'baseline (no previous revision)'}"
          f"{', instructions via perf' if instr else ''}", flush=True)
    def measure(e, m, repeats):
        def checkpoint(sample, samples):
            h['samples'].append({'entry': e['key'], **sample})
            for name, rs in samples.items():
                target = h['runs'] if name == 'new' else base['runs']
                if rs:
                    target[e['key']] = record_of(e, rs, [], expect_check=name == 'new')
            save()
        return measure_entry(bench, m, e, bins, repeats, instr, slow_for, budget=budget, checkpoint=checkpoint)

    for e in es:
        if budget.remaining() <= 0:
            skipped.append(e["key"])
            continue
        m = resolve(e["model"])
        recs = measure(e, m, a.repeat)
        if any(r.get("skipped") for r in recs.values()):
            skipped.append(e["key"])
        from benchmarking.baselines import content_digest
        recs["new"]["content_digest"] = content_digest(m) if m.get("tla") and m.get("cfg") else None
        recs["new"]["tlc_version"] = h["tla2tools"].get("revision")
        h["runs"][e["key"]] = recs["new"]
        if base:
            base["runs"][e["key"]] = recs["base"]
        show(e, recs)
        save()
    compare = lambda ra, rb: bench.compare_runs(ra, rb, metric="wall", threshold=a.threshold, max_noise=a.max_noise, min_delta=a.min_delta,
                                                  distinct_success_only=True)
    v = judge(base["runs"] if base else None, h["runs"], es, skipped, compare)
    # Retry once what is inconclusive or regressed (a noisy sample or a one-off
    # slow run), with two more repeats; the retry's samples are final.
    retry = sorted({r["key"] for r in v["regressions"] if r.get("ratio") is not None} | {r["key"] for r in v["inconclusive"]} - set(skipped))
    if base and retry:
        print(f"\nretrying {len(retry)} run(s) with {a.repeat + 2} repeats: {', '.join(retry)}", flush=True)
        for e in es:
            if e["key"] in retry and budget.remaining() > 0:
                recs = measure(e, resolve(e["model"]), a.repeat + 2)
                if any(r.get("skipped") for r in recs.values()):
                    skipped.append(e["key"])
                from benchmarking.baselines import content_digest
                m = resolve(e["model"])
                recs["new"]["content_digest"] = content_digest(m) if m.get("tla") and m.get("cfg") else None
                recs["new"]["tlc_version"] = h["tla2tools"].get("revision")
                h["runs"][e["key"]], base["runs"][e["key"]] = recs["new"], recs["base"]
                show(e, recs)
        v = judge(base["runs"], h["runs"], es, skipped, compare)
        v["retried"] = retry
    h["verdict"] = v
    h["range"] = commit_range(base["commit"], rev) if base and base["commit"] != "unknown" else []
    save()
    print_verdict(h, v)
    from benchmarking.legacy import ingest
    ingest(out)
    print(f"recorded in {os.path.relpath(out, ROOT)}")
    return exit_status(v)


def show(e, recs):
    new, base = recs["new"], recs.get("base")
    line = f"{e['key']:<86} min {new['min']:8.2f}s cpu {min((c or 0 for c in new['cpu']), default=0):8.2f}s {new['result']} {new['distinct']}"
    if base:
        line += f"  base {base['min']:8.2f}s  x{new['min'] / base['min'] if base['min'] else float('nan'):.3f}"
    if new.get("count_problems"):
        line += "  COUNT MISMATCH: " + "; ".join(new["count_problems"])
    print(line, flush=True)


# ---------------------------------------------------------------- trend

def load_history(directory=HISTORY):
    """The suite histories (bench/history/*.json with "suite"), oldest first."""
    hs = []
    if os.path.isdir(directory):
        for f in sorted(os.listdir(directory)):
            if not f.endswith(".json"):
                continue
            try:
                with open(os.path.join(directory, f)) as source:
                    h = json.load(source)
            except (OSError, ValueError):
                continue
            if isinstance(h, dict) and h.get("suite"):
                h["_file"] = f
                hs.append(h)
    return sorted(hs, key=lambda h: h.get("date", ""))


def fmt_s(x):
    return "-" if x is None else f"{x:.2f}" if x < 100 else f"{x:.0f}"


def trend_markdown(hists, last=6, man=None):
    """The historical trend view: the latest revision per model with speedup over
    TLC and change against the previous revision, then the wall time over the
    last revisions (same machine type only is comparable).

    This is not a report of record and no command writes it: the canonical
    report is `docs/performance.md` (`bench.py report`), and the suite history
    under `bench/history/` is what it is rendered from."""
    out = ["# Performance trend", "",
           "Generated by `scripts/bench.py suite-report` from `bench/history/*.json` (the suite runs of `scripts/bench.py track`; do not edit).",
           "Times are the minimum wall time of the repeats in seconds. `vs TLC` is TLC's 1-worker time from the TLC oracle "
           "(measured elsewhere, for scale only) divided by the run's time. Times of different machines are not comparable.", ""]
    if not hists:
        return "\n".join(out + ["No suite run recorded yet."]) + "\n"
    cur = hists[-1]
    prev = hists[-2] if len(hists) > 1 else None
    out += [f"Latest: `{cur['commit']}` ({cur['date']}), {cur['machine']}; verdict {cur.get('verdict', {}).get('outcome', '?')}"
            + (f" against `{cur['base']['commit']}`" if cur.get("base") else " (baseline)") + ".", ""]
    if prev:
        same = prev["machine"] == cur["machine"]
        out += [f"Previous recorded: `{prev['commit']}` ({prev['date']})" + ("" if same else ", **different machine: the change column is not meaningful**") + ".", ""]
    out += ["| size | model | mode | workers | wall s | cpu s | rss MiB | instr (G) | vs TLC | vs prev |", "|---|---|---|---:|---:|---:|---:|---:|---:|---:|"]
    speed = {}
    for k, r in sorted(cur["runs"].items(), key=lambda kv: (SIZES.index(kv[1]["tier"]) if kv[1]["tier"] in SIZES else 9, kv[0])):
        cpu = min((c for c in r.get("cpu") or [] if c), default=None)
        rss = statistics.median(x for x in r.get("rss_mib") or [] if x) if any(r.get("rss_mib") or []) else None
        ins = [x for x in r.get("instructions") or [] if x]
        ins = f"{min(ins) / 1e9:.1f}" if ins else "-"
        sp = r["tlc_1w_s"] / r["min"] if r.get("tlc_1w_s") and r["min"] else None
        if sp:
            speed.setdefault((r["tier"], r["mode"], r["workers"]), []).append(sp)
        ch = "-"
        if prev and prev["machine"] == cur["machine"] and k in prev["runs"] and prev["runs"][k]["min"]:
            ch = f"{r['min'] / prev['runs'][k]['min']:.2f}x"
        out.append(f"| {r['tier']} | {r['model']} | {r['mode']} | {r['workers']} | {fmt_s(r['min'])} | {fmt_s(cpu)} | "
                   f"{'-' if rss is None else f'{rss:.0f}'} | {ins} | {'-' if sp is None else f'{sp:.1f}x'} | {ch} |")
    out += ["", "Geometric mean of the speedup over TLC (1 worker) per size and mode:", "", "| size | mode | workers | models | geomean vs TLC |", "|---|---|---:|---:|---:|"]
    for (t, mode, w), xs in sorted(speed.items(), key=lambda kv: (SIZES.index(kv[0][0]) if kv[0][0] in SIZES else 9, kv[0][1], kv[0][2])):
        out.append(f"| {t} | {mode} | {w} | {len(xs)} | {geomean(xs):.1f}x |")
    shown = hists[-last:]
    out += ["", f"## Wall time over the last {len(shown)} recorded revisions (s)", "",
            "| model | mode | w | " + " | ".join(f"`{h['commit'][:8]}`<br>{h['date'][:10]}" for h in shown) + " |",
            "|---|---|---:|" + "---:|" * len(shown)]
    keys = sorted(cur["runs"], key=lambda k: (SIZES.index(cur["runs"][k]["tier"]) if cur["runs"][k]["tier"] in SIZES else 9, k))
    for k in keys:
        r = cur["runs"][k]
        out.append(f"| {r['model']} | {r['mode']} | {r['workers']} | " + " | ".join(fmt_s(h["runs"][k]["min"]) if k in h["runs"] else "-" for h in shown) + " |")
    machines = {}
    for h in shown:
        machines.setdefault(h["machine"], []).append(h["commit"][:8])
    out += ["", "Machines: " + "; ".join(f"{', '.join(cs)}: {m}" for m, cs in machines.items()), ""]
    flagged = [h for h in shown if h.get("verdict", {}).get("outcome") in ("REGRESSION", "INCONCLUSIVE")]
    if flagged:
        out += ["Runs with a non-passing verdict:", ""]
        for h in flagged:
            v = h["verdict"]
            names = [r["key"] for r in v.get("regressions", [])] + [f["key"] for f in v.get("count_failures", [])]
            out.append(f"- `{h['commit']}`: {v['outcome']}" + (f" ({', '.join(names)})" if names else ""))
        out.append("")
    return "\n".join(out)


def cmd_judge(a):
    """`suite-judge FILE`: the verdict of a recorded run again (e.g. with other thresholds); prints it, rewrites FILE with --write."""
    import bench
    with open(a.file) as source:
        h = json.load(source)
    compare = lambda ra, rb: bench.compare_runs(ra, rb, metric="wall", threshold=a.threshold, max_noise=a.max_noise, min_delta=a.min_delta,
                                                distinct_success_only=True)
    old = (h.get("verdict") or {}).get("outcome")
    v = judge((h.get("base") or {}).get("runs"), h["runs"], [], (h.get("verdict") or {}).get("skipped", []), compare)
    v["rejudged"] = {"from": old, "threshold": a.threshold, "max_noise": a.max_noise, "min_delta": a.min_delta}
    print_verdict(h, v)
    if a.write:
        h["verdict"] = v
        with open(a.file, "w") as f:
            json.dump(h, f, indent=1, sort_keys=True)
    return exit_status(v)


def cmd_report(a):
    from benchmarking.legacy import ingest
    from benchmarking.bench_records import generate
    for h in load_history(a.history):
        ingest(os.path.join(a.history, h["_file"]))
    generate(refresh=True)
    print("wrote docs/performance.md from canonical measurements")


# ---------------------------------------------------------------- track

def previous_recorded(rev, hists, is_ancestor=None):
    """The newest suite history before `rev` whose commit is an ancestor of it."""
    is_ancestor = is_ancestor or (lambda c, r: subprocess.run(["git", "merge-base", "--is-ancestor", c, r], cwd=ROOT, capture_output=True).returncode == 0)
    for h in reversed(hists):
        c = h["commit"].split("-dirty")[0]
        if c != rev[:len(c)] and is_ancestor(c, rev):
            return c
    return None


def remote_args(a, base):
    """The bench.py argument string of the remote run."""
    parts = ["suite", f"--sizes {a.sizes}", f"--repeat {a.repeat}", f"--max-minutes {a.max_minutes}"]
    if getattr(a, "deadline_min", None):
        parts.append(f"--deadline-min {a.deadline_min}")
    if getattr(a, "pin_adapt", ""):
        # The base binary is measured under the same pin in the same launch, so
        # both sides of the comparison are reproducible.
        parts.append(f"--pin-adapt {a.pin_adapt}")
    if a.models:
        parts.append(f"--models {a.models}")
    if base:
        parts.append(f"--base-bin target/bench-bins/base/tlx --base-rev {base}")
    for s in a.inject_slow or []:
        parts.append(f"--inject-slow {s}")
    return " ".join(parts)


def cloud_command(a, rev, base, args):
    cmd = [sys.executable, os.path.join(ROOT, "scripts", "cloud_verify.py"), rev, "--provider", a.provider, "--bench", args,
           "--max-minutes", str(a.max_minutes + a.setup_minutes)]
    if a.instance_type:
        cmd += ["--instance-type", a.instance_type]
    if base:
        cmd += ["--bench-bin", f"base={base}"]
    return cmd


def track_history(directory, rev, base):
    """The suite history file a receipt directory holds for this run, or None:
    `bench/history/<rev>.json`, the file the remote `bench.py suite` wrote, read
    back so its own `commit` and `base` are checked against the run. A history
    file of another revision (or another base) never gets recorded, whatever its
    file name is (HARNESS-06, HARNESS-12)."""
    hist = os.path.join(directory, "bench", "history")
    names = sorted(os.listdir(hist)) if os.path.isdir(hist) else []
    for name in names:
        if not name.endswith(".json"):
            continue
        try:
            with open(os.path.join(hist, name)) as source:
                h = json.load(source)
        except (OSError, ValueError):
            continue
        if not isinstance(h, dict) or not h.get("suite"):
            continue
        if not cloud_common.same_rev(h.get("commit"), rev):
            continue
        have = (h.get("base") or {}).get("commit")
        # A baseline run must carry no base; an A/B run must carry the requested one.
        matched = cloud_common.same_rev(have, base) if base else not have
        if matched:
            return os.path.join(hist, name)
    return None


def cmd_track(a):
    rev = git("rev-parse", "--short=12", a.rev)
    hists = load_history()
    base = None if a.base == "none" else previous_recorded(rev, hists) if a.base == "auto" else git("rev-parse", "--short=12", a.base)
    args = remote_args(a, base)
    cmd = cloud_command(a, rev, base, args)
    print(f"track {rev}: base {base or 'none (baseline)'}\n  " + " ".join(cmd), flush=True)
    if a.dry_run:
        return 0
    bins = [("base", base, "")] if base else []
    rc = subprocess.run(cmd, cwd=ROOT).returncode
    # A non-zero cloud_verify exit that is not a suite status produced no verdict
    # to record: a stale PASS file of an earlier run (or a partial copy this run
    # left behind) must not turn an infrastructure refusal, failure or the
    # deadline into a recorded pass (HARNESS-06).
    if not cloud_common.is_verdict_exit(rc):
        print(f"cloud_verify exited {rc}: not a suite status (0, 1 or 2), nothing recorded; "
              f"results and receipt, if any, stay in {BENCH_RESULTS}", file=sys.stderr)
        return 3
    d, _, problem = cloud_common.select_bench_receipt(BENCH_RESULTS, rev, bins, rc)
    if problem:
        print(f"cloud_verify exited {rc} but no receipt authorizes recording it: {problem}", file=sys.stderr)
        return 3
    src = track_history(d, rev, base)
    if not src:
        print(f"receipt {os.path.join(d, 'cloud.json')} holds no suite history for {rev}"
              + (f" (base {base})" if base else ""), file=sys.stderr)
        return 3
    print(f"track {rev}: receipt {os.path.relpath(d, ROOT)}, history {os.path.relpath(src, ROOT)}", flush=True)
    os.makedirs(HISTORY, exist_ok=True)
    dst = os.path.join(HISTORY, os.path.basename(src))
    shutil.copyfile(src, dst)
    with open(dst) as source:
        h = json.load(source)
    from benchmarking.legacy import ingest
    from benchmarking.bench_records import generate
    ingest(dst)
    generate(refresh=True)
    print(f"copied {os.path.relpath(dst, ROOT)}, regenerated docs/performance.md; commit history, records, baselines, policy and report")
    v = h.get("verdict") or {"outcome": "INCONCLUSIVE", "count_failures": [], "regressions": [], "inconclusive": [], "skipped": []}
    print_verdict(h, v)
    return exit_status(v) if h.get("verdict") else INCONCLUSIVE


# ---------------------------------------------------------------- CLI

def add_args(sub):
    p = sub.add_parser("suite-check", help="validate bench/suite.json")
    p.add_argument("--manifest", default=SUITE)
    p.add_argument("--oracle", action="store_true", help="compare tlc-oracle expectations with corpus/out")
    p = sub.add_parser("suite", help="run the benchmark suite (A/B against the previous recorded revision)")
    p.add_argument("--manifest", default=SUITE)
    p.add_argument("--sizes", default=DEFAULT_SIZES, help=f"comma-separated of {', '.join(SIZES)}, or all (default {DEFAULT_SIZES})")
    p.add_argument("--models", default="", help="only models whose id equals or contains one of these")
    p.add_argument("--modes", default="", help="only these run modes: default,compile,interp,tlc (default: all)")
    p.add_argument("--bin", default="", help="tlx binary under test (default: build target/release)")
    p.add_argument("--base-bin", default="", help="tlx binary of the previous recorded revision (A/B)")
    p.add_argument("--base-rev", default="", help="the revision of --base-bin (recorded, names the commit range)")
    p.add_argument("--repeat", type=int, default=3)
    p.add_argument("--max-minutes", type=int, default=0, help="stop starting new runs after M minutes (the rest is reported as skipped: inconclusive)")
    p.add_argument("--threshold", type=float, default=0.05)
    p.add_argument("--max-noise", type=float, default=0.25, help="maximum relative sample range; the ratio of the minima is robust "
                   "(identical binaries stayed within -5%%..+1.3%% on a cloud instance), so the gate is looser than bench.py compare's")
    p.add_argument("--min-delta", type=float, default=0.05)
    p.add_argument("--no-instructions", action="store_true", help="do not record retired instructions with perf")
    p.add_argument("--inject-slow", action="append", default=[], metavar="MODEL=FACTOR",
                   help="forced-regression test: the new binary's runs of models whose id contains MODEL take FACTOR times as long")
    p.add_argument("--pin-adapt", nargs="?", const="marked", default="", choices=["", "marked", "all"],
                   help="pin the adaptive tier chooser (TLX_MIXED_ADAPT=0) for compiled and default runs: "
                        "'marked' (the default when given) only for the manifest's tier-determined families, "
                        "'all' for every model. Recorded as configuration.env, so it is part of the run's key")
    p.add_argument("--out", default="", help="history file (default bench/history/<rev>.json)")
    p = sub.add_parser("suite-judge", help="judge a recorded run again")
    p.add_argument("file")
    p.add_argument("--threshold", type=float, default=0.05)
    p.add_argument("--max-noise", type=float, default=0.25)
    p.add_argument("--min-delta", type=float, default=0.05)
    p.add_argument("--write", action="store_true")
    p = sub.add_parser("suite-report", help="re-ingest bench/history and regenerate docs/performance.md")
    p.add_argument("--history", default=HISTORY)
    p = sub.add_parser("track", help="run the suite on a cloud instance and record it (the coordinator's command after merges)")
    p.add_argument("--rev", default="HEAD")
    p.add_argument("--base", default="auto", help="auto (the previous recorded revision), a revision, or none")
    p.add_argument("--sizes", default=DEFAULT_SIZES)
    p.add_argument("--models", default="")
    p.add_argument("--repeat", type=int, default=3)
    p.add_argument("--max-minutes", type=int, default=40, help="the suite's own budget (default 40)")
    p.add_argument("--setup-minutes", type=int, default=20, help="added to --max-minutes for the instance's dead-man switch (default 20)")
    p.add_argument("--provider", default="tencent")
    p.add_argument("--instance-type", default="")
    p.add_argument("--inject-slow", action="append", default=[], metavar="MODEL=FACTOR")
    p.add_argument("--pin-adapt", nargs="?", const="marked", default="", choices=["", "marked", "all"],
                   help="pin the adaptive tier chooser for compiled and default runs ('marked': the manifest's "
                        "tier-determined families; 'all': every model). Part of the run's key, so a pinned judgement "
                        "sits beside the adaptive one instead of moving it")
    p.add_argument("--dry-run", action="store_true")


def resolution_problems(man, available, *, examples_present=True):
    problems = []
    for m in man['models']:
        mid = m['id']
        if mid in available:
            continue
        if not examples_present and not mid.startswith(("bench/", bench_models.EXTERNAL_PREFIX)):
            continue
        problems.append(f"{mid}: benchmark model cannot be resolved from the corpus/stress manifests")
    return problems


def run_check(a):
    man = load_manifest(a.manifest)
    ids = [m["id"] for m in man["models"]]
    available = resolve_models(ids, stage=False)
    import corpus
    examples_present = os.path.isdir(os.path.join(corpus.EX, "specifications"))
    problems = resolution_problems(man, available, examples_present=examples_present)
    if problems:
        print("\n".join(problems))
        return 1
    n = len(entries(man, "all"))
    note = "" if examples_present else " (third_party/Examples absent; corpus resolution skipped)"
    print(f"{a.manifest}: {len(man['models'])} models, {n} runs{note}")
    if a.oracle:
        probs = oracle_problems(man, load_oracles())
        for p in probs:
            print("  " + p)
        if probs:
            return 1
    return 0


def dispatch(a):
    if a.cmd == "suite-check":
        sys.exit(run_check(a))
    if a.cmd == "suite":
        sys.exit(run_suite(a))
    if a.cmd == "suite-judge":
        sys.exit(cmd_judge(a))
    if a.cmd == "suite-report":
        return cmd_report(a)
    if a.cmd == "track":
        sys.exit(cmd_track(a))
