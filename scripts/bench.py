#!/usr/bin/env python3
"""Benchmarks of tlx: tiers of corpus models, a history per commit, and a
comparison that flags regressions; also the tlx-vs-TLC table, which can be
updated a subset of models at a time.

usage:
  scripts/bench.py tiers [--per-tier N]
      List the tiers and the models chosen for each.
  scripts/bench.py run [--tiers a,b,...] [--models id,...] [--modes compile,interp]
                       [--repeat R] [--per-tier N] [--timeout S] [--stats] [--tlc] [--out FILE]
                       [--external small,medium,...] [--workers 1,max] [--tlc-workers 1,max]
                       [--tlc-timeout S] [--resume]
      Run the tiers; record into bench/history/<commit>.json (merged with
      what is already there, so tiers can be run one at a time). With --tlc
      TLC is measured too (once per model and worker count, one JVM at a
      time; mode `tlc`, at 1 worker and at the tier's largest worker count,
      or --tlc-workers), so that `report` can compare against TLC on the
      same machine. --external runs the external models (corpus/external.json,
      ids ext/<repo>/<name>; --models may name them too) of these manifest
      tiers as bench tiers ext-<tier>; models without a TLC oracle result
      are checked against the TLC run of --tlc. --workers sets the tlx worker
      counts (max: the number of CPUs). Every tlx run's result kind and, for a
      complete search, distinct states are checked against TLC 1w (this
      run's, else the oracle). --resume skips the runs already recorded in
      the history file (TLC runs by model and worker count, whatever the
      tier), so that several invocations can share one file.
  scripts/bench.py report HISTORY [--top N] [--markdown]
      Speedups of a history file over TLC (needs a run with --tlc): per
      tier the geometric mean of TLC time / tlx time (min wall and CPU),
      the N models slowest relative to TLC, and the scaling of the
      multi-worker runs. --markdown: a table per model (TLC 1w and Nw, tlx
      interpreter 1w, -compile 1w and Nw, speedups, counts check), the
      geometric means per tier and per TLC 1w time bucket, and the models
      where -compile 1w is less than 3x faster than TLC (TLC >= 2 s).
  scripts/bench.py ab --bin NAME=PATH --bin NAME=PATH [...] --models id,...
                      [--args "-compile -workers 1"] [--env NAME:K=V] [--bin-args NAME:ARGS] [--hog N] [--repeat R]
                      [--timeout S] [--out FILE]
      A/B comparison of tlx binaries on the same models, interleaved (each
      round runs every model with every binary, the binaries' order
      rotating), after one discarded warm-up run per binary and model (C
      builds, page cache). Prints min/median CPU and wall, median peak RSS
      per binary and the ratios of median CPU and wall to the first
      binary's; --out writes every run as JSON. --env sets an environment
      variable for one binary's runs (the same PATH may be given twice
      under two names, e.g. to compare an allocator option), and
      --bin-args NAME:ARGS more tlx arguments (e.g. tlc:-tlc, to compare
      the default mode with -tlc on one binary); --hog N keeps
      N processes spinning (one core each) during the runs, to measure an
      oversubscribed machine. That is load the shared machine must not carry, so
      only a cloud instance may run it (cloud_verify.py sets TLX_CLOUD_HOST) and
      a local `--hog` is refused (section 1 of docs/cloud-verification.md).
      --stats adds `-stats json` to every run and
      records its search time, host region evaluations, value store
      operations and bytes and the states expanded again (restarts,
      resumes), with their medians and ratios in the summary. --interp runs
      every binary with the interpreter; --no-warmup skips the warm-up runs.
      TLC's times (the speedup table) come from --tlc-baseline or else from
      the keyed TLC baseline store for this machine type (never re-timed).
  scripts/bench.py perf --bin NAME=PATH [--bin NAME=PATH ...] --models id,... [--args "-workers 1"]
                        [--seconds S] [--freq HZ] [--timeout S] [--tlc] [--out DIR]
      Linux hardware profile (needs `perf`; installed with apt on a cloud
      host): per model and binary the counters of a whole run (`perf stat`:
      cycles, instructions, branch and cache misses) and the flat profile
      of its first S seconds (`perf report` by symbol), with --tlc also the
      counters of TLC -workers 1, as text files in DIR (default bench/perf/).
  scripts/bench.py layout --bin NAME=PATH [--bin NAME=PATH ...] [--models id,...] [--filter S]
                          [--args "-compile -workers 1"] [--jobs J] [--timeout S] [--out FILE]
      The compiled tier's start-up decisions over the corpus (default: every
      model of corpus/out/tlc.json), each binary once per model with
      `-stats json`: pre-run time and states, layout-miss restarts, resumed
      searches, restarts from scratch, fallbacks to dynamic values, total
      time and distinct states. Prints the sums per binary and every model
      whose counts differ from the first binary's; --out writes every run as
      JSON. J models run in parallel (default 1; the counts do not depend
      on it, the times do).
  scripts/bench.py compare A B [--threshold 0.05] [--min-delta 0.05] [--max-noise 0.05] [--metric wall|cpu]
      Compare two history files (commit ids or paths): per run the min
      wall (or CPU) time of B over A's; exit 0 for pass, 1 for regression,
      2 for inconclusive (no regression proved, but noisy/incomplete samples).
  scripts/bench.py suite | suite-check | suite-report | track
      Continuous performance tracking over the fixed suite bench/suite.json
      (A/B against the previous recorded revision, bench/history/<rev>.json;
      `track` runs it on one cloud instance): see
      scripts/benchmarking/bench_suite.py and docs/benchmarking.md.
      `suite`/`track --with-tlc-companion` also measure a same-instance `-tlc`
      twin of every default-mode run (same model, workers, arguments, environment
      and cache policy), so a reduced row has a like-for-like unreduced timing;
      the report pairs the two by model, instance, revision, workers, input
      digest and configuration.
  scripts/bench.py table
      Regenerate the fixed report docs/performance.md from the canonical
      records (bench/records); it measures nothing. Also the default without
      a subcommand. The report replaced the ad-hoc historical Markdown table,
      so the measurement options of that entry point are retired: passing
      --models, --filter, --workers, --timeout, --no-tlc, --measure-tlc,
      --repeat, --out, --tlc-baseline or --no-tier-columns is refused with
      the usage that replaces it (bench.py run / suite / track) instead of
      being silently ignored.
  scripts/bench.py tlcbase [--models id,...] [--filter S] [--slice I/N] [--workers 1,16]
                           [--no-large] [--timeout 1800] [--force] [--out FILE]
      The TLC baseline: TLC alone on every corpus model (corpus/out/tlc.json
      plus the large tier of the manifests, runtime 61-700s, which has no
      oracle), once per worker count, one JVM at a time, as the oracle runs
      it (scripts/tlc.py; simulations with seed 1). Records per run the
      process wall time, TLC's own "Finished in" time, CPU time and peak RSS
      of the JVM, the counts and the result (timeouts as such), with the
      machine, JVM version and default heap, and tla2tools.jar's revision,
      into bench/history/tlc-<tla2tools rev>[-sliceIofN].json (resumable:
      runs already there are skipped unless --force). --slice I/N runs the
      I-th of N slices of about equal estimated time (oracle times), for
      several machines in parallel.
  scripts/bench.py tlcbase-merge OUT IN... [--set K=V]
      Merge baseline slices into one file (--set adds header fields, e.g.
      instance_type=ecs.c8y.4xlarge).
  scripts/bench.py tlcbase-report FILE [--top N]
      A baseline's totals, time distribution and timeouts per worker count,
      the N slowest models, and the runs whose results or counts differ
      from the oracle (corpus/out/tlc.json).
  scripts/bench.py scale [--models id,...] [--workers 1,16,64,128,max] [--tlc-workers LIST]
                         [--tlc-1w all|none|id,...] [--no-tlc] [--tlc-mem 0.4] [--repeat 2] [--repeat-1w 1]
                         [--stats] [--timeout 3600] [--tlc-timeout S] [--force] [--out FILE]
      Many-core scaling on large models (default SCALE_DEFAULT: >= 20M
      distinct states; bench/<name> ids are bench/scaling/<name>.cfg, larger
      constants of a corpus spec): per model a warm-up run (tlx -compile at
      the most workers, C library built synchronously; its counts are
      checked too), then tlx -compile (default tiering, warm cache) at each
      worker count (min of --repeat runs, --repeat-1w at 1 worker), then
      TLC at each --tlc-workers count (one JVM at a time; the 1-worker run
      only for the --tlc-1w models) with -Xmx and -XX:MaxDirectMemorySize
      of --tlc-mem times the physical memory (TLC's off-heap fingerprint
      set; -fpmem stays at TLC's default). Records the machine with its
      topology (sockets, cores, SMT, NUMA from lscpu), the JVM and every
      run into bench/history/scale-<commit>.json (resumable: runs already
      there are skipped unless --force) and prints scale-report.
  scripts/bench.py scale-report FILE [--tlc-baseline FILE]
      Markdown of a scaling file: per model and worker count the wall
      times of tlx and TLC, tlx's speedup over TLC at the same count, the
      parallel efficiency of each (T1 / (w * Tw); TLC relative to its
      smallest measured count without a 1-worker run), the counts check
      (every tlx run against TLC), and geometric means.
  scripts/bench.py disk --models id,... [--bin NAME=PATH]... [--workers N] [--plan ITEMS]
                        [--ref-mib ID=MIB] [--env NAME:K=V] [--timeout S] [--tlc-timeout S] [--out FILE]
      State spaces beyond memory (scripts/benchmarking/bench_disk.py; its module doc
      lists the plan items): tlx in memory (peak RSS P), with -maxmem F*P,
      in a control group of F*P (a machine with that much memory, page
      cache included; cgroup v2 and sudo), and TLC with the same memory.
      Samples RSS, process I/O bytes, the control group's memory, spill
      directory size and progress once a second; checks counts; records
      bench/history/disk-<commit>.json and prints a Markdown report.
  scripts/bench.py profile --models id[@interp],... [--workers 1,4,8,16] [--record W,...]
                           [--c2c MODEL@W] [--bin PATH] [--dir bench/profile]
      Where the time per state goes as the worker count grows: per model
      and worker count a run under `perf stat` (Linux; installed on a
      cloud host), a -stats run (sampled with `perf record` at --record),
      the symbols whose samples per state grew most, annotated
      (scripts/benchmarking/bench_profile.py).
  table/report/ab --tlc-baseline FILE
      Take the TLC side from a baseline file instead of running TLC (table:
      the TLC 1w and Nw columns; report: instead of the history's TLC runs;
      ab: TLC's time and the speedup of each binary at the -workers of
      --args). FILE is a path or a bench/history name prefix (tlc-1813307).
      Meaningful only on the baseline's machine type (a warning otherwise).

Ordinary tiers (chosen from corpus/out/tlc.json by TLC's 1-worker wall time and
by features found in the .cfg; the N models of a tier are spread evenly
over its range of TLC times, so the choice is deterministic):
  startup    TLC < 1s: tlx start-up (front end, pre-run, C build/dlopen)
  medium     TLC 1-15s
  large      TLC 15-150s (compiled tier only by default)
  scaling    >= 100k distinct states, compiled tier with 1/4/8/18 workers
             (capped at the number of cores)
  liveness   temporal PROPERTYs (cfg has PROPERTY/PROPERTIES)
  symmetry   cfg has SYMMETRY
  simulation -simulate / -generate models (fixed seed)
  stress     fixed ClockSettles liveness and full MultiPaxos_MC layout cases
             (compiled, 1 worker; not sampled by TLC time or --per-tier)
Each tier runs in modes `compile` (tlx -compile) and `interp` (tlx -interp,
the interpreter) unless restricted (--modes) or the tier says otherwise;
`--modes default` runs without a tier flag (the compiled tier).

A run of a model is repeated R times (default 3); its record keeps every
wall time, the min and median, CPU time (user+sys of the child), the
distinct states and the result, and the load average around it. With
--stats a further run with `-stats json=...` records tlx's own breakdown
(phases, time per category, fallbacks; see `tlx -stats`).

Comparison: for each run key (tier:model:mode:workers),
ratio = min(B) / min(A) (wall times, or CPU times with --metric cpu:
multi-worker CPU time includes spinning, so prefer wall on an idle
machine). Noise is the relative range of its repeats ((max - min) / min),
including isolated slow samples. Noise above --max-noise (default 0.05),
fewer than three samples, unequal sample counts, missing keys/metric samples,
and unfinished runs are inconclusive: re-run on an idle machine. Noise never
widens the regression threshold: a regression is a ratio above 1 + threshold
with an absolute slowdown above --min-delta seconds; improvements likewise.
A changed number of distinct states is always flagged as a regression, even
with inconclusive timings. Regression takes precedence over inconclusive in
the exit status. Per tier the geometric mean of conclusive ratios is printed.

Benchmarks of record need an idle machine (check `uptime`); otherwise
compare CPU times, or mark the numbers as taken under load.

The machine is recorded as architecture, CPU model and core count, plus
TLX_BENCH_MACHINE when set (e.g. the cloud instance type, which
scripts/cloud_verify.py --bench sets).

Environment: TLX_JAVA (see scripts/tlc.py); TLX_* variables are passed on
to tlx.
"""
from benchmarking import measurement as bench_measure
from benchmarking import models as bench_models, machine as bench_machine
# load_records stays imported here: the A/B pass reads it through this module
# (bench.load_records), which is the patch point its tests replace it at.
from benchmarking.records import load_records  # noqa: F401
from benchmarking import cli as bench_cli
import tempdirs

from benchmarking import bench_budget

import json, math, os, re, shutil, statistics, subprocess, sys, tempfile, time

from tlxlib import ROOT, TP, load_oracle, geomean, interp_args, run_proc, build_tlx
HISTORY = os.path.join(ROOT, "bench", "history")
from tlc import parse


# Running as a script this module is `__main__`; the subcommand passes in
# `benchmarking/commands/` reach the shared helpers through it (`bench.tlx`) and
# a test patches a pass in through it, so publish it under its import name
# first: without that, the first lazy `import bench` inside a pass would load a
# second, identical copy of every global (HARNESS-03, duplicate module
# identity).

# Running as a script this module is `__main__`; the subcommand passes in
# `benchmarking/commands/` reach the shared helpers through it (`bench.tlx`) and
# a test patches a pass in through it, so publish it under its import name
# first: without that, the first lazy `import bench` inside a pass would load a
# second, identical copy of every global (HARNESS-03, duplicate module
# identity).
if __name__ == "__main__":
    sys.modules.setdefault("bench", sys.modules[__name__])

# The subcommand passes live in `benchmarking/commands/`, and their names stay
# importable from here: this module is the namespace a pass reaches its
# collaborators through and the surface the other bench_*.py modules read
# (`bench.mode_args`, `bench.build_release`, `bench.HISTORY`).
from benchmarking.commands.ab import (_ab_samples, _ab_summary, _ab_warmup_failure, cmd_ab,
                                      measured_costs, run_stats)
from benchmarking.commands.layout import cmd_layout
from benchmarking.commands.run import cmd_run, run_bench, run_problems, sample_problem
# The rendering, comparison and history-file helpers live in libraries of their
# own now (benchmarking/report.py, benchmarking/commands/*.py); they stay
# importable from here, because this module is the namespace the passes, the
# drivers and the tests reach them through (`bench.counts_check`,
# `bench.compare_runs`, `bench.load_tlc_baseline`, `bench.SCALE_KIND`) -- and the
# name a test replaces one at, which is why the moved passes call them through
# it too (HARNESS-03, duplicate module identity).
from benchmarking.report import (INCOMPLETE, TIME_BUCKETS, TLC_MODE, best, compare_runs,
                                 comparison_samples, counts_check, merge_rows, ok_result, parse_table,
                                 render_row, report_markdown, scale_counts, scale_report, table_cells,
                                 table_columns, table_header, upgrade_rows)
from benchmarking.commands.history import cmd_compare, cmd_history_report
from benchmarking.commands.tlcbase import (TLCBASE_KIND, TLC_MS_PROP, _collect_tlc_measured, cmd_tlcbase,
                                           cmd_tlcbase_merge, cmd_tlcbase_report, load_tlc_baseline,
                                           measured_jvm_options, tlc_measured, tlc_mismatch, tlcbase_estimate,
                                           tlcbase_models, tlcbase_slices, workers_list)
from benchmarking.commands.scale import SCALE_KIND, cmd_scale, cmd_scale_report, run_scale, scale_runs


def read_json(path, default=None):
    """The JSON of `path`, or `default` when it is absent; the handle is always
    closed (an unclosed `open()` is a ResourceWarning, and the drivers escalate
    warnings to errors)."""
    try:
        with open(path) as stream:
            return json.load(stream)
    except FileNotFoundError:
        return default


def tlx_cmd(m, args, exe=None):
    binary = exe or bench_machine.TLX
    bench_machine.require_fresh(binary)
    return bench_measure.check_argv(binary, m, args)


@bench_budget.model_pass
def tlx(m, args, timeout, exe=None, env=None, wrap=(), raw=False):
    """One run of tlx (binary `exe`, default target/release/tlx; extra
    environment `env`): the parsed result with wall and CPU time and the
    peak resident memory (MiB). `wrap`: a command prefix (e.g. perf stat).

    `raw`: also keep the child's exact output and exit code under `raw`, for a
    run whose parsed verdict alone would hide a crash (bpa-abi: an exit-101
    panic printed `unknown/None` and looked like a missing performance sample).
    The child runs with `rusage=True`, which folds its stderr into stdout, so
    `output` is the whole stream and `stderr` is kept only for callers that do
    not use rusage."""
    # (A model that writes files gets a scratch copy of its spec directory.)
    exe = bench_measure.binary_path(exe)
    with bench_measure.staged_run(m, "tlx-bench-") as (m, cwd, _):
        p = run_proc([*wrap, *tlx_cmd(m, args, exe)], timeout, cwd=cwd, env=bench_measure.measured_env(env),
                     rusage=True, raise_timeout=False, start_new_session=True)
        # (The child's own deadline result: a run killed by anything else - the
        # OOM killer - is not a timeout, and a run that failed at its own pace
        # after the deadline is not one either.)
        r = bench_measure.result_of(p, timeout)
        if raw:
            r["raw"] = {"output": p.stdout, "stderr": p.stderr, "exit": p.returncode}
    ru = p.rusage
    r["cpu_s"] = bench_measure.cpu_seconds(ru)
    r["maxrss_mib"] = bench_measure.rss_mib(ru)
    return r


@bench_budget.model_pass
def _collect_tlc(m, workers, timeout):
    """One run of TLC on model `m` with `workers` (and the model's simulation
    flags, seed 1): the parsed result with wall and CPU time and peak RSS.

    The CPU time and peak RSS are this child's own wait4 usage. A process-wide
    RUSAGE_CHILDREN delta around the call would fold in every other child
    reaped meanwhile, and bench_ttfr runs its lanes in parallel (HARNESS-09)."""
    from tlc import tlc_cmd
    args = ["-config", m["cfg"], "-workers", str(workers)]
    if m.get("flags"):
        args += m["flags"] + ["-seed", "1"]
    args += bench_models.oracle_tlc_args(m)
    spec = os.path.abspath(m["tla"])
    with bench_measure.staged_tlc_run(m) as (cwd, module):
        cmd = tlc_cmd(spec, args, m.get("features") or (), module=module)
        p = run_proc(cmd, timeout, cwd=cwd, rusage=True, raise_timeout=False, start_new_session=True)
    r = bench_measure.result_of(p, timeout)
    if not p.timed_out:
        # (This child's own CPU and peak RSS; a timed-out run is recorded
        # without them, as before: the record's usage is unmeasured rather
        # than a partial number.)
        r["cpu_s"] = bench_measure.cpu_seconds(p.rusage)
        r["maxrss_mib"] = bench_measure.rss_mib(p.rusage)
    return r


def tlc(m, workers, timeout):
    from benchmarking.baselines import cached_tlc
    return cached_tlc(m, workers, lambda: _collect_tlc(m, workers, timeout))


def mode_args(mode, workers, m, exe=None):
    """Select the execution tier, including older A/B binaries."""
    a = ["-workers", str(workers)]
    if mode == "compile":
        a.append("-compile")
    elif mode == "tlc":
        a.append("-tlc")
    elif mode == "interp":
        a += interp_args(exe or bench_machine.TLX)
    return a + bench_models.bench_flags(m)


def _lane_file(name):
    """Per-slice TLC baseline file, named `<baseline>-lane<slice>.json`."""
    return bool(re.search(r"-lane[^/]*\.json$", name))


def history_path(x):
    if os.path.exists(x):
        return x
    p = os.path.join(HISTORY, f"{x}.json")
    if os.path.exists(p):
        return p
    cands = sorted(f for f in os.listdir(HISTORY) if f.startswith(x)) if os.path.isdir(HISTORY) else []
    # A baseline may exist both as its canonical file and as per-slice lane files
    # (`tlc-<ver>-lane<s>.json`). Prefer the canonical file, but never guess
    # between lanes: several lane files matching one name stay an error.
    primary = [f for f in cands if not _lane_file(f)]
    cands = primary or cands
    if len(cands) == 1:
        return os.path.join(HISTORY, cands[0])
    sys.exit(f"no (unique) history file for {x}")


def cmd_tiers(a):
    sel = bench_models.select(list(bench_models.TIERS), a.per_tier)
    d = bench_models.oracle([k for ks in sel.values() for k in ks])
    for t, ks in sel.items():
        desc, modes, workers = bench_models.TIERS[t]
        print(f"{t}: {desc}; modes {','.join(modes)}; workers {','.join(map(str, workers))}")
        for k in ks:
            wall = d[k]["tlc"].get("wall_s")
            timing = f"{wall:8.2f}s" if wall is not None else "unmeasured"
            print(f"  {k:<60} TLC {timing}  {d[k]['tlc'].get('distinct') or '-'} states")


def build_release(prefix):
    """build_tlx of the release binary (benchmarks never use the fast profile).
    cloud_verify.py --bench runs this file with an older revision's tlxlib,
    whose build_tlx has no `profile` and builds release by default."""
    try:
        return build_tlx(profile="release", prefix=prefix)
    except TypeError:
        return build_tlx(prefix=prefix)


# A discarded run that builds the C library synchronously, so that the timed
# runs after it find it in the cache.
WARMUP_ENV = {"TLX_NATIVE_SYNC": "1"}


def wait_builds(cache):
    """Wait for the C builds still running in TLX_CACHE directory `cache`
    (started by a tlx run that has exited): each holds the advisory lock of
    its slot's build.lock (tlx-native/src/build.rs)."""
    import fcntl
    for d, _, files in os.walk(cache):
        if "build.lock" in files:
            with open(os.path.join(d, "build.lock"), "a") as f:
                fcntl.flock(f, fcntl.LOCK_EX)
                fcntl.flock(f, fcntl.LOCK_UN)


def tlx_cold(m, args, timeout, exe=None, env=None):
    """One run of tlx with an empty TLX_CACHE (as a user's first run), then
    waiting for its background C build outside the measured time."""
    cache = tempdirs.mkdtemp(prefix="tlx-bench-cold-")
    try:
        r = tlx(m, args, timeout, exe=exe, env={**(env or {}), "TLX_CACHE": cache})
        wait_builds(cache)
    finally:
        shutil.rmtree(cache, ignore_errors=True)
    return r


def cmd_table(a):
    from benchmarking.bench_records import generate
    generate()
    print("table is now the fixed docs/performance.md; record new measurements via bench.py suite/track")


def perf_report(budget, key, perf, data, timeout=900, estimate=120):
    """The flat profile of one perf record file, as text: `perf report` is a
    child of its own, so it goes through the shared deadline like the measured
    passes (HARNESS-08); a refusal or a failure returns a note instead."""
    seconds = budget.admit(key, timeout, estimate=estimate)
    if seconds is None:
        return "perf report skipped: benchmark deadline\n"
    try:
        p = subprocess.run([perf, "report", "-i", data, "--stdio", "--no-children", "--sort", "dso,symbol", "--percent-limit", "0.2"],
                           capture_output=True, text=True, timeout=seconds)
        return p.stdout
    except (OSError, subprocess.TimeoutExpired) as error:
        return f"perf report failed: {error}\n"


def cmd_perf(a):
    """Hardware counters (perf stat) and a flat profile (perf record) of tlx
    runs, per binary and model, and optionally the counters of TLC on the
    same models, into --out (default bench/perf/)."""
    from benchmarking import bench_profile
    perf = bench_profile.ensure_perf()
    if not perf:
        sys.exit("perf is not available")
    bins = []
    for b in a.bin:
        name, _, path = b.partition("=")
        if not name or not path or not os.access(os.path.abspath(path), os.X_OK):
            sys.exit(f"--bin expects NAME=PATH of an executable, got {b!r}")
        bins.append((name, os.path.abspath(path)))
    keys = [k.strip() for k in a.models.split(",") if k.strip()]
    d = bench_models.oracle(keys)
    for k in keys:
        if k not in d:
            sys.exit(f"unknown model {k}")
    out = a.out or os.path.join(ROOT, "bench", "perf")
    os.makedirs(out, exist_ok=True)
    events = "task-clock,cycles,instructions,branches,branch-misses,cache-references,cache-misses,L1-dcache-loads,L1-dcache-load-misses"
    env = bench_measure.measured_env()
    budget = bench_budget.current()

    def measured_cmd(k, exe):
        # (Built only when a pass is admitted: tlx_cmd may rebuild a stale binary.)
        return tlx_cmd(d[k], a.args.split() + bench_models.bench_flags(d[k]), exe)

    print(f"perf on {bench_machine.machine_desc()}: {perf}; {', '.join(f'{n}={p}' for n, p in bins)}; args {a.args}", flush=True)
    for k in keys:
        slug = k.replace("/", "_")
        for n, exe in bins:
            # (HARNESS-08: every perf pass is admitted through the one deadline
            # budget; a refused pass is named and skipped, never started - not
            # even the tlx_cmd path, which may rebuild a stale binary.)
            # (SIGINT: perf stops the run and still writes its output.)
            key = f"perf:{slug}:{n}"
            stat = os.path.join(out, f"{slug}.{n}.stat.txt")
            seconds = budget.admit(key, a.timeout)
            if seconds is None:
                print(f"  {k} {n}: stat skipped (deadline)", flush=True)
            else:
                p = run_proc(["timeout", "-s", "INT", str(seconds), perf, "stat", "-e", events, "-o", stat, "--"] + measured_cmd(k, exe), seconds + 60,
                             env=env, raise_timeout=False)
                budget.observe(key, p.wall)
            data = os.path.join(out, f"{slug}.{n}.data")
            seconds = budget.admit(key, a.seconds)
            if seconds is None:
                print(f"  {k} {n}: record skipped (deadline)", flush=True)
            else:
                run_proc(["timeout", "-s", "INT", str(seconds), perf, "record", "-F", str(a.freq), "-o", data, "--"] + measured_cmd(k, exe), seconds + 60,
                         env=env, raise_timeout=False)
                with open(os.path.join(out, f"{slug}.{n}.report.txt"), "w") as f:
                    f.write(perf_report(budget, f"{key}:report", perf, data))
                if os.path.exists(data):
                    os.remove(data)
            print(f"  {k} {n}: done", flush=True)
        if a.tlc:
            from tlc import tlc_cmd
            seconds = budget.admit(f"perf:{slug}:tlc", a.timeout)
            if seconds is None:
                print(f"  {k} tlc: stat skipped (deadline)", flush=True)
                continue
            with tempfile.TemporaryDirectory(prefix="tlx-perf-tlc-") as tmp:
                spec_dir = os.path.join(tmp, "spec")
                shutil.copytree(os.path.dirname(d[k]["tla"]), spec_dir)
                # (-Xmx given: the heap guard would insert it after perf.)
                cmd = tlc_cmd(d[k]["tla"], ["-workers", "1", "-config", os.path.basename(d[k]["cfg"])], d[k].get("features") or [],
                              jvm_extra=["-Xmx" + (os.environ.get("TLX_TLC_XMX") or "8g")], state_dir=os.path.join(tmp, "states"))
                stat = os.path.join(out, f"{slug}.tlc.stat.txt")
                run_proc(["timeout", "-s", "INT", str(seconds), perf, "stat", "-e", events, "-o", stat, "--"] + cmd, seconds + 60,
                         cwd=spec_dir, raise_timeout=False)
            print(f"  {k} tlc: done", flush=True)
    print(f"recorded in {out}")


def finish_bench(result):
    return result or int(bool(bench_budget.current().failures or bench_budget.current().skipped))


def main():
    argv = sys.argv[1:]
    # Cloud verification runs bench commands; keep the census implementation
    # and argument contract in coverage.py, with this single forwarding entry.
    if argv and argv[0] == "coverage":
        import coverage
        return coverage.main(argv[1:])
    ap, a = bench_cli.parse_args(argv, __doc__)
    try:
        bench_budget.configure(a)
    except ValueError as error:
        ap.error(str(error))
    # Any spinning process is artificial load on a machine many agents share, so
    # the boundary is zero, not "a few": the policy owner is section 1 of
    # docs/cloud-verification.md, and only a cloud instance may oversubscribe
    # itself (cloud_verify.py sets the marker). Refused here, before the smoke
    # path and before anything is built, so a refusal creates no load (HARNESS-20).
    if getattr(a, "hog", 0) > 0 and os.environ.get("TLX_CLOUD_HOST") != "1":
        sys.exit("STOP: local --hog is refused (artificial load on a shared machine); "
                 "measure oversubscription on cloud_verify.py")
    # Before the smoke/preflight path too: a retired option is refused however the
    # subcommand is reached, not only through the direct handler.
    bench_cli.refuse_retired_table_options(a)
    if a.cmd in ("report", "migrate"):
        from benchmarking import bench_records
        if a.cmd == "migrate":
            # The command's entry, not the library transaction: migration writes
            # the store, so a checkout that has none is refused before that
            # (bench_records.migrate_command).
            records = bench_records.migrate_command()
            bench_records.generate()
            print(f"migrated {len(records)} measurements; original records retained")
        elif a.check:
            errors = bench_records.check()
            print("\n".join(errors) if errors else "performance report: 0 problems")
            return int(bool(errors))
        else:
            bench_records.generate(refresh=a.refresh_ages)
        return 0
    if a.smoke:
        from benchmarking import bench_smoke
        return bench_smoke.run(a)
    # The subcommand modules this dispatch names; bench_cli.build_parser imports the
    # same ones for their arguments, and a subcommand neither list has is unreachable.
    from benchmarking import bench_disk
    from benchmarking import bench_liveness
    from benchmarking import bench_profile
    from benchmarking import bench_suite
    from benchmarking import bench_ttfr
    if a.cmd in ("suite", "suite-check", "suite-report", "suite-judge", "track"):
        return finish_bench(bench_suite.dispatch(a))
    result = {"tiers": cmd_tiers, "run": cmd_run, "compare": cmd_compare, "history-report": cmd_history_report, "ab": cmd_ab, "perf": cmd_perf,
              "layout": cmd_layout, "table": cmd_table,
              "tlcbase": cmd_tlcbase, "tlcbase-merge": cmd_tlcbase_merge, "tlcbase-report": cmd_tlcbase_report, "scale": cmd_scale,
              "scale-report": cmd_scale_report, "liveness": bench_liveness.run, "disk": bench_disk.run,
              "profile": bench_profile.run, "ttfr": bench_ttfr.run, "ttfr-report": bench_ttfr.run_report}[a.cmd](a)
    return finish_bench(result)


if __name__ == "__main__":
    sys.exit(main())
