"""`bench.py tlcbase`, `tlcbase-merge` and `tlcbase-report`: the TLC baseline.

TLC measured once per machine type, keyed in the record store and reused as the
TLC side of table/report/ab (--tlc-baseline FILE). `benchmarking/cli.py` owns the
parser and `scripts/bench.py` dispatches; the pass lives here (CODE-03), reaching
the helpers that stay in the entry point (`bench.read_json`, `bench.history_path`,
`bench.HISTORY`, `bench.tlcbase_models`, `bench.tlc_measured`, `bench.run_proc`)
through it: those are the names a test replaces, and the entry point publishes
itself under its import name (HARNESS-03).
"""
import json, os, re, shutil, sys, time

from benchmarking.records import COMPLETE
from benchmarking import bench_budget
from benchmarking import measurement as bench_measure
from benchmarking import machine as bench_machine, models as bench_models
from tlc import parse
from tlxlib import ROOT, TP, TLC_JVM_DEFAULT_HEAP, heap_pinned

# ---- TLC baseline (tlcbase): TLC measured once per machine type, reused as
# the TLC side of table/report/ab (--tlc-baseline FILE).

TLCBASE_KIND = "tlc-baseline"
# TLC prints "Finished in <ms>ms" with this property (human-readable minutes and
# seconds otherwise); it changes nothing else.
TLC_MS_PROP = "-Dtlc2.TLC.asMilliSeconds=true"
DEFAULT_TIMEOUT_S = 1800


def _suite_timeouts():
    """Map suite model ids to their manifest `timeout_s`, or {} if manifest is absent."""
    from benchmarking.bench_suite import SUITE, load_manifest
    if not os.path.isfile(SUITE):
        return {}
    return {m["id"]: m["timeout_s"] for m in load_manifest(SUITE)["models"]}


def model_timeout(mid, explicit_timeout, suite_timeouts=None):
    """Per-model TLC timeout: explicit --timeout, else manifest timeout_s, else 1800s."""
    if explicit_timeout is not None:
        return explicit_timeout
    if suite_timeouts is None:
        suite_timeouts = _suite_timeouts()
    return suite_timeouts.get(mid, DEFAULT_TIMEOUT_S)


def classify_baseline(entry, *, timeout, min_repetitions=1):
    """Classify a stored TLC baseline entry for `tlcbase --missing`.

    Returns `'satisfied'` (reusable with >= `min_repetitions` samples),
    `'bounded-timeout'` (stored timeout whose measured `wall_s >= timeout`),
    `'tlc-error'` (stored non-reusable `error`), or `'unmeasured'`.
    """
    from benchmarking.baselines import completed_repetitions, reusable
    if entry is None:
        return "unmeasured"
    if reusable(entry):
        return "satisfied" if completed_repetitions(entry) >= min_repetitions else "unmeasured"
    m = entry["measurement"]
    result = (m.get("counts") or {}).get("result")
    if result == "timeout":
        wall = (m.get("metrics") or {}).get("wall_s") or 0
        return "bounded-timeout" if wall >= timeout else "unmeasured"
    if result == "error":
        return "tlc-error"
    return "unmeasured"



def workers_list(s):
    return [int(w) for w in str(s).split(",") if w.strip()]



def tlcbase_models(a):
    """The models of a baseline run: {id: model}, every model of the oracle
    (corpus/out/tlc.json) plus, unless --no-large, the large tier (manifest
    runtime --large-min..--large-max seconds, no oracle results), narrowed by
    --models / --filter and --slice."""
    import corpus
    requested = a.models.split(",") if a.models else []
    if getattr(a, "missing", False) and not requested:
        from benchmarking.bench_suite import load_manifest
        requested = [m["id"] for m in load_manifest()["models"] if not a.no_large or m["size"] in ("small", "medium")]
    d = bench_models.oracle(requested)
    for mid in requested:
        if mid not in d:
            try:
                d.update(bench_models.scale_models([mid]))
            except (SystemExit, KeyError):
                pass
    if requested and not a.models:
        d = {k: v for k, v in d.items() if k in requested}
    ms = {k: {**m, "source": "corpus"} for k, m in d.items()}
    if not a.no_large:
        for m in corpus.models(a.large_max, a.large_min):
            ms.setdefault(m["id"], {**m, "source": "large", "tlc": {}})
    if a.models:
        keys = [k.strip() for k in a.models.split(",") if k.strip()]
        missing = [k for k in keys if k not in ms]
        if missing:
            sys.exit(f"unknown model(s): {', '.join(missing)}")
    else:
        keys = sorted(ms)
    keys = [k for k in keys if a.filter in k]
    if a.slice:
        try:
            i, n = bench_budget.parse_slice(a.slice)
        except ValueError as e:
            sys.exit(str(e))
        timeout = a.timeout if a.timeout is not None else DEFAULT_TIMEOUT_S
        suite_timeouts = None if a.timeout is not None else _suite_timeouts()
        keys = tlcbase_slices({k: ms[k] for k in keys}, n, timeout, workers_list(a.workers),
                              timeouts=suite_timeouts)[i - 1]
    return {k: ms[k] for k in keys}



def tlcbase_estimate(m, timeout, workers):
    """Expected seconds of a model's baseline runs (for balancing slices):
    the oracle's 1-worker wall time times 1.5 (the cloud core is slower) or,
    without one, 3× the manifest runtime; a quarter of that (at least 1.5s
    of JVM start-up) for each multi-worker run; each capped at the timeout."""
    import corpus
    w = (m.get("tlc") or {}).get("wall_s")
    one = min(timeout, 1.5 * w if w else 3 * corpus.secs(m.get("runtime")))
    return sum(one if n == 1 else min(timeout, max(1.5, one / 4)) for n in workers)



def tlcbase_slices(ms, n, timeout, workers, *, timeouts=None):
    """`ms` ({id: model}) split into `n` lists of about equal estimated time
    (longest first onto the least loaded slice; deterministic), each in id
    order."""
    def est(k):
        t = timeouts.get(k, timeout) if timeouts else timeout
        return tlcbase_estimate(ms[k], t, workers)
    return bench_budget.balance_slices(ms, n, est)



def measured_jvm_options(jvm_extra=(), default_heap=True):
    """The JVM options of a measured TLC run: `jvm_extra`, plus the request for
    the JVM's default heap when the caller pinned no heap and `default_heap`.
    Every measured TLC run wants the default heap (the oracle's method); only a
    driver that measures a specific heap (bench.py scale/ab) pins one, and then
    its `-Xmx` is what the run and its baseline key are about."""
    opts = list(jvm_extra)
    if default_heap and not heap_pinned(opts):
        opts.append(TLC_JVM_DEFAULT_HEAP)
    return opts


@bench_budget.model_pass



def _collect_tlc_measured(m, workers, timeout, jvm_extra=(), default_heap=True):
    """One TLC run of the baseline, as the oracle runs TLC (scripts/tlc.py:
    same JVM options and TLC flags; the model's simulation flags with seed 1)
    plus TLC's own run time in milliseconds: the parsed result with process
    wall time, TLC's "Finished in" time (finished_s), CPU time (user+sys of
    the JVM), peak RSS and TLC's description of its memory, fingerprint set
    and queue (tlc_memory). A run killed at `timeout` has result "timeout"
    and its last progress report under "at_timeout". `jvm_extra`: further
    JVM options (e.g. -Xmx; it wins over `default_heap`)."""
    import bench
    from tlc import metadir, tlc_cmd
    args = (["-config", m["cfg"], "-workers", str(workers)] + bench_models.bench_flags(m)
            + bench_models.oracle_tlc_args(m))
    load0 = os.getloadavg()[0]
    spec = os.path.abspath(m["tla"])
    with bench_measure.staged_tlc_run(m) as (cwd, module):
        cmd = tlc_cmd(spec, args, m.get("features") or (), module=module,
                      jvm_extra=[TLC_MS_PROP, *measured_jvm_options(jvm_extra, default_heap)])
        p = bench.run_proc(cmd, timeout, cwd=cwd, rusage=True, raise_timeout=False, start_new_session=True)
        wall, text, ru = p.wall, p.stdout, p.rusage
    # (A killed JVM leaves its states directory behind; the next run starts afresh anyway.)
    shutil.rmtree(metadir(), ignore_errors=True)
    r = parse(text, wall, p.returncode)
    if p.timed_out:
        partial = {x: r[x] for x in ("generated", "distinct", "left", "depth", "init") if x in r}
        r = {"result": "timeout", "wall_s": r["wall_s"], "exit": r["exit"], **({"at_timeout": partial} if partial else {})}
    if mm := re.search(r"Finished in (\d+)ms at", text):
        r["finished_s"] = int(mm.group(1)) / 1000
    if mm := re.search(r"workers? on \d+ cores with (.*?) \[pid: \d+\] \((.*)\)", text):
        # (e.g. "2048MB heap and 2048MB offheap memory; Linux ..., MSBDiskFPSet, DiskStateQueue")
        r["tlc_memory"] = f"{mm.group(1)}; {mm.group(2)}"
    r["cpu_s"] = bench_measure.cpu_seconds(ru)
    r["maxrss_mib"] = bench_measure.rss_mib(ru)
    r["load"] = [round(load0, 2), round(os.getloadavg()[0], 2)]
    return r



def tlc_measured(m, workers, timeout, jvm_extra=(), default_heap=True, *, repetitions=1, min_repetitions=1):
    """One measured TLC run, cached under the baseline key.

    `jvm_extra` is the heap/direct-memory the caller asked for, and it is what
    the key commits to: no `-Xmx` means the JVM's default heap (the collected
    baselines' method), so a run measured with a pinned heap can never satisfy
    a default-heap key (the marker `measured_jvm_options` adds is deliberately
    outside the digest)."""
    from benchmarking.baselines import cached_tlc
    keyed = {**m, "measurement_constraints": list(jvm_extra)} if jvm_extra else m
    return cached_tlc(keyed, workers,
                      lambda: _collect_tlc_measured(m, workers, timeout, jvm_extra, default_heap),
                      repetitions=repetitions, min_repetitions=min_repetitions)



def metric_text(value, width=8, precision=2):
    """Keep missing resource observations visibly unavailable."""
    return f"{value:{width}.{precision}f}" if value is not None else f"{'n/a':>{width}}"


def accepted_timing(run):
    return run.get('result') in COMPLETE and not run.get('count_problems') and run.get('wall_s') is not None


def cmd_tlcbase(a):
    import bench
    from benchmarking import baselines
    from tlc import JVM_OPTS
    ws = workers_list(a.workers)
    ms = bench.tlcbase_models(a)
    suite_timeouts = {} if a.timeout is not None else _suite_timeouts()
    min_reps = getattr(a, "min_repetitions", 1)
    retry_incomplete = getattr(a, "retry_incomplete", False)
    reps = max(getattr(a, "tlc_repetitions", 1), min_reps)
    selected = None
    if a.missing:
        from benchmarking.records import instance_info
        version = bench_machine.tla2tools_info().get("revision") or bench_machine.tla2tools_info().get("short")
        actual_instance = instance_info(bench_machine.machine_desc())["type"]
        instance = getattr(a, "instance_type", "") or actual_instance
        if a.collect and instance != actual_instance:
            sys.exit("baseline collection instance differs from --instance-type; collect on the target cloud instance")
        unmeasured, bounded_timeouts, tlc_errors = [], [], []
        for k, m in ms.items():
            target_timeout = model_timeout(k, a.timeout, suite_timeouts)
            for w in ws:
                b = baselines.stored_baseline(m, w, version=version, instance=instance)
                status = classify_baseline(b, timeout=target_timeout, min_repetitions=min_reps)
                if status == "unmeasured":
                    unmeasured.append((k, w))
                elif status == "bounded-timeout":
                    bounded_timeouts.append((k, w))
                elif status == "tlc-error":
                    tlc_errors.append((k, w))
        if retry_incomplete:
            wanted = set(unmeasured) | set(bounded_timeouts) | set(tlc_errors)
            to_collect = [(k, w) for k in ms for w in ws if (k, w) in wanted]
        else:
            to_collect = unmeasured
        for k, w in to_collect:
            print(f"missing/stale: {k} {w}w TLC {version} {instance}")
        summary = f"{len(unmeasured)} unmeasured/stale, {len(bounded_timeouts)} bounded-timeout, {len(tlc_errors)} tlc-error"
        if retry_incomplete:
            print(f"{len(to_collect)} baseline keys to collect ({summary}; --retry-incomplete)")
        else:
            print(summary)
        selected = set(to_collect)
        if not a.collect or not selected:
            return
    name = f"tlc-{bench_machine.tla2tools_info().get('short') or 'unknown'}" + (f"-slice{a.slice.replace('/', 'of')}" if a.slice else "")
    out = a.out or os.path.join(bench.HISTORY, name + ".json")
    h = bench.read_json(out, {})
    if h and h.get("kind") != TLCBASE_KIND:
        sys.exit(f"{out} is not a TLC baseline file")
    header_timeout = (a.timeout if a.timeout is not None
                      else max((model_timeout(k, None, suite_timeouts) for k in ms), default=DEFAULT_TIMEOUT_S))
    h.update({"kind": TLCBASE_KIND, "date": h.get("date") or time.strftime("%Y-%m-%d %H:%M:%S"), "machine": bench_machine.machine_desc(),
              "bench_machine": os.environ.get("TLX_BENCH_MACHINE", ""), "commit": bench_machine.git_commit(), "tla2tools": bench_machine.tla2tools_info(),
              "community_modules_sha256": bench_machine.sha256_short(os.path.join(TP, "community", "modules.jar")),
              "jvm": {**bench_machine.jvm_info(), "options": JVM_OPTS + [TLC_MS_PROP], "heap": "jvm-default",
                      "note": "no -Xmx and no -fpmem: the JVM's default max heap and TLC's default fpmem, as the oracle"},
              "timeout_s": header_timeout, "workers": ws, "slice": a.slice or None})
    models = h.setdefault("models", {})
    model_count = len({k for k, _ in selected}) if selected is not None else len(ms)
    print(f"TLC baseline on {h['machine']}: {model_count} models, workers {','.join(map(str, ws))}, timeout {header_timeout}s -> "
          f"{os.path.relpath(out, ROOT)}", flush=True)
    for k, m in ms.items():
        ws_for_model = [w for w in ws if selected is None or (k, w) in selected]
        if not ws_for_model:
            continue
        timeout = model_timeout(k, a.timeout, suite_timeouts)
        rec = models.setdefault(k, {})
        rec.update({"source": m["source"], "flags": m.get("flags") or [],
                    "oracle": {x: m["tlc"].get(x) for x in ("result", "violated", "distinct", "generated", "depth", "wall_s")} if m.get("tlc") else None,
                    "manifest": {"runtime": m.get("runtime"), "result": m.get("result"), "distinct": m.get("distinct"), "total": m.get("total")}})
        runs = rec.setdefault("runs", {})
        for w in ws_for_model:
            # Never trust a raw history row to decide freshness; tlc_measured
            # reuses the canonical key or collects this stale/missing key once.
            r = bench.tlc_measured(m, w, timeout, repetitions=reps, min_repetitions=min_reps)
            r.setdefault("date", time.strftime("%Y-%m-%d %H:%M:%S"))
            runs[str(w)] = r
            print(f"  {k:<60} {w:>2}w {r['result']:<16} {str(r.get('distinct', '-')):>10} wall {metric_text(r.get('wall_s'))}s "
                  f"TLC {metric_text(r.get('finished_s'))}s cpu {metric_text(r.get('cpu_s'))}s rss {metric_text(r.get('maxrss_mib'), 7, 0)}M", flush=True)
            h["date_end"] = time.strftime("%Y-%m-%d %H:%M:%S")
            os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
            with open(out, "w") as stream:
                json.dump(h, stream, indent=1, sort_keys=True)
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    with open(out, "w") as stream:
        json.dump(h, stream, indent=1, sort_keys=True)
    from benchmarking.legacy import ingest
    ingest(out)
    print(f"recorded in {os.path.relpath(out, ROOT)}")



def _run_evidence(r):
    """How much a slice's run proves, ordered as the store's `evidence` orders
    rows: a completed run beats a timeout, two timeouts are compared by the
    bound they measured (14400 s of TLC says more than 1800 s of it), and an
    error proves only its date."""
    from benchmarking.records import COMPLETE
    r = r or {}
    if r.get("result") in COMPLETE:
        return (2, r.get("wall_s") or 0.0, r.get("date") or "")
    if r.get("result") == "timeout":
        return (1, r.get("wall_s") or 0.0, r.get("date") or "")
    return (0, 0.0, r.get("date") or "")


def cmd_tlcbase_merge(a):
    """Merge baseline slices (same TLC revision) into one baseline file.

    A slice covers part of the corpus and a run measures the worker counts it
    was asked for, so the merged baseline covers the union of the inputs'
    workers. Per model and worker count the merged file keeps the run that
    proves most, not the last one read: a completed run over a timeout, and
    between two timeouts the longer bound (the policy the store's `evidence`
    applies to the same rows)."""
    import bench
    hs = [bench.read_json(p) for p in a.inputs]
    for p, h in zip(a.inputs, hs):
        if h.get("kind") != TLCBASE_KIND:
            sys.exit(f"{p} is not a TLC baseline file")
        if h.get("tla2tools") != hs[0].get("tla2tools"):
            sys.exit(f"{p}: other tla2tools than {a.inputs[0]}")
    out = {k: v for k, v in hs[0].items() if k not in ("models", "slice", "date", "date_end", "bench_machine")}
    out["workers"] = sorted({int(w) for h in hs for w in h.get("workers") or []})
    out["slices"] = [{"file": os.path.basename(p), "slice": h.get("slice"), "machine": h.get("machine"), "bench_machine": h.get("bench_machine"),
                      "date": h.get("date"), "date_end": h.get("date_end"), "models": len(h.get("models", {}))} for p, h in zip(a.inputs, hs)]
    for kv in a.set:
        k, eq, v = kv.partition("=")
        if not eq:
            sys.exit(f"--set expects K=V, got {kv!r}")
        out[k] = v
    out["date"] = min(h.get("date") or "" for h in hs)
    out["date_end"] = max(h.get("date_end") or "" for h in hs)
    models = {}
    for p, h in zip(a.inputs, hs):
        for k, m in h.get("models", {}).items():
            prev = models.get(k)
            if prev is None:
                models[k] = {**m, "runs": dict(m.get("runs") or {})}
                continue
            runs = dict(prev.get("runs") or {})
            for w, run in (m.get("runs") or {}).items():
                if w in runs and _run_evidence(run) <= _run_evidence(runs[w]):
                    print(f"{k} {w}w: {p} proves no more than {a.inputs[0]}; keeping the stronger run", file=sys.stderr)
                    continue
                runs[w] = run
            models[k] = {**prev, "runs": runs}
            for key, value in m.items():
                if key != "runs" and value is not None and prev.get(key) is None:
                    models[k][key] = value
    out["models"] = models
    with open(a.out, "w") as stream:
        json.dump(out, stream, indent=1, sort_keys=True)
    print(f"{len(models)} models, workers {out['workers']} from {len(hs)} files -> {a.out}")


def load_tlc_baseline(x):
    """A TLC baseline file (path or bench/history name prefix): (header,
    {(model, workers): run})."""
    import bench
    h = bench.read_json(bench.history_path(x))
    if h.get("kind") != TLCBASE_KIND:
        sys.exit(f"{x} is not a TLC baseline file (bench.py tlcbase)")
    runs = {(k, int(w)): r for k, m in h.get("models", {}).items() for w, r in m.get("runs", {}).items()}
    cpu = bench_machine.cpu_model()
    if cpu and cpu not in (h.get("machine") or ""):
        print(f"warning: the TLC baseline was measured on {h.get('machine')}; this machine is {bench_machine.machine_desc()}", file=sys.stderr)
    return h, runs



def tlc_mismatch(rec, w):
    """How a baseline model's `w`-worker run differs from the oracle, or ''.
    Simulations: the result only; violations with several workers: result
    and violated name (the counts depend on the workers' interleaving); else
    also distinct, generated and depth."""
    r, o = rec.get("runs", {}).get(str(w)), rec.get("oracle")
    if not r or not o or r.get("result") == "timeout" or o.get("result") in (None, "error"):
        return ""
    keys = ["result"] if rec.get("flags") else ["result", "violated"] + (["distinct", "generated", "depth"] if w == 1 or r.get("result") == "success" else [])
    return ", ".join(f"{x} {o.get(x)} -> {r.get(x)}" for x in keys if o.get(x) != r.get(x))



def cmd_tlcbase_report(a):
    import bench
    h, _ = load_tlc_baseline(a.baseline)
    ms = h["models"]
    ws = h.get("workers", [1])
    tla, jvm = h.get("tla2tools", {}), h.get("jvm", {})
    print(f"TLC {tla.get('short')} ({tla.get('version')}) on {h.get('machine')}; JVM {(jvm.get('version') or ['?'])[0]}, "
          f"max heap {jvm.get('max_heap_mib')} MiB; {len(ms)} models; timeout {h.get('timeout_s')}s")
    inf = float("inf")
    for w in ws:
        rs = {k: m["runs"][str(w)] for k, m in ms.items() if str(w) in m.get("runs", {})}
        done = {k: r for k, r in rs.items() if accepted_timing(r)}
        tos = sorted(k for k, r in rs.items() if r.get('result') == 'timeout')
        rejected = sorted(set(rs) - set(done) - set(tos))
        def total(field):
            values = [r.get(field) for r in done.values()]
            return sum(values) if all(v is not None for v in values) else None
        print(f"\n{w} worker(s): {len(rs)} runs, {len(tos)} timeouts, {len(rejected)} rejected; "
              f"accepted timings: wall {metric_text(total('wall_s'), 0, 0)}s, "
              f"TLC 'Finished in' {metric_text(total('finished_s'), 0, 0)}s, CPU {metric_text(total('cpu_s'), 0, 0)}s")
        for k in tos:
            print(f"  timeout: {k}")
        for k in rejected:
            print(f"  rejected: {k}")
        buckets = [(0, 1), (1, 5), (5, 15), (15, 60), (60, 300), (300, inf)]
        print("  wall time distribution: " + ", ".join(
            f"{lo:g}-{hi:g}s: {sum(lo <= r['wall_s'] < hi for r in done.values())}" if hi != inf else
            f">={lo:g}s: {sum(r['wall_s'] >= lo for r in done.values())}" for lo, hi in buckets) + f", timeout: {len(tos)}")
    print(f"\nthe {a.top} slowest models (1 worker wall; timeouts first):")
    w1 = {k: m["runs"].get("1", {}) for k, m in ms.items()}
    order = sorted(w1, key=lambda k: (w1[k].get("result") != "timeout", -(w1[k].get("wall_s") or 0)))
    print(f"  {'model':<60} {'result':<16} {'distinct':>11} " + " ".join(f"{str(w) + 'w wall':>10} {str(w) + 'w cpu':>10}" for w in ws) + f" {'1w rss':>8}")
    for k in order[:a.top]:
        rr = ms[k]["runs"]
        cells = " ".join(f"{metric_text(rr.get(str(w), {}).get('wall_s'), 10, 1)} {metric_text(rr.get(str(w), {}).get('cpu_s'), 10, 1)}" for w in ws)
        print(f"  {k:<60} {str(w1[k].get('result')):<16} {str(w1[k].get('distinct', '-')):>11} {cells} {metric_text(w1[k].get('maxrss_mib'), 7, 0)}M")
    print("\nmismatches against the oracle (corpus/out/tlc.json; the large models have no oracle):")
    n = 0
    for k, m in sorted(ms.items()):
        for w in ws:
            if diff := tlc_mismatch(m, w):
                n += 1
                print(f"  {k} {w}w: {diff}")
        rs = [m["runs"].get(str(w), {}) for w in ws]
        if not m.get("flags") and all(r.get("result") == "success" for r in rs) and len({(r.get("distinct"), r.get("depth")) for r in rs}) > 1:
            n += 1
            print(f"  {k}: distinct/depth differ between worker counts: {[(r.get('distinct'), r.get('depth')) for r in rs]}")
    print(f"  {n} mismatch(es)")
