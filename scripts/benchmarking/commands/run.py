"""`bench.py run`: the tiers measured into the history file.

`benchmarking/cli.py` owns the parser and `scripts/bench.py` dispatches; the
pass this subcommand runs lives here, so the command line and the execution it
requests are separate responsibilities (CODE-03). The shared helpers
(`bench.tlx`, `bench.mode_args`, `bench.HISTORY`) are reached through the entry
point module, the namespace a test replaces one in, the way
`bench_profile`/`bench_ttfr` do (HARNESS-03: the entry point publishes itself
under its import name, so that lookup is the running module and not a second
copy of it).
"""
import json, os, statistics, sys, tempfile, time

from benchmarking import models as bench_models, machine as bench_machine
from benchmarking import bench_budget
from tlxlib import ROOT


def cmd_run(a):
    import bench
    with bench.build_release("tlx-bench-") as binary:
        run_bench(a, binary)


def sample_problem(r, ref, *, mode, workers, asymmetric_symmetry=False):
    """The counts problem of one sample of `mode` at `workers` against the
    reference result `ref` (bench.counts_check), '' when it agrees or the
    comparison is not conclusive. The sample is seen with exactly the fields
    the aggregate record has always carried."""
    import bench
    sample = {k: r.get(k) for k in ("result", "distinct", "compatibility")}
    sample.update(mode=mode, workers=workers, compatibility=r.get("compatibility", mode == "tlc"))
    return "" if bench.counts_check(sample, ref, asymmetric_symmetry=asymmetric_symmetry) is not False \
        else "result or distinct differs from TLC"


def run_problems(rs, ref, *, mode, workers, asymmetric_symmetry=False):
    """Every counts problem of a run of repeated samples: the last sample's own
    (reported to the user unprefixed, as before) and, named by position, any
    earlier sample whose problem differs from it — a mismatch of an earlier
    sample is never erased by a later agreeing one."""
    import bench
    if not rs:
        return []
    kw = {"mode": mode, "workers": workers, "asymmetric_symmetry": asymmetric_symmetry}
    last = sample_problem(rs[-1], ref, **kw)
    out = [last] if last else []
    return out + [f"sample {i}: {p}" for i, r in enumerate(rs[:-1], 1)
                  if (p := sample_problem(r, ref, **kw)) and p != last]


def run_bench(a, binary):
    import bench
    if a.external:
        sel = bench_models.external_selection(a.external, a.models)
        if not sel:
            sys.exit("no external models selected")
    elif a.models:
        sel = {"custom": a.models.split(",")}
    else:
        tiers = a.tiers.split(",") if a.tiers else list(bench_models.TIERS)
        for t in tiers:
            if t not in bench_models.TIERS:
                sys.exit(f"unknown tier {t} (tiers: {', '.join(bench_models.TIERS)})")
        sel = bench_models.select(tiers, a.per_tier)
    d = bench_models.oracle([k for ks in sel.values() for k in ks])
    missing = [k for ks in sel.values() for k in ks if k not in d]
    if missing:
        sys.exit(f"unknown model(s): {', '.join(missing)}")
    selected = {k for ks in sel.values() for k in ks}
    for k in bench_models.STRESS_MODELS:
        if k in selected:
            if not all(os.path.isfile(d[k][p]) for p in ("tla", "cfg")):
                sys.exit(f"missing stress model {k}; run scripts/fetch-deps.sh and scripts/fetch-external.py --repos tlaplus-tests")
    cores = os.cpu_count() or 1
    out = a.out or os.path.join(bench.HISTORY, f"{bench_machine.git_commit()}.json")
    hist = bench.read_json(out, {})
    hist.update({"commit": bench_machine.git_commit(), "date": time.strftime("%Y-%m-%d %H:%M:%S"), "machine": bench_machine.machine_desc()})
    runs = hist.setdefault("runs", {})
    # TLC once per model and worker count (models recur across tiers; with
    # --resume also across invocations on the same history file).
    tlc_done = {}  # The canonical content/version/worker/instance key owns TLC reuse, even with --resume.

    def save():
        bench_budget.record(hist)
        os.makedirs(os.path.dirname(out) or ".", exist_ok=True)
        with open(out, "w") as stream:
            json.dump(hist, stream, indent=1, sort_keys=True)

    for t, ks in sel.items():
        _, modes, workers = bench_models.TIERS.get(t, ("", ["compile", "interp"], [1]))
        if a.modes:
            modes = a.modes.split(",")
        if a.workers:
            workers = bench_machine.scale_workers(a.workers, cores)
        tlc_workers = bench_machine.scale_workers(a.tlc_workers, cores) if a.tlc_workers else sorted({1, min(max(workers), cores)})
        for k in ks:
            m = d[k]
            if a.tlc:
                for w in sorted(set(tlc_workers) | ({1} if m.get("asymmetric_symmetry") else set())):
                    key = f"{t}:{k}:{bench.TLC_MODE}:{w}w"
                    if (k, w) not in tlc_done:
                        load0 = os.getloadavg()[0]
                        r = bench.tlc(m, w, a.tlc_timeout or a.timeout)
                        tlc_done[k, w] = {
                            "model": k, "mode": bench.TLC_MODE, "workers": w,
                            "content_digest": r.get("content_digest"), "tlc_version": r.get("tlc_version"), "date": r.get("date"),
                            "baseline_id": r.get("baseline_id"), "measurement_revision": r.get("measurement_revision"),
                            "walls": [r["wall_s"]], "min": r["wall_s"], "median": r["wall_s"], "cpu": [r.get("cpu_s")],
                            "rss_mib": [r.get("maxrss_mib")],
                            "distinct": r.get("distinct"), "result": r.get("result"),
                            "generated": r.get("generated"), "depth": r.get("depth"),
                            "expected_distinct": m["tlc"].get("distinct"),
                            "load": [round(load0, 2), round(os.getloadavg()[0], 2)],
                        }
                    runs[key] = {**tlc_done[k, w], "tier": t}
                    print(f"{key:<80} wall    {runs[key]['min']:7.2f}s                   cpu {runs[key]['cpu'][0] or 0:7.2f}s"
                          f"  {runs[key]['result']} {runs[key]['distinct']}", flush=True)
                    save()
            # The reference of the counts check: TLC on this machine (1 worker,
            # else the fewest workers that finished), else the oracle.
            ref = next((r for r in (tlc_done.get((k, w)) for w in ([1] if m.get("asymmetric_symmetry") else sorted({1, *tlc_workers}))) if r and bench.ok_result(r)), None) or m["tlc"] or None
            for mode in modes:
                for w in sorted({min(w, cores) for w in workers}):
                    key = f"{t}:{k}:{mode}:{w}w"
                    if a.resume and key in runs:
                        continue
                    load0 = os.getloadavg()[0]
                    rs = []
                    from benchmarking.measurement import cache_environment
                    with cache_environment(getattr(a, 'isolate_cache', False)) as (cache_env, cache):
                        for _ in range(a.repeat):
                            rs.append(bench.tlx(m, bench.mode_args(mode, w, m, exe=binary), a.timeout, exe=binary, env=cache_env or None))
                            if rs[-1].get("result") == "timeout":
                                break
                        walls = [r["wall_s"] for r in rs]
                        rec = {
                            "tier": t, "model": k, "mode": mode, "workers": w, "cache": cache,
                            "walls": walls, "min": min(walls), "median": statistics.median(walls),
                            "cpu": [r.get("cpu_s") for r in rs],
                            "rss_mib": [r.get("maxrss_mib") for r in rs],
                            "distinct": rs[-1].get("distinct"), "result": rs[-1].get("result"),
                            "compatibility": rs[-1].get("compatibility", mode == "tlc"),
                            "generated": rs[-1].get("generated"), "depth": rs[-1].get("depth"),
                            "expected_distinct": m["tlc"].get("distinct"),
                            "load": [round(load0, 2), round(os.getloadavg()[0], 2)],
                        }
                        from benchmarking.bench_suite import sample_record
                        rec["samples"] = [sample_record(r) for r in rs]
                        if a.stats:
                            with tempfile.NamedTemporaryFile(suffix=".json", delete=False) as f:
                                path = f.name
                            bench.tlx(m, bench.mode_args(mode, w, m, binary) + ["-stats", f"json={path}"], a.timeout, exe=binary, env=cache_env or None)
                            try:
                                rec["stats"] = bench.read_json(path)
                            except (OSError, ValueError):
                                pass
                            os.unlink(path)
                    from benchmarking.baselines import content_digest
                    rec["content_digest"] = content_digest(m)
                    rec["tlc_version"] = bench_machine.tla2tools_info().get("revision")
                    runs[key] = rec
                    # The last sample's problem is reported to the user as before;
                    # an earlier sample that disagrees is kept, named by its position.
                    problems = run_problems(rs, ref, mode=mode, workers=w,
                                            asymmetric_symmetry=m.get("asymmetric_symmetry", False))
                    if problems:
                        rec["count_problems"] = problems
                    if m.get("asymmetric_symmetry") and w != 1:
                        rec["counts_note"] = "non-equivariant SYMMETRY: multi-worker counts are scheduling-dependent (D-22)"
                    if m.get("oracle_error") and ref is None:
                        rec["oracle_error"] = m["oracle_error"]
                    ok = "" if not problems or m.get("flags") else "  (result or distinct differs from TLC)"
                    print(f"{key:<80} min {rec['min']:7.2f}s  median {rec['median']:7.2f}s  cpu {min(c or 0 for c in rec['cpu']):7.2f}s"
                          f"  {rec['result']} {rec['distinct']}{ok}", flush=True)
                    save()
    from benchmarking.legacy import ingest
    ingest(out)
    print(f"recorded in {os.path.relpath(out, ROOT)}")
