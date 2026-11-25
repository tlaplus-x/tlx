"""`bench.py compare` and `bench.py history-report`: two history files compared,
and one history file's speedups and peak-memory reduction over TLC.

`benchmarking/cli.py` owns the parser and `scripts/bench.py` dispatches; the two
passes live here (CODE-03), and the records they read are rendered and compared
by `benchmarking/report.py`. The helpers that stay in the entry point
(`bench.read_json`, `bench.history_path`, `bench.load_tlc_baseline`,
`bench.ok_result`) are reached through it, the way the other passes do
(HARNESS-03).
"""
import json, os, sys

from benchmarking import models as bench_models
from benchmarking.records import peak_rss
from benchmarking.report import TLC_MODE, compare_runs, report_markdown
from tlxlib import geomean


def geomean_text(values, unit='×'):
    """A geometric-mean cell, `-` when no pair carries the metric."""
    values = [value for value in values if value]
    return f"{geomean(values):7.2f}{unit}" if values else f"{'-':>8}"


def cmd_compare(a):
    import bench
    histories = []
    for path in (a.a, a.b):
        with open(bench.history_path(path)) as source:
            histories.append(json.load(source))
    A, B = histories
    ra, rb = A["runs"], B["runs"]
    if not set(ra) | set(rb):
        print("INCONCLUSIVE: no runs; re-run the benchmarks with >= 3 repeats")
        sys.exit(2)
    print(f"A = {A.get('commit')} ({A.get('date')}), B = {B.get('commit')} ({B.get('date')}); {len(set(ra) & set(rb))} runs in common")
    c = compare_runs(ra, rb, metric=a.metric, threshold=a.threshold, max_noise=a.max_noise, min_delta=a.min_delta)
    print(f"comparing min {a.metric} time; max noise {a.max_noise:.1%} ((max-min)/min)")
    print(f"{'run':<80} {'A min':>8} {'B min':>8} {'B/A':>6}  {'noise A/B':>15}  flag")
    for r in c["rows"]:
        if "a" not in r:
            print(f"{r['key']:<80} INCONCLUSIVE: {r['reasons'][0]}")
            continue
        flag = "INCONCLUSIVE: " + "; ".join(r["reasons"]) if r["reasons"] else r["flag"]
        if "distinct" in r:
            flag = "REGRESSION DISTINCT %s->%s; timing %s" % (*r["distinct"], flag)
        print(f"{r['key']:<80} {r['a']:8.2f} {r['b']:8.2f} {r['ratio']:6.2f}  {r['noise_a']:6.1%}/{r['noise_b']:6.1%}  {flag}")
    print("geometric mean of conclusive B/A per tier:")
    for t, rs in sorted(c["per_tier"].items()):
        rs = [r for r in rs if r == r and r > 0]
        if rs:
            print(f"  {t:<12} {geomean(rs):.3f}  ({len(rs)} runs)")
    loads = [r["load"][0] for r in list(ra.values()) + list(rb.values()) if r.get("load")]
    if a.metric == "wall" and loads and max(loads) > (os.cpu_count() or 1) / 2:
        print(f"warning: load average up to {max(loads):.1f} during the runs: wall times are noisy (try --metric cpu)")
    regress, inconclusive = c["regress"], c["inconclusive"]
    print(f"{len(regress)} regression(s), {len(c['better'])} improvement(s), {len(inconclusive)} inconclusive timing(s)")
    outcome = "REGRESSION" if regress else "INCONCLUSIVE" if inconclusive else "PASS"
    print(f"comparison: {outcome}")
    if inconclusive:
        print("re-run with >= 3 complete repeats on an idle machine; interleave A/B and inspect slow paths if noise persists")
    sys.exit(1 if regress else 2 if inconclusive else 0)



def cmd_history_report(a):
    import bench
    h = bench.read_json(bench.history_path(a.history))
    runs = h["runs"]
    if a.markdown:
        print("\n".join(report_markdown(h)))
        return
    print(f"{h.get('commit')} ({h.get('date')}) on {h.get('machine')}")
    if a.tlc_baseline:
        bh, base = bench.load_tlc_baseline(a.tlc_baseline)
        print(f"TLC side: {os.path.basename(bench.history_path(a.tlc_baseline))} (TLC {bh.get('tla2tools', {}).get('short')} on {bh.get('machine')})")
        tlcs = {k: {"min": r["wall_s"], "cpu": [r.get("cpu_s")], "maxrss_mib": r.get("maxrss_mib"),
                    "tlc_samples": r.get("tlc_samples"), "result": r.get("result")}
                for k, r in base.items()}
    else:
        tlcs = {(r["model"], r["workers"]): r for r in runs.values() if r["mode"] == TLC_MODE}
    if not tlcs:
        sys.exit("no TLC runs in this history file (bench.py run --tlc, or pass --tlc-baseline)")
    # (tier, model, mode, workers, TLC wall, tlx wall, TLC CPU, tlx CPU, TLC RSS, tlx RSS)
    rows = []
    for r in runs.values():
        tr = tlcs.get((r["model"], r["workers"]))
        if r["mode"] == TLC_MODE or not tr or not bench.ok_result(r) or not bench.ok_result(tr):
            continue
        cpu = min((c for c in r["cpu"] if c), default=None)
        rows.append((r["tier"], r["model"], r["mode"], r["workers"], tr["min"], r["min"], tr["cpu"][0], cpu,
                     peak_rss(tr), peak_rss(r)))
    print("\nspeedup = TLC time / tlx time, geometric mean (wall: min wall time; cpu: min user+sys; "
          "rss: median peak RSS)")
    print(f"{'tier':<12} {'mode':<8} {'workers':>7} {'runs':>5} {'wall':>8} {'cpu':>8} {'rss':>8}")
    groups = {}
    for t, k, mode, w, tw, xw, tc, xc, trss, xrss in rows:
        groups.setdefault((t, mode, w), []).append(
            (tw / xw, tc / xc if tc and xc else None, trss / xrss if trss and xrss else None))
    order = lambda g: (list(bench_models.TIERS).index(g[0]) if g[0] in bench_models.TIERS else len(bench_models.TIERS), g[1], g[2])
    for g in sorted(groups, key=order):
        xs = groups[g]
        print(f"{g[0]:<12} {g[1]:<8} {g[2]:>7} {len(xs):>5} {geomean_text([x for x, _, _ in xs])} "
              f"{geomean_text([c for _, c, _ in xs])} {geomean_text([r for _, _, r in xs])}")
    for mode in sorted({r[2] for r in rows}):
        # Each model once (models recur across tiers).
        one = {}
        for t, k, md, w, tw, xw, tc, xc, trss, xrss in rows:
            if md == mode and w == 1:
                one[k] = (tw / xw, tc / xc if tc and xc else None, trss / xrss if trss and xrss else None)
        print(f"{'all models':<12} {mode:<8} {1:>7} {len(one):>5} {geomean_text([x for x, _, _ in one.values()])} "
              f"{geomean_text([c for _, c, _ in one.values()])} {geomean_text([r for _, _, r in one.values()])}")
    one = {}
    for t, k, mode, w, tw, xw, *_ in rows:
        if mode == "compile" and w == 1:
            one[k] = (tw / xw, tw, xw)
    print(f"\nthe {a.top} models slowest relative to TLC (compile, 1 worker, wall):")
    for k, (sp, tw, xw) in sorted(one.items(), key=lambda kv: kv[1][0])[:a.top]:
        print(f"  {k:<60} TLC {tw:8.2f}s  tlx {xw:8.2f}s  {sp:7.2f}×")
    sc = {}
    for r in runs.values():
        if r["tier"] == "scaling" and bench.ok_result(r) and not (a.tlc_baseline and r["mode"] == TLC_MODE):
            sc.setdefault((r["model"], r["mode"]), {})[r["workers"]] = r["min"]
    if a.tlc_baseline:
        for k in {k for k, _ in sc}:
            for (bk, w), tr in tlcs.items():
                if bk == k and bench.ok_result(tr):
                    sc.setdefault((k, TLC_MODE), {})[w] = tr["min"]
    if sc:
        ws = sorted({w for v in sc.values() for w in v})
        print("\nscaling: min wall seconds (speedup over 1 worker)")
        print(f"  {'model':<44} {'mode':<8}" + "".join(f"{str(w) + 'w':>17}" for w in ws))
        for (k, mode), v in sorted(sc.items()):
            cells = "".join(f"{v[w]:9.2f} ({v[1] / v[w] if 1 in v else float('nan'):4.1f}×)" if w in v else f"{'-':>17}" for w in ws)
            print(f"  {k:<44} {mode:<8}{cells}")
