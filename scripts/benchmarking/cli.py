"""The bench CLI's one parser: its subcommands, options, defaults and help.

`scripts/bench.py` is the entry point: it keeps its own usage text (its module
docstring) and passes it in, and it still dispatches the parsed namespace to the
same handlers. The parser's structure lives here so that every consumer parses a
forwarded bench command with the parser that will execute it (HARNESS-02): the
cloud preflight used to assemble a second, incomplete one and refused
`profile --models A --deadline-min 5`, which bench.py itself accepts.
"""

import argparse
import sys

# `-h`/`--help` are the only arguments parse_args must not read as the default
# subcommand's options. `coverage` is not a subcommand of this parser either:
# bench.py forwards it to coverage.py before parsing.
HELP_FLAGS = ("-h", "--help")


# `table` regenerates the fixed docs/performance.md from the canonical records and
# measures nothing, so the options it inherited from the measurement entry point it
# replaced would be accepted and silently ignored (HARNESS-02). They stay
# declared -- a passed option is refused by name, never a silent no-op -- and
# each maps to the executable usage that replaces it.
RETIRED_TABLE = {
    "--models": "bench.py run --models a,b,...",
    "--filter": "bench.py run --models a,b,... (run selects ids, it has no substring filter)",
    "--workers": "bench.py run --workers N",
    "--timeout": "bench.py run --timeout S",
    "--no-tlc": "bench.py run",
    "--measure-tlc": "bench.py run --tlc",
    "--repeat": "bench.py run --repeat R",
    "--out": "the report path is fixed at docs/performance.md",
    "--tlc-baseline": "bench.py scale --tlc-baseline FILE",
    "--no-tier-columns": "the fixed report has a fixed column set",
}


def refuse_retired_table_options(a):
    """Refuse a retired `table` option the caller actually passed, naming the usage
    that replaces it.

    Every retired option defaults to None (the value options) or False (the
    switches), so "not passed" stays distinguishable from a passed value: the old
    defaults (os.cpu_count(), 600, 1) are values a caller could also pass, and
    `--repeat 1` or `--workers 8` are real invocations that must be refused too.
    """
    if a.cmd != "table":
        return
    # Attribute reads by name, not a computed `getattr`: the option-consumer check
    # is static and can only see a dest that is read literally.
    given = {"--models": a.models, "--filter": a.filter, "--workers": a.workers,
             "--timeout": a.timeout, "--no-tlc": a.no_tlc, "--measure-tlc": a.measure_tlc,
             "--repeat": a.repeat, "--out": a.out, "--tlc-baseline": a.tlc_baseline,
             "--no-tier-columns": a.no_tier_columns}
    passed = [(flag, RETIRED_TABLE[flag]) for flag, value in given.items()
              if value is not None and value is not False]
    if not passed:
        return
    print("bench.py table: the table is now the fixed docs/performance.md, generated from the canonical records, "
          "and measures nothing: these options have no effect", file=sys.stderr)
    for flag, usage in passed:
        print(f"  {flag}: {usage}", file=sys.stderr)
    sys.exit(2)


def subcommands(ap):
    """The subcommand names `ap` registers, in registration order.

    parse_args derives the default-subcommand rule from this instead of keeping a
    second copy of the list: a subcommand added to add_parser nowhere else is then
    reachable as itself, not read as `table`'s options.
    """
    for action in ap._actions:
        if isinstance(action, argparse._SubParsersAction):
            return tuple(action.choices)
    raise AssertionError("build_parser registered no subcommands")


def add_common_args(parser):
    """Options every subcommand accepts: the benchmark budget (`--deadline-min`,
    `--deadline-at`, from bench_budget) and the `--smoke` preflight switch."""
    parser.add_argument("--smoke", action="store_true", help=argparse.SUPPRESS)
    if "--deadline-min" not in parser._option_string_actions:
        parser.add_argument("--deadline-min", type=float, default=None, help="total benchmark budget, including warmups/repetitions")
    parser.add_argument("--deadline-at", type=float, default=None, help=argparse.SUPPRESS)


def build_parser(description=None, prog=None):
    """The execution parser: every subcommand with its options, defaults and help.

    `description` is the entry point's usage text (bench.py passes its docstring);
    `prog` is the name a parse error and the help usage line print.
    """
    ap = argparse.ArgumentParser(description=description, prog=prog, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    from benchmarking import bench_liveness
    bench_liveness.add_args(sub.add_parser("liveness", help="bounded ClockSettles/tableau scaling A/B"))
    from benchmarking import bench_disk
    bench_disk.add_args(sub.add_parser("disk", help="state spaces beyond memory: tlx -maxmem and TLC under a small heap"))
    from benchmarking import bench_suite
    bench_suite.add_args(sub)
    from benchmarking import release
    release.add_args(sub)
    from benchmarking import bench_profile
    bench_profile.add_args(sub.add_parser("profile", help="per-state cost by worker count (perf stat/record, -stats)"))
    from benchmarking import bench_ttfr
    bench_ttfr.add_args(sub.add_parser("ttfr", help="time to first result: tlx default flags vs TLC 1w, end to end, every model"))
    bench_ttfr.add_report_args(sub.add_parser("ttfr-report", help="distribution and losers of a ttfr file"))
    p = sub.add_parser("tiers")
    p.add_argument("--per-tier", type=int, default=6)
    p = sub.add_parser("run")
    p.add_argument("--isolate-cache", action="store_true", help="fresh TLX_CACHE per configuration, shared by its samples")
    p.add_argument("--tiers", default="")
    p.add_argument("--models", default="", help="run these models (tier 'custom') instead of the tiers")
    p.add_argument("--modes", default="", help="override the modes: compile, interp, default (no tier flag)")
    p.add_argument("--per-tier", type=int, default=6)
    p.add_argument("--repeat", type=int, default=3)
    p.add_argument("--timeout", type=int, default=600)
    p.add_argument("--stats", action="store_true", help="also record tlx -stats json (one more run)")
    p.add_argument("--tlc", action="store_true", help="also measure TLC (mode tlc, one JVM at a time)")
    p.add_argument("--external", default="", help="the external models of these manifest tiers (small,medium,...; tiers ext-<tier>; "
                                                   "with --models only those)")
    p.add_argument("--workers", default="", help="tlx -workers values, e.g. 1,max (default: the tier's)")
    p.add_argument("--tlc-workers", default="", help="TLC -workers values with --tlc (default: 1 and the most tlx workers)")
    p.add_argument("--tlc-timeout", type=int, default=0, help="TLC timeout (default --timeout)")
    p.add_argument("--resume", action="store_true", help="skip the runs already in the history file (TLC runs by model and workers)")
    p.add_argument("--out", default="", help="history file (default bench/history/<commit>.json)")
    p = sub.add_parser("compare")
    p.add_argument("a")
    p.add_argument("b")
    p.add_argument("--threshold", type=float, default=0.05)
    p.add_argument("--max-noise", type=float, default=0.05, help="maximum relative sample range before timings are inconclusive (default 0.05)")
    p.add_argument("--min-delta", type=float, default=0.05)
    p.add_argument("--metric", choices=["wall", "cpu"], default="wall", help="compare wall-clock or CPU (user+sys) times")
    p = sub.add_parser("report", help="generate the fixed docs/performance.md from canonical records")
    p.add_argument("--check", action="store_true")
    p.add_argument("--refresh-ages", action="store_true")
    p = sub.add_parser("migrate", help="convert legacy bench measurements and seed TLC baselines")
    p = sub.add_parser("history-report")
    p.add_argument("history")
    p.add_argument("--top", type=int, default=10)
    p.add_argument("--tlc-baseline", default="", help="TLC side from this TLC baseline file (bench.py tlcbase) instead of the history's TLC runs")
    p.add_argument("--markdown", action="store_true", help="a Markdown table per model with geometric means (needs the history's TLC runs)")
    p = sub.add_parser("ab")
    p.add_argument("--bin", action="append", default=[], help="NAME=PATH of a tlx binary (repeatable; the first is the baseline)")
    p.add_argument("--models", required=True)
    p.add_argument("--args", default="-compile -workers 1", help="tlx arguments (default: -compile -workers 1)")
    p.add_argument("--env", action="append", default=[], help="NAME:K=V: environment variable K=V for the runs of binary NAME (repeatable)")
    p.add_argument("--bin-args", action="append", default=[], help="NAME:ARGS: more tlx arguments for the runs of binary NAME (repeatable), "
                   "e.g. --bin default=target/release/tlx --bin tlc=target/release/tlx --bin-args tlc:-tlc")
    p.add_argument("--bin-rev", action="append", default=[], metavar="NAME=REV",
                   help="the revision of the executable --bin NAME=PATH runs (repeatable); a binary without it is recorded as unknown "
                        "(a label such as new/after or the checkout's own commit never identifies an external binary)")
    p.add_argument("--backend", choices=["default", "c", "jit", "closure"], default="",
                   help="the execution backend this A/B changes (c: TLX_JIT=0, jit: TLX_JIT=1, closure: TLX_NO_NATIVE=1); every --bin's --env must select it")
    p.add_argument("--hog", type=int, default=0, help="N processes spinning on a core each during the runs (oversubscription)")
    p.add_argument("--repeat", type=int, default=10)
    p.add_argument("--timeout", type=int, default=600)
    p.add_argument("--out", default="")
    p.add_argument("--tlc-baseline", default="", help="also compare with TLC's times from this TLC baseline file (bench.py tlcbase)")
    p.add_argument("--interp", action="store_true", help="run each binary with the interpreter (-interp, or no flag for an older binary)")
    p.add_argument("--no-warmup", action="store_true", help="skip the warm-up runs (nothing to build, e.g. with --interp)")
    p.add_argument("--stats", action="store_true",
                   help="also record each run's -stats json metrics (search time, host region evaluations, value store operations and bytes, "
                        "states expanded again); the timed runs then include the statistics' cost")
    p = sub.add_parser("perf")
    p.add_argument("--bin", action="append", default=[], help="NAME=PATH of a tlx binary (repeatable)")
    p.add_argument("--models", required=True)
    p.add_argument("--args", default="-workers 1", help="tlx arguments (default: -workers 1)")
    p.add_argument("--seconds", type=int, default=20, help="perf record runs at most this long")
    p.add_argument("--freq", type=int, default=999, help="perf record sampling frequency (Hz)")
    p.add_argument("--timeout", type=int, default=600, help="perf stat runs at most this long")
    p.add_argument("--tlc", action="store_true", help="also perf stat TLC (-workers 1) on each model")
    p.add_argument("--out", default="", help="output directory (default bench/perf)")
    p = sub.add_parser("layout")
    p.add_argument("--bin", action="append", default=[], help="NAME=PATH of a tlx binary (repeatable; the first is the baseline)")
    p.add_argument("--models", default="", help="comma-separated ids (default: every corpus model)")
    p.add_argument("--filter", default="", help="only models whose id contains this substring")
    p.add_argument("--args", default="-compile -workers 1", help="tlx arguments (default: -compile -workers 1)")
    p.add_argument("--jobs", type=int, default=1, help="models run in parallel")
    p.add_argument("--timeout", type=int, default=600)
    p.add_argument("--out", default="")
    p = sub.add_parser("table", help="regenerate the fixed docs/performance.md from the canonical records")
    # The retired measurement options (RETIRED_TABLE). They stay declared so a
    # passed one is refused by name in refuse_retired_table_options(); a None (or
    # False switch) default is the "not passed" sentinel, because the old defaults
    # (os.cpu_count(), 600, 1) are values a caller could also have passed explicitly.
    retired = "retired: no effect (the table is the fixed docs/performance.md)"
    p.add_argument("--models", default=None, help=retired)
    p.add_argument("--filter", default=None, help=retired)
    p.add_argument("--workers", type=int, default=None, help=retired)
    p.add_argument("--timeout", type=int, default=None, help=retired)
    p.add_argument("--no-tlc", action="store_true", help=retired)
    p.add_argument("--measure-tlc", action="store_true", help=retired)
    p.add_argument("--repeat", type=int, default=None, help=retired)
    p.add_argument("--out", default=None, help=retired)
    p.add_argument("--tlc-baseline", default=None, help=retired)
    p.add_argument("--no-tier-columns", action="store_true", help=retired)
    p = sub.add_parser("tlcbase")
    p.add_argument("--tlc-repetitions", type=int, default=1, help="samples for a new TLC baseline; existing valid keys are reused")
    p.add_argument("--min-repetitions", type=int, default=1, help="minimum completed samples required to treat a stored baseline as satisfied (default 1)")
    p.add_argument("--instance-type", default="", help="target baseline instance for --missing inventory (collection requires this actual instance)")
    p.add_argument("--missing", action="store_true", help="list exactly missing/stale baseline keys, without running TLC")
    p.add_argument("--retry-incomplete", action="store_true", help="with --missing, include already-bounded timeouts and stored TLC errors")
    p.add_argument("--collect", action="store_true", help="with --missing, collect only the listed missing keys")
    p.add_argument("--models", default="", help="comma-separated ids (default: every model, see --no-large)")
    p.add_argument("--filter", default="", help="only models whose id contains this substring")
    p.add_argument("--slice", default="", help="I/N: the I-th of N slices of about equal estimated time")
    p.add_argument("--workers", default="1,16", help="TLC -workers values (default 1,16)")
    p.add_argument("--no-large", action="store_true", help="only the models of corpus/out/tlc.json")
    p.add_argument("--large-min", type=int, default=61, help="large tier: manifest runtime at least S seconds (default 61)")
    p.add_argument("--large-max", type=int, default=700, help="large tier: manifest runtime at most S seconds (default 700)")
    p.add_argument("--timeout", type=int, default=None, help="per-run TLC timeout in seconds (default: suite manifest timeout_s, else 1800)")
    p.add_argument("--force", action="store_true", help="measure again the runs already in --out")
    p.add_argument("--out", default="", help="baseline file (default bench/history/tlc-<tla2tools rev>[-sliceIofN].json)")
    p = sub.add_parser("tlcbase-merge")
    p.add_argument("out")
    p.add_argument("inputs", nargs="+")
    p.add_argument("--set", action="append", default=[], metavar="K=V", help="a header field of the merged file (repeatable)")
    p = sub.add_parser("tlcbase-report")
    p.add_argument("baseline")
    p.add_argument("--top", type=int, default=15)
    p = sub.add_parser("scale")
    p.add_argument("--models", default="", help="comma-separated ids (default: SCALE_DEFAULT; bench/<name> = bench/scaling/<name>.cfg)")
    p.add_argument("--workers", default="1,16,64,128,max", help="tlx -workers values (max: the number of CPUs)")
    p.add_argument("--tlc-workers", default="", help="TLC -workers values (default: --workers)")
    p.add_argument("--tlc-1w", default="all", help="models whose TLC 1-worker run is measured: all, none, or comma-separated ids")
    p.add_argument("--no-tlc", action="store_true", help="tlx only")
    p.add_argument("--tlc-mem", type=float, default=0.4, help="TLC heap and direct memory, each this fraction of the physical memory (0: JVM defaults)")
    p.add_argument("--tlc-baseline", default="", help="reference counts from this TLC baseline file (for --no-tlc)")
    p.add_argument("--repeat", type=int, default=2, help="tlx runs per worker count > 1 (min)")
    p.add_argument("--repeat-1w", type=int, default=1, help="tlx runs at 1 worker (min)")
    p.add_argument("--stats", action="store_true", help="one more tlx run per worker count > 1 with -stats json")
    p.add_argument("--timeout", type=int, default=3600)
    p.add_argument("--tlc-timeout", type=int, default=0, help="TLC timeout (default --timeout)")
    p.add_argument("--force", action="store_true", help="measure again the runs already in --out")
    p.add_argument("--out", default="", help="scaling file (default bench/history/scale-<commit>.json)")
    p = sub.add_parser("scale-report")
    p.add_argument("file")
    p.add_argument("--tlc-baseline", default="", help="fill the TLC runs the file lacks from this TLC baseline file (same machine type)")
    for parser in sub.choices.values():
        add_common_args(parser)
    return ap


def parse_args(argv, description=None, prog=None):
    """Parse bench's argv with the execution parser; returns (parser, namespace).

    `bench.py <option>` is the documented spelling of `bench.py table <option>`,
    so an argument that is neither a subcommand nor `-h`/`--help` is read as the
    default subcommand's.
    """
    ap = build_parser(description, prog)
    if not argv or (argv[0] not in subcommands(ap) and argv[0] not in HELP_FLAGS):
        argv = ["table"] + list(argv)
    args = ap.parse_args(argv)
    if getattr(args, "tlc_repetitions", 1) < 1:
        ap.error("--tlc-repetitions must be positive")
    if getattr(args, "min_repetitions", 1) < 1:
        ap.error("--min-repetitions must be positive")
    return ap, args
