"""The bench CLI's option contract: one owner for its parser, and an option the
parser accepts must have an effect or an explicit refusal, never a silent no-op
(HARNESS-02).

`scripts/benchmarking/cli.py` owns the parser -- subcommands, options, defaults and
help; `scripts/bench.py` is the entry point that passes its usage text in, and
`cloud_verify.py`'s preflight parses a forwarded command with the same parser
instead of reassembling one. `table` regenerates the fixed docs/performance.md and
measures nothing, so the measurement options it inherited from the entry point it
replaced are retired. Known-bad before the retirement: every one of them exited 0
with the generic "table is now the fixed docs/performance.md" line and no
diagnostic, so `bench.py table --models X` looked like it had measured X.

The entry point dispatches; the pass of a subcommand lives in
`scripts/benchmarking/commands/` (run, ab, layout) and reaches its collaborators
through the entry point module. So the entry point has to be one module also when
a pass imports it, and moving a pass must not change the argv, the refusal or the
exit status the entry point produces -- both are checked below as real children
with the complete command kept (HARNESS-03, HARNESS-22).
"""

import argparse
import contextlib
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

import bench
from benchmarking import bench_records
from benchmarking import bench_smoke
from benchmarking import cli, legacy as bench_legacy


ROOT = Path(__file__).resolve().parents[2]

# One argv a caller could really type per retired option, so the refusal is
# exercised through the entry point rather than at the predicate.
RETIRED_ARGV = {
    "--models": ["--models", "MultiPaxos_MC"],
    "--filter": ["--filter", "Paxos"],
    "--workers": ["--workers", "4"],
    "--timeout": ["--timeout", "60"],
    "--no-tlc": ["--no-tlc"],
    "--measure-tlc": ["--measure-tlc"],
    "--repeat": ["--repeat", "3"],
    "--out": ["--out", "bench/results.md"],
    "--tlc-baseline": ["--tlc-baseline", "bench/tlc-baselines/x.json"],
    "--no-tier-columns": ["--no-tier-columns"],
}

# The least a caller can type for each subcommand to parse: every positional and
# every required option, nothing else. Values are inert strings -- parsing does not
# build a binary or run a model.
MINIMAL_ARGV = {
    "liveness": ["--before", "HEAD", "--before-bin", "path"], "disk": ["--models", "A"],
    "suite-check": [], "suite": [], "suite-judge": ["run.json"],
    "suite-report": [], "suite-merge": ["merged.json", "one.json"], "track": [], "profile": ["--models", "A"], "ttfr": ["--bin", "a=path"],
    "ttfr-report": ["ttfr.json"], "tiers": [], "run": [], "compare": ["a.json", "b.json"],
    "report": [], "migrate": [], "history-report": ["history.json"], "ab": ["--models", "A"],
    "perf": ["--models", "A"], "layout": [], "table": [], "tlcbase": [],
    "tlcbase-merge": ["merged.json", "one.json"], "tlcbase-report": ["tlc.json"],
    "scale": [], "scale-report": ["scale.json"],
}

# The defaults callers and documentation depend on (docs/benchmarking.md, bench
# commands in the skills). A move or a new option must not silently change one.
DOCUMENTED_DEFAULTS = {
    ("run", "repeat"): 3, ("run", "timeout"): 600, ("run", "per_tier"): 6,
    ("ab", "args"): "-compile -workers 1", ("ab", "repeat"): 10,
    ("layout", "args"): "-compile -workers 1", ("layout", "jobs"): 1,
    ("scale", "workers"): "1,16,64,128,max", ("profile", "workers"): "1,4,8,16",
    ("tlcbase", "workers"): "1,16", ("table", "models"): None,
}


def run_bench(argv, **env):
    """Run the real entry point and keep the complete argv with the result
    (HARNESS-22), so a failure names the exact command that produced it."""
    command = [sys.executable, str(ROOT / "scripts/bench.py"), *argv]
    result = subprocess.run(command, cwd=ROOT, env={**os.environ, "PYTHONPATH": str(ROOT / "scripts"), **env},
                            capture_output=True, text=True, timeout=120)
    result.command = command
    return result


def entry_point_imports(argv, **env):
    """(result, module names the child imported) of one real entry-point run.

    `-X importtime` makes the child itself report what it loaded, so the probe
    is the entry point's own run rather than a re-implementation of its import
    order (HARNESS-22)."""
    command = [sys.executable, "-X", "importtime", str(ROOT / "scripts/bench.py"), *argv]
    result = subprocess.run(command, cwd=ROOT, env={**os.environ, "PYTHONPATH": str(ROOT / "scripts"), **env},
                            capture_output=True, text=True, timeout=120)
    result.command = command
    return result, [line.rsplit("|", 1)[-1].strip() for line in result.stderr.splitlines()
                    if line.startswith("import time:")]


def subparser(parser, name):
    for action in parser._actions:
        if isinstance(action, argparse._SubParsersAction):
            return action.choices[name]
    raise AssertionError("the parser registers no subcommands")


def parse_text(parser, argv):
    """(exit code, output) of argparse's own help/error path for one argv, without
    exiting the test process."""
    out = io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(out):
        try:
            parser.parse_args(list(argv))
            return 0, out.getvalue()
        except SystemExit as exit:
            return exit.code, out.getvalue()


class SubcommandContract(unittest.TestCase):
    """Every subcommand's argv, defaults, help and error surface, through the parser
    the entry point uses (the owner's, not a test copy of it)."""

    def setUp(self):
        self.parser = cli.build_parser(description=bench.__doc__, prog="bench.py")

    def test_every_subcommand_is_reachable_by_name(self):
        # parse_args' default rule reads the names off the parser; a subcommand the
        # list did not know would be rewritten to `table <name>`.
        self.assertEqual(sorted(cli.subcommands(self.parser)), sorted(MINIMAL_ARGV))

    def test_every_subcommand_accepts_its_minimal_argv(self):
        for name, argv in sorted(MINIMAL_ARGV.items()):
            with self.subTest(subcommand=name):
                code, text = parse_text(self.parser, [name, *argv])
                self.assertEqual(code, 0, f"bench.py {name} {' '.join(argv)}: {text}")

    def test_every_subcommand_refuses_an_option_it_does_not_take(self):
        # The negative half of HARNESS-02: an unsupported --name is an error, not
        # something the parser swallows and the handler then ignores.
        for name, argv in sorted(MINIMAL_ARGV.items()):
            with self.subTest(subcommand=name):
                code, text = parse_text(self.parser, [name, *argv, "--definitely-unsupported"])
                self.assertEqual(code, 2, f"bench.py {name} accepted --definitely-unsupported: {text}")
                self.assertIn("unrecognized arguments: --definitely-unsupported", text)

    def test_every_subcommand_help_names_its_flags_and_the_shared_deadline_flag(self):
        with mock.patch.dict(os.environ, {"COLUMNS": "200"}):
            for name in cli.subcommands(self.parser):
                with self.subTest(subcommand=name):
                    sub = subparser(self.parser, name)
                    flags = sorted({flag for action in sub._actions if action.help != argparse.SUPPRESS
                                    for flag in action.option_strings if flag.startswith("--")})
                    # The shared flags every subcommand accepts (HARNESS-02's other
                    # half: help is the execution parser's own output).
                    self.assertIn("--deadline-min", flags, f"{name} does not accept the shared deadline budget")
                    code, text = parse_text(self.parser, [name, "--help"])
                    self.assertEqual(code, 0, f"bench.py {name} --help exited {code}: {text}")
                    self.assertTrue(text.startswith(f"usage: bench.py {name} "),
                                    f"the usage line does not start with the subcommand: {text[:200]}")
                    missing = [flag for flag in flags if flag not in text]
                    self.assertEqual(missing, [], f"bench.py {name} --help omits {missing}")

    def test_the_documented_defaults_are_unchanged(self):
        for (name, dest), want in sorted(DOCUMENTED_DEFAULTS.items()):
            with self.subTest(subcommand=name, option=dest):
                try:
                    parsed = self.parser.parse_args([name, *MINIMAL_ARGV[name]])
                except SystemExit as exit:
                    self.fail(f"bench.py {name} {' '.join(MINIMAL_ARGV[name])} exited {exit.code}")
                self.assertEqual(getattr(parsed, dest), want, f"{name} --{dest.replace('_', '-')}")

    def test_a_subcommand_with_its_own_deadline_min_keeps_it(self):
        # add_common_args must not collide with a subcommand's own --deadline-min
        # (ttfr declares one with a different default and its own help); the shared
        # one is added only when the subcommand has none.
        self.assertEqual(self.parser.parse_args(["ttfr", "--bin", "a=path"]).deadline_min, 0)
        self.assertIsNone(self.parser.parse_args(["run"]).deadline_min)

    def test_the_preflight_command_list_is_a_subset_of_the_cli(self):
        # bench_smoke preflights a forwarded command by running bench.py again; its
        # policy list must not name a subcommand the CLI does not have (`coverage`
        # is forwarded to coverage.py before parsing).
        known = set(cli.subcommands(self.parser)) | {"coverage"}
        self.assertEqual(sorted(set(bench_smoke.MEASURE_COMMANDS) - known), [],
                         "benchmarking.bench_smoke.MEASURE_COMMANDS names something bench.py does not accept")
        # Known-bad direction: the same predicate reports a name the CLI has not.
        self.assertEqual(sorted((set(bench_smoke.MEASURE_COMMANDS) | {"no-such-command"}) - known),
                         ["no-such-command"])

    def test_every_subcommand_help_runs_through_the_entry_point(self):
        # The same contract as above, but as a real child with the complete argv
        # (HARNESS-22): what the entry point prints is what a caller reads.
        for name in cli.subcommands(self.parser):
            with self.subTest(subcommand=name):
                result = run_bench([name, "--help"], COLUMNS="200")
                self.assertEqual(result.returncode, 0, f"{result.command}: {result.stderr}")
                self.assertTrue(result.stdout.startswith(f"usage: bench.py {name} "),
                                f"{result.command}: {result.stdout[:200]}")

    def test_the_entry_point_and_the_preflight_build_no_parser_of_their_own(self):
        # One owner (HARNESS-02): bench.py passes its usage text in and dispatches;
        # cloud_verify's preflight parses with the owner. A second parser is how the
        # preflight drifted (it refused `profile --deadline-min 5`).
        entry = (ROOT / "scripts/bench.py").read_text()
        self.assertNotIn("add_argument", entry)
        self.assertNotIn("ArgumentParser", entry)
        verify = (ROOT / "scripts/cloud_verify.py").read_text()
        self.assertNotIn("benchmarking.bench_profile.add_args", verify)
        self.assertNotIn("add_common_args", verify)


class RetiredTableOptions(unittest.TestCase):
    def test_every_retired_argv_matches_the_retirement_map(self):
        # The two lists are independent on purpose: the map is the policy, this
        # one is what a caller types. A gap means an option is unreachable by
        # test, so keep them equal.
        self.assertEqual(sorted(RETIRED_ARGV), sorted(cli.RETIRED_TABLE))

    def test_each_retired_option_is_refused_by_name_with_its_replacement(self):
        for flag in sorted(cli.RETIRED_TABLE):
            with self.subTest(flag=flag):
                result = run_bench(["table", *RETIRED_ARGV[flag]])
                self.assertEqual(result.returncode, 2,
                                 f"{result.command}: stdout={result.stdout!r} stderr={result.stderr!r}")
                self.assertIn(flag, result.stderr)
                self.assertIn(cli.RETIRED_TABLE[flag], result.stderr,
                              f"{result.command}: the refusal must name the usage that replaces {flag}")
                # The option is declared and refused by our policy, not rejected as
                # an unknown argument with no migration path.
                self.assertNotIn("unrecognized arguments", result.stderr)
                self.assertNotIn("PASS", result.stdout)

    def test_refusal_survives_the_default_subcommand(self):
        # `bench.py <option>` is `bench.py table <option>` (the documented default
        # without a subcommand), so the retirement must cover that spelling too.
        result = run_bench(["--models", "MultiPaxos_MC"])
        self.assertEqual(result.returncode, 2, f"{result.command}: {result.stderr}")
        self.assertIn("--models", result.stderr)

    def test_refusal_covers_the_preflight_smoke_path(self):
        # cloud_verify's preflight runs `bench.py <cmd> --smoke`, which returns
        # before the subcommand handler: a retired option must not slip through it.
        result = run_bench(["table", "--measure-tlc", "--smoke"])
        self.assertEqual(result.returncode, 2, f"{result.command}: {result.stderr}")
        self.assertIn("--measure-tlc", result.stderr)

    def test_bare_table_regenerates_the_report_from_the_canonical_records(self):
        # Passing control: the retirement must not refuse the supported
        # invocation, and regenerating must be deterministic - the report is the
        # records' own output, which doccheck (bench_records.check) also
        # enforces. The store is the test's own: the shipped measurement store is
        # not part of the source tree, so the docs/performance.md a checkout
        # holds is not reproducible from that checkout, and comparing bytes with
        # it would only assert that the recording machine still had its store on
        # disk.
        code, text = parse_text(cli.build_parser(description=bench.__doc__, prog="bench.py"), ["table"])
        self.assertEqual(code, 0, f"bench.py table exited {code}: {text}")
        self.assertRegex((ROOT / "scripts/bench.py").read_text(), r'"table": cmd_table\b',
                         "the entry point dispatches `table` somewhere else than the report generator")
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "bench").mkdir()
            (root / "bench/suite.json").write_text(json.dumps({"models": [{"id": "M"}]}))
            source = root / "bench/a.json"
            source.write_text(json.dumps({"commit": "abc", "date": "2026-10-07", "machine": "x86_64 SA5.4XLARGE32",
                                          "runs": {"M": {"model": "M", "mode": "compile", "workers": 1,
                                                         "wall_s": 2, "result": "success", "distinct": 10}}}))
            bench_legacy.ingest(source, root)
            report = root / "docs/performance.md"
            first = bench_records.generate(root)
            self.assertEqual(report.read_text(), first)
            self.assertIn("M", first)
            self.assertEqual(bench_records.generate(root), first, "regenerating the report changed it")
            self.assertEqual(bench_records.check(root), [])

    def test_the_migration_hints_are_runnable(self):
        # "keep an executable migration hint": a hint that names a command must
        # name a subcommand this CLI accepts and the flags it is credited with.
        hints = sorted({usage for usage in cli.RETIRED_TABLE.values() if usage.startswith("bench.py ")})
        self.assertTrue(hints)
        for usage in hints:
            words = usage.split()
            with self.subTest(usage=usage):
                result = run_bench([words[1], "--help"], COLUMNS="200")
                self.assertEqual(result.returncode, 0, f"{result.command}: {result.stderr}")
                for word in words[2:]:
                    # A flag token, not a word that merely follows one: trailing prose
                    # in a hint must not be read as an argument the subcommand takes.
                    if re.fullmatch(r"--[a-z][a-z0-9-]*", word):
                        self.assertIn(word, result.stdout, f"{usage}: bench.py {words[1]} does not accept {word}")

    def test_the_retirement_is_documented_in_help(self):
        # HARNESS-02's other half: a retired option is advertised as retired.
        result = run_bench(["table", "--help"], COLUMNS="200")
        self.assertEqual(result.returncode, 0, f"{result.command}: {result.stderr}")
        self.assertIn("retired: no effect", result.stdout)

    def test_the_shared_deadline_flags_are_not_swept_up(self):
        # `--deadline-min`/`--deadline-at` come from add_common_args, which every
        # subcommand accepts and cloud_verify's preflight parses against the same
        # contract; retiring them for `table` alone would make the parsers drift.
        self.assertNotIn("--deadline-min", cli.RETIRED_TABLE)
        self.assertNotIn("--deadline-at", cli.RETIRED_TABLE)
        self.assertNotIn("--smoke", cli.RETIRED_TABLE)


class RetiredTablePaths(unittest.TestCase):
    def test_the_measurement_entry_points_and_their_references_are_gone(self):
        # run_table had no caller and only table_models called it; with both
        # removed, no source can reach the retired measurement path at all.
        names = ("run_table", "table_models")
        self.assertFalse([name for name in names if hasattr(bench, name)])
        hits = []
        for path in sorted((ROOT / "scripts").rglob("*.py")):
            if path.resolve() == Path(__file__).resolve():
                continue
            for name in names:
                if name in path.read_text():
                    hits.append(f"{path.relative_to(ROOT)}: {name}")
        self.assertEqual(hits, [])


class MovedPassesThroughTheEntryPoint(unittest.TestCase):
    """The passes in `benchmarking/commands/` are still started by the entry
    point, with the arguments a caller types and the same refusal.

    The move (run/ab/layout/history/tlcbase/scale out of `scripts/bench.py`) may
    not change what the entry point does with an argv: each case below is a real
    child with the complete command kept (HARNESS-22), and it reaches the moved
    handler — a missing binary is refused by the layout pass's own check and a
    missing history file by the history pass's, not by the parser. The refusal
    is also the cheapest argv that enters the pass, so the case doubles as the
    control that the entry point dispatches at all.
    """

    # `layout` without `--bin` is refused by the `--bin` check, not by the model
    # resolution it used to reach first and then index an empty binary list:
    # both refusals are the pass's own and the argv is unchanged, but which one
    # is cheapest changed - a required argument is named before the pass reads
    # the model oracle to judge a name (`ab` already refuses on `--bin` first).
    CASES = [(("ab", "--models", "A"), "ab needs at least two --bin"),
             (("layout", "--models", "no/such-model"), "layout needs at least one --bin"),
             (("compare", "nosuch-a", "nosuch-b"), "no (unique) history file for nosuch-a"),
             (("history-report", "nosuch"), "no (unique) history file for nosuch"),
             (("tlcbase-report", "nosuch"), "no (unique) history file for nosuch"),
             (("scale-report", "nosuch"), "no (unique) history file for nosuch")]

    def test_each_moved_pass_refuses_through_its_own_handler(self):
        for argv, message in self.CASES:
            with self.subTest(argv=argv):
                result = run_bench(list(argv))
                self.assertEqual(result.returncode, 1, f"{result.command}: {result.stderr[-400:]}")
                self.assertIn(message, result.stderr, result.command)
                self.assertNotIn("Traceback", result.stderr, result.command)
                # Refused before any measurement: nothing was recorded or run.
                self.assertNotIn("PASS", result.stdout)


class OneEntrypointModuleIdentity(unittest.TestCase):
    """The entry point is one module, also when a pass imports it (HARNESS-03).

    A pass reaches its collaborators through the entry point module
    (`bench.tlx`), the way bench_profile/bench_ttfr/bench_suite do, so that name
    must resolve to the running entry point. Running as a script the entry point
    is `__main__`: without publishing itself under its import name, the pass's
    first `import bench` loads a second, identical copy of every global — the
    duplicate module identity HARNESS-03 names, and the namespace a test patches
    a pass in through stops being the one the pass reads.
    """

    # (argv, the pass module it enters) for every pass the entry point dispatches
    # to a module of its own; each argv is the one that pass refuses cheapest.
    MOVED = [(("ab", "--models", "A"), "benchmarking.commands.ab", "ab needs at least two --bin"),
             (("compare", "nosuch-a", "nosuch-b"), "benchmarking.commands.history",
              "no (unique) history file for nosuch-a"),
             (("history-report", "nosuch"), "benchmarking.commands.history",
              "no (unique) history file for nosuch"),
             (("tlcbase-report", "nosuch"), "benchmarking.commands.tlcbase",
              "no (unique) history file for nosuch"),
             (("scale-report", "nosuch"), "benchmarking.commands.scale",
              "no (unique) history file for nosuch")]

    def test_a_pass_reaches_the_running_entry_point_not_a_second_copy(self):
        # `ab --models A` enters the A/B pass (whose first statement imports
        # `bench`) and is then refused for the missing --bin: the pass ran, and
        # the probe needs no binary. Known-bad before the entry point published
        # itself: this same run reported `import time: ... | bench`.
        for argv, pass_module, message in self.MOVED:
            with self.subTest(argv=argv):
                result, imported = entry_point_imports(list(argv))
                self.assertEqual(result.returncode, 1, f"{result.command}: {result.stderr[-400:]}")
                self.assertIn(message, result.stderr, result.command)
                # The control: the pass the case names really ran, so its own
                # `import bench` did happen and would show up below.
                self.assertIn(pass_module, imported, f"{result.command}: import probe reported {imported[:5]}")
                self.assertNotIn("bench", imported,
                                 f"{result.command}: the pass imported a second copy of the entry point")


class TlcbaseMergeSlices(unittest.TestCase):
    """`tlcbase-merge` joins the slices of one TLC revision.

    Slices cover disjoint models and each measures the worker counts it was
    asked for, so the merged baseline covers the union of the inputs' workers:
    the check that every input declared the same `workers` refused every real
    lane set (the lanes split 1-worker and 16-worker keys across machines).
    Where two inputs do cover the same model and worker count, the run that
    proves more wins -- a completed run over a timeout, and between two
    timeouts the longer bound -- which is the order the store's `evidence`
    applies, not the last file read.
    """

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.dir = Path(self.tmp.name)

    def lane(self, name, models, workers, tla="rev-a"):
        h = {"kind": "tlc-baseline", "tla2tools": {"revision": tla, "short": tla[:7]}, "workers": workers,
             "timeout_s": 3600, "date": "2026-10-09 12:00:00", "date_end": "2026-10-09 12:30:00",
             "machine": "x86_64, tencent SA5.4XLARGE32", "models": models}
        path = self.dir / name
        path.write_text(json.dumps(h))
        return path

    def run_merge(self, inputs):
        from benchmarking.commands import tlcbase
        out = self.dir / "merged.json"
        a = argparse.Namespace(inputs=[str(p) for p in inputs], out=str(out), set=[])
        tlcbase.cmd_tlcbase_merge(a)
        return bench.read_json(str(out))

    def test_differing_worker_headers_merge_into_their_union(self):
        one = self.lane("one.json", {"A": {"runs": {"1": {"result": "success", "wall_s": 5.0}}}}, [1])
        two = self.lane("two.json", {"B": {"runs": {"16": {"result": "timeout", "wall_s": 3600.0}}}}, [16])
        merged = self.run_merge([one, two])
        self.assertEqual(merged["workers"], [1, 16])
        self.assertEqual(sorted(merged["models"]), ["A", "B"])

    def test_the_stronger_run_wins_over_the_last_one_read(self):
        completed = {"result": "success", "wall_s": 5.0, "date": "2026-10-09 12:00:00"}
        timeout = {"result": "timeout", "wall_s": 3600.0, "date": "2026-10-09 13:00:00"}
        short_to = {"result": "timeout", "wall_s": 1800.0, "date": "2026-10-09 14:00:00"}
        long_to = {"result": "timeout", "wall_s": 7200.0, "date": "2026-10-09 11:00:00"}
        # A finished run beats a later timeout; the longer bound beats a shorter one.
        weak = self.lane("weak.json", {"A": {"runs": {"1": timeout}}, "B": {"runs": {"1": short_to}}}, [1])
        strong = self.lane("strong.json", {"A": {"runs": {"1": completed}}, "B": {"runs": {"1": long_to}}}, [1])
        merged = self.run_merge([weak, strong])
        self.assertEqual(merged["models"]["A"]["runs"]["1"], completed)
        self.assertEqual(merged["models"]["B"]["runs"]["1"], long_to)
        # The same holds when the weaker run is read last.
        merged = self.run_merge([strong, weak])
        self.assertEqual(merged["models"]["A"]["runs"]["1"], completed)
        self.assertEqual(merged["models"]["B"]["runs"]["1"], long_to)

    def test_another_tla2tools_revision_is_refused(self):
        one = self.lane("one.json", {"A": {"runs": {"1": {"result": "success", "wall_s": 1.0}}}}, [1], tla="rev-a")
        two = self.lane("two.json", {"B": {"runs": {"1": {"result": "success", "wall_s": 1.0}}}}, [1], tla="rev-b")
        with self.assertRaises(SystemExit) as caught:
            self.run_merge([one, two])
        self.assertIn("other tla2tools", str(caught.exception))


class HistoryPathResolution(unittest.TestCase):
    """A baseline name resolves to the canonical file, never to a slice.

    A baseline is measured in slices on separate machines and each slice is
    committed as `tlc-<rev>-lane<s>.json` next to the canonical merged
    `tlc-<rev>-...json`. The prefix lookup then matched all of them and refused
    the name as ambiguous, so `tlcbase-report tlc-<rev>` -- the documented way
    to read a baseline -- could not resolve it at all. The canonical file now
    wins, but two slices with no canonical file stay an error: picking one
    would silently report a fraction of the corpus.
    """

    fmt = staticmethod(bench.history_path)

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.dir = Path(self.tmp.name)
        self.addCleanup(setattr, bench, "HISTORY", bench.HISTORY)
        bench.HISTORY = str(self.dir)

    def touch(self, *names):
        for name in names:
            (self.dir / name).write_text("{}")

    def test_the_canonical_file_wins_over_its_slices(self):
        self.touch("tlc-rev-SA5.4XLARGE32.json", "tlc-rev-laneF2.json", "tlc-rev-laneH3a.json")
        self.assertEqual(self.fmt("tlc-rev"),
                         os.path.join(str(self.dir), "tlc-rev-SA5.4XLARGE32.json"))

    def test_slices_alone_stay_ambiguous(self):
        self.touch("tlc-rev-laneF2.json", "tlc-rev-laneH3a.json")
        with self.assertRaises(SystemExit) as caught:
            self.fmt("tlc-rev")
        self.assertIn("no (unique) history file for tlc-rev", str(caught.exception))

    def test_one_slice_alone_still_resolves(self):
        self.touch("tlc-rev-laneF2.json")
        self.assertEqual(self.fmt("tlc-rev"), os.path.join(str(self.dir), "tlc-rev-laneF2.json"))

    def test_an_exact_file_and_path_win_first(self):
        self.touch("tlc-rev.json", "tlc-rev-laneF2.json")
        self.assertEqual(self.fmt("tlc-rev"), os.path.join(str(self.dir), "tlc-rev.json"))
        self.assertEqual(self.fmt(str(self.dir / "tlc-rev-laneF2.json")),
                         str(self.dir / "tlc-rev-laneF2.json"))


if __name__ == '__main__':
    unittest.main()
