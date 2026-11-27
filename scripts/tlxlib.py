"""Shared policies for the repository's Python drivers (TLC semantics live in tlc)."""
import tempdirs

from harness.git import run as run_git
from harness.process import ProcResult, capture as _run_proc
from harness.storage import atomic_json_update

import contextlib, fcntl, fnmatch, glob, json, math, os, re, shutil, subprocess, time
from dataclasses import dataclass

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TP = os.path.join(ROOT, "third_party")
DEFAULT_JOBS = 3
CLASSPATH_DIRS = [os.path.join(TP, path) for path in ("community", "tlapm/library", "apalache")]
TLX_ENV_KEEP = {"TLX_CACHE", "TLX_JAVA", "TLX_CLOUD_HOST", "TLX_TLC_XMX", "TLX_RUSTC_SLOTS"}
# `tlc_heap` pins 4 GB (`TLX_TLC_XMX`) for the local drivers; a *measured* TLC
# run must instead keep the JVM's default max heap, which is the documented
# baseline method and what the oracle uses (docs/testing.md "TLC baseline").
# This inert JVM property is that request: it travels in the command line, so
# `tlc_heap` can see it, and the JVM ignores it.
TLC_JVM_DEFAULT_HEAP = "-Dtlx.tlc.heap=default"
NATIVE_REPORT = re.compile(r"native code: (\d+)/(\d+) actions, (\d+)/(\d+) invariants")
IR_REPORT = re.compile(r"IR nodes (\d+) \((\d+) boxed, (\d+) interpreter")
ACTION_REPORT = re.compile(r"(\d+)/(\d+) actions lowered, (\d+) fully typed; " + IR_REPORT.pattern)
PRED_REPORT = re.compile(r"IR (invariants|action properties): (\d+) lowered; " + IR_REPORT.pattern)
RESULT_LINE = re.compile(r"(PASS|FAIL) (\S+)\s")
OUTCOME_LINE = re.compile(r"(PASS|FAIL) (\S+)\s+.*?tlx=(\{.*?\}|\S+)")
TEST_LINE = re.compile(r"test (\S+) \.\.\. (ok|FAILED|ignored)")

# A path naming the home directory of the machine a golden was recorded on: a
# home prefix followed by the recording account's own name. A recorded artifact
# must never carry one - it leaks that account name and it makes the golden
# machine-dependent, so a checkout whose third_party lives elsewhere compares
# against a path that does not exist. The normalizers that produce goldens
# (`spectest.normalize`, `fuzz_spec.artifacts.normalize`) share this pattern to
# refuse one.
FOREIGN_HOME = re.compile(r"/(?:Users|home|root)/[A-Za-z0-9._-]+/")


def no_foreign_home(text, what):
    """`text`, having established that it names no machine's home directory.

    Raises `ValueError` naming the offending path instead of writing it into a
    golden, where nothing would notice until a contributor cloned the repository.
    """
    if match := FOREIGN_HOME.search(text):
        raise ValueError(f"{what}: the recorded output names {match.group(0)!r}; normalize that "
                         f"absolute path before recording or refreshing the artifact")
    return text


def include_args():
    return [arg for path in CLASSPATH_DIRS for arg in ("-I", path)]


_HELP = {}


def tlx_options(binary):
    """The options tlx binary `binary` lists in its help (cached): an older
    binary (e.g. verify.py --baseline's merge-base build) may not have the
    newer ones."""
    if binary not in _HELP:
        try:
            p = subprocess.run([binary, "-h"], capture_output=True, text=True)
            _HELP[binary] = set(re.findall(r"^  (-[a-zA-Z]+)", p.stdout, re.M))
        except OSError:
            # (Not runnable: its runs fail anyway; assume the current options.)
            _HELP[binary] = {"-interp", "-tlc"}
    return _HELP[binary]


def interp_args(binary):
    """The arguments that run tlx binary `binary` with the interpreter:
    ["-interp"] since the compiled tier is the default, [] for an older
    binary (whose default is the interpreter)."""
    return ["-interp"] if "-interp" in tlx_options(binary) else []


def parity_args(binary, args):
    """tlx arguments `args` for a TLC-parity test with `binary`: `-tlc`
    (TLC-compatible results) and the tier made explicit, the interpreter
    (tlx's semantic reference) unless `args` choose one (`-compile` or
    `-interp`). Flags the binary does not know (an older build) are left
    out: it then has these semantics by default."""
    args = list(args)
    if "-compile" not in args and "-interp" not in args:
        args = [*interp_args(binary), *args]
    if "-tlc" not in args and "-tlc" in tlx_options(binary):
        args = ["-tlc", *args]
    return args


def mode_args(binary, args=(), *, mode):
    """Explicit benchmark intent: default follows each binary's default; tiers pin it.

    Default A/B and time-to-first-result measurements deliberately compare
    historical defaults. Correctness drivers must use parity_args instead.
    """
    args = list(args)
    if mode == 'default':
        return args
    if mode == 'compile':
        return args if '-compile' in args or '-interp' in args else ['-compile', *args]
    if mode == 'interp':
        return [*interp_args(binary), *args]
    raise ValueError(f'unknown execution mode {mode!r}')


def parity_env(args):
    """The environment of a TLC-parity run with tlx arguments `args`: in the
    compiled tier, an IR verifier rejection (a compiler bug, which would
    otherwise silently run the model in the interpreter) fails the run
    (TLX_IR_VERIFY_HARD), unless the caller's environment sets it."""
    if "-interp" in args or "TLX_IR_VERIFY_HARD" in os.environ:
        return {}
    return {"TLX_IR_VERIFY_HARD": "1"}


def tlx_env(strip_tlx=False, *, drop=(), classpath=False, extra=None):
    env = {key: value for key, value in os.environ.items()
           if key not in drop and not (strip_tlx and key.startswith("TLX_") and key not in TLX_ENV_KEEP)}
    if classpath:
        env["TLX_CLASSPATH"] = os.pathsep.join(CLASSPATH_DIRS)
    env.update(extra or {})
    return env


def local_path(path):
    marker = "third_party" + os.sep
    index = path.find(marker)
    return os.path.join(ROOT, path[index:]) if index >= 0 else path


EXTERNAL_PREFIX = "ext/"
EXTERNAL_ORACLE = "tlc-ext"


def load_oracle(filter="", ids=(), oracles=()):
    """The models of the TLC oracle corpus/out/tlc.json (and of the external
    oracle when `filter` or `ids` name external models, and of each extra
    oracle file corpus/out/<name>.json of `oracles`, e.g. tlc-ext-large)
    whose id contains `filter`, only those of `ids` if given."""
    data = {}
    path = os.path.join(ROOT, "corpus", "out", "tlc.json")
    if os.path.exists(path):
        with open(path) as source:
            data = json.load(source)
    # (No ids, e.g. difftest's default --ids "": every model; "".split(",") is [""].)
    ids = {i for i in (ids.split(",") if isinstance(ids, str) else ids) if i}
    names = [o for o in (oracles.split(",") if isinstance(oracles, str) else oracles) if o]
    # The external models (corpus/external.json) are only selected by name:
    # the default selection is the Examples corpus.
    if filter.startswith(EXTERNAL_PREFIX) or any(i.startswith(EXTERNAL_PREFIX) for i in ids):
        names.insert(0, EXTERNAL_ORACLE)
    for name in names:
        path = os.path.join(ROOT, "corpus", "out", name + ".json")
        if os.path.exists(path):
            with open(path) as source:
                data.update(json.load(source))
    return {key: {**model, **{field: local_path(model[field]) for field in ("tla", "cfg") if field in model}}
            for key, model in data.items() if filter in key and (not ids or model["id"] in ids)}


# Correctness drivers build and run the tlx binary of the fast profile
# (Cargo.toml: release optimizations without LTO, 16 codegen units, incremental;
# target/<profile>/tlx). Benchmarks pass profile="release". --release (or
# TLX_BUILD_PROFILE=release) selects the release build for a single run.
FAST_PROFILE = "test-release"
PROFILE_ENV = "TLX_BUILD_PROFILE"


def build_profile(release=False):
    return "release" if release else os.environ.get(PROFILE_ENV) or FAST_PROFILE


def profile_dir(profile):
    return {"dev": "debug", "test": "debug", "bench": "release"}.get(profile, profile)


def add_profile_args(ap):
    ap.add_argument("--release", action="store_true",
                    help=f"build and run the release binary (default: the {FAST_PROFILE} profile, or ${PROFILE_ENV})")
    ap.add_argument("--profile", default=None, help="cargo profile of the tlx binary (overrides --release)")


def profile_of(args):
    return args.profile or build_profile(args.release)


@contextlib.contextmanager
def build_tlx(copy=True, *, profile=None, prefix="tlx-run-", build=True):
    profile = profile or build_profile()
    if build:
        subprocess.run(["cargo", "build", "-q", "-p", "tlx", "--profile", profile], cwd=ROOT, check=True)
    binary = os.path.join(ROOT, "target", profile_dir(profile), "tlx")
    if not copy:
        yield binary
        return
    with tempdirs.TemporaryDirectory(prefix=prefix, dir=os.path.join(ROOT, "target"), owner_root=ROOT) as private:
        target = os.path.join(private, "tlx")
        shutil.copy2(binary, target)
        yield target


def cloud_host():
    return os.environ.get("TLX_CLOUD_HOST") == "1"


def heap_pinned(options):
    """True when `options` already pin the JVM's maximum heap."""
    return any(opt.startswith("-Xmx") or opt.startswith("-XX:MaxHeapSize") for opt in options)


def tlc_heap(cmd):
    if heap_pinned(cmd) or TLC_JVM_DEFAULT_HEAP in cmd:
        return list(cmd)
    heap = os.environ.get("TLX_TLC_XMX") or "4g"
    if not re.fullmatch(r"[1-9][0-9]*[kKmMgG]?", heap):
        raise SystemExit("STOP: invalid TLX_TLC_XMX heap size")
    return [cmd[0], "-Xmx" + heap, *cmd[1:]]


def tlc_lock_dir():
    """Git's private worktree directory survives driver scratch directories."""
    private = git("rev-parse", "--absolute-git-dir", cwd=ROOT)
    return os.path.join(private, "tlx-tlc-slots")


@contextlib.contextmanager
def tlc_slot():
    if cloud_host():
        yield
        return
    directory = tlc_lock_dir()
    os.makedirs(directory, exist_ok=True)
    with contextlib.ExitStack() as stack:
        slots = [stack.enter_context(open(os.path.join(directory, str(i)), "a+")) for i in range(2)]
        acquired = None
        while acquired is None:
            for slot in slots:
                try:
                    fcntl.flock(slot, fcntl.LOCK_EX | fcntl.LOCK_NB)
                    acquired = slot
                    break
                except BlockingIOError:
                    pass
            if acquired is None:
                time.sleep(.1)
        try:
            yield acquired
        finally:
            fcntl.flock(acquired, fcntl.LOCK_UN)


def check_tlc_model(cmd, cwd=None, *, allow_local_heavy=False):
    """Match configuration, not just module: reduced configs stay usable.

    Basenames also identify copied scratch specs. External manifest tiers and
    the Examples' >=15s bench large set (plus scaling/stress configs) are heavy.
    """
    if cloud_host() or allow_local_heavy:
        return
    cwd = cwd or ROOT
    name = cmd[-1] if cmd[-1].endswith(".tla") else cmd[-1] + ".tla"
    spec = os.path.realpath(os.path.join(cwd, name))
    config = cmd[cmd.index("-config") + 1] if "-config" in cmd else os.path.splitext(cmd[-1])[0] + ".cfg"
    config = config if config.endswith(".cfg") else config + ".cfg"
    cfg = os.path.realpath(os.path.join(cwd, config))
    def matches(tla, model_cfg):
        return ((spec == os.path.realpath(tla) and cfg == os.path.realpath(model_cfg)) or
                (any(part.startswith("tlx-scratch-") for part in spec.split(os.sep)) and
                 os.path.basename(spec) == os.path.basename(tla) and os.path.basename(cfg) == os.path.basename(model_cfg)))
    heavy = None
    path = os.path.join(ROOT, "corpus", "external.json")
    if os.path.exists(path):
        with open(path) as source:
            manifest = json.load(source)
        for model in manifest["models"]:
            base = os.path.join(ROOT, "third_party", "external", model["repo"])
            if model["tier"] in ("medium", "large", "huge") and matches(os.path.join(base, model["tla"]), os.path.join(base, model["cfg"])):
                heavy = f"ext/{model['repo']}/{model['name']} ({model['tier']})"
                break
    if heavy is None:
        oracle = os.path.join(ROOT, "corpus", "out", "tlc.json")
        if os.path.exists(oracle):
            with open(oracle) as source:
                for model in json.load(source).values():
                    if model.get("tlc", {}).get("wall_s", 0) >= 15 and matches(local_path(model["tla"]), local_path(model["cfg"])):
                        heavy = model["id"]
                        break
        for path in glob.glob(os.path.join(ROOT, "third_party", "Examples", "specifications", "*", "manifest.json")):
            if heavy:
                break
            with open(path) as source:
                manifest = json.load(source)
            for module in manifest["modules"]:
                for model in module.get("models", []):
                    runtime = model.get("runtime", "unknown")
                    if not runtime or runtime == "unknown":
                        continue
                    h, m, sec = (int(part) for part in runtime.split(":"))
                    if h * 3600 + m * 60 + sec >= 15:
                        base = os.path.join(ROOT, "third_party", "Examples")
                        if matches(os.path.join(base, module["path"]), os.path.join(base, model["path"])):
                            heavy = model["path"]
                            break
    if any(part in cfg.split(os.sep) for part in ("scaling", "stress")):
        heavy = cfg
    if heavy:
        raise SystemExit(f"STOP: local heavy TLC model {heavy}; use cloud_verify.py or --allow-local-heavy")


# The directory a model's run starts in. A spec opens its inputs relative to the
# working directory - TLC's Java overrides (`new File(path)`) and tlx's native
# `ndJsonDeserialize` both use the path as given - so a runner has to start it in
# the directory its inputs are relative to, and TLC and tlx have to agree on it.
# By default that is the spec's own directory (`docs/testing.md`, the corpus
# convention: a spec writes its CSV/JSON output next to itself). `"cwd": "root"`
# names a model whose spec reads inputs relative to the corpus root instead - the
# directory the corpus manifest's paths are relative to. Upstream's Examples CI
# runs TLC from the Examples root with those relative paths
# (`.github/scripts/check_small_models.py`, `--examples_root .`), so a spec that
# names `specifications/<dir>/<file>` resolves it there and nowhere else.
CORPUS_ROOT_CWD = "root"


def model_cwd(m):
    """The working directory of one run of model `m` (see `CORPUS_ROOT_CWD`).

    `m["cwd"]` names it: the spec's own directory (the default) or the corpus
    root `m["root"]` for a model whose inputs are named relative to it. A model
    that writes files is staged into a copy of the directory it runs in
    (`tlc.model_scratch_dir`), and the combination this helper cannot express is
    refused. The benchmark's own, frozen staging does not consult this helper.
    """
    if m.get("cwd") != CORPUS_ROOT_CWD:
        # (A relative spec path is relative to the caller's own directory: the
        # run keeps that directory, as it did before this helper existed. So
        # does a fixture without a spec path at all.)
        return os.path.dirname(m.get("tla") or "") or None
    root = m.get("root")
    if not root:
        raise ValueError(f'{m.get("id", m.get("tla"))}: `"cwd": "root"` needs the model\'s corpus `root`')
    if m.get("scratch"):
        raise ValueError(f'{m.get("id")}: `"cwd": "root"` and a model that writes files are not supported together')
    return root


def run_tlc_proc(cmd, timeout=None, *, cwd=None, allow_local_heavy=False, **kwargs):
    check_tlc_model(cmd, cwd, allow_local_heavy=allow_local_heavy)
    with tlc_slot() as slot:
        # Keep the slot alive in the JVM if its driver is killed abruptly.
        if slot is not None:
            kwargs["pass_fds"] = (*kwargs.get("pass_fds", ()), slot.fileno())
        return _run_proc(tlc_heap(cmd), timeout, cwd=cwd, **kwargs)


def run_proc(cmd, timeout=None, *, allow_local_heavy=False, **kwargs):
    """All driver TLC launches share the heap, model and concurrency guards."""
    if "tlc2.TLC" in cmd:
        return run_tlc_proc(cmd, timeout, allow_local_heavy=allow_local_heavy, **kwargs)
    return _run_proc(cmd, timeout, **kwargs)


def json_update(path, update, *, indent=1):
    """Compatibility adapter: atomic replacement; callers serialize updates."""
    atomic_json_update(path, update, indent=indent)


def git(*args, cwd=ROOT, check=True, strip=True):
    output = run_git(*args, cwd=cwd, check=check).stdout
    return output.strip() if strip else output


def main_checkout():
    if os.environ.get("TLX_MAIN"):
        return os.environ["TLX_MAIN"]
    common = git("rev-parse", "--git-common-dir", check=False)
    return os.path.dirname(os.path.realpath(os.path.join(ROOT, common))) if common else ROOT


def fmt_secs(seconds):
    return f"{seconds:.0f}s" if seconds < 60 else f"{int(seconds // 60)}m{int(seconds % 60):02d}s"


def geomean(values):
    values = [value for value in values if value and value > 0 and value == value]
    return math.exp(sum(map(math.log, values)) / len(values)) if values else float("nan")


def expected_match(entries, suite, tid, kind=None, *, match_result=True):
    return next((entry for entry in entries if fnmatch.fnmatchcase(suite, entry["suite"])
                 and fnmatch.fnmatchcase(tid, entry["id"])
                 and (not match_result or entry.get("result", kind) == kind)), None)


CASE_STATUSES = frozenset(("pass", "fail", "xfail", "xpass", "error", "skip", "timeout"))
BAD_STATUSES = frozenset(("fail", "xpass", "error", "timeout"))


@dataclass(frozen=True)
class CaseResult:
    """One execution/comparison; semantic error verdicts belong in details, not status."""
    id: str
    status: str
    details: dict

    def __post_init__(self):
        if not self.id or self.status not in CASE_STATUSES or not isinstance(self.details, dict):
            raise ValueError("invalid case result")


def judge_case(case, entries=(), suite="", *, known=None):
    """Apply expected differences once. Infrastructure errors can never be expected."""
    if case.status not in ("pass", "fail", "timeout"):
        return case
    kind = case.details.get("kind")
    entry = known or expected_match(entries, suite, case.id, kind,
                                   match_result=case.status != "pass")
    if not entry:
        return case
    if case.status == "pass":
        status = "pass" if entry.get("flaky") else "xpass"
    else:
        status = "xfail"
    return CaseResult(case.id, status, {**case.details, "expected": entry.get("reason", "known difference")})


def load_expected_cases(path=None):
    path = path or os.path.join(ROOT, "tests", "expected_failures.json")
    if not os.path.exists(path):
        return []
    with open(path) as source:
        return json.load(source)["expected_failures"]


def add_result_args(ap):
    ap.add_argument("--results-json", help="write the structured case report for verification")
    ap.add_argument("--suite", help="expected-failure suite name (normally inferred from the run mode)")


def finish_cases(cases, selected, path=None, *, coverage=None, suite=None):
    """The shared gate: validate the completion manifest, count statuses and decide exit.

    `suite` (the expected-failure suite name) is recorded in the report, so a
    downloaded JSON file identifies the run mode independently of its name."""
    from dataclasses import asdict
    cases, selected = list(cases), list(selected)
    ids = [c.id for c in cases]
    errors = []
    if not selected:
        errors.append("zero selected cases")
    if len(set(selected)) != len(selected) or len(set(ids)) != len(ids) or set(ids) != set(selected):
        errors.append("case results do not match the selection")
    counts = {status: sum(c.status == status for c in cases) for status in sorted(CASE_STATUSES)}
    if not any(c.status != "skip" for c in cases):
        errors.append("no case executed")
    if coverage and (coverage.get("missing", 0) or coverage.get("stale", 0)):
        errors.append("incomplete oracle coverage")
    report = {"version": 1, "suite": suite, "selected": selected, "cases": [asdict(c) for c in cases],
              "counts": counts, "coverage": coverage or {}, "errors": errors,
              "exit_code": int(bool(errors) or any(c.status in BAD_STATUSES for c in cases))}
    if path:
        json_update(path, lambda _: report)
    return report


def read_case_report(path, returncode):
    """Recompute the judgment; a successful report never overrides a failed process."""
    with open(path) as source:
        report = json.load(source)
    if report["version"] != 1:
        raise ValueError("unsupported case report version")
    cases = [CaseResult(**c) for c in report["cases"]]
    checked = finish_cases(cases, report["selected"], coverage=report["coverage"])
    if any(checked[k] != report[k] for k in ("counts", "errors", "exit_code")):
        raise ValueError("inconsistent case report")
    if returncode != checked["exit_code"]:
        checked["errors"].append(f"driver exit {returncode} disagrees with report exit {checked['exit_code']}")
    if returncode:
        checked["errors"].append(f"driver failed (exit {returncode})")
    checked["exit_code"] = int(bool(checked["errors"]) or bool(checked["exit_code"]))
    return cases, checked


def case_summary(report):
    counts = ", ".join(f"{n} {status}" for status, n in report["counts"].items() if n)
    errors = "; ".join(report["errors"])
    return f"judgment: {counts or 'no cases'}; exit={report['exit_code']}" + (f"; {errors}" if errors else "")
