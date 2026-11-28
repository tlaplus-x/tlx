"""Provider-neutral cloud verification, SSH, setup, uploads and result fetching.

The required provider contract lives in cloud.protocol.Provider. AWS uses its
SDK; Aliyun and Tencent share cloud.transport for bounded JSON CLI capture.
Provider-specific refusal and optional capability policies remain in adapters.
"""
import contextlib, dataclasses, datetime, hashlib, http.client, json, os, re, shlex, shutil, socket, ssl, subprocess, sys, threading, time, urllib.request, uuid

from tlxlib import ROOT, git, fmt_secs
from cloud import deadline as request_deadline
KEY_FILE = os.path.expanduser("~/.ssh/tlx-verify")
INFRA_FAIL = 3

# What the tests read from third_party/ (no Java remotely: tla2tools.jar is not needed).
# external/: the fetched external corpora (scripts/fetch-external.py) of the
# corpus-ext* suites.
THIRD_PARTY_FILTER = [
    "--exclude=.git/", "--exclude=*.jar", "--exclude=*_TTrace_*",
    "--include=/Examples/***", "--include=/community/***", "--include=/apalache/***",
    "--include=/tlapm/", "--include=/tlapm/library/***", "--include=/external/***", "--exclude=*",
]

# Bench and oracle mode (cloud_verify.py --bench, --oracle) also run TLC:
# tla2tools.jar and the community modules jar (scripts/tlc.py's class path)
# are uploaded too.
BENCH_THIRD_PARTY_FILTER = ["--include=/tla2tools.jar", "--include=/community/modules.jar"] + THIRD_PARTY_FILTER

# Oracle mode: the TLC result files of scripts/corpus.py that come back.
ORACLE_FILES = "tlc*.json"

TRIPLES = {"arm64": "aarch64-unknown-linux-gnu", "x86_64": "x86_64-unknown-linux-gnu"}

# Mirrors for China mainland (static.rust-lang.org and crates.io are slow or
# flaky from there).
RSPROXY = {
    "rustup_init": "https://rsproxy.cn/rustup-init.sh",
    "dist": "https://rsproxy.cn",
    "update_root": "https://rsproxy.cn/rustup",
    "index": "sparse+https://rsproxy.cn/index/",
}

# Environment variables that point subprocesses at a proxy.
PROXY_VARS = ("https_proxy", "HTTPS_PROXY", "http_proxy", "HTTP_PROXY", "all_proxy", "ALL_PROXY", "no_proxy", "NO_PROXY")


class Interrupted(BaseException):
    pass


def stop_code(message):
    """Stable stop classes; capacity fallback remains an advisory."""
    msg = message.lower()
    if "quota" in msg or "limitexceeded" in msg:
        return 20
    if any(word in msg for word in ("risk", "frozen", "blacklist", "qualification", "arrear", "insufficientbalance", "notenoughbalance")):
        return 21
    if any(word in msg for word in ("forbidden", "forbid", "unauthorized", "accessdenied", "permission", "camnoauth")):
        return 22
    if any(word in msg for word in ("account mismatch", "authfailure", "invalidaccesskey", "signature", "credentials")):
        return 24
    if "budget" in msg:
        return 25
    if any(word in msg for word in ("launch", "refused", "no spot offers")):
        return 23
    return INFRA_FAIL


class CloudStop(Exception):
    def __init__(self, message, code=None):
        self.message = message
        self.code = code if code is not None else stop_code(message)
        super().__init__("STOP: " + message)


class InfraError(CloudStop):
    pass


def mask_identity(text):
    """`text` with every account or user number (a run of 6 or more digits)
    replaced by `***` and its last 3 digits: identity lines and account
    errors end up in transcripts and logs (2026-10-08: `--list` printed the
    whole account and uin), while the suffix and the user type still tell
    two identities apart."""
    return re.sub(r"\d{6,}", lambda m: "***" + m.group()[-3:], str(text))


class AccountError(CloudStop):
    """The credentials are missing, invalid or belong to the wrong identity.
    The message is masked (`mask_identity`): it names the configured and the
    actual identity."""

    def __init__(self, message):
        super().__init__(mask_identity(message), 24)


class ProviderQuotaFull(InfraError):
    """The provider's dry run of the exact launch request reported a quota
    limit: refused before the real launch call (stop code 20)."""

    def __init__(self, message):
        super().__init__(message, 20)


class SkipOffer(Exception):
    """The launch was refused for this offer; `scope` says what to skip: 'zone' or 'region'."""

    def __init__(self, scope, msg):
        super().__init__(msg)
        self.scope = scope


def owner_tag(branch):
    """A portable, bounded tag value; preserve valid branch names verbatim."""
    safe = re.sub(r"[^A-Za-z0-9_./-]", "_", branch)
    if safe != branch or len(safe) > 64:
        safe = safe[:51] + "-" + hashlib.sha256(branch.encode()).hexdigest()[:12]
    return safe


def current_owner(required=True):
    branch = git("symbolic-ref", "--quiet", "--short", "HEAD", check=False)
    if not branch and not required:
        return None
    if not branch:
        raise CloudStop("cloud ownership needs a current git branch", 25)
    return owner_tag(branch)


def warning(msg):
    print(f"WARNING (not a stop condition): {msg}", flush=True)


def log(msg):
    if msg.startswith(("WARNING (not a stop condition):", "STOP:")):
        print(msg, flush=True)
        return
    print(f"[cloud {time.strftime('%H:%M:%S')}] {msg}", flush=True)


# The expected cloud identities live outside the repository, in a local JSON
# file (CONFIG_PATH, or $TLX_CLOUD_CONFIG; see docs/cloud-verification.md). A
# provider refuses to run without its entry: check_account compares the CLI's
# caller identity with this entry and never accepts whatever the CLI reports.
CONFIG_ENV = "TLX_CLOUD_CONFIG"
CONFIG_PATH = "~/.config/tlx/cloud.json"
# provider: (required fields, an example entry with placeholder values)
CONFIG_FIELDS = {
    "aws": (("account", "profile"), {"account": "123456789012", "profile": "tlx"}),
    "aliyun": (("arn", "profile"), {"arn": "acs:ram::1234567890123456:user/tlx", "profile": "tlx"}),
    "tencent": (("arn", "profile", "selfterm_role"),
                {"arn": "qcs::cam:100000000001:uin/100000000002", "profile": "tlx", "selfterm_role": "tlx-verify-selfterm"}),
}


def config_path():
    return os.path.expanduser(os.environ.get(CONFIG_ENV) or CONFIG_PATH)


def cloud_identity(provider):
    """The configured identity of `provider`: a dict of CONFIG_FIELDS[provider]
    (non-empty strings). Exits with instructions when it is missing."""
    fields, example = CONFIG_FIELDS[provider]
    path = config_path()
    how = (f"Create {path} (or point ${CONFIG_ENV} at another file) with an entry like\n"
           f"  {{\"{provider}\": {json.dumps(example)}}}\n"
           f"holding the identity the {provider} CLI profile must have (docs/cloud-verification.md).")
    try:
        with open(path, encoding="utf-8") as f:
            cfg = json.load(f)
    except FileNotFoundError:
        raise AccountError(f"cloud_verify: no cloud config {path}; refusing to run.\n{how}") from None
    except (OSError, ValueError) as e:
        raise AccountError(f"cloud_verify: cannot read cloud config {path} ({e}); refusing to run.\n{how}") from None
    entry = cfg.get(provider) if isinstance(cfg, dict) else None
    if not isinstance(entry, dict):
        raise AccountError(f"cloud_verify: {path} has no {provider!r} entry; refusing to run.\n{how}")
    missing = [k for k in fields if not isinstance(entry.get(k), str) or not entry[k]]
    if missing:
        raise AccountError(f"cloud_verify: the {provider!r} entry of {path} lacks {', '.join(missing)}; refusing to run.\n{how}")
    return {k: entry[k] for k in fields}


# Optional per-provider limits in the same entry: the account's spot instance
# quota (the provider's own limit, e.g. Tencent's LimitExceeded.UserSpotQuota)
# and the number of concurrent instances an owner may run without a grant
# that says more (cloud_verify.py --grant OWNER --slots N).
LIMIT_FIELDS = {"spot_instance_quota": None, "default_share": 1}


def cloud_limits(provider):
    """{"spot_instance_quota": int or None, "default_share": int} of
    `provider` from the cloud config (defaults for absent fields or a missing
    file: the identity check refuses that case separately). A present field
    that is not a positive integer refuses the run."""
    try:
        with open(config_path(), encoding="utf-8") as f:
            cfg = json.load(f)
    except (OSError, ValueError):
        cfg = {}
    entry = cfg.get(provider) if isinstance(cfg, dict) else None
    entry = entry if isinstance(entry, dict) else {}
    out = {}
    for key, default in LIMIT_FIELDS.items():
        value = entry.get(key, default)
        if value is not None and (isinstance(value, bool) or not isinstance(value, int) or value <= 0):
            raise AccountError(f"cloud_verify: {provider}.{key} in {config_path()} must be a positive integer, not {value!r}")
        out[key] = value
    return out


def no_proxy_env(base=None):
    """`base` (default os.environ) without proxy variables: a stable source address."""
    return {k: v for k, v in (base or os.environ).items() if k not in PROXY_VARS}


@dataclasses.dataclass
class Offer:
    price: float        # per hour, in the provider's currency
    region: str
    zone: str
    itype: str
    vcpus: int = 0
    deprioritized: bool = False   # e.g. the region's reported quota is too small: tried last
    market: str = "spot"          # or "on-demand" (pay-as-you-go: only with --on-demand, after every spot offer)


@dataclasses.dataclass
class SlotHolder:
    """One instance (or in-flight launch) that holds an account quota slot."""
    region: str
    id: str | None                # None: a launch reserved in the ledger whose instance is not known yet
    state: str                    # the provider's state, or "in flight"/"just launched" from the ledger
    owner: str | None             # the owner tag; "(untagged)" for an instance outside tlx's tags
    market: str = "spot"          # or "on-demand"
    deadline: float | None = None  # epoch seconds by which the dead-man's switch has ended it, if known
    source: str = "provider"      # or "ledger"


def rank_offers(offers):
    """Offers in launch order: spot before on-demand, deprioritized last,
    then cheapest, then fewest vCPUs (the same price for less is a smaller
    machine), then by name for a stable order."""
    return sorted(offers, key=lambda o: (o.market != "spot", o.deprioritized, o.price, o.vcpus, o.region, o.zone, o.itype))


def latest_prices(records, now=None):
    """{(zone, itype): price} from price-history records (dicts with zone,
    itype, price, time as an aware datetime): per zone and type, the newest
    record not in the future (or the oldest one if all are)."""
    now = now or datetime.datetime.now(datetime.timezone.utc)
    best = {}
    for r in records:
        key = (r["zone"], r["itype"])
        cur = best.get(key)
        if cur is None:
            best[key] = r
            continue
        past, cur_past = r["time"] <= now, cur["time"] <= now
        if past and (not cur_past or r["time"] > cur["time"]) or not past and not cur_past and r["time"] < cur["time"]:
            best[key] = r
    return {k: float(r["price"]) for k, r in best.items()}


def auto_release_time(now, minutes, minimum=30, margin=2):
    """The UTC release time `minutes` from `now` as yyyy-MM-ddTHH:mm:00Z,
    rounded up to a whole minute, at least `minimum` + `margin` minutes
    ahead (Aliyun rejects release times less than 30 minutes ahead; the
    margin covers the time until the API sees the request)."""
    now = now.astimezone(datetime.timezone.utc)
    t = now + datetime.timedelta(minutes=max(minutes, minimum + margin))
    if t.second or t.microsecond:
        t = t.replace(second=0, microsecond=0) + datetime.timedelta(minutes=1)
    return t.strftime("%Y-%m-%dT%H:%M:00Z")


def deadman_user_data(max_minutes, extra_ssh_ports=()):
    """User data (a shell script run as root at first boot): a shutdown
    `max_minutes` after boot, and an extra sshd on `extra_ssh_ports` (for
    networks that block outbound port 22)."""
    s = f"#!/bin/bash\n# dead-man's switch\nshutdown -h +{max_minutes}\n"
    if extra_ssh_ports:
        ports = " ".join(f"-p {p}" for p in extra_ssh_ports)
        # A transient unit, so that the end of the user-data run does not take it down.
        s += ("# a second sshd on other ports (the main one keeps port 22)\n"
              f"mkdir -p /run/sshd && systemd-run --unit=tlx-sshd-extra /usr/sbin/sshd -D {ports} -o PidFile=/run/sshd-extra.pid\n")
    return s


def local_toolchain():
    """The toolchain pinned in rust-toolchain.toml (so that both compile with
    the same compiler: a newer one may warn where this one does not), or
    stable when the file is missing or has no channel."""
    try:
        with open(os.path.join(ROOT, "rust-toolchain.toml")) as f:
            m = re.search(r'^\s*channel\s*=\s*"([^"]+)"', f.read(), re.M)
        return m.group(1) if m else "stable"
    except OSError:
        return "stable"


# --- Prelaunch local checks (pure, unit-tested) -------------------------------

# The release Clippy that verify.py's build suite and bench_script run on the
# instance rejects a lint error only after an instance has been paid for
# (2026-10-08: items_after_test_module burned a launch). cloud_verify runs the
# same command here first, at the shared machine's job budget.
CLIPPY_JOBS = 3


def workspace_lints(root=ROOT):
    """Whether the revision declares [workspace.lints] in its root Cargo.toml:
    only such revisions run Clippy in the build suite, so only they need the
    preflight (the predicate verify.py's has_workspace_lints uses)."""
    try:
        with open(os.path.join(root, "Cargo.toml"), encoding="utf-8") as f:
            return any(line.strip().startswith("[workspace.lints") for line in f)
    except OSError:
        return False


def clean_worktree(root=ROOT):
    """True when no tracked file differs from HEAD, so what a local Clippy
    compiles is the tree a marker or commit describes, not uncommitted edits."""
    try:
        return subprocess.run(["git", "diff", "HEAD", "--quiet"], cwd=root,
                              stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL).returncode == 0
    except OSError:
        return False


def full_gate_marker(root=ROOT):
    """The merge_gate marker when it authorizes exactly this checked-out tree
    with scope=full, else None: that gate already ran release Clippy with
    warnings denied, so the same tree does not pay for it twice. A narrower
    marker says nothing about Clippy and is not accepted."""
    try:
        path = os.path.join(root, git("rev-parse", "--git-path", "tlx-merge-gate", cwd=root))
        with open(path, encoding="utf-8") as f:
            marker = json.load(f)
        if (marker.get("version") == 1 and marker.get("scope") == "full"
                and clean_worktree(root)
                and marker.get("tree") == git("write-tree", cwd=root)
                and marker.get("head") == git("rev-parse", "HEAD", cwd=root)):
            return marker
    except (OSError, ValueError, TypeError, subprocess.SubprocessError):
        pass
    return None


def clippy_preflight(root=ROOT, rev=None, runner=None, marker=None, jobs=CLIPPY_JOBS, dry_run=False):
    """Run the build suite's Clippy before an instance is provisioned, so a lint
    error cannot consume a launch (HARNESS-08). Returns (ok, note, ran). A dry
    run, a revision without [workspace.lints], a launch of a revision other than
    the checked-out tree, a tree already covered by a full-scope merge_gate
    marker and a machine without a local cargo are skipped with a note rather
    than refused: none of them can be linted here, and the remote suite still
    checks the last two before it runs anything. `ran` states whether that
    exact command is known to have covered this tree here (it passed, or a
    full-scope marker records it), so a bench instance can skip paying for it
    again (`remote_clippy_needed`). `runner` (argv, cwd) -> exit status is a
    test double."""
    if dry_run:
        return True, "prelaunch clippy skipped: a dry run provisions nothing", False
    if not workspace_lints(root):
        return True, "prelaunch clippy skipped: this revision declares no [workspace.lints]", False
    if rev is not None and rev != git("rev-parse", "HEAD", cwd=root):
        return True, f"prelaunch clippy skipped: revision {str(rev)[:12]} is not this worktree's HEAD", False
    if marker is None:
        marker = full_gate_marker(root)
    if marker:
        return True, f"prelaunch clippy skipped: merge_gate marker covers tree {str(marker.get('tree'))[:12]} (scope=full)", True
    cargo = shutil.which("cargo")
    if cargo is None and runner is None:
        return True, "prelaunch clippy skipped: no local cargo; the remote build suite still checks it", False
    cmd = [cargo or "cargo", "clippy", "--workspace", "--release", "--all-targets",
           "-j", str(jobs), "--", "-D", "warnings"]
    run = _run_status if runner is None else runner
    rc = run(cmd, cwd=root)
    if rc == 0:
        return True, "prelaunch clippy passed", True
    return False, (f"prelaunch clippy failed (exit {rc}); the remote build suite would refuse this tree "
                   "after the instance was paid for"), False


def remote_clippy_needed(ran, platform=None):
    """Whether a bench instance still has to run the build suite's Clippy.

    `ran` is clippy_preflight's verdict (it passed here, or a full-scope
    merge_gate marker records it) on the revision that is uploaded, so the same
    command on the same tree cannot report anything new there -- except across
    operating systems: lints behind `cfg(target_os = "linux")` are invisible to
    a macOS Clippy, and letting one reach the timed run is exactly what the
    instance's own check prevents. A preflight that was skipped (no cargo,
    another revision, a dry run, no [workspace.lints]) never stands in for it.
    `platform` (sys.platform) is injectable for the test."""
    platform = sys.platform if platform is None else platform
    return not (ran and platform.startswith("linux"))


def _run_status(argv, cwd):
    """The exit status of `argv`, its output left on this terminal so a lint
    failure can be read without unpacking a captured result."""
    return subprocess.run(argv, cwd=cwd).returncode


def _stale_release(binary):
    """The first source under crates/ newer than `binary` (or `binary` itself
    when it is missing): whether `bench.py` would refuse to measure it."""
    from benchmarking import machine as bench_machine   # a leaf library: no CLI, no cloud
    return binary if not os.path.exists(binary) else bench_machine.stale_source(binary)


def release_preflight(root=ROOT, build=None, dry_run=False, binary=None, stale=None):
    """Bring target/release/tlx up to date before an instance is provisioned.

    Bench mode never measures a binary older than the sources under crates/:
    `benchmarking.machine.require_fresh` (and the bench smoke's own guard for a
    missing binary) builds first and then stops with "still older than ... after
    cargo build --release" when that build did not help. That message carries no
    exit status of the build, so a build that failed after a crates-touching
    merge read as a stale tree, and the launch attempt was wasted without naming
    the cause (2026-10-10).

    This is that one build, before anything is provisioned and with its exit
    status checked: a tree that cannot build refuses the launch with the build's
    own error, and a tree that can is left fresh for every later check.
    Returns (ok, note). A dry run provisions nothing, so it builds nothing.
    """
    if dry_run:
        return True, "prelaunch build skipped: a dry run provisions nothing"
    if binary is None:
        from benchmarking import machine as bench_machine
        binary = bench_machine.TLX
    older = (stale or _stale_release)(binary)
    if older is None:
        return True, "prelaunch build skipped: target/release/tlx is up to date"
    cargo = shutil.which("cargo")
    if cargo is None and build is None:
        return True, f"prelaunch build skipped: no local cargo (target/release/tlx is older than {older})"
    argv = [cargo or "cargo", "build", "--release", "-p", "tlx"]
    rc = _run_status(argv, root) if build is None else build(argv)
    if rc != 0:
        return False, (f"the release build failed (exit {rc}); nothing was provisioned. Fix the build "
                       "(cargo build --release -p tlx), or launch a revision that compiles")
    still = (stale or _stale_release)(binary)
    if still:
        return False, (f"target/release/tlx is still older than {still} after cargo build --release: cargo "
                       "does not track that file as an input of the binary, so the build cannot cover it")
    return True, "prelaunch build ok"


# --- Remote setup scripts (pure: unit-tested) ---------------------------------

ENV_FILE = "~/tlx-env.sh"   # sourced before verify.py runs


RUSTUP_UPSTREAM = "https://sh.rustup.rs"


def rust_script(source, toolchain, arch, tarball=None):
    """Remote shell installing Rust `toolchain` and writing ~/tlx-env.sh.
    source: 'upstream' (rustup from static.rust-lang.org), 'mirror' (rustup
    through rsproxy.cn, falling back to upstream when the mirror serves nothing
    usable), 'upload' (the standalone tarball `tarball`, already copied to ~,
    installed without rustup).

    A mirror answer that is empty (rsproxy.cn served 0 bytes) reads as success
    to `curl | sh` and installs nothing, so the download is written to a file
    and required to be non-empty first; a failed or empty mirror install falls
    back to upstream, writing the upstream environment to ~/tlx-env.sh so no
    later rustup call revisits the broken mirror (2026-11-28). The components
    of rust-toolchain.toml come with the toolchain, so that the first cargo run
    does not have to fetch them (rustup auto-installs missing components of the
    pinned toolchain, which would stall the verification mid-run)."""
    if source == "upload":
        name = os.path.basename(tarball)
        d = name[:-len(".tar.xz")]
        return ("set -e\ncd ~ && tar xJf " + shlex.quote(name) + "\n"
                f"./{d}/install.sh --prefix=$HOME/rust --without=rust-docs --disable-ldconfig >/dev/null\n"
                f"rm -rf {shlex.quote(d)} {shlex.quote(name)}\n"
                f"echo 'export PATH=$HOME/rust/bin:$PATH' > {ENV_FILE}\n"
                f". {ENV_FILE} && rustc --version\n")
    if source not in ("upstream", "mirror"):
        raise ValueError(f"unknown Rust source {source!r}")
    install = ("-y -q --profile minimal --default-toolchain " + toolchain
               + " -c rustfmt -c clippy")
    # (The `&&` list is an if/condition position under `set -e`: a failed
    # download stops the script instead of being masked by the pipeline's last
    # command.)
    upstream = (f'curl -sSfL {RUSTUP_UPSTREAM} -o "$init" && [ -s "$init" ]'
                f' && sh "$init" {install} >/dev/null 2>&1')
    s = ["set -e"]
    if source == "mirror":
        exports = (f"export RUSTUP_DIST_SERVER={RSPROXY['dist']} "
                   f"RUSTUP_UPDATE_ROOT={RSPROXY['update_root']}")
        s += [f"mirror_exports={shlex.quote(exports)}",
              'eval "$mirror_exports"']
    s += ['init=$(mktemp)']
    if source == "upstream":
        s += [upstream]
    else:
        s += [f'if curl -sSfL {RSPROXY["rustup_init"]} -o "$init" && [ -s "$init" ]'
              f' && sh "$init" {install} >/dev/null 2>&1; then',
              '  env_exports="$mirror_exports"',
              "else",
              "  echo " + shlex.quote(f"WARNING (not a stop condition): {RSPROXY['rustup_init']} "
                                    f"failed or served an empty file; installing Rust from {RUSTUP_UPSTREAM}") + " >&2",
              "  unset RUSTUP_DIST_SERVER RUSTUP_UPDATE_ROOT",
              "  env_exports=''",
              "  " + upstream,
              "fi"]
    # (Only the source that installed the toolchain goes into the environment
    # file; a fallback must not leave the broken mirror to a later rustup.)
    s += ["rm -f \"$init\"",
          f": > {ENV_FILE}",
          f"if [ -n \"${{env_exports:-}}\" ]; then printf '%s\\n' \"$env_exports\" >> {ENV_FILE}; fi",
          f"echo '. ~/.cargo/env' >> {ENV_FILE}",
          f". {ENV_FILE} && rustc --version"]
    return "\n".join(s) + "\n"


def cargo_config(source, vendor_dir=None):
    """~/.cargo/config.toml for the crates source: 'upstream' (none),
    'mirror' (rsproxy.cn sparse index), 'vendor' (`vendor_dir`)."""
    if source == "upstream":
        return None
    if source == "mirror":
        return ("[source.crates-io]\nreplace-with = 'rsproxy-sparse'\n"
                f"[source.rsproxy-sparse]\nregistry = \"{RSPROXY['index']}\"\n")
    if source == "vendor":
        return f"[source.crates-io]\nreplace-with = 'vendored-sources'\n[source.vendored-sources]\ndirectory = \"{vendor_dir}\"\n"
    raise ValueError(f"unknown crates source {source!r}")


BENCH_BINS = "target/bench-bins"   # under ~/tlx: the --bench-bin binaries, <NAME>/tlx
HEAD_BINARY = "target/release/tlx"   # under ~/tlx: the binary of the uploaded revision

# Bench subcommands that execute no tlx binary at all: `tlcbase` measures TLC
# alone (and its merge/report subcommands only read the files it wrote).
TLC_ONLY_COMMANDS = frozenset({"tlcbase", "tlcbase-merge", "tlcbase-report"})

# Bench subcommands, and the option that names the binary each one measures:
# omitting it falls back to building HEAD's target/release/tlx, so such a
# command still needs that build even when another binary option is present
# (`suite --base-bin ...` measures HEAD's binary against the base). A
# subcommand that is not here keeps the build. `liveness` is deliberately
# absent: its rustc probes link HEAD's own `target/release/deps/libtlx_*.rlib`,
# which only HEAD's build produces, whatever --before-bin/--after-bin name.
DEFAULT_HEAD_OPTION = {
    "suite": "--bin", "track": "--bin", "profile": "--bin", "coverage": "--bin",
    "disk": "--bin", "ab": "--bin", "perf": "--bin", "layout": "--bin",
    "ttfr": "--bin",
}

# Bench options whose value names a tlx binary, either as NAME=PATH (the
# repeatable --bin of ab/perf/layout/disk) or as a bare PATH
# (suite/profile/coverage and --after-bin). --stats-bin names one of those
# names, so it is not a path.
BINARY_OPTIONS = ("--bin", "--base-bin", "--before-bin", "--after-bin")


def parse_bench_bin(spec):
    """NAME=REV[:FEATURES] (FEATURES comma-separated cargo features of
    tlx-cli) -> (name, rev, features)."""
    name, sep, rest = spec.partition("=")
    rev, _, features = rest.partition(":")
    if not sep or not re.fullmatch(r"[A-Za-z0-9_.-]+", name) or not rev:
        raise ValueError(f"--bench-bin expects NAME=REV[:FEATURES], got {spec!r}")
    return name, rev, features


def bench_binary_paths(words):
    """The tlx binaries one `--bench` command names ([] when it names none)."""
    paths = []
    for i, w in enumerate(words):
        value = None
        for opt in BINARY_OPTIONS:
            if w == opt and i + 1 < len(words):
                value = words[i + 1]
            elif w.startswith(opt + "="):
                value = w[len(opt) + 1:]
            if value is not None:
                break
        if value is None:
            continue
        name, sep, rest = value.partition("=")
        # `--bin NAME=PATH` or a bare `--bin PATH`: NAME is the short label of a
        # binary, never a path, so the same split as parse_bench_bin's.
        paths.append(rest if sep and re.fullmatch(r"[A-Za-z0-9_.-]+", name) else value)
    return paths


def _is_head_binary(path):
    """Whether `path` names the uploaded revision's own binary: a relative
    `target/release/tlx`, its absolute form, or the `~/tlx` one."""
    norm = os.path.normpath(path)
    return norm == HEAD_BINARY or norm.endswith("/" + HEAD_BINARY)


def head_binary_needed(cmds):
    """Whether a bench pass executes the uploaded revision's own binary.

    A command that names the binary it measures and every other one it runs
    (`suite --bin target/bench-bins/<name>/tlx`, `ab --bin a=... --bin b=...`)
    never builds or runs `target/release/tlx`, and `tlcbase` runs TLC alone;
    building HEAD for those costs the instance a cold release build of the whole
    workspace for nothing. Everything else -- an unqualified `run`, `suite
    --base-bin ...` (whose --bin defaults to HEAD), a subcommand this does not
    recognize -- keeps the build: a command whose binary resolution is not
    provable here can never silently measure the wrong thing.
    """
    if not cmds:
        return True
    for c in cmds:
        try:
            words = shlex.split(c)
        except ValueError:
            return True
        if not words:
            return True
        sub = words[0]
        if sub in TLC_ONLY_COMMANDS:
            continue
        primary = DEFAULT_HEAD_OPTION.get(sub)
        if primary is None:
            return True
        if not any(w == primary or w.startswith(primary + "=") for w in words):
            return True          # omitting it measures HEAD's binary
        if any(_is_head_binary(p) for p in bench_binary_paths(words)):
            return True
    return False


def bench_script(home, cc, machine, bins, cmds, deadline_at=None, skip_head_build=False, skip_remote_clippy=False):
    """Remote shell of a bench run in ~/tlx (pure): record the machine, build
    the binaries the commands run, drop the cached TLC -workers N results that
    came with corpus/out (they were measured on another machine), then run
    scripts/bench.py once per entry of `cmds` (argument strings). Exit status 1
    if any of them failed.

    `CARGO_TARGET_DIR` is the uploaded tree's own `target/`, so the third-party
    crates compile once for the tree and every `--bench-bin` worktree (`bins`,
    [(name, sha, features)]) instead of once per worktree with its own empty
    target/ -- and every consumer that assumes cargo's default target dir keeps
    working (`bench_machine.TLX`, `tlxlib.build_tlx`, the release rlibs
    `bench_liveness.probe` links, `coverage`'s `test-release` build).

    The worktrees are built first, each copied out to BENCH_BINS/<name>/tlx
    immediately, and the uploaded revision last: its build then owns
    target/release/tlx and the newest `deps/libtlx_*.rlib`. `skip_head_build`
    (from head_binary_needed) drops that last build and removes
    target/release/tlx, so no `--bench-bin` binary is left at HEAD's path.
    `skip_remote_clippy` (from `remote_clippy_needed`) drops the instance's
    Clippy: the prelaunch one already covered this exact tree on Linux."""
    q = shlex.quote
    target = '"$CARGO_TARGET_DIR/release/tlx"'
    s = ["set -u", f". {ENV_FILE}", f"cd {home}/tlx",
         f"export TLX_CLOUD_HOST=1 CC={q(cc)} TLX_JAVA=$(command -v java) TLX_BENCH_MACHINE={q(machine)}",
         f"export CARGO_TARGET_DIR={home}/tlx/target",
         "mkdir -p bench",
         # (Retired instructions for the suite's history: best effort; a VM often has no usable counters.)
         "command -v perf >/dev/null 2>&1 || sudo -n apt-get install -y -qq linux-tools-common \"linux-tools-$(uname -r)\" >/dev/null 2>&1 || true",
         "sudo -n sysctl -qw kernel.perf_event_paranoid=-1 >/dev/null 2>&1 || true",
         "{ echo \"machine: $TLX_BENCH_MACHINE\"; lscpu; echo; free -h; echo; java -version 2>&1; rustc --version; "
         "$CC --version | head -1; } > bench/machine.txt 2>&1",
         "cat bench/machine.txt",
         "rm -f corpus/out/bench-tlc.json",
         "rc=0"]
    if skip_remote_clippy:
        s += ["echo '== cargo clippy skipped: the local prelaunch Clippy covered this tree'"]
    else:
        # Bench mode skips verify.py's build suite. Check native Linux
        # warnings here before any timed work, rather than merely claiming
        # the local cross-Clippy skip is covered by the cloud build suite.
        s += ["echo '== cargo clippy --workspace --release --all-targets'",
              "cargo clippy --workspace --release --all-targets -- -D warnings || exit 1"]
    # (The worktrees come first: each build replaces the shared target dir's
    # release/tlx, so it is copied to the path its commands name before the
    # next build; the uploaded revision is built last and owns that path.)
    for name, sha, features in bins:
        src = f"{home}/bench-src/{name}"
        feat = f" --features {q(features)}" if features else ""
        s += [f"echo {q(f'== bench binary {name}: {sha[:12]}' + (f' (features {features})' if features else ''))}",
              f"git worktree add -q -f --detach {src} {sha} || exit 1",
              f"(cd {src} && cargo build -q --release -p tlx{feat}) || exit 1",
              f"mkdir -p {BENCH_BINS}/{name} && cp {target} {BENCH_BINS}/{name}/tlx"]
    if skip_head_build:
        # (No command runs it, and a later build's binary must not be left
        # where HEAD's is expected.)
        s += [f"echo '== cargo build skipped: no --bench command runs {HEAD_BINARY}'",
              f"rm -f {HEAD_BINARY}"]
    else:
        # (A no-op for the uploaded tree -- CARGO_TARGET_DIR is its own target/
        # -- and it leaves target/release/{tlx,deps} holding this revision.)
        s += ["echo '== cargo build --release'",
              "cargo build -q --release -p tlx || exit 1"]
    for c in cmds:
        deadline = f" --deadline-at {deadline_at}" if deadline_at is not None else ""
        s += [f"echo {q('== scripts/bench.py ' + c)}", f"python3 -u scripts/bench.py {c}{deadline} || rc=1"]
    s.append("exit $rc")
    return "\n".join(s) + "\n"


def oracle_script(home, cmds):
    """Remote bash script of the oracle passes in ~/tlx (pure): run
    scripts/corpus.py once per entry of `cmds` (argument strings, e.g. "tlc
    --source external --tier medium -j 8"), all at the same time (give each
    its share of the CPUs with -j and --tlc-workers), each writing its TLC
    results to corpus/out/; output lines are prefixed with [oracle N]. Exit
    status 1 if any of them failed."""
    q = shlex.quote
    s = ["set -u", f". {ENV_FILE}", f"cd {home}/tlx", "export TLX_CLOUD_HOST=1 TLX_JAVA=$(command -v java)",
         "java -version 2>&1 | head -1",
         'run() { n=$1; shift; python3 scripts/corpus.py "$@" 2>&1 | sed -u "s/^/[oracle $n] /"; return ${PIPESTATUS[0]}; }',
         "pids=()"]
    for i, c in enumerate(cmds, 1):
        s += [f"echo {q(f'== [oracle {i}] scripts/corpus.py ' + c)}", f"run {i} {c} &", "pids+=($!)"]
    s += ["rc=0", 'for p in "${pids[@]}"; do wait "$p" || rc=1; done', "exit $rc"]
    return "\n".join(s) + "\n"


# A transient network failure (DNS, a refused connection, a timeout) must not
# discard a finished run's results or leave a billed instance behind: provider
# calls and the final result transfers retry with bounded backoff before they
# are reported (HARNESS-06, HARNESS-09). The total is capped, and a stop
# reserves time to terminate the instance before the dead-man's switch.
NETWORK_RETRY_SECS = 600        # setup/provider retry budget for one operation
RESULT_TRANSFER_RETRY_SECS = 3600  # final copies may outlast a local network outage
NETWORK_RETRY_INITIAL_SECS = 5  # first backoff
NETWORK_RETRY_CAP_SECS = 60     # backoff ceiling
TERMINATE_RESERVE_SECS = 120    # kept free before the dead-man's switch

# Types a provider SDK may raise directly, plus the text its errors carry when
# it wraps one (tccli reports "code:CliError message:Name resolution error ...").
NETWORK_ERROR_TYPES = (socket.gaierror, socket.timeout, TimeoutError, ConnectionError,
                       ConnectionResetError, ConnectionRefusedError, ConnectionAbortedError,
                       BrokenPipeError, ssl.SSLError)
NETWORK_ERROR_HINTS = ("name resolution", "name or service not known", "no such host",
                       "temporary failure in name resolution", "nodename nor servname",
                       "getaddrinfo", "gaierror", "connection refused", "connection reset",
                       "connection aborted", "failed to establish a new connection",
                       "max retries exceeded", "network is unreachable", "no route to host",
                       "connect timed out", "operation timed out", "read timed out",
                       "request timed out", "timed out", "remote end closed connection",
                       "broken pipe", "eof occurred", "connection error", "network error")


class TransientFailure(Exception):
    """An attempt that may be retried; it drives `retry_network` for a step
    whose failure is an exit status (rsync), not an exception."""


def is_network_error(exc):
    """True when `exc` looks like a transient network failure worth retrying."""
    if isinstance(exc, NETWORK_ERROR_TYPES):
        return True
    text = str(exc).lower()
    return any(hint in text for hint in NETWORK_ERROR_HINTS)


def network_deadline(dead_at, reserve=TERMINATE_RESERVE_SECS, budget=NETWORK_RETRY_SECS,
                     now=None, monotonic=None):
    """Monotonic instant past which retrying must stop: `budget` seconds from
    now, never past `dead_at - reserve`, so the instance can still be
    terminated before the dead-man's switch. The clock is looked up at call
    time, so a test can substitute it."""
    now = time.time if now is None else now
    monotonic = time.monotonic if monotonic is None else monotonic
    secs = budget
    if dead_at is not None:
        secs = min(secs, dead_at - reserve - now())
    return monotonic() + max(0.0, secs)


class RetryClock:
    """One bounded retry loop's clock and sleep, injectable from the outside.

    A loop that reads ``time.monotonic`` and calls ``time.sleep`` directly can
    only be tested by waiting for real: one harness test backed off about ten
    minutes before it was killed (2026-10-08 step-back). Every retry loop that
    waits between attempts takes one of these, built from its own injectable
    ``sleep``/``monotonic`` keyword arguments, so a test passes
    ``testkit.FakeClock`` and the loop runs to completion in microseconds while
    still recording the schedule it would have slept.
    """

    def __init__(self, monotonic=None, sleep=None):
        self._monotonic = time.monotonic if monotonic is None else monotonic
        self._sleep = time.sleep if sleep is None else sleep

    def now(self):
        return self._monotonic()

    def sleep(self, seconds):
        if seconds > 0:
            self._sleep(seconds)

    def sleep_until(self, wake, slice_secs=60.0):
        """Sleep until the `wake` instant in slices of at most `slice_secs`, so a
        long wait stays interruptible (signal handling, heartbeat output)."""
        while (left := wake - self.now()) > 0:
            self.sleep(min(slice_secs, left))


def retry_bounded(attempt, what, retry=None, tries=None, until=None, gap=0.0,
                  sleep=None, monotonic=None, clock=None, on_retry=None):
    """Call `attempt`, repeating while `retry(result)` holds, bounded by `tries`
    attempts and/or the `until` instant (a clock reading); returns the result of
    the last attempt. `attempt` returns the loop's result (the caller reads what
    it needs from it); an exception propagates to the caller. `gap` seconds are
    slept between attempts through `clock` (a :class:`RetryClock`, built from
    `sleep`/`monotonic` when not given), and `on_retry(attempt, result)` may
    report each repeat. One call at least unless `until` is already past."""
    clock = RetryClock(monotonic, sleep) if clock is None else clock
    if until is not None and clock.now() >= until:
        return None
    attempt_no = 0
    while True:
        attempt_no += 1
        result = attempt()
        if retry is None or not retry(result):
            return result
        if (tries is not None and attempt_no >= tries) or (until is not None and clock.now() >= until):
            return result
        if on_retry is not None:
            on_retry(attempt_no, result)
        clock.sleep(gap(attempt_no) if callable(gap) else gap)


def retry_network(fn, what, deadline=None, budget=None, retry=None,
                  sleep=None, monotonic=None):
    """Run a network operation with bounded exponential backoff, then raise
    InfraError: a transient failure is retried for at most `budget` seconds
    (`NETWORK_RETRY_SECS` by default) and never past `deadline`. A non-network
    failure, and an interrupt (a BaseException, e.g. `Interrupted`), propagate
    unchanged. The clock is looked up at call time, so a test can substitute it."""
    retry = is_network_error if retry is None else retry
    sleep = time.sleep if sleep is None else sleep
    monotonic = time.monotonic if monotonic is None else monotonic
    budget = NETWORK_RETRY_SECS if budget is None else budget
    start, delay, attempt = monotonic(), NETWORK_RETRY_INITIAL_SECS, 0
    until = start + budget if deadline is None else min(start + budget, deadline)
    while True:
        if monotonic() >= until:
            raise InfraError(f"{what}: retry deadline expired before attempt {attempt + 1}")
        attempt += 1
        try:
            return fn()
        except Exception as e:  # noqa: BLE001 - only transient failures are retried
            if not retry(e):
                raise
            elapsed = monotonic() - start
            left = budget - elapsed if deadline is None else min(budget - elapsed, deadline - monotonic())
            if left <= delay:
                raise InfraError(f"{what}: still failing after {attempt} attempts in {fmt_secs(elapsed)}: {e}") from e
            warning(f"{what}: transient network failure ({e}); retry {attempt} in {fmt_secs(delay)}")
            sleep(delay)
            delay = min(delay * 2, NETWORK_RETRY_CAP_SECS)


def required_rsync(m, cmd, name, deadline=None, sleep=None, monotonic=None):
    """The final, authoritative copy of a result back to this machine: retry a
    bounded, backed-off number of times within `deadline`, then raise InfraError
    (HARNESS-06), so a transfer that never completed cannot yield a success
    receipt. A periodic best-effort copy uses `copy_back(..., quiet=True)`."""
    state = []

    def attempt():
        p = m.run(cmd, check=False, capture_output=True, ssh_deadline=deadline)
        if p.returncode:
            state[:] = [p.returncode, ((p.stdout or b"") + (p.stderr or b"")).decode(errors="replace").strip()[-400:]
                        + (f"; {p.ssh_diagnosis}" if hasattr(p, "ssh_diagnosis") else "")]
            raise TransientFailure(f"rsync exit {p.returncode}")

    try:
        retry_network(attempt, name, deadline=deadline, budget=RESULT_TRANSFER_RETRY_SECS,
                      retry=lambda e: isinstance(e, TransientFailure),
                      sleep=sleep, monotonic=monotonic)
    except InfraError as e:
        raise InfraError(f"required transfer failed: {e}" + (f": {state[1]}" if len(state) > 1 and state[1] else "")) from e


def copy_back(m, cmd, name, quiet, deadline=None):
    """One result transfer: a periodic best-effort copy (`quiet`) that never
    raises, or a required receipt (`required_rsync`)."""
    if quiet:
        m.run(cmd, check=False, capture_output=True)
    else:
        required_rsync(m, cmd, name, deadline=deadline)


def fetch_oracle_results(m, local_dir, quiet=False, deadline=None):
    """The TLC result files (corpus/out/tlc*.json) of the instance and the oracle pass's output
    (`quiet`: the periodic best-effort copies; the final copy is a required receipt)."""
    os.makedirs(local_dir, exist_ok=True)
    rsync = ["rsync", "-az", "-e", m.ssh_transport()]
    copy_back(m, rsync + ["--include=" + ORACLE_FILES, "--exclude=*", m.remote("tlx/corpus/out/"), local_dir + "/"],
              "oracle result files", quiet, deadline)
    copy_back(m, rsync + [m.remote("verify.out"), os.path.join(local_dir, "oracle.out")], "oracle output", quiet, deadline)


def rust_tarball_url(toolchain, arch):
    if not re.fullmatch(r"\d+\.\d+\.\d+", toolchain):
        raise InfraError(f"--rust-from upload needs a numbered toolchain, not {toolchain!r}")
    return f"https://static.rust-lang.org/dist/rust-{toolchain}-{TRIPLES[arch]}.tar.xz"


# --- The launched machine ------------------------------------------------------

def over_ssh(cmd):
    """Whether `cmd` reaches the instance over ssh: ssh(1), rsync over ssh
    (`-e` carries the transport) or git over an ssh:// remote. Every other
    command of a run is local, and a matching word in its output means
    nothing."""
    head = os.path.basename(cmd[0]) if cmd else ""
    if head == "ssh":
        return True
    if head == "rsync":
        return "-e" in cmd
    if head == "git":
        return any(isinstance(a, str) and a.startswith("ssh://") for a in cmd)
    return False



class Machine:
    """A launched instance: identity, ssh endpoint, cost accounting."""

    def __init__(self, provider, offer, proxy=None):
        self.provider, self.offer, self.proxy = provider, offer, proxy
        self.id = None
        self.ip = None
        self.port = 22
        self.token = None
        self.t_launch = None
        self.t_end = None
        self.terminated = False
        # ssh, rsync and git over ssh only use a proxy when told to
        # (ProxyCommand): keep proxy variables away from them.
        self.env = no_proxy_env()
        # The operator-IP allowlist's recovery hook (`cloud.allowlist.SshAccess`,
        # a duck-typed `run(attempt, cmd, step=None)`), attached by cloud_verify once the
        # machine is launched; without it `run` is the plain subprocess call.
        self.access = None

    @property
    def region(self):
        return self.offer.region

    @property
    def user(self):
        return self.provider.ssh_user

    def ssh_cmd(self, *extra, port=None):
        return ["ssh", "-F", "/dev/null", "-i", KEY_FILE, "-o", "IdentitiesOnly=yes", "-o", "StrictHostKeyChecking=no",
                "-o", "UserKnownHostsFile=/dev/null", "-o", "LogLevel=ERROR", "-o", "ServerAliveInterval=15",
                "-o", "ServerAliveCountMax=8", "-o", "ConnectTimeout=10", "-p", str(port or self.port),
                *(["-o", f"ProxyCommand=nc -X connect -x {self.proxy} %h %p"] if self.proxy else []),
                *extra, f"{self.user}@{self.ip}"]

    def ssh_transport(self):
        return " ".join(shlex.quote(a) for a in self.ssh_cmd()[:-1])

    def run(self, cmd, ssh_step=None, ssh_deadline=None, **kw):
        """Run one command against the instance. Every transport of the run -
        the ssh calls, the rsync transfers, the git push - goes through here,
        so this one place can notice that a failure is the operator's egress
        address having moved out of the security group rather than a sick
        instance (cloud/allowlist.py) and repair it before the caller's retry
        budget is spent on it."""
        options = {"env": self.env, **kw}
        if self.access is None:
            return subprocess.run(cmd, **options)
        # Even a visible setup step must retain stderr for diagnosis. Previously
        # apt inherited it, raised 255, and cleanup raced a background repair.
        relay_stderr = over_ssh(cmd) and not options.get("capture_output") and "stderr" not in options
        if relay_stderr:
            options["stderr"] = subprocess.PIPE
        check = options.pop("check", False)

        def attempt(remaining):
            bounded = dict(options)
            if over_ssh(cmd):
                bounded["timeout"] = min(options.get("timeout") or remaining, remaining)
            try:
                p = subprocess.run(cmd, **bounded)
            except subprocess.TimeoutExpired as error:
                if not over_ssh(cmd):
                    raise
                stderr = error.stderr or b""
                if isinstance(stderr, bytes):
                    stderr = stderr.decode(errors="replace")
                stderr += "\nssh transport operation timed out (client deadline)"
                stdout = error.stdout
                if options.get("text"):
                    if isinstance(stdout, bytes):
                        stdout = stdout.decode(errors="replace")
                else:
                    stderr = stderr.encode()
                p = subprocess.CompletedProcess(cmd, 255, stdout, stderr)
            if relay_stderr and p.stderr:
                sys.stderr.write(p.stderr.decode(errors="replace") if isinstance(p.stderr, bytes) else p.stderr)
            return p

        p = self.access.run(attempt, cmd, step=ssh_step, deadline=ssh_deadline)
        if check:
            p.check_returncode()
        return p

    def ssh(self, script, check=True, capture=False, step=None, deadline=None):
        p = self.run(self.ssh_cmd() + [script], capture_output=capture, text=True, ssh_step=step, ssh_deadline=deadline)
        if check and p.returncode != 0:
            raise InfraError(f"remote command failed (exit {p.returncode}): {script[:200]}" + (f"\n{p.stderr}" if capture else "")
                             + (f"\n{p.ssh_diagnosis}" if hasattr(p, "ssh_diagnosis") else ""))
        return p

    def wait_ssh(self, timeout=300, *, sleep=None, monotonic=None):
        """Wait until ssh answers on one of the provider's ports; use that port.

        The clock and sleep are injectable (`RetryClock`) so a test drives the
        poll without waiting for real."""
        clock = RetryClock(monotonic, sleep)

        def probe():
            for port in self.provider.ssh_ports:
                p = self.run(self.ssh_cmd("-o", "ConnectTimeout=5", port=port) + ["echo $SSH_CLIENT"], capture_output=True, text=True)
                if p.returncode == 0:
                    self.port = port
                    log(f"ssh up on port {port}; the instance sees this machine as {p.stdout.split()[0] if p.stdout.split() else '?'}")
                    return port
            return None

        if retry_bounded(probe, "ssh", retry=lambda port: port is None, until=clock.now() + timeout,
                         gap=3, clock=clock) is None:
            raise InfraError(f"ssh did not come up (ports {', '.join(map(str, self.provider.ssh_ports))})")

    def remote(self, path):
        return f"{self.user}@{self.ip}:{path}"

    def wall(self):
        return ((self.t_end or time.time()) - self.t_launch) if self.t_launch else 0.0

    def cost(self):
        return self.wall() / 3600 * self.offer.price


def ensure_local_key():
    """Create ~/.ssh/tlx-verify if missing; True if it was created now."""
    if os.path.exists(KEY_FILE):
        return False
    os.makedirs(os.path.dirname(KEY_FILE), mode=0o700, exist_ok=True)
    subprocess.run(["ssh-keygen", "-q", "-t", "ed25519", "-N", "", "-C", "tlx-verify", "-f", KEY_FILE], check=True)
    log(f"created ssh key {KEY_FILE}")
    return True


def ipv4_create_connection(address, timeout=socket._GLOBAL_DEFAULT_TIMEOUT, source_address=None, **_):
    """`socket.create_connection` restricted to IPv4 addresses.

    The security-group rule needs this machine's IPv4 address. On a machine whose direct route
    prefers IPv6, the echo services answer with an IPv6 address and the launch stopped with
    "cannot determine this machine's public IP" (2026-10-09, n-n15).
    """
    host, port = address
    error = None
    for family, kind, proto, _name, sockaddr in socket.getaddrinfo(host, port, socket.AF_INET, socket.SOCK_STREAM):
        sock = socket.socket(family, kind, proto)
        try:
            if timeout is not socket._GLOBAL_DEFAULT_TIMEOUT:
                sock.settimeout(timeout)
            if source_address:
                sock.bind(source_address)
            sock.connect(sockaddr)
            return sock
        except OSError as e:
            error = e
            sock.close()
    raise error or OSError(f"no IPv4 address for {host}")


class _IPv4HTTPSConnection(http.client.HTTPSConnection):
    _create_connection = staticmethod(ipv4_create_connection)


class _IPv4HTTPSHandler(urllib.request.HTTPSHandler):
    def https_open(self, req):
        return self.do_open(_IPv4HTTPSConnection, req, context=self._context)


IP_ECHO_URLS = ("https://myip.ipip.net", "https://ifconfig.me/ip", "https://api.ipify.org", "https://checkip.amazonaws.com")


def direct_public_ip():
    """This machine's IPv4 address as seen without any proxy, asked over IPv4."""
    direct = urllib.request.build_opener(urllib.request.ProxyHandler({}), _IPv4HTTPSHandler())
    for url in IP_ECHO_URLS:
        try:
            with direct.open(url, timeout=request_deadline.remaining(10)) as r:
                text = r.read().decode(errors="replace")
            if m := re.search(r"\b(\d{1,3}(?:\.\d{1,3}){3})\b", text):
                return m.group(1)
        except Exception:  # noqa: BLE001 - try the next service
            pass
    raise InfraError("cannot determine this machine's public IPv4 address (" + ", ".join(IP_ECHO_URLS) + " failed)")


# --- Setup, verification, results ------------------------------------------------

def run_bg(fn, name, errors, timings):
    """Run `fn()` (returns a status line or None) in a thread; record its
    duration in `timings[name]`, append a message to `errors` when it raises."""
    def body():
        t0 = time.time()
        try:
            msg = fn()
            timings[name] = time.time() - t0
            log(f"{name} done ({fmt_secs(timings[name])}){(': ' + msg) if msg else ''}")
        except Exception as e:  # noqa: BLE001 - collected and reported by the caller
            errors.append(f"{name} failed: {e}")
    t = threading.Thread(target=body, daemon=True)
    t.start()
    return t


def checked(m, cmd, name, **kw):
    p = m.run(cmd, ssh_step=name, **{"capture_output": True, "text": True, **kw})
    if p.returncode != 0:
        raise InfraError(f"{name} (exit {p.returncode}): {(p.stdout + p.stderr)[-800:]}"
                         + (f"\n{p.ssh_diagnosis}" if hasattr(p, "ssh_diagnosis") else ""))
    return p.stdout.strip().splitlines()[-1] if p.stdout.strip() else None


def fetch_rust_tarball(toolchain, arch):
    """The local path of the standalone Rust tarball (downloaded once into ~/.cache/tlx-cloud)."""
    url = rust_tarball_url(toolchain, arch)
    path = os.path.join(os.path.expanduser("~/.cache/tlx-cloud"), os.path.basename(url))
    if not os.path.exists(path):
        os.makedirs(os.path.dirname(path), exist_ok=True)
        log(f"downloading {url}")
        t0 = time.time()
        with urllib.request.urlopen(url, timeout=60) as r, open(path + ".part", "wb") as f:
            while chunk := r.read(1 << 20):
                f.write(chunk)
        os.rename(path + ".part", path)
        log(f"downloaded {os.path.getsize(path) >> 20} MB ({fmt_secs(time.time() - t0)})")
    return path


def vendor_crates(sha):
    """A local `cargo vendor` directory for the Cargo.lock of `sha` (cached by its hash)."""
    import hashlib, tempfile
    lock = subprocess.run(["git", "show", f"{sha}:Cargo.lock"], cwd=ROOT, check=True, capture_output=True).stdout
    out = os.path.join(ROOT, "target", "cloud-cache", "vendor-" + hashlib.sha256(lock).hexdigest()[:16])
    if os.path.isdir(out):
        return out
    with tempfile.TemporaryDirectory() as tmp:
        archive = subprocess.run(["git", "archive", sha], cwd=ROOT, check=True, capture_output=True).stdout
        subprocess.run(["tar", "x", "-C", tmp], input=archive, check=True)
        subprocess.run(["cargo", "vendor", "--locked", "-q", out + ".part"], cwd=tmp, check=True, stdout=subprocess.DEVNULL)
    os.rename(out + ".part", out)
    return out


def harness_files(root=ROOT):
    """Every harness module (scripts/**/*.py) of this tree, relative to `root`, sorted.

    Relative paths preserve the package layout across the upload (HARNESS-13):
    a nested scripts/<package>/mod.py lands at tlx/scripts/<package>/mod.py.
    A flat scripts/*.py glob (and a flat rsync) would drop it once modules move
    into packages."""
    d = os.path.join(root, "scripts")
    files = []
    for base, dirs, names in os.walk(d):
        dirs[:] = [name for name in dirs if name != "__pycache__"]
        files += [os.path.relpath(os.path.join(base, name), root)
                  for name in names if name.endswith(".py")]
    return sorted(files)


def setup_remote(m, sha, toolchain, arch, rust_from, crates_from, timings, bench_refs=None, extra_refs=None, oracle=False,
                 tlc=False):
    """Install packages and Rust, upload the revision, third_party and corpus/out.
    With `bench_refs` ({name: sha}, possibly empty; None: not a bench run)
    also Java and the TLC jars, those revisions (as refs/bench/<name>), and
    this tree's scripts/bench.py and scripts/tlc.py. `extra_refs` ({name:
    sha}): more revisions to push (as refs/extra/<name>, e.g. for --then).
    With `oracle` also Java and the TLC jars, and this tree's
    scripts/corpus.py and scripts/tlc.py (for --oracle). With `tlc` (a
    verify.py pass runs TLC: the fuzz suites) also Java and the TLC jars."""
    bench = bench_refs is not None
    java = bench or oracle or tlc
    errors = []
    home = m.provider.home
    jobs = []
    rsync = ["rsync", "-az", "-e", m.ssh_transport()]
    # Rust only needs curl/tar (both in the images): it runs while the package manager installs the rest.
    if rust_from == "upload":
        def rust():
            tarball = fetch_rust_tarball(toolchain, arch)
            t0 = time.time()
            checked(m, ["rsync", "-a", "--partial", "-e", m.ssh_transport(), tarball, m.remote("")], "toolchain upload")
            timings["toolchain upload"] = time.time() - t0
            return checked(m, m.ssh_cmd() + [rust_script("upload", toolchain, arch, tarball)], "rust install")
    else:
        def rust():
            return checked(m, m.ssh_cmd() + [rust_script(rust_from, toolchain, arch)], "rustup")
    jobs.append(run_bg(rust, f"rust ({rust_from})", errors, timings))
    if crates_from == "vendor":
        def crates():
            d = vendor_crates(sha)
            return checked(m, rsync + ["--delete", d + "/", m.remote("vendor/")], "vendor upload")
        jobs.append(run_bg(crates, "crates (vendor)", errors, timings))
    config = cargo_config(crates_from, f"{home}/vendor")
    t0 = time.time()
    m.ssh(m.provider.packages_script() + (m.provider.java_script() if java else "") +
          "git init -q ~/tlx\ngit -C ~/tlx config receive.denyCurrentBranch ignore\n"
          "mkdir -p ~/tlx/third_party ~/tlx/corpus/out ~/.cargo\n" +
          (f"cat > ~/.cargo/config.toml <<'EOF'\n{config}EOF\n" if config else ""), step="install packages and initialize checkout")
    timings["packages"] = time.time() - t0
    log(f"packages installed ({fmt_secs(timings['packages'])})")
    tp = os.path.realpath(os.path.join(ROOT, "third_party"))
    out = os.path.realpath(os.path.join(ROOT, "corpus", "out"))
    jobs += [
        run_bg(lambda: checked(m, rsync + (BENCH_THIRD_PARTY_FILTER if java else THIRD_PARTY_FILTER)
                               + [tp + "/", m.remote("tlx/third_party/")], "rsync"),
               "third_party upload", errors, timings),
        run_bg(lambda: checked(m, rsync + [out + "/", m.remote("tlx/corpus/out/")], "rsync"), "corpus/out upload", errors, timings),
    ]
    t0 = time.time()
    refspecs = ([f"{sha}:refs/heads/verify"] + [f"{s}:refs/bench/{n}" for n, s in (bench_refs or {}).items()]
                + [f"{s}:refs/extra/{n}" for n, s in (extra_refs or {}).items()])
    p = m.run(["git", "push", "-q", f"ssh://{m.user}@{m.ip}{home}/tlx", *refspecs],
              cwd=ROOT, env=dict(m.env, GIT_SSH_COMMAND=m.ssh_transport()), capture_output=True, text=True)
    if p.returncode != 0:
        errors.append(f"git push failed: {p.stderr[-800:]}"
                      + (f"\n{p.ssh_diagnosis}" if hasattr(p, "ssh_diagnosis") else ""))
    else:
        m.ssh(f"git -C ~/tlx checkout -q --detach {sha}")
        timings["git push"] = time.time() - t0
        log(f"git push done ({fmt_secs(timings['git push'])})")
    # The whole harness (scripts/**/*.py) of this tree, as when verifying an older revision
    # locally: a partial overlay mixed bench.py of this tree with an older bench_profile.py
    # and crashed a measurement run (2026-10-07). The checked engine stays the revision's.
    # -R keeps the source-relative layout, so nested packages land at tlx/scripts/<package>/
    # instead of being flattened into tlx/scripts/ (HARNESS-13).
    checked(m, ["rsync", "-aR", "-e", m.ssh_transport(), *harness_files(), m.remote("tlx/")],
            "harness upload", cwd=ROOT)
    for t in jobs:
        t.join()
    if errors:
        raise InfraError("setup failed:\n" + "\n".join(errors))
    if bench or oracle:
        # third_party/ is uploaded from the shared store of the main checkout (its
        # realpath), so a cfg this branch changed would not reach the instance: apply
        # the checked-out revision's corpus/external/ overlays over it, as a fetch
        # would (2026-10-09: a kraft oracle lane ran the pre-fix cfg of its model).
        t0 = time.time()
        p = m.ssh("cd ~/tlx && python3 scripts/fetch-external.py --overlay-only", capture=True, step="external overlays")
        timings["external overlays"] = time.time() - t0
        for line in (p.stdout or "").splitlines():
            if line.strip():
                log(f"  | {line.strip()}")


# A remote job ends this long before the dead-man's switch shuts the
# instance down, so that its results can still be copied back.
FETCH_MARGIN_SECS = 300

# The exit status of a remote job stopped at its deadline (timeout(1)).
DEADLINE_RC = 124


def remote_deadline(m, now):
    """Seconds the next remote job of `m` may run (None: no limit known):
    until FETCH_MARGIN_SECS before the dead-man's switch (`m.dead_at`).
    Zero or less means no time is left: the caller must not start a job that
    could not copy its results back before the switch. (On 2026-10-07 a
    benchmark ran into the shutdown and every result on the instance was
    lost: bench mode copied them only at the end. A 60 s floor below the
    margin started exactly such a doomed job.)"""
    dead_at = getattr(m, "dead_at", None)
    if dead_at is None:
        return None
    return int(dead_at - FETCH_MARGIN_SECS - now)


def deadline_cmd(args, secs):
    """`args` run under timeout(1) for `secs` seconds (TERM, then KILL 30 s
    later); unchanged without a deadline."""
    return args if secs is None else ["timeout", "--signal=TERM", "--kill-after=30", f"{secs}s", *args]


def remote_start_script(cmd, token, deadline_at=None):
    """A replayable detached start, identified once per pass.

    The remote lock covers the job, and the ready marker is permanent for this
    token. An SSH failure after dispatch can replay this exact start without
    running a second benchmark or removing the first job's result files.
    Python's flock is available on all supported Linux images.
    """
    marker = f"verify-start-{token}.ready"
    program = f"""import fcntl, pathlib, subprocess, time
home = pathlib.Path.home()
with (home / 'verify.lock').open('w') as lock:
    fcntl.flock(lock, fcntl.LOCK_EX)
    ready = home / {marker!r}
    if ready.exists():
        raise SystemExit(0)
    (home / 'verify.rc').unlink(missing_ok=True)
    with (home / 'verify.out').open('w') as out:
        ready.touch()
        command = ['sh', '-c', {('. ' + ENV_FILE + '; ' + cmd)!r}]
        deadline_at = {deadline_at!r}
        remaining = None if deadline_at is None else int(deadline_at - time.time())
        if remaining is not None and remaining <= 0:
            code = {DEADLINE_RC}
        else:
            if remaining is not None:
                command = ['timeout', '--signal=TERM', '--kill-after=30', str(remaining) + 's'] + command
            code = subprocess.call(command, cwd=home / 'tlx', stdout=out, stderr=out)
    (home / 'verify.rc').write_text(str(code))
"""
    launcher = "python3 -c " + shlex.quote(program)
    return ("export TLX_CLOUD_HOST=1 PYTHONUNBUFFERED=1; J=$(command -v java) && export TLX_JAVA=$J; "
            f"if [ ! -e ~/{marker} ]; then (nohup sh -c {shlex.quote(launcher)} > ~/verify-start-{token}.log 2>&1 < /dev/null &); fi; "
            f"n=0; while [ ! -e ~/{marker} ] && [ $n -lt 500 ]; do sleep 0.1; n=$((n+1)); done; "
            f"test -e ~/{marker} || {{ cat ~/verify-start-{token}.log >&2; exit 1; }}")


@contextlib.contextmanager
def remote_output_stream(m, lines, remaining):
    """Bound the local SSH stream too, even if no output or EOF arrives."""
    child = subprocess.Popen(m.ssh_cmd() + [
        f"while [ ! -e ~/verify.out ]; do sleep 1; done; tail -n +{lines + 1} -f ~/verify.out & T=$!; "
        "while [ ! -e ~/verify.rc ]; do sleep 2; done; sleep 2; kill $T"],
        stdout=subprocess.PIPE, text=True, env=m.env)
    timer = threading.Timer(max(0, remaining), child.terminate)
    timer.daemon = True
    timer.start()
    try:
        yield child.stdout
    finally:
        timer.cancel()
        if child.poll() is None:
            child.terminate()
        try:
            child.wait(timeout=5)
        except subprocess.TimeoutExpired:
            child.kill()
            child.wait()
        close = getattr(child.stdout, "close", None)
        if close is not None:
            close()


def run_remote_verify(m, args, on_logdir=None, *, now=None, sleep=None):
    """Start verify.py detached on the instance, stream its output; returns (exit code, remote log dir).
    The job is stopped at `remote_deadline` (exit DEADLINE_RC), before the dead-man's switch;
    an already expired deadline (InfraError) starts nothing, so the instance is still released
    with the time left to fetch what earlier passes produced. `on_logdir` (a callback) is
    told the remote log directory as soon as the stream announces it, so a periodic copy can
    follow a still-running pass."""
    # `m.dead_at` is a wall-clock instant (t_launch + max_minutes), so the
    # default clock is time.time; `now`/`sleep` are injectable for tests (a
    # retry loop that reads time.time directly can only be tested with real
    # time). RetryClock carries both through one object.
    clock = RetryClock(time.time if now is None else now, sleep)
    secs = remote_deadline(m, clock.now())
    if secs is not None and secs <= 0:
        raise InfraError("no time left to start a remote job: the dead-man's switch is closer than the "
                         f"{fmt_secs(FETCH_MARGIN_SECS)} reserved for fetching its results back")
    if secs is not None:
        log(f"remote job deadline: {fmt_secs(secs)} (the dead-man's switch is {fmt_secs(m.dead_at - clock.now())} away)")
    cmd = " ".join(shlex.quote(a) for a in args)
    # (TLX_JAVA: the installed java, for the passes that run TLC; verify.py keeps it.)
    start = remote_start_script(cmd, uuid.uuid4().hex,
                                deadline_at=m.dead_at - FETCH_MARGIN_SECS if secs is not None else None)
    m.ssh(start, step="start detached verification pass",
          deadline=time.monotonic() + (secs if secs is not None else RESULT_TRANSFER_RETRY_SECS))
    lines = 0
    logdir = None
    # The remote job owns its exit code. A transport event cannot prove job
    # failure, even when streams repeatedly close immediately or SSH stays down
    # for hours. Reserve the final fetch before the instance's dead-man switch.
    dead_at = getattr(m, "dead_at", None)
    reconnect_until = (dead_at - FETCH_MARGIN_SECS if dead_at is not None
                       else clock.now() + RESULT_TRANSFER_RETRY_SECS)
    reconnects = 0
    while True:
        stream_start = clock.now()
        with remote_output_stream(m, lines, reconnect_until - clock.now()) as output:
            for line in output:
                lines += 1
                sys.stdout.write("  | " + line)
                sys.stdout.flush()
                if mm := re.match(r"logs: (\S+)", line):
                    logdir = mm.group(1)
                    if on_logdir is not None:
                        on_logdir(logdir)
        stream_secs = clock.now() - stream_start
        rc = m.ssh("cat ~/verify.rc 2>/dev/null || true", check=False, capture=True,
                   deadline=time.monotonic() + max(0, reconnect_until - clock.now()))
        if rc.returncode == 0 and rc.stdout.strip():
            code = int(rc.stdout.strip())
            if code == DEADLINE_RC and secs is not None:
                warning(f"the remote job was stopped at its deadline ({fmt_secs(secs)}), before the dead-man's switch")
            return code, logdir
        reconnects += 1
        if clock.now() >= reconnect_until:
            raise InfraError(f"ssh reconnect stopped for final result fetch before the dead-man's switch; "
                             f"instance {m.id}; reconnects: {reconnects}; "
                             f"{getattr(rc, 'ssh_diagnosis', 'provider state: not queried')}")
        access = getattr(m, "access", None)
        if access is not None and access.last_state in ("gone", "stopped"):
            raise InfraError(f"ssh reconnect stopped: provider state: {access.last_state}; reconnects: {reconnects}")
        warning(f"output stream ended early after {stream_secs:.0f}s, reconnecting "
                f"(attempt {reconnects}; ssh exit {rc.returncode})")
        clock.sleep(min(5, max(0, reconnect_until - clock.now())))


def fetch_bench_results(m, local_dir, quiet=False, deadline=None):
    """bench/ of the remote checkout (history/, ab results,
    machine.txt), the TLC -workers N cache and the run's output (`quiet`: the
    periodic best-effort copies; the final copies are required receipts, except
    the optional TLC cache, which may be absent)."""
    os.makedirs(local_dir, exist_ok=True)
    rsync = ["rsync", "-az", "-e", m.ssh_transport()]
    copy_back(m, rsync + [m.remote("tlx/bench/"), os.path.join(local_dir, "bench") + "/"], "bench results", quiet, deadline)
    # (Absent when no TLC -workers N ran: optional, so it never fails a run.)
    m.run(rsync + [m.remote("tlx/corpus/out/bench-tlc.json"), local_dir + "/"], check=False, capture_output=True)
    copy_back(m, rsync + [m.remote("verify.out"), os.path.join(local_dir, "bench.out")], "bench output", quiet, deadline)


def fetch_results(m, logdir, local_dir, quiet=False, deadline=None):
    """A pass's log directory and output back on this machine: the final copy
    is a required receipt, a periodic copy (`quiet`) keeps only what already
    arrived (`logdir` is None before the pass has announced one)."""
    os.makedirs(local_dir, exist_ok=True)
    rsync = ["rsync", "-az", "-e", m.ssh_transport()]
    if logdir:
        copy_back(m, rsync + [m.remote(f"{logdir}/"), local_dir + "/"], "log directory", quiet, deadline)
    copy_back(m, rsync + [m.remote("verify.out"), os.path.join(local_dir, "verify.out")], "run output", quiet, deadline)


# ------------------------------------------------------- bench result receipts
# HARNESS-06 and HARNESS-12: `scripts/bench.py track` decides what to record
# after a cloud bench launch from the invocation's own receipt
# (`target/bench/<run>/cloud.json`), never from the newest directory's mtime.
# The receipt binds the revision, the external binaries the launch built and the
# exit status of the run; one validator checks every binding field, so no reader
# can adopt a run through the single field it happens to like.
#
# A completed suite ends in one of `bench_suite`'s statuses (PASS, REGRESSION,
# INCONCLUSIVE); any other exit of `cloud_verify.py` is an infrastructure
# refusal, failure or the deadline's, and the receipt next to it is failure
# evidence, never a result to record.
VERDICT_EXITS = (0, 1, 2)


def is_verdict_exit(code):
    """True when `code` is a status a completed benchmark suite produces: the
    infrastructure codes (INFRA_FAIL, a stop code, DEADLINE_RC) are not."""
    return code in VERDICT_EXITS


def same_rev(a, b):
    """Two spellings of one revision: a short hash and its full hash match, and
    a `-dirty` suffix and the revision it names match."""
    a, b = str(a or "").split("-dirty")[0], str(b or "").split("-dirty")[0]
    return bool(a) and bool(b) and (a.startswith(b) or b.startswith(a))


def read_receipt(directory):
    """The cloud receipt of one result directory, or None: `cloud.json`, the
    file a launch writes to bind its results to what it actually ran."""
    try:
        with open(os.path.join(directory, "cloud.json"), encoding="utf-8") as source:
            receipt = json.load(source)
    except (OSError, ValueError):
        return None
    return receipt if isinstance(receipt, dict) else None


def write_receipt(directory, receipt):
    """Write `receipt` as the directory's `cloud.json` and return its path."""
    path = os.path.join(directory, "cloud.json")
    with open(path, "w", encoding="utf-8") as handle:
        json.dump(receipt, handle, indent=1)
    return path


def cloud_receipt(a, sha, rc, *, phases, rust, crates, machine, bins, then_results, fetched_at, currency):
    """The receipt of one launch (its result directory's `cloud.json`): what ran
    and how it ended. It is written for every invocation that produced a result
    directory - a machine that never came up, a refused launch that still
    fetched partial results and a failed run included - so a later reader binds
    the results to this invocation instead of guessing by mtime (HARNESS-06).
    Only the fields a launched `machine` can state are added when one exists."""
    receipt = {"provider": a.provider, "arch": a.arch, "rev": sha, "verify_exit": rc, "verify_env": a.env,
               "rust_from": rust, "crates_from": crates, "fetched_at": fetch_stamp(fetched_at),
               "phases_s": {k: (round(v) if isinstance(v, float) else v) for k, v in phases.items()}}
    if machine is not None:
        o = machine.offer
        receipt.update({"instance": machine.id, "instance_type": o.itype, "vcpus": o.vcpus, "region": o.region,
                        "zone": o.zone, "market": o.market, "spot_price_per_hour": o.price, "currency": currency,
                        "wall_s": round(machine.wall()), "estimated_cost": round(machine.cost(), 4)})
    if a.then:
        receipt["then"] = then_results
    if a.oracle:
        receipt["oracle"] = a.oracle
    if a.bench:
        receipt["bench"] = a.bench
        receipt["bench_bins"] = [{"name": n, "rev": s, "features": f} for n, s, f in bins]
    return receipt


def fetch_stamp(when):
    """The receipt's fetch cutoff: the wall-clock time of the last successful
    result transfer, so a partial local copy says up to when it is complete."""
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(when)) if when else None


def receipt_problem(receipt, rev, bench_bins=(), exit_code=0):
    """Why `receipt` does not authorize the benchmark run of `rev` with
    `bench_bins` that exited `exit_code`, or None when it does. Every identity
    and scope field is validated here (HARNESS-12):
      rev         the receipt's revision is this run's revision;
      verify_exit the receipt states this run's exit status, so a stale PASS
                  left next to a failed run cannot authorize anything;
      bench       the receipt is of a benchmark launch;
      bench_bins  the same external binaries (name and revision) were built.
    `bench_bins` are the requested `(name, rev, features)` triples; a binary the
    receipt does not pin is a mismatch, not a wildcard (HARNESS-19)."""
    if not same_rev(receipt.get("rev"), rev):
        return f"receipt revision {receipt.get('rev') or '?'} is not {rev}"
    if receipt.get("verify_exit") != exit_code:
        return f"receipt exit {receipt.get('verify_exit')!r} is not {exit_code}"
    if not receipt.get("bench"):
        return "receipt is not of a benchmark launch"
    want = {name: bref for name, bref, _ in bench_bins}
    got = {b.get("name"): b.get("rev") for b in receipt.get("bench_bins") or [] if isinstance(b, dict)}
    if set(want) != set(got):
        return f"receipt built {sorted(map(str, got))}, not {sorted(want)}"
    for name, wanted in want.items():
        if not same_rev(got.get(name), wanted):
            return f"receipt binary {name}@{got.get(name) or '?'} is not {name}@{wanted}"
    return None


def select_bench_receipt(directory, rev, bench_bins=(), exit_code=0):
    """The one result directory under `directory` whose receipt authorizes the
    benchmark run of `rev` with `bench_bins` that exited `exit_code`, as
    `(path, receipt, problem)`. No match (the launch wrote no receipt, or its
    results did not come back) and more than one match (two concurrent runs of
    the same revision) both authorize nothing: the caller must refuse instead
    of guessing by mtime (HARNESS-06). `problem` is None exactly when a unique
    directory was found."""
    matches = []
    for name in sorted(os.listdir(directory)) if os.path.isdir(directory) else []:
        path = os.path.join(directory, name)
        if not os.path.isdir(path):
            continue
        receipt = read_receipt(path)
        if receipt is not None and receipt_problem(receipt, rev, bench_bins, exit_code) is None:
            matches.append((path, receipt))
    if not matches:
        return None, None, f"no receipt under {directory} authorizes rev {rev} (exit {exit_code})"
    if len(matches) > 1:
        return None, None, "more than one receipt matches: " + ", ".join(sorted(os.path.basename(d) for d, _ in matches))
    return matches[0][0], matches[0][1], None


TERMINAL_STATES = {"terminated", "terminating", "shutdown", "deleted"}


def active_launch_leftovers(instances, launched_ids):
    """Leaks from this invocation; another concurrent owned launch is valid."""
    return [row for row in instances if row[1] in launched_ids and row[2].lower() not in TERMINAL_STATES]


def terminate_until_gone(provider, m, deadline=None, sleep=None, monotonic=None):
    """Terminate instance `m`, retrying terminate until the provider no longer
    reports it, or `deadline` (monotonic) passes; a network failure is retried
    instead of raised. On timeout an explicit LEFTOVER line with the manual
    command is printed (HARNESS-09), so a local outage cannot silently leave a
    billed instance. Returns True when the instance is gone."""
    sleep = time.sleep if sleep is None else sleep
    monotonic = time.monotonic if monotonic is None else monotonic
    hint = provider.terminate_hint(m)
    if deadline is None:
        deadline = monotonic() + NETWORK_RETRY_SECS
    while True:
        try:
            if provider.terminate(m):
                return True
        except Exception as e:  # noqa: BLE001 - a transient failure is retried below
            if not is_network_error(e):
                raise
            warning(f"terminate {m.id}: {e}")
        if monotonic() >= deadline:
            print(f"LEFTOVER INSTANCE {m.id} {m.region}: terminate with\n    {hint}\n", flush=True)
            return False
        sleep(5)
