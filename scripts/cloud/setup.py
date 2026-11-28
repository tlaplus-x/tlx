"""The plan of one cloud run and the argv of the passes it will run.

`cloud_verify.py` resolves the environment -- owner, ledger, provider, the local
preflights, the revisions -- because that is where the launch policy lives;
this module turns the resolved offer and revisions into the plan a session
executes, and is the only place the plan's wording exists: the offer table, the
`plan:` line and the dry-run block. Rendering sits apart from policy and
execution so a change to what runs does not have to touch what it says
(HARNESS-03).

`verify_args`, `then_args` and `verify_runs_tlc` translate this invocation's
options into the argv of the remote passes. A raw `--bench`/`--then` string is
split here once, so the shell semantics of those strings -- an optional leading
REV, then the options -- are decided in one place instead of at each pass
(HARNESS-02).
"""
import dataclasses
import os
import re
import shlex
import time
from typing import Any, Callable

from cloud.cloud_common import ROOT, log, warning


def env_proxy():
    """host:port of the environment's HTTP proxy (https_proxy etc.), or None."""
    for k in ("https_proxy", "HTTPS_PROXY", "http_proxy", "HTTP_PROXY"):
        if m := re.fullmatch(r"http://([^/@]+:\d+)/?", os.environ.get(k, "")):
            return m.group(1)
    return None


def sources(provider, region, rust_from, crates_from):
    """The effective (rust, crates) sources for `region` (resolving 'auto')."""
    mirror = provider.mainland(region)
    return (rust_from if rust_from != "auto" else ("mirror" if mirror else "upstream"),
            crates_from if crates_from != "auto" else ("mirror" if mirror else "upstream"))


def verify_runs_tlc(a):
    """Whether a verify.py pass runs TLC (the fuzz suites, which are in the
    full tier): then Java and the TLC jars are installed."""

    def runs(suites, tier):
        names = [s for s in suites.split(",") if s]
        return any(n.startswith("fuzz") for n in names) if names else tier == "full"
    if not a.bench and (not a.oracle or a.suites) and runs(a.suites, a.tier):
        return True
    for spec in a.then:
        words = shlex.split(spec)
        suites = next((w.split("=", 1)[1] for w in words if w.startswith("--suites=")), "")
        if "--suites" in words[:-1]:
            suites = words[words.index("--suites") + 1]
        tier = "full" if "--full" in words else "quick" if "--quick" in words else a.tier
        if runs(suites, tier):
            return True
    return False


def verify_args(a, sha, jobs):
    """The argv of the main verify.py pass."""
    args = ["python3", "scripts/verify.py", sha, f"--{a.tier}", "-j", str(jobs)]
    if a.suites:
        args += ["--suites", a.suites]
    if a.filter:
        args += ["--filter", a.filter]
    for pair in a.env:
        args += ["--env", pair]
    if a.strict:
        args.append("--strict")
    if a.fuzz_minutes is not None:
        args += ["--fuzz-minutes", str(a.fuzz_minutes)]
    if a.verbose:
        args.append("-v")
    return args


def then_args(a, spec, default_sha, resolve, jobs):
    """(sha, verify.py argv) of one --then pass: an optional leading REV, then verify.py options."""
    words = shlex.split(spec)
    sha = default_sha
    if words and not words[0].startswith("-"):
        sha = resolve(words.pop(0))
    args = ["python3", "scripts/verify.py", sha]
    if not any(w in ("--quick", "--full") for w in words):
        args.append(f"--{a.tier}")
    if not any(w in ("-j", "--jobs") or w.startswith("--jobs=") for w in words):
        args += ["-j", str(jobs)]
    return sha, args + words


def offer_lines(offers, currency):
    """One line per ranked offer, cheapest first: the price the plan is about to
    commit to, listed before the budget decision that may refuse it."""
    return [f"  {o.market} {o.itype} ({o.vcpus} vCPUs) {o.zone}: {o.price:.4f} {currency}/h"
            + (" (tried last)" if o.deprioritized else "")
            for o in offers]


def local_dir(a, provider, label):
    """Where this run's results are copied back: one directory per provider,
    revision and architecture, time-stamped so two concurrent runs of the same
    revision never write into each other's."""
    return os.path.join(ROOT, "target", "bench" if a.bench else "verify",
                        time.strftime("%Y%m%d-%H%M%S") + f"-{label}-{provider.label_suffix}"
                        + ("" if a.arch == "arm64" else f"-{a.arch}"))


@dataclasses.dataclass
class Plan:
    """One launch, fully resolved before anything is provisioned.

    `offers` is every ranked offer in the order the boot tries them (cheapest
    first); `sha`, `bins` and `then_shas` are the revisions the instance is set
    up with, so the plan is what the receipt later states the run bound.
    """
    a: Any
    provider: Any
    owner: str | None
    ledger: Any
    admitter: Any
    offers: list
    jobs: int
    sha: str
    label: str
    bins: list
    then_shas: list
    resolve: Callable
    vargs: list
    rust: str
    crates: str
    toolchain: str
    proxy: str | None
    local_dir: str
    types: list              # the instance types that were offered, for a launch that fails on every one
    tlc: bool                # a pass runs TLC (fuzz suites): Java and the TLC jars are installed
    # A --bench run builds the uploaded revision's binary only when a command
    # runs it, and runs Clippy on the instance only when the local preflight
    # did not already cover this tree (see head_binary_needed and
    # remote_clippy_needed). Both default to the pre-optimization behavior.
    skip_head_build: bool = False
    skip_remote_clippy: bool = False

    @property
    def offer(self):
        """The offer the launch tries first (the cheapest one)."""
        return self.offers[0]

    @property
    def currency(self):
        return self.provider.currency

    def work(self):
        """What the instance will run, for the plan line."""
        a = self.a
        if a.bench:
            return " ".join(f"[bench.py {c}]" for c in a.bench) + "".join(
                f" [build {n}={s[:9]}{':' + f if f else ''}]" for n, s, f in self.bins) + "".join(
                f"; then [{' '.join(then_args(a, t, self.sha, self.resolve, self.jobs)[1][1:])}]" for t in a.then)
        oracle = " ".join(f"[corpus.py {c}]" for c in a.oracle)
        if a.oracle and not a.suites:
            return oracle
        return (oracle + "; " if oracle else "") + " ".join(self.vargs[1:]) + "".join(
            f"; then [{' '.join(then_args(a, t, self.sha, self.resolve, self.jobs)[1][1:])}]" for t in a.then)

    def description(self):
        """The `plan:` line: what will be launched, at what price and with what
        work, so the cost and the dead-man's switch are stated before the call."""
        a, o = self.a, self.offer
        return (f"plan: {o.itype} ({a.arch}, {o.vcpus} vCPUs) {o.market} in {o.zone} at {o.price:.4f} {self.currency}/h; "
                f"rev {self.label}; remote: Rust {self.toolchain} ({self.rust}), crates ({self.crates}), CC={a.cc} {self.work()}; "
                f"dead-man's switch {a.max_minutes} min (at most "
                f"{o.price * max(a.max_minutes, self.provider.min_lifetime_minutes) / 60:.2f} {self.currency}); ssh "
                + (f"through proxy {self.proxy}" if self.proxy else "direct"))


def dry_run(a, offer, provider, admitter, ledger):
    """Print what a launch would do, creating nothing.

    The provider's own dry run (tencent), the account's slot view and the
    admission decision are all reported, so a refused launch can be diagnosed
    without spending one (HARNESS-08).
    """
    for line in provider.describe_plan(offer, a.arch):
        log(line if line.startswith("WARNING (not a stop condition):") else f"dry run: {line}")
    try:
        view = admitter.view_fn()
        with ledger.locked() as rows:
            decision = admitter.decide(view, rows)
        log(f"dry run: slots by owner: {decision.by_owner()}")
        log("dry run: a launch now would be admitted" if decision.ok
            else f"dry run: a launch now would wait or stop: {decision.reason}")
    except Exception as e:  # noqa: BLE001 - information only in a dry run
        warning(f"dry run: cannot count the account's slots: {type(e).__name__}: {e}")
    log("dry run: nothing launched")
