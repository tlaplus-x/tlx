#!/usr/bin/env python3
"""Run scripts/verify.py on a cloud spot machine (Linux; arm64 or x86_64).

usage:
  scripts/cloud_verify.py [REV] [--quick | --full] [--suites NAME,...] [--filter SUBSTR]
                          [--env K=V]... [--then "[REV] VERIFY.PY ARGS"]... [--fuzz-minutes M]
                          [--bench "BENCH.PY ARGS"]... [--bench-bin NAME=REV[:FEATURES]]...
                          [--oracle "CORPUS.PY ARGS"]...
                          [--provider aliyun|tencent|aws] [--arch arm64|x86_64] [--instance-type T]
                          [--region R] [--on-demand] [-j N] [--cc CC] [--rust-from auto|mirror|upload|upstream]
                          [--crates-from auto|mirror|vendor|upstream] [--ssh-proxy auto|none|HOST:PORT]
                          [--keep-instance] [--dry-run] [--list] [--cleanup] [--max-minutes N] [-v]
                          [--wait-quota MINUTES|auto] [--slots N] [--max-account-slots N] [--cancel]
                          [--coordinator-hub] [--grant OWNER --minutes M [--slots N] [--budget-cny X] [--reason TEXT]]

Launches one spot instance with the provider (default aliyun: Alibaba Cloud
ECS, see scripts/cloud/cloud_aliyun.py; tencent: Tencent Cloud CVM, see
scripts/cloud/cloud_tencent.py; aws: EC2, paused, see scripts/cloud/cloud_aws.py) at the
cheapest offer for the instance type(s) (--instance-type, or the provider's
defaults for --arch and the tier), installs packages and the Rust toolchain
pinned in rust-toolchain.toml, pushes commit REV (default HEAD) to a git
repository on the instance, copies the parts of third_party/ the tests read
(Examples without .git, community/*.tla, apalache, tlapm/library, external) and
corpus/out/ (the cached TLC oracle; no Java or TLC runs remotely, except for
the fuzz suites, see below), and runs
this tree's scripts/verify.py there with -j <vCPUs-1> (or -j N), streaming
its output. The results (summary.json and the per-suite logs) are copied to
target/verify/<time>-<rev>-<provider>[-x86_64]/, together with cloud.json
(instance, region, price, phase times, cost). What a still-running pass has
produced is copied back every 5 minutes (a reclaimed spot instance or the
dead-man's switch keeps the rest), and the final copy of a pass is a required
receipt: a transfer that cannot finish is retried with bounded backoff within
the time left and the run ends as an infrastructure failure (3) rather than
reporting success over a local copy that is known to be incomplete; summary.json
records the cutoff of the last successful copy as `fetched_at`.

More passes on the same instance (--then, repeatable): after the main run,
run verify.py again with each --then argument string in turn (shell words:
an optional REV first, default the main REV, then verify.py options such as
--suites, --env K=V, --cold-cache; the tier and -j are the main run's unless
the string names --quick/--full or -j). Each REV is pushed too. Results go
to then-<N>/ under the main result directory; the exit status is the worst
of all passes. One launch then covers several environment variants (e.g.
--then "--suites build,corpus-compile --env TLX_JIT=0") or an older
revision for a same-machine timing baseline. Pass a --max-minutes that
covers every pass.

Fuzz campaigns: the verify.py suites fuzz (in the full tier) and
fuzz-campaign compare tlx with TLC on generated specs, so when a pass selects
them Java 21 and the TLC jars are installed as in bench mode (and TLX_JAVA
is set). --fuzz-minutes M sets the campaign's duration (forwarded to the
main verify.py), e.g. --suites build,fuzz-campaign --fuzz-minutes 40
--max-minutes 60; its report, the failing specs and the minimized findings
come back with the logs (fuzz-campaign/ in the result directory).

Rust and crates in China mainland regions (crates.io and static.rust-lang.org
are slow or flaky from there): --rust-from mirror (rustup through rsproxy.cn)
or upload (the standalone tarball, downloaded here once into
~/.cache/tlx-cloud and copied up), --crates-from mirror (rsproxy.cn sparse
index) or vendor (`cargo vendor` here, copied up). `auto` is mirror in the
mainland and upstream elsewhere.

Safety rules (the account pays per second): each provider checks the
identity of its fixed profile (`tlx`) before anything else; every resource
is tagged Project=tlx (tlx-project=tlx on tencent, which reserves the key
Project); the instance is released in a `finally` (exceptions, Ctrl-C,
SIGTERM, SIGHUP) and also carries a dead-man's switch
(--max-minutes: a shutdown from the user data, plus AutoReleaseTime on aliyun,
self-termination with an instance CAM role on tencent (spot instances take
no ActionTimer; checked over ssh before the run) or the `terminate` shutdown
behavior on aws), so a lost local process cannot
leave it running. --keep-instance skips the local release (for debugging)
but not the dead-man's switch. At the end the provider lists the instances
still tagged Project=tlx in the regions used.

Bench mode (--bench, repeatable): instead of verify.py, run
scripts/bench.py on the instance with each --bench argument string in turn
(shell words, e.g. --bench "tlcbase --missing --collect" --bench "run
--tlc --repeat 3"), for benchmarks of record on a quiet machine. Java 21 is installed
for TLC and tla2tools.jar and community/modules.jar are uploaded; the TLC
-workers N cache that came with corpus/out is dropped (measured elsewhere);
this tree's bench.py and tlc.py are used. TLX_BENCH_MACHINE names the
instance (type, zone, spot price), recorded with the results. --bench-bin
NAME=REV[:FEATURES] (repeatable) also builds revision REV (with these
comma-separated cargo features of tlx-cli) into
target/bench-bins/NAME/tlx on the instance, for `bench.py ab`, e.g.
  --bench-bin nostats=HEAD:no-stats --bench "ab --bin default=target/release/tlx
  --bin nostats=target/bench-bins/nostats/tlx --models ... --repeat 10"
A before/after comparison on one instance is the same shape with a second
--bench pass, each naming its own binary, e.g. a coverage census of the
previous revision and of this tree on the same machine:
  --bench-bin before=HEAD~1 --bench "coverage --dynamic --bin target/bench-bins/before/tlx"
  --bench "coverage --dynamic --bin target/release/tlx"
Every --bench argument is validated here, before anything is built or
provisioned: its subcommand must be one the prelaunch smoke can run and its
options must parse with bench.py's own parser.
Everything under bench/ on the instance (history/*.json, ab outputs,
machine.txt), bench-tlc.json and the output (bench.out) are copied
to target/bench/<time>-<rev>-<provider>[-x86_64]/ with cloud.json, also
after a failed run; copy what should be committed into bench/ by hand. Pass
a --max-minutes that covers the whole run. Bench mode runs bench.py instead of
verify.py, so the main-pass selectors of verify.py are refused before the
launch: --suites cannot be combined with --bench, and
--oracle cannot be combined with --bench (run such a verify.py pass in a
second invocation). --then may be combined with --bench: those passes run
after the benchmark commands, on the same instance.

Oracle mode (--oracle, repeatable): before verify.py, run scripts/corpus.py
on the instance with each --oracle argument string, all at the same time
(shell words; share the CPUs out with -j and --tlc-workers,
e.g. --oracle "tlc --source external --tier medium,large -j 4 --tlc-workers
8 --timeout 10800"), to compute TLC oracles that take too long on the local
machine. Java 21 is installed and tla2tools.jar and community/modules.jar
are uploaded (as in bench mode); this tree's corpus.py and tlc.py are used.
The corpus/out/tlc*.json files of the instance come back to oracle/ under
the result directory (copy the ones you want into corpus/out/ by hand),
during the passes and at the end, also after a failed pass. verify.py runs
afterwards only when --suites is given (then with the fresh oracle files, e.g.
--suites corpus-ext-large), followed by the --then passes. The external corpora (third_party/external,
fetched by scripts/fetch-external.py) are uploaded in every mode.

--dry-run prints the plan without creating anything; without valid
credentials it prints what it can. --list only lists tagged instances;
--list --mine selects the current branch's owner tag, and --cleanup --mine
terminates only that owner's instances. All-owner cleanup requires --all.
The shared git ledger caps each branch at 5 CNY of estimated 12 h compute
spend (for tencent/aliyun; expandable with --grant --budget-cny) and 60 min
per launch (expandable with --grant --minutes); more than 16 vCPU needs
--full/--bench with --allow-big. Coordinator operations (--grant,
--budget-override, --prune-sg) require the main worktree, or --coordinator-hub
in a linked worktree whose shared git common directory is a bare repository.
The exit status is verify.py's (0 passed, 1 failed), 3 for infrastructure
failure, or a classified STOP code 20-25 (docs/cloud-verification.md).

Launch admission: before the launch call (atomically with the ledger
reservation) the run counts the account's instances (the provider's listing
of all regions plus the ledger's launches it cannot show yet) and refuses
locally, without a provider call, when the owner already runs its share
(the largest of default_share in the cloud config, --slots N on the launch,
and the --slots of a coordinator grant in the 12 h window) or the account's
spot_instance_quota (or --max-account-slots) is used up; on tencent the exact
request then goes to RunInstances as a dry run first, whose quota answer
also stops it before anything is created. --wait-quota MINUTES|auto waits
for a slot instead (same offer, read-only checks). Refused, cancelled and
never-sent launches cost no launch, grant or budget. A cancel (signal, or
--cancel from the same worktree) is checked after the preflights, while
waiting and immediately before the launch call.
"""
import argparse, dataclasses, math, contextlib, fcntl, json, os, shlex, signal, subprocess, sys, threading, time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cloud import setup
from cloud.session import Hooks, Session
from cloud.setup import env_proxy, sources, then_args, verify_args, verify_runs_tlc
from cloud.cloud_common import AccountError, CloudStop, clippy_preflight, cloud_limits, current_owner, mask_identity, owner_tag, release_preflight, warning, INFRA_FAIL, Interrupted, Machine, Offer, ProviderQuotaFull, ROOT, RetryClock, SkipOffer, SlotHolder, TERMINAL_STATES, ensure_local_key, git, local_toolchain, log, parse_bench_bin, rank_offers, retry_network, terminate_until_gone

PROVIDERS = {"aliyun": "cloud.cloud_aliyun.AliyunProvider", "aws": "cloud.cloud_aws.AwsProvider", "tencent": "cloud.cloud_tencent.TencentProvider"}


def _resolve_git_path(path):
    return os.path.realpath(path if os.path.isabs(path) else os.path.join(ROOT, path))


def _is_bare_git_dir(common_dir):
    try:
        return git("--git-dir", common_dir, "rev-parse", "--is-bare-repository") == "true"
    except (OSError, subprocess.CalledProcessError):
        return False


def check_coordinator(coordinator_hub=False):
    git_dir = _resolve_git_path(git("rev-parse", "--git-dir"))
    common_dir = _resolve_git_path(git("rev-parse", "--git-common-dir"))
    if git_dir == common_dir:
        return
    if coordinator_hub and _is_bare_git_dir(common_dir):
        return
    if coordinator_hub:
        raise CloudStop(
            "--coordinator-hub is only valid when the shared git common directory is a bare repository; "
            "run coordinator operations from the main worktree instead",
            25,
        )
    raise CloudStop(
        "budget override/grant/security-group prune is coordinator-only (main worktree, or a linked worktree "
        "backed by a bare git common directory with --coordinator-hub); ask the coordinator for a grant "
        "(cloud_verify.py --grant OWNER --minutes M)",
        25,
    )


def check_override(reason, *, coordinator_hub=False):
    if reason is None:
        return
    if not reason.strip():
        raise CloudStop("budget override needs a nonempty reason", 25)
    check_coordinator(coordinator_hub)
    warning("budget override: " + reason)


# Ledger row statuses that count as a launch (the provider may have created an
# instance): "reserved" (outcome unknown) and "launched". Every other status
# ("refused": the provider or the admission said no; "cancelled": stopped
# before the provider call) costs neither a launch, a grant nor budget.
LAUNCH_STATUSES = ("reserved", "launched")
GRANT_WINDOW_SECS = 12 * 3600
# Estimated spend per owner (tencent/aliyun) in the window without a grant; a grant
# with --budget-cny adds its allowance to this (a coordinator grant's budget).
BASE_BUDGET_CNY = 5
# A launch longer than this needs a coordinator grant that names a heavy job (user decision
# 2026-10-08: a named heavy job may run past three hours; on-demand billing stays forbidden).
MAX_GRANT_MINUTES = 180
MAX_LONG_GRANT_MINUTES = 720
LONG_GRANT_HINT = ("long lane: this is a spot instance, so a reclaim is always possible - the run "
                   "copies each model's result back as it completes, so a reclaim loses only the "
                   "model in flight; the dead-man's switch still ends the instance at the limit")
MAX_GRANT_BUDGET_CNY = 30


class AdmissionRefused(CloudStop):
    """The local admission refused a launch before any provider call."""

    def __init__(self, admission):
        super().__init__(admission.reason, admission.code)
        self.admission = admission


class Cancelled(Interrupted):
    """A cancel (signal or `--cancel`) seen at a checkpoint before the provider launch call."""


class LaunchLedger:
    """The common git directory serializes budget decisions across worktrees.

    Reserve before the API call, persist even after a crash, and retain unknown
    outcomes conservatively. A reservation the provider refused, that the local
    admission refused or that never reached the provider call does not use a
    launch, a grant or budget; its row stays as evidence.
    """
    def __init__(self, path=None):
        self.path = path or os.path.join(_resolve_git_path(git("rev-parse", "--git-common-dir")), "tlx-cloud-ledger.json")

    @contextlib.contextmanager
    def locked(self):
        with open(self.path + ".lock", "a+") as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            try:
                with open(self.path) as source:
                    rows = json.load(source)
            except FileNotFoundError:
                rows = []
            except (ValueError, OSError) as e:
                raise CloudStop(f"budget ledger unreadable: {e}", 25) from e
            if not isinstance(rows, list) or any(not isinstance(row, dict) for row in rows):
                raise CloudStop("budget ledger is not a list of launch records", 25)
            yield rows

    def write(self, rows):
        tmp = self.path + ".tmp"
        with open(tmp, "w") as target:
            json.dump(rows, target, indent=1)
            target.flush()
            os.fsync(target.fileno())
        os.replace(tmp, self.path)

    def usage(self, owner, rows):
        """The owner's rolling 12 h window: (launches used, spent CNY, cap CNY, extra grant CNY)."""
        cutoff = time.time() - GRANT_WINDOW_SECS
        recent = [row for row in rows if row.get("owner") == owner and row.get("time", 0) > cutoff]
        counted = [row for row in recent if not row.get("grant") and row.get("status") in LAUNCH_STATUSES]
        used = len(counted)
        spent = sum(row.get("estimated_cost", 0) for row in counted if row.get("provider") in ("tencent", "aliyun"))
        extra = sum(row.get("budget_cny", 0) for row in recent if row.get("grant"))
        return used, spent, BASE_BUDGET_CNY + extra, extra

    def recent_launches(self, owner, rows=None):
        if rows is None:
            with self.locked() as records:
                return self.recent_launches(owner, records)
        return self.usage(owner, rows)[0]

    def launch_report(self, owner, rows=None):
        """The owner's 12 h launch count and remaining estimated CNY budget."""
        if rows is None:
            with self.locked() as records:
                return self.launch_report(owner, records)
        used, spent, cap, extra = self.usage(owner, rows)
        remaining_cny = max(0.0, cap - spent)
        return (f"owner {owner}: {used} launch(es) in 12 h; "
                f"{remaining_cny:.2f} of {cap:g} CNY estimated budget remaining "
                f"({BASE_BUDGET_CNY:g} CNY base + {extra:g} CNY from grants, {spent:.2f} CNY used)")

    def check_grant_owner(self, owner, rows):
        """Resolve a local branch to the worker's portable tag, or retain a ledger owner."""
        try:
            git("check-ref-format", "refs/heads/" + owner)
            git("rev-parse", "--verify", "--end-of-options", "refs/heads/" + owner)
            return owner_tag(owner)
        except subprocess.CalledProcessError:
            if owner and any(row.get("owner") == owner for row in rows):
                return owner
            branches = git("for-each-ref", "--format=%(refname:short)", "refs/heads/").splitlines()
        candidates = [branch for branch in branches if branch.rsplit("/", 1)[-1] == owner]
        hint = "; use " + " or ".join("--grant " + branch for branch in candidates) if candidates else (
            "; use --grant <exact-local-branch> (git branch --list), or an owner already in the launch ledger")
        raise CloudStop(f"grant owner {owner!r} is neither a local branch nor a recorded ledger owner" + hint, 25)

    def grant(self, owner, reason, minutes=60, slots=None, budget_cny=None):
        """Coordinator-only: grant `owner` a longer-duration lane (`minutes`),
        a higher 12 h concurrency share (`slots`), and/or extra 12 h estimated-
        spend budget (`budget_cny`)."""
        if not 0 < minutes <= MAX_LONG_GRANT_MINUTES:
            raise CloudStop(f"grant --minutes must be between 1 and {MAX_LONG_GRANT_MINUTES}", 25)
        if minutes > MAX_GRANT_MINUTES and reason in ("", "coordinator grant"):
            raise CloudStop(f"grant --minutes above {MAX_GRANT_MINUTES} needs --reason naming the "
                            f"heavy job it is for", 25)
        if slots is not None and not 0 < slots <= MAX_SLOTS:
            raise CloudStop(f"grant --slots must be between 1 and {MAX_SLOTS}", 25)
        if budget_cny is not None and not 0 < budget_cny <= MAX_GRANT_BUDGET_CNY:
            raise CloudStop(f"grant --budget-cny must be between 0 and {MAX_GRANT_BUDGET_CNY}", 25)
        with self.locked() as rows:
            owner = self.check_grant_owner(owner, rows)
            row = {"owner": owner, "time": time.time(), "grant": 1, "minutes": minutes, "reason": reason, "status": "grant"}
            if slots is not None:
                row["slots"] = slots
            if budget_cny is not None:
                row["budget_cny"] = budget_cny
            rows.append(row)
            self.write(rows)
            return row

    @staticmethod
    def share(rows, owner, default, requested=None):
        """How many instances `owner` may run at the same time: the largest of
        `default`, `requested` (`--slots` on a launch), and the `slots` of its
        grants in the 12 h window."""
        cutoff = time.time() - GRANT_WINDOW_SECS
        values = [default] + [row.get("slots", 0) for row in rows
                              if row.get("owner") == owner and row.get("grant") and row.get("time", 0) > cutoff]
        if requested is not None:
            values.append(requested)
        return max(values)

    @staticmethod
    def extra_budget(rows, owner):
        """The CNY allowance of `owner`'s grants in the 12 h window (consumed or not)."""
        cutoff = time.time() - GRANT_WINDOW_SECS
        return sum(row.get("budget_cny", 0) for row in rows
                   if row.get("owner") == owner and row.get("grant") and row.get("time", 0) > cutoff)

    def available_grant(self, rows, owner, minutes):
        return next((row for row in rows if row.get("owner") == owner and row.get("grant")
                     and row.get("time", 0) > time.time() - GRANT_WINDOW_SECS
                     and "consumed_by" not in row and row.get("minutes", 60) >= minutes), None)

    def release(self, owner, when, instance):
        """Record that the instance of the reservation made at `when` is gone
        (terminated by its run): the admission stops counting it."""
        self.release_instances(lambda row: row.get("owner") == owner and row.get("time") == when
                               and row.get("instance") in (None, instance), instance)

    def release_instances(self, match, instance=None):
        with self.locked() as rows:
            hit = False
            for row in rows:
                if not row.get("grant") and not row.get("released") and match(row):
                    row["released"] = time.time()
                    if instance and not row.get("instance"):
                        row["instance"] = instance
                    hit = True
            if hit:
                self.write(rows)

    def check(self, rows, owner, a, offer=None):
        if a.max_minutes <= 0:
            raise CloudStop("budget requires a positive --max-minutes", 25)
        if a.budget_override:
            return
        if a.max_minutes > 60 and self.available_grant(rows, owner, a.max_minutes) is None:
            raise CloudStop("budget requires --max-minutes between 1 and 60; ask the coordinator for a grant (cloud_verify.py --grant OWNER --minutes M)", 25)
        # A quota refusal is a stop condition, not a reason to try another region
        # (2026-10-07: a worker relaunched in a second region after one).
        # (A local admission refusal counts the whole account, not a region: no rule here.)
        if offer is not None:
            quota = [row for row in rows if row.get("owner") == owner and row.get("code") == 20 and not row.get("local")
                     and row.get("time", 0) > time.time() - 3600 and row.get("region") != offer.region]
            if quota:
                raise CloudStop(f"budget: {owner} had a quota refusal in {quota[-1].get('region')} within the hour; "
                                "do not work around it in another region (ask the coordinator)", 20)
        if offer and a.provider in ("tencent", "aliyun"):
            _, spent, cap, extra = self.usage(owner, rows)
            estimate = offer.price * max(a.max_minutes, getattr(a, "min_lifetime_minutes", 0)) / 60
            if spent + estimate > cap:
                raise CloudStop(f"budget: estimated 12 h cost {spent + estimate:.2f} CNY exceeds the {cap:g} CNY cap "
                                f"({BASE_BUDGET_CNY:g} CNY base + {extra:g} CNY from grants)", 25)
        if offer and offer.vcpus <= 0:
            raise CloudStop("budget: offer has no usable vCPU count", 25)
        if offer and offer.vcpus > 16 and not (
                a.allow_big and (a.tier == "full" or a.bench)):
            raise CloudStop("budget: more than 16 vCPU needs --full/--bench and --allow-big", 25)

    @contextlib.contextmanager
    def launch(self, owner, a, offer, admit=None):
        """Reserve a launch (under the ledger lock): the budget checks, then
        `admit(rows)` (an `Admission`; a refusal is recorded and raised as
        `AdmissionRefused` before anything is reserved), then the row. The body
        sets entry["api_called"] once the provider launch call is about to be
        made (`arm_checkpoint`); an exception before that, a provider refusal
        (stop codes 20-24) and a cancel leave a row that is no launch, and the
        grant it took is given back."""
        with self.locked() as rows:
            self.check(rows, owner, a, offer)
            now = time.time()
            admission = admit(rows) if admit else None
            if admission is not None and not admission.ok:
                rows.append({"owner": owner, "time": now, "instance": None, "type": offer.itype, "provider": a.provider,
                             "region": offer.region, "market": offer.market, "status": "refused", "code": admission.code,
                             "local": True, "admission": admission.record()})
                self.write(rows)
                raise AdmissionRefused(admission)
            entry = {"owner": owner, "time": now, "instance": None, "type": offer.itype,
                     "max_minutes": a.max_minutes, "estimated_cost": offer.price * max(a.max_minutes, getattr(a, "min_lifetime_minutes", 0)) / 60,
                     "provider": a.provider, "region": offer.region, "market": offer.market, "override": a.budget_override,
                     "status": "reserved"}
            if admission is not None:
                entry["admission"] = admission.record()
            grant = self.available_grant(rows, owner, a.max_minutes) if a.max_minutes > 60 and not a.budget_override else None
            if grant is not None:
                grant["consumed_by"] = entry["time"]
                entry["grant_minutes"] = grant.get("minutes", 60)
            rows.append(entry)
            self.write(rows)
            try:
                yield entry
            except CloudStop as e:
                if e.code in (20, 21, 22, 23, 24) or not entry.get("api_called"):
                    entry["status"] = "refused"
                    entry["code"] = e.code
                raise
            except BaseException as e:
                if not entry.get("api_called"):
                    # Nothing reached the provider: a cancel or a local error is no launch.
                    entry["status"] = "cancelled" if isinstance(e, (Interrupted, KeyboardInterrupt)) else "refused"
                    entry["local"] = True
                raise
            finally:
                if entry["instance"]:
                    entry["status"] = "launched"
                if entry["status"] not in LAUNCH_STATUSES and grant is not None and grant.get("consumed_by") == entry["time"]:
                    # A refused or cancelled launch gives its grant back (2026-10-08: a
                    # refused launch consumed a coordinator grant; the row stays as evidence).
                    del grant["consumed_by"]
                    entry["grant_returned"] = True
                self.write(rows)


# --- Launch admission: the account's instance slots and the owner's share -------

MAX_SLOTS = 16
# A reservation without an instance id counts for this long (RunInstances
# answers in seconds; a crashed process's instance shows in the provider's
# listing after that).
IN_FLIGHT_SECS = 600
# A recorded instance missing from a listing taken up to this long after its
# launch still counts (the listing may not show it yet).
LISTING_LAG_SECS = 180
# Re-listing interval while waiting for a slot (read-only listings, no launch call).
ADMISSION_POLL_SECS = (60, 120, 240)
# --wait-quota auto: until the earliest recorded dead-man's deadline of a
# blocking instance plus this margin, at most AUTO_WAIT_CAP_MIN (60 when no
# deadline is known).
AUTO_WAIT_MARGIN_SECS = 120
AUTO_WAIT_CAP_MIN = 180
AUTO_WAIT_UNKNOWN_MIN = 60


@dataclasses.dataclass
class Admission:
    """The admission decision for one launch, from the provider's listing and the ledger."""
    ok: bool
    in_use: int              # the account's spot instances (every owner, untagged ones included)
    quota: int | None        # the account's spot instance quota (cloud.json), None when not configured
    yours: int               # the owner's active instances (any market)
    share: int               # how many the owner may run at the same time
    holders: list
    code: int = 0
    reason: str = ""
    next_free: float | None = None   # earliest recorded dead-man's deadline among the blocking instances

    def line(self):
        head = (f"{self.in_use} of {self.quota} account spot slots in use" if self.quota is not None
                else f"{self.in_use} spot instances in use (no account quota configured)")
        return f"{head} (yours {self.yours}, share {self.share})"

    def by_owner(self):
        counts = {}
        for h in self.holders:
            counts[h.owner] = counts.get(h.owner, 0) + 1
        return ", ".join(f"{o} {n}" for o, n in sorted(counts.items(), key=lambda kv: (-kv[1], str(kv[0])))) or "none"

    def record(self):
        return {"in_use": self.in_use, "quota": self.quota, "yours": self.yours, "share": self.share,
                "holders": [{"owner": h.owner, "state": h.state, "source": h.source, "market": h.market} for h in self.holders]}


def slot_view(provider):
    """(holders, listed_at): the provider's view of the account's instances in
    all its regions (`slot_holders`; providers without it: the tagged
    instances, owners from a second, owner-filtered listing)."""
    listed_at = time.time()
    if hasattr(provider, "slot_holders"):
        return retry_network(lambda: provider.slot_holders(provider.all_regions), "list the account's instances"), listed_at
    every = retry_network(lambda: provider.leftovers(provider.all_regions), "list tagged instances")
    mine = {iid for _, iid, _ in retry_network(lambda: provider.leftovers(provider.all_regions, owner=provider.owner),
                                               "list owned instances")} if provider.owner else set()
    return [SlotHolder(r, iid, state, provider.owner if iid in mine else "(other)") for r, iid, state in every], listed_at


def holding(state):
    """Whether an instance in `state` runs for its owner (the share); every
    listed state, terminating ones included, holds account quota."""
    return state.lower() not in TERMINAL_STATES and state.upper() != "LAUNCH_FAILED"


def admit(view, rows, owner, provider_name, market, quota, share, now=None, account_cap=None):
    """The `Admission` of one more `market` instance for `owner`: the
    provider's listing plus the ledger's launches it cannot show yet
    (reservations in flight, instances launched after the listing). The
    account check applies to spot launches under the smaller of the configured
    `quota` and the launcher's own `account_cap` (`--max-account-slots`); the
    share applies to every launch (share None: none, a budget override)."""
    now = time.time() if now is None else now
    # A wave of concurrent launchers of one account honours both caps together:
    # the listing every launcher reads is account-wide.
    caps = [(value, name) for value, name in ((quota, "the cloud config's spot_instance_quota"),
                                              (account_cap, "--max-account-slots")) if value is not None]
    quota, cap_from = min(caps, key=lambda pair: pair[0]) if caps else (None, "")
    holders, listed_at = view
    holders = list(holders)
    listed = {h.id for h in holders if h.id}
    deadlines = {}
    for row in rows:
        if (row.get("grant") or row.get("provider") != provider_name or row.get("status") not in LAUNCH_STATUSES
                or row.get("released")):
            continue
        t, iid = row.get("time", 0), row.get("instance")
        due = t + row.get("max_minutes", 60) * 60
        if iid in listed:
            deadlines[iid] = due
        elif iid is None and t > now - IN_FLIGHT_SECS:
            holders.append(SlotHolder(row.get("region", "?"), None, "in flight", row.get("owner"),
                                      row.get("market", "spot"), due, "ledger"))
        elif iid and t > listed_at - LISTING_LAG_SECS:
            holders.append(SlotHolder(row.get("region", "?"), iid, "just launched", row.get("owner"),
                                      row.get("market", "spot"), due, "ledger"))
    for h in holders:
        if h.deadline is None and h.id in deadlines:
            h.deadline = deadlines[h.id]
    spot = [h for h in holders if h.market == "spot"]
    mine = [h for h in holders if h.owner == owner and holding(h.state)]
    a = Admission(True, len(spot), quota, len(mine), share if share is not None else MAX_SLOTS, holders)

    def due(blocking):
        known = [h.deadline for h in blocking if h.deadline]
        return min(known) if known else None
    if share is not None and len(mine) >= share:
        a.ok, a.code, a.next_free = False, 25, due(mine)
        a.reason = (f"admission: {owner} already runs {len(mine)} instance(s), its share is {share} ({a.line()}); "
                    "nothing was sent to the provider. Wait for your instance (--wait-quota MINUTES|auto) or raise "
                    "your concurrency share with --slots N (bounded by the account spot quota)")
    elif market == "spot" and quota is not None and len(spot) >= quota:
        a.ok, a.code, a.next_free = False, 20, due(spot)
        a.reason = (f"admission: the account's spot quota is full: {a.line()}; held by {a.by_owner()}; "
                    f"the cap is {quota} from {cap_from}; "
                    "nothing was sent to the provider. Wait (--wait-quota MINUTES|auto) -- never switch region, "
                    "instance type or provider to get around it")
    if not a.ok and a.next_free:
        a.reason += f"; the earliest recorded dead-man's switch ends one by {time.strftime('%H:%M', time.localtime(a.next_free))}"
    return a


class Admitter:
    """Admission of the launches of one run: lists, decides under the ledger
    lock (`LaunchLedger.launch(admit=...)`), and waits for a slot within the
    --wait-quota budget with read-only listings only."""

    def __init__(self, provider, provider_name, owner, market, limits, share, wait_minutes, wait_auto, cancel=None,
                 *, account_cap=None, monotonic=None, sleep=None, view=None):
        self.provider, self.provider_name, self.owner, self.market = provider, provider_name, owner, market
        self.quota, self.share = limits.get("spot_instance_quota"), share
        self.account_cap = account_cap
        self.wait_minutes, self.wait_auto, self.cancel = wait_minutes, wait_auto, cancel
        self.clock = RetryClock(monotonic, sleep)
        self.view_fn = view or (lambda: slot_view(provider))
        self.until = None
        self.polls = 0
        self.last = None

    def decide(self, view, rows):
        self.last = admit(view, rows, self.owner, self.provider_name, self.market, self.quota, self.share,
                          account_cap=self.account_cap)
        log(self.last.line() + ("" if self.last.ok else " -- refused locally"))
        return self.last

    def budget_minutes(self, decision=None):
        """The --wait-quota budget; `auto` follows the ledger's deadlines."""
        if not self.wait_auto:
            return self.wait_minutes
        decision = decision or self.last
        if decision is None or not decision.next_free:
            return AUTO_WAIT_UNKNOWN_MIN
        return max(1.0, min(AUTO_WAIT_CAP_MIN, (decision.next_free + AUTO_WAIT_MARGIN_SECS - time.time()) / 60))

    def wait(self, refusal):
        """After a local refusal: sleep one poll interval if the budget allows
        (the caller lists and decides again), else raise the refusal."""
        if self.until is None:
            minutes = self.budget_minutes(refusal.admission)
            if minutes <= 0:
                raise refusal
            self.until = self.clock.now() + minutes * 60
            log(f"admission wait: up to {minutes:g} min for a slot (same region and type; read-only listings)")
        remaining = self.until - self.clock.now()
        if remaining <= 0:
            raise CloudStop(f"admission wait expired: {refusal.admission.reason}", refusal.code) from refusal
        delay = min(ADMISSION_POLL_SECS[min(self.polls, len(ADMISSION_POLL_SECS) - 1)], remaining)
        self.polls += 1
        self.clock.sleep_until(self.clock.now() + delay)
        if self.cancel:
            self.cancel.check("waiting for a slot")


CANCEL_FILE = "tlx-cloud-cancel"


class Cancel:
    """The cancel flag of a run: set by SIGINT/SIGTERM/SIGHUP, or by
    `cloud_verify.py --cancel` in the same worktree (a file in its git
    directory, newer than the run's start: a run started in the background
    may not see a signal). Checked after the preflights, while waiting for a
    slot and immediately before the provider launch call; a cancel there
    launches nothing."""

    def __init__(self, path=None, started=None):
        self._path = path
        self.started = time.time() if started is None else started
        self.reason = None

    @property
    def path(self):
        # (Resolved when first needed: --list/--grant never look.)
        if self._path is None:
            self._path = os.path.join(git("rev-parse", "--absolute-git-dir"), CANCEL_FILE)
        return self._path

    def set(self, reason):
        self.reason = self.reason or reason

    def requested(self):
        if self.reason:
            return self.reason
        try:
            if os.stat(self.path).st_mtime >= self.started:
                return f"cancel requested ({self.path})"
        except OSError:
            pass
        return None

    def check(self, where):
        why = self.requested()
        if why:
            raise Cancelled(f"cancelled before {where} ({why}); nothing launched")

    @staticmethod
    def request(path=None):
        path = path or os.path.join(git("rev-parse", "--absolute-git-dir"), CANCEL_FILE)
        with open(path, "w") as f:
            f.write(f"{time.time()}\n")
        return path


def wait_for_quota(provider, offer, arch, minutes, ledger, owner, *, monotonic=None, sleep=None):
    """Probe only the refused offer; neither capacity refusals nor probes spend launches.

    The clock and sleep are injectable (`RetryClock`), so a test drives the whole
    wait without real time."""
    clock = RetryClock(monotonic, sleep)
    until = clock.now() + minutes * 60
    backoff = 120
    while True:
        remaining = until - clock.now()
        if remaining <= 0:
            raise CloudStop(f"quota wait expired for {offer.itype} in {offer.region}", 20)
        delay = min(backoff, remaining)
        log(f"quota wait: {offer.region} {offer.itype}; dry-run in {delay / 60:g} min")
        # Keep signal handling and heartbeat output responsive during long waits.
        clock.sleep_until(clock.now() + delay)
        try:
            lines = provider.describe_plan(offer, arch)
            for line in lines:
                log("quota dry-run: " + line)
            if not any("DryRun: would succeed" in line for line in lines):
                raise CloudStop("quota dry-run cannot prove capacity (network/key prerequisites unavailable)", 23)
            log(f"quota available: {offer.region} {offer.itype}; launching this offer once")
            return
        except CloudStop as error:
            if error.code != 20:
                raise
            log(f"quota dry-run refused: {offer.region} {offer.itype}: {error}")
            with ledger.locked() as rows:
                rows.append({"owner": owner, "time": time.time(), "region": offer.region, "type": offer.itype,
                             "status": "refused", "code": 20, "probe": True})
                ledger.write(rows)
        backoff = min(backoff * 2, 480)


def spot_quota_refusal(error):
    """A provider's spot quota refusal (of the dry-run admission or of the
    launch call): Tencent's LimitExceeded.UserSpotQuota / LimitExceeded.SpotQuota."""
    return error.code == 20 and (isinstance(error, ProviderQuotaFull) or "SpotQuota" in str(error))


def arm_checkpoint(provider, entry, cancel):
    """The last check before the provider's launch call: a cancel raises
    `Cancelled` (nothing launched); otherwise the reservation is marked as
    having reached the provider. Providers that do not call `checkpoint`
    themselves pass it here, before `launch` (conservatively: their setup
    calls count as the launch call)."""
    def checkpoint():
        if cancel is not None:
            cancel.check("the provider launch call")
        entry["api_called"] = True
    provider.checkpoint = checkpoint
    if not getattr(provider, "calls_checkpoint", False):
        checkpoint()


def launch_with_quota_wait(provider, machine, ips, fresh, a, ledger, owner, launched_ids, admitter=None, cancel=None):
    """Admit, reserve and launch `machine.offer` once. A local admission
    refusal waits for a slot within the --wait-quota budget (read-only
    listings); a provider spot-quota refusal waits with same-offer dry-runs
    (`wait_for_quota`) and retries once. Returns the ledger entry."""
    retried = False
    while True:
        if cancel is not None:
            cancel.check("admission")
        view = admitter.view_fn() if admitter else None
        entry = {}
        try:
            with ledger.launch(owner, a, machine.offer,
                               admit=(lambda rows: admitter.decide(view, rows)) if admitter else None) as entry:
                machine.ledger_time = entry["time"]
                arm_checkpoint(provider, entry, cancel)
                try:
                    provider.launch(machine, ips, fresh, a.max_minutes, a.arch)
                except SkipOffer:
                    entry["status"] = "refused"
                    raise
                finally:
                    entry["instance"] = provider.find_launched(machine) if entry.get("api_called") else None
                    if entry["instance"]:
                        launched_ids.add(entry["instance"])
            return entry
        except AdmissionRefused as refusal:
            admitter.wait(refusal)
        except SkipOffer as error:
            if retried:
                raise CloudStop(f"same-offer launch retry refused after quota wait: {error}", 23) from error
            raise
        except CloudStop as error:
            if (retried or not a.wait_quota or not spot_quota_refusal(error)
                    or (entry.get("api_called") and provider.find_launched(machine))):
                raise
            if admitter and admitter.last:
                warning(f"the provider refused a launch the local count admitted ({admitter.last.line()}): it counts "
                        "more, or another limit applies (the ledger row records both views)")
            wait_for_quota(provider, machine.offer, a.arch,
                           admitter.budget_minutes() if admitter else a.wait_quota, ledger, owner)
            retried = True


def instance_machine(provider, region, iid):
    """A Machine-shaped handle for an instance this invocation did not launch
    (termination and the leftover line only use its region and id)."""
    m = Machine(provider, Offer(0.0, region, "", ""))
    m.id = iid
    return m


def manage_instances(provider, a, owner, summary=None, released=None):
    """--list / --cleanup. `summary()` prints the account's slot use (every
    owner, so a worker can plan around the shared quota); `released(iids)`
    records terminated instances in the ledger."""
    if a.cleanup and not (a.mine or a.all):
        raise CloudStop("cleanup without --mine requires explicit --all", 25)
    left = retry_network(lambda: provider.leftovers(provider.all_regions, owner=owner if a.mine else None),
                         "list tagged instances")
    for region, iid, state in left:
        log(f"  {region}: {iid} {state}")
    log(f"{len(left)} tagged instance(s)" + (f" owned by {owner}" if a.mine else ""))
    if summary is not None and not a.cleanup:
        try:
            summary()
        except Exception as e:  # noqa: BLE001 - information only; the exit status is the listing's
            warning(f"cannot count the account's slots: {type(e).__name__}: {e}")
    active = [r for r in left if r[2].lower() not in TERMINAL_STATES]
    if a.cleanup:
        failed, gone = [], []
        for region, iid, _ in active:
            m = instance_machine(provider, region, iid)
            if not terminate_until_gone(provider, m):
                failed.append(iid)
                log(f"STOP: could not terminate {iid} in {region}: {provider.terminate_hint(m)}")
            else:
                gone.append(iid)
        if released is not None and gone:
            released(gone)
        return INFRA_FAIL if failed else 0
    return 1 if (active if a.mine else left) else 0


def prune_security_groups(provider, ledger, regions, *, coordinator_hub=False):
    """The only destructive SG operation: coordinator, idle account, launch lock.

    LaunchLedger.launch holds this same lock through the provider launch call,
    so zero-instance admission and deletion cannot race a supported launch.
    The check is account-wide even when pruning just one requested region.
    """
    check_coordinator(coordinator_hub)
    with ledger.locked() as rows:
        recent = [r for r in rows if r.get("provider") == provider.name
                  and r.get("status") in LAUNCH_STATUSES
                  and time.time() - r.get("time", 0) < IN_FLIGHT_SECS]
        if recent:
            raise CloudStop("security-group prune refused: recent launch reservations may not be visible yet; "
                            "wait for launch visibility and release", 25)
        left = provider.leftovers(provider.all_regions)
        if left:
            raise CloudStop(f"security-group prune refused: {len(left)} tagged instance(s) still exist "
                            "in the account; wait until all runs have released their instances", 25)
        provider.prune_ssh_rules(regions)
    return 0


def make_provider(name):
    mod, cls = PROVIDERS[name].rsplit(".", 1)
    return getattr(__import__(mod, fromlist=[cls]), cls)()


def parse_args(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("rev", nargs="?", default="HEAD")
    tier = ap.add_mutually_exclusive_group()
    tier.add_argument("--quick", dest="tier", action="store_const", const="quick")
    tier.add_argument("--full", dest="tier", action="store_const", const="full")
    ap.add_argument("--suites", default="")
    ap.add_argument("--filter", default="")
    ap.add_argument("--env", action="append", default=[], metavar="K=V",
                    help="forwarded to the remote verify.py --env (repeatable): environment for the tlx runs")
    ap.add_argument("--strict", action="store_true")
    ap.add_argument("--fuzz-minutes", type=float, default=None,
                    help="forwarded to the remote verify.py: duration of the fuzz-campaign suite")
    ap.add_argument("--then", action="append", default=[], metavar="ARGS",
                    help="after the main run, run verify.py again on the same instance with these arguments "
                    "(shell words: [REV] [--suites ...] [--env K=V]...; repeatable, in order; also after --bench, "
                    "where the benchmark commands run first)")
    ap.add_argument("--bench", action="append", default=[], metavar="ARGS",
                    help="bench mode: run scripts/bench.py ARGS remotely instead of verify.py (repeatable, in order)")
    ap.add_argument("--bench-bin", action="append", default=[], metavar="NAME=REV[:FEATURES]",
                    help="bench mode: also build REV (cargo features of tlx-cli) into target/bench-bins/NAME/tlx")
    ap.add_argument("--oracle", action="append", default=[], metavar="ARGS",
                    help="oracle mode: run scripts/corpus.py ARGS remotely first (repeatable, in order); "
                    "verify.py follows only with --suites")
    ap.add_argument("--provider", choices=sorted(PROVIDERS), default="aliyun")
    ap.add_argument("--arch", choices=["arm64", "x86_64"], help="default: the provider's (arm64; tencent: x86_64)")
    ap.add_argument("--instance-type", help="default: the provider's types for --arch (aliyun: ecs.c8y/g8y.4xlarge or "
                    "ecs.c8a/g8a.4xlarge, cheapest wins; tencent: SA5/SA9.4XLARGE32 (--quick) or SA9.16XLARGE128, "
                    "SA5.16XLARGE256, SA4.16XLARGE128 (--full) for x86_64, SR1 for arm64; aws: c7g.16xlarge or c7a.16xlarge)")
    ap.add_argument("--disk-gb", type=int, default=None,
                    help="system-disk size in GB (default: the provider's constant: tencent 512, sized for the "
                         "corpus; aliyun/aws 40). TLC's disk-backed state queue (and -metadir) is unbounded on a "
                         "large model: a run that dies with 'No space left on device' wants a larger --disk-gb")
    ap.add_argument("--region", help="aliyun: cn-hangzhou (default), cn-shanghai, cn-beijing, cn-hongkong, ap-northeast-1, "
                    "ap-southeast-1; tencent: ap-guangzhou and ap-shanghai (default: both), ap-beijing, ap-nanjing, "
                    "ap-chengdu, ap-hongkong, ap-singapore; aws: ap-northeast-1, ap-southeast-1 (default: both)")
    ap.add_argument("--on-demand", action="store_true",
                    help="tencent: also offer pay-as-you-go (POSTPAID_BY_HOUR) instances, tried after every spot offer")
    ap.add_argument("-j", "--jobs", type=int, help="verify.py -j (default: vCPUs - 1)")
    ap.add_argument("--toolchain", help="Rust toolchain (default: rust-toolchain.toml)")
    ap.add_argument("--rust-from", choices=["auto", "mirror", "upload", "upstream"], default="auto")
    ap.add_argument("--crates-from", choices=["auto", "mirror", "vendor", "upstream"], default="auto")
    ap.add_argument("--cc", default="clang", help="C compiler for generated code and C deps (default clang, as on macOS)")
    ap.add_argument("--keep-instance", action="store_true", help="do not release (the dead-man's switch still applies)")
    ap.add_argument("--dry-run", action="store_true")
    ap.add_argument("--wait-quota", default="0", metavar="MINUTES|auto",
                    help="when the account's spot slots or your share are in use, wait up to MINUTES for one (read-only "
                    "listings; after a provider quota refusal, dry-runs of the same region/type), then launch once; "
                    f"auto: until the earliest recorded dead-man's switch of a blocking instance (at most {AUTO_WAIT_CAP_MIN} min)")
    ap.add_argument("--max-account-slots", type=int, metavar="N",
                    help="refuse a launch locally, before any provider call, while the account already runs N spot "
                         "instances (a tighter cap than the cloud config's spot_instance_quota; the listing is "
                         "account-wide, so concurrent launchers of the account stop together at N)")
    ap.add_argument("--list", action="store_true", help="list the instances tagged Project=tlx and exit")
    ap.add_argument("--mine", action="store_true", help="list/clean only instances owned by this git branch")
    ap.add_argument("--all", action="store_true", help="explicitly allow cleanup of every owner's instances")
    ap.add_argument("--allow-big", action="store_true", help="allow more than 16 vCPU for --full or --bench")
    ap.add_argument("--budget-override", metavar="REASON", help="coordinator-only budget exception, recorded in the ledger")
    ap.add_argument("--coordinator-hub", action="store_true",
                    help="authorize --grant, --budget-override, or --prune-sg from a linked worktree when the "
                         "shared git common directory is a bare repository")
    ap.add_argument("--grant", metavar="OWNER",
                    help="coordinator-only: grant OWNER (a branch) a longer launch lane (--minutes), a higher 12 h "
                         "concurrency share (--slots), and/or a larger 12 h estimated-spend cap (--budget-cny)")
    ap.add_argument("--minutes", type=int, help="with --grant: maximum minutes for its one long launch "
                    f"(1-{MAX_LONG_GRANT_MINUTES}, above {MAX_GRANT_MINUTES} only with --reason; default 60)")
    ap.add_argument("--reason", help="with --grant: why the grant is needed; required above "
                    f"{MAX_GRANT_MINUTES} minutes, where it must name the heavy job")
    ap.add_argument("--budget-cny", type=float, metavar="X", help="with --grant: raise OWNER's estimated 12 h spend cap by X CNY "
                    f"for the window (0-{MAX_GRANT_BUDGET_CNY}; default: the base {BASE_BUDGET_CNY} CNY only)")
    ap.add_argument("--slots", type=int, metavar="N",
                    help=f"maximum concurrent instances this owner may run (1-{MAX_SLOTS}; on a launch or --dry-run, "
                         "raises this invocation's share while remaining bounded by spot_instance_quota and "
                         "--max-account-slots; with --grant, persists a 12 h share grant for OWNER; default: the "
                         "provider's default_share in the cloud config, 1)")
    ap.add_argument("--cancel", action="store_true", help="cancel this worktree's running cloud_verify before it launches "
                    "(it stops at its next checkpoint: after the preflights, while waiting for a slot, before the launch call)")
    ap.add_argument("--prune-sg", action="store_true", help="coordinator-only: prune owner-tagged ssh rules, "
                    "only when the account has no tagged instances; requires --cleanup")
    ap.add_argument("--cleanup", action="store_true", help="terminate every instance tagged Project=tlx and exit")
    ap.add_argument("--ssh-proxy", help="HOST:PORT of an HTTP CONNECT proxy for ssh, 'none', or 'auto' (the https_proxy "
                    "of the environment); default: auto for aws, none for aliyun")
    ap.add_argument("--max-minutes", type=int, default=60, help="dead-man's switch: the instance shuts down / is released after this")
    ap.add_argument("-v", "--verbose", action="store_true", help="verify.py -v (stream all suite output)")
    a = ap.parse_args(argv)
    a.tier = a.tier or "quick"
    if a.disk_gb is not None and a.disk_gb < 20:
        ap.error("--disk-gb must be at least 20")
    if a.prune_sg and (not a.cleanup or a.mine or a.all or a.list or a.dry_run or a.grant or a.slots is not None):
        ap.error("--prune-sg requires --cleanup alone (no --mine/--all/--list/--dry-run/--grant/--slots); it never terminates instances")
    if a.coordinator_hub and not (a.grant or a.budget_override is not None or a.prune_sg):
        ap.error("--coordinator-hub requires --grant, --budget-override, or --prune-sg")
    if a.minutes is not None and (not a.grant or not 0 < a.minutes <= MAX_LONG_GRANT_MINUTES):
        ap.error(f"--minutes requires --grant and must be between 1 and {MAX_LONG_GRANT_MINUTES}")
    if a.reason is not None and not a.grant:
        ap.error("--reason requires --grant")
    if (a.minutes or 60) > MAX_GRANT_MINUTES and not a.reason:
        ap.error(f"--minutes above {MAX_GRANT_MINUTES} requires --reason naming the heavy job")
    if a.slots is not None and not 0 < a.slots <= MAX_SLOTS:
        ap.error(f"--slots must be between 1 and {MAX_SLOTS}")
    if a.budget_cny is not None and (not a.grant or not 0 < a.budget_cny <= MAX_GRANT_BUDGET_CNY):
        ap.error(f"--budget-cny requires --grant and must be between 0 and {MAX_GRANT_BUDGET_CNY}")
    a.wait_auto = a.wait_quota == "auto"
    try:
        a.wait_quota = float(AUTO_WAIT_CAP_MIN if a.wait_auto else a.wait_quota)
    except ValueError:
        ap.error("--wait-quota must be a number of minutes or auto")
    if not math.isfinite(a.wait_quota) or a.wait_quota < 0:
        ap.error("--wait-quota must be finite and nonnegative")
    if a.mine and a.all:
        ap.error("--mine and --all are mutually exclusive")
    if (a.mine or a.all) and not (a.list or a.cleanup):
        ap.error("--mine/--all needs --list or --cleanup")
    if a.max_account_slots is not None and a.max_account_slots < 1:
        ap.error("--max-account-slots must be at least 1")
    if a.bench_bin and not a.bench:
        ap.error("--bench-bin needs --bench")
    if a.oracle and a.bench:
        ap.error("--oracle cannot be combined with --bench")
    if a.suites and a.bench:
        ap.error("--suites cannot be combined with --bench: bench mode runs bench.py instead of verify.py, "
                 "so --suites would be ignored; drop one of them, or run the suites in a second invocation")
    try:
        a.bench_bins = [parse_bench_bin(b) for b in a.bench_bin]
    except ValueError as e:
        ap.error(str(e))
    # Every --bench argument is validated here, before anything local is built:
    # the subcommand the prelaunch smoke can run, its options through bench.py's
    # own parser (whose single owner is benchmarking/cli.py - a preflight that
    # rebuilt the subparser by hand missed the flags bench.py adds to every
    # subcommand and refused `profile --models A --deadline-min 5`, which
    # bench.py itself accepts, HARNESS-02), and profile model IDs resolved
    # without building a binary or executing a model (H-03 item 8).
    if not (a.list or a.cleanup):
        check_bench_commands(a.bench, ap)
    for pair in a.env:
        if "=" not in pair or not pair.split("=", 1)[0]:
            ap.error(f"--env expects K=V, got {pair!r}")
    return a


def check_bench_commands(commands, ap):
    """Refuse a ``--bench`` argument the launch could not run, at the selector stage.

    ``benchmarking.bench_smoke.preflight`` is what executes the command, but before it looks
    at the subcommand it brings ``target/release/tlx`` up to date (and, for a
    coverage census, runs a workspace Clippy). A typo such as
    ``--bench "repr_check --oracle"`` was therefore refused as "prelaunch bench
    smoke refused" only after minutes of local work, and after the launcher had
    already been chosen (H-03 item 8). The judgement is the same one, moved to
    where a selector error belongs: the subcommand set is bench_smoke's own
    (``MEASURE_COMMANDS`` - the smoke's authority, never a second copy), and
    every other option is parsed by bench.py's own parser, the parser that will
    execute it (HARNESS-02). ``profile`` model ids are resolved here too, as
    before provisioning.

    Raises through ``ap.error``: the refusal is a selector refusal, so it prints
    like every other one and exits 2.
    """
    import contextlib
    import io
    from benchmarking.bench_smoke import MEASURE_COMMANDS
    for command in commands:
        words = shlex.split(command)
        if not words:
            ap.error("--bench command is empty")
        if words[0] == "profile":
            from benchmarking import bench_profile
            from benchmarking import cli as bench_cli
            _, options = bench_cli.parse_args(words, prog=f"bench.py {words[0]}")
            bench_profile.resolve([m.strip() for m in options.models.split(",") if m.strip()])
            continue
        if words[0] not in MEASURE_COMMANDS:
            ap.error(f"--bench {words[0]!r} is not a benchmark the prelaunch smoke can run: "
                     + ", ".join(sorted(MEASURE_COMMANDS)))
        if words[0] != "coverage":
            # `coverage` is forwarded to coverage.py by bench.py before parsing;
            # every other measure command is bench.py's own subparser. Its own
            # error text is kept (the tail of it) and re-raised through this
            # parser, so the refusal is a selector refusal with the cause in it.
            from benchmarking import cli as bench_cli
            captured = io.StringIO()
            try:
                with contextlib.redirect_stderr(captured):
                    bench_cli.parse_args(words, prog=f"bench.py {words[0]}")
            except SystemExit:
                reason = " ".join(captured.getvalue().split())
                ap.error(f"--bench {command!r} is refused by bench.py's own parser: {reason[-400:]}")


def main():
    try:
        return run(parse_args())
    except CloudStop as e:
        log(str(e))
        return e.code
    except Interrupted as e:
        # (Raised before the launch phase: that phase handles its own.)
        log(f"STOP: interrupted ({e}); nothing launched")
        return INFRA_FAIL
    except Exception as e:
        error = CloudStop(f"infrastructure failure: {type(e).__name__}: {e}")
        log(str(error))
        return error.code


def run(a):
    if a.cancel:
        log(f"cancel requested ({Cancel.request()}): a cloud_verify of this worktree stops before its next launch call")
        return 0
    cancel = Cancel()

    def on_signal(signum, _frame):
        cancel.set(f"signal {signum}")
        raise Interrupted(f"signal {signum}")
    # From the start, not only once the launch phase begins (2026-10-08: a cancel
    # during the local preflight still provisioned an instance; a background
    # run inherits an ignored SIGINT unless it installs its own handler).
    previous = {}
    if threading.current_thread() is threading.main_thread():
        previous = {s: signal.signal(s, on_signal) for s in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)}
    try:
        return run_checked(a, cancel)
    finally:
        for s, handler in previous.items():
            signal.signal(s, handler)


def run_checked(a, cancel):
    """The preflights, the plan, and then the session that executes it.

    Everything up to the plan is this entrypoint's own policy -- who owns the
    launch, whether the budget allows it, whether the tree would even build
    remotely -- and it happens before anything is provisioned. The plan states
    what will be launched; from there `cloud/session.py` owns the run and its
    single cleanup.
    """
    owner = current_owner() if a.mine or not (a.list or a.cleanup or a.grant) else None
    check_override(a.budget_override, coordinator_hub=a.coordinator_hub)
    if a.prune_sg:
        check_coordinator(a.coordinator_hub)
    if a.grant:
        check_coordinator(a.coordinator_hub)
        ledger = LaunchLedger()
        row = ledger.grant(a.grant, a.reason or a.budget_override or "coordinator grant",
                           minutes=a.minutes or 60, slots=a.slots, budget_cny=a.budget_cny)
        if (a.minutes or 60) > MAX_GRANT_MINUTES:
            log(LONG_GRANT_HINT)
        log(f"granted {row['minutes']} min lane to {row['owner']}"
            + (f" with a share of {a.slots} concurrent instance(s)" if a.slots else "")
            + (f" and {a.budget_cny:.2f} CNY more estimated spend" if a.budget_cny else "")
            + f" ({ledger.launch_report(row['owner'])})")
        return 0
    if a.cleanup and not (a.mine or a.all or getattr(a, "prune_sg", False)):
        raise CloudStop("cleanup without --mine requires explicit --all", 25)
    ledger = LaunchLedger()
    if a.prune_sg:
        provider = make_provider(a.provider)
        log(f"{a.provider}: {mask_identity(provider.check_account())}")
        regions = [a.region] if a.region else provider.all_regions
        if any(r not in provider.all_regions for r in regions):
            raise CloudStop("unknown prune region", 25)
        return prune_security_groups(provider, ledger, regions, coordinator_hub=a.coordinator_hub)
    if not (a.list or a.cleanup):
        with ledger.locked() as rows:
            ledger.check(rows, owner, a)
            log(ledger.launch_report(owner, rows))
    if a.bench and not (a.list or a.cleanup):
        # A release binary the bench smoke would refuse (stale or missing) is
        # built here, once, before anything is provisioned: the smoke's own
        # freshness guard builds too, but it ignores the build's exit status and
        # stops with "still older than ... after cargo build --release", which
        # names no cause (2026-10-10).
        ok, note = release_preflight(dry_run=a.dry_run)
        if not ok:
            raise CloudStop(f"prelaunch release build refused: {note}", 23)
        log(note)
        from benchmarking.bench_smoke import preflight
        try:
            preflight(a.bench)
        except (ValueError, OSError, subprocess.SubprocessError) as error:
            raise CloudStop(f"prelaunch bench smoke refused: {error}", 23) from error
    provider = make_provider(a.provider)
    provider.owner = owner
    if a.disk_gb is not None:
        provider.disk_gb = a.disk_gb
    a.min_lifetime_minutes = provider.min_lifetime_minutes
    a.arch = a.arch or getattr(provider, "default_arch", "arm64")
    if a.on_demand:
        if not getattr(provider, "supports_on_demand", False):
            raise CloudStop(f"cloud_verify: --on-demand is not supported with --provider {a.provider}")
        provider.on_demand = True
    if a.region and a.region not in provider.all_regions:
        raise CloudStop(f"cloud_verify: --region {a.region} is not one of {', '.join(provider.all_regions)} ({a.provider})")
    regions = [a.region] if a.region else provider.default_regions
    types = [a.instance_type] if a.instance_type else provider.default_types(a.arch, a.tier)
    toolchain = a.toolchain or local_toolchain()
    ssh_proxy = a.ssh_proxy or provider.default_ssh_proxy
    proxy = env_proxy() if ssh_proxy == "auto" else (None if ssh_proxy == "none" else ssh_proxy)

    sha = git("rev-parse", "--verify", a.rev + "^{commit}")
    label = git("rev-parse", "--short", sha)
    bins = [(n, git("rev-parse", "--verify", r + "^{commit}"), f) for n, r, f in a.bench_bins]
    resolve = lambda r: git("rev-parse", "--verify", r + "^{commit}")
    then_shas = [then_args(a, t, sha, resolve, 0)[0] for t in a.then]

    # A launch the remote build suite would reject on Clippy is refused here,
    # before an instance is provisioned (2026-10-08: a lint error consumed a
    # launch): the same all-targets Clippy, or the full-scope merge_gate marker
    # of the same tree, which already ran it.
    if not (a.list or a.cleanup):
        # (Not for --list/--cleanup: they launch nothing, and a listing ran a
        # whole Clippy build on the shared machine, 2026-10-08.)
        ok, note = clippy_preflight(ROOT, rev=sha, dry_run=a.dry_run)
        if not ok:
            raise CloudStop(f"prelaunch clippy refused: {note}", 23)
        log(note)
        cancel.check("asking the provider for offers")

    # (Masked: identity lines end up in transcripts and logs.)
    log(f"{a.provider}: {mask_identity(provider.check_account())}")
    limits = cloud_limits(a.provider)

    def admitter_for(market, share):
        return Admitter(provider, a.provider, owner, market, limits, share, a.wait_quota, a.wait_auto, cancel,
                        account_cap=a.max_account_slots)

    if a.list or a.cleanup:
        def summary():
            me = owner or current_owner(required=False)
            view = slot_view(provider)
            with ledger.locked() as rows:
                decision = admit(view, rows, me, a.provider, "spot", limits["spot_instance_quota"],
                                 ledger.share(rows, me, limits["default_share"], a.slots) if me else None,
                                 account_cap=a.max_account_slots)
            log(decision.line() if me else decision.line().split(" (yours")[0])
            log(f"slots by owner: {decision.by_owner()}")
        released = lambda iids: ledger.release_instances(lambda row: row.get("instance") in iids)
        return manage_instances(provider, a, owner, summary=summary, released=released)

    cands = rank_offers(provider.offers(types, a.arch, regions))
    if not cands:
        raise CloudStop(f"cloud_verify: no spot offers for {', '.join(types)} in {', '.join(regions)}")
    best = cands[0]
    for line in setup.offer_lines(cands, provider.currency):
        log(line)
    with ledger.locked() as rows:
        ledger.check(rows, owner, a, best)
        # A coordinator's budget override is also exempt from the share (the account quota still applies).
        share = None if a.budget_override else ledger.share(rows, owner, limits["default_share"], a.slots)
    jobs = a.jobs or max(1, best.vcpus - 1)
    rust, crates = sources(provider, best.region, a.rust_from, a.crates_from)
    plan = setup.Plan(a=a, provider=provider, owner=owner, ledger=ledger, admitter=admitter_for(best.market, share),
                      offers=cands, jobs=jobs, sha=sha, label=label, bins=bins, then_shas=then_shas,
                      resolve=resolve, vargs=verify_args(a, sha, jobs), rust=rust, crates=crates, toolchain=toolchain,
                      proxy=proxy, local_dir=setup.local_dir(a, provider, label), types=types, tlc=verify_runs_tlc(a))
    log(plan.description())
    if a.dry_run:
        setup.dry_run(a, best, provider, plan.admitter, ledger)
        return 0
    return Session(a, plan, cancel, Hooks(launch=launch_with_quota_wait, key=ensure_local_key)).run()


if __name__ == "__main__":
    sys.exit(main())
