"""The remote half of a session: boot the instance, set it up, run the passes.

Every pass of a run -- the bench driver, the TLC oracle passes, verify.py and
each `--then` pass -- runs the same way: a periodic best-effort copy of what
has arrived so far while the pass is running, then one required final copy
whose completion the receipt records. `run_pass` is that one implementation, so
no pass can differ from the others in how it fetches (CODE-23) or in whether a
transfer that never finished can still be reported as success (HARNESS-06).

What a pass runs is the plan's argv (`cloud/setup.py`); this module decides the
order of the passes, their timing and their copies, and nothing else. It reaches
the entrypoint only through `Hooks` (HARNESS-03), never by importing it.
"""
import os
import threading
import time
from typing import TYPE_CHECKING

from cloud import setup
from cloud.allowlist import SshAccess
from cloud.cloud_common import InfraError, Machine, SkipOffer, RESULT_TRANSFER_RETRY_SECS, bench_script, fetch_bench_results, fetch_oracle_results, fetch_results, fmt_secs, log, network_deadline, oracle_script, retry_network, run_remote_verify, setup_remote, terminate_until_gone, warning

if TYPE_CHECKING:
    from cloud.session import Session

# How often a running pass copies what it has produced so far back to this
# machine; a reclaimed spot instance or the dead-man's switch keeps the rest.
PERIODIC_FETCH_SECS = 300


def periodic_fetch(stop, fetch):
    """Copy what a running pass has produced so far every `PERIODIC_FETCH_SECS`,
    until `stop` is set. The copy is best effort: a failed or refused transfer
    is warned about and the loop keeps its cadence, so an outage never ends
    either the pass or the periodic copying, and what already arrived stays on
    this machine (2026-10-08: a final fetch that failed after a DNS outage lost
    a whole run's results)."""
    while not stop.wait(PERIODIC_FETCH_SECS):
        try:
            fetch()
        except Exception as e:  # noqa: BLE001 - a copy never ends the pass
            warning(f"periodic fetch failed (best effort): {type(e).__name__}: {e}")


def release_dead_boot(session: "Session", provider, m):
    """Release an instance that launched but never answered ssh, so the next
    offer can be tried without two instances billing.

    A spot instance that reaches RUNNING on a host whose cloud-init never
    finishes is infrastructure, not a stop condition (2026-11-28: `STOP: ssh
    did not come up` aborted a whole shard after a single offer). The ledger
    reservation is released and the instance leaves `launched_ids` only once
    the provider confirms it is gone; an unconfirmed release keeps both, so the
    session's own leftover check reports it and the run never looks clean over
    a live instance (HARNESS-09, HARNESS-10). The release is a *dead boot*: it
    gives back the grant the launch consumed and charges the row only for the
    time it lived, so the next offer can pass the same budget checks instead of
    the retry dying on exit 25 (`LaunchLedger.release_dead_boot`). Returns True
    when it is gone."""
    try:
        m.terminated = terminate_until_gone(provider, m)
    except Exception as e:  # noqa: BLE001 - reported, never a silent leak
        m.terminated = False
        warning(f"terminate {m.id} failed: {type(e).__name__}: {e}")
    if not m.terminated:
        return False
    if getattr(m, "ledger_time", None):
        session.plan.ledger.release_dead_boot(session.plan.owner, m.ledger_time, m.id)
    session.launched_ids.discard(m.id)
    return True


def boot(session: "Session"):
    """Launch one offer, wait for ssh, and attach the operator-IP allowlist.

    The offers are tried cheapest first. A refusal that is about a whole region
    (no capacity in any zone of it) skips that region's remaining offers;
    anything else goes to the next offer. Every attempt is admitted and
    reserved through the ledger, so a refused launch costs no launch and no
    grant. An instance that launched but never answered ssh is terminated,
    released and replaced by the next offer once: a dead boot must not end the
    shard.
    """
    a, plan = session.a, session.plan
    provider, ledger = plan.provider, plan.ledger
    fresh = session.hooks.key()
    ips = provider.public_ips(plan.proxy)
    if hasattr(provider, "reap"):
        # Leftovers of runs whose local process died (tencent: stopped or past their deadline).
        retry_network(provider.reap, "reap expired leftovers")
    last_err = None
    last_failure = "launch"
    skipped_regions = set()
    boot_retries = 1
    m = None
    for offer in plan.offers:
        if offer.region in skipped_regions:
            continue
        m = Machine(provider, offer, plan.proxy)
        session.machine = m
        session.used_regions.add(offer.region)
        plan.admitter.market = offer.market
        try:
            session.hooks.launch(provider, m, ips, fresh, a, ledger, plan.owner, session.launched_ids,
                                 plan.admitter, session.cancel)
            fresh = False
            # (The dead-man's switch shuts the instance down then at the
            # earliest: remote jobs end before it, see remote_deadline.)
            m.dead_at = m.t_launch + a.max_minutes * 60 if m.t_launch else None
            log(f"launched {m.id} ({offer.itype}, {offer.zone}, {offer.market} {offer.price:.4f} {plan.currency}/h)")
        except SkipOffer as e:
            last_err = str(e)
            if provider.find_launched(m) and provider.terminate(m) and getattr(m, "ledger_time", None):
                ledger.release(plan.owner, m.ledger_time, m.id)
            m = session.machine = None
            warning(f"{e}; trying the next offer")
            if e.scope == "region":
                skipped_regions.add(offer.region)
            continue
        t = time.time()
        try:
            provider.wait_ready(m)
            log(f"running at {m.ip}")
            m.wait_ssh()
        except InfraError as e:
            detail = getattr(e, "message", str(e))
            last_err, last_failure = f"{m.id or 'the instance'} did not answer ssh: {detail}", "boot"
            if not release_dead_boot(session, provider, m):
                # (The machine stays current and in launched_ids: cleanup tries
                # the release again and the leftover check fails the run, so a
                # second offer is never paid for next to a live instance.)
                raise InfraError(f"{last_err}; could not release {m.id}") from e
            if boot_retries == 0:
                raise InfraError(f"{last_err} (no offer left to retry)") from e
            boot_retries -= 1
            warning(f"{last_err}; trying the next offer")
            m = session.machine = None
            continue
        # (Not before: during the boot wait a refused connection is sshd not
        # being up yet, not a stale rule.) The launch wrote the security group
        # for `ips`; from here the machine's transports notice on their own when
        # that address has been left behind, and repair it (cloud/allowlist.py).
        m.access = SshAccess(provider, m, ips)
        if hasattr(provider, "check_deadman"):
            # (An InfraError: the instance is terminated by the session's cleanup.)
            retry_network(lambda: provider.check_deadman(m), f"dead-man's switch check on {m.id}")
        session.phases["boot"] = time.time() - t
        log(f"ssh up {fmt_secs(m.wall())} after the launch")
        return
    # (The wording matters: a dead boot is an infrastructure failure, not a
    # refused launch, and `stop_code` reads the message.)
    raise InfraError(f"could not {last_failure} {', '.join(plan.types)} anywhere (last: {last_err})")


def prepare(session: "Session"):
    """Upload this tree and write the driver script the passes run.

    (Called `prepare` because `setup_remote` is the uploader and `cloud/setup.py`
    is the plan; the module this file imports must keep that name.)

    `setup_remote` records what each of its parts cost in `phases["setup_parts"]`;
    the phase's own duration is recorded even when it raises, so a setup that
    failed late in the run still shows what it had spent.
    """
    a, plan, m = session.a, session.plan, session.machine
    provider = plan.provider
    t = time.time()
    timings = {}
    try:
        setup_remote(m, plan.sha, plan.toolchain, a.arch, plan.rust, plan.crates, timings,
                     bench_refs={n: s for n, s, _ in plan.bins} if a.bench else None,
                     extra_refs={f"then-{i}": s for i, s in enumerate(plan.then_shas, 1) if s != plan.sha},
                     oracle=bool(a.oracle), tlc=plan.tlc)
    finally:
        session.phases["setup"] = time.time() - t
        session.phases["setup_parts"] = {k: round(v) for k, v in timings.items()}
    home = provider.home
    if a.bench:
        o = m.offer
        machine = f"{a.provider} {o.itype} ({o.zone}, {o.market} {o.price:.4f} {provider.currency}/h)"
        # The driver ends the benchmarks `deadline_at` before the dead-man's
        # switch, so their results are complete when the instance goes.
        m.ssh(f"cat > {home}/bench-driver.sh <<'TLX_BENCH_EOF'\n"
              + bench_script(home, a.cc, machine, plan.bins, a.bench,
                             deadline_at=m.dead_at - 300 if m.dead_at else None,
                             skip_head_build=plan.skip_head_build,
                             skip_remote_clippy=plan.skip_remote_clippy)
              + "TLX_BENCH_EOF\n")
        log(f"setup done ({fmt_secs(session.phases['setup'])}); running the benchmarks")
        return
    if a.oracle:
        m.ssh(f"cat > {home}/oracle-driver.sh <<'TLX_ORACLE_EOF'\n{oracle_script(home, a.oracle)}TLX_ORACLE_EOF\n")
    log(f"setup done ({fmt_secs(session.phases['setup'])})")


def run_pass(session: "Session", argv, key, fetch, on_logdir=None):
    """Run one remote pass and copy its results back; return its exit status.

    `fetch(quiet)` performs one copy and returns when it finished; the periodic
    copies are best effort, the final one is required -- an incomplete transfer
    ends the run as an infrastructure failure instead of reporting success over
    a local copy that is known to be incomplete (HARNESS-06). The pass's remote
    runtime is recorded under `key` and the copy under "fetch", so the receipt
    separates the work from the transfer.
    """
    stop = threading.Event()
    copier = threading.Thread(target=periodic_fetch, args=(stop, lambda: fetch(True)), daemon=True)
    started = time.time()
    copier.start()
    try:
        rc, _ = run_remote_verify(session.machine, argv, on_logdir=on_logdir)
    finally:
        stop.set()
        copier.join()
        # Fetch even after a transport error, deadline, or interrupt. A
        # detached pass may already have results; Session cleanup follows us.
        session.phases[key] = time.time() - started
        started = time.time()
        try:
            session.fetched_at = fetch(False)
        except BaseException as error:
            raise InfraError(f"final result fetch failed for instance {session.machine.id}; "
                             f"remote results may be lost: {type(error).__name__}: {error}") from error
        finally:
            session.phases["fetch"] = time.time() - started
    return rc


def _bench_fetcher(m, local_dir):
    def fetch(quiet):
        fetch_bench_results(m, local_dir, quiet=quiet, deadline=network_deadline(m.dead_at, budget=RESULT_TRANSFER_RETRY_SECS))
        return time.time()
    return fetch


def _oracle_fetcher(m, oracle_dir):
    def fetch(quiet):
        fetch_oracle_results(m, oracle_dir, quiet=quiet, deadline=network_deadline(m.dead_at, budget=RESULT_TRANSFER_RETRY_SECS))
        return time.time()
    return fetch


def _results_fetcher(m, local_dir):
    """The copy-back of a verify.py pass, and the hook that learns its remote
    log directory: the periodic copy and the final receipt share one
    destination, so the final copy is an increment of the periodic one and not
    a second destination."""
    holder = {}

    def fetch(quiet):
        fetch_results(m, holder.get("logdir"), local_dir, quiet=quiet, deadline=network_deadline(m.dead_at, budget=RESULT_TRANSFER_RETRY_SECS))
        return time.time()
    return fetch, lambda d: holder.update(logdir=d)


def then_passes(session: "Session", local_dir, rc):
    """The `--then` verify.py passes of a run, whatever its main pass was.

    A bench run's `--then` passes collect the verify.py results the same
    instance can produce afterwards, so one launch covers both.
    """
    a, plan, m = session.a, session.plan, session.machine
    for i, spec in enumerate(a.then, 1):
        _, targs = setup.then_args(a, spec, plan.sha, plan.resolve, plan.jobs)
        log(f"pass then-{i}: {' '.join(targs[2:])}")
        fetch, on_logdir = _results_fetcher(m, os.path.join(local_dir, f"then-{i}"))
        trc = run_pass(session, ["env", f"CC={a.cc}"] + targs, f"then-{i}", fetch, on_logdir=on_logdir)
        session.then_results.append({"args": targs[2:], "exit": trc})
        log(f"pass then-{i}: exit {trc}")
        rc = max(rc, trc)
    return rc


def passes(session: "Session"):
    """Run the plan's passes in order and keep the worst exit status.

    Every pass's results are copied back while it runs and once at the end; the
    final copy of the last pass sets the receipt's `fetched_at` cutoff, so a
    partial local copy says up to when it is complete (HARNESS-06).
    """
    a, plan, m, local_dir = session.a, session.plan, session.machine, session.plan.local_dir
    home = plan.provider.home
    if a.bench:
        rc = run_pass(session, ["bash", f"{home}/bench-driver.sh"], "bench", _bench_fetcher(m, local_dir))
    else:
        rc = 0
        if a.oracle:
            oracle_dir = os.path.join(local_dir, "oracle")
            rc = run_pass(session, ["bash", f"{home}/oracle-driver.sh"], "oracle", _oracle_fetcher(m, oracle_dir))
            log(f"oracle passes: exit {rc}; TLC results in {oracle_dir}")
        if not a.oracle or a.suites:
            log("running verify")
            fetch, on_logdir = _results_fetcher(m, local_dir)
            rc = max(rc, run_pass(session, ["env", f"CC={a.cc}"] + plan.vargs, "verify", fetch, on_logdir=on_logdir))
    rc = then_passes(session, local_dir, rc)
    session.rc = rc
    log(f"results in {local_dir}")
