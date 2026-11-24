# Cloud verification

`scripts/cloud_verify.py` runs this tree's verification and benchmark tiers on a rented machine; the
provider modules behind it own identity, offers, launch, release and cleanup. This document owns
where work runs ([section 1](#1-what-runs-on-a-cloud-instance)), the launcher's commands and modes,
the launch admission rules and budgets, and the operator-facing safety rules. The benchmark commands
themselves are owned by [benchmarking.md](benchmarking.md).

## 1. What runs on a cloud instance

CPU-heavy verification, large-model TLC/tlx runs, corpus-wide runs and benchmarks of record run on
cloud instances; local builds, unit tests, short differential runs and reduced configurations stay on
the workstation. That workstation is shared by several agents, so it is never loaded artificially: a
measurement that needs a quiet machine, or an oversubscribed one, is a cloud measurement, and a local
run that would create load is refused rather than allowed because the machine happens to look idle
([HARNESS-20](development-standards.md#harness-20)). Scripts that take `-j` run with `-j 3`.

The drivers enforce that budget themselves. Every Python driver launches TLC through
`tlxlib.run_proc`, which supplies a heap limit and holds one of two file-lock slots in the worktree's
private git directory until the JVM exits, including timeout and error cleanup; a third local JVM
waits for a slot. External configurations marked medium/large/huge, the benchmark large set (TLC or
manifest time at least 15 s), and the benchmark scaling and stress configurations are rejected
locally - matching uses the spec and configuration together, so a reduced configuration of the same
spec stays available. `scripts/tlc.py SPEC.tla --allow-local-heavy ...` is the explicit escape hatch;
it retains the heap and concurrency limits. `bench.py --hog N`, which keeps N spinning processes
alive to measure an oversubscribed machine, is a cloud measurement too: creating that load on the
shared machine is prohibited, and `scripts/bench.py` refuses a local `--hog` run. Cloud drivers set
the remote host marker; heap limits still apply, while the cloud may run heavier models and more
concurrent JVMs. See [configuration.md](configuration.md) for the heap override and remote host
marker.

Cloud verification is also the Linux portability check, and `--bench` runs `bench.py` there for
records on a quiet machine. The launcher pushes the revision with git, uploads the parts of
`third_party/` and `corpus/out/` the tests read (the TLC oracle is cached, so remote runs need no
Java), installs the pinned Rust toolchain, runs this tree's `verify.py -j <vCPUs-1>` with the output
streamed back, and copies results (`summary.json`, logs, `cloud.json` with instance type, price and
phase times) to `target/verify/<time>-<rev>-<provider>/`. The exit code is `verify.py`'s (0/1), or one
of the stop codes below. Provider modules (`scripts/cloud_*.py`) implement identity check, offer
selection, launch with a dead-man switch, release and listing. The system disk is sized per provider
(Tencent 512 GB, raised from 200 GB after two large models filled it: TLC's default fingerprint set
spills to disk, so a huge model's own state queue can outgrow the disk; Aliyun/AWS 40 GB), and
`--disk-gb N` overrides it for a model that needs more.

## 2. Local identity configuration

The scripts refuse to run unless the cloud CLI's caller identity equals the one configured in
`~/.config/tlx/cloud.json` (or the file named by `TLX_CLOUD_CONFIG`). The file is never committed.
It has one entry per provider; if it or an entry is missing, the script (also with `--dry-run`
and `--list`) stops and prints the fields to create (`CONFIG_FIELDS` in `scripts/cloud/cloud_common.py`).
Use a dedicated, least-privilege CLI profile for it. Two optional fields of an entry feed the launch
admission (below): `spot_instance_quota`, the account's spot instance quota as the provider set it
(e.g. `"spot_instance_quota": 10` for Tencent), and `default_share`, how many instances an owner
may run at the same time without a grant that says more (default 1). Every identity line the
scripts print is masked (`***` plus the last three digits of each account or user number).

## 3. Commands

```sh
python3 scripts/cloud_verify.py --dry-run                       # identity, stock, price, image, network; creates nothing
python3 scripts/cloud_verify.py [REV] --quick                   # default provider, 16 vCPU
python3 scripts/cloud_verify.py [REV] --full --instance-type T --allow-big  # larger instance for the full tier
python3 scripts/cloud_verify.py --provider P --list             # tagged instances, and the account's slots by owner
python3 scripts/cloud_verify.py --provider P --list --mine      # exit 1 if an owned instance is still active
python3 scripts/cloud_verify.py --provider P --cleanup --mine   # terminate only this branch
python3 scripts/cloud_verify.py --provider P --cleanup --all    # explicitly terminate every owner
python3 scripts/cloud_verify.py --cancel                        # stop this worktree's running launch before its launch call
python3 scripts/verify_compare.py target/verify/<local> target/verify/<remote>   # tlx results identical across platforms?
python3 scripts/tests/test_cloud_verify.py                            # logic tests, no cloud API calls
```

`--provider` (see `--help` for the available ones), `--arch arm64|x86_64`, `--region`,
`--instance-type`, `--max-minutes` (must cover all passes; spot instances can be reclaimed, so
split long benchmarks) and `--env K=V` (forwarded to the remote `verify.py`) are the main options.
`--disk-gb N` sizes the system disk (Tencent's default is sized for the corpus, see
section 1); TLC's disk-backed state queue is unbounded on a large model, so a run that dies with
`No space left on device` wants a larger disk there.
`--fuzz-minutes M` is forwarded to `verify.py` (the `fuzz-campaign` suite's duration); a pass that
runs a fuzz suite (`fuzz-campaign`, or `fuzz` in the full tier) gets Java and the TLC jars installed
as in benchmark mode ([testing.md](testing.md) section 7.1).
`--then "[REV] <verify.py args>"` (repeatable) runs further `verify.py` passes on the same
instance, with results in `then-<N>/`; use it to combine environment variants or an older revision
as a same-machine timing baseline in one launch. A `--bench` run takes `--then` passes too: the
benchmark commands run first and the verify.py passes follow them on the same instance, so one
launch produces both (`--suites` and `--oracle` write the *main* pass, and stay refused with
`--bench`):

```sh
S=build,spectest-compile,corpus-compile
python3 scripts/cloud_verify.py HEAD --full --allow-big --suites $S --env TLX_PRERUN=1 \
    --then "--suites $S --env TLX_JIT=0" --max-minutes 60
```

Oracle mode: `--oracle "<corpus.py args>"` (repeatable) runs `scripts/corpus.py` remotely before
`verify.py`, all passes at the same time (share the CPUs out with `-j` and `--tlc-workers`), with
Java and the TLC jars installed as in benchmark mode; the instance's `corpus/out/tlc*.json` come
back to `oracle/` under the result directory (also after a failure; copy them into `corpus/out/`
by hand). `verify.py` follows only with `--suites`, then with the fresh oracles:

```sh
python3 scripts/cloud_verify.py --provider tencent --full --allow-big --instance-type SA5.8XLARGE64 \
    --oracle "tlc --source external --tier medium -j 8 --timeout 3300 --only-failed" \
    --oracle "tlc --source external --tier large -j 3 --tlc-workers 8 --timeout 3300" \
    --suites corpus-ext,corpus-ext-large --max-minutes 60
```

Benchmark mode: `--bench "<bench.py args>"` (repeatable) runs `scripts/bench.py` remotely instead
of `verify.py` (Java is installed and `tla2tools.jar` and the community modules jar are uploaded;
the uploaded `bench-tlc.json`, measured elsewhere, is removed); `--bench-bin NAME=REV[:FEATURES]`
builds another revision (optionally with tlx-cli cargo features) into
`target/bench-bins/NAME/tlx` for `bench.py ab`. Output (`bench/` contents, `bench.out`) comes back
to `target/bench/<time>-<rev>-<provider>/`; copy files you want to commit into `bench/`.

```sh
python3 scripts/cloud_verify.py --bench "tlcbase --missing --collect --workers 1,16 --no-large" --bench "run --tlc --repeat 3" --max-minutes 60
python3 scripts/cloud_verify.py --bench-bin nostats=HEAD:no-stats --bench-bin base=<rev> \
    --bench "ab --bin main=target/release/tlx --bin nostats=target/bench-bins/nostats/tlx --models X,Y --repeat 10 --out bench/ab.json"
```

## 4. Benchmark preflight and deadlines

Before a bench launch, the requested command is parsed locally and its measurement path
is smoke-tested on tiny scratch, external-path and simulation fixtures (10 seconds per
fixture, 60 seconds per command). A smoke failure refuses the launch. This needs a
current local release binary (`cargo build --release`); it does not collect timing
baselines or write benchmark records.

`bench.py run`, `ab`, `disk`, `profile`, `suite` and `track` accept `--deadline-min M`
for a total measurement budget, including warmups, repeated samples and variants.
Cloud benchmark commands also share the instance deadline, five minutes before its
dead-man switch. A previous sample or manifest estimate determines whether the next
pass fits; a known cost (a measurement of that key here, else the caller's estimate)
reserves no more than the enforced sample timeout, while a key whose cost is not
known yet reserves only what it can still consume in the remaining budget and runs
with its timeout capped there. Child timeouts
are capped by the remaining budget. Skipped passes are recorded as incomplete and
produce a nonzero result. Suite samples print the model, variant, round and elapsed
seconds and atomically checkpoint after every run, preserving completed samples when
a later sample times out or cannot fit. Partial entries are marked skipped.

## 5. Mechanical guards and stop codes

Each instance carries its launching git branch as an owner tag (`tlx-owner` on Tencent/AWS,
`Owner` on Aliyun). Values use a portable character set, with a hash suffix when sanitizing or
truncating would otherwise collide. `--list --mine` queries only that owner and exits 1 while
any owned instance is active, including stopped instances that still incur charges; terminating
or terminated instances pass. `--cleanup --mine` and Tencent's automatic expired-instance
reaper never touch another owner. Cleanup across owners requires `--cleanup --all`; plain
`--list` still shows every tagged instance. Untagged legacy instances require explicit cleanup
across owners.

A locked `tlx-cloud-ledger.json` in git's common directory shares launch records across
worktrees. An owner gets two launches in a rolling 12-hour window, at most 60 minutes each
(default 60), with an estimated total compute cost of at most 5 CNY for Tencent/Aliyun.
Network traffic charges are not included. The dry run prints remaining launches.
Reservations survive interruption and count conservatively when the API outcome is unknown;
a launch the provider refused (quota, risk, permission, capacity), one the local admission
refused, one that never reached the provider's launch call and a cancelled one consume neither a
launch, a grant nor cost budget; their rows stay in the ledger as evidence.

Launch admission. Before the launch call, and atomically with the ledger reservation, the run
counts the account's instances: the provider's listing of every instance in all its regions
(Tencent: tagged or not, pending and terminating ones included), plus the ledger's reservations
in flight and instances launched after the listing, minus instances their run has recorded as
released. It prints `N of M account spot slots in use (yours K, share S)` and refuses locally,
without a provider call, when the owner already runs its share (exit 25) or, for a spot launch,
the account's spot instances are at the cap (exit 20; the message names the owners holding the
slots and which cap applies). That cap is the cloud config's `spot_instance_quota`, or the smaller
of it and `--max-account-slots N` - the launcher's own cap on the account, which a wave of
concurrent launchers honours together because the listing each of them reads is account-wide. The
share is `default_share`, or the largest `--slots` of the owner's grants in the 12-hour
window; a maintainer `--budget-override` is exempt from the share, not from the cap. Tencent's
own spot limits are not one account-wide number (2026-10-08: with 7 instances running, ap-shanghai
refused one more with `LimitExceeded.UserSpotQuota` while ap-guangzhou accepted two more and refused a
third with `LimitExceeded.SpotQuota`), so the Tencent provider also sends the exact request as a
`RunInstances` dry run immediately before the real call. A spot-quota answer there
(`LimitExceeded.UserSpotQuota` / `LimitExceeded.SpotQuota`) is zone-scoped, so the launch then tries
the region's other zones with the same instance type and market, logging each step (`zone
ap-shanghai-5: quota refused; trying ap-shanghai-8 (same region/type)`); every other `LimitExceeded`
code stays account-wide and stops at once. Only when every zone of the region refuses is it a quota
stop (exit 20, the message names the zones) and nothing was created. `--list` and `--dry-run` print
the same count and the slots by owner.

Quota refusals stop the run (exit 20) unless `--wait-quota MINUTES|auto` is given: a local
refusal is then re-checked with read-only listings after 1, 2 and then every 4 minutes, and a
provider refusal with read-only dry runs of the same region, instance type and zones after 2, 4 and
then 8 minutes, up to the wait; the same offer is then launched once. `auto` waits until the earliest
recorded dead-man's switch of an instance in the way plus two minutes (at most 180 minutes, 60 when
no deadline is known). Every refusal is logged; probes spend no launch. Risk, permission and other
refusals stop at once, and nothing switches region, instance type or provider to get around a
limit - a zone-scoped spot-quota refusal may only move to another zone of the same region with the
same type and market: the ledger forbids another region for an hour after a provider quota refusal.

Cancel: SIGINT, SIGTERM and SIGHUP are handled from the start of a run (also during the local
preflights, which a background run would otherwise not see with an inherited ignored SIGINT), and
`cloud_verify.py --cancel` in the same worktree writes a cancel file in its git directory that a
running invocation reads. The run checks the flag after the preflights, while waiting for a slot
and immediately before the provider's launch call; a cancel there launches nothing. Records include owner, time, instance,
type, duration and estimated compute cost. More than 16 vCPU requires `--full` or `--bench`
with `--allow-big`. A maintainer in the main worktree may use `--budget-override REASON`;
The maintainer can give a linked-worktree branch one more launch in the 12-hour window with `scripts/cloud_verify.py --grant OWNER --minutes M [--slots N] [--reason TEXT]` (main checkout only, 1–720 minutes, default 60; above 180 minutes `--reason` is required and must name the heavy job the lane is for, for a named heavy job while retaining the spot-only policy - such a grant prints the spot-reclaim advisory; a lane that long usually also needs `--budget-cny`, since the estimate grows with the minutes; `--slots`, 1–16, raises the owner's share of concurrent instances for the window; `--budget-cny X`, 0–30, raises the owner's 12-hour estimated-spend cap of 5 CNY by X for the window, consumed or not). That worktree can then launch once with `--max-minutes` up to M from its own worktree without a budget override. The shared ledger records the grant and consumes it at launch reservation; a refused, cancelled or never-sent launch gives it back, and dry runs do not consume it. Grants expire after 12 hours and retain cost, capacity and quota checks; an optional `--budget-override REASON` records the maintainer’s reason when issuing one.
the nonempty reason is recorded, and linked worktrees reject the option.

Advisories start with `WARNING (not a stop condition):`; in particular, an unavailable CAM
self-termination role permits shutdown fallback. Fatal conditions start with `STOP:` and stop
without trying another offer:

| Exit | Condition |
|---|---|
| 3 | Infrastructure failure, interruption or incomplete cleanup |
| 20 | Provider quota exceeded (for a spot request: every zone of the region refused) |
| 21 | Risk control or blocked account |
| 22 | Forbidden operation or missing permission |
| 23 | Launch refused, unavailable offers or exhausted capacity choices |
| 24 | Missing/invalid identity configuration, credentials or account mismatch |
| 25 | Ownership, budget or unsafe cleanup request refused |

What a run may do locally - the two TLC JVM slots, the rejected heavy configurations and their
reduced counterparts, the `--allow-local-heavy` escape hatch, the `--hog` prohibition and the
remote host marker - is owned by [section 1](#1-what-runs-on-a-cloud-instance) and enforced by
the drivers, not by this launcher.

## 6. The operator's ssh allowlist

Every instance's ssh security group (`tlx-verify-ssh`) allows tcp 22, 443 and 2222 from this
machine's public address **as it is when the instance is created**, and nothing used to re-check
it afterwards. It is the operator's egress address that moves on its own (the ISP moved it
`1.202.18.10 -> 61.149.241.75` on 2026-10-08), and a rule that no longer matches looks exactly like
a dead instance to ssh, rsync and git-over-ssh: each transport spends its whole retry budget and
the run ends in a bare exit 3 (infrastructure failure) while the instance, and the job running on
it, are healthy. Two verification waves were lost that way.

`Machine.run` routes every transport of a run through `cloud/allowlist.py` (attached once the
instance has answered ssh for the first time - before that, a refused connection is just sshd not
being up yet), so a failure of a command that reaches the instance over ssh is classified before
the retry budget is spent on it:

- the instance is **gone or stopped** at the provider: the run says so and hands the failure back -
  nothing is re-applied, and no retry is spent against a dead host;
- the instance is **running**: the allowlist may have changed, or the network may be down. The
  tool prints the current and last-written operator addresses and a manual repair command, adds
  the current address to the shared group, waits five seconds for propagation, and re-runs the
  failed step. A running provider state is not proof of SSH reachability;
- the instance's state cannot be read: nothing is changed on a guess, and the command that would
  fix it is printed instead.

Visible setup commands retain stderr for diagnosis too. Each idempotent setup/upload step gets
at most four attempts within a ten-minute network budget, capped before the dead-man's switch's
120-second cleanup reserve. The log names the step, the transport error and each actual re-run;
a final STOP includes the last provider state, step attempts and repairs. A detached benchmark or
verification start carries a per-pass token and a remote lock: retrying a start whose SSH response
was lost never starts the pass twice or erases its results. Stream reconnects and required final
result copies tolerate an hour of transport outage, still capped by the cleanup reserve. In the
worst case a result transfer waits up to 60 minutes, and that time counts against the instance's
`--max-minutes`; budget the launch accordingly. Output-stream reconnects carry no fixed attempt
cap: while the remote `verify.rc` exit file is absent and the provider does not report the
instance `gone` or `stopped`, `run_remote_verify` reconnects every five seconds until five
minutes before the dead-man's switch (or the one-hour transfer window when no switch deadline is
set), reserving the remaining margin for the final result fetch.

Provider diagnosis/repair requests and the repair-lock wait share a monotonic deadline. CLI,
public-IP HTTP and AWS SDK requests use the remaining time; a repair is skipped when less
than another 120 seconds remain beyond the network deadline's cleanup reserve.

Provider diagnosis/repair calls share a thread-safe budget of three rounds per fifteen-minute
window per instance. Each round reads state and the operator address and may add missing rules;
parallel setup and result-copy threads cannot overspend that budget. A later outage gets a fresh
window. A failed permission check is reported, never retried by changing identity or region.

The group is **shared by every owner on this machine**. Owner descriptions (`cloud_verify:<owner>`)
record who wrote a rule, not who uses it: a later launch can borrow the same address without adding
a duplicate rule. Consequently both launch reconciliation and transport recovery are **add only**,
even for rules bearing the current owner's tag. Neither path deletes rules or replaces the whole
policy set. A launch logs observed ingress rules, planned additions and the provider's documented
default limit ([Tencent: 100 ingress](https://cloud.tencent.com/document/product/213/43699),
[Aliyun: 200 total](https://www.alibabacloud.com/help/id/ecs/api-authorizesecuritygroup),
[AWS: 60 ingress](https://docs.aws.amazon.com/vpc/latest/userguide/amazon-vpc-limits.html); account quota
increases may raise these limits). World-open rules are warned about and never written by this tool.

To reclaim accumulated rules, the maintainer may run:

```sh
python3 scripts/cloud_verify.py --provider tencent --cleanup --prune-sg
```

This operation never terminates instances. It is refused outside the main checkout, while **any
project-tagged instance exists anywhere in that provider account**, or while recent launch ledger
entries might still be hidden by listing lag. The zero-instance check and prune hold the same
common-git ledger lock as launches. Only rules carrying a nonempty `cloud_verify:<owner>` tag are
removed; ownerless legacy rules and manual rules stay. Tencent deletion includes the policy
version to refuse stale positional indexes; Aliyun and AWS delete by stable rule IDs. Prune defaults
to all configured regions; `--region` narrows deletion, never the account-wide idle check. Use it
alone with `--cleanup`, without `--mine`, `--all`, `--list`, `--dry-run` or `--grant`.

These guards cover launches from this repository's common-git ledger. External tools and older
already-running launchers do not acquire new guards retroactively; update launchers before starting
new campaigns. Normal `--list` and `--cleanup --mine` still manage instances by branch ownership.

## 7. Safety rules

Instances are billed per second, so every launch follows these rules:

- Always `--dry-run` first; on a new environment run one small `--quick` instance and confirm it
  is released before using a large one.
- Every instance has a dead-man switch (a scheduled provider-side release or in-instance
  termination, plus `shutdown`), is tagged with project and owner so that `--list`/`--cleanup` find it, and is released
  in a `finally` block on errors, Ctrl-C and SIGTERM. `--keep-instance` is for debugging only.
- Stop at once on risk-control, permission or credential errors. Quota waiting is allowed only
  through the same-offer dry-run backoff described above; do not switch region to
  work around them.
- Child processes run without proxy and cloud credential variables, so the source address and
  identity are stable. That address is what the instance's ssh rule is written for, and it can
  change under a running run: the transports diagnose and repair it themselves, add only, and
  never touch another owner's security group or another owner's rules (see "The operator's ssh
  allowlist" above).
- A run ends by printing instance type, zone, spot price, duration and estimated cost (also in
  `cloud.json`).
