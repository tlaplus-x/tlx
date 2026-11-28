"""Launch admission, refusals that cost nothing, cancel checkpoints and masked
identities of scripts/cloud_verify.py (incidents of 2026-10-08): provider and API
doubles, a temporary ledger, an injected clock; no network, no real waiting.

Each guard is first triggered with the known-bad case of its incident (the
account's spot quota full, a refused launch, a cancel after the preflight),
then checked with a valid control.

usage: python3 -m unittest discover -s scripts -p test_cloud_admission.py
"""
import contextlib, io, json, os, signal, sys, tempfile, time, unittest
from unittest import mock

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from cloud import cloud_common
from cloud import cloud_tencent
from cloud import remote as cloud_remote
import cloud_verify as cv
import testkit
from cloud.cloud_common import CloudStop, Offer, SkipOffer, SlotHolder

FAKE_CONFIG = {"tencent": {"arn": "qcs::cam:100000000001:uin/100000000002", "profile": "tlx-test",
                           "selfterm_role": "tlx-verify-selfterm", "spot_instance_quota": 3}}
OFFER = Offer(0.16, "ap-shanghai", "ap-shanghai-5", "SA5.4XLARGE32", 16)
OFFER2 = Offer(0.17, "ap-shanghai", "ap-shanghai-8", "SA5.4XLARGE32", 16)
PRICEY = Offer(3.0, "ap-shanghai", "ap-shanghai-5", "SA5.4XLARGE32", 16)
PRICEY_NEXT = Offer(3.1, "ap-shanghai", "ap-shanghai-8", "SA5.4XLARGE32", 16)


def holders(*owners, state="RUNNING", market="spot"):
    return [SlotHolder("ap-shanghai", f"ins-{owner}-{i}", state, owner, market) for i, owner in enumerate(owners)]


class FakeProvider:
    """A provider double whose launch calls the checkpoint (as the Tencent and
    Aliyun providers do) and records each RunInstances it would send."""
    calls_checkpoint = True
    all_regions = ["ap-shanghai"]
    min_lifetime_minutes = 7
    default_regions = ["ap-shanghai"]
    default_ssh_proxy = "none"

    def default_types(self, arch, tier):
        return [OFFER.itype]

    def __init__(self, views=None, refuse=None, before_run=None):
        self.views, self.refuse, self.before_run = list(views or []), refuse, before_run
        self.run_instances, self.listings, self.dry_runs, self.owner = [], 0, 0, "worker"

    def checkpoint(self):
        pass

    def slot_holders(self, regions):
        self.listings += 1
        return self.views.pop(0) if len(self.views) > 1 else self.views[0]

    def launch(self, m, ips, fresh, minutes, arch):
        if self.before_run:
            self.before_run()
        m.token = "tok"
        self.checkpoint()
        self.run_instances.append(m.offer)
        if self.refuse:
            raise self.refuse
        m.id = "ins-new"

    def find_launched(self, m):
        return getattr(m, "id", None)

    def describe_plan(self, offer, arch):
        self.dry_runs += 1
        return ["RunInstances DryRun: would succeed"]


class Machine:
    def __init__(self, offer=OFFER):
        self.offer, self.id, self.token = offer, None, None


class DeadBootProvider(FakeProvider):
    """Every offer launches a new instance; the `dead` ones reach RUNNING but
    never answer ssh, as when a spot boot's cloud-init hangs."""

    def __init__(self, *args, dead=("ins-1",), **kwargs):
        super().__init__(*args, **kwargs)
        self.dead = set(dead)
        self.terminated = []

    def launch(self, m, ips, fresh, minutes, arch):
        self.run_instances.append(m.offer)
        self.checkpoint()
        m.id = f"ins-{len(self.run_instances)}"

    def wait_ready(self, m):
        if m.id in self.dead:
            raise cloud_common.InfraError("ssh did not come up (ports 22, 443, 2222)")
        m.ip = "192.0.2.1"

    def terminate(self, m):
        self.terminated.append(m.id)
        return True


class LedgerCase(testkit.GuardedTestCase):
    def setUp(self):
        # run_checked's cleanup ignores SIGINT/SIGTERM/SIGHUP (run() restores them); a
        # test that calls it directly must restore them too, or every later child
        # process inherits an ignored SIGTERM (test_tlxlib's timeout then sees SIGKILL).
        for sig in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
            self.addCleanup(signal.signal, sig, signal.getsignal(sig))
        d = tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        self.dir = d.name
        self.ledger = cv.LaunchLedger(os.path.join(d.name, "ledger.json"))
        # Grant fixtures use known branch identities, without spending launches.
        import subprocess
        repo = os.path.join(d.name, "repo")
        subprocess.run(["git", "init", "-qb", "worker", repo], check=True)
        subprocess.run(["git", "-C", repo, "-c", "user.email=fixture@example.com",
                        "-c", "user.name=Fixture", "commit", "--allow-empty", "-qm", "Initial"], check=True)
        for branch in ("other", "x"):
            subprocess.run(["git", "-C", repo, "branch", branch], check=True)
        original_git = cv.git
        def fixture_git(*args, **kwargs):
            if args[0] == "check-ref-format" or any(str(arg).startswith("refs/heads/") for arg in args):
                kwargs["cwd"] = repo
            return original_git(*args, **kwargs)
        owner_git = mock.patch.object(cv, "git", side_effect=fixture_git)
        owner_git.start()
        self.addCleanup(owner_git.stop)
        quiet = mock.patch.object(cv, "log")
        quiet.start()
        self.addCleanup(quiet.stop)
        warn = mock.patch.object(cv, "warning")
        warn.start()
        self.addCleanup(warn.stop)

    def rows(self):
        with self.ledger.locked() as rows:
            return rows

    def args(self, *argv):
        a = cv.parse_args(["--provider", "tencent", *argv])
        a.arch = "x86_64"
        return a

    def admitter(self, provider, share=1, quota=3, wait="0", clock=None, cancel=None):
        a = self.args("--wait-quota", wait)
        clock = clock or testkit.FakeClock()
        return cv.Admitter(provider, "tencent", "worker", "spot", {"spot_instance_quota": quota}, share,
                           a.wait_quota, a.wait_auto, cancel, monotonic=clock, sleep=clock.sleep,
                           view=lambda: (cv.slot_view(provider)[0], time.time())), a, clock

    def launch(self, provider, admitter, a, cancel=None):
        return cv.launch_with_quota_wait(provider, Machine(), [], False, a, self.ledger, "worker", set(), admitter, cancel)


class Counting(LedgerCase):
    def test_the_count_is_the_providers_view_plus_launches_it_cannot_show_yet(self):
        now = time.time()
        listed = holders("a", "b") + holders("(untagged)") + holders("c", state="TERMINATING") \
            + holders("d", market="on-demand")
        rows = [
            {"owner": "e", "time": now - 30, "instance": None, "provider": "tencent", "status": "reserved", "max_minutes": 60},
            {"owner": "f", "time": now - 2 * cv.IN_FLIGHT_SECS, "instance": None, "provider": "tencent", "status": "reserved"},
            {"owner": "g", "time": now - 5, "instance": "ins-g", "provider": "tencent", "status": "launched"},
            {"owner": "h", "time": now - 3600, "instance": "ins-gone", "provider": "tencent", "status": "launched"},
            {"owner": "i", "time": now - 5, "instance": "ins-i", "provider": "tencent", "status": "launched", "released": now},
            {"owner": "j", "time": now - 5, "instance": None, "provider": "tencent", "status": "refused", "code": 20},
            {"owner": "k", "time": now - 5, "instance": None, "provider": "aliyun", "status": "reserved"},
            {"owner": "a", "time": now - 600, "instance": "ins-a-0", "provider": "tencent", "status": "launched", "max_minutes": 60},
        ]
        d = cv.admit((listed, now), rows, "a", "tencent", "spot", 10, 2, now=now)
        # a, b, untagged, c (terminating still holds quota), e (in flight), g (launched after the listing);
        # not: on-demand d, f (stale reservation), h (gone from the listing), i (released), j, k.
        self.assertEqual(d.in_use, 6)
        self.assertEqual(d.yours, 1)
        self.assertEqual(d.line(), "6 of 10 account spot slots in use (yours 1, share 2)")
        self.assertTrue(d.ok)
        self.assertEqual(listed[0].deadline, now - 600 + 3600)   # the ledger's dead-man deadline joins the listing
        self.assertIn("(untagged) 1", d.by_owner())

    def test_terminating_instances_hold_quota_but_not_the_owners_share(self):
        d = cv.admit((holders("w", state="TERMINATING"), time.time()), [], "w", "tencent", "spot", 10, 1)
        self.assertEqual((d.in_use, d.yours, d.ok), (1, 0, True))

    def test_tencent_lists_every_instance_of_the_account(self):
        insts = [
            {"InstanceId": "ins-1", "InstanceState": "RUNNING", "InstanceChargeType": "SPOTPAID",
             "Tags": [{"Key": "tlx-project", "Value": "tlx"}, {"Key": "tlx-owner", "Value": "kylezh/x"},
                      {"Key": "tlx-deadline", "Value": "20261008T1344Z"}]},
            {"InstanceId": "ins-2", "InstanceState": "PENDING", "InstanceChargeType": "SPOTPAID", "Tags": []},
            {"InstanceId": "ins-3", "InstanceState": "RUNNING", "InstanceChargeType": "POSTPAID_BY_HOUR",
             "Tags": [{"Key": "tlx-project", "Value": "tlx"}]},
        ]
        calls = []

        def tccli(product, api, region=None, **params):
            calls.append((api, region, params))
            return {"InstanceSet": insts, "TotalCount": 3}
        with mock.patch.dict(os.environ, {cloud_common.CONFIG_ENV: self.config()}), \
             mock.patch.object(cloud_tencent, "tccli", tccli):
            out = cloud_tencent.TencentProvider().slot_holders(["ap-shanghai"])
        self.assertNotIn("Filters", calls[0][2])   # untagged instances hold quota too
        self.assertEqual([(h.id, h.owner, h.market, h.state) for h in out],
                         [("ins-1", "kylezh/x", "spot", "RUNNING"), ("ins-2", "(untagged)", "spot", "PENDING"),
                          ("ins-3", "(no owner)", "on-demand", "RUNNING")])
        self.assertEqual(time.strftime("%Y%m%dT%H%MZ", time.gmtime(out[0].deadline)), "20261008T1344Z")
        self.assertIsNone(out[1].deadline)

    def config(self, **extra):
        cfg = json.loads(json.dumps(FAKE_CONFIG))
        cfg["tencent"].update(extra)
        path = os.path.join(self.dir, "cloud.json")
        with open(path, "w") as f:
            json.dump(cfg, f)
        return path

    def test_limits_come_from_the_cloud_config(self):
        with mock.patch.dict(os.environ, {cloud_common.CONFIG_ENV: self.config()}):
            self.assertEqual(cloud_common.cloud_limits("tencent"), {"spot_instance_quota": 3, "default_share": 1})
            self.assertEqual(cloud_common.cloud_limits("aliyun"), {"spot_instance_quota": None, "default_share": 1})
        with mock.patch.dict(os.environ, {cloud_common.CONFIG_ENV: self.config(default_share=2)}):
            self.assertEqual(cloud_common.cloud_limits("tencent")["default_share"], 2)
        for bad in (0, -1, "10", True, 1.5):
            with mock.patch.dict(os.environ, {cloud_common.CONFIG_ENV: self.config(spot_instance_quota=bad)}), \
                 self.assertRaises(cloud_common.AccountError):
                cloud_common.cloud_limits("tencent")


class QuotaAdmission(LedgerCase):
    def test_known_bad_full_account_is_refused_locally_without_a_provider_call(self):
        provider = FakeProvider([holders("a", "b", "c")])
        admitter, a, _ = self.admitter(provider)
        with self.assertRaises(cv.AdmissionRefused) as raised:
            self.launch(provider, admitter, a)
        self.assertEqual(raised.exception.code, 20)
        self.assertIn("3 of 3 account spot slots in use (yours 0, share 1)", str(raised.exception))
        self.assertIn("never switch region", str(raised.exception))
        self.assertEqual(provider.run_instances, [])
        self.assertEqual(provider.dry_runs, 0)
        [row] = self.rows()
        self.assertEqual((row["status"], row["code"], row["local"], row["admission"]["in_use"]), ("refused", 20, True, 3))
        self.assertEqual(self.ledger.recent_launches("worker"), 0)

    def test_the_launch_line_reports_recent_launches_and_remaining_cny_budget(self):
        self.ledger.grant("worker", "r", minutes=60, budget_cny=5)
        with self.ledger.locked() as rows:
            rows.append({"owner": "worker", "time": time.time(), "instance": "ins-1", "status": "launched",
                         "provider": "tencent", "estimated_cost": 1.25})
            self.ledger.write(rows)
        with self.ledger.locked() as rows:
            self.assertEqual(self.ledger.recent_launches("worker", rows), 1)
            self.assertEqual(self.ledger.launch_report("worker", rows),
                             "owner worker: 1 launch(es) in 12 h; "
                             "8.75 of 10 CNY estimated budget remaining "
                             "(5 CNY base + 5 CNY from grants, 1.25 CNY used)")

    def test_known_bad_the_launchers_own_cap_refuses_a_launch_the_quota_admits(self):
        # 2026-10-10: `--max-account-slots N` is the launcher's own cap on the
        # account (a wave of launchers of one account stops together at N, the
        # listing being account-wide), where the hand-built slot gate used to be
        # the only way to hold a wave under a number the cloud config did not
        # carry. Here the config allows 10 and the launcher allows 3.
        provider = FakeProvider([holders("a", "b", "c")])
        a = self.args("--max-account-slots", "3")
        admitter = cv.Admitter(provider, "tencent", "worker", "spot", {"spot_instance_quota": 10}, 1,
                               a.wait_quota, a.wait_auto, None, account_cap=a.max_account_slots,
                               view=lambda: (cv.slot_view(provider)[0], time.time()))
        with self.assertRaises(cv.AdmissionRefused) as raised:
            self.launch(provider, admitter, a)
        self.assertEqual(raised.exception.code, 20)
        self.assertIn("3 of 3 account spot slots in use", str(raised.exception))
        self.assertIn("the cap is 3 from --max-account-slots", str(raised.exception))
        self.assertEqual(provider.run_instances, [])       # refused locally, no provider call
        self.assertEqual(self.rows()[-1]["status"], "refused")

    def test_control_one_below_the_cap_launches(self):
        provider = FakeProvider([holders("a", "b")])
        a = self.args("--max-account-slots", "3")
        admitter = cv.Admitter(provider, "tencent", "worker", "spot", {"spot_instance_quota": 10}, 1,
                               a.wait_quota, a.wait_auto, None, account_cap=a.max_account_slots,
                               view=lambda: (cv.slot_view(provider)[0], time.time()))
        self.assertEqual(self.launch(provider, admitter, a)["status"], "launched")

    def test_the_account_cap_is_the_smaller_of_the_config_and_the_flag(self):
        listed = holders("a", "b", "c")
        both = cv.admit((listed, time.time()), [], "w", "tencent", "spot", 2, 1, account_cap=5)
        self.assertEqual(both.quota, 2)                    # the cloud config is the tighter cap here
        self.assertFalse(both.ok)                          # ...and 3 running instances are over it
        flag = cv.admit((listed, time.time()), [], "w", "tencent", "spot", 10, 1, account_cap=3)
        self.assertEqual(flag.quota, 3)                    # --max-account-slots is the tighter cap here

    def test_control_a_free_slot_launches_once(self):
        provider = FakeProvider([holders("a", "b")])
        admitter, a, _ = self.admitter(provider)
        entry = self.launch(provider, admitter, a)
        self.assertEqual(provider.run_instances, [OFFER])
        self.assertEqual((entry["status"], entry["instance"], entry["admission"]["in_use"]), ("launched", "ins-new", 2))
        self.assertEqual(self.ledger.recent_launches("worker"), 1)

    def test_on_demand_launches_are_outside_the_spot_quota(self):
        provider = FakeProvider([holders("a", "b", "c")])
        admitter, a, _ = self.admitter(provider)
        admitter.market = "on-demand"
        self.launch(provider, admitter, a)
        self.assertEqual(len(provider.run_instances), 1)

    def test_a_local_refusal_does_not_forbid_the_cheaper_region_of_a_later_run(self):
        provider = FakeProvider([holders("a", "b", "c")])
        admitter, a, _ = self.admitter(provider)
        with self.assertRaises(cv.AdmissionRefused):
            self.launch(provider, admitter, a)
        with self.ledger.locked() as rows:
            self.ledger.check(rows, "worker", a, Offer(0.16, "ap-guangzhou", "z", "t", 16))   # no code-20 stop

    def test_waiting_relists_until_a_slot_frees_then_launches_the_same_offer_once(self):
        provider = FakeProvider([holders("a", "b", "c"), holders("a", "b", "c"), holders("a", "b")])
        admitter, a, clock = self.admitter(provider, wait="20")
        self.launch(provider, admitter, a)
        self.assertEqual(provider.run_instances, [OFFER])
        self.assertEqual(provider.listings, 3)
        self.assertEqual(sum(clock.sleeps), 60 + 120)   # one poll after each refusal (in slices of at most a minute)
        self.assertEqual(provider.dry_runs, 0)
        self.assertEqual([r["status"] for r in self.rows()], ["refused", "refused", "launched"])
        self.assertEqual(self.ledger.recent_launches("worker"), 1)

    def test_the_wait_is_bounded_and_ends_without_a_launch(self):
        provider = FakeProvider([holders("a", "b", "c")])
        admitter, a, clock = self.admitter(provider, wait="5")
        with self.assertRaises(CloudStop) as raised:
            self.launch(provider, admitter, a)
        self.assertEqual(raised.exception.code, 20)
        self.assertIn("admission wait expired", str(raised.exception))
        self.assertEqual(provider.run_instances, [])
        self.assertLessEqual(sum(clock.sleeps), 300)
        self.assertEqual(self.ledger.recent_launches("worker"), 0)

    def test_auto_waits_until_the_earliest_recorded_deadline(self):
        provider = FakeProvider([holders("a")])
        admitter, a, _ = self.admitter(provider, wait="auto")
        self.assertTrue(a.wait_auto)
        due = time.time() + 30 * 60
        d = cv.Admission(False, 3, 3, 0, 1, [], 20, "full", next_free=due)
        self.assertAlmostEqual(admitter.budget_minutes(d), 32, delta=0.1)
        d.next_free = time.time() + 10 * 3600
        self.assertEqual(admitter.budget_minutes(d), cv.AUTO_WAIT_CAP_MIN)
        d.next_free = None
        self.assertEqual(admitter.budget_minutes(d), cv.AUTO_WAIT_UNKNOWN_MIN)
        with self.assertRaises(SystemExit), contextlib.redirect_stderr(io.StringIO()):
            cv.parse_args(["--wait-quota", "soon"])

    def test_a_provider_refusal_after_admission_records_both_views(self):
        provider = FakeProvider([holders("a")], refuse=CloudStop("quota exceeded in ap-shanghai (LimitExceeded.UserSpotQuota: x)", 20))
        admitter, a, _ = self.admitter(provider)
        with self.assertRaises(CloudStop) as raised:
            self.launch(provider, admitter, a)
        self.assertEqual(raised.exception.code, 20)
        [row] = self.rows()
        self.assertEqual((row["status"], row["admission"]["in_use"], row["admission"]["quota"]), ("refused", 1, 3))


class Share(LedgerCase):
    def test_known_bad_second_instance_beyond_the_share_is_refused_locally(self):
        provider = FakeProvider([holders("worker")])
        admitter, a, _ = self.admitter(provider, share=1, quota=10)
        with self.assertRaises(cv.AdmissionRefused) as raised:
            self.launch(provider, admitter, a)
        self.assertEqual(raised.exception.code, 25)
        self.assertIn("its share is 1", str(raised.exception))
        self.assertEqual(provider.run_instances, [])

    def test_control_a_grant_with_slots_raises_the_share(self):
        self.ledger.grant("worker", "oracle backfill", minutes=180, slots=4)
        self.ledger.grant("other", "unrelated", slots=8)
        with self.ledger.locked() as rows:
            self.assertEqual(self.ledger.share(rows, "worker", 1), 4)
            self.assertEqual(self.ledger.share(rows, "third", 1), 1)
        with mock.patch.object(cv.time, "time", return_value=time.time() + cv.GRANT_WINDOW_SECS + 1):
            with self.ledger.locked() as rows:
                self.assertEqual(self.ledger.share(rows, "worker", 1), 1)   # the window has passed
        provider = FakeProvider([holders("worker", "worker", "worker")])
        admitter, a, _ = self.admitter(provider, share=4, quota=10)
        self.launch(provider, admitter, a)
        self.assertEqual(len(provider.run_instances), 1)

    def test_grant_and_launch_cli_take_slots(self):
        a = cv.parse_args(["--grant", "kylezh/x", "--minutes", "180", "--slots", "4"])
        self.assertEqual((a.grant, a.minutes, a.slots), ("kylezh/x", 180, 4))
        launch_a = cv.parse_args(["--slots", "4"])
        self.assertEqual((launch_a.grant, launch_a.slots), (None, 4))
        for argv in (["--slots", "0"], ["--slots", str(cv.MAX_SLOTS + 1)],
                     ["--grant", "x", "--slots", "0"], ["--grant", "x", "--slots", str(cv.MAX_SLOTS + 1)],
                     ["--cleanup", "--prune-sg", "--slots", "2"]):
            with self.assertRaises(SystemExit), contextlib.redirect_stderr(io.StringIO()):
                cv.parse_args(argv)
        with self.assertRaises(CloudStop):
            self.ledger.grant("x", "r", slots=0)
        self.ledger.grant("x", "r", slots=2)
        self.assertEqual(self.rows()[-1]["slots"], 2)

    def test_launch_slots_raises_share_and_respects_account_caps(self):
        # Launch --slots raises the owner's share without a grant, and takes max(grant, --slots).
        with self.ledger.locked() as rows:
            self.assertEqual(self.ledger.share(rows, "worker", 1, requested=4), 4)
        self.ledger.grant("worker", "share grant", slots=6)
        with self.ledger.locked() as rows:
            self.assertEqual(self.ledger.share(rows, "worker", 1, requested=4), 6)
            self.assertEqual(self.ledger.share(rows, "worker", 1, requested=8), 8)

        # A wave of concurrent shards with --slots 4 stops at min(share=4, spot_instance_quota=3).
        provider = FakeProvider([[]])
        counter = [0]

        def launch_unique(m, ips, fresh, minutes, arch):
            m.token = f"tok-{counter[0]}"
            provider.checkpoint()
            provider.run_instances.append(m.offer)
            counter[0] += 1
            m.id = f"ins-{counter[0]}"

        provider.launch = launch_unique
        a = self.args("--slots", "4")
        admitter = cv.Admitter(provider, "tencent", "worker", "spot", {"spot_instance_quota": 3},
                               self.ledger.share(self.rows(), "worker", 1, a.slots),
                               a.wait_quota, a.wait_auto, None, account_cap=a.max_account_slots,
                               view=lambda: ([], time.time()))
        for _ in range(3):
            self.launch(provider, admitter, a)
        with self.assertRaises(cv.AdmissionRefused) as raised:
            self.launch(provider, admitter, a)
        self.assertEqual(raised.exception.code, 20)
        self.assertIn("3 of 3 account spot slots in use", str(raised.exception))
        self.assertEqual(len(provider.run_instances), 3)

        # --max-account-slots tighter than both --slots and spot_instance_quota still caps admission.
        provider2 = FakeProvider([[]])
        a2 = self.args("--slots", "5", "--max-account-slots", "2")
        admitter2 = cv.Admitter(provider2, "tencent", "other", "spot", {"spot_instance_quota": 10}, 5,
                                a2.wait_quota, a2.wait_auto, None, account_cap=a2.max_account_slots,
                                view=lambda: (holders("other", "other"), time.time()))
        with self.assertRaises(cv.AdmissionRefused) as raised2:
            cv.launch_with_quota_wait(provider2, Machine(), [], False, a2, self.ledger, "other", set(), admitter2)
        self.assertEqual(raised2.exception.code, 20)
        self.assertIn("the cap is 2 from --max-account-slots", str(raised2.exception))
        self.assertEqual(provider2.run_instances, [])

    def test_dry_run_wires_launch_slots_into_admitter_share(self):
        provider = FakeProvider([holders("worker", "worker")])
        provider.currency, provider.label_suffix = "CNY", "fake"
        provider.check_account = lambda: "qcs::cam:100000000001:uin/100000000002 (CAMUser)"
        provider.offers = lambda types, arch, regions: [OFFER]
        provider.mainland = lambda region: True
        lines = []
        with mock.patch.dict(os.environ, {cloud_common.CONFIG_ENV: Counting.config(self, spot_instance_quota=10)}), \
             mock.patch.object(cv, "current_owner", return_value="worker"), \
             mock.patch.object(cv, "LaunchLedger", return_value=self.ledger), \
             mock.patch.object(cv, "clippy_preflight", return_value=(True, "ok", True)), \
             mock.patch.object(cv, "make_provider", return_value=provider), \
             mock.patch.object(cv, "local_toolchain", return_value="1.0.0"), \
             mock.patch.object(cv, "log", side_effect=lines.append), \
             mock.patch("cloud.setup.log", side_effect=lines.append):
            rc = cv.run_checked(self.args("--quick", "--slots", "4", "--dry-run"), cv.Cancel(os.path.join(self.dir, "c")))
        self.assertEqual(rc, 0)
        text = "\n".join(lines)
        self.assertIn("2 of 10 account spot slots in use (yours 2, share 4)", text)
        self.assertIn("a launch now would be admitted", text)

    def test_a_released_instance_no_longer_counts(self):
        provider = FakeProvider([holders("a")])
        admitter, a, _ = self.admitter(provider, share=1, quota=10)
        entry = self.launch(provider, admitter, a)
        admitter.view_fn = lambda: ([], time.time())   # the listing no longer shows it
        with self.ledger.locked() as rows:
            self.assertEqual(admitter.decide(admitter.view_fn(), rows).yours, 1)   # just launched: still counted
        self.ledger.release("worker", entry["time"], "ins-new")
        with self.ledger.locked() as rows:
            self.assertEqual(admitter.decide(admitter.view_fn(), rows).yours, 0)


class RefusalsCostNothing(LedgerCase):
    def grant_and_launch(self, provider):
        self.ledger.grant("worker", "long run", minutes=180)
        admitter, a, _ = self.admitter(provider, quota=10)
        a.max_minutes = 180
        return admitter, a

    def test_known_bad_a_refused_launch_keeps_the_grant(self):
        provider = FakeProvider([[]], refuse=CloudStop("LimitExceeded.UserSpotQuota", 20))
        admitter, a = self.grant_and_launch(provider)
        with self.assertRaises(CloudStop):
            self.launch(provider, admitter, a)
        with self.ledger.locked() as rows:
            self.assertIsNotNone(self.ledger.available_grant(rows, "worker", 180))
            refused = rows[-1]
        self.assertEqual((refused["status"], refused["code"], refused["grant_returned"]), ("refused", 20, True))
        self.assertEqual(self.ledger.recent_launches("worker"), 0)

    def test_risk_forbidden_and_zone_refusals_keep_the_grant_and_stop(self):
        for error in (CloudStop("risk control", 21), CloudStop("Forbidden", 22), SkipOffer("zone", "sold out")):
            provider = FakeProvider([[]], refuse=error)
            admitter, a = self.grant_and_launch(provider)
            with self.assertRaises(type(error)):
                self.launch(provider, admitter, a)
            self.assertEqual(len(provider.run_instances), 1)   # one call, no retry loop
            with self.ledger.locked() as rows:
                self.assertIsNotNone(self.ledger.available_grant(rows, "worker", 180))

    def test_control_a_launch_consumes_the_grant(self):
        provider = FakeProvider([[]])
        admitter, a = self.grant_and_launch(provider)
        self.launch(provider, admitter, a)
        with self.ledger.locked() as rows:
            self.assertIsNone(self.ledger.available_grant(rows, "worker", 180))
        self.assertEqual(self.ledger.recent_launches("worker"), 1)

    def test_an_unknown_outcome_after_the_call_stays_a_launch(self):
        provider = FakeProvider([[]], refuse=CloudStop("tccli cvm RunInstances timed out", cloud_common.INFRA_FAIL))
        admitter, a = self.grant_and_launch(provider)
        with self.assertRaises(CloudStop):
            self.launch(provider, admitter, a)
        self.assertEqual(self.rows()[-1]["status"], "reserved")
        with self.ledger.locked() as rows:
            self.assertIsNone(self.ledger.available_grant(rows, "worker", 180))

    def test_a_local_error_before_the_call_is_no_launch(self):
        def setup_fails():
            raise cloud_common.InfraError("ensure_vpc: DescribeVpcs timed out", cloud_common.INFRA_FAIL)
        provider = FakeProvider([[]], before_run=setup_fails)
        admitter, a = self.grant_and_launch(provider)
        with self.assertRaises(CloudStop):
            self.launch(provider, admitter, a)
        self.assertEqual(provider.run_instances, [])
        self.assertEqual(self.rows()[-1]["status"], "refused")
        self.assertEqual(self.ledger.recent_launches("worker"), 0)


class CancelCheckpoints(LedgerCase):
    def cancel(self):
        return cv.Cancel(os.path.join(self.dir, "cancel"), started=time.time() - 1)

    def test_known_bad_cancel_after_the_preflight_launches_nothing(self):
        cancel = self.cancel()
        provider = FakeProvider([[]])
        admitter, a, _ = self.admitter(provider, cancel=cancel)
        cv.Cancel.request(cancel.path)    # e.g. `cloud_verify.py --cancel` while Clippy ran
        with self.assertRaises(cv.Cancelled):
            self.launch(provider, admitter, a, cancel)
        self.assertEqual(provider.run_instances, [])
        self.assertEqual(self.rows(), [])     # not even a reservation

    def test_cancel_during_the_provider_setup_stops_at_the_launch_call(self):
        cancel = self.cancel()
        provider = FakeProvider([[]], before_run=lambda: cancel.set("signal 15"))
        self.ledger.grant("worker", "r", minutes=180)
        admitter, a, _ = self.admitter(provider, cancel=cancel)
        a.max_minutes = 180
        with self.assertRaises(cv.Cancelled):
            self.launch(provider, admitter, a, cancel)
        self.assertEqual(provider.run_instances, [])
        row = self.rows()[-1]
        self.assertEqual((row["status"], row.get("api_called")), ("cancelled", None))
        self.assertTrue(row["grant_returned"])
        self.assertEqual(self.ledger.recent_launches("worker"), 0)

    def test_control_without_a_cancel_the_launch_proceeds(self):
        cancel = self.cancel()
        provider = FakeProvider([[]])
        admitter, a, _ = self.admitter(provider, cancel=cancel)
        self.launch(provider, admitter, a, cancel)
        self.assertEqual(len(provider.run_instances), 1)
        self.assertTrue(self.rows()[-1]["api_called"])

    def test_an_older_cancel_file_does_not_cancel_a_new_run(self):
        path = os.path.join(self.dir, "cancel")
        cv.Cancel.request(path)
        os.utime(path, (time.time() - 60, time.time() - 60))
        cv.Cancel(path).check("x")

    def test_tencent_checks_immediately_before_run_instances(self):
        calls = []

        def tccli(product, api, region=None, **params):
            calls.append(api + (" (dry run)" if params.get("DryRun") else ""))
            return {"RoleInfo": {"PolicyDocument": "cvm.qcloud.com"}} if api == "GetRole" else {"InstanceIdSet": ["ins-1"]}
        with mock.patch.dict(os.environ, {cloud_common.CONFIG_ENV: Counting.config(self)}), \
             mock.patch.object(cloud_tencent, "tccli", tccli), mock.patch.object(cloud_tencent, "log"):
            p = cloud_tencent.TencentProvider()
            p.owner = "worker"
            p.ensure_key_pair = lambda region: "key-1"
            p.ensure_vpc = lambda region: "vpc-1"
            p.ensure_subnet = lambda region, vpc, zone: "subnet-1"
            p.ensure_security_group = lambda region, ips: "sg-1"
            p.image = lambda region, arch, itype: ("img-1", "Ubuntu")
            cancel = self.cancel()
            entry = {}
            cv.arm_checkpoint(p, entry, cancel)
            cancel.set("signal 2")
            m = Machine()
            with self.assertRaises(cv.Cancelled):
                p.launch(m, ["1.2.3.4"], False, 30, "x86_64")
            self.assertNotIn("RunInstances", calls)
            cancel.reason = None
            p.launch(m, ["1.2.3.4"], False, 30, "x86_64")
            self.assertEqual((calls[-1], entry["api_called"], m.id), ("RunInstances", True, "ins-1"))

    def test_run_checks_the_cancel_flag_after_the_preflight(self):
        a = cv.parse_args(["--quick", "--provider", "tencent"])
        provider = mock.MagicMock()
        cancel = self.cancel()

        def clippy(*args, **kw):
            cv.Cancel.request(cancel.path)   # the cancel arrives while the preflight runs
            return True, "prelaunch clippy passed", True
        with mock.patch.object(cv, "current_owner", return_value="worker"), \
             mock.patch.object(cv, "LaunchLedger", return_value=self.ledger), \
             mock.patch.object(cv, "clippy_preflight", side_effect=clippy), \
             mock.patch.object(cv, "make_provider", return_value=provider):
            with self.assertRaises(cv.Cancelled):
                cv.run_checked(a, cancel)
        provider.offers.assert_not_called()
        provider.launch.assert_not_called()

    def test_main_reports_a_cancel_before_the_launch_phase(self):
        with mock.patch.object(cv, "parse_args", return_value=object()), \
             mock.patch.object(cv, "run", side_effect=cv.Cancelled("cancelled before admission")), \
             mock.patch.object(cv, "log") as log:
            self.assertEqual(cv.main(), cloud_common.INFRA_FAIL)
        self.assertIn("nothing launched", log.call_args.args[0])

    def test_run_installs_the_signal_handlers_before_the_preflight_and_restores_them(self):
        seen = {}

        def checked(a, cancel):
            seen["int"] = signal.getsignal(signal.SIGINT)
            return 0
        before = signal.getsignal(signal.SIGINT)
        with mock.patch.object(cv, "run_checked", side_effect=checked), \
             mock.patch.object(cv, "git", return_value=self.dir):
            cv.run(cv.parse_args([]))
        self.assertNotEqual(seen["int"], before)
        self.assertNotIn(seen["int"], (signal.SIG_IGN, signal.SIG_DFL, signal.default_int_handler))
        self.assertEqual(signal.getsignal(signal.SIGINT), before)


class ProviderDryRunAdmission(LedgerCase):
    """Tencent's spot limits are not one account-wide number, so the provider
    answers for the exact request with a dry run before the real call."""

    def provider(self, dry_run_error):
        calls = []

        def tccli(product, api, region=None, **params):
            calls.append(api + (" (dry run)" if params.get("DryRun") else ""))
            if api == "GetRole":
                return {"RoleInfo": {"PolicyDocument": "cvm.qcloud.com"}}
            if params.get("DryRun"):
                raise dry_run_error
            return {"InstanceIdSet": ["ins-1"]}
        for patcher in (mock.patch.dict(os.environ, {cloud_common.CONFIG_ENV: Counting.config(self)}),
                        mock.patch.object(cloud_tencent, "tccli", tccli), mock.patch.object(cloud_tencent, "log")):
            patcher.start()
            self.addCleanup(patcher.stop)
        p = cloud_tencent.TencentProvider()
        p.owner = "worker"
        p.all_regions = ["ap-shanghai"]
        p.slot_holders = lambda regions: []
        p.ensure_key_pair = lambda region: "key-1"
        p.ensure_vpc = lambda region: "vpc-1"
        p.ensure_subnet = lambda region, vpc, zone: "subnet-1"
        p.ensure_security_group = lambda region, ips: "sg-1"
        p.image = lambda region, arch, itype: ("img-1", "Ubuntu")
        return p, calls

    def test_known_bad_a_provider_quota_dry_run_refusal_launches_nothing_and_costs_nothing(self):
        E = cloud_tencent.TencentError
        for code in ("LimitExceeded.UserSpotQuota", "LimitExceeded.SpotQuota"):
            self.ledger.write([])
            p, calls = self.provider(E(code, "spot quota exceeded", []))
            self.ledger.grant("worker", "r", minutes=180)
            admitter, a, _ = self.admitter(p, quota=10)
            a.max_minutes = 180
            with self.assertRaises(cloud_common.ProviderQuotaFull) as raised:
                self.launch(p, admitter, a)
            self.assertEqual(raised.exception.code, 20)
            self.assertIn("nothing launched", str(raised.exception))
            self.assertNotIn("RunInstances", calls)          # no real launch call
            row = self.rows()[-1]
            self.assertEqual((row["status"], row["code"], row.get("api_called"), row["grant_returned"]),
                             ("refused", 20, None, True))
            self.assertEqual(self.ledger.recent_launches("worker"), 0)

    def test_with_a_wait_the_same_offer_is_probed_and_launched_once(self):
        p, calls = self.provider(cloud_tencent.TencentError("LimitExceeded.UserSpotQuota", "x", []))
        admitter, a, _ = self.admitter(p, quota=10, wait="10")

        def freed(*args, **kw):
            # (The probe itself is wait_for_quota's, tested in test_quota_wait.)
            p.admit_dry_run = lambda offer, params: None
        with mock.patch.object(cv, "wait_for_quota", side_effect=freed) as waited:
            entry = self.launch(p, admitter, a)
        waited.assert_called_once()
        self.assertEqual(waited.call_args.args[1], OFFER)    # the same region, zone and type
        self.assertEqual(calls.count("RunInstances"), 1)
        self.assertEqual(entry["status"], "launched")

    def test_control_a_dry_run_that_would_succeed_launches(self):
        p, calls = self.provider(cloud_tencent.TencentError("DryRunOperation", "would succeed", []))
        admitter, a, _ = self.admitter(p, quota=10)
        entry = self.launch(p, admitter, a)
        self.assertEqual(calls[-2:], ["RunInstances (dry run)", "RunInstances"])
        self.assertEqual((entry["status"], entry["instance"]), ("launched", "ins-1"))

    def test_other_dry_run_errors_are_left_to_the_real_call(self):
        p, calls = self.provider(cloud_tencent.TencentError("InvalidParameterValue.Whatever", "x", []))
        admitter, a, _ = self.admitter(p, quota=10)
        self.launch(p, admitter, a)
        self.assertIn("RunInstances", calls)
        self.ledger.write([])
        p, calls = self.provider(cloud_tencent.TencentError("OperationDenied.RiskControl", "x", []))
        admitter, a, _ = self.admitter(p, quota=10)
        with self.assertRaisesRegex(CloudStop, "risk control"):
            self.launch(p, admitter, a)
        self.assertNotIn("RunInstances", calls)


class ZoneQuotaRetry(LedgerCase):
    """A spot-quota refusal is zone-scoped (2026-10-08): the same region, the
    same instance type and the same market may still admit the request in
    another zone, so only those zones are tried, and only after a spot-quota
    refusal. Risk/forbidden refusals and every other quota code stop at once;
    another region or type is never tried; a zone refusal that succeeds in the
    next zone spends exactly one launch, and a region where every zone refuses
    spends none (a quota stop, code 20, so --wait-quota re-probes it)."""

    ZONES = ["ap-shanghai-5", "ap-shanghai-8"]

    @staticmethod
    def offer(zone="ap-shanghai-5"):
        return Offer(0.1584, "ap-shanghai", zone, "SA5.4XLARGE32", 16)

    def provider(self, zones=None, dry_run=None, real=None, rows=None):
        """A TencentProvider whose tccli double answers the zone listing from
        `rows` (default: `zones` as SELL rows of the offer's type), refuses a
        dry run whose zone `dry_run` (a callable or an exception) names, and a
        real RunInstances whose zone `real` names. Recorded calls keep the
        (kind, region, zone) triple, so a test can prove which region, type
        and zone the launch actually touched."""
        self.calls, self.logs, self.subnets = [], [], []

        def rows_for(zs):
            return [{"Zone": z, "InstanceType": "SA5.4XLARGE32", "InstanceFamily": "SA5", "Cpu": 16,
                     "Status": "SELL", "StatusCategory": "EnoughStock",
                     "Price": {"UnitPrice": 2.64, "UnitPriceDiscount": 0.1584}} for z in zs]

        def tccli(product, api, region=None, **params):
            zone = (params.get("Placement") or {}).get("Zone")
            if api == "GetRole":
                return {"RoleInfo": {"PolicyDocument": "cvm.qcloud.com"}}
            if api == "DescribeZoneInstanceConfigInfos":
                self.calls.append(("zones", region, None))
                if rows is not None:
                    return {"InstanceTypeQuotaSet": rows}
                return {"InstanceTypeQuotaSet": rows_for(zones or self.ZONES)}
            if api == "DescribeAccountBalance":
                return {"RealBalance": 100000}
            if api == "InquiryPriceRunInstances":
                return {"Price": {"InstancePrice": {"UnitPrice": 2.64, "UnitPriceDiscount": 0.1584, "Discount": 94},
                                  "BandwidthPrice": {"UnitPrice": 0.8, "UnitPriceDiscount": 0.8}}}
            if api == "DescribeVpcs":
                return {"VpcSet": [{"VpcId": "vpc-1"}]}
            if api == "DescribeSubnets":
                return {"SubnetSet": [{"Zone": z, "SubnetId": "subnet-" + z} for z in (zones or self.ZONES)]}
            if api == "DescribeSecurityGroups":
                return {"SecurityGroupSet": [{"SecurityGroupId": "sg-1"}]}
            if api == "DescribeKeyPairs":
                return {"KeyPairSet": [{"KeyId": "skey-1"}]}
            if api != "RunInstances":
                return {}
            kind = "dry" if params.get("DryRun") else "run"
            self.calls.append((kind, region, zone))
            # The subnet of the request: a fallback zone must be probed with
            # its own zone's subnet, not the original zone's (the probe cannot
            # read the zone off `offer`, which zone_scan has already moved).
            self.subnets.append((kind, zone, (params.get("VirtualPrivateCloud") or {}).get("SubnetId")))
            error = (dry_run(zone) if kind == "dry" else real(zone)) if callable(
                dry_run if kind == "dry" else real) else (dry_run if kind == "dry" else real)
            if error:
                raise error
            return {"InstanceIdSet": ["ins-" + zone]}

        for patcher in (mock.patch.dict(os.environ, {cloud_common.CONFIG_ENV: Counting.config(self)}),
                        mock.patch.object(cloud_tencent, "tccli", tccli),
                        mock.patch.object(cloud_tencent, "log", lambda *a: self.logs.append(" ".join(map(str, a)))),
                        mock.patch.object(cloud_tencent, "warning", lambda *a: None),
                        mock.patch.object(cloud_tencent, "direct_public_ip", lambda: "1.2.3.4")):
            patcher.start()
            self.addCleanup(patcher.stop)
        p = cloud_tencent.TencentProvider()
        p.owner = "worker"
        p.all_regions = ["ap-shanghai"]
        p.slot_holders = lambda regions: []
        p.ensure_key_pair = lambda region: "skey-1"
        p.ensure_vpc = lambda region: "vpc-1"
        p.ensure_subnet = lambda region, vpc, zone: "subnet-" + zone
        p.ensure_security_group = lambda region, ips: "sg-1"
        p.image = lambda region, arch, itype: ("img-1", "Ubuntu")
        return p

    def launch_offer(self, provider, offer, wait="0", grant=None):
        admitter, a, _ = self.admitter(provider, quota=10, wait=wait)
        if grant:
            self.ledger.grant("worker", "long run", minutes=grant)
            a.max_minutes = grant
        return cv.launch_with_quota_wait(provider, Machine(offer), [], False, a, self.ledger, "worker", set(), admitter)

    def of_kind(self, kind):
        return [zone for k, _, zone in self.calls if k == kind]

    def subnets_of(self, kind):
        return [(zone, subnet) for k, zone, subnet in self.subnets if k == kind]

    def test_known_bad_a_zone_quota_refusal_launches_in_the_next_zone_of_the_same_region(self):
        E = cloud_tencent.TencentError
        p = self.provider(dry_run=lambda z: E("LimitExceeded.UserSpotQuota", "spot quota exceeded", [])
                          if z == "ap-shanghai-5" else None)
        offer = self.offer()
        entry = self.launch_offer(p, offer)
        self.assertEqual(self.of_kind("dry"), ["ap-shanghai-5", "ap-shanghai-8"])
        self.assertEqual(self.of_kind("run"), ["ap-shanghai-8"])            # exactly one real launch, in the other zone
        self.assertEqual(self.subnets_of("dry"), [("ap-shanghai-5", "subnet-ap-shanghai-5"),
                                                  ("ap-shanghai-8", "subnet-ap-shanghai-8")])
        self.assertEqual((entry["status"], entry["instance"]), ("launched", "ins-ap-shanghai-8"))
        self.assertEqual((offer.zone, offer.region, offer.itype), ("ap-shanghai-8", "ap-shanghai", "SA5.4XLARGE32"))
        self.assertEqual(self.ledger.recent_launches("worker"), 1)          # one launch consumed, not two
        self.assertIn("zone ap-shanghai-5: quota refused; trying ap-shanghai-8 (same region/type)", self.logs)

    def test_known_bad_a_real_call_quota_refusal_also_falls_back_to_the_next_zone(self):
        E = cloud_tencent.TencentError
        p = self.provider(real=lambda z: E("LimitExceeded.SpotQuota", "spot quota exceeded", [])
                          if z == "ap-shanghai-5" else None)
        entry = self.launch_offer(p, self.offer())
        self.assertEqual(self.of_kind("run"), ["ap-shanghai-5", "ap-shanghai-8"])
        self.assertEqual((entry["status"], entry["instance"]), ("launched", "ins-ap-shanghai-8"))
        self.assertEqual(self.ledger.recent_launches("worker"), 1)

    def test_known_bad_every_zone_refusing_is_one_region_quota_stop_that_keeps_the_grant(self):
        E = cloud_tencent.TencentError
        p = self.provider(dry_run=lambda z: E("LimitExceeded.UserSpotQuota", "spot quota exceeded", []))
        with self.assertRaises(cloud_common.ProviderQuotaFull) as raised:
            self.launch_offer(p, self.offer(), grant=180)
        self.assertEqual(raised.exception.code, 20)
        self.assertIn("spot quota refused in every zone (ap-shanghai-5, ap-shanghai-8)", str(raised.exception))
        self.assertIn("nothing launched", str(raised.exception))
        self.assertEqual(self.of_kind("dry"), ["ap-shanghai-5", "ap-shanghai-8"])
        self.assertEqual(self.of_kind("run"), [])                          # nothing launched anywhere
        row = self.rows()[-1]
        self.assertEqual((row["status"], row["code"], row["grant_returned"]), ("refused", 20, True))
        self.assertEqual(self.ledger.recent_launches("worker"), 0)         # no launch counted; grant kept
        with self.ledger.locked() as rows:
            self.assertIsNotNone(self.ledger.available_grant(rows, "worker", 180))

    def test_known_bad_only_the_same_region_and_type_is_tried_after_a_quota_refusal(self):
        E = cloud_tencent.TencentError
        other = [{"Zone": "ap-shanghai-9", "InstanceType": "SA9.4XLARGE32", "InstanceFamily": "SA9", "Cpu": 16,
                  "Status": "SELL", "StatusCategory": "EnoughStock",
                  "Price": {"UnitPrice": 2.64, "UnitPriceDiscount": 0.1584}},
                 {"Zone": "ap-shanghai-2", "InstanceType": "SA5.4XLARGE32", "InstanceFamily": "SA5", "Cpu": 16,
                  "Status": "SOLD_OUT", "StatusCategory": "WithoutStock",
                  "Price": {"UnitPrice": 2.64, "UnitPriceDiscount": 0.1584}}]
        rows = [{"Zone": z, "InstanceType": "SA5.4XLARGE32", "InstanceFamily": "SA5", "Cpu": 16,
                 "Status": "SELL", "StatusCategory": "EnoughStock",
                 "Price": {"UnitPrice": 2.64, "UnitPriceDiscount": 0.1584}} for z in self.ZONES] + other
        p = self.provider(rows=rows, dry_run=lambda z: E("LimitExceeded.UserSpotQuota", "x", []))
        self.assertEqual([o.zone for o in p.zone_offers(self.offer())], self.ZONES)   # SELL + same type only
        self.calls = []
        with self.assertRaises(cloud_common.ProviderQuotaFull) as raised:
            self.launch_offer(p, self.offer())
        self.assertNotIsInstance(raised.exception, SkipOffer)   # a SkipOffer is what would let the caller try another offer
        self.assertEqual(self.of_kind("dry"), self.ZONES)
        self.assertEqual(self.of_kind("run"), [])
        self.assertEqual({region for _, region, _ in self.calls}, {"ap-shanghai"})   # never another region

    def test_known_bad_a_risk_or_forbidden_refusal_stops_without_probing_the_next_zone(self):
        E = cloud_tencent.TencentError
        for code, stop in (("OperationDenied.RiskControl", 21), ("Forbidden", 22)):
            self.ledger.write([])
            p = self.provider(dry_run=lambda z, code=code: E(code, "control", []) if z == "ap-shanghai-5" else None)
            with self.assertRaises(CloudStop) as raised:
                self.launch_offer(p, self.offer())
            self.assertEqual(raised.exception.code, stop)
            self.assertEqual(self.of_kind("dry"), ["ap-shanghai-5"])        # the next zone is never probed
            self.assertEqual(self.of_kind("run"), [])
            self.assertEqual(self.rows()[-1]["status"], "refused")

    def test_an_account_wide_limit_exceeded_is_not_zone_scoped_and_stops_at_once(self):
        """Only `LimitExceeded.UserSpotQuota` / `LimitExceeded.SpotQuota` move
        to another zone; every other `LimitExceeded` code is account-wide, so
        the next zone of the region is never probed."""
        E = cloud_tencent.TencentError
        p = self.provider(dry_run=lambda z: E("LimitExceeded.InstanceQuotaExceeded", "quota", [])
                          if z == "ap-shanghai-5" else None)
        with self.assertRaises(cloud_common.ProviderQuotaFull) as raised:
            self.launch_offer(p, self.offer())
        self.assertEqual(raised.exception.code, 20)
        self.assertEqual(self.of_kind("dry"), ["ap-shanghai-5"])            # the next zone is never probed
        self.assertEqual(self.of_kind("run"), [])
        self.assertEqual(self.rows()[-1]["status"], "refused")

    def test_the_read_only_plan_reports_the_zone_sequence_without_launching(self):
        E = cloud_tencent.TencentError
        p = self.provider(dry_run=lambda z: E("LimitExceeded.UserSpotQuota", "x", []) if z == "ap-shanghai-5" else None)
        key = os.path.join(self.dir, "tlx-verify")
        with open(key + ".pub", "w") as f:
            f.write("ssh-ed25519 AAAA test\n")
        offer = self.offer()
        with mock.patch.object(cloud_tencent, "KEY_FILE", key):
            lines = p.describe_plan(offer, "x86_64")
        self.assertIn("RunInstances DryRun: would succeed", lines)
        self.assertEqual(self.of_kind("dry"), ["ap-shanghai-5", "ap-shanghai-8"])
        self.assertEqual(self.subnets_of("dry"), [("ap-shanghai-5", "subnet-ap-shanghai-5"),
                                                  ("ap-shanghai-8", "subnet-ap-shanghai-8")])
        self.assertEqual(self.of_kind("run"), [])                          # read-only: no real call
        self.assertEqual(offer.zone, "ap-shanghai-8")


class DeadBootRelease(LedgerCase):
    """A launch whose instance never answers ssh must not keep its grant or be
    charged the whole unrun `max_minutes`: the same owner launches the next
    offer, and `check` refuses a >60-minute launch without an unconsumed grant
    (2026-11-28: the retry of a dead spot boot died on exit 25)."""

    def test_a_dead_boot_returns_its_grant_and_pays_only_for_the_time_it_lived(self):
        self.ledger.grant("worker", "external campaign shard", minutes=180)
        provider = FakeProvider([holders("other")])
        admitter, _, _ = self.admitter(provider)
        a = self.args("--max-minutes", "180")
        a.min_lifetime_minutes = provider.min_lifetime_minutes
        entry = self.launch(provider, admitter, a)
        self.assertEqual(next(r for r in self.rows() if r.get("grant"))["consumed_by"], entry["time"])
        self.assertAlmostEqual(entry["estimated_cost"], 0.16 * 180 / 60)

        self.assertTrue(self.ledger.release_dead_boot("worker", entry["time"], entry["instance"]))

        rows = self.rows()
        grant = next(r for r in rows if r.get("grant"))
        row = next(r for r in rows if not r.get("grant"))
        self.assertNotIn("consumed_by", grant)          # available to the retry
        self.assertEqual(self.ledger.available_grant(rows, "worker", 180)["minutes"], 180)
        self.assertTrue(row["grant_returned"])
        self.assertTrue(row["dead_boot"])
        self.assertIn("released", row)
        self.assertEqual((row["status"], row["instance"]), ("launched", "ins-new"))   # still evidence
        # The 7-minute provider minimum, not the 180 minutes it never ran.
        self.assertAlmostEqual(row["estimated_cost"], 0.16 * 7 / 60)

    def test_the_release_is_a_no_op_for_a_row_that_is_not_this_launch(self):
        self.ledger.write([{"owner": "worker", "time": 1.0, "instance": "ins-old", "status": "launched",
                            "provider": "tencent", "estimated_cost": 1.0}])
        self.assertFalse(self.ledger.release_dead_boot("worker", 2.0, "ins-new"))
        self.assertNotIn("released", self.rows()[0])


class DeadBootRetry(LedgerCase):
    """The retry of a dead first boot passes the same budget checks as the
    launch it replaces: a >60-minute grant and the 12 h CNY cap."""

    def provider(self, offers):
        provider = DeadBootProvider([holders("other")])
        provider.currency, provider.label_suffix = "CNY", "fake"
        provider.check_account = lambda: "qcs::cam:100000000001:uin/100000000002 (CAMUser)"
        provider.offers = lambda types, arch, regions: list(offers)
        provider.mainland = lambda region: True
        provider.public_ips = lambda proxy: ["192.0.2.1"]
        provider.terminate_hint = lambda m: "terminate it"
        provider.leftovers = lambda regions, owner=None: []
        return provider

    def run_boot(self, provider, *argv):
        """`run_checked` up to and including boot; the passes are stubbed so the
        retry itself is what the test observes."""
        with mock.patch.dict(os.environ, {cloud_common.CONFIG_ENV: Counting.config(self)}), \
             mock.patch.object(cv, "current_owner", return_value="worker"), \
             mock.patch.object(cv, "LaunchLedger", return_value=self.ledger), \
             mock.patch.object(cv, "clippy_preflight", return_value=(True, "ok", True)), \
             mock.patch.object(cv, "make_provider", return_value=provider), \
             mock.patch.object(cv, "ensure_local_key", return_value=False), \
             mock.patch.object(cv, "local_toolchain", return_value="1.0.0"), \
             mock.patch.object(cloud_common.Machine, "wait_ssh", lambda self, timeout=300, **kw: None), \
             mock.patch.object(cloud_remote, "prepare"), \
             mock.patch.object(cloud_remote, "passes", lambda session: setattr(session, "rc", 0)), \
             mock.patch("builtins.print"):
            return cv.run_checked(self.args(*argv), cv.Cancel(os.path.join(self.dir, "c")))

    def test_a_dead_first_boot_returns_the_grant_and_the_next_offer_launches(self):
        self.ledger.grant("worker", "external campaign shard", minutes=180)
        provider = self.provider([OFFER, OFFER2])
        rc = self.run_boot(provider, "--quick", "--max-minutes", "180")
        self.assertEqual(rc, 0)                                    # offer 2 launched, not exit 25
        self.assertEqual(provider.run_instances, [OFFER, OFFER2])
        self.assertEqual(provider.terminated, ["ins-1", "ins-2"])  # the dead boot, then cleanup
        rows = self.rows()
        grant = next(r for r in rows if r.get("grant"))
        dead = next(r for r in rows if r.get("dead_boot"))
        live = next(r for r in rows if r.get("instance") == "ins-2")
        self.assertEqual(grant["consumed_by"], live["time"])        # the retry took it
        self.assertTrue(dead["grant_returned"])
        self.assertLess(dead["estimated_cost"], 0.16 * 180 / 60)
        self.assertEqual(dead["instance"], "ins-1")

    def test_a_dead_first_boot_is_not_charged_its_whole_max_minutes_against_the_cap(self):
        # $3/h x 60 min twice would be 6 CNY against the 5 CNY base cap; the
        # dead VM lived seconds, so only the 7-minute minimum is charged and the
        # second offer fits.
        provider = self.provider([PRICEY, PRICEY_NEXT])
        rc = self.run_boot(provider, "--quick", "--max-minutes", "60")
        self.assertEqual(rc, 0)
        rows = self.rows()
        dead = next(r for r in rows if r.get("dead_boot"))
        self.assertAlmostEqual(dead["estimated_cost"], 3.0 * 7 / 60)
        self.assertEqual(len(rows), 2)


class EndToEnd(LedgerCase):
    def test_a_run_reserves_launches_terminates_and_releases_its_slot(self):
        provider = FakeProvider([holders("other")])
        provider.currency, provider.label_suffix, provider.terminated = "CNY", "fake", []
        provider.check_account = lambda: "qcs::cam:100000000001:uin/100000000002 (CAMUser)"
        provider.offers = lambda types, arch, regions: [OFFER]
        provider.mainland = lambda region: True
        provider.public_ips = lambda proxy: ["192.0.2.1"]
        provider.terminate_hint = lambda m: "terminate it"
        provider.leftovers = lambda regions, owner=None: []

        def wait_ready(m):
            raise cloud_common.InfraError("boot failed")
        provider.wait_ready = wait_ready
        provider.terminate = lambda m: provider.terminated.append(m.id) or True
        with mock.patch.dict(os.environ, {cloud_common.CONFIG_ENV: Counting.config(self)}), \
             mock.patch.object(cv, "current_owner", return_value="worker"), \
             mock.patch.object(cv, "LaunchLedger", return_value=self.ledger), \
             mock.patch.object(cv, "clippy_preflight", return_value=(True, "ok", True)), \
             mock.patch.object(cv, "make_provider", return_value=provider), \
             mock.patch.object(cv, "ensure_local_key", return_value=False), \
             mock.patch.object(cv, "local_toolchain", return_value="1.0.0"), \
             mock.patch("builtins.print"):
            rc = cv.run_checked(self.args("--quick"), cv.Cancel(os.path.join(self.dir, "c")))
        self.assertEqual(rc, cloud_common.INFRA_FAIL)
        self.assertEqual((provider.run_instances, provider.terminated), ([OFFER], ["ins-new"]))
        [row] = self.rows()
        self.assertEqual((row["status"], row["instance"], row["admission"]["in_use"]), ("launched", "ins-new", 1))
        self.assertIn("released", row)
        self.assertEqual(self.ledger.recent_launches("worker"), 1)


class ListingAndIdentity(LedgerCase):
    def test_mask_identity_keeps_the_type_and_a_short_suffix(self):
        self.assertEqual(cloud_common.mask_identity("qcs::cam:100000000001:uin/100000000002 (CAMUser)"),
                         "qcs::cam:***001:uin/***002 (CAMUser)")
        self.assertEqual(cloud_common.mask_identity("account 123456789012 (arn:aws:iam::123456789012:user/tlx)"),
                         "account ***012 (arn:aws:iam::***012:user/tlx)")
        self.assertEqual(cloud_common.mask_identity("ins-1 at 12:05, 10 slots"), "ins-1 at 12:05, 10 slots")
        e = cloud_common.AccountError("profile 'tlx' is qcs::cam:100000000001:uin/100000000001, expected qcs::cam:100000000001:uin/100000000002")
        self.assertNotRegex(str(e), r"\d{6}")

    def test_list_masks_the_identity_skips_clippy_and_shows_every_owner(self):
        provider = FakeProvider([holders("kylezh/a", "kylezh/a", "kylezh/b") + holders("(untagged)")])
        provider.leftovers = lambda regions, owner=None: [("ap-shanghai", "ins-1", "RUNNING")]
        provider.check_account = lambda: "qcs::cam:100000000001:uin/100000000002 (CAMUser)"
        lines = []
        with mock.patch.dict(os.environ, {cloud_common.CONFIG_ENV: Counting.config(self)}), \
             mock.patch.object(cv, "current_owner", return_value="kylezh/a"), \
             mock.patch.object(cv, "LaunchLedger", return_value=self.ledger), \
             mock.patch.object(cv, "clippy_preflight") as clippy, \
             mock.patch.object(cv, "make_provider", return_value=provider), \
             mock.patch.object(cv, "log", side_effect=lambda m: lines.append(m)):
            cv.run_checked(cv.parse_args(["--provider", "tencent", "--list"]), cv.Cancel(os.path.join(self.dir, "c")))
        clippy.assert_not_called()
        text = "\n".join(lines)
        self.assertIn("tencent: qcs::cam:***001:uin/***002 (CAMUser)", text)
        self.assertNotRegex(text, r"\d{9}")
        self.assertIn("4 of 3 account spot slots in use", text)
        self.assertIn("slots by owner: kylezh/a 2, (untagged) 1, kylezh/b 1", text)

    def test_cleanup_records_the_release(self):
        self.ledger.write([{"owner": "w", "time": 1.0, "instance": "ins-1", "provider": "tencent", "status": "launched"}])
        provider = mock.Mock(all_regions=["r"])
        provider.leftovers.return_value = [("r", "ins-1", "RUNNING")]
        released = lambda iids: self.ledger.release_instances(lambda row: row.get("instance") in iids)
        self.assertEqual(cv.manage_instances(provider, cv.parse_args(["--cleanup", "--mine"]), "w", released=released), 0)
        self.assertIn("released", self.rows()[0])


class GrantBudget(LedgerCase):
    """A coordinator grant can add a CNY allowance to the owner's 12 h cap."""
    def spend(self, cost, when=None):
        with self.ledger.locked() as rows:
            rows.append({"owner": "worker", "time": when or time.time(), "instance": "ins-old", "status": "launched",
                         "provider": "tencent", "estimated_cost": cost})
            self.ledger.write(rows)

    def admit(self, price):
        """The budget check of one 60-minute launch that costs `price` CNY."""
        with self.ledger.locked() as rows:
            self.ledger.check(rows, "worker", self.args(), Offer(price, "ap-shanghai", "ap-shanghai-5", "SA5.4XLARGE32", 16))

    def test_known_bad_spent_budget_refuses_the_next_launch_at_the_5_cny_cap(self):
        self.spend(4.3)
        with self.assertRaises(CloudStop) as raised:
            self.admit(0.8)   # 4.3 + 0.8 = 5.1 > 5
        self.assertEqual(raised.exception.code, 25)
        self.assertIn("exceeds the 5 CNY cap", str(raised.exception))
        self.assertIn("5 CNY base", str(raised.exception))

    def test_control_a_launch_within_the_cap_is_admitted(self):
        self.spend(4.3)
        self.admit(0.5)   # 4.3 + 0.5 = 4.8 <= 5

    def test_known_bad_a_grant_without_budget_adds_nothing(self):
        self.spend(4.3)
        self.ledger.grant("worker", "long run", minutes=60)
        with self.assertRaises(CloudStop) as raised:
            self.admit(0.8)
        self.assertIn("exceeds the 5 CNY cap", str(raised.exception))

    def test_a_grant_with_budget_cny_raises_the_cap_by_that_amount(self):
        self.spend(4.3)
        self.ledger.grant("worker", "tlc baseline sweep", minutes=60, budget_cny=5)
        self.assertEqual(self.rows()[-1]["budget_cny"], 5)
        self.admit(0.8)                       # 5.1 <= 10: admitted under the raised cap
        with self.assertRaises(CloudStop) as raised:
            self.admit(6)                     # 4.3 + 6 = 10.3 > 10
        self.assertEqual(raised.exception.code, 25)
        self.assertIn("exceeds the 10 CNY cap", str(raised.exception))
        self.assertIn("5 CNY base + 5 CNY from grants", str(raised.exception))

    def test_the_grant_budget_counts_whether_or_not_its_launch_was_consumed(self):
        self.ledger.grant("worker", "r", minutes=60, budget_cny=5)
        with self.ledger.locked() as rows:
            rows[-1]["consumed_by"] = time.time()
            self.ledger.write(rows)
        self.spend(9.5)
        self.admit(0.4)                       # 9.5 + 0.4 = 9.9 <= 10
        with self.assertRaises(CloudStop):
            self.admit(0.6)                   # 10.1 > 10

    def test_grants_older_than_the_window_do_not_count(self):
        old = time.time() - cv.GRANT_WINDOW_SECS - 1
        with self.ledger.locked() as rows:
            rows.append({"owner": "worker", "time": old, "grant": 1, "minutes": 60, "budget_cny": 5,
                         "reason": "old", "status": "grant"})
            self.ledger.write(rows)
        self.spend(4.3)
        with self.assertRaises(CloudStop) as raised:
            self.admit(0.8)
        self.assertIn("exceeds the 5 CNY cap", str(raised.exception))

    def test_budget_cny_is_coordinator_only_like_grant(self):
        a = cv.parse_args(["--grant", "kylezh/x", "--budget-cny", "5"])
        self.assertEqual((a.grant, a.budget_cny), ("kylezh/x", 5.0))
        for argv in (["--budget-cny", "5"], ["--grant", "x", "--budget-cny", "0"], ["--grant", "x", "--budget-cny", "31"]):
            with self.assertRaises(SystemExit), contextlib.redirect_stderr(io.StringIO()):
                cv.parse_args(argv)
        worktree = mock.patch.object(cv, "git", side_effect=lambda *args: {
            "rev-parse --git-dir": ".git/worktrees/w", "rev-parse --git-common-dir": ".git"}[" ".join(args)])
        worktree.start()
        self.addCleanup(worktree.stop)
        with self.assertRaises(CloudStop) as raised:
            cv.run_checked(cv.parse_args(["--grant", "kylezh/x", "--budget-cny", "5"]), cv.Cancel())
        self.assertEqual(raised.exception.code, 25)
        self.assertIn("coordinator-only", str(raised.exception))
        self.assertEqual(self.rows(), [])


    def test_more_than_two_cheap_launches_succeed_in_12h_while_spend_cap_still_refuses(self):
        a = self.args()
        for i in range(5):
            with self.ledger.launch("worker", a, OFFER) as entry:
                entry["instance"] = f"ins-{i}"
        self.assertEqual(self.ledger.recent_launches("worker"), 5)
        # 5 * 0.16 = 0.80 CNY used; adding 4.50 CNY crosses the 5 CNY cap.
        with self.assertRaises(CloudStop) as raised:
            self.admit(4.5)
        self.assertEqual(raised.exception.code, 25)
        self.assertIn("exceeds the 5 CNY cap", str(raised.exception))


class BareHubCoordinator(testkit.GuardedTestCase):
    """Bare-repository worktree pools have no non-bare main worktree, so
    coordinator operations require --coordinator-hub (or GIT_DIR pointing to
    the bare common directory) and stay refused for ordinary linked-worktree
    invocations and non-bare linked worktrees."""

    def setUp(self):
        import subprocess
        self.subprocess = subprocess
        d = tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        self.dir = d.name
        seed = os.path.join(self.dir, "seed")
        subprocess.run(["git", "init", "-qb", "main", seed], check=True)
        subprocess.run(["git", "-C", seed, "-c", "user.email=fixture@example.com",
                        "-c", "user.name=Fixture", "commit", "--allow-empty", "-qm", "Initial"], check=True)
        # Bare hub + linked worktree
        self.hub = os.path.join(self.dir, "hub.git")
        subprocess.run(["git", "clone", "--bare", "-q", seed, self.hub], check=True)
        self.bare_wt = os.path.join(self.dir, "bare-wt")
        subprocess.run(["git", "-C", self.hub, "worktree", "add", "-q", "-b", "feature/shard", self.bare_wt], check=True)
        # Standard non-bare repo + linked worktree
        self.std_main = os.path.join(self.dir, "std-main")
        subprocess.run(["git", "clone", "-q", seed, self.std_main], check=True)
        self.std_wt = os.path.join(self.dir, "std-wt")
        subprocess.run(["git", "-C", self.std_main, "worktree", "add", "-q", "-b", "feature/worker", self.std_wt], check=True)

    def _patch_repo(self, workdir, extra_env=None):
        def fake_git(*args, cwd=workdir, check=True, strip=True):
            env = {k: v for k, v in os.environ.items() if k not in ("GIT_DIR", "GIT_WORK_TREE")}
            if extra_env:
                env.update(extra_env)
            p = self.subprocess.run(["git", *args], cwd=cwd, env=env, text=True, check=check, capture_output=True)
            return p.stdout.strip() if strip else p.stdout
        stack = contextlib.ExitStack()
        stack.enter_context(mock.patch.object(cv, "ROOT", workdir))
        stack.enter_context(mock.patch.object(cv, "git", side_effect=fake_git))
        stack.enter_context(mock.patch.object(cloud_common, "git", side_effect=fake_git))
        stack.enter_context(mock.patch.object(cv, "log"))
        stack.enter_context(mock.patch.object(cv, "warning"))
        return stack

    def test_known_bad_bare_hub_linked_worktree_refuses_without_coordinator_hub(self):
        with self._patch_repo(self.bare_wt):
            for argv in (["--grant", "feature/shard"],
                         ["--budget-override", "urgent rerun"],
                         ["--provider", "tencent", "--cleanup", "--prune-sg"]):
                with self.subTest(argv=argv), self.assertRaises(CloudStop) as raised:
                    cv.run_checked(cv.parse_args(argv), cv.Cancel())
                self.assertEqual(raised.exception.code, 25)
                self.assertIn("coordinator-only", str(raised.exception))

    def test_known_bad_non_bare_linked_worktree_cannot_use_coordinator_hub(self):
        with self._patch_repo(self.std_wt):
            for argv in (["--coordinator-hub", "--grant", "feature/worker"],
                         ["--coordinator-hub", "--budget-override", "bypass"],
                         ["--coordinator-hub", "--provider", "tencent", "--cleanup", "--prune-sg"]):
                with self.subTest(argv=argv), self.assertRaises(CloudStop) as raised:
                    cv.run_checked(cv.parse_args(argv), cv.Cancel())
                self.assertEqual(raised.exception.code, 25)
                self.assertIn("bare repository", str(raised.exception))

    def test_control_bare_hub_with_coordinator_hub_authorizes_grant_override_and_prune(self):
        with self._patch_repo(self.bare_wt):
            # 1. --grant writes into the bare common dir's shared ledger.
            rc = cv.run_checked(cv.parse_args(["--coordinator-hub", "--grant", "feature/shard", "--minutes", "180"]), cv.Cancel())
            self.assertEqual(rc, 0)
            ledger_path = os.path.join(os.path.realpath(self.hub), "tlx-cloud-ledger.json")
            with open(ledger_path) as f:
                rows = json.load(f)
            self.assertEqual((rows[-1]["owner"], rows[-1]["minutes"]), ("feature/shard", 180))
            # 2. --budget-override passes coordinator check.
            cv.check_override("approved bare-hub override", coordinator_hub=True)
            # 3. --cleanup --prune-sg succeeds under the shared lock when idle.
            provider = mock.Mock(all_regions=["ap-shanghai"])
            provider.name = "tencent"
            provider.check_account.return_value = "qcs::cam:100000000001:uin/100000000002"
            provider.leftovers.return_value = []
            with mock.patch.object(cv, "make_provider", return_value=provider):
                rc = cv.run_checked(cv.parse_args(["--coordinator-hub", "--provider", "tencent", "--cleanup", "--prune-sg"]), cv.Cancel())
            self.assertEqual(rc, 0)
            provider.prune_ssh_rules.assert_called_once_with(["ap-shanghai"])

    def test_control_git_dir_pointing_to_bare_hub_works_even_with_unborn_head(self):
        # Point bare HEAD at an unborn branch to ensure --grant and --prune-sg never crash on bare HEAD.
        self.subprocess.run(["git", "--git-dir", self.hub, "symbolic-ref", "HEAD", "refs/heads/unborn"], check=True)
        with self._patch_repo(self.bare_wt, extra_env={"GIT_DIR": self.hub}):
            rc = cv.run_checked(cv.parse_args(["--grant", "feature/shard", "--minutes", "120"]), cv.Cancel())
            self.assertEqual(rc, 0)
            provider = mock.Mock(all_regions=["ap-shanghai"])
            provider.name = "tencent"
            provider.check_account.return_value = "qcs::cam:100000000001:uin/100000000002"
            provider.leftovers.return_value = []
            with mock.patch.object(cv, "make_provider", return_value=provider):
                rc = cv.run_checked(cv.parse_args(["--provider", "tencent", "--cleanup", "--prune-sg"]), cv.Cancel())
            self.assertEqual(rc, 0)
            provider.prune_ssh_rules.assert_called_once_with(["ap-shanghai"])

    def test_bare_check_fails_closed_on_git_error(self):
        with mock.patch.object(cv, "git", side_effect=["/fake/hub.git/worktrees/w", "/fake/hub.git",
                                                        self.subprocess.CalledProcessError(128, ["git"])]):
            with self.assertRaises(CloudStop) as raised:
                cv.check_coordinator(coordinator_hub=True)
            self.assertEqual(raised.exception.code, 25)


if __name__ == "__main__":
    unittest.main()
