#!/usr/bin/env python3
"""Unit tests of the pure parts of scripts/cloud_verify.py (no cloud calls).

usage: python3 scripts/tests/test_cloud_verify.py [-v]
"""
import ast, base64, builtins, contextlib, datetime, functools, io, json, os, shutil, signal, socket, subprocess, sys, tempfile, time, unittest
from unittest import mock

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from cloud import cloud_aliyun
from cloud import cloud_aws
from cloud import cloud_common
from cloud import cloud_tencent
from cloud import cloud_tencent_selfterm
import cloud_verify
import testkit
from cloud import allowlist as cloud_allowlist, remote as cloud_remote, session as cloud_session, setup as cloud_setup
from cloud.cloud_common import Offer, auto_release_time, cargo_config, deadman_user_data, latest_prices, rank_offers, rust_script

UTC = datetime.timezone.utc

# Fake identities: the tests never read the real cloud config.
FAKE_CONFIG = {
    "aws": {"account": "123456789012", "profile": "tlx-test"},
    "aliyun": {"arn": "acs:ram::1234567890123456:user/tlx", "profile": "tlx-no-such-profile-for-tests"},
    "tencent": {"arn": "qcs::cam:100000000001:uin/100000000002", "profile": "tlx-test", "selfterm_role": "tlx-verify-selfterm"},
}
_config_dir = None
_env_patch = None


def read_source(name):
    """The text of a harness script, read with the file closed: asserting on the
    source is how a pure test locks an ordering that a mock cannot observe, and
    a leaked handle only shows up as a ResourceWarning in a full-suite run."""
    with open(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), name), encoding="utf-8") as f:
        return f.read()


def write_config(directory, cfg, name="cloud.json"):
    path = os.path.join(directory, name)
    with open(path, "w", encoding="utf-8") as f:
        f.write(cfg if isinstance(cfg, str) else json.dumps(cfg))
    return path


def setUpModule():
    global _config_dir, _env_patch
    _config_dir = tempfile.TemporaryDirectory()
    _env_patch = mock.patch.dict(os.environ, {cloud_common.CONFIG_ENV: write_config(_config_dir.name, FAKE_CONFIG)})
    _env_patch.start()


def tearDownModule():
    _env_patch.stop()
    _config_dir.cleanup()


class CliTransport(unittest.TestCase):
    def calls(self):
        return [
            (lambda: cloud_aliyun.aliyun("ecs", "DescribeInstances", "cn-hangzhou", "--PageSize", 100),
             ["aliyun", "ecs", "DescribeInstances", "--profile", FAKE_CONFIG["aliyun"]["profile"],
              "--region", "cn-hangzhou", "--RegionId", "cn-hangzhou", "--PageSize", "100"], cloud_aliyun.AliyunError),
            (lambda: cloud_tencent.tccli("cvm", "DescribeInstances", "ap-shanghai", Limit=100, Filters=[]),
             ["tccli", "cvm", "DescribeInstances", "--profile", "tlx-test", "--region", "ap-shanghai",
              "--Limit", "100", "--Filters", "[]"], cloud_tencent.TencentError),
        ]

    def test_full_argv_capture_and_environment(self):
        from cloud import transport
        for call, argv, _ in self.calls():
            with self.subTest(argv=argv), mock.patch.dict(os.environ, {
                    "https_proxy": "secret", "ALIYUN_TOKEN": "secret", "ALICLOUD_KEY": "secret",
                    "ALIBABA_CLOUD_KEY": "secret", "TENCENTCLOUD_SECRET_ID": "secret", "QCLOUD_KEY": "secret"}), \
                    mock.patch.object(transport.subprocess, "run", return_value=mock.Mock(returncode=0, stdout='{"ok":true}')) as run:
                self.assertEqual(call(), {"ok": True})
                run.assert_called_once()
                args, kw = run.call_args
                self.assertEqual(args, (argv,))
                self.assertEqual({k: kw[k] for k in ("capture_output", "text", "timeout")},
                                 {"capture_output": True, "text": True, "timeout": 120})
                self.assertNotIn("https_proxy", kw["env"])
                prefixes = ("ALIYUN_", "ALICLOUD_", "ALIBABA_CLOUD_") if argv[0] == "aliyun" else ("TENCENTCLOUD_", "QCLOUD_")
                self.assertFalse(any(k.startswith(prefixes) for k in kw["env"]))
                self.assertEqual(kw["env"][cloud_common.CONFIG_ENV], os.environ[cloud_common.CONFIG_ENV])

    def test_real_cli_child_rejects_bad_json_without_cloud_access(self):
        # Exercise the actual subprocess boundary with a local executable only.
        import pathlib
        with tempfile.TemporaryDirectory() as directory:
            for call, argv, _ in self.calls():
                executable = pathlib.Path(directory, argv[0])
                receipt = pathlib.Path(directory, "receipt.json")
                executable.write_text(
                    "#!" + sys.executable + "\nimport json, os, sys\n"
                    "with open(" + repr(str(receipt)) + ", 'w') as f:\n"
                    "    json.dump({'argv': sys.argv, 'cwd': os.getcwd(), 'proxy': os.environ.get('https_proxy')}, f)\n"
                    "print('invalid JSON')\n", encoding="utf-8")
                executable.chmod(0o700)
                with mock.patch.dict(os.environ, {"PATH": directory, "https_proxy": "secret"}):
                    with self.assertRaises(json.JSONDecodeError):
                        call()
                recorded = json.loads(receipt.read_text())
                self.assertEqual(recorded, {"argv": [str(executable), *argv[1:]], "cwd": os.getcwd(), "proxy": None})
                self.assertNotEqual(recorded["argv"], [str(executable), *argv[2:]])

    def test_missing_timeout_bad_json_empty_and_provider_errors(self):
        from cloud import transport
        for call, argv, error in self.calls():
            for raised, expected in [(FileNotFoundError(), cloud_common.AccountError),
                                     (transport.subprocess.TimeoutExpired(argv, 120), cloud_common.InfraError)]:
                with self.subTest(argv=argv, raised=raised), mock.patch.object(transport.subprocess, "run", side_effect=raised):
                    with self.assertRaises(expected):
                        call()
            for stdout, expected in [("", {}), ("  ", {})]:
                with mock.patch.object(transport.subprocess, "run", return_value=mock.Mock(returncode=0, stdout=stdout)):
                    self.assertEqual(call(), expected)
            with mock.patch.object(transport.subprocess, "run", return_value=mock.Mock(returncode=0, stdout="invalid")):
                with self.assertRaises(json.JSONDecodeError):
                    call()
            with mock.patch.object(transport.subprocess, "run", return_value=mock.Mock(returncode=1, stdout="bad", stderr=" request")):
                with self.assertRaises(error) as caught:
                    call()
                self.assertEqual(caught.exception.code, "CliError")
                self.assertEqual(caught.exception.message, "bad request")


class ProviderContract(unittest.TestCase):
    def test_three_provider_surface_and_arch_arguments(self):
        import inspect
        from cloud.protocol import Provider
        for cls in (cloud_aws.AwsProvider, cloud_aliyun.AliyunProvider, cloud_tencent.TencentProvider):
            with self.subTest(provider=cls.name):
                provider = cls()
                self.assertIsInstance(provider, Provider)
                for arch in ("x86_64", "arm64"):
                    self.assertTrue(provider.default_types(arch, tier="quick"))
                    inspect.signature(provider.offers).bind(types=["type"], arch=arch, regions=["region"])
                    inspect.signature(provider.describe_plan).bind(offer=Offer(1, "region", "zone", "type"), arch=arch)
                    inspect.signature(provider.launch).bind(m=object(), ips=[], fresh_key=False, max_minutes=30, arch=arch)
                inspect.signature(provider.leftovers).bind(regions=["region"], owner="branch")
                # The operator-IP allowlist surface every provider must answer
                # (cloud/allowlist.py) is part of the contract, not optional.
                inspect.signature(provider.instance_state).bind(m=object())
                inspect.signature(provider.allow_ssh).bind(m=object(), ips=["1.2.3.4"])
                inspect.signature(provider.allow_hint).bind(m=object(), ips=["1.2.3.4"])

    def test_owner_filters_for_all_three_providers(self):
        aws = cloud_aws.AwsProvider()
        ec2 = mock.Mock()
        ec2.describe_instances.return_value = {"Reservations": []}
        with mock.patch.object(aws, "ec2", return_value=ec2):
            self.assertEqual(aws.leftovers(["r"], owner="branch"), [])
        ec2.describe_instances.assert_called_once_with(Filters=[
            {"Name": "tag:tlx-owner", "Values": ["branch"]}, {"Name": "tag:Project", "Values": ["tlx"]},
            {"Name": "instance-state-name", "Values": ["pending", "running", "stopping", "stopped"]}])
        with mock.patch.object(cloud_aliyun, "aliyun", return_value={}) as cli:
            self.assertEqual(cloud_aliyun.AliyunProvider().leftovers(["r"], owner="branch"), [])
        cli.assert_called_once_with("ecs", "DescribeInstances", "r", "--Tag.1.Key", "Project", "--Tag.1.Value", "tlx",
                                    "--Tag.2.Key", "Owner", "--Tag.2.Value", "branch", "--PageSize", 100, "--PageNumber", 1)
        with mock.patch.object(cloud_tencent, "tccli", return_value={}) as cli:
            self.assertEqual(cloud_tencent.TencentProvider().leftovers(["r"], owner="branch"), [])
        cli.assert_called_once_with("cvm", "DescribeInstances", "r", Filters=[
            {"Name": "tag:tlx-project", "Values": ["tlx"]}, {"Name": "tag:tlx-owner", "Values": ["branch"]}], Limit=100, Offset=0)


class BenchmarkPreflight(unittest.TestCase):
    def test_unknown_profile_model_is_rejected_before_cloud_access(self):
        with self.assertRaises(SystemExit):
            cloud_verify.parse_args(["--bench", "profile --models ext/ccf/MCccfraft", "--dry-run"])

    def test_profile_models_are_resolved_without_running_them(self):
        with mock.patch("benchmarking.bench_profile.resolve", return_value={}) as resolve:
            cloud_verify.parse_args(["--bench", "profile --models ext/ccf/MCccfraft_1C2N --workers 1,16 --extra=-tlc"])
        resolve.assert_called_once_with(["ext/ccf/MCccfraft_1C2N"])

    def test_an_unknown_bench_subcommand_is_refused_at_the_selector_stage(self):
        """Fail-before evidence: the prelaunch smoke refused this one.

        `benchmarking.bench_smoke.preflight` brings target/release/tlx up to date (and, for a
        census, runs a workspace Clippy) before it looks at the subcommand, so
        `--bench "repr_check --oracle"` was reported as "prelaunch bench smoke
        refused" only after minutes of local work and after a launcher had
        already been chosen (H-03 item 8). The selector stage now refuses it, and
        the refusal names the subcommands the smoke can run.
        """
        with contextlib.redirect_stderr(io.StringIO()) as err:
            with self.assertRaises(SystemExit) as raised:
                cloud_verify.parse_args(["--bench", "repr_check --oracle", "--dry-run"])
        self.assertEqual(raised.exception.code, 2)
        self.assertIn("is not a benchmark the prelaunch smoke can run", err.getvalue())
        self.assertIn("coverage", err.getvalue())

    def test_bad_options_of_a_real_subcommand_are_refused_too(self):
        """The smoke also builds before it parses the options, so a flag typo
        costs the same local work as a wrong subcommand."""
        with contextlib.redirect_stderr(io.StringIO()) as err:
            with self.assertRaises(SystemExit) as raised:
                cloud_verify.parse_args(["--bench", "run --oracle x", "--dry-run"])
        self.assertEqual(raised.exception.code, 2)
        self.assertIn("refused by bench.py's own parser", err.getvalue())

    def test_every_subcommand_the_smoke_runs_still_parses(self):
        from benchmarking import bench_smoke
        for command in ("run --tlc", "table", "ab --bin a=x --bin b=y --models M",
                        "coverage --dynamic --bin target/release/tlx", "disk --models M"):
            with self.subTest(command=command):
                self.assertIn(command.split()[0], bench_smoke.MEASURE_COMMANDS)
                with contextlib.redirect_stderr(io.StringIO()):
                    parsed = cloud_verify.parse_args(["--bench", command])
                self.assertEqual(parsed.bench, [command])

    def test_the_documented_before_after_pair_parses(self):
        argv = ["--bench-bin", "before=HEAD~1",
                "--bench", "coverage --dynamic --bin target/bench-bins/before/tlx",
                "--bench", "coverage --dynamic --bin target/release/tlx"]
        parsed = cloud_verify.parse_args(argv)
        self.assertEqual(len(parsed.bench), 2)
        self.assertEqual(len(parsed.bench_bins), 1)


class CloudConfig(unittest.TestCase):
    def with_config(self, cfg):
        d = tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        return mock.patch.dict(os.environ, {cloud_common.CONFIG_ENV: write_config(d.name, cfg)})

    def refusal(self, make):
        with self.assertRaises(cloud_common.CloudStop) as cm:
            make()
        return str(cm.exception)

    def test_loads_the_configured_identity(self):
        self.assertEqual(cloud_common.cloud_identity("tencent"), FAKE_CONFIG["tencent"])
        self.assertEqual(cloud_aws.AwsProvider().account, "123456789012")

    def test_missing_file_refuses_every_provider(self):
        with mock.patch.dict(os.environ, {cloud_common.CONFIG_ENV: "/nonexistent/tlx-cloud.json"}):
            for make in (cloud_aws.AwsProvider, cloud_aliyun.AliyunProvider, cloud_tencent.TencentProvider):
                msg = self.refusal(make)
                self.assertIn("no cloud config /nonexistent/tlx-cloud.json; refusing to run", msg)
                self.assertIn("docs/cloud-verification.md", msg)

    def test_missing_entry_or_field_refuses(self):
        with self.with_config({"aws": FAKE_CONFIG["aws"]}):
            msg = self.refusal(cloud_tencent.TencentProvider)
            self.assertIn("no 'tencent' entry", msg)
            self.assertIn('"selfterm_role": "tlx-verify-selfterm"', msg)   # the example entry
        with self.with_config({"aliyun": {"profile": "tlx"}}):
            self.assertIn("lacks arn", self.refusal(cloud_aliyun.AliyunProvider))
        with self.with_config({"aws": {"account": "", "profile": "tlx"}}):
            self.assertIn("lacks account", self.refusal(cloud_aws.AwsProvider))
        with self.with_config("{not json"):
            self.assertIn("cannot read cloud config", self.refusal(cloud_aws.AwsProvider))

    def test_aws_checks_the_configured_account(self):
        p = cloud_aws.AwsProvider()
        sts = mock.Mock()
        p._sess = mock.Mock(client=mock.Mock(return_value=sts))
        sts.get_caller_identity.return_value = {"Account": "210987654321", "Arn": "arn:aws:iam::210987654321:user/x"}
        msg = self.refusal(p.check_account)
        self.assertIn("is account ***321, expected ***012", msg)   # masked: no account number in a log
        self.assertNotIn("123456789012", msg)
        sts.get_caller_identity.return_value = {"Account": "123456789012", "Arn": "arn:aws:iam::123456789012:user/tlx"}
        self.assertEqual(p.check_account(), "account 123456789012 (arn:aws:iam::123456789012:user/tlx)")


class AutoReleaseTime(unittest.TestCase):
    def test_rounds_up_to_the_minute(self):
        now = datetime.datetime(2026, 10, 4, 15, 25, 26, tzinfo=UTC)
        self.assertEqual(auto_release_time(now, 90), "2026-10-04T16:56:00Z")

    def test_whole_minute_kept(self):
        now = datetime.datetime(2026, 10, 4, 15, 25, 0, tzinfo=UTC)
        self.assertEqual(auto_release_time(now, 90), "2026-10-04T16:55:00Z")

    def test_at_least_30_minutes_plus_margin(self):
        now = datetime.datetime(2026, 10, 4, 15, 25, 0, tzinfo=UTC)
        self.assertEqual(auto_release_time(now, 5), "2026-10-04T15:57:00Z")

    def test_converts_to_utc_and_crosses_midnight(self):
        cst = datetime.timezone(datetime.timedelta(hours=8))
        now = datetime.datetime(2026, 10, 5, 7, 30, 1, tzinfo=cst)   # 23:30:01 UTC on the 4th
        self.assertEqual(auto_release_time(now, 60), "2026-10-05T00:31:00Z")


class Prices(unittest.TestCase):
    def rec(self, zone, price, hour, itype="t"):
        return {"zone": zone, "itype": itype, "price": price, "time": datetime.datetime(2026, 10, 4, hour, tzinfo=UTC)}

    def test_latest_past_record_per_zone(self):
        now = datetime.datetime(2026, 10, 4, 15, 30, tzinfo=UTC)
        recs = [self.rec("a", 0.5, 13), self.rec("a", 0.47, 15), self.rec("a", 0.9, 16),   # 16:00 is in the future
                self.rec("b", 0.6, 14), self.rec("b", 0.55, 12)]
        self.assertEqual(latest_prices(recs, now), {("a", "t"): 0.47, ("b", "t"): 0.6})

    def test_only_future_records_take_the_earliest(self):
        now = datetime.datetime(2026, 10, 4, 10, tzinfo=UTC)
        self.assertEqual(latest_prices([self.rec("a", 0.9, 13), self.rec("a", 0.8, 12)], now), {("a", "t"): 0.8})

    def test_types_are_separate(self):
        now = datetime.datetime(2026, 10, 4, 15, tzinfo=UTC)
        self.assertEqual(latest_prices([self.rec("a", 1, 14, "x"), self.rec("a", 2, 14, "y")], now),
                         {("a", "x"): 1.0, ("a", "y"): 2.0})

    def test_rank_cheapest_first_deprioritized_last(self):
        offers = [Offer(0.67, "r", "b", "g8y", 16), Offer(0.47, "r", "k", "c8y", 16), Offer(0.47, "r", "b", "c8y", 16),
                  Offer(0.10, "r", "j", "c8y", 16, deprioritized=True), Offer(0.47, "r", "a", "big", 64)]
        self.assertEqual([(o.zone, o.itype) for o in rank_offers(offers)],
                         [("b", "c8y"), ("k", "c8y"), ("a", "big"), ("b", "g8y"), ("j", "c8y")])


class LaunchCleanup(unittest.TestCase):
    def test_other_live_launch_of_the_same_owner_is_not_a_leak(self):
        rows = [("region", "own-launch", "TERMINATING"), ("region", "concurrent-launch", "RUNNING")]
        self.assertEqual(cloud_common.active_launch_leftovers(rows, {"own-launch"}), [])

    def test_current_launch_still_running_is_a_leak(self):
        row = ("region", "own-launch", "RUNNING")
        self.assertEqual(cloud_common.active_launch_leftovers([row], {"own-launch"}), [row])

    def test_failed_attempts_are_checked_with_the_successful_launch(self):
        rows = [("region", "failed-attempt", "STOPPED"), ("region", "successful-launch", "TERMINATED")]
        self.assertEqual(cloud_common.active_launch_leftovers(rows, {"failed-attempt", "successful-launch"}), rows[:1])


class Planning(unittest.TestCase):
    def test_sources_auto(self):
        p = cloud_aliyun.AliyunProvider()
        self.assertEqual(cloud_verify.sources(p, "cn-hangzhou", "auto", "auto"), ("mirror", "mirror"))
        self.assertEqual(cloud_verify.sources(p, "cn-hongkong", "auto", "auto"), ("upstream", "upstream"))
        self.assertEqual(cloud_verify.sources(p, "ap-northeast-1", "upload", "vendor"), ("upload", "vendor"))

    def test_mainland(self):
        p = cloud_aliyun.AliyunProvider()
        self.assertEqual([r for r in cloud_aliyun.REGIONS if p.mainland(r)], ["cn-hangzhou", "cn-shanghai", "cn-beijing"])

    def test_verify_args(self):
        a = cloud_verify.parse_args(["--full", "--filter", "DieHard", "--strict",
                                     "--suites", "build,corpus-compile"])
        self.assertEqual(a.provider, "aliyun")
        # --suites must reach the forwarded verify.py argv: a --bench run once
        # dropped it and a requested build suite silently never ran.
        self.assertEqual(cloud_verify.verify_args(a, "abc", 15),
                         ["python3", "scripts/verify.py", "abc", "--full", "-j", "15",
                          "--suites", "build,corpus-compile", "--filter", "DieHard", "--strict"])
        self.assertEqual(cloud_verify.parse_args([]).tier, "quick")

    def test_disk_gb_argument(self):
        self.assertIsNone(cloud_verify.parse_args([]).disk_gb)
        self.assertEqual(cloud_verify.parse_args(["--disk-gb", "400"]).disk_gb, 400)
        with self.assertRaises(SystemExit):
            cloud_verify.parse_args(["--disk-gb", "5"])

    def test_max_account_slots_argument(self):
        self.assertIsNone(cloud_verify.parse_args([]).max_account_slots)
        self.assertEqual(cloud_verify.parse_args(["--max-account-slots", "8"]).max_account_slots, 8)
        with self.assertRaises(SystemExit):
            cloud_verify.parse_args(["--max-account-slots", "0"])

    def test_then_args(self):
        a = cloud_verify.parse_args(["--full", "--then", "--suites build,corpus-compile --env TLX_JIT=0",
                                     "--then", "old --suites corpus-compile --cold-cache", "--then", "--quick -j 4"])
        resolve = lambda r: "sha-" + r
        self.assertEqual(cloud_verify.then_args(a, a.then[0], "abc", resolve, 63),
                         ("abc", ["python3", "scripts/verify.py", "abc", "--full", "-j", "63",
                                  "--suites", "build,corpus-compile", "--env", "TLX_JIT=0"]))
        self.assertEqual(cloud_verify.then_args(a, a.then[1], "abc", resolve, 63),
                         ("sha-old", ["python3", "scripts/verify.py", "sha-old", "--full", "-j", "63",
                                      "--suites", "corpus-compile", "--cold-cache"]))
        self.assertEqual(cloud_verify.then_args(a, a.then[2], "abc", resolve, 63),
                         ("abc", ["python3", "scripts/verify.py", "abc", "--quick", "-j", "4"]))
        # A bench run takes `--then` passes too: they run verify.py on the same
        # instance after the benchmark commands (2026-10-10: the natural "run the
        # bench suite, then collect the verify.py results" needed a second launch).
        a = cloud_verify.parse_args(["--quick", "--bench", "run --tlc", "--then", "--suites build"])
        self.assertEqual(a.bench, ["run --tlc"])
        plan = cloud_setup.Plan(a=a, provider=mock.Mock(currency="CNY", min_lifetime_minutes=0,
                                                        label_suffix="fake"), owner="worker",
                                ledger=None, admitter=None, offers=[Offer(0.5, "r", "z", "fake", 2)], jobs=3,
                                sha="a" * 40, label="abc1234", bins=[], then_shas=[], resolve=lambda r: "sha-" + r,
                                vargs=cloud_setup.verify_args(a, "a" * 40, 3), rust="upstream", crates="upstream",
                                toolchain="1.90", proxy=None, local_dir="/tmp", types=["fake"], tlc=True)
        self.assertIn("[bench.py run --tlc]", plan.work())
        self.assertIn("then [scripts/verify.py " + "a" * 40 + " --quick -j 3 --suites build]", plan.work())

    def test_run_args(self):
        p = cloud_aliyun.AliyunProvider()

        class M:
            offer = Offer(0.47, "cn-hangzhou", "cn-hangzhou-j", "ecs.c8y.4xlarge", 16)
            token = "tok"
        args = [str(x) for x in p.run_args(M(), "img", "sg-1", "vsw-1", 45, now=datetime.datetime(2026, 10, 4, 15, 0, 30, tzinfo=UTC))]
        kv = dict(zip(args[::2], args[1::2]))
        self.assertEqual(kv["--SpotStrategy"], "SpotAsPriceGo")
        self.assertEqual(kv["--InstanceChargeType"], "PostPaid")
        self.assertEqual(kv["--AutoReleaseTime"], "2026-10-04T15:46:00Z")
        self.assertEqual((kv["--Tag.1.Key"], kv["--Tag.1.Value"]), ("Project", "tlx"))
        self.assertEqual((kv["--Tag.2.Key"], kv["--Tag.2.Value"]), ("tlx-run", "tok"))
        ud = base64.b64decode(kv["--UserData"]).decode()
        self.assertIn("shutdown -h +45\n", ud)
        self.assertIn("-p 443 -p 2222", ud)

    def test_parse_cli_errors(self):
        js = ('{"schemaVersion":"v1","message":"Your account does not have enough balance to order postpaid product.",'
              '"error_code":"InvalidAccountStatus.NotEnoughBalance","status_code":403,"request_id":"X"}')
        self.assertEqual(cloud_aliyun.parse_error("ERROR: " + js),
                         ("InvalidAccountStatus.NotEnoughBalance", "Your account does not have enough balance to order postpaid product."))
        self.assertEqual(cloud_aliyun.parse_error("ERROR: SDK.ServerError\nErrorCode: OperationDenied.NoStock\nMessage: sold out\n"),
                         ("OperationDenied.NoStock", "sold out"))

    def test_missing_profile_is_an_account_error(self):
        # FAKE_CONFIG's aliyun profile does not exist.
        with self.assertRaises(cloud_common.AccountError):
            cloud_aliyun.AliyunProvider().check_account()


class FakeTccli:
    """Stands in for cloud.cloud_tencent.tccli: records the calls, answers from
    `responses` ({api: dict, exception or callable(params)})."""

    def __init__(self, responses):
        self.responses, self.calls = responses, []

    def __call__(self, product, api, region=None, **params):
        self.calls.append((api, region, params))
        r = self.responses.get(api, {})
        if isinstance(r, Exception):
            raise r
        return r(params) if callable(r) else r

    def apis(self):
        return [c[0] for c in self.calls]


class Tencent(unittest.TestCase):
    def setUp(self):
        self._tccli = cloud_tencent.tccli

    def tearDown(self):
        cloud_tencent.tccli = self._tccli

    def fake(self, responses):
        f = cloud_tencent.tccli = FakeTccli(responses)
        return f

    def machine(self, market="spot"):
        class M:
            offer = Offer(0.1584, "ap-shanghai", "ap-shanghai-5", "SA5.4XLARGE32", 16, market=market)
            token = "tok"
            region = "ap-shanghai"
            id = None
        return M()

    def test_parse_cli_errors(self):
        out = ("usage: tccli [options] ...\n[TencentCloudSDKException] code:ResourcesSoldOut.SpecifiedInstanceType "
               "message:The specified type is sold out. requestId:abc-123\n")
        self.assertEqual(cloud_tencent.parse_error(out), ("ResourcesSoldOut.SpecifiedInstanceType", "The specified type is sold out."))
        self.assertEqual(cloud_tencent.parse_error("boom")[0], "CliError")

    def test_fatal_errors(self):
        E = cloud_tencent.TencentError
        self.assertTrue(E("OperationDenied.RiskControl", "x", []).fatal)
        self.assertTrue(E("FailedOperation", "account under audit", []).fatal)
        self.assertTrue(E("UnauthorizedOperation.Forbidden", "x", []).fatal)
        self.assertFalse(E("ResourcesSoldOut.SpecifiedInstanceType", "sold out", []).fatal)
        # Each kind has its own message: a missing permission is not a blocked account.
        self.assertEqual(E("OperationDenied.RiskControl", "x", []).kind, "risk")
        denied = E("AuthFailure.UnauthorizedOperation", "you are not authorized to perform operation (cam:PassRole)", [])
        self.assertEqual(denied.kind, "denied")
        self.assertIn("CAM policy", denied.hint)
        self.assertNotIn("blocked", denied.hint)
        self.assertEqual(E("UnauthorizedOperation.CamNoAuth", "x", []).kind, "denied")
        self.assertEqual(E("AuthFailure.SignatureFailure", "x", []).kind, "credentials")
        self.assertIn("credentials", E("AuthFailure.SecretIdNotFound", "x", []).hint)
        self.assertEqual(E("InvalidParameterCombination", "x", []).hint, "")

    def test_cli_args(self):
        self.assertEqual(cloud_tencent.cli_args({"InstanceType": "SA5.4XLARGE32", "InstanceCount": 1, "DryRun": True,
                                                 "Placement": {"Zone": "z"}}),
                         ["--InstanceType", "SA5.4XLARGE32", "--InstanceCount", "1", "--DryRun", "true", "--Placement", '{"Zone":"z"}'])

    def test_system_disk_size_is_configurable(self):
        # A disk-backed TLC BFS queue outgrew the fixed 200 GB system disk on
        # kraft_kip_996_small (2026-10-09, ~950 MB/min, 156 GB); --disk-gb must
        # reach RunInstances, and the default must stay the provider constant.
        p = cloud_tencent.TencentProvider()
        m = self.machine()
        args = (m.offer, "img", "sg", "subnet", "vpc", "key", "tok")
        self.assertEqual(p.base_params(*args)["SystemDisk"]["DiskSize"], cloud_tencent.DISK_GB)
        p.disk_gb = 400
        self.assertEqual(p.base_params(*args)["SystemDisk"]["DiskSize"], 400)
        self.assertEqual(p.base_params(*args)["SystemDisk"]["DiskType"], cloud_tencent.DISK_TYPE)

    def test_cli_env_drops_credentials_and_proxies(self):
        old = dict(os.environ)
        os.environ.update(TENCENTCLOUD_SECRET_ID="x", https_proxy="http://p:1")
        try:
            env = cloud_tencent.cli_env()
        finally:
            os.environ.clear()
            os.environ.update(old)
        self.assertNotIn("TENCENTCLOUD_SECRET_ID", env)
        self.assertNotIn("https_proxy", env)

    def test_key_name(self):
        n = cloud_tencent.key_name("ssh-ed25519 AAAA tlx-verify\n")
        self.assertRegex(n, r"^tlx_verify_[0-9a-f]{10}$")
        self.assertLessEqual(len(n), 25)
        self.assertEqual(n, cloud_tencent.key_name("ssh-ed25519 AAAA tlx-verify"))
        self.assertNotEqual(n, cloud_tencent.key_name("ssh-ed25519 BBBB tlx-verify"))

    def test_pick_image(self):
        imgs = [{"ImageId": "img-26", "ImageName": "Ubuntu Server 26.04 LTS 64位", "Architecture": "x86_64"},
                {"ImageId": "img-24", "ImageName": "Ubuntu Server 24.04 LTS 64位", "Architecture": "x86_64"},
                {"ImageId": "img-24u", "ImageName": "Ubuntu Server 24.04 LTS 64位 UEFI版", "Architecture": "x86_64"},
                {"ImageId": "img-app", "ImageName": "OpenCode on Ubuntu24.04", "Architecture": "x86_64"},
                {"ImageId": "img-22", "ImageName": "Ubuntu Server 22.04 LTS 64位", "Architecture": "x86_64"},
                {"ImageId": "img-a22", "ImageName": "Ubuntu 22.04(arm64)", "Architecture": "arm"},
                {"ImageId": "img-a20", "ImageName": "Ubuntu 20.04(arm64)", "Architecture": "arm"}]
        self.assertEqual(cloud_tencent.pick_image(imgs, "x86_64"), ("img-24", "Ubuntu Server 24.04 LTS 64位"))
        self.assertEqual(cloud_tencent.pick_image(imgs, "arm64"), ("img-a22", "Ubuntu 22.04(arm64)"))
        self.assertIsNone(cloud_tencent.pick_image(imgs[3:4], "x86_64"))

    def test_default_types(self):
        p = cloud_tencent.TencentProvider()
        self.assertEqual(p.default_types("x86_64"), ["SA5.4XLARGE32", "SA9.4XLARGE32"])
        self.assertIn("SA9.16XLARGE128", p.default_types("x86_64", "full"))
        self.assertTrue(all(t.startswith("SR1.") for t in p.default_types("arm64")))
        a = cloud_verify.parse_args(["--provider", "tencent", "--on-demand", "--full"])
        self.assertEqual((a.provider, a.on_demand, a.tier), ("tencent", True, "full"))

    def test_spot_run_params(self):
        p = cloud_tencent.TencentProvider()
        p._unit_price[("ap-shanghai-5", "SA5.4XLARGE32")] = 2.64
        r = p.run_params(self.machine(), "img-1", "sg-1", "subnet-1", "vpc-1", "skey-1", 45, "",
                         now=datetime.datetime(2026, 10, 5, 12, 0, 30, tzinfo=UTC))
        self.assertEqual(r["InstanceChargeType"], "SPOTPAID")
        self.assertEqual(r["InstanceMarketOptions"],
                         {"MarketType": "spot", "SpotOptions": {"MaxPrice": "2.6400", "SpotInstanceType": "one-time"}})
        self.assertNotIn("ActionTimer", r)   # refused for spot instances
        self.assertNotIn("CamRoleName", r)
        self.assertEqual(r["Placement"], {"Zone": "ap-shanghai-5", "ProjectId": 0})
        self.assertEqual(r["InternetAccessible"]["InternetChargeType"], "TRAFFIC_POSTPAID_BY_HOUR")
        self.assertEqual(r["LoginSettings"], {"KeyIds": ["skey-1"]})
        self.assertEqual(r["VirtualPrivateCloud"], {"VpcId": "vpc-1", "SubnetId": "subnet-1"})
        self.assertEqual(r["SecurityGroupIds"], ["sg-1"])
        self.assertEqual(r["ClientToken"], "tok")
        # Deadline: 45 min + 5 slack + 1 (rounding) after 12:00:30.
        self.assertEqual(r["TagSpecification"], [{"ResourceType": "instance", "Tags": [
            {"Key": "tlx-project", "Value": "tlx"}, {"Key": "tlx-run", "Value": "tok"}, {"Key": "tlx-owner", "Value": p.owner},
            {"Key": "tlx-deadline", "Value": "20261005T1251Z"}]}])
        self.assertEqual(cloud_tencent.TAGS, [{"Key": "tlx-project", "Value": "tlx"}])
        ud = base64.b64decode(r["UserData"]).decode()
        self.assertIn("shutdown -h +45\n", ud)
        self.assertIn("-p 443 -p 2222", ud)
        self.assertNotIn("tlx-selfterm", ud)

    def test_spot_run_params_with_the_role(self):
        p = cloud_tencent.TencentProvider()
        r = p.run_params(self.machine(), "img-1", "sg-1", "subnet-1", "vpc-1", "skey-1", 45, "tlx-verify-selfterm",
                         now=datetime.datetime(2026, 10, 5, 12, 0, 30, tzinfo=UTC))
        self.assertEqual(r["CamRoleName"], "tlx-verify-selfterm")
        self.assertNotIn("ActionTimer", r)
        self.assertIn({"Key": "tlx-deadline", "Value": "20261005T1256Z"}, r["TagSpecification"][0]["Tags"])
        ud = base64.b64decode(r["UserData"]).decode()
        self.assertTrue(ud.startswith("#!/bin/bash\n"))
        # Self-termination after 45 minutes, the shutdown 5 minutes later.
        self.assertIn("systemd-run --unit=tlx-selfterm --on-active=45min /usr/bin/python3 /usr/local/sbin/tlx-selfterm "
                      "terminate tlx-verify-selfterm\n", ud)
        self.assertIn("shutdown -h +50\n", ud)
        # The script itself, verbatim, in a quoted here-document.
        with open(cloud_tencent.SELFTERM_FILE) as f:
            script = f.read()
        self.assertIn(f"cat > /usr/local/sbin/tlx-selfterm <<'TLX_SELFTERM_EOF'\n{script}TLX_SELFTERM_EOF\n", ud)
        self.assertNotIn("TLX_SELFTERM_EOF", script)
        self.assertLess(len(r["UserData"]), 16 * 1024)   # RunInstances' limit

    def test_on_demand_run_params_carry_the_timer(self):
        p = cloud_tencent.TencentProvider()
        r = p.run_params(self.machine("on-demand"), "img-1", "sg-1", "subnet-1", "vpc-1", "skey-1", 45, "",
                         now=datetime.datetime(2026, 10, 5, 12, 0, 30, tzinfo=UTC))
        self.assertEqual(r["InstanceChargeType"], "POSTPAID_BY_HOUR")
        self.assertNotIn("InstanceMarketOptions", r)
        self.assertEqual(r["ActionTimer"], {"TimerAction": "TerminateInstances", "ActionTime": "2026-10-05T12:46:00Z"})
        # At least 5 minutes ahead (plus the margin).
        self.assertEqual(cloud_tencent.TencentProvider.action_timer(1, datetime.datetime(2026, 10, 5, 12, 0, 0, tzinfo=UTC)),
                         {"TimerAction": "TerminateInstances", "ActionTime": "2026-10-05T12:07:00Z"})

    def test_offers(self):
        def configs(params):
            charge = params["Filters"][0]["Values"][0]
            q = lambda zone, status, cat, disc: {"Zone": zone, "InstanceType": "SA5.4XLARGE32", "InstanceFamily": "SA5", "Cpu": 16,
                                                  "Status": status, "StatusCategory": cat,
                                                  "Price": {"UnitPrice": 2.64, "UnitPriceDiscount": disc}}
            if charge == "SPOTPAID":
                return {"InstanceTypeQuotaSet": [q("z5", "SELL", "EnoughStock", 0.1584), q("z8", "SELL", "UnderStock", 0.1584),
                                                 q("z2", "SOLD_OUT", "WithoutStock", 0.5)]}
            return {"InstanceTypeQuotaSet": [q("z5", "SELL", "EnoughStock", 2.64)]}
        f = self.fake({"DescribeZoneInstanceConfigInfos": configs})
        p = cloud_tencent.TencentProvider()
        offers = p.offers(["SA5.4XLARGE32"], "x86_64", ["ap-shanghai"])
        self.assertEqual([(o.zone, o.price, o.deprioritized, o.market) for o in offers],
                         [("z5", 0.1584, False, "spot"), ("z8", 0.1584, True, "spot")])
        self.assertEqual(f.calls[0][2]["Filters"], [{"Name": "instance-charge-type", "Values": ["SPOTPAID"]},
                                                     {"Name": "instance-type", "Values": ["SA5.4XLARGE32"]}])
        p.on_demand = True
        ranked = rank_offers(p.offers(["SA5.4XLARGE32"], "x86_64", ["ap-shanghai"]))
        self.assertEqual([(o.zone, o.market) for o in ranked], [("z5", "spot"), ("z8", "spot"), ("z5", "on-demand")])
        with self.assertRaises(cloud_common.CloudStop):
            p.offers(["SA5.4XLARGE32"], "arm64", ["ap-shanghai"])

    def test_security_group_rules(self):
        # A launch adds the ports it needs, tags what it writes with its owner,
        # and leaves every rule it does not own where it is - including one
        # that carries no owner tag at all (SharedSecurityGroup has the
        # per-owner cases).
        policies = {"SecurityGroupPolicySet": {
            "Ingress": [{"PolicyIndex": 0, "Protocol": "TCP", "Port": "22", "CidrBlock": "1.2.3.4/32", "Action": "ACCEPT"},
                        {"PolicyIndex": 1, "Protocol": "TCP", "Port": "22", "CidrBlock": "9.9.9.9/32", "Action": "ACCEPT"}],
            "Egress": []}}
        f = self.fake({"DescribeSecurityGroups": {"SecurityGroupSet": [{"SecurityGroupId": "sg-1"}]},
                       "DescribeSecurityGroupPolicies": policies})
        p = cloud_tencent.TencentProvider()
        p.owner = "test-owner"
        self.assertEqual(p.ensure_security_group("ap-shanghai", ["1.2.3.4"]), "sg-1")
        self.assertEqual(f.apis(), ["DescribeSecurityGroups", "DescribeSecurityGroupPolicies",
                                    "CreateSecurityGroupPolicies", "CreateSecurityGroupPolicies"])
        self.assertEqual([(r["Port"], r["CidrBlock"], r["PolicyDescription"])
                          for r in f.calls[2][2]["SecurityGroupPolicySet"]["Ingress"]],
                         [("2222", "1.2.3.4/32", "cloud_verify:test-owner"),
                          ("443", "1.2.3.4/32", "cloud_verify:test-owner")])
        self.assertEqual(f.calls[3][2]["SecurityGroupPolicySet"]["Egress"][0]["CidrBlock"], "0.0.0.0/0")

    def provider(self):
        p = cloud_tencent.TencentProvider()
        # Explicit owner: the tests must not depend on the checkout having a
        # branch (verify.py runs them in a detached checkout on the cloud).
        p.owner = "test-owner"
        p.ensure_key_pair = lambda region: "skey-1"
        p.ensure_vpc = lambda region: "vpc-1"
        p.ensure_subnet = lambda region, vpc, zone: "subnet-1"
        p.ensure_security_group = lambda region, ips: "sg-1"
        p.image = lambda region, arch, itype: ("img-1", "Ubuntu")
        return p

    def test_fixture_does_not_need_a_branch(self):
        f = self.fake({"GetRole": self.ROLE, "RunInstances": {"InstanceIdSet": ["ins-1"]}})
        real = cloud_tencent.current_owner

        def detached(required=True):
            if required:
                raise cloud_tencent.CloudStop("cloud ownership needs a current git branch", 25)
            return None
        cloud_tencent.current_owner = detached
        try:
            self.provider().launch(self.machine(), ["1.2.3.4"], False, 30, "x86_64")
        finally:
            cloud_tencent.current_owner = real
        self.assertIn("RunInstances", f.apis())

    ROLE = {"RoleInfo": {"RoleName": "tlx-verify-selfterm", "PolicyDocument":
                         '{"version":"2.0","statement":[{"action":"name/sts:AssumeRole","effect":"allow",'
                         '"principal":{"service":["cvm.qcloud.com"]}}]}'}}

    def test_spot_launch_with_the_role(self):
        f = self.fake({"GetRole": self.ROLE, "RunInstances": {"InstanceIdSet": ["ins-1"]}})
        m = self.machine()
        self.provider().launch(m, ["1.2.3.4"], False, 30, "x86_64")
        self.assertEqual((m.id, m.selfterm_role), ("ins-1", "tlx-verify-selfterm"))
        # No timer API call at all (spot instances take none; nothing while PENDING); the
        # provider's dry-run admission of the same request comes first.
        self.assertEqual(f.apis(), ["GetRole", "RunInstances", "RunInstances"])
        self.assertTrue(f.calls[1][2]["DryRun"])
        self.assertNotIn("DryRun", f.calls[2][2])
        self.assertEqual(f.calls[2][2]["CamRoleName"], "tlx-verify-selfterm")

    def test_spot_launch_without_the_role_falls_back_to_the_shutdown(self):
        E = cloud_tencent.TencentError
        for get_role in (E("InvalidParameter.RoleNotExist", "Role not exist.", []),
                         E("AuthFailure.UnauthorizedOperation", "(cam:GetRole)", []),
                         {"RoleInfo": {"PolicyDocument": '{"principal":{"service":["scf.qcloud.com"]}}'}}):
            f = self.fake({"GetRole": get_role, "RunInstances": {"InstanceIdSet": ["ins-1"]}})
            m = self.machine()
            p = self.provider()
            p.launch(m, ["1.2.3.4"], False, 30, "x86_64")
            self.assertEqual((m.id, m.selfterm_role), ("ins-1", ""))
            self.assertNotIn("CamRoleName", f.calls[1][2])
            self.assertIn("billed until it is terminated", p.deadman_warning())
        # The role exists but RunInstances refuses it (no cam:PassRole): launched again without it.
        runs = []

        def run(params):
            if params.get("DryRun"):
                return {}
            runs.append(params)
            if "CamRoleName" in params:
                raise E("AuthFailure.CamRoleNameAuthenticateFailed", "role auth failed", [])
            return {"InstanceIdSet": ["ins-3"]}
        self.fake({"GetRole": self.ROLE, "RunInstances": run})
        m = self.machine()
        self.provider().launch(m, ["1.2.3.4"], False, 30, "x86_64")
        self.assertEqual((m.id, m.selfterm_role, len(runs)), ("ins-3", "", 2))
        self.assertNotEqual(runs[0]["ClientToken"], runs[1]["ClientToken"])

    def test_launch_errors(self):
        E = cloud_tencent.TencentError
        p = self.provider()
        # Sold out: the next offer; risk control, missing permissions: stop, with the right message.
        self.fake({"RunInstances": E("ResourcesSoldOut.SpecifiedInstanceType", "sold out", [])})
        with self.assertRaises(cloud_common.SkipOffer):
            p.launch(self.machine(), ["1.2.3.4"], False, 30, "x86_64")
        self.fake({"RunInstances": E("OperationDenied.RiskControl", "x", [])})
        with self.assertRaisesRegex(cloud_common.InfraError, "risk control"):
            p.launch(self.machine(), ["1.2.3.4"], False, 30, "x86_64")
        self.fake({"RunInstances": E("AuthFailure.UnauthorizedOperation", "not authorized (cvm:RunInstances)", [])})
        with self.assertRaisesRegex(cloud_common.InfraError, "CAM policy") as cm:
            p.launch(self.machine(), ["1.2.3.4"], False, 30, "x86_64")
        self.assertNotIn("blocked", str(cm.exception))

    def test_check_deadman(self):
        p = cloud_tencent.TencentProvider()
        s = p.deadman_script("tlx-verify-selfterm")
        self.assertIn("sudo test -e /run/systemd/shutdown/scheduled", s)
        self.assertIn("systemctl is-active --quiet tlx-selfterm.timer", s)
        self.assertIn("sudo /usr/bin/python3 /usr/local/sbin/tlx-selfterm check tlx-verify-selfterm", s)
        self.assertNotIn("tlx-selfterm", p.deadman_script(""))

        class Proc:
            def __init__(self, rc, out):
                self.returncode, self.stdout, self.stderr = rc, out, ""
        m = self.machine()
        m.id, m.selfterm_role = "ins-1", ""
        m.ssh = lambda script, check=True, capture=False: Proc(0, "")
        p.check_deadman(m)
        # Not armed: an InfraError (the caller then terminates the instance).
        m.ssh = lambda script, check=True, capture=False: Proc(1, "no shutdown scheduled\n")
        with self.assertRaisesRegex(cloud_common.InfraError, "not armed: no shutdown scheduled"):
            p.check_deadman(m)

    def test_expired_and_reap(self):
        now = datetime.datetime(2026, 10, 5, 12, 0, 0, tzinfo=UTC)
        dl = lambda v: [{"Key": "tlx-project", "Value": "tlx"}, {"Key": "tlx-deadline", "Value": v}]
        ex = cloud_tencent.expired
        self.assertTrue(ex({"InstanceState": "STOPPED"}, now))
        self.assertTrue(ex({"InstanceState": "RUNNING", "Tags": dl("20261005T1159Z")}, now))
        self.assertFalse(ex({"InstanceState": "RUNNING", "Tags": dl("20261005T1200Z")}, now))
        self.assertFalse(ex({"InstanceState": "PENDING", "Tags": dl("20261005T1300Z")}, now))
        self.assertFalse(ex({"InstanceState": "RUNNING", "Tags": []}, now))       # (no deadline: --cleanup)
        self.assertFalse(ex({"InstanceState": "TERMINATING", "Tags": dl("20261005T1000Z")}, now))
        self.assertEqual(cloud_tencent.deadline(now, 90, "r"), "20261005T1341Z")
        self.assertEqual(cloud_tencent.deadline(now, 90, ""), "20261005T1336Z")
        insts = [{"InstanceId": "ins-old", "InstanceState": "RUNNING", "Tags": dl("20261005T1100Z")},
                 {"InstanceId": "ins-stopped", "InstanceState": "STOPPED", "Tags": dl("20261005T1300Z")},
                 {"InstanceId": "ins-live", "InstanceState": "RUNNING", "Tags": dl("20261005T1300Z")}]
        f = self.fake({"DescribeInstances": lambda params: {"InstanceSet": [] if "InstanceIds" in params else insts}})
        cloud_tencent.TencentProvider().reap(["ap-shanghai"], now=now)
        self.assertEqual([c[2]["InstanceIds"] for c in f.calls if c[0] == "TerminateInstances"], [["ins-old"], ["ins-stopped"]])

    def test_leftovers_and_terminate(self):
        f = self.fake({"DescribeInstances": lambda params: {"InstanceSet": [] if "InstanceIds" in params else
                                                           [{"InstanceId": "ins-1", "InstanceState": "RUNNING"}]}})
        p = cloud_tencent.TencentProvider()
        self.assertEqual(p.leftovers(["ap-shanghai"]), [("ap-shanghai", "ins-1", "RUNNING")])
        self.assertEqual(f.calls[0][2]["Filters"], [{"Name": "tag:tlx-project", "Values": ["tlx"]}])
        m = self.machine()
        m.id = "ins-1"
        self.assertTrue(p.terminate(m))
        self.assertIn(("TerminateInstances", "ap-shanghai", {"InstanceIds": ["ins-1"]}), f.calls)

    def test_wrong_identity_aborts(self):
        self.fake({"GetCallerIdentity": {"Arn": "qcs::cam:1:uin/2", "Type": "CAMUser"}})
        with self.assertRaises(cloud_common.AccountError):
            cloud_tencent.TencentProvider().check_account()
        self.fake({"GetCallerIdentity": {"Arn": FAKE_CONFIG["tencent"]["arn"], "Type": "CAMUser"}})
        self.assertIn("100000000002", cloud_tencent.TencentProvider().check_account())

    def test_balance_denied_is_reported(self):
        self.fake({"DescribeAccountBalance": cloud_tencent.TencentError("UnauthorizedOperation.CamNoAuth", "no", [])})
        self.assertEqual(cloud_tencent.TencentProvider().balance(), "WARNING (not a stop condition): balance not readable (UnauthorizedOperation.CamNoAuth)")
        self.fake({"DescribeAccountBalance": {"RealBalance": 12345}})
        self.assertEqual(cloud_tencent.TencentProvider().balance(), "balance: 123.45 CNY")


class TencentSelfterm(unittest.TestCase):
    """scripts/cloud/cloud_tencent_selfterm.py (runs on the instance): signing and
    the check/terminate logic, with the metadata service and the API faked.
    (sign() was checked against the real API on 2026-10-05: accepted with
    valid credentials, AuthFailure.SignatureFailure with a wrong key.)"""

    S = cloud_tencent_selfterm

    def setUp(self):
        self._metadata, self._call, self._sleep, self._argv = self.S.metadata, self.S.call, self.S.time.sleep, sys.argv

    def tearDown(self):
        self.S.metadata, self.S.call, self.S.time.sleep, sys.argv = self._metadata, self._call, self._sleep, self._argv

    def test_sign(self):
        h = self.S.sign("AKIDx", "key", "cvm.tencentcloudapi.com", "TerminateInstances", "ap-shanghai", '{"InstanceIds":["ins-1"]}',
                        1759665600, "tok")
        self.assertRegex(h["Authorization"], r"^TC3-HMAC-SHA256 Credential=AKIDx/2025-10-05/cvm/tc3_request, "
                                             r"SignedHeaders=content-type;host, Signature=[0-9a-f]{64}$")
        self.assertEqual((h["X-TC-Action"], h["X-TC-Region"], h["X-TC-Version"], h["X-TC-Timestamp"], h["X-TC-Token"]),
                         ("TerminateInstances", "ap-shanghai", "2017-03-12", "1759665600", "tok"))
        h2 = self.S.sign("AKIDx", "key", "cvm.tencentcloudapi.com", "TerminateInstances", "ap-shanghai", '{"InstanceIds":["ins-2"]}',
                         1759665600)
        self.assertNotEqual(h["Authorization"], h2["Authorization"])
        self.assertNotIn("X-TC-Token", h2)

    def fake(self, responses):
        calls = []
        md = {"instance-id": "ins-1", "placement/region": "ap-shanghai",
              "cam/security-credentials/r": '{"Code":"Success","TmpSecretId":"i","TmpSecretKey":"k","Token":"t"}'}
        self.S.metadata = lambda path: md[path]
        self.S.time.sleep = lambda s: None

        def call(cred, action, region, body):
            calls.append((cred, action, region, body))
            r = responses.pop(0)
            if isinstance(r, Exception):
                raise r
            return r
        self.S.call = call
        return calls

    def run_main(self, *argv):
        sys.argv = ["cloud_tencent_selfterm.py", *argv]
        self.S.main()

    def test_check(self):
        calls = self.fake([{"Error": {"Code": "InvalidInstanceId.NotFound", "Message": "x"}}])
        self.run_main("check", "r")
        self.assertEqual(calls, [(("i", "k", "t"), "TerminateInstances", "ap-shanghai", {"InstanceIds": ["ins-00000000"]})])
        self.fake([{"Error": {"Code": "AuthFailure.UnauthorizedOperation", "Message": "x"}}])
        self.run_main("check", "r")
        for bad in ({"Error": {"Code": "AuthFailure.SignatureFailure", "Message": "x"}}, {"InstanceIdSet": []}):
            self.fake([bad])
            with self.assertRaises(SystemExit):
                self.run_main("check", "r")
        # No credentials for the role (the metadata service answers 404).
        self.fake([])
        with self.assertRaisesRegex(SystemExit, "credentials of role other"):
            self.run_main("check", "other")

    def test_terminate_retries_until_accepted(self):
        calls = self.fake([RuntimeError("no API endpoint answered"), {"Error": {"Code": "InternalError", "Message": "x"}}, {}])
        self.run_main("terminate", "r")
        self.assertEqual([c[1:] for c in calls], [("TerminateInstances", "ap-shanghai", {"InstanceIds": ["ins-1"]})] * 3)
        calls = self.fake([{"Error": {"Code": "InvalidInstanceId.NotFound", "Message": "x"}}])
        self.run_main("terminate", "r")
        self.assertEqual(len(calls), 1)


class Scripts(unittest.TestCase):
    def test_user_data(self):
        self.assertEqual(deadman_user_data(90), "#!/bin/bash\n# dead-man's switch\nshutdown -h +90\n")

    def test_rust_mirror(self):
        s = rust_script("mirror", "1.93.0", "arm64")
        self.assertIn("export RUSTUP_DIST_SERVER=https://rsproxy.cn RUSTUP_UPDATE_ROOT=https://rsproxy.cn/rustup\n", s)
        self.assertIn("curl -sSf https://rsproxy.cn/rustup-init.sh | sh -s -- -y -q --profile minimal --default-toolchain 1.93.0", s)

    def test_rust_upstream_and_upload(self):
        self.assertIn("https://sh.rustup.rs", rust_script("upstream", "1.93.0", "x86_64"))
        s = rust_script("upload", "1.93.0", "arm64", "/x/rust-1.93.0-aarch64-unknown-linux-gnu.tar.xz")
        self.assertIn("./rust-1.93.0-aarch64-unknown-linux-gnu/install.sh --prefix=$HOME/rust", s)
        self.assertEqual(cloud_common.rust_tarball_url("1.93.0", "x86_64"),
                         "https://static.rust-lang.org/dist/rust-1.93.0-x86_64-unknown-linux-gnu.tar.xz")
        with self.assertRaises(cloud_common.InfraError):
            cloud_common.rust_tarball_url("stable", "arm64")

    def test_cargo_config(self):
        self.assertIsNone(cargo_config("upstream"))
        self.assertIn("replace-with = 'rsproxy-sparse'", cargo_config("mirror"))
        self.assertIn('directory = "/root/vendor"', cargo_config("vendor", "/root/vendor"))


class Bench(unittest.TestCase):
    def test_bench_bin(self):
        self.assertEqual(cloud_common.parse_bench_bin("nostats=HEAD:no-stats"), ("nostats", "HEAD", "no-stats"))
        self.assertEqual(cloud_common.parse_bench_bin("base=bcd7ede"), ("base", "bcd7ede", ""))
        for bad in ("base", "=HEAD", "a b=HEAD", "x="):
            with self.assertRaises(ValueError):
                cloud_common.parse_bench_bin(bad)

    def test_args(self):
        a = cloud_verify.parse_args(["--bench", "run --tlc", "--bench-bin", "b=HEAD~1", "--max-minutes", "150"])
        self.assertEqual((a.bench, a.bench_bins), (["run --tlc"], [("b", "HEAD~1", "")]))
        with self.assertRaises(SystemExit):
            cloud_verify.parse_args(["--bench-bin", "b=HEAD"])

    def test_script(self):
        s = cloud_common.bench_script("/root", "clang", "aliyun ecs.c8y.4xlarge (z, spot 0.5 CNY/h)",
                                      [("nostats", "a" * 40, "no-stats")], ["table --measure-tlc", "run --tlc"])
        self.assertIn("TLX_BENCH_MACHINE='aliyun ecs.c8y.4xlarge (z, spot 0.5 CNY/h)'", s)
        self.assertIn("rm -f corpus/out/bench-tlc.json", s)
        clippy = "cargo clippy --workspace --release --all-targets -- -D warnings || exit 1"
        self.assertIn(clippy, s)
        self.assertLess(s.index(clippy), s.index("cargo build -q --release -p tlx-cli"))
        self.assertLess(s.index(clippy), s.index("python3 -u scripts/bench.py"))
        self.assertIn(f"git worktree add -q -f --detach /root/bench-src/nostats {'a' * 40}", s)
        self.assertIn("cargo build -q --release -p tlx-cli --features no-stats", s)
        self.assertIn("cp /root/bench-src/nostats/target/release/tlx target/bench-bins/nostats/tlx", s)
        self.assertLess(s.index("python3 -u scripts/bench.py table --measure-tlc || rc=1"), s.index("python3 -u scripts/bench.py run --tlc || rc=1"))
        self.assertTrue(s.endswith("exit $rc\n"))


class Oracle(unittest.TestCase):
    def test_args(self):
        a = cloud_verify.parse_args(["--oracle", "tlc --source external --tier medium", "--suites", "corpus-ext"])
        self.assertEqual((a.oracle, a.suites), (["tlc --source external --tier medium"], "corpus-ext"))
        with self.assertRaises(SystemExit):
            cloud_verify.parse_args(["--oracle", "tlc", "--bench", "run"])

    def test_script(self):
        s = cloud_common.oracle_script("/root", ["tlc --source external --tier medium -j 4", "tlc --source external --tier large"])
        self.assertIn("export TLX_CLOUD_HOST=1 TLX_JAVA=$(command -v java)", s)
        self.assertLess(s.index("run 1 tlc --source external --tier medium -j 4 &"),
                        s.index("run 2 tlc --source external --tier large &"))
        self.assertIn('wait "$p" || rc=1', s)
        self.assertTrue(s.endswith("exit $rc\n"))

    def test_external_corpora_are_uploaded(self):
        self.assertIn("--include=/external/***", cloud_common.THIRD_PARTY_FILTER)
        self.assertLess(cloud_common.THIRD_PARTY_FILTER.index("--include=/external/***"), cloud_common.THIRD_PARTY_FILTER.index("--exclude=*"))

    def test_the_declared_trace_inputs_reach_the_cloud_bundle(self):
        # The staging fix is only usable in the cloud if the input a root-relative
        # model declares (corpus.MODEL_INPUTS, named relative to the corpus root =
        # third_party/Examples) is in the uploaded third_party/ tree. A dry run
        # proves the real rsync pattern keeps it and still drops the jars the
        # filter excludes. The bytes are synthetic: the filter is about paths, and
        # a quality CI checkout (--tests-only) has no third_party/Examples.
        import corpus
        if not shutil.which('rsync'):
            self.skipTest('rsync is not installed')
        self.assertTrue(corpus.MODEL_INPUTS, "no declared model inputs to package")
        for model_id, inputs in corpus.MODEL_INPUTS.items():
            self.assertIn(model_id, corpus.ROOT_RELATIVE_MODELS)
            for name in inputs:
                with tempfile.TemporaryDirectory() as base:
                    src, dst = os.path.join(base, 'src'), os.path.join(base, 'dst')
                    staged = os.path.join(src, 'Examples', *name.split('/'))
                    os.makedirs(os.path.dirname(staged))
                    with open(staged, 'w') as stream:
                        stream.write('{"N": 1}\n')
                    with open(os.path.join(src, 'tla2tools.jar'), 'w') as stream:
                        stream.write('x')
                    p = subprocess.run(['rsync', '-ni', '-a', *cloud_common.THIRD_PARTY_FILTER, src + '/', dst + '/'],
                                       capture_output=True, text=True)
                    self.assertEqual(p.returncode, 0, p.stderr)
                    self.assertIn(os.path.join('Examples', *name.split('/')), p.stdout)
                    self.assertNotIn('tla2tools.jar', p.stdout)


class FakeMachine:
    """A machine double for the result transfers: records every invocation's
    complete argv, executable included (HARNESS-22), and answers with the exit
    codes or exceptions in `answers` (the last entry repeats)."""

    dead_at = None          # a copy's retry budget counts down to the dead-man's switch

    def __init__(self, *answers):
        self.answers, self.calls = list(answers), []

    def ssh_transport(self):
        return "ssh -i /key"

    def remote(self, path):
        return "root@192.0.2.1:" + path

    def run(self, cmd, **kw):
        self.calls.append((list(cmd), kw))
        answer = self.answers.pop(0) if len(self.answers) > 1 else self.answers[0]
        if isinstance(answer, BaseException):
            raise answer
        return mock.Mock(returncode=answer, stdout=b"", stderr=b"")

    def args(self, i):
        return self.calls[i][0]


class FakeClock:
    """A monotonic clock that advances a fixed step on every reading, so a
    bounded retry loop terminates deterministically without real waiting."""

    def __init__(self, step=100.0):
        self.t, self.step = 0.0, step

    def __call__(self):
        self.t += self.step
        return self.t


class FakeProvider:
    """A provider double for the terminate path: `terminate` answers from
    `outcomes` (the last entry repeats), raising an outcome that is an
    exception."""

    def __init__(self, *outcomes, hint="tccli cvm TerminateInstances ..."):
        self.outcomes, self.calls, self.hint = list(outcomes), 0, hint

    def terminate_hint(self, m):
        return self.hint

    def terminate(self, m):
        self.calls += 1
        out = self.outcomes.pop(0) if len(self.outcomes) > 1 else self.outcomes[0]
        if isinstance(out, BaseException):
            raise out
        return out


class StopAfter:
    """A `threading.Event`-shaped stop flag: reports "not stopped" N times,
    then stopped."""

    def __init__(self, n):
        self.n, self.calls = n, 0

    def wait(self, secs):
        self.calls += 1
        return self.calls > self.n


class CopyingMachine(FakeMachine):
    """A FakeMachine that leaves a file in the rsync destination on success, so
    a test can see what a (partial) local copy holds."""

    def run(self, cmd, **kw):
        p = super().run(cmd, **kw)
        if p.returncode == 0:
            dest = cmd[-1]
            d = dest if dest.endswith("/") else os.path.dirname(dest)
            os.makedirs(d, exist_ok=True)
            with open(os.path.join(d, "arrived"), "w", encoding="utf-8") as f:
                f.write("x")
        return p


class ResultTransferReceipt(unittest.TestCase):
    """HARNESS-06: a run's final, required copy of a result must fail loud -
    bounded retries, then an infra error - so a transfer that never completed
    cannot yield a success receipt. The periodic best-effort copies and the
    optional TLC -workers N cache stay quiet (CODE-23 keeps the repair in the
    transfer helper, not mixed into the callers' control flow).

    The retry delay is patched as a decorator (never `patch(...).start()`,
    which returns the replacement mock: keeping that instead of the patcher
    left the global `time.sleep` mocked for every later test module)."""

    @mock.patch.object(cloud_common.time, "sleep")
    def test_required_transfer_recovers_on_a_later_attempt(self, sleep):
        # rsync 23 (partial transfer) once, then success: no raise, one retry.
        m = FakeMachine(23, 0, 0, 0)
        with tempfile.TemporaryDirectory() as d:
            cloud_common.fetch_bench_results(m, d)
            self.assertEqual(m.args(0), ["rsync", "-az", "-e", "ssh -i /key",
                                         "root@192.0.2.1:tlx/bench/", os.path.join(d, "bench") + "/"])
        self.assertEqual(len(m.calls), 4)  # bench/ twice, the cache, bench.out
        self.assertEqual(sleep.call_count, 1)

    def test_the_argv_double_keeps_the_executable_and_every_argument(self):
        # HARNESS-22: the production assertion below is only meaningful because
        # the double records argv[0] and the arguments in order.
        m = FakeMachine(0)
        m.run(["rsync", "-az"], check=False)
        self.assertEqual(m.calls[0], (["rsync", "-az"], {"check": False}))

    @mock.patch.object(cloud_common.time, "sleep")
    def test_required_transfer_exhaustion_is_an_infra_error(self, sleep):
        m = FakeMachine(23)
        with tempfile.TemporaryDirectory() as d:
            # A clock that jumps on every reading bounds the retry budget in a
            # few attempts instead of ten real minutes.
            with mock.patch.object(cloud_common.time, "monotonic", FakeClock(100.0)):
                with self.assertRaises(cloud_common.InfraError) as raised:
                    cloud_common.fetch_bench_results(m, d)
        self.assertEqual(raised.exception.code, cloud_common.INFRA_FAIL)
        self.assertNotEqual(raised.exception.code, 0)
        self.assertIn("still failing after", str(raised.exception))
        self.assertIn("required transfer failed:", str(raised.exception))
        self.assertIn("rsync exit 23", str(raised.exception))
        # Only the required bench/ copy was attempted; it stopped the whole
        # transfer instead of continuing to the next file, and every attempt
        # but the last slept once.
        self.assertEqual(len(m.calls), sleep.call_count + 1)
        self.assertGreaterEqual(len(m.calls), 3)
        self.assertLessEqual(len(m.calls), cloud_common.RESULT_TRANSFER_RETRY_SECS // 100 + 4)
        self.assertEqual(m.args(0)[0], "rsync")

    def test_optional_bench_tlc_cache_missing_is_not_a_failure(self):
        # First required copy ok, the optional cache copy fails (a run with no
        # TLC -workers N), the last required copy ok: no raise.
        m = FakeMachine(0, 23, 0)
        with tempfile.TemporaryDirectory() as d:
            cloud_common.fetch_bench_results(m, d)
        self.assertEqual(len(m.calls), 3)
        self.assertTrue(m.args(1)[-2].endswith("corpus/out/bench-tlc.json"))
        self.assertIs(m.calls[1][1].get("check"), False)  # optional: never checked

    def test_best_effort_periodic_copies_never_raise(self):
        m = FakeMachine(23)
        with tempfile.TemporaryDirectory() as d:
            cloud_common.fetch_bench_results(m, d, quiet=True)
            cloud_common.fetch_oracle_results(m, os.path.join(d, "oracle"), quiet=True)
        self.assertEqual(len(m.calls), 5)  # bench/ + cache + bench.out + oracle files + oracle.out
        self.assertTrue(all(c[1].get("check") is False for c in m.calls))

    @mock.patch.object(cloud_common.time, "sleep")
    def test_oracle_required_transfers_are_strict(self, sleep):
        m = FakeMachine(0, 23)  # tlc*.json ok, verify.out -> oracle.out always fails
        with tempfile.TemporaryDirectory() as d:
            with mock.patch.object(cloud_common.time, "monotonic", FakeClock(100.0)):
                with self.assertRaises(cloud_common.InfraError):
                    cloud_common.fetch_oracle_results(m, os.path.join(d, "oracle"))
        self.assertIn("--include=" + cloud_common.ORACLE_FILES, m.args(0))
        self.assertEqual(len(m.calls), 1 + sleep.call_count + 1)  # + the failed oracle-files copy

    def test_an_interrupted_required_transfer_is_not_retried(self):
        # An interrupt (Ctrl-C / the signal handler) propagates as-is: it must
        # not be swallowed by the retry loop nor turned into an infra error.
        for interrupt in (KeyboardInterrupt(), cloud_common.Interrupted("signal 15")):
            with self.subTest(interrupt=type(interrupt).__name__):
                m = FakeMachine(interrupt)
                with tempfile.TemporaryDirectory() as d:
                    with self.assertRaises(type(interrupt)):
                        cloud_common.fetch_bench_results(m, d)
                self.assertEqual(len(m.calls), 1)

    def test_a_failed_required_receipt_cannot_exit_zero(self):
        # The required fetch raises inside cloud_verify.run; main()'s CloudStop
        # handler turns it into the infra exit code, never 0 (HARNESS-06).
        failure = cloud_common.InfraError("required transfer failed after 3 attempts: bench results (rsync exit 23)")
        with mock.patch.object(cloud_verify, "run", side_effect=failure), \
             mock.patch.object(sys, "argv", ["cloud_verify.py", "--quick"]), \
             mock.patch.object(cloud_verify, "log"):
            rc = cloud_verify.main()
        self.assertEqual(rc, cloud_common.INFRA_FAIL)
        self.assertNotEqual(rc, 0)


class BenchCombinationRefusal(unittest.TestCase):
    """bench mode runs bench.py instead of verify.py, so a verify.py option in
    the same call was silently dropped (2026-10-08: a requested build suite
    never ran). Refused before the launch, with a passing control each."""

    def test_suites_with_bench_is_refused_in_either_order(self):
        for argv in (["--suites", "build,corpus-compile", "--bench", "run --tlc"],
                     ["--bench", "run --tlc", "--suites", "build,corpus-compile"]):
            with self.subTest(argv=argv):
                with self.assertRaises(SystemExit) as raised:
                    cloud_verify.parse_args(argv)
                self.assertEqual(raised.exception.code, 2)  # argparse refusal

    def test_each_option_alone_still_parses(self):
        self.assertEqual(cloud_verify.parse_args(["--suites", "build"]).suites, "build")
        self.assertEqual(cloud_verify.parse_args(["--bench", "run --tlc"]).bench, ["run --tlc"])
        # ...and the pre-existing --oracle refusal stays in force.
        for argv in (["--oracle", "tlc", "--bench", "run"],):
            with self.subTest(argv=argv):
                with self.assertRaises(SystemExit):
                    cloud_verify.parse_args(argv)
        self.assertEqual(cloud_verify.parse_args(["--then", "--suites x", "--bench", "run"]).then, ["--suites x"])


class FullGateMarker(unittest.TestCase):
    """Only a full-scope merge_gate marker over exactly this checked-out tree
    may stand in for the local Clippy the preflight would otherwise run: the
    full gate ran release Clippy with warnings denied, a narrower one did not."""

    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.addCleanup(self.dir.cleanup)

    def fake_git(self, **values):
        def git(*args, **kw):
            key = " ".join(args)
            if key not in values:
                raise AssertionError(f"unexpected git call {key!r}")
            return values[key]
        return git

    def write_marker(self, **over):
        marker = {"version": 1, "tree": "t" * 12, "head": "h" * 12, "scope": "full", "quick": False}
        marker.update(over)
        with open(os.path.join(self.dir.name, "tlx-merge-gate"), "w", encoding="utf-8") as f:
            json.dump(marker, f)
        return marker

    def read_marker(self, **over):
        self.write_marker(**over)
        with mock.patch.object(cloud_common, "git", side_effect=self.fake_git(**{
                "rev-parse --git-path tlx-merge-gate": "tlx-merge-gate",
                "write-tree": "t" * 12, "rev-parse HEAD": "h" * 12})), \
             mock.patch.object(cloud_common, "clean_worktree", return_value=True):
            return cloud_common.full_gate_marker(self.dir.name)

    def test_a_full_scope_marker_of_this_tree_is_accepted(self):
        marker = self.write_marker()
        self.assertEqual(self.read_marker(), marker)

    def test_a_narrower_scope_says_nothing_about_clippy(self):
        self.assertIsNone(self.read_marker(scope="scripts"))
        self.assertIsNone(self.read_marker(scope="docs"))

    def test_a_stale_tree_head_or_dirty_worktree_is_refused(self):
        self.assertIsNone(self.read_marker(tree="x" * 12))
        self.assertIsNone(self.read_marker(head="x" * 12))
        self.assertIsNone(self.read_marker(version=2))
        self.write_marker()
        with mock.patch.object(cloud_common, "clean_worktree", return_value=False):
            with mock.patch.object(cloud_common, "git", side_effect=self.fake_git(**{
                    "rev-parse --git-path tlx-merge-gate": "tlx-merge-gate",
                    "write-tree": "t" * 12, "rev-parse HEAD": "h" * 12})):
                self.assertIsNone(cloud_common.full_gate_marker(self.dir.name))

    def test_no_marker_at_all_is_not_a_crash(self):
        with mock.patch.object(cloud_common, "clean_worktree", return_value=True):
            self.assertIsNone(cloud_common.full_gate_marker(self.dir.name))


class ClippyPreflight(unittest.TestCase):
    """A launch the remote build suite would reject on Clippy is refused here,
    before an instance is paid for (2026-10-08: items_after_test_module was
    rejected on the instance only). A check that cannot run locally is skipped,
    never turned into a false refusal (HARNESS-08)."""

    def setUp(self):
        self.dir = tempfile.TemporaryDirectory()
        self.addCleanup(self.dir.cleanup)
        self.root = self.dir.name

    def manifest(self, text="[workspace]\nmembers = []\n\n[workspace.lints.clippy]\n"):
        with open(os.path.join(self.root, "Cargo.toml"), "w", encoding="utf-8") as f:
            f.write(text)

    @staticmethod
    def fail_if_run(argv, **kw):  # a runner double that proves the command was not run
        raise AssertionError(f"the local Clippy must not run here: {argv}")

    def test_this_repository_declares_workspace_lints(self):
        # If this stops holding, verify.py's build suite stops running Clippy
        # remotely too, and the preflight silently follows it.
        self.assertTrue(cloud_common.workspace_lints())

    def test_a_failing_command_refuses_with_its_whole_argv(self):
        self.manifest()
        seen = []

        def runner(argv, **kw):
            seen.append((argv, kw))
            return 101

        with mock.patch.object(cloud_common.shutil, "which", return_value="/usr/bin/cargo"):
            ok, note = cloud_common.clippy_preflight(self.root, runner=runner, marker={})
        self.assertFalse(ok)
        self.assertIn("prelaunch clippy failed (exit 101)", note)
        self.assertIn("would refuse this tree", note)
        self.assertEqual(seen, [(["/usr/bin/cargo", "clippy", "--workspace", "--release", "--all-targets",
                                  "-j", "3", "--", "-D", "warnings"], {"cwd": self.root})])

    def test_a_clean_command_is_the_passing_control(self):
        self.manifest()
        with mock.patch.object(cloud_common.shutil, "which", return_value="/usr/bin/cargo"):
            ok, note = cloud_common.clippy_preflight(self.root, runner=lambda argv, **kw: 0, marker={})
        self.assertTrue(ok)
        self.assertEqual(note, "prelaunch clippy passed")

    def test_a_full_scope_marker_skips_the_command(self):
        self.manifest()
        marker = {"version": 1, "scope": "full", "tree": "t" * 12, "head": "h" * 12}
        ok, note = cloud_common.clippy_preflight(self.root, marker=marker, runner=self.fail_if_run)
        self.assertTrue(ok)
        self.assertIn("merge_gate marker covers tree", note)

    def test_a_revision_without_workspace_lints_is_skipped(self):
        self.manifest("[workspace]\nmembers = []\n")
        ok, note = cloud_common.clippy_preflight(self.root, runner=self.fail_if_run)
        self.assertTrue(ok)
        self.assertIn("no [workspace.lints]", note)

    def test_a_machine_without_local_cargo_is_skipped_not_refused(self):
        self.manifest()
        with mock.patch.object(cloud_common.shutil, "which", return_value=None):
            ok, note = cloud_common.clippy_preflight(self.root)
        self.assertTrue(ok)
        self.assertIn("no local cargo", note)

    def test_a_launch_of_another_revision_is_skipped(self):
        self.manifest()
        with mock.patch.object(cloud_common, "git", return_value="h" * 12):
            ok, note = cloud_common.clippy_preflight(self.root, rev="a" * 12, runner=self.fail_if_run)
        self.assertTrue(ok)
        self.assertIn("is not this worktree's HEAD", note)

    def test_a_dry_run_skips_the_expensive_check(self):
        self.manifest()
        ok, note = cloud_common.clippy_preflight(self.root, dry_run=True, runner=self.fail_if_run)
        self.assertTrue(ok)
        self.assertIn("dry run provisions nothing", note)


class ReleasePreflight(unittest.TestCase):
    """The one release build a bench launch pays for locally, before anything is
    provisioned (2026-10-10: the bench smoke's own freshness guard builds but
    ignores the build's exit status, so a failed build after a crates-touching
    merge read as "still older than crates/..." and the attempt was wasted)."""

    BIN = "/nonexistent/target/release/tlx"

    def test_a_missing_binary_is_built_instead_of_refused(self):
        # (A fresh worktree has no target/: the bench smoke refuses it with
        # "run cargo build --release first", and with a stale binary the smoke's
        # own guard stops after a build whose exit status it never reads.)
        state, seen = {"missing": True}, []

        def build(argv):
            seen.append(argv)
            state["missing"] = False        # the build produced the binary
            return 0

        ok, note = cloud_common.release_preflight(build=build, binary=self.BIN,
                                                  stale=lambda b: b if state["missing"] else None)
        self.assertTrue(ok)
        self.assertEqual(note, "prelaunch build ok")
        self.assertEqual([1 for argv in seen], [1])
        self.assertTrue(seen[0][0].endswith("cargo"))
        self.assertEqual(seen[0][1:], ["build", "--release", "-p", "tlx-cli"])

    def test_a_failing_build_refuses_naming_the_build_not_the_stale_file(self):
        ok, note = cloud_common.release_preflight(build=lambda argv: 101, binary=self.BIN,
                                                  stale=lambda b: "crates/tlx-eval/src/lib.rs")
        self.assertFalse(ok)
        self.assertIn("the release build failed (exit 101)", note)
        self.assertIn("nothing was provisioned", note)
        self.assertNotIn("still older than", note)

    def test_a_build_that_does_not_cover_the_file_refuses_with_that_file(self):
        # The pre-change failure mode, kept as the reason the check exists: the
        # build "succeeded" and the tree still looks stale - the operator has to
        # be told which file, not left with a bare STOP mid-launch.
        ok, note = cloud_common.release_preflight(build=lambda argv: 0, binary=self.BIN,
                                                  stale=lambda b: "crates/tlx-native/src/tlx_abi.h")
        self.assertFalse(ok)
        self.assertIn("still older than crates/tlx-native/src/tlx_abi.h", note)
        self.assertIn("cargo does not track that file", note)

    def test_an_up_to_date_binary_is_not_built(self):
        def fail_if_run(argv):
            raise AssertionError(f"no build may run here: {argv}")
        ok, note = cloud_common.release_preflight(build=fail_if_run, binary=self.BIN, stale=lambda b: None)
        self.assertTrue(ok)
        self.assertIn("up to date", note)

    def test_a_dry_run_builds_nothing(self):
        def fail_if_run(argv):
            raise AssertionError(f"a dry run must not build: {argv}")
        ok, note = cloud_common.release_preflight(build=fail_if_run, dry_run=True, binary=self.BIN,
                                                  stale=lambda b: "crates/x.rs")
        self.assertTrue(ok)
        self.assertIn("dry run provisions nothing", note)


class ReleasePreflightLaunchRefusal(unittest.TestCase):
    """A tree that cannot build is refused before the provider is asked for
    offers, so nothing is provisioned and no quota is spent."""

    def test_a_failing_release_build_refuses_the_launch_before_the_provider(self):
        a = cloud_verify.parse_args(["--quick", "--provider", "tencent", "--bench", "run --tlc"])
        provider = mock.MagicMock()
        with mock.patch.object(cloud_verify, "current_owner", return_value="c-h02"), \
             mock.patch.object(cloud_verify, "LaunchLedger") as ledger, \
             mock.patch.object(cloud_verify, "clippy_preflight", return_value=(True, "ok")), \
             mock.patch.object(cloud_verify, "release_preflight",
                               return_value=(False, "the release build failed (exit 101)")) as preflight, \
             mock.patch.object(cloud_verify, "make_provider", return_value=provider):
            with self.assertRaises(cloud_common.CloudStop) as raised:
                cloud_verify.run_checked(a, cloud_verify.Cancel())
        self.assertEqual(raised.exception.code, 23)
        self.assertIn("the release build failed (exit 101)", str(raised.exception))
        preflight.assert_called_once()
        provider.offers.assert_not_called()          # no API call, no offer, no quota


class ClippyLaunchRefusal(unittest.TestCase):
    """The refusal happens before the provider is asked for offers or an
    instance, so a lint error costs no API call and no quota."""

    def test_a_failing_preflight_refuses_the_launch(self):
        a = cloud_verify.parse_args(["--quick", "--provider", "tencent"])
        provider = mock.MagicMock()
        with mock.patch.object(cloud_verify, "current_owner", return_value="c-d20"), \
             mock.patch.object(cloud_verify, "LaunchLedger") as ledger, \
             mock.patch.object(cloud_verify, "clippy_preflight",
                               return_value=(False, "clippy: items_after_test_module")) as preflight, \
             mock.patch.object(cloud_verify, "make_provider", return_value=provider), \
             mock.patch.object(cloud_verify, "log"):
            ledger.return_value.locked.return_value.__enter__.return_value = []
            ledger.return_value.remaining.return_value = 2
            with self.assertRaises(cloud_verify.CloudStop) as raised:
                cloud_verify.run(a)
        self.assertEqual(raised.exception.code, 23)
        self.assertIn("prelaunch clippy refused: clippy: items_after_test_module", str(raised.exception))
        preflight.assert_called_once()
        # The preflight checks the revision that would be uploaded, not "HEAD".
        self.assertEqual(preflight.call_args.kwargs["rev"], cloud_verify.git("rev-parse", "HEAD"))
        self.assertFalse(preflight.call_args.kwargs["dry_run"])
        provider.launch.assert_not_called()
        provider.offers.assert_not_called()


class NetworkRetry(unittest.TestCase):
    """A transient network failure (the 2026-10-08 DNS outage) is retried with
    bounded backoff, then reported as an infra error, instead of discarding a
    finished run or leaving a billed instance (HARNESS-06, HARNESS-09)."""

    def test_transient_failures_are_recognised_by_type_and_by_text(self):
        self.assertTrue(cloud_common.is_network_error(socket.gaierror("Name or service not known")))
        self.assertTrue(cloud_common.is_network_error(ConnectionRefusedError("refused")))
        self.assertTrue(cloud_common.is_network_error(TimeoutError("read timed out")))
        # A provider CLI wraps the DNS failure in its own message.
        self.assertTrue(cloud_common.is_network_error(
            Exception("code:CliError message:Name resolution error ... cvm.tencentcloudapi.com")))
        self.assertFalse(cloud_common.is_network_error(ValueError("invalid parameter")))
        self.assertFalse(cloud_common.is_network_error(cloud_common.InfraError("terminate refused")))

    @mock.patch.object(cloud_common.time, "sleep")
    def test_it_recovers_after_transient_failures(self, sleep):
        calls = []

        def fn():
            calls.append(1)
            if len(calls) < 3:
                raise socket.gaierror("Temporary failure in name resolution")
            return "listed"

        self.assertEqual(cloud_common.retry_network(fn, "list instances", monotonic=FakeClock(1.0)), "listed")
        self.assertEqual(len(calls), 3)
        self.assertEqual(sleep.call_count, 2)

    @mock.patch.object(cloud_common.time, "sleep")
    def test_exhaustion_is_a_bounded_infra_error(self, sleep):
        def fn():
            raise socket.gaierror("Name resolution error")

        with self.assertRaises(cloud_common.InfraError) as raised:
            cloud_common.retry_network(fn, "fetch results", monotonic=FakeClock(50.0))
        self.assertIn("still failing after", str(raised.exception))
        self.assertIn("Name resolution error", str(raised.exception))
        self.assertGreaterEqual(sleep.call_count, 3)
        self.assertLessEqual(sleep.call_count, 12)  # bounded, not endless

    def test_a_non_network_error_is_not_retried(self):
        calls = []

        def fn():
            calls.append(1)
            raise ValueError("invalid parameter")

        with self.assertRaises(ValueError):
            cloud_common.retry_network(fn, "x")
        self.assertEqual(len(calls), 1)

    def test_an_interrupt_is_not_retried_and_is_not_wrapped(self):
        def fn():
            raise cloud_common.Interrupted("signal 15")

        with self.assertRaises(cloud_common.Interrupted):
            cloud_common.retry_network(fn, "x")

    def test_the_deadline_reserves_time_to_terminate_before_the_switch(self):
        clock = FakeClock(0.0)  # a stopped clock, so only the offsets differ
        # 300 s to the dead-man's switch and 120 s reserved: 180 s of retry.
        self.assertEqual(cloud_common.network_deadline(300.0, reserve=120, budget=600,
                                                       now=lambda: 0.0, monotonic=clock), 180.0)
        # Plenty of time: the 600 s budget is the cap, not the switch.
        self.assertEqual(cloud_common.network_deadline(100000.0, budget=600,
                                                       now=lambda: 0.0, monotonic=clock), 600.0)
        # Already inside the reserve: no time to retry, the instance is freed.
        self.assertEqual(cloud_common.network_deadline(100.0, reserve=120, budget=600,
                                                       now=lambda: 0.0, monotonic=clock), 0.0)


class BoundedRetry(testkit.GuardedTestCase):
    """``retry_bounded`` is the one shared bounded-retry loop: it takes an
    injectable clock and sleep (through ``RetryClock``), so every loop migrated
    onto it runs to completion in a test without waiting for real time. One
    harness test once backed off for about ten minutes and had to be killed
    (2026-10-08 step-back); the injection above makes that impossible."""

    def test_a_passing_attempt_returns_without_sleeping(self):
        clock = testkit.FakeClock()
        result = cloud_common.retry_bounded(lambda: "ok", "unit", retry=lambda r: False,
                                            clock=cloud_common.RetryClock(clock, clock.sleep))
        self.assertEqual(result, "ok")
        self.assertEqual(clock.sleeps, [])

    def test_tries_bounds_the_attempts_and_sleeps_between_them_only(self):
        clock = testkit.FakeClock()
        attempts = []

        def attempt():
            attempts.append(clock())
            return "still failing"

        result = cloud_common.retry_bounded(attempt, "unit", retry=lambda r: True, tries=3,
                                            gap=5, clock=cloud_common.RetryClock(clock, clock.sleep))
        self.assertEqual(result, "still failing")
        self.assertEqual(len(attempts), 3)  # not a fourth attempt after the bound
        self.assertEqual(clock.sleeps, [5, 5])  # slept between attempts, never after the last

    def test_until_releases_the_loop_once_the_clock_passes_it(self):
        clock = testkit.FakeClock()
        cloud_common.retry_bounded(lambda: "x", "unit", retry=lambda r: True, until=12.0,
                                   gap=5, clock=cloud_common.RetryClock(clock, clock.sleep))
        self.assertEqual(clock.sleeps, [5, 5, 5])

    def test_an_already_expired_until_runs_no_attempt(self):
        clock = testkit.FakeClock(100.0)
        calls = []
        result = cloud_common.retry_bounded(lambda: calls.append(1), "unit", retry=lambda r: True,
                                            until=50.0, clock=cloud_common.RetryClock(clock, clock.sleep))
        self.assertIsNone(result)
        self.assertEqual(calls, [])

    def test_a_callable_gap_gets_the_attempt_number(self):
        clock = testkit.FakeClock()
        cloud_common.retry_bounded(lambda: "x", "unit", retry=lambda r: True, tries=3,
                                   gap=lambda attempt_no: attempt_no,
                                   clock=cloud_common.RetryClock(clock, clock.sleep))
        self.assertEqual(clock.sleeps, [1, 2])

    def test_on_retry_reports_each_repeat(self):
        seen = []
        clock = testkit.FakeClock()
        cloud_common.retry_bounded(lambda: "x", "unit", retry=lambda r: True, tries=3, gap=1,
                                   clock=cloud_common.RetryClock(clock, clock.sleep),
                                   on_retry=lambda attempt_no, result: seen.append((attempt_no, result)))
        self.assertEqual(seen, [(1, "x"), (2, "x")])

    def test_the_clock_is_built_from_the_sleep_and_monotonic_keywords(self):
        # with_fake_time injects sleep/monotonic by name; retry_bounded builds its
        # own RetryClock from them, so a caller need not know RetryClock exists.
        result, clock = testkit.with_fake_time(cloud_common.retry_bounded, lambda: "x", "unit",
                                               retry=lambda r: True, tries=2, gap=4)
        self.assertEqual(result, "x")
        self.assertEqual(clock.sleeps, [4])


class MigratedRetryLoops(testkit.GuardedTestCase):
    """The loops moved onto ``retry_bounded`` take an injectable clock, so their
    backoff is asserted instead of waited for. Before the fix each read
    ``time.time``/``time.sleep`` (or ``time.monotonic``) directly and this
    injection failed with ``TypeError: unexpected keyword argument``."""

    def test_wait_ssh_polls_the_provider_ports_without_real_waiting(self):
        provider = mock.Mock(ssh_ports=[22, 2222])
        m = cloud_common.Machine(provider, Offer(1, "region", "zone", "type", 16))
        m.ip = "203.0.113.7"
        down = mock.Mock(returncode=255, stdout="")
        up = mock.Mock(returncode=0, stdout="203.0.113.7 55555 22\n")
        # First round probes both ports and fails, second round answers on :22.
        m.run = mock.Mock(side_effect=[down, down, up])
        clock = testkit.FakeClock()
        with mock.patch.object(cloud_common, "log"):
            m.wait_ssh(timeout=100, monotonic=clock, sleep=clock.sleep)
        self.assertEqual(m.port, 22)
        self.assertEqual(m.run.call_count, 3)
        self.assertEqual(clock.sleeps, [3])  # one gap between the two probe rounds

    def test_run_remote_verify_reconnects_without_real_waiting(self):
        m = mock.Mock(dead_at=5000.0, env={})
        m.ssh_cmd.return_value = ["ssh", "host"]
        # 1) the detached start (return ignored), 2) an empty rc (stream ended
        # early), 3) the real rc (0) - exactly one reconnect.
        m.ssh.side_effect = [mock.Mock(), mock.Mock(returncode=0, stdout=""), mock.Mock(returncode=0, stdout="0\n")]
        clock = testkit.FakeClock()
        with mock.patch.object(cloud_common, "subprocess") as subprocess_mod, \
             mock.patch.object(cloud_common, "log"), mock.patch.object(cloud_common, "warning"):
            subprocess_mod.PIPE = object()
            subprocess_mod.Popen.return_value.stdout = iter([])
            code, logdir = cloud_common.run_remote_verify(m, ["python3", "verify.py", "--release"],
                                                          now=clock, sleep=clock.sleep)
        self.assertEqual((code, logdir), (0, None))
        self.assertEqual(m.ssh_cmd.call_count, 2)  # two streaming attempts
        self.assertEqual(clock.sleeps, [5])  # the reconnect gap, never slept for real

    def test_a_dropped_stream_that_carried_the_job_forward_never_abandons_the_lane(self):
        # 2026-10-09: an operator-IP ssh rule another process kept removing
        # dropped every lane's stream about once every five minutes. The old
        # count cap (20) then aborted four healthy jobs ~100 minutes into a
        # multi-hour baseline, losing every row they had not yet written. A
        # stream that lasted at least RECONNECT_BURST_SECS is a blip, whatever
        # the reconnect count.
        m = mock.Mock(dead_at=200_000.0, env={})
        m.ssh_cmd.return_value = ["ssh", "host"]
        m.ssh.side_effect = [mock.Mock()] + [mock.Mock(returncode=0, stdout="")] * 25 + \
            [mock.Mock(returncode=0, stdout="0\n")]
        clock = testkit.FakeClock()
        def stream():
            clock.advance(300)  # the stream lived five minutes before it dropped
            yield "  | still working\n"
        with mock.patch.object(cloud_common, "subprocess") as subprocess_mod, \
             mock.patch.object(cloud_common, "log"), mock.patch.object(cloud_common, "warning"):
            subprocess_mod.PIPE = object()
            subprocess_mod.Popen.side_effect = lambda *a, **k: mock.Mock(stdout=stream())
            code, logdir = cloud_common.run_remote_verify(m, ["python3", "verify.py", "--release"],
                                                          now=clock, sleep=clock.sleep)
        self.assertEqual((code, logdir), (0, None))
        self.assertEqual(len(clock.sleeps), 25)  # every reconnect happened, none aborted

    def test_a_stream_without_progress_stops_at_the_fetch_reserve(self):
        # Empty streams do not prove remote failure. Recover until the time
        # reserve, then let the caller fetch results before instance cleanup.
        m = mock.Mock(dead_at=500.0, env={}, access=None, id="fixture-instance")
        m.ssh_cmd.return_value = ["ssh", "host"]
        m.ssh.return_value = mock.Mock(returncode=0, stdout="")
        clock = testkit.FakeClock()
        with mock.patch.object(cloud_common, "subprocess") as subprocess_mod, \
             mock.patch.object(cloud_common, "log"), mock.patch.object(cloud_common, "warning"):
            subprocess_mod.PIPE = object()
            subprocess_mod.Popen.return_value.stdout = iter([])
            with self.assertRaises(cloud_common.InfraError) as raised:
                cloud_common.run_remote_verify(m, ["python3", "verify.py", "--release"],
                                               now=clock, sleep=clock.sleep)
        self.assertIn("final result fetch", str(raised.exception))
        self.assertEqual(clock(), m.dead_at - cloud_common.FETCH_MARGIN_SECS)
        self.assertGreater(len(clock.sleeps), 20)


class TerminateUntilGone(unittest.TestCase):
    """Cleanup keeps retrying list+terminate through a local outage and prints
    an explicit LEFTOVER line instead of leaving a billed instance silently
    (HARNESS-09)."""

    @mock.patch.object(cloud_common.time, "sleep")
    def test_a_network_failure_is_retried_until_the_instance_is_gone(self, sleep):
        p = FakeProvider(ConnectionError("Name resolution error"), True)
        m = mock.Mock(id="ins-1", region="ap-guangzhou")
        self.assertTrue(cloud_common.terminate_until_gone(p, m, monotonic=FakeClock(1.0)))
        self.assertEqual(p.calls, 2)

    @mock.patch.object(cloud_common.time, "sleep")
    def test_a_persistent_network_failure_prints_a_leftover_line(self, sleep):
        p = FakeProvider(socket.gaierror("no such host"), hint="tccli cvm TerminateInstances --region ap-beijing")
        m = mock.Mock(id="ins-2", region="ap-beijing")
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertFalse(cloud_common.terminate_until_gone(p, m, monotonic=FakeClock(100.0)))
        self.assertIn("LEFTOVER INSTANCE ins-2 ap-beijing: terminate with", out.getvalue())
        self.assertIn("tccli cvm TerminateInstances", out.getvalue())
        self.assertGreaterEqual(p.calls, 2)

    @mock.patch.object(cloud_common.time, "sleep")
    def test_a_refusal_that_cannot_terminate_is_left_over(self, sleep):
        p = FakeProvider(False)
        m = mock.Mock(id="ins-3", region="ap-shanghai")
        out = io.StringIO()
        with contextlib.redirect_stdout(out):
            self.assertFalse(cloud_common.terminate_until_gone(p, m, monotonic=FakeClock(100.0)))
        self.assertIn("LEFTOVER INSTANCE ins-3", out.getvalue())

    def test_a_non_network_error_is_raised(self):
        p = FakeProvider(cloud_common.InfraError("TerminateInstances refused: fatal"))
        m = mock.Mock(id="ins-4", region="ap-guangzhou")
        with self.assertRaises(cloud_common.InfraError):
            cloud_common.terminate_until_gone(p, m)


class PeriodicFetch(unittest.TestCase):
    """While a pass runs, a periodic best-effort copy lands the completed
    artifacts in the same local target directory, so an outage that kills the
    final fetch still leaves what already arrived (2026-10-08)."""

    def test_the_copy_cadence_survives_a_network_outage(self):
        with tempfile.TemporaryDirectory() as d:
            m = CopyingMachine(0, ConnectionError("Name resolution error"), 0)
            stop = StopAfter(3)
            cloud_remote.periodic_fetch(stop, lambda: cloud_common.fetch_results(m, "remote-logs", d, quiet=True))
            self.assertEqual(stop.calls, 4)     # three copies, then stopped
            self.assertEqual(len(m.calls), 6)   # 3 copies x (log directory + run output)
            # The copies that arrived are still on this machine after the outage.
            self.assertTrue(os.path.exists(os.path.join(d, "arrived")))

    def test_a_periodic_copy_never_raises_on_a_failed_transfer(self):
        m = FakeMachine(23)
        with tempfile.TemporaryDirectory() as d:
            cloud_common.fetch_results(m, "remote-logs", d, quiet=True)  # nonzero rsync exit: ignored
            cloud_common.fetch_oracle_results(m, os.path.join(d, "oracle"), quiet=True)
        self.assertEqual(len(m.calls), 4)  # logdir + output + oracle files + oracle.out
        self.assertTrue(all(c[1].get("check") is False for c in m.calls))

class FetchReceipt(unittest.TestCase):
    """The receipt records the wall-clock cutoff of the last successful result
    transfer, so a partial local copy says up to when it is complete
    (HARNESS-06)."""

    def test_the_stamp_is_utc_and_none_without_a_fetch(self):
        self.assertIsNone(cloud_common.fetch_stamp(None))
        self.assertIsNone(cloud_common.fetch_stamp(0))
        self.assertEqual(cloud_common.fetch_stamp(1.0), "1970-01-01T00:00:01Z")


class CloudReceipt(unittest.TestCase):
    """HARNESS-06: a launch leaves the receipt its results are bound to, whether
    or not a machine came up and whether the run succeeded, so a consumer of the
    results never has to guess which invocation produced them."""

    def args(self, **over):
        a = mock.Mock(provider="tencent", arch="arm64", env={}, then=[], oracle=None,
                      bench=["suite --sizes small"])
        for k, v in over.items():
            setattr(a, k, v)
        return a

    def machine(self):
        m = mock.Mock(id="ins-1")
        m.wall.return_value, m.cost.return_value = 100.0, 1.5
        m.offer = Offer(price=0.5, region="ap-shanghai", zone="ap-shanghai-2", itype="SA5.MEDIUM4", vcpus=2, market="spot")
        return m

    def test_a_launched_receipt_binds_the_revision_the_bins_and_the_exit(self):
        r = cloud_common.cloud_receipt(self.args(), "a" * 40, 0, phases={"boot": 1.0, "bench": 2.0},
                                       rust="1.90", crates="/c", machine=self.machine(),
                                       bins=[("base", "b" * 40, "")], then_results=[], fetched_at=1.0, currency="CNY")
        self.assertEqual(r["rev"], "a" * 40)
        self.assertEqual(r["verify_exit"], 0)
        self.assertEqual(r["instance"], "ins-1")
        self.assertEqual(r["wall_s"], 100)
        self.assertEqual(r["bench"], ["suite --sizes small"])
        self.assertEqual(r["bench_bins"], [{"name": "base", "rev": "b" * 40, "features": ""}])
        self.assertEqual(r["fetched_at"], "1970-01-01T00:00:01Z")
        self.assertEqual(r["phases_s"], {"boot": 1, "bench": 2})

    def test_a_run_without_a_machine_still_leaves_its_evidence(self):
        # A refused or failed launch that already fetched something must not
        # vanish: the receipt states the exit status and keeps the failure
        # visible, with only the fields a machine could state omitted.
        r = cloud_common.cloud_receipt(self.args(), "a" * 40, cloud_common.INFRA_FAIL, phases={}, rust="1.90",
                                       crates="/c", machine=None, bins=[], then_results=[], fetched_at=None, currency="CNY")
        self.assertEqual(r["verify_exit"], cloud_common.INFRA_FAIL)
        self.assertNotIn("instance", r)
        self.assertNotIn("wall_s", r)
        self.assertEqual(r["phases_s"], {})
        self.assertIsNone(r["fetched_at"])


class RemoteDeadline(unittest.TestCase):
    """Remote jobs end before the dead-man's switch, so their results can be copied back."""

    def test_no_deadline_without_a_launch_time(self):
        m = mock.Mock(spec=[])
        self.assertIsNone(cloud_common.remote_deadline(m, 1000.0))
        self.assertEqual(cloud_common.deadline_cmd(["bash", "x.sh"], None), ["bash", "x.sh"])

    def test_deadline_boundaries_before_at_and_after_the_fetch_margin(self):
        # HARNESS-08: no floor below the fetch margin. A positive budget this
        # close to the dead-man's switch started a job whose results could not
        # be copied back before the shutdown (2026-10-07).
        m = mock.Mock(dead_at=10_000.0)
        self.assertEqual(cloud_common.remote_deadline(m, 10_000.0 - 3600), 3600 - cloud_common.FETCH_MARGIN_SECS)  # before
        self.assertEqual(cloud_common.remote_deadline(m, 10_000.0 - cloud_common.FETCH_MARGIN_SECS), 0)  # at the cutoff
        self.assertLess(cloud_common.remote_deadline(m, 10_000.0 - 100), 0)  # inside the margin
        self.assertEqual(cloud_common.deadline_cmd(["bash", "x.sh"], 120), ["timeout", "--signal=TERM", "--kill-after=30", "120s", "bash", "x.sh"])

    def test_the_pre_fix_floor_is_the_known_bad_state(self):
        # HARNESS-11 fail-repair-pass on one fixture: the known bad state is the
        # pre-fix floor at an instant with no time left, and the repair is the
        # plain remaining time (negative there).
        m = mock.Mock(dead_at=10_000.0)
        now = 10_000.0 - 100
        self.assertEqual(max(60, int(m.dead_at - cloud_common.FETCH_MARGIN_SECS - now)), 60)  # pre-fix: started a doomed job
        self.assertEqual(cloud_common.remote_deadline(m, now), 100 - cloud_common.FETCH_MARGIN_SECS)  # repaired: refused

    def test_expired_deadline_starts_no_remote_job(self):
        # HARNESS-08: at or past the cutoff nothing is started, so the instance
        # is released with the time left to fetch what earlier passes produced.
        with mock.patch.object(cloud_common, 'log'):
            for when, dead_at in (('at the cutoff', 1000.0 + cloud_common.FETCH_MARGIN_SECS),
                                  ('past the cutoff', 1100.0)):
                with self.subTest(when=when):
                    m = mock.Mock(dead_at=dead_at)
                    with mock.patch.object(cloud_common.time, 'time', return_value=1000.0):
                        with self.assertRaises(cloud_common.InfraError) as raised:
                            cloud_common.run_remote_verify(m, ["python3", "verify.py", "--release"])
                    self.assertIn('no time left to start a remote job', str(raised.exception))
                    m.ssh.assert_not_called()

    def test_time_left_still_starts_the_remote_job(self):
        # Passing control for the refusal above: with a positive deadline the
        # detached job is started and its return code is read.
        m = mock.Mock(dead_at=5000.0, env={})
        m.ssh_cmd.return_value = ['ssh', 'host']
        m.ssh.return_value = mock.Mock(returncode=0, stdout='0\n')
        with mock.patch.object(cloud_common.time, 'time', return_value=1000.0), \
             mock.patch.object(cloud_common, 'subprocess') as subprocess_mod, \
             mock.patch.object(cloud_common, 'log'):
            subprocess_mod.PIPE = object()
            subprocess_mod.Popen.return_value.stdout = iter([])
            code, logdir = cloud_common.run_remote_verify(m, ["python3", "verify.py", "--release"])
        self.assertEqual((code, logdir), (0, None))
        start = next(c.args[0] for c in m.ssh.call_args_list if 'nohup sh -c' in c.args[0])
        self.assertIn('deadline_at = 4700.0', start)  # converted remotely at the actual start

# ------------------------------------------ a session's phases and its cleanup
# The phases of a run live in cloud/remote.py (boot, remote setup, the passes)
# and the single cleanup in cloud/session.py. These drive them with a provider,
# a machine and a ledger double, so what a launch depends on -- the order of the
# ssh wait and the allowlist hook, the dead-man's deadline, the release after a
# failed phase, the receipt and the argv a pass runs -- is observed rather than
# asserted on the text of the file that happens to hold it (HARNESS-11: a
# text-presence test proves neither an order nor a refusal).

BOOT_OFFER = Offer(0.5, "ap-shanghai", "ap-shanghai-2", "SA5.MEDIUM4", 2)


class BootMachine(cloud_common.Machine):
    """A Machine whose ssh wait answers without a connection and records the
    allowlist state as it is at that moment."""

    def __init__(self, provider, offer, proxy=None, *, order):
        super().__init__(provider, offer, proxy)
        self.order = order

    def wait_ssh(self, timeout=300, **kw):
        self.order.append(("wait_ssh", self.access))
        self.ip = "192.0.2.1"


class BootProvider:
    """A provider double for the boot phase: it records every call in `order`,
    launches by handing the machine an id and a launch time, and answers
    `wait_ready`/`terminate` from what the test asked for."""

    home, currency, label_suffix, ssh_user = "/home/tlx", "CNY", "fake", "ubuntu"
    min_lifetime_minutes, ssh_ports = 7, [22]

    def __init__(self, order, fail=None, terminate=True):
        self.order, self.fail, self.terminate_answer = order, fail, terminate
        self.terminated = []

    def public_ips(self, proxy):
        self.order.append("public_ips")
        return ["192.0.2.1"]

    def launch(self, m, ips, fresh, minutes, arch):
        self.order.append(("launch", list(ips), fresh, minutes, arch))
        m.id, m.t_launch = "ins-1", 1000.0

    def find_launched(self, m):
        return m.id

    def wait_ready(self, m):
        self.order.append("wait_ready")
        if self.fail == "wait_ready":
            raise cloud_common.InfraError("boot failed")

    def check_deadman(self, m):
        self.order.append("check_deadman")

    def terminate(self, m):
        self.terminated.append(m.id)
        return self.terminate_answer

    def terminate_hint(self, m):
        return "tccli cvm TerminateInstances --InstanceIds ins-1"

    def leftovers(self, regions, owner=None):
        return []


class SessionCase(testkit.GuardedTestCase):
    """Builds a session whose boot phase runs against the doubles above."""

    extra_args = []

    def setUp(self):
        # Session cleanup ignores signals while releasing the instance; direct
        # fixture calls must restore them before the next test starts.
        for sig in cloud_session.HANDLED_SIGNALS:
            self.addCleanup(signal.signal, sig, signal.getsignal(sig))
        d = tempfile.TemporaryDirectory()
        self.addCleanup(d.cleanup)
        self.dir = d.name
        self.order = []
        self.provider = BootProvider(self.order)
        self.args = self.args_for(*self.extra_args)

    def args_for(self, *argv):
        a = cloud_verify.parse_args(["--quick", "--provider", "tencent", "--max-minutes", "30", "--cc", "clang", *argv])
        a.arch = "x86_64"
        return a

    def session(self, provider=None, machine=None, a=None, **over):
        provider = provider or self.provider
        a = a or self.args
        fields = dict(a=a, provider=provider, owner="worker", ledger=mock.Mock(), admitter=mock.Mock(market="spot"),
                      offers=[BOOT_OFFER], jobs=3, sha="a" * 40, label="abc1234", bins=[], then_shas=[],
                      resolve=lambda r: "sha-" + r, vargs=cloud_setup.verify_args(a, "a" * 40, 3), rust="upstream",
                      crates="upstream", toolchain="1.90", proxy=None, local_dir=self.dir, types=["SA5.MEDIUM4"],
                      tlc=False)
        fields.update(over)
        hooks = cloud_session.Hooks(launch=self.launcher(provider), key=lambda: False)
        session = cloud_session.Session(a=a, plan=cloud_setup.Plan(**fields), cancel=None, hooks=hooks)
        session.machine = machine
        return session

    def launcher(self, provider):
        """The entrypoint's launch adapter: reserve through the ledger, launch,
        and publish the instance this run created."""
        def launch(prov, m, ips, fresh, a, ledger, owner, launched_ids, admitter, cancel):
            self.order.append("launch")
            provider.launch(m, ips, fresh, a.max_minutes, a.arch)
            m.ledger_time = 1000.0
            launched_ids.add(m.id)
        return launch

    def boot(self, session, provider=None):
        provider = provider or self.provider
        with mock.patch.object(cloud_remote, "Machine", functools.partial(BootMachine, order=self.order)):
            cloud_remote.boot(session)


class BootPhase(SessionCase):
    """The launch, the ssh wait and the operator-IP allowlist hook."""

    def test_the_allowlist_hook_is_attached_only_after_ssh_answers(self):
        # It goes in after wait_ssh: during the boot wait a refused connection is
        # sshd not being up yet, and diagnosing that would put a wrong message -
        # and three pointless provider rounds - on every ordinary launch.
        session = self.session()
        self.boot(session)
        self.assertIn(("wait_ssh", None), self.order)
        self.assertEqual(self.order[self.order.index(("wait_ssh", None)) + 1], "check_deadman")
        self.assertIsInstance(session.machine.access, cloud_allowlist.SshAccess)
        self.assertEqual(session.machine.access.written, ["192.0.2.1"])
        self.assertEqual(session.machine.id, "ins-1")

    def test_the_dead_mans_deadline_counts_from_the_launch_time(self):
        session = self.session()
        self.boot(session)
        self.assertEqual(session.machine.dead_at, 1000.0 + 30 * 60)
        self.assertEqual(session.phases["boot"] >= 0, True)

    def test_a_failed_boot_leaves_the_instance_releasable(self):
        self.provider.fail = "wait_ready"
        session = self.session()
        with mock.patch.object(cloud_session, "terminate_until_gone", return_value=True) as release:
            rc = session.run()
        self.assertEqual(rc, cloud_common.INFRA_FAIL)
        self.assertEqual(release.call_args.args[1].id, "ins-1")
        self.assertNotIn("setup", session.phases)      # the failure ended the boot phase

    def test_an_interrupt_stops_the_session_without_a_traceback(self):
        provider = BootProvider(self.order, fail="wait_ready")
        provider.wait_ready = lambda m: (_ for _ in ()).throw(cloud_common.Interrupted("signal 15"))
        session = self.session(provider=provider)
        with mock.patch.object(cloud_session, "terminate_until_gone", return_value=True) as release:
            rc = session.run()
        self.assertEqual(rc, cloud_common.INFRA_FAIL)
        self.assertEqual(release.call_args.args[1].id, "ins-1")

    def test_a_release_that_fails_is_reported_not_raised(self):
        provider = BootProvider(self.order, fail="wait_ready")
        session = self.session(provider=provider)
        with mock.patch.object(cloud_session, "terminate_until_gone", return_value=False), \
             mock.patch("builtins.print") as printed:
            rc = session.run()
        self.assertEqual(rc, cloud_common.INFRA_FAIL)   # never 0 over a live instance
        self.assertIn("COULD NOT RELEASE ins-1",
                      "\n".join(c.args[0] for c in printed.call_args_list if c.args))

    def test_a_terminate_exception_does_not_escape_the_cleanup(self):
        provider = BootProvider(self.order, fail="wait_ready")
        session = self.session(provider=provider)
        with mock.patch.object(cloud_session, "terminate_until_gone", side_effect=RuntimeError("api down")), \
             mock.patch.object(cloud_session, "warning") as warned:
            rc = session.run()
        self.assertEqual(rc, cloud_common.INFRA_FAIL)
        self.assertIn("terminate ins-1 failed", warned.call_args.args[0])


class SessionReceipt(SessionCase):
    """Every invocation that produced a result directory leaves its receipt."""

    def receipt(self):
        return cloud_common.read_receipt(self.dir)

    def boot_failed_session(self):
        """A session whose launch never produced an instance (the provider's
        listing does not know it), so the receipt has only the fields of a
        launch that did not come up."""
        provider = BootProvider(self.order, fail="wait_ready")
        provider.find_launched = lambda m: None
        return self.session(provider=provider)

    def test_a_run_that_never_launched_still_leaves_its_evidence(self):
        # The write used to sit under `if m and provider.find_launched(m)`, so a
        # launch whose instance never appeared left no evidence and the consumer
        # fell back to the newest directory by mtime.
        rc = self.boot_failed_session().run()
        self.assertEqual(rc, cloud_common.INFRA_FAIL)
        receipt = self.receipt()
        self.assertEqual(receipt["verify_exit"], cloud_common.INFRA_FAIL)
        self.assertEqual(receipt["rev"], "a" * 40)
        self.assertNotIn("instance", receipt)          # no machine ever came up
        self.assertNotIn("setup", receipt["phases_s"])   # the boot never finished

    def test_the_receipt_carries_the_fetch_cutoff_of_the_last_copy(self):
        # A run that failed after the instance came up still states the cutoff,
        # so a reader of a partial copy knows up to when it is complete.
        session = self.session()
        session.fetched_at = 1.0
        with mock.patch.object(cloud_remote, "setup_remote", side_effect=cloud_common.InfraError("no toolchain")), \
             mock.patch.object(cloud_remote, "Machine", functools.partial(BootMachine, order=self.order)), \
             mock.patch.object(cloud_session, "terminate_until_gone", return_value=True):
            rc = session.run()
        self.assertEqual(rc, cloud_common.INFRA_FAIL)
        receipt = self.receipt()
        self.assertEqual(receipt["fetched_at"], "1970-01-01T00:00:01Z")
        self.assertEqual(receipt["instance"], "ins-1")


class PassCopies(SessionCase):
    """What a pass runs and how its results come back."""

    extra_args = ["--suites", "build"]

    def run_passes(self, machine, remote_verify, period=0.01):
        session = self.session(machine=machine)
        with mock.patch.object(cloud_remote, "run_remote_verify", remote_verify), \
             mock.patch.object(cloud_remote, "PERIODIC_FETCH_SECS", period):
            cloud_remote.passes(session)
        return session

    def test_the_periodic_and_final_copies_share_one_target(self):
        # The periodic copy and the final receipt share one destination, so the
        # final fetch is an increment of the periodic one and not a second
        # destination (the file that arrived is not re-copied elsewhere, and a
        # partial copy is complete up to fetched_at).
        machine = CopyingMachine(0)

        def remote_verify(m, argv, on_logdir=None):
            if on_logdir:
                on_logdir("remote-logs")
            time.sleep(0.05)               # long enough for a few periodic copies
            return 0, "remote-logs"

        session = self.run_passes(machine, remote_verify)
        destinations = {dest.rstrip("/") if dest.endswith("/") else os.path.dirname(dest)
                        for dest in (c[0][-1] for c in machine.calls)}
        self.assertEqual(destinations, {self.dir})         # one destination for both copies
        self.assertGreaterEqual(len(machine.calls), 4)     # at least two copies: logdir + output
        self.assertTrue(os.path.exists(os.path.join(self.dir, "arrived")))
        self.assertIsInstance(session.fetched_at, float)
        self.assertIn("verify", session.phases)
        self.assertIn("fetch", session.phases)

    def test_a_failed_pass_still_fetches_what_arrived(self):
        machine = CopyingMachine(0)
        session = self.run_passes(machine, lambda m, argv, on_logdir=None: (1, "remote-logs"))
        self.assertEqual(session.rc, 1)                    # the pass's own exit, not a blanket 0
        self.assertTrue(os.path.exists(os.path.join(self.dir, "arrived")))

    def test_the_pass_runs_the_plans_argv_verbatim(self):
        # `--bench`/`--then` are shell-word strings; the argv built from them
        # reaches the remote command without a second shell pass over it.
        a = cloud_verify.parse_args(["--quick", "--suites", "build",
                                     "--then", "--suites corpus-compile --env 'PAYLOAD=a b; rm -rf /'"])
        a.arch = "x86_64"
        seen = []
        session = self.session(machine=FakeMachine(0),
                               vargs=cloud_setup.verify_args(a, "a" * 40, 3))
        session.a = a

        def remote_verify(m, argv, on_logdir=None):
            seen.append(list(argv))
            return 0, None

        with mock.patch.object(cloud_remote, "run_remote_verify", remote_verify):
            cloud_remote.passes(session)
        self.assertEqual(seen[0], ["env", "CC=clang", "python3", "scripts/verify.py", "a" * 40,
                                   "--quick", "-j", "3", "--suites", "build"])
        self.assertEqual(seen[1], ["env", "CC=clang", "python3", "scripts/verify.py", "a" * 40,
                                   "--quick", "-j", "3", "--suites", "corpus-compile",
                                   "--env", "PAYLOAD=a b; rm -rf /"])
        self.assertEqual(session.then_results, [{"args": seen[1][4:], "exit": 0}])

    def test_the_worst_pass_exit_is_the_runs(self):
        a = cloud_verify.parse_args(["--quick", "--suites", "build", "--then", "--suites corpus-compile"])
        a.arch = "x86_64"
        codes = iter([0, 3])
        session = self.session(machine=FakeMachine(0), vargs=cloud_setup.verify_args(a, "a" * 40, 3))
        session.a = a
        with mock.patch.object(cloud_remote, "run_remote_verify", lambda m, argv, on_logdir=None: (next(codes), None)):
            cloud_remote.passes(session)
        self.assertEqual(session.rc, 3)


class ScriptMachine(CopyingMachine):
    """A machine double that also records the driver script written over ssh."""

    dead_at = None
    offer = BOOT_OFFER

    def __init__(self, *answers):
        super().__init__(*answers)
        self.scripts = []

    def ssh(self, script, check=True, capture=False):
        self.scripts.append(script)
        return mock.Mock(returncode=0, stdout="", stderr="")


class PreparePhase(SessionCase):
    """What the instance is set up to run: one driver script per mode, written
    once, then run as one pass whose results come back."""

    def test_bench_mode_writes_the_driver_and_brings_the_bench_results_back(self):
        machine = ScriptMachine(0)
        session = self.session(a=self.args_for("--bench", "run --models KeyValueStore/MCKVSSafetySmall"),
                               machine=machine)
        with mock.patch.object(cloud_remote, "setup_remote"), \
             mock.patch.object(cloud_remote, "run_remote_verify", lambda m, argv, on_logdir=None: (0, None)):
            cloud_remote.prepare(session)
            cloud_remote.passes(session)
        self.assertIn("TLX_BENCH_EOF", machine.scripts[0])
        self.assertIn("scripts/bench.py run --models KeyValueStore/MCKVSSafetySmall", machine.scripts[0])
        self.assertTrue(os.path.exists(os.path.join(self.dir, "arrived")))   # the bench results came back
        self.assertIn("bench", session.phases)

    def test_a_bench_run_with_then_runs_the_benchmarks_then_the_verify_passes(self):
        # 2026-10-10: `--then` after `--bench`: the benchmark commands run first
        # and the verify.py passes follow on the same instance, so one launch
        # produces both (they used to need two launches, with the refuser
        # pointing at "run any verify.py pass in a second invocation").
        machine = ScriptMachine(0)
        session = self.session(a=self.args_for("--bench", "run --models Keymobile/MCKeySafe",
                                               "--then", "--suites corpus-compile"), machine=machine)
        seen = []

        def remote_verify(m, argv, on_logdir=None):
            seen.append(list(argv))
            return 0, None

        with mock.patch.object(cloud_remote, "setup_remote"), \
             mock.patch.object(cloud_remote, "run_remote_verify", remote_verify):
            cloud_remote.prepare(session)
            cloud_remote.passes(session)
        home = self.provider.home
        self.assertEqual(seen[0], ["bash", f"{home}/bench-driver.sh"])
        self.assertEqual(seen[1][:4], ["env", "CC=clang", "python3", "scripts/verify.py"])
        self.assertIn("--suites", seen[1])
        self.assertEqual(session.then_results, [{"args": seen[1][4:], "exit": 0}])
        self.assertIn("then-1", session.phases)          # the then pass's own runtime is timed
        self.assertIsNotNone(session.fetched_at)

    def test_oracle_mode_writes_the_oracle_driver_and_brings_the_tlc_results_back(self):
        machine = ScriptMachine(0)
        session = self.session(a=self.args_for("--oracle", "tlc --source external --tier medium"), machine=machine)
        with mock.patch.object(cloud_remote, "setup_remote"), \
             mock.patch.object(cloud_remote, "run_remote_verify", lambda m, argv, on_logdir=None: (2, None)):
            cloud_remote.prepare(session)
            cloud_remote.passes(session)
        self.assertIn("TLX_ORACLE_EOF", machine.scripts[0])
        self.assertIn("scripts/corpus.py tlc --source external --tier medium", machine.scripts[0])
        self.assertEqual(session.rc, 2)
        self.assertTrue(os.path.exists(os.path.join(self.dir, "oracle", "arrived")))


class EntrypointAdapters(testkit.GuardedTestCase):
    """`run_checked` hands the session the two adapters the phase modules must
    not import (HARNESS-03: a library never imports the CLI). The lookup happens
    when the run starts and not at import, which is why a test that patches the
    entrypoint's own name still patches what the boot phase calls."""

    def plan_of(self, ssh_proxy="none"):
        """The (plan, hooks, patched names) `run_checked` builds for one launch.

        Every provider call, the ledger, the two preflights and the session are
        doubles: only the entrypoint's own resolution runs.
        """
        a = cloud_verify.parse_args(["--quick", "--provider", "tencent"])
        provider = mock.MagicMock(min_lifetime_minutes=0, currency="CNY", default_arch="x86_64",
                                  default_regions=["r"], default_ssh_proxy=ssh_proxy, label_suffix="fake")
        provider.offers.return_value = [Offer(0.5, "r", "z", "fake", 2)]
        provider.check_account.return_value = "fake"
        provider.default_types.return_value = ["fake"]
        with mock.patch.object(cloud_verify, "current_owner", return_value="worker"), \
             mock.patch.object(cloud_verify, "git", return_value="a" * 40), \
             mock.patch.object(cloud_verify, "local_toolchain", return_value="1.90"), \
             mock.patch.object(cloud_verify, "clippy_preflight", return_value=(True, "ok")), \
             mock.patch.object(cloud_verify, "make_provider", return_value=provider), \
             mock.patch.object(cloud_verify, "LaunchLedger", return_value=mock.MagicMock()), \
             mock.patch.object(cloud_verify, "ensure_local_key", return_value=False) as key, \
             mock.patch.object(cloud_verify, "launch_with_quota_wait") as launch, \
             mock.patch.object(cloud_verify, "Session") as session_cls:
            cloud_verify.run_checked(a, cloud_verify.Cancel())
        return session_cls.call_args.args[1], session_cls.call_args.args[3], session_cls, launch, key

    def test_the_environment_proxy_is_resolved_for_a_provider_that_defaults_to_it(self):
        # aws (and --ssh-proxy auto) asks for this machine's https_proxy; the
        # lookup lives with the plan, and this is the path that reached a name
        # the phases move had left behind: imported nowhere and only read there,
        # so nothing but driving it could have found it.
        # (Every other spelling is cleared: this machine's own proxy would win.)
        with mock.patch.dict(os.environ, {"https_proxy": "", "http_proxy": "", "HTTP_PROXY": "",
                                          "HTTPS_PROXY": "http://proxy.test:3128"}):
            plan, _, _, _, _ = self.plan_of(ssh_proxy="auto")
        self.assertEqual(plan.proxy, "proxy.test:3128")
        plan, _, _, _, _ = self.plan_of(ssh_proxy="none")
        self.assertIsNone(plan.proxy)

    def test_run_checked_hands_the_session_its_own_adapters(self):
        plan, hooks, session_cls, launch, key = self.plan_of()
        self.assertIs(hooks.launch, launch)           # the boot phase launches through this module's name
        self.assertIs(hooks.key, key)
        self.assertEqual((plan.sha, plan.owner), ("a" * 40, "worker"))
        self.assertEqual([o.price for o in plan.offers], [0.5])
        session_cls.return_value.run.assert_called_once()


def undefined_names(path):
    """Global names `path` reads but never binds (a move that leaves one behind).

    Only a call reaches it: a name dropped by a move is not an ImportError, it
    is a NameError on the one branch that uses it. `env_proxy` was lost this way
    when the phases moved -- `run_checked` resolved it only for a provider whose
    ssh proxy defaults to `auto`, so nothing but driving aws found it
    (done_check's ownership listing did). A file with a star import is skipped:
    what it binds cannot be known statically.
    """
    tree = ast.parse(open(path, encoding="utf-8").read())
    if any(isinstance(n, ast.ImportFrom) and any(a.name == "*" for a in n.names) for n in ast.walk(tree)):
        return []
    bound = set(dir(builtins)) | {"__file__", "__name__", "__doc__", "__package__"}
    for node in ast.walk(tree):
        if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
            bound.add(node.name)
        elif isinstance(node, ast.Name) and isinstance(node.ctx, ast.Store):
            bound.add(node.id)
        elif isinstance(node, ast.arg):
            bound.add(node.arg)
        elif isinstance(node, (ast.Import, ast.ImportFrom)):
            bound.update((n.asname or n.name).split(".")[0] for n in node.names)
        elif isinstance(node, ast.ExceptHandler) and node.name:
            bound.add(node.name)
        elif isinstance(node, ast.Global):
            bound.update(node.names)
    return sorted({n.id for n in ast.walk(tree) if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Load)} - bound)


class MovedPhaseModules(testkit.GuardedTestCase):
    """The phases this batch moved read only names they bind or import."""

    def test_the_driver_and_its_phase_modules_have_no_undefined_name(self):
        for name in ("cloud_verify.py", os.path.join("cloud", "setup.py"), os.path.join("cloud", "remote.py"),
                     os.path.join("cloud", "session.py")):
            with self.subTest(module=name):
                self.assertEqual(undefined_names(os.path.join(os.path.dirname(os.path.dirname(os.path.abspath(__file__))), name)), [])

    def test_the_check_catches_a_name_a_move_left_behind(self):
        # HARNESS-11: the known-bad state is the real one this guard was written
        # for -- the moved `env_proxy`, still read by the entrypoint.
        with tempfile.TemporaryDirectory() as d:
            path = os.path.join(d, "moved.py")
            with open(path, "w", encoding="utf-8") as f:
                f.write("def run(a):\n    return env_proxy() if a else None\n")
            self.assertEqual(undefined_names(path), ["env_proxy"])
            with open(path, "w", encoding="utf-8") as f:
                f.write("def env_proxy():\n    return None\n\n\ndef run(a):\n    return env_proxy() if a else None\n")
            self.assertEqual(undefined_names(path), [])


class DryRun(unittest.TestCase):
    """--dry-run prints the plan and creates nothing (a dry run that called the
    provider's create path would cost a launch to answer a question)."""

    def test_it_plans_renders_both_decisions_and_launches_nothing(self):
        offers = [Offer(0.5, "ap-shanghai", "ap-shanghai-2", "SA5.MEDIUM4", 2, deprioritized=True),
                  Offer(0.4, "ap-shanghai", "ap-shanghai-3", "SA5.SMALL2", 2)]
        self.assertEqual(cloud_setup.offer_lines(cloud_common.rank_offers(offers), "CNY"),
                         ["  spot SA5.SMALL2 (2 vCPUs) ap-shanghai-3: 0.4000 CNY/h",
                          "  spot SA5.MEDIUM4 (2 vCPUs) ap-shanghai-2: 0.5000 CNY/h (tried last)"])
        provider = mock.Mock(min_lifetime_minutes=7, currency="CNY")
        provider.describe_plan.return_value = ["DryRun: would succeed"]
        decision = mock.Mock(ok=True, reason="")
        decision.by_owner.return_value = "worker 1"
        admitter = mock.Mock(market="spot", view_fn=lambda: ([], 0.0), decide=lambda view, rows: decision)
        lines = []
        with mock.patch.object(cloud_setup, "log", side_effect=lines.append):
            cloud_setup.dry_run(cloud_verify.parse_args(["--quick", "--provider", "tencent"]),
                                offers[0], provider, admitter, mock.MagicMock())
        self.assertIn("dry run: DryRun: would succeed", lines)
        self.assertIn("dry run: slots by owner: worker 1", lines)
        self.assertIn("dry run: a launch now would be admitted", lines)
        self.assertEqual(lines[-1], "dry run: nothing launched")
        provider.launch.assert_not_called()


# ------------------------------------------------- the operator-IP allowlist
# Every provider writes the ssh security group for this machine's public address
# as it is at launch time and nothing re-checks it. The address moves on its own
# (the ISP moved it 1.202.18.10 -> 61.149.241.75 on 2026-10-08) and the result is
# indistinguishable from a dead instance to ssh, rsync and git-over-ssh: the
# whole retry budget is spent, then a bare exit 3, while the remote job is
# healthy. Two waves were lost that way before any of it was diagnosed.
SSH_IP_MOVED = ("ssh: connect to host 1.2.3.4 port 22: Operation timed out\n"
                "rsync: connection unexpectedly closed (0 bytes received so far) [sender]\n"
                "rsync error: unexplained error (code 255) at io.c(228) [sender=3.2.7]\n")
SSH_REACHED = "ubuntu@1.2.3.4: Permission denied (publickey).\n"
RSYNC_VANISHED = "rsync: some files vanished before they could be transferred (code 24) at main.c(1338)\n"

OLD_IP, NEW_IP = "1.202.18.10", "61.149.241.75"


def process(returncode, stderr=""):
    """A completed-child double as subprocess.run returns it (bytes, as the
    transports read them)."""
    return mock.Mock(returncode=returncode, stdout=b"", stderr=stderr.encode())


class AllowlistProvider:
    """A provider double for the allowlist transport: records every read of the
    instance's state and every security-group write, and answers the state and
    this machine's address the test sets."""

    name, ssh_user, ssh_ports = "tencent", "ubuntu", [22, 443, 2222]

    def __init__(self, state="running", ips=(NEW_IP,), write_error=None):
        self.state, self.ips, self.write_error = state, list(ips), write_error
        self.states, self.writes, self.hints = [], [], []

    def instance_state(self, m):
        self.states.append(m.id)
        return self.state

    def public_ips(self, proxy):
        return list(self.ips)

    def allow_ssh(self, m, ips):
        self.writes.append(list(ips))
        if self.write_error:
            raise self.write_error
        return f"security group sg-1: ssh allowed from {', '.join(ips)} (3 new rule(s))"

    def allow_hint(self, m, ips):
        self.hints.append(list(ips))
        return f"tccli vpc CreateSecurityGroupPolicies --SecurityGroupId sg-1 --SecurityGroupPolicies {','.join(ips)}"


class OperatorAllowlist(testkit.GuardedTestCase):
    """The ssh transport of a running run depends on a security-group rule that
    is written once, at launch, and never re-checked. These are the two lost
    waves of 2026-10-08/09 as tests: the trigger is this machine's egress
    address moving, the instance and its remote job staying healthy."""

    def setUp(self):
        quiet = mock.patch.object(cloud_allowlist, "log")
        quiet.start()
        self.addCleanup(quiet.stop)
        warn = mock.patch.object(cloud_allowlist, "warning")
        self.warn = warn.start()
        self.addCleanup(warn.stop)
        # The real Machine.run, with only the child process faked: the ssh,
        # rsync and git-over-ssh argv shapes are the production ones.
        run = mock.patch.object(cloud_common.subprocess, "run")
        self.child = run.start()
        self.addCleanup(run.stop)

    def machine(self, provider, ips=(OLD_IP,), attach=True):
        m = cloud_common.Machine(provider, Offer(0.16, "ap-shanghai", "ap-shanghai-5", "SA5.4XLARGE32", 16))
        m.id, m.ip, m.proxy = "ins-1", "1.2.3.4", None
        if attach:
            m.access = cloud_allowlist.SshAccess(provider, m, list(ips), sleep=lambda secs: None)
        return m

    def answers(self, *codes):
        """subprocess.run answers with these exit codes in order (and then the
        last one for ever), with the moved-address stderr on every failure."""
        pending = list(codes)

        def answer(cmd, **kw):
            code = pending.pop(0) if len(pending) > 1 else pending[0]
            return process(code, SSH_IP_MOVED if code else "")
        self.child.side_effect = answer

    def warnings(self):
        return " ".join(str(c.args[0]) for c in self.warn.call_args_list)

    def test_without_the_hook_a_moved_address_is_a_bare_transport_failure(self):
        # Known bad: the incident. No access hook, so an ssh call, an rsync
        # transfer and a git push over ssh each fail the same opaque way, no
        # provider call happens, and nothing says what changed.
        provider = AllowlistProvider()
        m = self.machine(provider, attach=False)
        self.answers(255)
        self.assertEqual(m.run(["ssh", "-i", "k", "ubuntu@1.2.3.4", "true"]).returncode, 255)
        self.answers(255)
        self.assertEqual(m.run(["rsync", "-az", "-e", "ssh -i k", "src", "ubuntu@1.2.3.4:dst"]).returncode, 255)
        self.answers(128)
        self.assertEqual(m.run(["git", "push", "ssh://ubuntu@1.2.3.4/home/tlx", "rev"]).returncode, 128)
        self.assertEqual((provider.states, provider.writes), ([], []))

    def test_a_changed_operator_ip_recovers_on_the_retry(self):
        # The fix. The address is now NEW_IP, the rules were written with
        # OLD_IP, the instance is running: the allowlist is re-applied once for
        # the current address and the command that failed is simply run again.
        provider = AllowlistProvider()
        m = self.machine(provider)
        self.answers(255, 0)
        p = m.run(["rsync", "-az", "-e", "ssh -i k", "src", "ubuntu@1.2.3.4:dst"])
        self.assertEqual(p.returncode, 0)                      # the run continues
        self.assertEqual(provider.writes, [[NEW_IP]])          # once, for the current address
        self.assertEqual(provider.states, ["ins-1"])
        self.assertEqual(self.child.call_count, 2)
        self.assertIn("may be the operator-IP allowlist or a network outage", self.warnings())
        self.assertIn(NEW_IP, self.warnings())
        self.assertIn(OLD_IP, self.warnings())
        self.assertIn("tccli vpc CreateSecurityGroupPolicies", self.warnings())

    def test_the_same_repair_covers_ssh_and_git_over_ssh(self):
        # One hook under Machine.run, so every transport of the run is covered,
        # not just the transfers that were noticed first.
        for cmd in (["ssh", "-i", "k", "ubuntu@1.2.3.4", "true"],
                    ["git", "push", "ssh://ubuntu@1.2.3.4/home/tlx", "rev"]):
            with self.subTest(command=cmd[0]):
                provider = AllowlistProvider()
                m = self.machine(provider)
                self.answers(255, 0)
                self.assertEqual(m.run(cmd).returncode, 0)
                self.assertEqual(provider.writes, [[NEW_IP]])

    def test_a_healthy_instance_with_an_unchanged_address_still_gets_the_rule_re_applied(self):
        # The address did not move but the rule did (a concurrent launch
        # reconciles the same shared group and revokes it): the re-apply is
        # add-only and idempotent, so the transport recovers anyway.
        provider = AllowlistProvider(ips=(OLD_IP,))
        m = self.machine(provider)
        self.answers(255, 0)
        self.assertEqual(m.run(["ssh", "-i", "k", "ubuntu@1.2.3.4", "true"]).returncode, 0)
        self.assertEqual(provider.writes, [[OLD_IP]])

    def test_a_dead_instance_is_not_an_allowlist_problem(self):
        # The control: a genuinely dead instance must still stop the run. No
        # security-group write is made, and the message names the instance.
        for state in ("gone", "stopped"):
            with self.subTest(state=state):
                self.child.reset_mock()
                provider = AllowlistProvider(state=state)
                m = self.machine(provider)
                self.answers(255)
                self.assertEqual(m.run(["ssh", "-i", "k", "ubuntu@1.2.3.4", "true"]).returncode, 255)
                self.assertEqual(provider.writes, [])
                self.assertEqual(self.child.call_count, 1)     # no retry against a dead host
                self.assertIn(f"reports it {state}", self.warnings())
                self.assertIn("the instance, not the ssh allowlist, is the problem", self.warnings())

    def test_an_unreadable_state_does_not_change_the_group_on_a_guess(self):
        provider = AllowlistProvider(state=None)
        m = self.machine(provider)
        self.answers(255)
        self.assertEqual(m.run(["ssh", "-i", "k", "ubuntu@1.2.3.4", "true"]).returncode, 255)
        self.assertEqual(provider.writes, [])
        self.assertIn("not changing the ssh allowlist on a guess", self.warnings())
        self.assertIn("tccli vpc CreateSecurityGroupPolicies", self.warnings())

    def test_the_provider_budget_is_bounded(self):
        # An ISP that keeps moving the address, or a transport that never
        # recovers: at most MAX_ROUNDS reads of the state and MAX_ROUNDS
        # security-group writes for one instance in one run.
        provider = AllowlistProvider()
        m = self.machine(provider)
        self.answers(255)
        for _ in range(20):
            self.assertEqual(m.run(["ssh", "-i", "k", "ubuntu@1.2.3.4", "true"]).returncode, 255)
        self.assertEqual(len(provider.states), cloud_allowlist.MAX_ROUNDS)
        self.assertEqual(len(provider.writes), cloud_allowlist.MAX_ROUNDS)
        self.assertIn("already diagnosed", self.warnings())

    def test_a_retry_loop_gets_one_diagnosis_not_one_per_attempt(self):
        # The caller's own retry loop hands the same failure back every attempt:
        # a worker reads one actionable message, not ten copies of it.
        provider = AllowlistProvider(state="gone")
        m = self.machine(provider)
        self.answers(255)
        for _ in range(20):
            m.run(["ssh", "-i", "k", "ubuntu@1.2.3.4", "true"])
        self.assertLessEqual(self.warn.call_count, 2)   # the diagnosis and the budget note, once each
        # The provider work is the round budget, not one round per attempt.
        self.assertEqual(len(provider.states), cloud_allowlist.MAX_ROUNDS)

    def test_a_provider_that_cannot_write_names_the_command_by_hand(self):
        provider = AllowlistProvider(write_error=RuntimeError("UnauthorizedOperation"))
        m = self.machine(provider)
        self.answers(255)
        self.assertEqual(m.run(["ssh", "-i", "k", "ubuntu@1.2.3.4", "true"]).returncode, 255)
        self.assertEqual(self.child.call_count, 1)
        self.assertIn("UnauthorizedOperation", self.warnings())
        self.assertIn("add it by hand", self.warnings())
        self.assertIn("tccli vpc CreateSecurityGroupPolicies", self.warnings())

    def test_a_failure_that_reached_the_host_is_not_an_allowlist_problem(self):
        # The host answered: the packets got there, so the allowlist is fine.
        provider = AllowlistProvider()
        m = self.machine(provider)
        self.child.side_effect = [process(255, SSH_REACHED)]
        self.assertEqual(m.run(["ssh", "-i", "k", "ubuntu@1.2.3.4", "true"]).returncode, 255)
        self.assertEqual((provider.states, provider.writes), ([], []))

    def test_a_transfer_that_failed_for_another_reason_is_left_alone(self):
        provider = AllowlistProvider()
        m = self.machine(provider)
        self.child.side_effect = [process(24, RSYNC_VANISHED)]
        self.assertEqual(m.run(["rsync", "-az", "-e", "ssh -i k", "src", "ubuntu@1.2.3.4:dst"]).returncode, 24)
        self.assertEqual((provider.states, provider.writes), ([], []))

    def test_a_local_command_is_never_an_ssh_allowlist_problem(self):
        # A local build's log can contain the very words of an ssh timeout;
        # only a command that actually reaches the instance is diagnosed.
        provider = AllowlistProvider()
        m = self.machine(provider)
        self.child.side_effect = [process(1, "test_connect ... Connection timed out\n")]
        self.assertEqual(m.run(["target/release/tlx", "check", "spec"]).returncode, 1)
        self.assertEqual((provider.states, provider.writes), ([], []))

    def test_the_transport_shapes_are_recognised(self):
        self.assertTrue(cloud_allowlist.over_ssh(["ssh", "-i", "k", "host", "true"]))
        self.assertTrue(cloud_allowlist.over_ssh(["rsync", "-az", "-e", "ssh -i k", "a", "b"]))
        self.assertTrue(cloud_allowlist.over_ssh(["git", "push", "ssh://ubuntu@h/tlx", "rev"]))
        self.assertFalse(cloud_allowlist.over_ssh(["rsync", "-az", "a", "b"]))       # local copy
        self.assertFalse(cloud_allowlist.over_ssh(["git", "push", "origin", "rev"]))
        self.assertFalse(cloud_allowlist.over_ssh(["python3", "verify.py"]))


class AllowlistProviders(testkit.GuardedTestCase):
    """The provider side of the recovery: the security-group change must only
    ever ADD this machine's current address to this project's own group. No
    rule is revoked, no group is created, nothing is opened to 0.0.0.0/0 and
    another owner's group is never touched."""

    def test_tencent_adds_the_current_address_and_revokes_nothing(self):
        policies = {"SecurityGroupPolicySet": {"Ingress": [
            {"PolicyIndex": 0, "Protocol": "TCP", "Port": "22", "CidrBlock": f"{OLD_IP}/32", "Action": "ACCEPT"},
            {"PolicyIndex": 1, "Protocol": "TCP", "Port": "443", "CidrBlock": f"{OLD_IP}/32", "Action": "ACCEPT"},
            {"PolicyIndex": 2, "Protocol": "TCP", "Port": "2222", "CidrBlock": f"{OLD_IP}/32", "Action": "ACCEPT"}]}}
        f = FakeTccli({"DescribeSecurityGroups": {"SecurityGroupSet": [{"SecurityGroupId": "sg-1"}]},
                       "DescribeSecurityGroupPolicies": policies})
        self._with_tccli(f)
        p = cloud_tencent.TencentProvider()
        m = mock.Mock(region="ap-shanghai", id="ins-1")
        note = p.allow_ssh(m, [NEW_IP])
        self.assertIn("sg-1", note)
        self.assertIn(NEW_IP, note)
        self.assertEqual(f.apis(), ["DescribeSecurityGroups", "DescribeSecurityGroupPolicies", "CreateSecurityGroupPolicies"])
        added = f.calls[2][2]["SecurityGroupPolicySet"]["Ingress"]
        self.assertEqual({(r["Port"], r["CidrBlock"]) for r in added},
                         {(port, f"{NEW_IP}/32") for port in ("22", "443", "2222")})
        self.assertNotIn("0.0.0.0/0", json.dumps(added))
        # The old address stays allowed: the recovery only ever adds.
        self.assertNotIn("DeleteSecurityGroupPolicies", f.apis())

    def test_tencent_allow_ssh_is_idempotent(self):
        policies = {"SecurityGroupPolicySet": {"Ingress": [
            {"Protocol": "TCP", "Port": port, "CidrBlock": f"{NEW_IP}/32", "Action": "ACCEPT"}
            for port in ("22", "443", "2222")]}}
        f = FakeTccli({"DescribeSecurityGroups": {"SecurityGroupSet": [{"SecurityGroupId": "sg-1"}]},
                       "DescribeSecurityGroupPolicies": policies})
        self._with_tccli(f)
        m = mock.Mock(region="ap-shanghai", id="ins-1")
        note = cloud_tencent.TencentProvider().allow_ssh(m, [NEW_IP])
        self.assertEqual(f.apis(), ["DescribeSecurityGroups", "DescribeSecurityGroupPolicies"])
        self.assertIn("already present", note)

    def test_tencent_allow_hint_names_the_call_and_never_raises(self):
        f = FakeTccli({"DescribeSecurityGroups": {"SecurityGroupSet": [{"SecurityGroupId": "sg-1"}]}})
        self._with_tccli(f)
        m = mock.Mock(region="ap-shanghai", id="ins-1")
        hint = cloud_tencent.TencentProvider().allow_hint(m, [NEW_IP])
        self.assertIn("tccli vpc CreateSecurityGroupPolicies", hint)
        self.assertIn("--SecurityGroupId sg-1", hint)
        self.assertIn(f"{NEW_IP}/32", hint)
        # A provider that cannot even be asked still yields a usable line.
        self._with_tccli(FakeTccli({"DescribeSecurityGroups": cloud_tencent.TencentError("Unauthorized", "no", [])}))
        self.assertIn("CreateSecurityGroupPolicies", cloud_tencent.TencentProvider().allow_hint(m, [NEW_IP]))

    def test_tencent_missing_group_is_an_infra_error_not_a_new_group(self):
        f = self._with_tccli(FakeTccli({"DescribeSecurityGroups": {"SecurityGroupSet": []}}))
        with self.assertRaises(cloud_common.InfraError):
            cloud_tencent.TencentProvider().allow_ssh(mock.Mock(region="ap-shanghai", id="ins-1"), [NEW_IP])
        self.assertEqual(f.apis(), ["DescribeSecurityGroups"])   # nothing was created

    def test_tencent_instance_state(self):
        p = cloud_tencent.TencentProvider()
        m = mock.Mock(region="ap-shanghai", id="ins-1")
        for instance_state, want in ((None, "gone"), ("RUNNING", "running"), ("STOPPED", "stopped"),
                                     ("TERMINATED", "gone"), ("SHUTDOWN", "stopped"), ("PENDING", "running")):
            with self.subTest(state=instance_state):
                inst = [] if instance_state is None else [{"InstanceId": "ins-1", "InstanceState": instance_state}]
                self._with_tccli(FakeTccli({"DescribeInstances": {"InstanceSet": inst}}))
                self.assertEqual(p.instance_state(m), want)

    def test_aliyun_adds_the_current_address_and_revokes_nothing(self):
        perms = {"Permissions": {"Permission": [
            {"IpProtocol": "tcp", "PortRange": port, "SourceCidrIp": f"{OLD_IP}/32"} for port in ("22/22", "443/443", "2222/2222")]}}
        cli = self._with_aliyun({"DescribeVpcs": {"Vpcs": {"Vpc": [{"VpcId": "vpc-1"}]}},
                                 "DescribeSecurityGroups": {"SecurityGroups": {"SecurityGroup": [{"SecurityGroupId": "sg-1"}]}},
                                 "DescribeSecurityGroupAttribute": perms})
        m = mock.Mock(region="cn-hangzhou", id="i-1")
        note = cloud_aliyun.AliyunProvider().allow_ssh(m, [NEW_IP])
        self.assertIn("sg-1", note)
        self.assertEqual([c[1] for c in cli.calls], ["DescribeVpcs", "DescribeSecurityGroups", "DescribeSecurityGroupAttribute",
                                                     "AuthorizeSecurityGroup", "AuthorizeSecurityGroup", "AuthorizeSecurityGroup"])
        for call in cli.calls[3:]:
            self.assertEqual(call[2][call[2].index("--SourceCidrIp") + 1], f"{NEW_IP}/32")
            self.assertNotIn("Revoke", call[1])

    def test_aliyun_instance_state(self):
        p = cloud_aliyun.AliyunProvider()
        m = mock.Mock(region="cn-hangzhou", id="i-1")
        for status, want in ((None, "gone"), ("Running", "running"), ("Stopped", "stopped"),
                             ("Deleted", "gone"), ("Pending", "running")):
            with self.subTest(status=status):
                inst = [] if status is None else [{"InstanceId": "i-1", "Status": status}]
                self._with_aliyun({"DescribeInstances": {"Instances": {"Instance": inst}}})
                self.assertEqual(p.instance_state(m), want)

    def test_aws_adds_the_current_address_and_revokes_nothing(self):
        sg = {"GroupId": "sg-1", "IpPermissions": [
            {"IpProtocol": "tcp", "FromPort": 22, "ToPort": 22, "IpRanges": [{"CidrIp": f"{OLD_IP}/32"}]}]}
        ec2 = mock.Mock()
        ec2.describe_security_groups.return_value = {"SecurityGroups": [sg]}
        ec2.describe_vpcs.return_value = {"Vpcs": [{"VpcId": "vpc-1"}]}
        aws = self._aws(ec2)
        aws.owner = "test-owner"
        m = mock.Mock(region="ap-northeast-1", id="i-1")
        note = aws.allow_ssh(m, [NEW_IP])
        self.assertIn("sg-1", note)
        ec2.authorize_security_group_ingress.assert_called_once_with(GroupId="sg-1", IpPermissions=[
            {"IpProtocol": "tcp", "FromPort": 22, "ToPort": 22,
             "IpRanges": [{"CidrIp": f"{NEW_IP}/32", "Description": "cloud_verify:test-owner"}]}])
        ec2.revoke_security_group_ingress.assert_not_called()

    def test_aws_instance_state(self):
        patch_botocore = contextlib.nullcontext()
        try:
            from botocore.exceptions import ClientError
        except ModuleNotFoundError:
            import types

            class ClientError(Exception):
                def __init__(self, response, operation_name):
                    super().__init__(operation_name)
                    self.response = response

            botocore = types.ModuleType("botocore")
            exceptions = types.ModuleType("botocore.exceptions")
            exceptions.ClientError = ClientError
            botocore.exceptions = exceptions
            patch_botocore = mock.patch.dict(sys.modules, {"botocore": botocore, "botocore.exceptions": exceptions})
        with patch_botocore:
            aws = cloud_aws.AwsProvider()
            m = mock.Mock(region="ap-northeast-1", id="i-1")
            for state, want in (("running", "running"), ("stopped", "stopped"), ("terminated", "gone"),
                                ("shutting-down", "gone"), ("pending", "running")):
                with self.subTest(state=state):
                    ec2 = mock.Mock()
                    ec2.describe_instances.return_value = {"Reservations": [{"Instances": [{"State": {"Name": state}}]}]}
                    with mock.patch.object(aws, "ec2", return_value=ec2):
                        self.assertEqual(aws.instance_state(m), want)
            ec2 = mock.Mock()
            ec2.describe_instances.side_effect = ClientError({"Error": {"Code": "InvalidInstanceID.NotFound"}}, "DescribeInstances")
            with mock.patch.object(aws, "ec2", return_value=ec2):
                self.assertEqual(aws.instance_state(m), "gone")

    # --- the three fakes the provider cases above need ---

    def _with_tccli(self, fake):
        patcher = mock.patch.object(cloud_tencent, "tccli", fake)
        patcher.start()
        self.addCleanup(patcher.stop)
        return fake

    def _with_aliyun(self, responses):
        cli = mock.Mock()
        cli.calls = []
        cli.side_effect = lambda product, api, region=None, *a, **kw: (
            cli.calls.append((product, api, list(a))), responses.get(api, {}))[1]
        patcher = mock.patch.object(cloud_aliyun, "aliyun", cli)
        patcher.start()
        self.addCleanup(patcher.stop)
        return cli

    def _aws(self, ec2):
        aws = cloud_aws.AwsProvider()
        patcher = mock.patch.object(aws, "ec2", return_value=ec2)
        patcher.start()
        self.addCleanup(patcher.stop)
        return aws


class SharedSecurityGroup(testkit.GuardedTestCase):
    """The reconcile a *launch* runs on the shared ssh group.

    `tlx-verify-ssh` is one group per region, used by every owner on this
    machine at the same time. The launch reconcile used to narrow it: it
    computed the rules the launching machine's address needs and revoked every
    other ingress rule as stale. On a shared group that is destructive - a
    launch by one owner took away the operator-IP rule another owner's running
    lane reached its instance with (and, when this machine's egress address
    flaps between three addresses, the launching owner's own earlier one), so
    a healthy lane lost ssh and rsync while its remote job kept running.
    These are that incident and its controls: the reconcile adds what this
    launch needs and revokes only the rules this owner's own launches wrote.
    """

    # The third address this machine's egress address flaps between.
    THIRD_IP = "150.158.149.193"
    # What a rule this project's launches write carries: the owner that wrote
    # it, after the marker. The literal form is part of the contract (an older
    # process reads these descriptions), so the tests do not build it from the
    # module under test.
    A, B = "cloud_verify:owner-a", "cloud_verify:owner-b"

    def egress(self):
        return [{"PolicyIndex": 0, "Protocol": "ALL", "CidrBlock": "0.0.0.0/0", "Action": "ACCEPT"}]

    def revokes(self, f):
        return [c[2]["SecurityGroupPolicySet"]["Ingress"] for c in f.calls if c[0] == "DeleteSecurityGroupPolicies"]

    def added(self, f):
        return [r for c in f.calls if c[0] == "CreateSecurityGroupPolicies"
                for r in c[2]["SecurityGroupPolicySet"].get("Ingress", [])]

    def capture_warnings(self, module):
        """Collect what a provider warns about; returns the messages read so
        far, so a case can assert on what it reported."""
        patched = mock.patch.object(module, "warning")
        fake = patched.start()
        self.addCleanup(patched.stop)
        return lambda: " ".join(str(c.args[0]) for c in fake.call_args_list)

    # --- Tencent Cloud ---

    def tencent(self, ingress):
        return self._with_tccli(FakeTccli({
            "DescribeSecurityGroups": {"SecurityGroupSet": [{"SecurityGroupId": "sg-1"}]},
            "DescribeSecurityGroupPolicies": {"SecurityGroupPolicySet": {"Ingress": ingress, "Egress": self.egress()}}}))

    def tencent_launch(self, f, ips, owner="owner-a"):
        p = cloud_tencent.TencentProvider()
        p.owner = owner
        return p.ensure_security_group("ap-shanghai", ips)

    def test_tencent_a_launch_leaves_the_other_owners_rule_alone(self):
        # The incident, as the two workers diagnosed it: owner B's rule is the
        # one B's running lane uses, owner A launches, and B loses ssh.
        f = self.tencent([
            {"PolicyIndex": 0, "Protocol": "TCP", "Port": "22", "CidrBlock": f"{OLD_IP}/32",
             "Action": "ACCEPT", "PolicyDescription": self.B},
            {"PolicyIndex": 1, "Protocol": "TCP", "Port": "22", "CidrBlock": f"{NEW_IP}/32",
             "Action": "ACCEPT", "PolicyDescription": self.A}])
        self.assertEqual(self.tencent_launch(f, [NEW_IP]), "sg-1")
        # Nothing is revoked at all here (A's own address is already allowed),
        # and in particular B's rule is not.
        self.assertEqual(self.revokes(f), [])
        self.assertEqual({r["Port"] for r in self.added(f)}, {"443", "2222"})   # 22 already allows NEW_IP

    def test_tencent_a_launch_keeps_its_own_previous_address(self):
        # Another running lane may have borrowed our previous address.
        # Ownership records provenance, not an exclusive access lease.
        f = self.tencent([
            {"PolicyIndex": 0, "Protocol": "TCP", "Port": "22", "CidrBlock": f"{self.THIRD_IP}/32",
             "Action": "ACCEPT", "PolicyDescription": self.A},
            {"PolicyIndex": 1, "Protocol": "TCP", "Port": "443", "CidrBlock": f"{NEW_IP}/32",
             "Action": "ACCEPT", "PolicyDescription": self.A}])
        self.tencent_launch(f, [NEW_IP])
        self.assertEqual(self.revokes(f), [])
        self.assertEqual({(r["Port"], r["CidrBlock"], r["PolicyDescription"]) for r in self.added(f)},
                         {("22", f"{NEW_IP}/32", self.A), ("2222", f"{NEW_IP}/32", self.A)})

    def test_tencent_a_rule_with_no_owner_is_never_revoked(self):
        # A rule written before rules were tagged (or by hand) may belong to a
        # lane that is running right now: an unknown rule stays, however stale
        # it looks.
        f = self.tencent([
            {"PolicyIndex": 0, "Protocol": "TCP", "Port": "22", "CidrBlock": f"{OLD_IP}/32", "Action": "ACCEPT"},
            {"PolicyIndex": 1, "Protocol": "TCP", "Port": "22", "CidrBlock": f"{OLD_IP}/32",
             "Action": "ACCEPT", "PolicyDescription": "cloud_verify"}])
        self.tencent_launch(f, [NEW_IP])
        self.assertEqual(self.revokes(f), [])

    def test_tencent_never_writes_a_world_open_rule(self):
        # Every rule this tool writes is one address. Even a degenerate answer
        # from the address lookup stays a single host, and a world-open rule
        # that is already there is reported rather than added to or revoked.
        f = self.tencent([])
        self.tencent_launch(f, ["0.0.0.0"])
        self.assertEqual({r["CidrBlock"] for r in self.added(f)}, {"0.0.0.0/32"})
        said = self.capture_warnings(cloud_tencent)
        f = self.tencent([{"PolicyIndex": 0, "Protocol": "TCP", "Port": "22", "CidrBlock": "0.0.0.0/0",
                           "Action": "ACCEPT"}])
        self.tencent_launch(f, [NEW_IP])
        self.assertEqual(self.revokes(f), [])            # not ours to revoke
        self.assertNotIn("0.0.0.0/0", json.dumps(self.added(f)))
        self.assertIn("0.0.0.0/0", said())
        self.assertIn("open to the world", said())

    def test_tencent_a_detached_checkout_revokes_nothing(self):
        # No owner means nothing is ours to clean up (never a guess).
        f = self.tencent([{"PolicyIndex": 0, "Protocol": "TCP", "Port": "22", "CidrBlock": f"{self.THIRD_IP}/32",
                           "Action": "ACCEPT", "PolicyDescription": "cloud_verify"}])
        p = cloud_tencent.TencentProvider()
        p.owner = None
        real = cloud_tencent.current_owner
        cloud_tencent.current_owner = lambda required=True: None
        try:
            p.ensure_security_group("ap-shanghai", [NEW_IP])
        finally:
            cloud_tencent.current_owner = real
        self.assertEqual(self.revokes(f), [])

    # --- Aliyun ---

    def aliyun(self, perms):
        return self._with_aliyun({"DescribeVpcs": {"Vpcs": {"Vpc": [{"VpcId": "vpc-1"}]}},
                                  "DescribeSecurityGroups": {"SecurityGroups": {"SecurityGroup": [{"SecurityGroupId": "sg-1"}]}},
                                  "DescribeSecurityGroupAttribute": {"Permissions": {"Permission": perms}}})

    def aliyun_launch(self, cli, ips, owner="owner-a"):
        p = cloud_aliyun.AliyunProvider()
        p.owner = owner
        return p.ensure_security_group("cn-hangzhou", "vpc-1", ips)

    def test_aliyun_a_launch_leaves_the_other_owners_rule_alone(self):
        cli = self.aliyun([
            {"IpProtocol": "tcp", "PortRange": "22/22", "SourceCidrIp": f"{OLD_IP}/32",
             "Description": self.B, "SecurityGroupRuleId": "sgr-b"},
            {"IpProtocol": "tcp", "PortRange": "22/22", "SourceCidrIp": f"{NEW_IP}/32",
             "Description": self.A, "SecurityGroupRuleId": "sgr-a"}])
        self.aliyun_launch(cli, [NEW_IP])
        self.assertEqual([c for c in cli.calls if c[1] == "RevokeSecurityGroup"], [])
        self.assertEqual({c[2][c[2].index("--PortRange") + 1] for c in cli.calls if c[1] == "AuthorizeSecurityGroup"},
                         {"443/443", "2222/2222"})   # 22/22 already allows NEW_IP

    def test_aliyun_a_launch_keeps_its_own_previous_address(self):
        cli = self.aliyun([
            {"IpProtocol": "tcp", "PortRange": "22/22", "SourceCidrIp": f"{self.THIRD_IP}/32",
             "Description": self.A, "SecurityGroupRuleId": "sgr-old"},
            {"IpProtocol": "tcp", "PortRange": "22/22", "SourceCidrIp": f"{OLD_IP}/32",
             "Description": self.B, "SecurityGroupRuleId": "sgr-b"}])
        self.aliyun_launch(cli, [NEW_IP])
        self.assertEqual([c for c in cli.calls if c[1] == "RevokeSecurityGroup"], [])
        for call in (c for c in cli.calls if c[1] == "AuthorizeSecurityGroup"):
            self.assertEqual(call[2][call[2].index("--Description") + 1], self.A)
            self.assertNotIn("0.0.0.0/0", " ".join(call[2]))

    # --- AWS ---

    def aws(self, permissions):
        ec2 = mock.Mock()
        ec2.describe_security_groups.return_value = {"SecurityGroups": [{"GroupId": "sg-1", "IpPermissions": permissions}]}
        return self._aws(ec2), ec2

    def test_aws_a_launch_leaves_the_other_owners_rule_alone(self):
        aws, ec2 = self.aws([{"IpProtocol": "tcp", "FromPort": 22, "ToPort": 22, "IpRanges": [
            {"CidrIp": f"{OLD_IP}/32", "Description": self.B},
            {"CidrIp": f"{NEW_IP}/32", "Description": self.A}]}])
        aws.owner = "owner-a"
        aws.ensure_security_group(ec2, "vpc-1", [NEW_IP])
        ec2.revoke_security_group_ingress.assert_not_called()
        ec2.authorize_security_group_ingress.assert_not_called()

    def test_aws_a_launch_keeps_its_own_previous_address(self):
        aws, ec2 = self.aws([
            {"IpProtocol": "tcp", "FromPort": 22, "ToPort": 22, "IpRanges": [
                {"CidrIp": f"{OLD_IP}/32", "Description": self.A},
                {"CidrIp": "10.0.0.0/8"}]}])          # untagged: never revoked
        aws.owner = "owner-a"
        aws.ensure_security_group(ec2, "vpc-1", [NEW_IP])
        ec2.revoke_security_group_ingress.assert_not_called()
        ec2.authorize_security_group_ingress.assert_called_once_with(GroupId="sg-1", IpPermissions=[
            {"IpProtocol": "tcp", "FromPort": 22, "ToPort": 22,
             "IpRanges": [{"CidrIp": f"{NEW_IP}/32", "Description": self.A}]}])

    # --- the fakes the cases above need ---

    def _with_tccli(self, fake):
        patcher = mock.patch.object(cloud_tencent, "tccli", fake)
        patcher.start()
        self.addCleanup(patcher.stop)
        return fake

    def _with_aliyun(self, responses):
        cli = mock.Mock()
        cli.calls = []
        cli.side_effect = lambda product, api, region=None, *a, **kw: (
            cli.calls.append((product, api, list(a))), responses.get(api, {}))[1]
        patcher = mock.patch.object(cloud_aliyun, "aliyun", cli)
        patcher.start()
        self.addCleanup(patcher.stop)
        return cli

    def _aws(self, ec2):
        aws = cloud_aws.AwsProvider()
        patcher = mock.patch.object(aws, "ec2", return_value=ec2)
        patcher.start()
        self.addCleanup(patcher.stop)
        return aws


if __name__ == "__main__":
    unittest.main()
