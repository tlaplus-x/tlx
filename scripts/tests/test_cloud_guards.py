"""Cloud and local load policies: fake providers, no network."""
import unittest.mock
import contextlib, concurrent.futures, io, json, os, subprocess, sys, tempfile, threading, unittest
from pathlib import Path
from unittest.mock import Mock, patch

import bench
from cloud import cloud_common as common
import cloud_verify as cloud
import tlc
import tlxlib


class CloudGuards(unittest.TestCase):
    def test_owner_tag_is_collision_resistant(self):
        self.assertEqual(cloud.owner_tag("feature/a"), "feature/a")
        self.assertNotEqual(cloud.owner_tag("a?b"), cloud.owner_tag("a*b"))
        self.assertLessEqual(len(cloud.owner_tag("x" * 200)), 64)

    def test_budget_refuses_third_and_override_is_logged(self):
        with tempfile.TemporaryDirectory() as tmp:
            ledger = cloud.LaunchLedger(os.path.join(tmp, "ledger.json"))
            offer = common.Offer(1, "r", "z", "t", 16)
            a = cloud.parse_args([])
            for iid in ("i1", "i2"):
                with ledger.launch("owner", a, offer) as entry:
                    entry["instance"] = iid
            self.assertEqual(ledger.remaining("owner"), 0)
            with self.assertRaises(common.CloudStop) as raised:
                with ledger.launch("owner", a, offer):
                    self.fail("third launch allowed")
            self.assertEqual(raised.exception.code, 25)
            a.budget_override = "coordinator approved regression rerun"
            with ledger.launch("owner", a, offer) as entry:
                entry["instance"] = "i3"
            with open(ledger.path) as source:
                self.assertEqual(json.load(source)[-1]["override"], a.budget_override)
            self.assertEqual(ledger.remaining("other"), 2)

    def test_grant_adds_one_launch_for_the_owner(self):
        with tempfile.TemporaryDirectory() as tmp:
            ledger = cloud.LaunchLedger(os.path.join(tmp, "ledger.json"))
            offer = common.Offer(1, "r", "z", "t", 16)
            a = cloud.parse_args([])
            for iid in ("i1", "i2"):
                with ledger.launch("owner", a, offer) as entry:
                    entry["instance"] = iid
            self.assertEqual(ledger.remaining("owner"), 0)
            self.assertEqual(ledger.grant("owner", "coordinator approved a third run"), 1)
            self.assertEqual(ledger.remaining("other"), 2)
            with ledger.launch("owner", a, offer) as entry:
                entry["instance"] = "i3"
            self.assertEqual(ledger.remaining("owner"), 0)
            with self.assertRaises(common.CloudStop):
                with ledger.launch("owner", a, offer):
                    self.fail("launch beyond the grant allowed")

    def test_a_long_grant_needs_a_reason_and_is_capped_at_twelve_hours(self):
        """A named heavy job may run past three hours (user decision 2026-10-08); the reason is what
        makes it named, so a long grant without one is refused, and on-demand billing stays out."""
        with tempfile.TemporaryDirectory() as tmp:
            ledger = cloud.LaunchLedger(os.path.join(tmp, "ledger.json"))
            offer = common.Offer(1, "r", "z", "t", 16)
            for iid in ("i1", "i2"):
                with ledger.launch("owner", cloud.parse_args([]), offer) as entry:
                    entry["instance"] = iid
            self.assertEqual(ledger.remaining("owner"), 0)
            with self.assertRaises(common.CloudStop) as raised:
                ledger.grant("owner", "coordinator grant", minutes=240)
            self.assertIn("--reason", str(raised.exception))
            with self.assertRaises(common.CloudStop):
                ledger.grant("owner", "a named heavy job", minutes=cloud.MAX_LONG_GRANT_MINUTES + 1)
            # a ten-hour lane also costs more than the base cap, so the grant carries its budget
            self.assertEqual(ledger.grant("owner", "named heavy TLC oracle lane", minutes=600,
                                          budget_cny=20), 1)
            a = cloud.parse_args(["--max-minutes", "600"])
            with ledger.launch("owner", a, offer) as entry:      # the long grant admits the launch
                entry["instance"] = "i3"
            with self.assertRaises(common.CloudStop):
                with ledger.launch("owner", a, offer):
                    self.fail("a second launch beyond the grant was allowed")

    def test_the_cli_requires_reason_above_three_hours(self):
        cloud.parse_args(["--grant", "owner", "--minutes", "180"])
        with self.assertRaises(SystemExit):
            cloud.parse_args(["--grant", "owner", "--minutes", "181"])
        a = cloud.parse_args(["--grant", "owner", "--minutes", "600", "--reason", "named heavy job"])
        self.assertEqual(a.reason, "named heavy job")
        with self.assertRaises(SystemExit):
            cloud.parse_args(["--reason", "no grant"])

    def test_quota_refusal_blocks_other_regions_for_an_hour(self):
        with tempfile.TemporaryDirectory() as tmp:
            ledger = cloud.LaunchLedger(os.path.join(tmp, "ledger.json"))
            a = cloud.parse_args([])
            with self.assertRaises(common.CloudStop):
                with ledger.launch("owner", a, common.Offer(1, "ap-shanghai", "z", "t", 16)):
                    raise common.CloudStop("LimitExceeded.UserSpotQuota", 20)
            with self.assertRaises(common.CloudStop) as raised:
                with ledger.launch("owner", a, common.Offer(1, "ap-guangzhou", "z", "t", 16)):
                    self.fail("launched in another region after a quota refusal")
            self.assertEqual(raised.exception.code, 20)
            with ledger.launch("owner", a, common.Offer(1, "ap-shanghai", "z", "t", 16)) as entry:
                entry["instance"] = "i1"  # the same region may be retried once the quota frees
            with ledger.launch("other", a, common.Offer(1, "ap-guangzhou", "z", "t", 16)) as entry:
                entry["instance"] = "i2"  # other owners are unaffected
            a.budget_override = "coordinator moved this run"
            with ledger.launch("owner", a, common.Offer(1, "ap-guangzhou", "z", "t", 16)) as entry:
                entry["instance"] = "i3"

    def test_launch_budget_is_atomic_across_processes(self):
        with tempfile.TemporaryDirectory() as tmp:
            script = ("import sys; sys.path.insert(0, sys.argv[1]); import cloud_verify as c; "
                      "from cloud.cloud_common import CloudStop, Offer\n"
                      "try:\n"
                      " with c.LaunchLedger(sys.argv[2]).launch('owner', c.parse_args([]), Offer(1,'r','z','t',16)) as row:\n"
                      "  row['instance'] = 'fake'\n"
                      "except CloudStop as error: sys.exit(error.code)\n")
            def launch(_):
                return subprocess.run([sys.executable, "-c", script, os.path.dirname(cloud.__file__), os.path.join(tmp, "ledger")],
                                      capture_output=True, text=True, timeout=30).returncode
            with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:
                self.assertEqual(sorted(pool.map(launch, range(3))), [0, 0, 25])

    def test_confirmed_quota_refusal_does_not_use_launch(self):
        with tempfile.TemporaryDirectory() as tmp:
            ledger = cloud.LaunchLedger(os.path.join(tmp, "ledger"))
            a = cloud.parse_args(["--provider", "tencent"])
            offer = common.Offer(1, "r", "z", "t", 16)
            with self.assertRaises(common.CloudStop):
                with ledger.launch("owner", a, offer):
                    raise common.InfraError("LimitExceeded.UserSpotQuota")
            self.assertEqual(ledger.remaining("owner"), 2)
            with ledger.launch("owner", a, offer):
                pass   # Unknown outcome after a lost connection stays reserved.
            self.assertEqual(ledger.remaining("owner"), 1)

    def test_compute_cost_budget(self):
        with tempfile.TemporaryDirectory() as tmp:
            ledger = cloud.LaunchLedger(os.path.join(tmp, "ledger"))
            a = cloud.parse_args(["--provider", "tencent"])
            offer = common.Offer(3, "r", "z", "t", 16)
            with ledger.launch("owner", a, offer) as entry:
                entry["instance"] = "first"
            with self.assertRaisesRegex(common.CloudStop, "5 CNY"):
                with ledger.launch("owner", a, offer):
                    self.fail("cost budget exceeded")

    def test_budget_expiry_sizes_and_minutes(self):
        with tempfile.TemporaryDirectory() as tmp:
            ledger = cloud.LaunchLedger(os.path.join(tmp, "ledger"))
            offer = common.Offer(1, "r", "z", "big", 64)
            a = cloud.parse_args([])
            for modify in ({}, {"max_minutes": 61}, {"max_minutes": 0}):
                for key, value in modify.items():
                    setattr(a, key, value)
                with self.assertRaises(common.CloudStop):
                    ledger.check([], "owner", a, offer)
            a = cloud.parse_args(["--full", "--allow-big"])
            ledger.check([], "owner", a, offer)
            a = cloud.parse_args(["--allow-big"])
            with self.assertRaises(common.CloudStop):
                ledger.check([], "owner", a, offer)
            with patch.object(cloud.time, "time", return_value=50000):
                self.assertEqual(ledger.remaining("owner", [{"owner": "owner", "time": 1}]), 2)

    def test_mine_list_and_cleanup_ignore_others(self):
        provider = Mock()
        provider.all_regions = ["r"]
        provider.leftovers.return_value = [("r", "mine", "RUNNING")]
        a = cloud.parse_args(["--list", "--mine"])
        self.assertEqual(cloud.manage_instances(provider, a, "owner"), 1)
        provider.leftovers.assert_called_once_with(["r"], owner="owner")
        provider.leftovers.return_value = [("r", "mine", "TERMINATING")]
        self.assertEqual(cloud.manage_instances(provider, a, "owner"), 0)
        self.assertEqual(cloud.manage_instances(provider, cloud.parse_args(["--list"]), "owner"), 1)
        a = cloud.parse_args(["--cleanup", "--mine"])
        provider.leftovers.return_value = [("r", "mine", "RUNNING")]
        self.assertEqual(cloud.manage_instances(provider, a, "owner"), 0)
        self.assertEqual(provider.terminate.call_args.args[0].id, "mine")
        with self.assertRaises(common.CloudStop):
            cloud.manage_instances(provider, cloud.parse_args(["--cleanup"]), "owner")

    def test_messages_and_stop_codes(self):
        stream = io.StringIO()
        with contextlib.redirect_stdout(stream):
            common.warning("no CAM role")
        self.assertTrue(stream.getvalue().startswith("WARNING (not a stop condition):"))
        for msg, code in (("LimitExceeded.UserSpotQuota", 20), ("risk control", 21),
                          ("Forbidden", 22), ("launch refused", 23), ("account mismatch", 24)):
            error = common.CloudStop(msg)
            self.assertEqual(error.code, code)
            self.assertTrue(str(error).startswith("STOP:"))

    def test_main_preserves_classified_exit_codes(self):
        for code in (20, 21, 22, 23, 24, 25):
            output = io.StringIO()
            with patch.object(cloud, "parse_args", return_value=object()), \
                 patch.object(cloud, "run", side_effect=common.CloudStop("test refusal", code)), \
                 contextlib.redirect_stdout(output):
                self.assertEqual(cloud.main(), code)
                self.assertTrue(output.getvalue().startswith("STOP:"))

    def test_provider_owner_tags_filters_and_reaper(self):
        from cloud import cloud_aliyun
        from cloud import cloud_tencent
        with patch.object(common, "cloud_identity", return_value={}), patch.object(cloud_aliyun, "identity", return_value={}), \
             patch.object(cloud_tencent, "identity", return_value={}), patch.object(common, "git", return_value="feature/a"):
            tencent = cloud_tencent.TencentProvider()
            aliyun = cloud_aliyun.AliyunProvider()
            offer = common.Offer(1, "r", "z", "t", 16)
            tags = tencent.base_params(offer, "img", "sg", "subnet", "vpc", "key", "token")["TagSpecification"][0]["Tags"]
            self.assertIn({"Key": "tlx-owner", "Value": "feature/a"}, tags)
            machine = Mock(offer=offer, token="token")
            args = aliyun.run_args(machine, "img", "sg", "switch", 60)
            values = dict(zip(args[::2], args[1::2]))
            self.assertEqual((values["--Tag.3.Key"], values["--Tag.3.Value"]), ("Owner", "feature/a"))
            with patch.object(cloud_tencent, "tccli", return_value={"InstanceSet": []}) as api:
                tencent.leftovers(["r"], owner="feature/a")
                self.assertIn({"Name": "tag:tlx-owner", "Values": ["feature/a"]}, api.call_args.kwargs["Filters"])
                tencent.reap(["r"])
                self.assertIn({"Name": "tag:tlx-owner", "Values": ["feature/a"]}, api.call_args.kwargs["Filters"])
            with patch.object(cloud_aliyun, "aliyun", return_value={}) as api:
                aliyun.leftovers(["r"], owner="feature/a")
                args = api.call_args.args[3:]
                values = dict(zip(args[::2], args[1::2]))
                self.assertEqual((values["--Tag.2.Key"], values["--Tag.2.Value"]), ("Owner", "feature/a"))

    def test_worker_cannot_override(self):
        with patch.object(cloud, "git", side_effect=["/git/worktrees/a", "/git"]):
            with self.assertRaises(common.CloudStop):
                cloud.check_override("test")


class LocalGuards(unittest.TestCase):
    def test_tlc_always_has_heap_and_user_heap_wins(self):
        with patch.dict(os.environ, {"TLX_TLC_XMX": "2g"}):
            self.assertIn("-Xmx2g", tlxlib.tlc_heap(["java", "tlc2.TLC"]))
            cmd = tlxlib.tlc_heap(["java", "-Xmx1g", "tlc2.TLC"])
            self.assertEqual([x for x in cmd if x.startswith("-Xmx")], ["-Xmx1g"])
        for explicit in (["-Xmx1g"], ["-XX:MaxHeapSize=1g"]):
            self.assertTrue(tlxlib.heap_pinned(explicit))
        self.assertFalse(tlxlib.heap_pinned([]))

    def test_measured_tlc_keeps_the_jvm_default_heap(self):
        # The collected baselines and the oracle measure TLC at the JVM's
        # default heap; `tlc_heap`'s 4 GB local default must not reach them.
        self.assertEqual(bench.measured_jvm_options([]), [tlxlib.TLC_JVM_DEFAULT_HEAP])
        cmd = tlxlib.tlc_heap(tlc.tlc_cmd("M.tla", [], [], [bench.TLC_MS_PROP, *bench.measured_jvm_options([])]))
        self.assertEqual([x for x in cmd if x.startswith("-Xmx")], [])
        # An explicitly measured heap wins, and then carries no default-heap marker.
        self.assertEqual(bench.measured_jvm_options(["-Xmx6g"]), ["-Xmx6g"])
        self.assertEqual(bench.measured_jvm_options(["-Xmx6g"], default_heap=False), ["-Xmx6g"])
        cmd = tlxlib.tlc_heap(tlc.tlc_cmd("M.tla", [], [], [bench.TLC_MS_PROP, *bench.measured_jvm_options(["-Xmx6g"])]))
        self.assertEqual([x for x in cmd if x.startswith("-Xmx")], ["-Xmx6g"])

    def test_tlcbase_measures_at_the_default_heap_under_one_key(self):
        # The baseline key commits to the caller's heap request (none = the JVM
        # default) and never to the marker, so the stored default-heap
        # baselines stay reusable and a pinned-heap run cannot satisfy them.
        # `cached_tlc` is authoritative in `benchmarking.baselines`
        # (`bench_records` only re-exports it), so patch the library module.
        import benchmarking.baselines
        model = {"id": "M", "tla": "M.tla", "cfg": "M.cfg"}
        keys = []
        with patch.object(benchmarking.baselines, "cached_tlc",
                          side_effect=lambda m, w, collect, **kw: keys.append(m) or {"wall_s": 1, "result": "success"}):
            bench.tlc_measured(model, 1, 10)
            bench.tlc_measured(model, 1, 10, jvm_extra=["-Xmx6g"])
        self.assertNotIn("measurement_constraints", keys[0])
        self.assertEqual(keys[1]["measurement_constraints"], ["-Xmx6g"])
        self.assertNotIn(tlxlib.TLC_JVM_DEFAULT_HEAP, json.dumps(keys))

    def test_tlcbase_header_records_the_heap_policy(self):
        import argparse
        with tempfile.TemporaryDirectory() as tmp:
            out = os.path.join(tmp, "tlc.json")
            model = {"id": "M", "tla": "M.tla", "cfg": "M.cfg", "source": "fixture"}
            raw = {"result": "success", "distinct": 1, "wall_s": 7, "cpu_s": 8, "maxrss_mib": 10}
            a = argparse.Namespace(workers="1", missing=False, collect=True, out=out, force=False, timeout=1, slice="")
            from benchmarking import bench_records
            with patch.object(bench, "tlcbase_models", return_value={"M": model}), \
                 patch.object(bench.bench_machine, "jvm_info", return_value={}), \
                 patch.object(bench.bench_machine, "git_commit", return_value="fixture"), \
                 patch.object(bench, "tlc_measured", return_value=raw), \
                 patch.object(bench_records, "ingest"):
                bench.cmd_tlcbase(a)
            with open(out) as stream:
                header = json.load(stream)
            self.assertEqual(header["jvm"]["heap"], "jvm-default")
            self.assertEqual([x for x in header["jvm"]["options"] if x.startswith("-Xmx")], [])

    def test_heavy_config_refusal_cloud_and_explicit_override(self):
        model = {"repo": "r", "tla": "Spec.tla", "cfg": "big.cfg", "tier": "medium", "name": "big"}
        with tempfile.TemporaryDirectory() as tmp, patch.object(tlxlib, "ROOT", tmp):
            os.makedirs(os.path.join(tmp, "corpus"))
            with open(os.path.join(tmp, "corpus", "external.json"), "w") as source:
                json.dump({"models": [model]}, source)
            spec = os.path.join(tmp, "third_party", "external", "r", "Spec.tla")
            cmd = ["java", "tlc2.TLC", "-config", "big.cfg", spec]
            with patch.dict(os.environ, {"TLX_CLOUD_HOST": "0"}):
                with self.assertRaisesRegex(SystemExit, "STOP:.*heavy"):
                    tlxlib.check_tlc_model(cmd, os.path.dirname(spec))
                with self.assertRaisesRegex(SystemExit, "STOP:.*heavy"):
                    tlxlib.check_tlc_model(["java", "tlc2.TLC", "-config", "big", spec[:-4]], os.path.dirname(spec))
                # Broad Exception handlers in corpus.py must not turn a guard
                # refusal into a cached semantic oracle or a successful exit.
                with self.assertRaises(SystemExit):
                    try:
                        tlxlib.check_tlc_model(cmd, os.path.dirname(spec))
                    except Exception:
                        self.fail("guard swallowed as a semantic error")
                tlxlib.check_tlc_model(["java", "tlc2.TLC", "-config", "reduced.cfg", spec], os.path.dirname(spec))
                tlxlib.check_tlc_model(cmd, os.path.dirname(spec), allow_local_heavy=True)
            with patch.dict(os.environ, {"TLX_CLOUD_HOST": "1"}):
                tlxlib.check_tlc_model(cmd, os.path.dirname(spec))

    def test_third_slot_waits_until_one_is_released(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(tlxlib, "tlc_lock_dir", return_value=tmp), patch.dict(os.environ, {"TLX_CLOUD_HOST": "0"}):
            entered = threading.Event()
            def third():
                with tlxlib.tlc_slot():
                    entered.set()
            with tlxlib.tlc_slot():
                with tlxlib.tlc_slot():
                    thread = threading.Thread(target=third)
                    thread.start()
                    self.assertFalse(entered.wait(.2))
                self.assertTrue(entered.wait(30))  # a slot handover, not a speed measurement
            thread.join(30)
            self.assertFalse(thread.is_alive())

    def test_slot_limit_applies_across_processes(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(tlxlib, "tlc_lock_dir", return_value=tmp), \
             patch.dict(os.environ, {"TLX_CLOUD_HOST": "0"}):
            script = ("import sys; sys.path.insert(0, sys.argv[1]); import tlxlib; "
                      "tlxlib.tlc_lock_dir=lambda: sys.argv[2]\n"
                      "with tlxlib.tlc_slot(): print('acquired', flush=True)\n")
            with tlxlib.tlc_slot():
                with tlxlib.tlc_slot():
                    child = subprocess.Popen([sys.executable, "-c", script, os.path.dirname(tlxlib.__file__), tmp],
                                             stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True)
                    try:
                        with self.assertRaises(subprocess.TimeoutExpired):
                            child.communicate(timeout=.2)
                    except BaseException:
                        child.kill()
                        child.communicate()
                        raise
                out, err = child.communicate(timeout=30)
                self.assertEqual((child.returncode, out, err), (0, "acquired\n", ""))

    def test_heap_and_slots_survive_timeout(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(tlxlib, "tlc_lock_dir", return_value=tmp), \
             patch.object(tlxlib, "check_tlc_model"), patch.dict(os.environ, {"TLX_CLOUD_HOST": "0", "TLX_TLC_XMX": "4g"}):
            with patch.object(tlxlib, "_run_proc", side_effect=subprocess.TimeoutExpired("java", .1)) as run:
                with self.assertRaises(subprocess.TimeoutExpired):
                    tlxlib.run_proc(["java", "tlc2.TLC", "Spec.tla"], .1)
                self.assertIn("-Xmx4g", run.call_args.args[0])
                self.assertEqual(len(run.call_args.kwargs["pass_fds"]), 1)
            # Both locks must be available again after timeout cleanup.
            with tlxlib.tlc_slot(), tlxlib.tlc_slot():
                pass

    def test_run_proc_routes_tlc_to_guarded_helper(self):
        with patch.object(tlxlib, "run_tlc_proc", return_value="guarded") as run:
            self.assertEqual(tlxlib.run_proc(["java", "tlc2.TLC", "Spec.tla"]), "guarded")
            run.assert_called_once()

    def test_hog_refusal_before_any_build(self):
        with patch.dict(os.environ, {"TLX_CLOUD_HOST": "0"}), patch.object(sys, "argv", ["bench.py", "ab", "--models", "test", "--hog", "3"]):
            with self.assertRaisesRegex(SystemExit, "STOP:.*hog"):
                bench.main()


class HarnessUpload(unittest.TestCase):
    def test_the_whole_harness_is_uploaded(self):
        # A partial overlay (bench.py without bench_profile.py) crashed a cloud run.
        from cloud import cloud_common
        names = [os.path.basename(p) for p in cloud_common.harness_files()]
        for required in ("bench.py", "bench_profile.py", "bench_suite.py", "verify.py", "tlxlib.py", "corpus.py", "tlc.py"):
            self.assertIn(required, names)
        self.assertTrue(all(n.endswith(".py") for n in names))

    def test_nested_package_modules_keep_source_relative_paths(self):
        # A module under scripts/<package>/ must keep its path in the upload
        # manifest, or the remote import breaks (HARNESS-13). __pycache__ never
        # travels.
        from cloud import cloud_common
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            package = root / "scripts" / "cloud"
            package.mkdir(parents=True)
            (package / "__init__.py").write_text("")
            (package / "store.py").write_text("")
            (package / "__pycache__").mkdir()
            (package / "__pycache__" / "store.cpython-314.pyc").write_bytes(b"\0")
            (root / "scripts" / "bench.py").write_text("")
            files = cloud_common.harness_files(root)
            self.assertIn(os.path.join("scripts", "cloud", "store.py"), files)
            self.assertIn(os.path.join("scripts", "cloud", "__init__.py"), files)
            self.assertIn(os.path.join("scripts", "bench.py"), files)
            self.assertEqual(files, sorted(files))
            self.assertTrue(all(not os.path.isabs(f) for f in files))
            self.assertFalse(any("__pycache__" in f for f in files))

    def test_checked_forwards_extra_run_keywords(self):
        # The upload passes cwd= so rsync's -R resolves source-relative paths
        # from the repository root.
        from cloud import cloud_common
        m = Mock()
        m.run.return_value = Mock(returncode=0, stdout="done\n", stderr="")
        self.assertEqual(cloud_common.checked(m, ["rsync"], "upload", cwd="/repo"), "done")
        kwargs = m.run.call_args.kwargs
        self.assertEqual(kwargs["cwd"], "/repo")
        self.assertTrue(kwargs["capture_output"])
        self.assertTrue(kwargs["text"])


class ProfilePreflightOptions(unittest.TestCase):
    def test_profile_preflight_accepts_the_options_bench_adds_to_every_subcommand(self):
        # The preflight parser lacked --deadline-min/--deadline-at/--smoke (audit 2026-10-07).
        from benchmarking import bench_profile
        with unittest.mock.patch.object(bench_profile, "resolve", return_value={}):
            a = cloud.parse_args(["--provider", "tencent", "--bench", "profile --models A --deadline-min 5 --smoke"])
        self.assertEqual(len(a.bench), 1)

    def test_the_preflight_parses_with_the_parser_that_executes_the_command(self):
        # One parser for the entry point and the preflight (HARNESS-02): the
        # preflight must go through bench.py's parser owner, not a copy of the
        # profile subparser that drifts from it.
        from benchmarking import cli
        from benchmarking import bench_profile
        with unittest.mock.patch.object(bench_profile, "resolve", return_value={}) as resolve, \
             unittest.mock.patch.object(cli, "parse_args", wraps=cli.parse_args) as parse:
            cloud.parse_args(["--provider", "tencent", "--bench", "profile --models A --deadline-min 5"])
        parse.assert_called_once_with(["profile", "--models", "A", "--deadline-min", "5"], prog="bench.py profile")
        resolve.assert_called_once_with(["A"])

    def test_a_preflight_parser_without_the_shared_flags_would_refuse_a_valid_command(self):
        """Known-bad, the original defect: cloud_verify rebuilt the profile subparser
        with benchmarking.bench_profile.add_args alone, so it refused `profile --models A
        --deadline-min 5` (exit 2, "unrecognized arguments") although bench.py itself
        accepts it. Kept as the reproduction, not as the fix.
        """
        import argparse
        from benchmarking import bench_profile
        from benchmarking import cli
        hand_built = argparse.ArgumentParser(prog="bench.py profile")
        bench_profile.add_args(hand_built)
        with self.assertRaises(SystemExit) as refused, contextlib.redirect_stderr(io.StringIO()) as stderr:
            hand_built.parse_args(["--models", "A", "--deadline-min", "5"])
        self.assertEqual(refused.exception.code, 2)
        self.assertIn("unrecognized arguments: --deadline-min", stderr.getvalue())
        # The execution parser accepts the same command, which is what the preflight
        # now runs (the shared flags reach every subcommand).
        _, options = cli.parse_args(["profile", "--models", "A", "--deadline-min", "5"])
        self.assertEqual((options.cmd, options.models, options.deadline_min), ("profile", "A", 5.0))


if __name__ == "__main__":
    unittest.main()
