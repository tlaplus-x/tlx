"""Fixtures for the shared dependency store service (scripts/dependencies.py).

Synthetic linked-worktree layouts, fake downloads and private scratch copies
only: no network and no write to the real third_party/ store. Every new refusal
is first shown on a known-bad state and then on a passing control, and the
read-only path is shown to leave the store byte-identical (HARNESS-11, HARNESS-15).
fetch-deps.sh runs end to end through fake curl/git/unzip/tar commands that only
ever write inside the staging directory they are handed.
"""
import hashlib, importlib.util, io, json, os, re, shutil, subprocess, sys, tarfile, tempfile, threading, time, unittest, zipfile
from unittest.mock import patch

import dependencies, testkit, tlxlib

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SPEC = {"repo": "owner/name", "commit": "a" * 40, "root": "root"}

# A revision a synthetic jar's manifest reports; never the committed baseline
# (1813307068...), so a test that accepts it can only have used its own pin.
SYNTH_REV = "a1b2c3d4" * 5


def synthetic_jar(revision=SYNTH_REV, version="2.0 synthetic"):
    """A minimal jar carrying the manifest identity verify_tla2tools reads."""
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w") as jar:
        jar.writestr("META-INF/MANIFEST.MF",
                     "Manifest-Version: 1.0\r\n"
                     f"X-Git-Revision: {revision}\r\n"
                     f"X-Git-ShortRevision: {revision[:7]}\r\n"
                     f"Implementation-Version: {version}\r\n"
                     "Build-TimeStamp: 2026-10-08T00:00:00.0Z\r\n\r\n")
    return buf.getvalue()


def pin_env(blob, **overrides):
    """A TLA2TOOLS_PIN_JSON value that declares exactly `blob` (tests only)."""
    fields = {"sha256": hashlib.sha256(blob).hexdigest(), "revision": SYNTH_REV,
              "short": SYNTH_REV[:7], "version": "2.0 synthetic"}
    fields.update(overrides)
    return json.dumps(fields)


def community_pin_env(blob, **overrides):
    """A COMMUNITY_MODULES_PIN_JSON value that declares exactly `blob` (tests only)."""
    fields = {"sha256": hashlib.sha256(blob).hexdigest()}
    fields.update(overrides)
    return json.dumps(fields)


def load_fetch_external():
    """A fresh fetch-external module so each test patches its own DEST/OVERLAY."""
    path = os.path.join(tlxlib.ROOT, "scripts", "fetch-external.py")
    spec = importlib.util.spec_from_file_location("fetch_external_under_test", path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def tarball(members):
    buf = io.BytesIO()
    with tarfile.open(fileobj=buf, mode="w:gz") as tar:
        for name, data in members.items():
            info = tarfile.TarInfo(name)
            info.size = len(data)
            tar.addfile(info, io.BytesIO(data))
    return buf.getvalue()


def snapshot(root):
    """{relative path: bytes} of every file below root; the no-shared-write proof."""
    out = {}
    for base, dirs, files in os.walk(root):
        dirs.sort()
        for name in sorted(files):
            path = os.path.join(base, name)
            with open(path, "rb") as source:
                out[os.path.relpath(path, root)] = source.read()
    return out


class Layout(testkit.GuardedTestCase):
    """A main checkout with a real third_party/ and a linked worktree symlinking to it."""

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="tlx-deps-")
        self.addCleanup(self.tmp.cleanup)
        self.main = os.path.join(self.tmp.name, "main")
        self.work = os.path.join(self.tmp.name, "work")
        os.makedirs(os.path.join(self.main, "third_party"))
        os.makedirs(self.work)
        os.symlink(os.path.join(self.main, "third_party"), os.path.join(self.work, "third_party"))

    def store(self, root=None):
        return os.path.join(root or self.main, "third_party")

    def fetch_env(self, root, payload, overlay_files=None):
        """Patch a fresh fetch-external onto `root` with a fake network and overlay."""
        fx = load_fetch_external()
        overlay = os.path.join(self.tmp.name, "overlay")
        for name, data in (overlay_files or {}).items():
            path = os.path.join(overlay, name)
            os.makedirs(os.path.dirname(path), exist_ok=True)
            with open(path, "wb") as out:
                out.write(data)
        calls = []

        def request(url, retries=3):
            calls.append(url)
            return payload

        for patch_ in (patch.object(dependencies, "ROOT", root),
                       patch.object(fx, "DEST", os.path.join(root, "third_party", "external")),
                       patch.object(fx, "OVERLAY", overlay),
                       patch.object(fx, "request", request)):
            patch_.start()
            self.addCleanup(patch_.stop)
        return fx, calls


class Ownership(Layout):

    def test_require_owner_refuses_a_linked_worktree_but_not_its_owner(self):
        # Known bad: the worktree reaches another checkout's third_party through a symlink.
        self.assertFalse(dependencies.owns_store(self.work))
        with self.assertRaises(SystemExit) as caught:
            dependencies.require_owner(self.work)
        self.assertIn("refusing", str(caught.exception))
        # Control: the owning checkout may install.
        self.assertTrue(dependencies.owns_store(self.main))
        self.assertEqual(dependencies.require_owner(self.main), os.path.realpath(self.store()))

    def test_worker_install_is_refused_before_any_write(self):
        sentinel = os.path.join(self.store(), "keep")
        with open(sentinel, "wb") as out:
            out.write(b"shared")
        before = snapshot(self.store())
        fx, calls = self.fetch_env(self.work, tarball({"name-abc/root/a.tla": b"A"}))
        with self.assertRaises(SystemExit):
            fx.fetch_repo("name", SPEC)
        self.assertEqual(calls, [], "the refusal must precede the download")
        self.assertEqual(snapshot(self.store()), before, "a worker install must not write the shared store")

    def test_a_linked_worktree_reads_the_same_store(self):
        # The worktree's third_party/ is the owner's tree: an owner install is
        # visible through it, which is exactly the write a worker must not make.
        self.assertTrue(os.path.islink(os.path.join(self.work, "third_party")))
        fx, _ = self.fetch_env(self.main, tarball({"name-abc/root/a.tla": b"A"}))
        fx.fetch_repo("name", SPEC)
        with open(os.path.join(self.main, "third_party", "external", "name", "a.tla"), "rb") as source:
            installed = source.read()
        self.assertEqual(snapshot(os.path.join(self.work, "third_party"))["external/name/a.tla"], installed)


class CommandLine(Layout):

    def run_cli(self, root, *args):
        script = os.path.join(tlxlib.ROOT, "scripts", "dependencies.py")
        return subprocess.run([sys.executable, script, "--root", root, *args], capture_output=True, text=True)

    def test_owner_check_and_run(self):
        refused = self.run_cli(self.work, "owner-check")     # known bad
        self.assertNotEqual(refused.returncode, 0)
        self.assertIn("refusing", refused.stderr)
        self.assertNotEqual(self.run_cli(self.work, "run", "--", "true").returncode, 0)
        accepted = self.run_cli(self.main, "owner-check")    # control
        self.assertEqual(accepted.returncode, 0, accepted.stderr)
        self.assertEqual(accepted.stdout.strip(), os.path.realpath(self.store()))
        self.assertEqual(self.run_cli(self.main, "run", "--", "true").returncode, 0)
        self.assertEqual(sorted(os.listdir(self.store())), [dependencies.LOCK_NAME])

    def test_fetch_deps_script_refuses_a_worker(self):
        if dependencies.owns_store():
            self.skipTest("the main checkout owns the store and would fetch for real")
        result = subprocess.run(["bash", os.path.join(tlxlib.ROOT, "scripts", "fetch-deps.sh")],
                                cwd=tlxlib.ROOT, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("refusing", result.stderr)


class PinFixtures:
    """Private scratch jars and CLI calls shared by the baseline-pin tests."""

    def write(self, name, blob):
        path = os.path.join(tempfile.mkdtemp(prefix="tlx-pin-"), name)
        self.addCleanup(shutil.rmtree, os.path.dirname(path), True)
        with open(path, "wb") as out:
            out.write(blob)
        return path

    def run_cli(self, *args, env=None):
        script = os.path.join(tlxlib.ROOT, "scripts", "dependencies.py")
        return subprocess.run([sys.executable, script, *args], capture_output=True, text=True,
                              env={**os.environ, **(env or {})})


class BaselinePin(PinFixtures, unittest.TestCase):
    """DOC-09: the TLC oracle is a declared, verified baseline, never "a jar exists"."""

    def test_the_committed_pin_names_the_declared_baseline(self):
        pin = dependencies.TLA2TOOLS_PIN
        self.assertEqual(pin["revision"], "1813307068bbc5759a441df820f3f548948d6b7a")
        self.assertEqual(pin["short"], pin["revision"][:7])
        self.assertRegex(pin["sha256"], r"^[0-9a-f]{64}$")
        self.assertEqual(pin["version"], "2.0 2026-10-02")
        self.assertEqual(dependencies.declared_pin(), pin, "no override means the committed pin")

    def test_a_matching_jar_is_accepted_and_its_identity_returned(self):
        blob = synthetic_jar()
        path = self.write("ok.jar", blob)
        pin = {"sha256": hashlib.sha256(blob).hexdigest(), "revision": SYNTH_REV, "short": SYNTH_REV[:7]}
        self.assertEqual(dependencies.verify_tla2tools(path, pin=pin),
                         {"sha256": pin["sha256"], "revision": SYNTH_REV, "short": SYNTH_REV[:7],
                          "version": "2.0 synthetic"})

    def test_a_jar_that_is_not_the_pin_is_refused_even_though_it_exists(self):
        blob = synthetic_jar(revision="b" * 40)
        path = self.write("other.jar", blob)
        with self.assertRaises(SystemExit) as caught:      # known bad: real pin, other bytes
            dependencies.verify_tla2tools(path, pin=dependencies.TLA2TOOLS_PIN)
        self.assertIn("not the declared TLC baseline", str(caught.exception))
        control = {"sha256": hashlib.sha256(blob).hexdigest(), "revision": "b" * 40}
        self.assertEqual(dependencies.verify_tla2tools(path, pin=control)["revision"], "b" * 40)

    def test_missing_truncated_and_non_jar_files_are_refused(self):
        pin = {"sha256": hashlib.sha256(synthetic_jar()).hexdigest(), "revision": SYNTH_REV}
        with self.assertRaises(SystemExit) as caught:
            dependencies.verify_tla2tools(os.path.join(os.path.dirname(self.write("keep", b"")), "none.jar"),
                                          pin=pin)
        self.assertIn("no tla2tools.jar", str(caught.exception))
        for name, blob in (("truncated.jar", synthetic_jar()[:128]), ("plain.jar", b"not a zip at all"),
                           ("empty.jar", b"")):
            path = self.write(name, blob)
            with self.assertRaises(SystemExit) as caught:
                dependencies.verify_tla2tools(path, pin=pin)
            self.assertIn("not the declared TLC baseline", str(caught.exception), name)
            self.assertIsNone(dependencies.jar_identity(path).get("revision"),
                              f"{name} must not report a manifest revision")

    def test_a_pin_whose_revision_contradicts_its_hash_is_refused(self):
        blob = synthetic_jar()
        path = self.write("ok.jar", blob)
        pin = {"sha256": hashlib.sha256(blob).hexdigest(), "revision": "c" * 40}
        with self.assertRaises(SystemExit) as caught:
            dependencies.verify_tla2tools(path, pin=pin)
        self.assertIn("pin is inconsistent", str(caught.exception))

    def test_the_override_is_narrow_and_blank_means_committed(self):
        blob = synthetic_jar()
        path = self.write("ok.jar", blob)
        with patch.dict(os.environ, {dependencies.PIN_OVERRIDE_ENV: pin_env(blob)}):
            self.assertEqual(dependencies.declared_pin()["revision"], SYNTH_REV)
            self.assertEqual(dependencies.verify_tla2tools(path)["sha256"],
                             hashlib.sha256(blob).hexdigest())
        for bad in ("", "{not json", "{}", '{"nosuch": 1}', '[1]'):
            with patch.dict(os.environ, {dependencies.PIN_OVERRIDE_ENV: bad}):
                if bad in ("",):
                    self.assertEqual(dependencies.declared_pin(), dependencies.TLA2TOOLS_PIN)
                else:
                    with self.assertRaises(SystemExit):
                        dependencies.declared_pin()

    def test_pin_and_verify_jar_commands(self):
        blob = synthetic_jar()
        path = self.write("ok.jar", blob)
        full = self.run_cli("pin")
        self.assertEqual(full.returncode, 0, full.stderr)
        self.assertEqual(json.loads(full.stdout), dependencies.TLA2TOOLS_PIN)
        self.assertEqual(self.run_cli("pin", "short").stdout.strip(), dependencies.TLA2TOOLS_PIN["short"])
        refused = self.run_cli("verify-jar", path)          # known bad: real pin
        self.assertNotEqual(refused.returncode, 0)
        self.assertIn("not the declared TLC baseline", refused.stderr)
        accepted = self.run_cli("verify-jar", path, env={dependencies.PIN_OVERRIDE_ENV: pin_env(blob)})
        self.assertEqual(accepted.returncode, 0, accepted.stderr)
        self.assertIn("declared baseline", accepted.stdout)
        self.assertNotEqual(self.run_cli("verify-jar").returncode, 0, "verify-jar needs a path")


class CommunityBaselinePin(PinFixtures, unittest.TestCase):
    """DOC-09/HARNESS-15: CommunityModules is a declared, verified baseline too."""

    def test_the_committed_pin_names_the_declared_release(self):
        pin = dependencies.COMMUNITY_MODULES_PIN
        self.assertEqual(pin["release"], "202609120237")
        self.assertEqual(pin["sha256"],
                         "3d9a282c360e90d55e9bbe99caa2987d508fef1556d652760b4af4455e283733")
        self.assertIn(f"/releases/download/{pin['release']}/", pin["url"])
        self.assertEqual(dependencies.declared_pin(dependencies.COMMUNITY_MODULES_PIN,
                                                   dependencies.COMMUNITY_PIN_OVERRIDE_ENV), pin)

    def test_a_matching_community_jar_is_accepted_and_its_identity_returned(self):
        blob = synthetic_jar()
        path = self.write("ok.jar", blob)
        pin = {"sha256": hashlib.sha256(blob).hexdigest()}
        self.assertEqual(dependencies.verify_community_modules(path, pin=pin),
                         {"sha256": pin["sha256"], "revision": SYNTH_REV, "short": SYNTH_REV[:7],
                          "version": "2.0 synthetic"})

    def test_a_community_jar_that_is_not_the_pin_is_refused_even_though_it_exists(self):
        blob = synthetic_jar(revision="b" * 40)
        path = self.write("other.jar", blob)
        with self.assertRaises(SystemExit) as caught:      # known bad: real pin, other bytes
            dependencies.verify_community_modules(path, pin=dependencies.COMMUNITY_MODULES_PIN)
        self.assertIn("not the declared CommunityModules baseline", str(caught.exception))
        control = {"sha256": hashlib.sha256(blob).hexdigest()}
        self.assertEqual(dependencies.verify_community_modules(path, pin=control)["sha256"],
                         control["sha256"])

    def test_missing_and_non_jar_community_files_are_refused(self):
        pin = {"sha256": hashlib.sha256(synthetic_jar()).hexdigest()}
        with self.assertRaises(SystemExit) as caught:
            dependencies.verify_community_modules(
                os.path.join(os.path.dirname(self.write("keep", b"")), "none.jar"), pin=pin)
        self.assertIn("no modules.jar", str(caught.exception))
        for name, blob in (("truncated.jar", synthetic_jar()[:128]), ("plain.jar", b"not a zip at all")):
            path = self.write(name, blob)
            with self.assertRaises(SystemExit) as caught:
                dependencies.verify_community_modules(path, pin=pin)
            self.assertIn("not the declared CommunityModules baseline", str(caught.exception), name)

    def test_the_community_override_is_narrow_and_blank_means_committed(self):
        blob = synthetic_jar()
        path = self.write("ok.jar", blob)

        def declared():
            return dependencies.declared_pin(dependencies.COMMUNITY_MODULES_PIN,
                                             dependencies.COMMUNITY_PIN_OVERRIDE_ENV)

        with patch.dict(os.environ, {dependencies.COMMUNITY_PIN_OVERRIDE_ENV: community_pin_env(blob)}):
            self.assertEqual(declared()["sha256"], hashlib.sha256(blob).hexdigest())
            self.assertEqual(dependencies.verify_community_modules(path)["sha256"],
                             hashlib.sha256(blob).hexdigest())
        for bad in ("", "{not json", "{}", '{"nosuch": 1}', '[1]'):
            with patch.dict(os.environ, {dependencies.COMMUNITY_PIN_OVERRIDE_ENV: bad}):
                if bad in ("",):
                    self.assertEqual(declared(), dependencies.COMMUNITY_MODULES_PIN)
                else:
                    with self.assertRaises(SystemExit):
                        declared()

    def test_pin_community_and_verify_community_commands(self):
        blob = synthetic_jar()
        path = self.write("ok.jar", blob)
        full = self.run_cli("pin-community")
        self.assertEqual(full.returncode, 0, full.stderr)
        self.assertEqual(json.loads(full.stdout), dependencies.COMMUNITY_MODULES_PIN)
        self.assertEqual(self.run_cli("pin-community", "release").stdout.strip(),
                         dependencies.COMMUNITY_MODULES_PIN["release"])
        refused = self.run_cli("verify-community", path)     # known bad: real pin
        self.assertNotEqual(refused.returncode, 0)
        self.assertIn("not the declared CommunityModules baseline", refused.stderr)
        accepted = self.run_cli("verify-community", path,
                                env={dependencies.COMMUNITY_PIN_OVERRIDE_ENV: community_pin_env(blob)})
        self.assertEqual(accepted.returncode, 0, accepted.stderr)
        self.assertIn("declared baseline", accepted.stdout)
        self.assertNotEqual(self.run_cli("verify-community").returncode, 0,
                            "verify-community needs a path")


class BaselineDocuments(unittest.TestCase):
    """The committed pin, the docs and the TLC source checkout name one revision."""

    def test_the_documents_name_the_pinned_baseline(self):
        pin = dependencies.TLA2TOOLS_PIN
        for name in ("compat.md", "features.md"):
            with open(os.path.join(tlxlib.ROOT, "docs", name), encoding="utf-8") as source:
                self.assertIn(pin["short"], source.read(),
                              f"docs/{name} must name the pinned TLC revision {pin['short']}")
        with open(os.path.join(tlxlib.ROOT, "docs", "tlc-semantics.md"), encoding="utf-8") as source:
            self.assertIn(pin["revision"], source.read(),
                          "docs/tlc-semantics.md must pin its TLC source checkout to the baseline revision")


class InstalledBaseline(unittest.TestCase):
    """The pin describes the actual git-ignored store, when it is fetched here."""

    def test_the_installed_jar_is_the_pinned_bytes(self):
        jar = os.path.join(tlxlib.TP, "tla2tools.jar")
        if not os.path.isfile(jar):
            self.skipTest("third_party/tla2tools.jar is not fetched in this checkout")
        identity = dependencies.verify_tla2tools(jar)
        self.assertEqual(identity["sha256"], dependencies.TLA2TOOLS_PIN["sha256"],
                         "the installed jar must be the pinned bytes, not just a jar")
        self.assertEqual(identity["revision"], dependencies.TLA2TOOLS_PIN["revision"])

    def test_the_tlaplus_source_checkout_is_at_the_pinned_revision(self):
        source = os.path.join(tlxlib.TP, "tlaplus")
        if not os.path.isdir(os.path.join(source, ".git")):
            self.skipTest("third_party/tlaplus is not a checkout in this worktree")
        head = subprocess.run(["git", "-C", source, "rev-parse", "HEAD"], capture_output=True, text=True)
        self.assertEqual(head.returncode, 0, head.stderr)
        self.assertEqual(head.stdout.strip(), dependencies.TLA2TOOLS_PIN["revision"],
                         "the source the citations point at must be the baseline revision")


class InstalledCommunityBaseline(unittest.TestCase):
    """The community pin describes the actual store and the canonical ClockSettles key."""

    CLOCK_DIGEST = "dbdef99c55ecd1833e70f2ed6f1d4d25da71d10b46348dd8ef8019efcce3056d"

    def test_the_installed_community_jar_is_the_pinned_bytes(self):
        jar = os.path.join(tlxlib.TP, "community", "modules.jar")
        if not os.path.isfile(jar):
            self.skipTest("third_party/community/modules.jar is not fetched in this checkout")
        identity = dependencies.verify_community_modules(jar)
        self.assertEqual(identity["sha256"], dependencies.COMMUNITY_MODULES_PIN["sha256"],
                         "the installed jar must be the pinned bytes, not just a jar")

    def test_the_pinned_community_jar_reproduces_the_canonical_clock_digest(self):
        jar = os.path.join(tlxlib.TP, "community", "modules.jar")
        tla = os.path.join(tlxlib.TP, "external", "tlaplus-tests", "test-model", "examples",
                           "SpecifyingSystems", "Liveness", "LiveHourClock.tla")
        if not os.path.isfile(jar) or not os.path.isfile(tla):
            self.skipTest("the community jar and the tlaplus-tests corpus are not fetched here")
        from benchmarking import baselines
        model = {"id": "bench/ClockSettles", "tla": tla,
                 "cfg": os.path.join(tlxlib.ROOT, "bench", "stress", "ClockSettles.cfg"),
                 "features": [], "flags": [], "tlc": {}}
        self.assertEqual(baselines.content_digest(model), self.CLOCK_DIGEST,
                         "the pinned modules.jar must reproduce the canonical baseline key")


class Locking(Layout):

    def test_install_lock_is_exclusive(self):
        with dependencies.install_lock(self.store()):
            with self.assertRaises(SystemExit) as caught:   # known bad: lock held
                with dependencies.install_lock(self.store(), timeout=0.2):
                    pass
            self.assertIn("another installer", str(caught.exception))
        with dependencies.install_lock(self.store(), timeout=5):   # control: free again
            pass

    def test_a_waiting_installer_keeps_the_old_complete_input(self):
        fx, _ = self.fetch_env(self.main, tarball({"name-abc/root/a.tla": b"new"}))
        dest = os.path.join(self.main, "third_party", "external", "name")
        os.makedirs(dest)
        with open(os.path.join(dest, "a.tla"), "wb") as out:
            out.write(b"old")
        with open(os.path.join(dest, fx.MARKER), "w") as out:
            out.write(f"{SPEC['commit']} {fx.overlay_digest('name')}\n")
        result = {}

        def installer():
            try:
                fx.fetch_repo("name", SPEC, force=True)
                result["ok"] = True
            except BaseException as error:      # noqa: BLE001 - reported to the test
                result["error"] = error

        with dependencies.install_lock(self.store()):
            thread = threading.Thread(target=installer)
            thread.start()
            time.sleep(0.3)
            self.assertEqual(result, {}, "the second installer must wait for the lock")
            with open(os.path.join(dest, "a.tla"), "rb") as source:
                self.assertEqual(source.read(), b"old", "the old complete input must survive")
        thread.join(timeout=20)
        self.assertTrue(result.get("ok"), result.get("error"))
        with open(os.path.join(dest, "a.tla"), "rb") as source:
            self.assertEqual(source.read(), b"new")


class Publish(Layout):

    @staticmethod
    def fail_nth_rename(fail_at):
        real = os.rename
        seen = {"n": 0}

        def rename(source, target):
            seen["n"] += 1
            if seen["n"] == fail_at:
                raise OSError("injected rename failure")
            return real(source, target)
        return rename

    def test_publish_replaces_the_old_tree_and_leaves_no_backup(self):
        dest = os.path.join(self.tmp.name, "dest")
        os.makedirs(dest)
        with open(os.path.join(dest, "old"), "w") as out:
            out.write("old")
        staging = dependencies.staging_dir(dest)
        with open(os.path.join(staging, "new"), "w") as out:
            out.write("new")
        dependencies.publish(staging, dest)
        self.assertEqual(os.listdir(dest), ["new"])
        self.assertFalse(os.path.exists(dest + ".prev"), "the backup must be removed on success")

    def test_failed_rename_restores_the_old_tree(self):
        dest = os.path.join(self.tmp.name, "dest")
        os.makedirs(dest)
        with open(os.path.join(dest, "old"), "w") as out:
            out.write("old")
        staging = dependencies.staging_dir(dest)
        with open(os.path.join(staging, "new"), "w") as out:
            out.write("new")
        with patch.object(dependencies.os, "rename", side_effect=self.fail_nth_rename(2)):
            with self.assertRaises(OSError):
                dependencies.publish(staging, dest)
        self.assertEqual(os.listdir(dest), ["old"], "the old complete tree must be restored")
        self.assertTrue(os.path.isdir(staging), "the staged tree stays for the caller to clean up")


class Install(Layout):

    def complete(self, fx, dest, commit, content=b"old"):
        os.makedirs(dest, exist_ok=True)
        with open(os.path.join(dest, "a.tla"), "wb") as out:
            out.write(content)
        with open(os.path.join(dest, fx.MARKER), "w") as out:
            out.write(f"{commit} {fx.overlay_digest('name')}\n")

    def test_up_to_date_requires_a_matching_receipt(self):
        fx, _ = self.fetch_env(self.main, b"")
        dest = os.path.join(self.main, "third_party", "external", "name")
        os.makedirs(dest)
        with open(os.path.join(dest, "partial"), "w") as out:
            out.write("x")
        self.assertFalse(fx.up_to_date("name", dest, SPEC), "a tree without a receipt is incomplete")
        self.complete(fx, dest, "b" * 40)
        self.assertFalse(fx.up_to_date("name", dest, SPEC), "a receipt for another commit is not ours")
        self.complete(fx, dest, SPEC["commit"])
        self.assertTrue(fx.up_to_date("name", dest, SPEC))

    def test_overlay_digest_matches_apply_overlay(self):
        fx, _ = self.fetch_env(self.main, b"", {"name/d/x.cfg": b"ours"})
        dest = os.path.join(self.tmp.name, "tree")
        os.makedirs(dest)
        self.assertEqual(fx.apply_overlay("name", dest), fx.overlay_digest("name"))
        self.assertEqual(fx.overlay_digest("absent"), fx.overlay_digest("also-absent"))

    def test_fetch_repo_stages_overlay_and_receipt(self):
        fx, calls = self.fetch_env(self.main, tarball({"name-abc/root/a.tla": b"A", "name-abc/root/sub/b.cfg": b"B"}),
                                   {"name/extra.cfg": b"ours"})
        fx.fetch_repo("name", SPEC)
        dest = os.path.join(self.main, "third_party", "external", "name")
        self.assertEqual(sorted(snapshot(dest)), [".fetched", "a.tla", "extra.cfg", "sub/b.cfg"])
        with open(os.path.join(dest, ".fetched")) as source:
            self.assertEqual(source.read(), f"{SPEC['commit']} {fx.overlay_digest('name')}\n")
        self.assertEqual(len(calls), 1)
        fx.fetch_repo("name", SPEC)                       # up to date: no download, no write
        self.assertEqual(len(calls), 1)
        self.assertFalse([n for n in os.listdir(os.path.dirname(dest)) if n.startswith(".name")],
                         "staging leftovers must not survive")

    def test_partial_final_tree_is_reinstalled(self):
        fx, _ = self.fetch_env(self.main, tarball({"name-abc/root/a.tla": b"A"}))
        dest = os.path.join(self.main, "third_party", "external", "name")
        os.makedirs(dest)
        with open(os.path.join(dest, "half"), "w") as out:
            out.write("half")
        fx.fetch_repo("name", SPEC)
        self.assertEqual(sorted(snapshot(dest)), [".fetched", "a.tla"])

    def test_overlay_only_skips_a_tree_that_was_never_uploaded(self):
        fx, calls = self.fetch_env(self.main, b"", {"name/d/x.cfg": b"ours"})
        dest = os.path.join(self.main, "third_party", "external", "name")
        self.assertIsNone(fx.overlay_uploaded("name", SPEC), "no uploaded tree, nothing to overlay")
        self.assertFalse(os.path.exists(dest))
        self.assertEqual(calls, [])

    def test_overlay_only_applies_the_branch_overlay_and_keeps_the_uploaded_commit(self):
        # The cloud rsyncs third_party/ from the shared store, so a cfg this branch
        # changed only reaches the instance through the overlay (2026-10-09).
        fx, calls = self.fetch_env(self.main, b"", {"name/d/x.cfg": b"ours"})
        dest = os.path.join(self.main, "third_party", "external", "name")
        os.makedirs(os.path.join(dest, "d"))
        with open(os.path.join(dest, "d", "x.cfg"), "wb") as out:
            out.write(b"the shared store's older overlay")
        with open(os.path.join(dest, "a.tla"), "wb") as out:
            out.write(b"A")
        with open(os.path.join(dest, fx.MARKER), "w") as out:
            out.write(f"{SPEC['commit']} {'0' * 16}\n")
        self.assertEqual(fx.overlay_uploaded("name", SPEC),
                         f"applied {'0' * 16}->{fx.overlay_digest('name')}")
        with open(os.path.join(dest, "d", "x.cfg"), "rb") as source:
            self.assertEqual(source.read(), b"ours", "the branch overlay must reach the uploaded tree")
        with open(os.path.join(dest, fx.MARKER)) as source:
            self.assertEqual(source.read(), f"{SPEC['commit']} {fx.overlay_digest('name')}\n",
                             "the receipt keeps the uploaded tree's commit")
        self.assertEqual(calls, [], "overlay-only never downloads")

    def test_overlay_only_is_a_no_op_when_the_uploaded_overlay_is_current(self):
        fx, _ = self.fetch_env(self.main, b"", {"name/d/x.cfg": b"ours"})
        dest = os.path.join(self.main, "third_party", "external", "name")
        os.makedirs(os.path.join(dest, "d"))
        with open(os.path.join(dest, "d", "x.cfg"), "wb") as out:
            out.write(b"ours")
        with open(os.path.join(dest, fx.MARKER), "w") as out:
            out.write(f"{SPEC['commit']} {fx.overlay_digest('name')}\n")
        before = snapshot(dest)
        self.assertEqual(fx.overlay_uploaded("name", SPEC), "unchanged " + fx.overlay_digest("name"))
        self.assertEqual(snapshot(dest), before)

    def test_failed_overlay_keeps_the_old_complete_tree(self):
        fx, _ = self.fetch_env(self.main, tarball({"name-abc/root/a.tla": b"new"}))
        dest = os.path.join(self.main, "third_party", "external", "name")
        self.complete(fx, dest, SPEC["commit"])
        before = snapshot(dest)
        with patch.object(fx, "apply_overlay", side_effect=OSError("injected overlay failure")):
            with self.assertRaises(OSError):
                fx.fetch_repo("name", SPEC, force=True)
        self.assertEqual(snapshot(dest), before, "a failed overlay must not publish")
        self.assertFalse([n for n in os.listdir(os.path.dirname(dest)) if n.startswith(".name")])



FAKE_LIB = """record() {
  name="$1"; shift
  { printf '%s' "$name"; for a in "$@"; do printf ' %s' "$a"; done; printf '\\n'; } >>"$FAKE_LOG"
}
"""

# Minimal stand-ins for the network/clone/unpack tools of fetch-deps.sh: every
# fake records its complete argv (HARNESS-22) and only ever writes inside the
# staging directory the script hands it.
FAKES = {
    "curl": """#!/bin/sh
. "$FAKE_LIB"
record curl "$@"
out=""; url=""
while [ $# -gt 0 ]; do
  case "$1" in -o) out="$2"; shift 2 ;; *) url="$1"; shift ;; esac
done
[ -n "$out" ] || exit 2
if [ -n "${FAKE_CURL_FAIL:-}" ]; then printf 'partial' >"$out"; exit 22; fi
case "$url" in
  # The pinned-baseline jars are real archives; the test supplies their bytes.
  *tla2tools.jar) cp "${FAKE_CURL_JAR:?}" "$out" ;;
  *CommunityModules*) cp "${FAKE_CURL_COMMUNITY:?}" "$out" ;;
  *) printf 'payload\\n' >"$out" ;;
esac
""",
    "git": """#!/bin/sh
. "$FAKE_LIB"
record git "$@"
case "$1" in
  clone) for last in "$@"; do :; done; mkdir -p "$last"; printf 'clone\\n' >"$last/README" ;;
esac
""",
    "unzip": """#!/bin/sh
. "$FAKE_LIB"
record unzip "$@"
dir="."
while [ $# -gt 0 ]; do
  case "$1" in -d) dir="$2"; shift 2 ;; *) shift ;; esac
done
mkdir -p "$dir"
printf 'module\\n' >"$dir/CommunityModules.tla"
""",
    "tar": """#!/bin/sh
. "$FAKE_LIB"
record tar "$@"
dir="."
while [ $# -gt 0 ]; do
  case "$1" in -C) dir="$2"; shift 2 ;; *) shift ;; esac
done
mkdir -p "$dir/tlapm-main"
printf 'tlapm\\n' >"$dir/tlapm-main/README"
""",
}


class FetchDepsScript(Layout):
    """fetch-deps.sh end to end: fake curl/git/unzip/tar, private checkout, no network."""

    def setUp(self):
        super().setUp()
        # The declared baselines are fixed jars; a test cannot reproduce their
        # bytes, so it declares synthetic ones through the pin overrides.
        self.jar = synthetic_jar()
        self.jar_path = os.path.join(self.tmp.name, "synthetic-tla2tools.jar")
        with open(self.jar_path, "wb") as out:
            out.write(self.jar)
        self.community = synthetic_jar(revision="c" * 40, version="CommunityModules synthetic")
        self.community_path = os.path.join(self.tmp.name, "synthetic-community.jar")
        with open(self.community_path, "wb") as out:
            out.write(self.community)

    def pin_envs(self):
        """The synthetic pins plus the fake downloads that satisfy them."""
        return {dependencies.PIN_OVERRIDE_ENV: pin_env(self.jar),
                dependencies.COMMUNITY_PIN_OVERRIDE_ENV: community_pin_env(self.community),
                "FAKE_CURL_JAR": self.jar_path, "FAKE_CURL_COMMUNITY": self.community_path}

    def checkout(self, root):
        """A synthetic checkout: real third_party/ plus copies of the fetched scripts."""
        os.makedirs(os.path.join(root, "scripts"))
        for name in ("fetch-deps.sh", "dependencies.py", "tlxlib.py", "tempdirs.py"):
            shutil.copy(os.path.join(HERE, name), os.path.join(root, "scripts", name))
        shutil.copytree(os.path.join(HERE, "harness"), os.path.join(root, "scripts", "harness"))
        return os.path.join(root, "scripts", "fetch-deps.sh")

    def fake_path(self):
        """A bin directory of fakes ahead of PATH; returns (env, argv log path)."""
        bin_dir = os.path.join(self.tmp.name, "bin")
        os.makedirs(bin_dir, exist_ok=True)
        lib = os.path.join(bin_dir, "fakelib.sh")
        with open(lib, "w") as out:
            out.write(FAKE_LIB)
        for name, body in FAKES.items():
            path = os.path.join(bin_dir, name)
            with open(path, "w") as out:
                out.write(body)
            os.chmod(path, 0o755)
        log = os.path.join(self.tmp.name, "argv.log")
        return {"PATH": bin_dir + os.pathsep + os.environ["PATH"], "FAKE_LOG": log, "FAKE_LIB": lib}, log

    def test_tests_only_uses_verified_bundled_oracle_without_cloning_examples(self):
        root = self.main
        script = self.checkout(root)
        bundled = os.path.join(root, 'tests', 'deps', 'tla2tools.jar')
        os.makedirs(os.path.dirname(bundled))
        with open(bundled, 'wb') as out:
            out.write(self.jar)
        env, log = self.fake_path()
        env.update(self.pin_envs())
        result = subprocess.run(['bash', script, '--tests-only'], cwd=root, capture_output=True,
                                text=True, env={**os.environ, **env})
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertFalse(os.path.exists(os.path.join(root, 'third_party', 'Examples')))
        with open(log) as source:
            commands = source.read()
        self.assertNotIn(dependencies.TLA2TOOLS_PIN['url'], commands)
        self.assertNotIn('git clone', commands)
        with open(os.path.join(root, 'third_party', 'tla2tools.jar'), 'rb') as source:
            self.assertEqual(source.read(), self.jar)

    def test_corrupt_bundled_oracle_is_refused_before_download(self):
        root = self.main
        script = self.checkout(root)
        bundled = os.path.join(root, 'tests', 'deps', 'tla2tools.jar')
        os.makedirs(os.path.dirname(bundled))
        with open(bundled, 'wb') as out:
            out.write(b'not the declared jar')
        env, log = self.fake_path()
        env.update(self.pin_envs())
        result = subprocess.run(['bash', script, '--tests-only'], cwd=root, capture_output=True,
                                text=True, env={**os.environ, **env})
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(os.path.exists(os.path.join(root, 'third_party', 'tla2tools.jar')))
        if os.path.exists(log):
            with open(log) as source:
                self.assertNotIn('curl ', source.read())

    def test_fetch_deps_stages_every_artifact_and_publishes_it(self):
        root = self.main
        script = self.checkout(root)
        env, log = self.fake_path()
        env = {**env, **self.pin_envs()}
        result = subprocess.run(["bash", script], cwd=root, capture_output=True, text=True,
                                env={**os.environ, **env})
        self.assertEqual(result.returncode, 0, result.stderr)
        store = os.path.join(root, "third_party")
        self.assertEqual(sorted(os.listdir(store)),
                         [".dependencies.lock", "Examples", "apalache", "community", "tla2tools.jar", "tlapm"])
        self.assertEqual(sorted(os.listdir(os.path.join(store, "apalache"))),
                         ["Apalache.tla", "Option.tla", "Variants.tla"])
        self.assertTrue(os.path.isfile(os.path.join(store, "tlapm", "README")))
        self.assertTrue(os.path.isfile(os.path.join(store, "community", "CommunityModules.tla")))
        self.assertTrue(os.path.isfile(os.path.join(store, "Examples", "README")))
        self.assertEqual(snapshot(store)["tla2tools.jar"], self.jar,
                         "the verified download must be the published jar")
        self.assertEqual(snapshot(store)["community/modules.jar"], self.community,
                         "the verified CommunityModules download must be the published jar")
        with open(log) as source:
            argv = source.read().splitlines()
        # Staged next to the target (same filesystem) and renamed into place.
        # The URL comes from the declared pin, not from a literal in the script.
        self.assertTrue(any(re.fullmatch(
            r"curl -sSfL -o \./\.tla2tools\.jar\.\w+ "
            + re.escape(dependencies.TLA2TOOLS_PIN["url"]), line)
            for line in argv), argv)
        self.assertTrue(any(re.fullmatch(
            r"curl -sSfL -o \.community\.\w+/\.modules\.jar\.\w+ "
            + re.escape(dependencies.COMMUNITY_MODULES_PIN["url"]), line)
            for line in argv), argv)
        self.assertNotIn("releases/latest", "\n".join(argv),
                         "the community download must use the pinned release URL")
        self.assertTrue(any(re.fullmatch(r"git clone -q --depth 1 https://github\.com/tlaplus/Examples\.git "
                                         r"\.Examples\.\w+", line) for line in argv), argv)
        self.assertTrue(any(line.startswith("unzip -q -o ") and line.endswith(" -d .") for line in argv), argv)
        self.assertTrue(any(line.startswith("tar -xzf ") and " -C " in line for line in argv), argv)
        self.assertFalse([n for n in os.listdir(store) if n.startswith(".") and n != dependencies.LOCK_NAME],
                         "no staging leftovers may survive")
        before = snapshot(store)
        again = subprocess.run(["bash", script], cwd=root, capture_output=True, text=True,
                               env={**os.environ, **env})
        self.assertEqual(again.returncode, 0, again.stderr)
        self.assertEqual(snapshot(store), before, "a second fetch must not rewrite the store")

    def test_an_existing_foreign_jar_is_refused_not_silently_kept(self):
        root = self.main
        script = self.checkout(root)
        foreign = os.path.join(root, "third_party", "tla2tools.jar")
        os.makedirs(os.path.dirname(foreign), exist_ok=True)
        with open(foreign, "wb") as out:
            out.write(b"an older or arbitrary jar")
        env, _ = self.fake_path()
        env = {**env, **self.pin_envs()}
        result = subprocess.run(["bash", script], cwd=root, capture_output=True, text=True,
                                env={**os.environ, **env})
        self.assertNotEqual(result.returncode, 0, "an existing foreign jar must fail the fetch")
        self.assertIn("refusing an existing", result.stderr)
        with open(foreign, "rb") as source:
            self.assertEqual(source.read(), b"an older or arbitrary jar",
                             "the refused jar must be left as it was, not replaced")
        # Control: the jar that IS the declared baseline is accepted in place.
        with open(foreign, "wb") as out:
            out.write(self.jar)
        again = subprocess.run(["bash", script], cwd=root, capture_output=True, text=True,
                               env={**os.environ, **env})
        self.assertEqual(again.returncode, 0, again.stderr)
        self.assertEqual(snapshot(os.path.dirname(foreign))["tla2tools.jar"], self.jar)

    def test_an_existing_foreign_community_jar_is_refused_not_silently_kept(self):
        root = self.main
        script = self.checkout(root)
        foreign = os.path.join(root, "third_party", "community", "modules.jar")
        os.makedirs(os.path.dirname(foreign), exist_ok=True)
        with open(foreign, "wb") as out:
            out.write(b"an older or arbitrary CommunityModules jar")
        env, _ = self.fake_path()
        env = {**env, **self.pin_envs()}
        result = subprocess.run(["bash", script, "--tests-only"], cwd=root, capture_output=True,
                                text=True, env={**os.environ, **env})
        self.assertNotEqual(result.returncode, 0, "an existing foreign community jar must fail")
        self.assertIn("refusing an existing", result.stderr)
        with open(foreign, "rb") as source:
            self.assertEqual(source.read(), b"an older or arbitrary CommunityModules jar",
                             "the refused community jar must be left as it was, not replaced")
        # Control: the jar that IS the declared baseline is accepted in place.
        with open(foreign, "wb") as out:
            out.write(self.community)
        again = subprocess.run(["bash", script, "--tests-only"], cwd=root, capture_output=True,
                               text=True, env={**os.environ, **env})
        self.assertEqual(again.returncode, 0, again.stderr)
        self.assertEqual(snapshot(os.path.dirname(foreign))["modules.jar"], self.community)

    def test_a_corrupt_community_download_is_refused_before_publication(self):
        root = self.main
        script = self.checkout(root)
        wrong = os.path.join(self.tmp.name, "wrong-community.jar")
        with open(wrong, "wb") as out:
            out.write(self.community[:200])     # non-empty, but not the declared bytes
        env, _ = self.fake_path()
        env = {**env, **self.pin_envs(), "FAKE_CURL_COMMUNITY": wrong}
        result = subprocess.run(["bash", script, "--tests-only"], cwd=root, capture_output=True,
                                text=True, env={**os.environ, **env})
        self.assertNotEqual(result.returncode, 0, "bytes that are not the pin must fail the fetch")
        self.assertIn("refusing the bytes served by", result.stderr)
        store = os.path.join(root, "third_party")
        self.assertFalse(os.path.exists(os.path.join(store, "community")),
                         "a refused body must not become third_party/community")
        self.assertFalse([n for n in os.listdir(store) if n.startswith(".community")],
                         "a refused body must not leave a staging directory")

    def test_a_download_that_is_not_the_pinned_jar_is_refused(self):
        root = self.main
        script = self.checkout(root)
        wrong = os.path.join(self.tmp.name, "wrong.jar")
        with open(wrong, "wb") as out:
            out.write(self.jar[:200])           # non-empty, but not the declared bytes
        env, _ = self.fake_path()
        env = {**env, **self.pin_envs(), "FAKE_CURL_JAR": wrong}
        result = subprocess.run(["bash", script], cwd=root, capture_output=True, text=True,
                                env={**os.environ, **env})
        self.assertNotEqual(result.returncode, 0, "bytes that are not the pin must fail the fetch")
        self.assertIn("refusing the bytes served by", result.stderr)
        store = os.path.join(root, "third_party")
        self.assertEqual(sorted(os.listdir(store)), [dependencies.LOCK_NAME],
                         "a refused body must not become tla2tools.jar or a staging leftover")

    def test_failed_download_leaves_no_partial_final_file(self):
        root = self.main
        script = self.checkout(root)
        env, _ = self.fake_path()
        result = subprocess.run(["bash", script], cwd=root, capture_output=True, text=True,
                                env={**os.environ, **env, "FAKE_CURL_FAIL": "1"})
        self.assertNotEqual(result.returncode, 0, "a failed download must fail the fetch")
        store = os.path.join(root, "third_party")
        self.assertEqual(sorted(os.listdir(store)), [dependencies.LOCK_NAME],
                         "the partial body must not become the final file")
        self.assertIn("failed or empty download", result.stderr)


if __name__ == "__main__":
    unittest.main()
