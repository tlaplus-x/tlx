#!/usr/bin/env python3
"""The single installation service for the shared third_party/ dependency store.

third_party/ is shared: every linked worktree holds a symlink to the main
checkout's tree, so a direct write from a worker lands in another checkout. An
install must therefore go through one owner and one atomic path (HARNESS-15):

  owner     the store is writable only by the checkout whose own third_party/
            path resolves to it; a worker's write through the symlink is
            refused before a byte is downloaded (realpath ownership review).
  staging   an install is built in a hidden sibling of the final path and
            published with a single rename, so a partial download, a failed
            overlay or a failed rename leaves the previous complete tree in
            place instead of a partial final directory or file.
  receipt   the completion receipt (fetch-external's .fetched, <commit>
            <overlay digest>) is written into the staged tree, so a published
            tree always carries a receipt that matches it; a tree without one
            is incomplete, not an installation.
  lock      installers serialize on <store>/.dependencies.lock (flock); the
            second one waits and then finds the install already up to date.

The TLC oracle baseline (third_party/tla2tools.jar) is declared once in
TLA2TOOLS_PIN below: its release URL, the SHA-256 of the pinned bytes and the git
revision its manifest must report. A jar that merely exists is not the baseline;
verify_tla2tools refuses a jar that does not match exactly (DOC-09).

third_party/community/modules.jar is declared the same way in
COMMUNITY_MODULES_PIN: the pinned CommunityModules release URL and the SHA-256 of
its bytes. Those bytes enter every TLC baseline's content_digest
(benchmarking/baselines.py), so verify_community_modules refuses an existing jar
that does not match and a mutable `releases/latest` cannot silently invalidate
stored baselines (DOC-09, HARNESS-15).

usage:
  scripts/dependencies.py owner-check [--root DIR]     # exit 1 unless DIR owns third_party/
  scripts/dependencies.py run [--root DIR] -- CMD ...  # run CMD holding the store lock
  scripts/dependencies.py verify-jar PATH              # exit 1 unless PATH is the pinned tla2tools.jar
  scripts/dependencies.py verify-community PATH        # exit 1 unless PATH is the pinned modules.jar
  scripts/dependencies.py pin [FIELD]                  # print the TLC baseline (or one field)
  scripts/dependencies.py pin-community [FIELD]        # print the CommunityModules baseline (or one field)

A synthetic test that produces its own bytes declares them through the
TLA2TOOLS_PIN_JSON / COMMUNITY_MODULES_PIN_JSON environment overrides (see
declared_pin); every normal install verifies against the committed pins above.
"""
import argparse, contextlib, fcntl, hashlib, json, os, re, shutil, subprocess, tempfile, time, zipfile

from tlxlib import ROOT

LOCK_NAME = ".dependencies.lock"


class InstallError(SystemExit):
    """Refused or failed install; str() is the CLI message (no traceback)."""


# Test seams, deliberately outside the reserved TLX_ environment namespace: JSON
# objects that override fields of TLA2TOOLS_PIN and COMMUNITY_MODULES_PIN (see
# declared_pin). Unset or blank always selects the committed pin, so they cannot
# quietly loosen a normal install; only synthetic tests that produce their own
# bytes set them.
PIN_OVERRIDE_ENV = "TLA2TOOLS_PIN_JSON"
COMMUNITY_PIN_OVERRIDE_ENV = "COMMUNITY_MODULES_PIN_JSON"

# The declared TLC oracle baseline (DOC-09): one source of truth for the identity
# of third_party/tla2tools.jar. `sha256` are the pinned bytes; `revision` is the
# git revision the jar's manifest must report (SHA-256 already fixes it, so the
# revision is a cross-check that catches an edited pin). The v1.8.0 release asset
# has since been re-uploaded with another revision, so the URL is only a
# best-effort download source and the verification, not the URL, is the authority.
TLA2TOOLS_PIN = {
    "name": "tla2tools.jar",
    "url": "https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar",
    "sha256": "b490f45c1de08e4ff9753259a00338981b9cf464f01ca9e9cd5f19f33cf0bb92",
    "revision": "1813307068bbc5759a441df820f3f548948d6b7a",
    "short": "1813307",
    "version": "2.0 2026-10-02",
    "build": "2026-10-02T16:35:56.5Z",
}

# The declared CommunityModules baseline (DOC-09, HARNESS-15): one source of
# truth for the identity of third_party/community/modules.jar. Its manifest has
# no git revision, so the release tag and the SHA-256 of the pinned bytes are the
# identity. The release URL is immutable by tag, but `releases/latest` is not:
# only the hash decides whether an installed jar is the baseline.
COMMUNITY_MODULES_PIN = {
    "name": "modules.jar",
    "url": ("https://github.com/tlaplus/CommunityModules/releases/download/"
            "202609120237/CommunityModules-deps.jar"),
    "release": "202609120237",
    "sha256": "3d9a282c360e90d55e9bbe99caa2987d508fef1556d652760b4af4455e283733",
}


def declared_pin(pin=TLA2TOOLS_PIN, override_env=PIN_OVERRIDE_ENV):
    """The committed baseline pin, unless `override_env` overrides some fields.

    The override exists only so a synthetic test can declare the bytes it made
    instead of the real release; it accepts a partial object (at least one field)
    and never gains a field the committed pin does not have.
    """
    override = os.environ.get(override_env)
    if not override:
        return dict(pin)
    try:
        fields = json.loads(override)
    except ValueError as error:
        raise InstallError(f"{override_env}: not valid JSON: {error}")
    if not isinstance(fields, dict) or not fields or set(fields) - set(pin):
        raise InstallError(f"{override_env}: expected a non-empty object with keys from "
                           f"{sorted(pin)}")
    return {**pin, **fields}

def sha256_file(path, chunk=1 << 20):
    """Hex SHA-256 of a file's bytes (streamed; a jar is a few MiB)."""
    digest = hashlib.sha256()
    with open(path, "rb") as source:
        for block in iter(lambda: source.read(chunk), b""):
            digest.update(block)
    return digest.hexdigest()


def jar_manifest(path):
    """The `Key: value` fields of a jar's META-INF/MANIFEST.MF, or {} if unreadable."""
    try:
        with zipfile.ZipFile(path) as jar:
            text = jar.read("META-INF/MANIFEST.MF").decode("utf-8", "replace")
    except (OSError, KeyError, zipfile.BadZipFile):
        return {}
    return dict(re.findall(r"^([A-Za-z0-9][A-Za-z0-9-]*):\s?(.*?)\s*$", text, re.M))


def jar_identity(path):
    """{sha256, revision, short, version} of a jar; any field may be None."""
    try:
        digest = sha256_file(path)
    except OSError:
        return {}
    manifest = jar_manifest(path)
    return {"sha256": digest, "revision": manifest.get("X-Git-Revision"),
            "short": manifest.get("X-Git-ShortRevision"),
            "version": manifest.get("Implementation-Version")}


def verify_tla2tools(path, pin=None):
    """Refuse unless `path` is exactly the declared TLC baseline jar.

    Returns the observed identity on an exact match and raises InstallError
    otherwise: a missing file, a non-jar, a jar whose bytes differ from the pin,
    or a pin whose declared revision contradicts its hash. Existing is not enough
    (DOC-09), so the download URL cannot silently define compatibility.
    """
    pin = {**TLA2TOOLS_PIN, **pin} if pin else declared_pin()
    if not os.path.isfile(path):
        raise InstallError(f"{path}: no {pin['name']}; expected the declared TLC baseline "
                           f"{pin['short']} ({pin['url']})")
    identity = jar_identity(path)
    if identity.get("sha256") != pin["sha256"]:
        raise InstallError(
            f"{path}: not the declared TLC baseline {pin['short']}: "
            f"sha256 {identity.get('sha256') or 'unreadable'} != pinned {pin['sha256']}\n"
            f"  the pinned jar is TLC {pin['version']} (rev {pin['revision']}, build {pin['build']})\n"
            f"  from {pin['url']}; that release asset has been re-uploaded with another revision,\n"
            f"  so do not accept whatever the URL serves: provide the pinned bytes instead")
    if identity.get("revision") != pin["revision"]:
        raise InstallError(
            f"{path}: pinned bytes but manifest revision {identity.get('revision')!r} "
            f"!= declared {pin['revision']!r}: the pin is inconsistent")
    return identity


def verify_community_modules(path, pin=None):
    """Refuse unless `path` is exactly the declared CommunityModules baseline jar.

    Returns the observed identity on an exact match and raises InstallError
    otherwise: a missing file or bytes whose SHA-256 differs from the pin. The
    jar's bytes are part of every model's `content_digest`, so an upstream
    `releases/latest` move must not redefine the baseline (DOC-09, HARNESS-15).
    """
    pin = ({**COMMUNITY_MODULES_PIN, **pin} if pin
           else declared_pin(COMMUNITY_MODULES_PIN, COMMUNITY_PIN_OVERRIDE_ENV))
    if not os.path.isfile(path):
        raise InstallError(f"{path}: no {pin['name']}; expected the declared CommunityModules "
                           f"baseline {pin['release']} ({pin['url']})")
    identity = jar_identity(path)
    if identity.get("sha256") != pin["sha256"]:
        raise InstallError(
            f"{path}: not the declared CommunityModules baseline {pin['release']}: "
            f"sha256 {identity.get('sha256') or 'unreadable'} != pinned {pin['sha256']}\n"
            f"  the pinned jar is the CommunityModules {pin['release']} release asset from\n"
            f"  {pin['url']}\n"
            f"  its bytes enter every TLC baseline's content_digest, so do not accept whatever\n"
            f"  releases/latest serves: provide the pinned bytes instead")
    return identity


def store_path(root=None):
    """The third_party/ path of a checkout (a symlink in a linked worktree)."""
    return os.path.join(root or ROOT, "third_party")


def store_realpath(root=None):
    return os.path.realpath(store_path(root))


def owns_store(root=None):
    """True when this checkout's third_party/ is its own, not another checkout's."""
    root = os.path.realpath(root or ROOT)
    return store_realpath(root) == os.path.join(root, "third_party")


def require_owner(root=None):
    """The resolved store this checkout may install into, or refuse.

    third_party/ is reached through a symlink in a linked worktree; writing
    through it would change another checkout's tree, so only the checkout that
    owns the resolved path may install.
    """
    if not owns_store(root):
        raise InstallError(
            f"refusing to install into the shared dependency store {store_realpath(root)!r}: "
            f"{store_path(root)!r} is not this checkout's own third_party/ "
            f"(it belongs to {os.path.dirname(store_realpath(root))!r}); run the fetch in that "
            f"checkout, or ask the coordinator to refresh the shared store")
    return store_realpath(root)


@contextlib.contextmanager
def install_lock(store, timeout=None):
    """Hold the exclusive installer lock of `store` for the block."""
    os.makedirs(store, exist_ok=True)
    path = os.path.join(store, LOCK_NAME)
    fd = os.open(path, os.O_CREAT | os.O_RDWR, 0o644)
    deadline = None if timeout is None else time.monotonic() + timeout
    try:
        while True:
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except OSError:
                if deadline is not None and time.monotonic() >= deadline:
                    raise InstallError(f"another installer holds {path}; retry later")
                time.sleep(0.05)
        yield store
    finally:
        fcntl.flock(fd, fcntl.LOCK_UN)
        os.close(fd)


def staging_dir(dest):
    """An empty staging directory next to `dest` (same filesystem, one rename)."""
    parent = os.path.dirname(dest)
    os.makedirs(parent, exist_ok=True)
    return tempfile.mkdtemp(prefix=f".{os.path.basename(dest)}.", dir=parent)


def prune(dest):
    """Remove staging and backup leftovers of `dest`; call only under the lock."""
    parent, base = os.path.dirname(dest), os.path.basename(dest)
    for entry in os.listdir(parent) if os.path.isdir(parent) else ():
        if entry.startswith(f".{base}.") or entry == base + ".prev":
            path = os.path.join(parent, entry)
            shutil.rmtree(path, ignore_errors=True)
            if os.path.lexists(path):
                os.unlink(path)


def publish(staging, dest):
    """Atomically replace directory `dest` with the completed `staging` tree.

    The old tree survives a failed rename: `dest` is always either the complete
    old or the complete new tree, and `.prev` is removed on success.
    """
    if not os.path.lexists(dest):
        os.rename(staging, dest)
        return
    backup = dest + ".prev"
    shutil.rmtree(backup, ignore_errors=True)
    os.rename(dest, backup)
    try:
        os.rename(staging, dest)
    except OSError:
        os.rename(backup, dest)
        raise
    shutil.rmtree(backup, ignore_errors=True)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--root", default=None, help=f"checkout root (default: {ROOT})")
    ap.add_argument("command", choices=("owner-check", "run", "verify-jar", "verify-community", "pin",
                                        "pin-community"),
                    help="owner-check: refuse a foreign store; run: execute a command under the lock; "
                         "verify-jar: exit 1 unless PATH is the pinned tla2tools.jar; "
                         "verify-community: exit 1 unless PATH is the pinned modules.jar; pin: print the "
                         "declared TLC baseline; pin-community: print the declared CommunityModules "
                         "baseline")
    ap.add_argument("rest", nargs=argparse.REMAINDER,
                    help="run/verify-jar/verify-community/pin/pin-community arguments (owner-check "
                         "ignores them)")
    a = ap.parse_args(argv)
    args = a.rest[1:] if a.rest[:1] == ["--"] else a.rest
    # verify-jar, verify-community, pin and pin-community are read-only on the
    # declared baselines: no store ownership or lock.
    if a.command in ("verify-jar", "verify-community"):
        if len(args) != 1:
            ap.error(f"{a.command} needs exactly one PATH")
        if a.command == "verify-jar":
            identity = verify_tla2tools(args[0])
            pin = declared_pin()
            print(f"{args[0]}: TLC {pin['version']} (rev {pin['short']}, "
                  f"sha256 {identity['sha256']}) is the declared baseline {pin['url']}")
        else:
            identity = verify_community_modules(args[0])
            pin = declared_pin(COMMUNITY_MODULES_PIN, COMMUNITY_PIN_OVERRIDE_ENV)
            print(f"{args[0]}: CommunityModules {pin['release']} (sha256 {identity['sha256']}) "
                  f"is the declared baseline {pin['url']}")
        return 0
    if a.command in ("pin", "pin-community"):
        pin = (declared_pin() if a.command == "pin"
               else declared_pin(COMMUNITY_MODULES_PIN, COMMUNITY_PIN_OVERRIDE_ENV))
        if not args:
            print(json.dumps(pin, indent=2, sort_keys=True))
            return 0
        if len(args) != 1 or args[0] not in pin:
            ap.error(f"{a.command} takes one field of {sorted(pin)}")
        print(pin[args[0]])
        return 0
    store = require_owner(a.root)
    if a.command == "owner-check":
        print(store)
        return 0
    if not args:
        ap.error("run needs a command after --")
    with install_lock(store):
        return subprocess.run(args).returncode


if __name__ == "__main__":
    raise SystemExit(main())
