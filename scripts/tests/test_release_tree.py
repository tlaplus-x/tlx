"""Verify a release with public benchmark inputs and its current measurement store.

Missing-input fixtures separately exercise damaged checkouts. The real released
copy must carry runnable inputs without relying on ignored maintainer files.
"""

import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import tempdirs
import unshipped

ROOT = Path(__file__).resolve().parents[2]

#: The manifest of the benchmark suite: the store file every reader of the store
#: reaches first, and so the one a released tree lacks before any other.
MANIFEST = 'bench/suite.json'

#: The manifest the `manifest` tree carries, built rather than copied.
#:
#: The manifest is itself a store file, so a checkout of the published sources
#: has none to copy from and a fixture that read the checkout's would pass only
#: on a machine that still keeps the store on disk - the silent-skip shape
#: `scripts/tests/test_bench_records.py`'s `StoreCoherenceTest` rules out by owning
#: its data. This one is a valid manifest (`bench_suite.validate_manifest`
#: accepts it, which the rows below would catch first, because an unreadable
#: fixture is refused with a `ValueError` traceback rather than the sentence
#: they pin) and it names a `bench/Repr*` model on purpose: once the manifest is
#: present, that is the id family whose configurations are the *next* store
#: input a reader reaches, so every `manifest`-tree row of `STORE_INPUTS` still
#: lands on `bench/repr-models.toml` and `REPR_REFUSAL`, not on the manifest.
FIXTURE_MANIFEST = {
    'version': 1,
    'models': [
        {'id': 'bench/ReprRaft', 'size': 'small', 'timeout_s': 120,
         'runs': [{'mode': 'compile', 'workers': 1, 'args': ['-tlc']}],
         'expect': {'source': 'unpinned'}},
    ],
}

#: The two sentences an absent store file is refused with, as the code prints
#: them. `bench_suite.missing_input` owns the first, for the suite commands and
#: for `bench_records.store_text` (its sibling), and `repr_check` the second, for
#: the one file two readers share (`benchmarking.models.stress_models` says the
#: same thing about `bench/repr-models.toml`).
MANIFEST_REFUSAL = ('No such file: %s: benchmark inputs and current baseline records ship with the sources '
                    '(docs/benchmarking.md section 6.2)')
REPR_REFUSAL = (' is not in this checkout: the reduced representation configurations '
                'are missing; restore the tracked bench/repr-models.toml and bench/repr-configs/')

#: Every command whose first input in a released tree is a store file, with the
#: tree it is driven in and the store file its refusal must name. `released` is
#: the tree without `bench/` at all, where every reader reaches the manifest
#: first; `manifest` is that tree plus `bench/suite.json` alone, where the
#: manifest is there and the next missing input is the representation
#: configurations - the step the hand sweep measured, which is a row here now.
STORE_INPUTS = (
    ('missing', ('scripts/bench.py', 'suite-check'), MANIFEST),
    ('missing', ('scripts/bench.py', 'report'), MANIFEST),
    ('missing', ('scripts/bench.py', 'table'), MANIFEST),
    ('missing', ('scripts/bench.py', 'suite-report'), MANIFEST),
    ('missing', ('scripts/bench.py', 'migrate'), MANIFEST),
    ('missing', ('scripts/bench.py', 'release', '--report-only'), MANIFEST),
    ('manifest', ('scripts/bench.py', 'suite-check'), 'bench/repr-models.toml'),
    ('manifest', ('scripts/bench.py', 'report'), 'bench/repr-models.toml'),
    ('manifest', ('scripts/bench.py', 'table'), 'bench/repr-models.toml'),
    ('manifest', ('scripts/bench.py', 'suite-report'), 'bench/repr-models.toml'),
    ('manifest', ('scripts/bench.py', 'tlcbase', '--missing'), 'bench/repr-models.toml'),
)

#: The `bench.py` subcommands `STORE_INPUTS` does not drive: each one needs a
#: built tlx binary (the program builds one), the corpus under `third_party/`,
#: TLC, or a file the contributor names, so its first failure in a released tree
#: is not the store's absence. `test_every_bench_subcommand_is_classified` makes
#: the two sets cover the parser's subcommands, so a subcommand added to
#: `bench.py` has to be classified before it can go silent.
NOT_STORE_INPUT = frozenset({
    'liveness', 'disk', 'suite', 'suite-judge', 'suite-merge', 'track', 'profile', 'ttfr', 'ttfr-report',
    'tiers', 'run', 'compare', 'history-report', 'ab', 'perf', 'layout', 'tlcbase-merge',
    'tlcbase-report', 'scale', 'scale-report',
})

# The document the known-bad control edits, and the file this checkout has and
# the released tree does not: a link between them is a link into the store, the
# class the released-tree check exists to refuse.
CONTROL_DOCUMENT = 'docs/performance.md'
CONTROL_TARGET = 'work/archive/unpublished.json'


def bench_subcommand(argv):
    """The `bench.py` subcommand `argv` names, or None for a standalone script."""
    return argv[1] if argv[0] == 'scripts/bench.py' else None


def bench_subcommands():
    """`bench.py`'s subcommand names, from the parser that owns the list."""
    import benchmarking.cli
    return tuple(benchmarking.cli.subcommands(benchmarking.cli.build_parser()))


def git(cwd, *args, **kwargs):
    """A git command that never depends on the machine's git configuration."""
    settings = ['-c', 'user.name=released tree', '-c', 'user.email=tree@example.com',
                '-c', 'commit.gpgsign=false', '-c', 'advice.detachedHead=false',
                # ... and that never starts housekeeping behind this module's back:
                # `git commit` runs `maintenance run --auto` detached by default, and
                # its loose-object task packs the ~2300 objects the commit just wrote
                # within the second - a copy of `.git` taken then fails with `[Errno
                # 2]` on `.git/objects/<xx>` entries the pack removed (2026-10-10:
                # 256 loose directories, 0 one second later, `in-pack: 2300`).
                '-c', 'maintenance.auto=false', '-c', 'gc.auto=0']
    return subprocess.run(['git', *settings, *args], cwd=cwd, capture_output=True, **kwargs)


def tracked(root=ROOT):
    """The tracked paths of `root`, as `git ls-files` reports them."""
    listed = git(root, 'ls-files', '-z', check=True)
    return [name for name in listed.stdout.decode('utf-8', 'surrogateescape').split('\0') if name]


def release_tree(root, into):
    """Copy the released subset of `root`'s tracked tree into `into`, as a repository.

    Returns the copied paths. The copy is a repository because a clone is one
    and two checks read the index (see the module docstring); `into` must be an
    existing, empty directory.
    """
    kept = [name for name in tracked(root) if not unshipped.covers(name)]
    for name in kept:
        target = Path(into) / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(root / name, target)
    for args in (('init', '-q'), ('add', '-A'), ('commit', '-qm', 'released tree')):
        git(into, *args, check=True)
    return kept


def paths(root):
    """Every path the tree holds outside `.git`.

    "Did this command change the checkout" is a question about the paths, not
    about the index: `git status --short` reports the untracked directory a
    command created, and is compared beside this, but a tree shared by several
    cases needs an answer that does not depend on which of them ran first.
    """
    return sorted(p.relative_to(root).as_posix() for p in Path(root).rglob('*') if '.git' not in p.parts)


def run(script, *args, cwd, timeout=300):
    """One entry point of the tree under test, run the way a contributor runs it."""
    return subprocess.run([sys.executable, script, *args], cwd=cwd, capture_output=True,
                          text=True, timeout=timeout)


class ReleasedTree(unittest.TestCase):
    """One released tree for the whole module: building it is the expensive part."""

    @classmethod
    def setUpClass(cls):
        cls.scratch = tempdirs.TemporaryDirectory(prefix='tlx-release-tree-', owner_root=ROOT)
        cls.trees = {}
        started = time.time()
        cls.tree = Path(cls.scratch.name) / 'tree'
        cls.tree.mkdir()
        cls.kept = release_tree(ROOT, cls.tree)
        cls.trees['released'] = cls.tree
        cls.trees['missing'] = Path(cls.scratch.name) / 'missing-input-tree'
        shutil.copytree(cls.tree, cls.trees['missing'])
        shutil.rmtree(cls.trees['missing'] / 'bench')
        # The same tree with the suite manifest and nothing else of the store: the
        # manifest is the first store file every reader reaches, so this is the
        # tree in which the *next* missing input - the representation
        # configurations - is reached. Copied rather than linked, so a command
        # that writes cannot reach back into the released tree through a shared
        # inode; it needs no commit, because no check reads this tree's index.
        cls.trees['manifest'] = Path(cls.scratch.name) / 'manifest-tree'
        shutil.copytree(cls.trees['missing'], cls.trees['manifest'], symlinks=True)
        (cls.trees['manifest'] / 'bench').mkdir()
        (cls.trees['manifest'] / MANIFEST).write_text(json.dumps(FIXTURE_MANIFEST))
        cls.build_seconds = time.time() - started
        print(f'released tree: {len(cls.kept)} of {len(tracked())} tracked paths, '
              f'the two trees built in {cls.build_seconds:.1f}s')

    @classmethod
    def tearDownClass(cls):
        cls.scratch.cleanup()

    def test_release_tree_is_a_repository_the_index_checks_can_read(self):
        # The two checks that read `git ls-files` (the pre-commit hook and the
        # gate run them) must work here: in a directory without an index they
        # fail with exit 128 whatever paths the recipe dropped.
        listed = git(self.tree, 'ls-files', check=True).stdout.decode()
        # One production script here and one store file not: the literal path
        # also ties this module to bench_suite.py for the hook's reference scan,
        # which is where a store reader changes.
        self.assertIn('scripts/benchmarking/bench_suite.py\n', listed)
        self.assertIn('bench/suite.json\n', listed)
        for script, expected in (('scripts/check_imports.py', 'imports: no cycle'),
                                 ('scripts/knobs_check.py', 'knobs: all source names are registered')):
            with self.subTest(script=script):
                result = run(script, cwd=self.tree)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertIn(expected, result.stdout)

    def test_dependency_check_passes_on_the_released_tree(self):
        # The layering and feature-closure policy reads the Cargo manifests and
        # the lockfile, which the released tree carries, and resolves offline,
        # so a checkout of the published sources must still run it.
        result = run('scripts/dependency_check.py', cwd=self.tree)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('; 0 problem(s)', result.stdout)

    def test_doccheck_passes_on_the_released_tree(self):
        result = run('scripts/doccheck.py', cwd=self.tree)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('-- 0 problems', result.stdout)
        self.assertTrue((self.tree / 'AGENTS.md').is_file())
        self.assertNotIn('absent from this checkout, not checked: AGENTS.md', result.stdout)

    def test_public_docs_do_not_require_private_tools(self):
        import re
        documents = [self.tree / name for name in ('README.md', 'AGENTS.md', 'CONTRIBUTING.md', 'SECURITY.md')]
        documents.extend((self.tree / 'docs').rglob('*.md'))
        private = re.compile(r"`(?:harness/|\.agents/|\.claude/|\.githooks/)|"
                             r"\b(?:python3?|sh|bash)\s+(?:harness/|\.agents/|\.claude/|\.githooks/)")
        failures = []
        for path in documents:
            self.assertTrue(path.is_file(), str(path))
            for number, line in enumerate(path.read_text().splitlines(), 1):
                if private.search(line):
                    failures.append(f'{path.relative_to(self.tree)}:{number}: {line}')
        self.assertEqual(failures, [], '\n'.join(failures))

    def test_the_check_rejects_a_document_that_links_unshipped_data(self):
        # An archive link may resolve in the maintainer checkout but must be
        # refused in a clean release. Membership in the shared private set is
        # the invariant, independent of what happens to exist locally.
        self.assertTrue(unshipped.covers(CONTROL_TARGET),
                        f'{CONTROL_TARGET} must be unshipped for the control to be a link into archived data')
        self.assertFalse((self.tree / CONTROL_TARGET).exists(),
                         f'the released tree must not carry {CONTROL_TARGET} for the link to be broken there')
        document = self.tree / CONTROL_DOCUMENT
        original = document.read_text(encoding='utf-8')
        self.addCleanup(document.write_text, original, encoding='utf-8')
        document.write_text(original + f'\nSee [the suite](../{CONTROL_TARGET}).\n', encoding='utf-8')
        result = run('scripts/doccheck.py', cwd=self.tree)
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        self.assertIn(f'{CONTROL_DOCUMENT}:', result.stdout)
        self.assertIn(f'broken link ../{CONTROL_TARGET}', result.stdout)

    def test_a_command_whose_input_is_store_data_names_the_file_it_lacks(self):
        # The class the hand sweep was looking for, as a table: a command whose
        # first input is a store file names that file, says the sources do not
        # ship it, exits non-zero and prints nothing else - one line, no
        # traceback, and no report that renders nothing. The sentence is pinned
        # above, so a reader that drifts from the others turns this red rather
        # than quietly saying something else (`benchmarking.legacy.missing_input`
        # is the one owner for the store's absence, and
        # `benchmarking.models.stress_models` repeats `repr_check`'s words for
        # the representation configurations).
        for tree, argv, missing in STORE_INPUTS:
            with self.subTest(tree=tree, argv=argv):
                result = run(*argv, cwd=self.trees[tree])
                self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
                message = (result.stdout + result.stderr).strip()
                if tree == 'manifest' and argv[1] in ('report', 'table', 'suite-report'):
                    self.assertEqual(message, 'no benchmark measurements: restore a verified data snapshot before generating the report')
                    continue
                refusal = (MANIFEST_REFUSAL % missing) if missing == MANIFEST else REPR_REFUSAL
                self.assertIn(refusal, message)
                self.assertIn(missing, message)
                self.assertNotIn('Traceback', message)
                self.assertNotIn('\n', message)

    def test_every_bench_subcommand_is_classified(self):
        # The boundary of the sweep, mechanically: every subcommand of `bench.py`
        # is either driven by STORE_INPUTS or named in NOT_STORE_INPUT. That is
        # what a hand sweep cannot do - it cannot notice the subcommand nobody
        # classified - and it is why the answer to "which commands still break in
        # a released tree" is a table that grows with the program.
        driven = {bench_subcommand(argv) for _, argv, _ in STORE_INPUTS} - {None}
        self.assertEqual(driven, set(bench_subcommands()) - set(NOT_STORE_INPUT))

    def test_a_refused_command_leaves_the_checkout_as_it_found_it(self):
        # `migrate` re-derives the store and realigns `bench/records`: refused
        # after that, it leaves a store behind a command that failed, and the
        # next run starts from a tree the user did not choose (docs/benchmarking.md
        # 6.2). The tree is one for the whole module, so what is asserted is what
        # this command changed (the listing, which does not depend on the order
        # the other cases ran in), not that the tree is pristine.
        before, status = paths(self.trees['missing']), git(self.trees['missing'], 'status', '--short', check=True).stdout
        result = run('scripts/bench.py', 'migrate', cwd=self.trees['missing'])
        self.assertNotEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('bench/suite.json', result.stdout + result.stderr)
        self.assertEqual(paths(self.trees['missing']), before, 'the refused command wrote into the checkout')
        self.assertEqual(git(self.trees['missing'], 'status', '--short', check=True).stdout, status,
                         'the refused command changed the checkout')
        self.assertFalse((self.trees['missing'] / 'bench').exists(), 'the refused command wrote the store')

    def test_the_tree_carries_exactly_the_tracked_paths_the_sources_publish(self):
        # Nothing joins the copy that a clone would not have: no `target/`, no
        # temporary-directory marker, no file the checkout did not track. A
        # leaked marker would also be committed by the recipe's `git add -A`.
        copied = set(tracked(self.tree))
        self.assertEqual(copied, set(self.kept))
        # What the checks read has to be here, or their agreement means nothing.
        for path in ('crates/tlx-base/src/knobs.rs', 'docs/performance.md', 'scripts/doccheck.py', 'README.md'):
            self.assertIn(path, copied)

    def test_the_tree_carries_none_of_the_unshipped_set(self):
        # The set is a claim about this tree, and a set that stopped matching -
        # a directory renamed, a glob that no longer covers the files it was
        # written for - would leave the released tree carrying harness or store
        # material while every other test here still passed.
        survived = sorted(name for name in tracked(self.tree) if unshipped.covers(name))
        self.assertEqual(survived, [], 'the released tree carries paths the release does not ship')
        # Every path the set covers in this checkout is really absent from the
        # copy. This asks what the recipe copied, not what is on disk: the
        # commands this module drives write into their tree, which is why the
        # manifest tree below is a copy of it and not a link into it. (The
        # notes' evidence was the set's one glob and is no longer in the set at
        # all - it left the repository for `work/notes/` on 2026-10-10 - so the
        # entries this walks are directory prefixes and plain paths.)
        kept = set(self.kept)
        for name in tracked():
            if unshipped.covers(name):
                with self.subTest(path=name):
                    self.assertNotIn(name, kept)
        self.assertFalse((self.tree / 'harness').exists())
        for path in ('scripts/harness/plan_document.py',
                     'scripts/harness/process_observation.py',
                     'scripts/bench_store_equivalence.py',
                     'scripts/move_proof.py', 'scripts/test_move_proof.py',
                     'scripts/code_health.py', 'scripts/repr_check.py',
                     'scripts/coverage_tlc_baselines.py'):
            self.assertNotIn(path, kept, 'local process tooling must not return to the released tree')
        for path in ('work/archive/unpublished.json',):
            self.assertNotIn(path, kept, path)
        # And what the release *does* publish is still there.
        for path in ('AGENTS.md', 'scripts/doccheck.py', 'scripts/verify.py', 'scripts/harness/git.py'):
            self.assertIn(path, kept, path)

    def test_public_benchmark_baseline_reproduces_without_private_archives(self):
        result = subprocess.run([sys.executable, '-m', 'benchmarking.snapshot', 'inputs'],
                                cwd=self.tree, env={**os.environ, 'PYTHONPATH': str(self.tree / 'scripts')},
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('benchmark inputs valid', result.stdout)
        self.assertTrue((self.tree / 'bench/records').is_dir())
        self.assertTrue((self.tree / 'bench/tlc-baselines').is_dir())
        before = paths(self.tree)
        report = (self.tree / 'docs/performance.md').read_bytes()
        result = run('scripts/bench.py', 'report', cwd=self.tree)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual((self.tree / 'docs/performance.md').read_bytes(), report)
        result = run('scripts/bench.py', 'report', '--check', cwd=self.tree)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertEqual(paths(self.tree), before)

    def test_a_product_tool_still_runs_without_the_harness(self):
        # The other half of "the released tree works": not only do the checks
        # report what is missing, the ordinary entry points still start and
        # print their own interface.
        for argv in (('scripts/coverage.py', '--help'), ('scripts/bench.py', '--help')):
            with self.subTest(argv=argv):
                result = run(*argv, cwd=self.tree)
                self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
                self.assertNotIn('Traceback', result.stdout + result.stderr)


if __name__ == '__main__':
    unittest.main()
