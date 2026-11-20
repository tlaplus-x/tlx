"""Owner admission and transport recovery regressions, with no cloud requests."""
import contextlib
import io
import json
import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from cloud import cloud_common as common
import cloud_verify as cloud
import testkit


class GrantOwner(testkit.GuardedTestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        subprocess.run(['git', 'init', '-q', str(self.root)], check=True)
        subprocess.run(['git', '-C', str(self.root), 'config', 'user.email', 'fixture@example.com'], check=True)
        subprocess.run(['git', '-C', str(self.root), 'config', 'user.name', 'Fixture'], check=True)
        subprocess.run(['git', '-C', str(self.root), 'commit', '--allow-empty', '-qm', 'Initial'], check=True)
        subprocess.run(['git', '-C', str(self.root), 'branch', 'feature/baseline'], check=True)
        self.ledger = cloud.LaunchLedger(str(self.root / 'ledger.json'))
        # Keep all git lookups in the isolated repository, including CLI run().
        self.patch = mock.patch.object(cloud, 'git', side_effect=lambda *args: subprocess.run(['git', *args], cwd=self.root, check=True, capture_output=True, text=True).stdout.strip())
        self.patch.start()
        self.addCleanup(self.patch.stop)

    def test_worker_short_name_is_refused_with_the_correct_branch(self):
        with self.assertRaises(common.CloudStop) as raised:
            self.ledger.grant('baseline', 'long oracle lane')
        self.assertEqual(raised.exception.code, 25)
        self.assertIn('--grant feature/baseline', str(raised.exception))
        self.assertFalse(Path(self.ledger.path).exists())

    def test_real_branch_and_historical_owner_are_accepted(self):
        self.ledger.grant('feature/baseline', 'oracle lane')
        self.ledger.write([dict(owner='retired-owner', status='released', time=0)])
        self.ledger.grant('retired-owner', 'collect archived results')
        self.assertEqual(json.loads(Path(self.ledger.path).read_text())[-1]['owner'], 'retired-owner')

    def test_known_branch_grant_uses_the_workers_portable_owner_identity(self):
        for branch in ('feature/with+portable-tag', 'feature/' + 'long' * 20):
            with self.subTest(branch=branch):
                subprocess.run(['git', '-C', str(self.root), 'branch', branch], check=True)
                self.ledger.grant(branch, 'oracle lane')
                rows = json.loads(Path(self.ledger.path).read_text())
                self.assertEqual(rows[-1]['owner'], common.owner_tag(branch))
                self.assertIsNotNone(self.ledger.available_grant(rows, common.owner_tag(branch), 60))

    def test_commitish_is_not_an_owner_branch(self):
        for name in ('HEAD', '--help', 'feature/baseline~0', ''):
            with self.subTest(owner=name), self.assertRaises(common.CloudStop):
                self.ledger.grant(name, 'oracle lane')

    def test_cli_run_refuses_before_creating_a_grant(self):
        with mock.patch.object(cloud, 'LaunchLedger', return_value=self.ledger), \
             self.assertRaisesRegex(common.CloudStop, '--grant feature/baseline'):
            cloud.run(cloud.parse_args(['--grant', 'baseline']))

    def test_grant_does_not_require_a_current_branch(self):
        detached = mock.patch.object(
            cloud, 'current_owner', side_effect=common.CloudStop('cloud ownership needs a current git branch', 25))
        with detached, mock.patch.object(cloud, 'LaunchLedger', return_value=self.ledger), \
             contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(cloud.run(cloud.parse_args(['--grant', 'feature/baseline'])), 0)
        rows = json.loads(Path(self.ledger.path).read_text())
        self.assertEqual(rows[-1]['owner'], 'feature/baseline')


class Reconnect(unittest.TestCase):
    def run_case(self, rc, drops, *, seconds=0, dead_at=20000):
        clock = testkit.FakeClock()
        machine = mock.Mock(dead_at=dead_at, env={}, access=None)
        machine.ssh_cmd.return_value = ['ssh', 'fixture']
        machine.ssh.side_effect = [mock.Mock()] + [mock.Mock(returncode=rc, stdout='')] * drops + [mock.Mock(returncode=0, stdout='0\n')]

        def stream(*args, **kwargs):
            def lines():
                clock.advance(seconds)
                yield 'logs: target/verify/fixture\n'
            return mock.Mock(stdout=lines())

        with mock.patch.object(common.subprocess, 'Popen', side_effect=stream), \
             mock.patch.object(common, 'warning'), mock.patch.object(common, 'log'), \
             contextlib.redirect_stdout(io.StringIO()):
            result = common.run_remote_verify(machine, ['true'], now=clock, sleep=clock.sleep)
        return result, clock

    def test_short_stream_drops_cannot_destroy_a_run_that_emitted_results(self):
        result, clock = self.run_case(0, 30, seconds=1)
        self.assertEqual(result, (0, 'target/verify/fixture'))
        self.assertEqual(len(clock.sleeps), 30)

    def test_transport_outage_longer_than_one_hour_survives_until_deadman(self):
        result, clock = self.run_case(255, 750)
        self.assertEqual(result[0], 0)
        self.assertGreater(clock(), 3600)


if __name__ == '__main__':
    unittest.main()
