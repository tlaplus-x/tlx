"""Quota backoff stays read-only and never changes the launch offer.

`wait_for_quota` takes an injectable clock/sleep (`RetryClock`), so these tests
drive the full backoff with `testkit.FakeClock` and assert the schedule it
produced instead of waiting for real (2026-10-08)."""
import os
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import Mock, patch

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
import cloud_verify as cv
import testkit
from cloud.cloud_common import CloudStop, Offer


class QuotaWait(unittest.TestCase):
    def test_wait_retries_only_dry_runs_and_logs_without_spending_launch(self):
        offer = Offer(.3, 'same-region', 'same-zone', 'same-type', vcpus=16)
        provider = Mock()
        provider.describe_plan.side_effect = [CloudStop('LimitExceeded.UserSpotQuota', 20),
                                             ['RunInstances DryRun: would succeed']]
        clock = testkit.FakeClock()
        with tempfile.TemporaryDirectory() as directory:
            ledger = cv.LaunchLedger(directory + '/ledger.json')
            args = cv.parse_args(['--provider', 'tencent', '--wait-quota', '10'])
            with patch.object(cv, 'log'):
                cv.wait_for_quota(provider, offer, 'x86_64', args.wait_quota, ledger, 'worker',
                                  monotonic=clock, sleep=clock.sleep)
            self.assertEqual(ledger.recent_launches('worker'), 0)
            with ledger.locked() as rows:
                self.assertEqual(rows[0]['region'], offer.region)
                self.assertEqual(rows[0]['type'], offer.itype)
                self.assertEqual(rows[0]['code'], 20)
        self.assertEqual(sum(clock.sleeps), 360)
        self.assertLessEqual(max(clock.sleeps), 60)
        self.assertEqual(provider.describe_plan.call_count, 2)
        for call in provider.describe_plan.call_args_list:
            self.assertEqual(call.args, (offer, 'x86_64'))
        provider.launch.assert_not_called()

    def test_expiry_and_nonquota_errors_never_launch(self):
        offer = Offer(.3, 'region', 'zone', 'type', vcpus=16)
        for error, minutes in ((CloudStop('LimitExceeded.UserSpotQuota', 20), 1),
                               (CloudStop('risk refusal', 21), 10)):
            provider = Mock()
            provider.describe_plan.side_effect = error
            clock = testkit.FakeClock()
            with tempfile.TemporaryDirectory() as directory, \
                 patch.object(cv, 'log'), self.assertRaises(CloudStop) as raised:
                cv.wait_for_quota(provider, offer, 'x86_64', minutes,
                                  cv.LaunchLedger(directory + '/ledger.json'), 'worker',
                                  monotonic=clock, sleep=clock.sleep)
            self.assertEqual(raised.exception.code, error.code)
            provider.launch.assert_not_called()

    def test_refused_launch_then_one_launch_after_successful_probe(self):
        provider = Mock()
        provider.launch.side_effect = [CloudStop('LimitExceeded.UserSpotQuota', 20), None]
        provider.find_launched.return_value = None
        offer = Offer(.3, 'region', 'zone', 'type', vcpus=16)
        machine = SimpleNamespace(offer=offer)
        args = cv.parse_args(['--provider', 'tencent', '--wait-quota', '10'])
        with tempfile.TemporaryDirectory() as directory:
            ledger = cv.LaunchLedger(directory + '/ledger.json')
            with patch.object(cv, 'wait_for_quota') as waiting:
                cv.launch_with_quota_wait(provider, machine, [], False, args, ledger, 'worker', set())
            waiting.assert_called_once()
            self.assertEqual(provider.launch.call_count, 2)
            self.assertEqual(ledger.recent_launches('worker'), 1)


if __name__ == '__main__':
    unittest.main()
