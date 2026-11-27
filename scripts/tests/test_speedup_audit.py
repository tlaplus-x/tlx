"""The speedup inventory selects and pairs exactly as the report does.

`benchmarking.speedup_audit` exists so a reader can recompute which paired
tlx/TLC ratios the report publishes, with the same `eligible` selection and
`historical_match` pairing. These tests pin that equality: a row the report
would not publish (an expectation mismatch, a diagnostic, an incomplete
repetition, a changed distinct count outside default mode, a different
machine) must not appear in the inventory, and the cold warm-up must be read
from the raw result rather than confused with the timed samples.
"""

import os
from pathlib import Path
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from benchmarking import speedup_audit
from benchmarking.records import normalize


def row(header=None, **changes):
    """One measurement row, built the way the store's normalizer builds it."""
    header = {'commit': 'abc123', 'date': '2026-10-07', 'machine': 'x86_64, tencent SA5.4XLARGE32',
              **(header or {})}
    raw = {'model': 'M', 'mode': '-compile', 'workers': 1, 'walls': [1.0, 1.0, 1.0],
           'cpu': [1.0, 1.0, 1.0], 'result': 'success', 'distinct': 10, 'generated': 20, 'depth': 3,
           'content_digest': 'd' * 64, 'tlc_version': 'v1', 'compatibility': True,
           'cache': {'mode': 'shared-batch', 'initial_state': 'unknown', 'warmup': True},
           'raw_result': {'walls': [1.0, 1.0, 1.0],
                          'warmups': [{'wall_s': 4.0, 'cpu_s': 4.0, 'result': 'success', 'distinct': 10}]}}
    raw.update(changes)
    r = normalize(header, raw, 'bench/history/a.json', '/runs/M')
    r['instance'] = {'type': 'SA5.4XLARGE32', 'arch': 'x86_64', 'description': 'x86_64'}
    r['content_digest'] = raw['content_digest']
    r['tlc_version'] = raw['tlc_version']
    return r


class SpeedupAuditTest(unittest.TestCase):
    def setUp(self):
        self.tlc = row(tool='tlc', mode='-tlc', walls=[300.0], cpu=[1.0])

    def paired(self, tlx):
        tlx = dict(tlx)
        tlx['baseline'] = self.tlc['id']
        return speedup_audit.inventory([tlx, self.tlc], threshold=100.0)

    def test_pairs_and_reports_a_large_ratio(self):
        tlx = row()
        tlx['baseline'] = self.tlc['id']
        cases = self.paired(tlx)
        self.assertEqual(len(cases), 1)
        self.assertAlmostEqual(cases[0]['ratio'], 300.0, places=6)
        self.assertEqual(cases[0]['cold_tlx_s'], 4.0)
        self.assertEqual(cases[0]['tlx']['provenance']['source'], tlx['provenance']['source'])
        self.assertIn('300.00×', speedup_audit.markdown(cases))

    def test_excluded_rows_are_not_claims(self):
        # An expectation mismatch, a diagnostic run and an incomplete repetition
        # all fail `bench_records.eligible`, so the report never publishes them.
        for reason, a_tlx in (
                ('expectation mismatch', row(count_problems=['1 != 2'])),
                ('diagnostic', row(raw_stats={'phases': {'search': 1}})),
                ('incomplete repetition', row({'suite': 's', 'repeat': 3}, walls=[1.0, 1.0]))):
            with self.subTest(reason=reason):
                self.assertEqual(self.paired(a_tlx), [])

    def test_pairing_requires_the_same_machine_and_counts(self):
        other = dict(self.tlc)
        other['instance'] = {**self.tlc['instance'], 'type': 'other'}
        tlx = dict(row(), baseline=self.tlc['id'])
        self.assertEqual(speedup_audit.inventory([tlx, other], threshold=100.0), [])

        # Outside default mode a changed distinct count is not the same
        # measurement, so the report refuses the pairing.
        mismatched = dict(self.tlc)
        mismatched['counts'] = {**self.tlc['counts'], 'distinct': 11}
        tlx = dict(row(), baseline=self.tlc['id'])
        self.assertEqual(speedup_audit.inventory([tlx, mismatched], threshold=100.0), [])

    def test_a_default_mode_row_carries_its_unreduced_twin(self):
        # The audit can now show, next to the TLC ratio, the like-for-like
        # unreduced factor: same model, revision, instance, workers and input.
        reduced = row(mode='default', walls=[2.0])
        reduced['id'] = 'reduced'
        reduced['baseline'] = self.tlc['id']
        twin = row(mode='-tlc', tool='tlx', walls=[12.0])
        twin['id'] = 'twin'
        cases = speedup_audit.inventory([reduced, twin, self.tlc], threshold=2.0)
        self.assertEqual(len(cases), 1)
        reported = cases[0]['unreduced_twin']
        self.assertEqual(reported['id'], twin['id'])
        self.assertAlmostEqual(reported['ratio'], 6.0, places=6)
        self.assertTrue(cases[0]['checks']['unreduced_twin'])
        self.assertTrue(cases[0]['checks']['twin_counts_equal_tlc'])
        text = speedup_audit.markdown(cases)
        self.assertIn('-tlc / default', text)
        self.assertIn('12.000', text)
        self.assertIn('6.00×', text)

    def test_a_twin_on_another_instance_or_configuration_is_not_used(self):
        reduced = row(mode='default', walls=[2.0])
        reduced['id'] = 'reduced'
        reduced['baseline'] = self.tlc['id']
        twin = row(mode='-tlc', tool='tlx', walls=[12.0])
        twin['id'] = 'twin'
        for label, change in (
                ('instance', {'instance': {**twin['instance'], 'type': 'other'}}),
                ('arch', {'instance': {**twin['instance'], 'arch': 'aarch64'}}),
                ('workers', {'workers': 2}),
                ('input', {'content_digest': 'f' * 64}),
                ('unknown instance', {'instance': {**twin['instance'], 'type': None}}),
                ('unknown arch', {'instance': {**twin['instance'], 'arch': None}}),
                ('unknown input', {'content_digest': None}),
                ('cache regime', {'provenance': {**twin['provenance'],
                                                 'cache': {'mode': 'fresh-per-model', 'initial_state': 'empty',
                                                           'warmup': True}}}),
                ('configuration', {'configuration': {**twin['configuration'], 'args': ['-maxmem', '512']}})):
            with self.subTest(change=label):
                cases = speedup_audit.inventory([reduced, {**twin, **change}, self.tlc], threshold=2.0)
                self.assertIsNone(cases[0]['unreduced_twin'])
                self.assertFalse(cases[0]['checks']['unreduced_twin'])
                self.assertNotIn('-tlc / default', speedup_audit.markdown(cases))
        # Outside default mode the row has no twin protocol at all.
        compiled = row(walls=[2.0])
        compiled['baseline'] = self.tlc['id']
        cases = speedup_audit.inventory([compiled, twin, self.tlc], threshold=2.0)
        self.assertIsNone(cases[0]['unreduced_twin'])

    def test_an_unknown_pairing_dimension_on_both_sides_is_not_paired(self):
        def drop_cache(r):
            return {**r, 'provenance': {k: v for k, v in r['provenance'].items() if k != 'cache'}}
        changes = {
            'unknown instance type': lambda r: {**r, 'instance': {**r['instance'], 'type': None}},
            'unknown architecture': lambda r: {**r, 'instance': {**r['instance'], 'arch': None}},
            'unknown input bytes': lambda r: {**r, 'content_digest': None},
            'unknown cache provenance': drop_cache,
        }
        for label, change in changes.items():
            with self.subTest(change=label):
                reduced = row(mode='default', walls=[2.0])
                reduced['id'] = 'reduced'
                reduced['baseline'] = self.tlc['id']
                twin = row(mode='-tlc', tool='tlx', walls=[12.0])
                twin['id'] = 'twin'
                cases = speedup_audit.inventory([change(reduced), change(twin), self.tlc], threshold=2.0)
                # An unknown machine also loses the TLC-baseline pairing, so the
                # case may be absent; it is never present with a twin.
                self.assertTrue(not cases or cases[0]['unreduced_twin'] is None)

    def test_a_newer_twin_on_another_revision_keeps_the_matching_one(self):
        reduced = row(mode='default', walls=[2.0])
        reduced['id'] = 'reduced'
        reduced['baseline'] = self.tlc['id']
        twin = row(mode='-tlc', tool='tlx', walls=[12.0])
        twin['id'] = 'twin'
        newer = row(mode='-tlc', tool='tlx', walls=[20.0])
        newer.update(id='newer', revision='newrev', date='2026-11-01')
        cases = speedup_audit.inventory([reduced, twin, newer, self.tlc], threshold=2.0)
        self.assertEqual(cases[0]['unreduced_twin']['id'], 'twin')
        self.assertAlmostEqual(cases[0]['unreduced_twin']['ratio'], 6.0, places=6)

    def test_threshold_filters_small_ratios(self):
        tlx = dict(row(walls=[100.0, 100.0, 100.0]), baseline=self.tlc['id'])
        self.assertEqual(speedup_audit.inventory([tlx, self.tlc], threshold=100.0), [])
        self.assertEqual(len(speedup_audit.inventory([tlx, self.tlc], threshold=2.0)), 1)

    def test_digest_check_uses_the_resolved_inputs(self):
        cases = self.paired(dict(row(), baseline=self.tlc['id']))
        speedup_audit.add_digest_checks(cases, {'M': {'tla': __file__, 'cfg': __file__}})
        self.assertFalse(cases[0]['digest']['tlx_matches'])
        speedup_audit.add_digest_checks(cases, {})
        self.assertIsNone(cases[0]['digest']['recomputed'])


if __name__ == '__main__':
    unittest.main()
