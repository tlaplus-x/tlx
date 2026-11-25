"""`bench.py history-report` publishes peak-RSS reduction with wall and CPU.

The plain report compares one history file with its TLC runs (or a `tlcbase`
file); the RSS column pairs the same runs' peak resident memory, so a memory
claim names the same statistic and the same cohort as the wall and CPU columns.
"""

import contextlib
import io
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import bench
from benchmarking.commands.history import cmd_history_report
from benchmarking.records import peak_rss


class HistoryReportRSS(unittest.TestCase):
    def tlx_run(self, **changes):
        return {'tier': 'small', 'model': 'M', 'mode': 'compile', 'workers': 1, 'min': 2.0,
                'walls': [2.0], 'cpu': [1.5], 'rss_mib': [100.0], 'result': 'success', **changes}

    def tlc_run(self, **changes):
        return {'tier': 'small', 'model': 'M', 'mode': 'tlc', 'workers': 1, 'min': 8.0,
                'walls': [8.0], 'cpu': [4.0], 'rss_mib': [400.0], 'result': 'success', **changes}

    def report(self, history, baseline='', baseline_rss=400.0, baseline_samples=None):
        args = SimpleNamespace(history='h.json', markdown=False, tlc_baseline=baseline, top=10)
        out = io.StringIO()
        with contextlib.ExitStack() as stack:
            stack.enter_context(patch.object(bench, 'read_json', return_value=history))
            stack.enter_context(patch.object(bench, 'history_path', side_effect=lambda path: path))
            if baseline:
                stack.enter_context(patch.object(bench, 'load_tlc_baseline', return_value=(
                    {}, {('M', 1): {'wall_s': 8.0, 'cpu_s': 4.0, 'maxrss_mib': baseline_rss,
                                    'tlc_samples': baseline_samples, 'result': 'success'}})))
            stack.enter_context(contextlib.redirect_stdout(out))
            cmd_history_report(args)
        return out.getvalue()

    def test_rss_reduction_is_reported_with_wall_and_cpu(self):
        history = {'commit': 'abc', 'date': 'd', 'machine': 'm',
                   'runs': {'M#tlc': self.tlc_run(), 'M#compile': self.tlx_run()}}
        text = self.report(history)
        self.assertIn('rss', text)
        # wall 8/2, CPU 4/1.5, RSS 400/100, as the same geometric-mean column set.
        self.assertRegex(text, r'small\s+compile\s+1\s+1\s+4\.00×\s+2\.67×\s+4\.00×')
        self.assertRegex(text, r'all models\s+compile\s+1\s+1\s+4\.00×\s+2\.67×\s+4\.00×')

    def test_rss_reduction_reads_the_tlcbase_scalar(self):
        history = {'commit': 'abc', 'date': 'd', 'machine': 'm', 'runs': {'M#compile': self.tlx_run()}}
        text = self.report(history, baseline='tlc.json')
        self.assertRegex(text, r'small\s+compile\s+1\s+1\s+4\.00×\s+2\.67×\s+4\.00×')

    def test_legacy_history_falls_back_to_its_timed_samples(self):
        # A history written before `run` kept an aggregate RSS still has the
        # timed samples' own `maxrss_mib`; both sides of 480/120 are present.
        tlx = self.tlx_run()
        del tlx['rss_mib']
        tlx['samples'] = [{'maxrss_mib': 100.0}, {'maxrss_mib': 140.0}]
        history = {'commit': 'abc', 'date': 'd', 'machine': 'm', 'runs': {'M#compile': tlx}}
        text = self.report(history, baseline='tlc.json', baseline_rss=480.0)  # the baseline records 480 MiB
        self.assertRegex(text, r'small\s+compile\s+1\s+1\s+4\.00×\s+2\.67×\s+4\.00×')

    def test_mixed_rss_list_drops_the_unknown_sample(self):
        # [0, 100] is one real 100 MiB measurement, not a 50 MiB median: the
        # store import and history-report have to agree on 400/100 = 4.00×.
        history = {'commit': 'abc', 'date': 'd', 'machine': 'm',
                   'runs': {'M#tlc': self.tlc_run(rss_mib=[400.0]),
                            'M#compile': self.tlx_run(rss_mib=[0, 100.0])}}
        text = self.report(history)
        self.assertRegex(text, r'small\s+compile\s+1\s+1\s+4\.00×\s+2\.67×\s+4\.00×')
        self.assertNotIn('8.00×', text)

    def test_repeated_baseline_prefers_its_retained_samples(self):
        # An existing repeated baseline may carry a stale aggregate (the plain
        # median 200 of [0, 400]) next to the retained timed samples; the 400 MiB
        # real measurement is what the tlx 100 MiB row has to be compared with.
        history = {'commit': 'abc', 'date': 'd', 'machine': 'm', 'runs': {'M#compile': self.tlx_run()}}
        text = self.report(history, baseline='tlc.json', baseline_rss=200.0,
                           baseline_samples=[{'maxrss_mib': 0}, {'maxrss_mib': 400.0}])
        self.assertRegex(text, r'small\s+compile\s+1\s+1\s+4\.00×\s+2\.67×\s+4\.00×')

    def test_missing_rss_stays_unknown_instead_of_a_nan_ratio(self):
        history = {'commit': 'abc', 'date': 'd', 'machine': 'm',
                   'runs': {'M#tlc': self.tlc_run(rss_mib=None), 'M#compile': self.tlx_run(rss_mib=None)}}
        text = self.report(history)
        self.assertRegex(text, r'small\s+compile\s+1\s+1\s+4\.00×\s+2\.67×\s+-')
        self.assertNotIn('nan', text)

    def test_peak_rss_uses_the_store_statistic_and_rejects_non_measurements(self):
        self.assertEqual(peak_rss({'rss_mib': [100.0, 140.0]}), 120.0)
        self.assertEqual(peak_rss({'rss_mib': [0, 100.0]}), 100.0)
        self.assertEqual(peak_rss({'maxrss_mib': 400.0}), 400.0)
        self.assertEqual(peak_rss({'samples': [{'maxrss_mib': 100.0}, {'maxrss_mib': 140.0}]}), 120.0)
        for record in ({}, {'rss_mib': [0, None]}, {'maxrss_mib': 0}, {'rss_mib': []}):
            with self.subTest(record=record):
                self.assertIsNone(peak_rss(record))


if __name__ == '__main__':
    unittest.main()
