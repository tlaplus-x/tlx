"""Canonical benchmark records, conservative migration, cache and report gates."""

import ast
from benchmarking import baselines, legacy, machine as bench_machine, records as store
from benchmarking.baselines import (cached_tlc, content_digest, find_baseline, historical_match,
                                    raw_baseline, seed_baselines)
from benchmarking.legacy import adopt_legacy, ingest, legacy_rows, measurement_rows, migrate
from benchmarking.records import (dump, load_records, normalize, receipt_revisions,
                                  store_lock, validate, write_records)
import copy
import contextlib
import io
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import Mock, patch

from benchmarking import bench_records as br


class RecordsTest(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / 'bench').mkdir()
        (self.root / 'docs').mkdir()
        self.model = {'id': 'M', 'tla': str(self.root / 'M.tla'), 'cfg': str(self.root / 'M.cfg')}
        Path(self.model['tla']).write_text('---- MODULE M ----\n====\n')
        Path(self.model['cfg']).write_text('INIT Init\n')

    def record(self, **changes):
        h = {'commit': 'abc123', 'date': '2026-10-07', 'machine': 'x86_64, tencent SA5.4XLARGE32'}
        r = normalize(h, {'model': 'M', 'mode': 'compile', 'workers': 1, 'walls': [2, 4, 3],
                          'cpu': [1, 2, 3], 'result': 'success', 'distinct': 10}, 'bench/history/a.json', '/runs/M')
        r.update(changes)
        return r

    def test_diagnostic_samples_are_retained_without_becoming_headlines(self):
        header = {'commit': 'abc123', 'machine': 'x86_64 SA5.4XLARGE32'}
        sample = {'model': 'M', 'args': ['-compile'], 'result': 'success',
                  'wall_s': 1, 'cpu_s': 1, 'distinct': 1}
        ordinary = normalize(header, sample, 'bench/profile.json', '/models/M')
        self.assertTrue(br.eligible(ordinary))
        cases = [({**header, 'diagnostic': True}, sample),
                 ({**header, 'kind': 'profile'}, sample),
                 (header, {**sample, 'raw_stats': {'phases': {'search': 1}}}),
                 (header, {**sample, 'args': ['-compile', '-stats']})]
        for h, raw in cases:
            with self.subTest(header=h, sample=raw):
                record = normalize(h, raw, 'bench/profile.json', '/models/M')
                validate(record)
                self.assertEqual(record['metrics']['cpu_s'], 1)
                self.assertIn('diagnostic', record['category'])
                self.assertFalse(br.eligible(record))

    def test_schema_version_and_required_metrics(self):
        r = self.record()
        validate(r)
        self.assertEqual(r['metrics']['wall_s'], 3)
        self.assertEqual(r['metrics']['cpu_s'], 2)
        self.assertIsNone(r['metrics']['instructions'])
        self.assertEqual(r['instance']['type'], 'SA5.4XLARGE32')
        for change in ({'schema_version': store.VERSION + 1}, {'schema_version': 1}, {'mode': 'magic'},
                       {'workers': 0}, {'model': ''}):
            with self.subTest(change=change), self.assertRaises(ValueError):
                validate({**r, **change})
        r['metrics']['wall_s'] = -1
        with self.assertRaises(ValueError):
            validate(r)

    def test_peak_rss_skips_unknown_samples_and_legacy_spellings(self):
        # One reader for the store import, the report and history-report: a
        # zero sample is unknown, so it is dropped instead of averaging into a
        # real measurement, and the legacy spellings stay readable.
        header = {'commit': 'abc123', 'date': '2026-10-07', 'machine': 'x86_64, tencent SA5.4XLARGE32'}
        raw = {'model': 'M', 'mode': 'compile', 'workers': 1, 'walls': [1.0, 2.0],
               'cpu': [1.0, 2.0], 'result': 'success', 'distinct': 10, 'rss_mib': [0, 100]}
        r = normalize(header, raw, 'bench/history/a.json', '/runs/M')
        self.assertEqual(r['metrics']['rss_mib'], 100)
        self.assertEqual(store.peak_rss({'rss_mib': [100.0, 140.0]}), 120.0)
        self.assertEqual(store.peak_rss({'rss_mib': [0, 100.0]}), 100.0)
        self.assertEqual(store.peak_rss({'maxrss_mib': 400.0}), 400.0)
        self.assertEqual(store.peak_rss({'samples': [{'maxrss_mib': 100.0}, {'maxrss_mib': 140.0}]}), 120.0)
        # Retained repeated-baseline samples outrank a stored aggregate that
        # could have been computed with an unknown sample.
        self.assertEqual(store.peak_rss({'maxrss_mib': 200.0,
                                         'tlc_samples': [{'maxrss_mib': 0}, {'maxrss_mib': 400.0}]}), 400.0)
        self.assertIsNone(store.peak_rss({'rss_mib': [0, None]}))
        self.assertIsNone(store.peak_rss({'rss': 0}))

    def test_disk_telemetry_is_not_read_as_peak_rss(self):
        # The disk lane reuses `samples` for telemetry vectors: elapsed time,
        # instantaneous RSS, I/O and disk byte counts, state count, cgroup MiB.
        # Only named RSS fields under samples are measurements, so a run whose
        # wait4 usage was lost stays unknown instead of publishing the number
        # that happens to sit in the read-byte column.
        header = {'machine': 'x86_64, tencent SA5.4XLARGE32'}
        raw = {'model': 'M', 'mode': 'compile', 'workers': 1, 'walls': [1.0], 'cpu': [1.0],
               'result': 'bench-error', 'distinct': 10,
               'samples': [[1, 64, 4096, 1048576, 2097152, 40000, 128],
                           [2, 72, 8192, 2097152, 4194304, 50000, 256]]}
        self.assertIsNone(normalize(header, raw, 'bench/disk/a.json', '/runs/M')['metrics']['rss_mib'])
        self.assertIsNone(store.peak_rss(raw))
        raw['samples'] = [{'maxrss_mib': 100.0}, {'maxrss_mib': 140.0}]
        self.assertEqual(store.peak_rss(raw), 120.0)

    def test_explicit_default_semantics_survive_normalization_and_match_tlc_time(self):
        header = {'machine': 'x86_64 SA5.4XLARGE32'}
        raw = {'model': 'M', 'mode': 'compile', 'workers': 1, 'result': 'success',
               'distinct': 2, 'wall_s': 1, 'compatibility': False}
        new = normalize(header, raw, 'bench/history/a.json', '/runs/M')
        tlc = normalize(header, {**raw, 'distinct': 100, 'tool': 'tlc', 'compatibility': True},
                        'bench/history/tlc.json', '/runs/M')
        self.assertIs(new['configuration']['compatibility'], False)
        self.assertTrue(historical_match(new, tlc))
        new['configuration']['compatibility'] = True
        self.assertFalse(historical_match(new, tlc))

    def test_expectation_mismatch_rejects_baseline_reuse_and_pairing(self):
        tx = self.record(content_digest='input', tlc_version='tlc-version')
        tc = self.record(tool='tlc', mode='-tlc', revision=None, id='baseline',
                         content_digest='input', tlc_version='tlc-version')
        entry = {'key': store.measurement_key(tc), 'measurement': tc}
        for verdict in ('success', 'safety failure', 'deadlock'):
            tx['counts']['result'] = tc['counts']['result'] = verdict
            for row in (tx, tc):
                row['provenance']['count_problems'] = []
            self.assertTrue(baselines.reusable(entry))
            self.assertTrue(historical_match(tx, tc))
            for rejected in (tx, tc):
                with self.subTest(verdict=verdict, rejected=rejected['tool']):
                    baselines.attach_baselines([tx, tc])
                    self.assertEqual(tx['baseline'], tc['id'])
                    rejected['provenance']['count_problems'] = ['result differs from expectation']
                    self.assertFalse(historical_match(tx, tc))
                    self.assertEqual(baselines.reusable(entry), rejected is tx)
                    baselines.attach_baselines([tx, tc])
                    self.assertIsNone(tx['baseline'])
                    report = br.render([tx, tc], {'models': []}, baseline_inputs={
                        'M': {'content_digest': 'input', 'tlc_version': 'tlc-version'}})
                    self.assertIn('No eligible records with a matching TLC baseline.', report)
                    if rejected is tc:
                        self.assertIn('missing/stale baseline key', report)
                    rejected['provenance']['count_problems'] = []

    def test_migration_shapes_and_idempotence(self):
        h = {'commit': 'abc', 'date': '2026-10-07', 'machine': 'x86_64', 'runs': {
            'small:M:compile:1w': {'model': 'M', 'mode': 'compile', 'workers': 1, 'walls': [2], 'result': 'success'},
            'M#base': [{'wall': 3, 'cpu': 2, 'result': 'success'}]}}
        p = self.root / 'bench' / 'old.json'
        p.write_text(json.dumps(h))
        a = migrate(self.root)
        b = migrate(self.root)
        self.assertEqual(a, b)
        self.assertEqual(len(a), 2)
        base = next(r for r in a if r['provenance']['pointer'].endswith('base'))
        self.assertIsNone(base['revision'])  # header commit belongs to new binary, not base
        self.assertIsNone(base['content_digest'])

    def test_ab_rows_keep_sample_exits_and_unknown_stays_unknown(self):
        # HARNESS-19/-21: normalization must read the A/B producer's per-sample
        # evidence, so a sample its raw guard rejected (a missing or
        # verdict-mismatched child exit, or an incompletely repeated set) is not
        # adopted into a canonical comparison; a source that records no exit at
        # all is unknown, never refuted by absence.
        def row(runs, summary=None, variant='new'):
            h = {'commit': 'abc123', 'date': '2026-10-07', 'machine': 'x86_64 SA5.4XLARGE32',
                 'bins': {'base': '/base', 'new': '/new'}, 'args': ['-compile', '-workers', '1'],
                 'runs': {f'M#{variant}': runs}}
            if summary is not None:
                h['summary'] = {f'M#{variant}': summary}
            raw, pointer, kw = next(iter(legacy_rows(h)))
            r = normalize(h, raw, 'bench/ab/x.json', pointer, **kw)
            r['revision'] = 'abc123'  # provenance is separate; isolate the exit gate here
            return r
        sample = dict(result='success', distinct=10, wall=1, cpu=1, rss=1)
        complete = {'complete': True, 'completed_samples': 3}
        self.assertTrue(br.eligible(row([{**sample, 'exit': 0}] * 3, complete)))
        self.assertFalse(br.eligible(row([{**sample, 'exit': 101}] * 3, complete)))
        self.assertFalse(br.eligible(row([sample] * 3, complete)))
        self.assertFalse(br.eligible(row([{**sample, 'exit': 0}] * 2 + [sample],
                                        {'complete': False, 'completed_samples': 2})))
        legacy = row([sample] * 3)  # no exit recorded, no completeness verdict
        self.assertTrue(br.eligible(legacy))
        self.assertNotIn('sample_results', legacy['provenance'])

    def test_ab_revision_is_stated_never_inferred_from_the_label(self):
        # HARNESS-19: an external binary's revision is adopted only when the
        # artifact states it. A variant label ("new", "after", "fix") and the
        # runner checkout's own commit say nothing about the executable that was
        # measured, so a labelled row without a stated revision stays unknown.
        sample = dict(result='success', distinct=10, wall=1, cpu=1, rss=1, exit=0)

        def norm(header, variant='new'):
            h = {'commit': 'checkout-commit', 'date': '2026-10-07', 'machine': 'x86_64',
                 'bins': {'base': '/base', 'new': '/new'}, 'args': ['-compile'],
                 'runs': {f'M#{variant}': [sample] * 3},
                 'summary': {f'M#{variant}': {'complete': True, 'completed_samples': 3}}, **header}
            raw, pointer, kw = next(iter(legacy_rows(h)))
            return normalize(h, raw, 'bench/ab/x.json', pointer, **kw)

        for variant in ('new', 'after', 'fix'):
            with self.subTest(variant=variant):
                titled = norm({}, variant)
                self.assertIsNone(titled['revision'])
                self.assertNotIn('revision_source', titled['provenance'])
        stated = norm({'bin_revs': {'new': 'deadbeef'}})
        self.assertEqual(stated['revision'], 'deadbeef')
        self.assertEqual(stated['provenance']['revision_source'], 'artifact')
        self.assertEqual(norm({'bin_revs': {'new': 'deadbeef'}, 'bin_revs_receipt': 'host-1'})['provenance']['revision_source'],
                         'cloud receipt host-1')
        legacy = norm({'new': 'legacysha'})  # a pre-bin_revs artifact keyed by the variant
        self.assertEqual(legacy['revision'], 'legacysha')
        self.assertEqual(legacy['provenance']['revision_source'], 'artifact')

    def test_cloud_receipt_supplies_an_external_binary_revision(self):
        # HARNESS-19: a launch receipt pins what it fetched (`bench_bins`), and
        # the artifact's `--bin LABEL=.../bench-bins/<name>/...` names that
        # binary; LABEL adopts <name>'s revision and names the receipt as the
        # source. A revision no receipt pins is never invented.
        sample = dict(result='success', distinct=10, wall=1, cpu=1, rss=1, exit=0)
        receipt = {'bench_bins': [{'name': 'new', 'rev': 'deadbeef', 'features': ''}],
                   'bench': ['ab --bin base=target/release/tlx --bin new=target/bench-bins/new/tlx '
                             '--models M --out bench/ab/x.json']}
        header = {'commit': 'checkout-commit', 'date': '2026-10-07', 'machine': 'x86_64',
                  'bins': {'base': '/base', 'new': '/new'}, 'args': ['-compile'],
                  'runs': {'M#new': [sample] * 3},
                  'summary': {'M#new': {'complete': True, 'completed_samples': 3}}}

        def build(root):
            (root / 'bench/ab').mkdir(parents=True)
            (root / 'target/bench/2026-10-07-host').mkdir(parents=True)
            (root / 'target/bench/2026-10-07-host/cloud.json').write_text(json.dumps(receipt))
            source = root / 'bench/ab/x.json'
            source.write_text(json.dumps(header))
            return source

        build(self.root)
        self.assertEqual(receipt_revisions(self.root),
                         {'bench/ab/x.json': ('2026-10-07-host', {'new': 'deadbeef'})})
        migrated = [r for r in migrate(self.root) if r['configuration']['variant'] == 'new']
        self.assertEqual(migrated[0]['revision'], 'deadbeef')
        self.assertEqual(migrated[0]['provenance']['revision_source'], 'cloud receipt 2026-10-07-host')
        # The producer path (ingest) shares the recovery, on a root of its own.
        other = Path(self.tmp.name) / 'ingest-root'
        other.mkdir()
        ingested, = ingest(build(other), other)
        self.assertEqual(ingested['revision'], 'deadbeef')
        self.assertEqual(ingested['provenance']['revision_source'], 'cloud receipt 2026-10-07-host')

    def test_disk_command_limits_survive_normalization(self):
        h = {'commit': 'abc', 'workers': 16, 'args': '--fractions 0.25,0.5'}
        raw = {'wall_s': 3, 'result': 'success', 'cmd': '/model.tla -compile -workers 16 -maxmem 856M -metadir /tmp/unique', 'cgroup_mib': 1713}
        r = normalize(h, raw, 'bench/history/disk.json', '/models/M/runs/new', model='M', mode='-compile')
        self.assertEqual(r['configuration']['args'][-2:], ['-maxmem', '856M'])
        self.assertEqual(r['configuration']['cgroup_mib'], 1713)
        self.assertNotIn('/tmp/unique', r['configuration']['args'])
        tc = normalize(h, {'wall_s': 9, 'cmd': '-Xmx479m -XX:MaxDirectMemorySize=239m -workers 16'},
                          'bench/history/disk.json', '/models/M/runs/TLC', model='M', mode='-tlc')
        self.assertIn('-Xmx479m', tc['configuration']['args'])
        self.assertIn('-XX:MaxDirectMemorySize=239m', tc['configuration']['args'])

    def test_corpus_series_migration_and_unknown_layout_refusal(self):
        h = {'machine': 'SA5.4XLARGE32', 'series': {
            'abcdef0 corpus-compile-w8 TLX_SPILL=always': {'M': [2, 4, 3]}}}
        (self.root / 'bench/old.json').write_text(json.dumps(h))
        r, = migrate(self.root)
        self.assertEqual((r['revision'], r['workers'], r['mode']), ('abcdef0', 8, '-compile'))
        self.assertEqual(r['metrics']['wall_s'], 3)
        self.assertEqual(r['configuration']['env'], {'TLX_SPILL': 'always'})
        self.assertIsNone(r['counts']['result'])
        (self.root / 'bench/unknown.json').write_text(json.dumps({'results': [{'wall': 2}]}))
        with self.assertRaisesRegex(ValueError, 'unrecognized benchmark layout'):
            migrate(self.root)

    def test_full_stats_diagnostics_do_not_become_timing_samples(self):
        stats = {'sample_every': 8, 'phases': {'search': 2}, 'counters': {'units': 10},
                 'time_est_s': {}, 'actions': []}
        (self.root / 'bench/full.stats.json').write_text(json.dumps(stats))
        self.assertEqual(migrate(self.root), [])
        with self.assertRaisesRegex(ValueError, 'unrecognized benchmark layout'):
            list(measurement_rows({'phases': {'search': 2}}))

    def test_partial_suite_samples_are_retained_but_excluded_from_headlines(self):
        h = {'suite': True, 'repeat': 3, 'commit': 'abc123', 'runs': {
            'M': {'model': 'M', 'mode': 'compile', 'workers': 1, 'walls': [2, 3],
                  'result': 'success', 'content_digest': 'verified-input'}}}
        path = self.root / 'bench/partial.json'
        path.write_text(json.dumps(h))
        r, = migrate(self.root)
        self.assertEqual(r['samples']['wall_s'], [2, 3])
        self.assertEqual(r['counts']['result'], 'success')
        self.assertFalse(br.eligible(r))
        self.assertEqual(r['provenance']['repetitions'], {'requested': 3, 'completed': 2})
        # Refresh completeness even when preserving an existing verified identity.
        del r['provenance']['repetitions']
        write_records([r], self.root)
        r, = migrate(self.root)
        self.assertFalse(br.eligible(r))
        h['runs']['M']['walls'].append(4)
        path.write_text(json.dumps(h))
        r, = migrate(self.root)
        self.assertTrue(br.eligible(r))

    def test_suite_expectation_failures_survive_ingest_migration_and_render(self):
        from benchmarking import bench_suite
        entry = {'size': 'large', 'model': 'ext/ccf/MCccfraft_1C3N',
                 'mode': 'compile', 'workers': 1, 'expect': {'result': 'success', 'distinct': 10}}
        good = {'result': 'success', 'distinct': 10, 'wall_s': 12, 'cpu_s': 12}
        bad = {**good, 'result': 'safety failure', 'violated': 'TypeInv', 'wall_s': 0.2}
        cases = (([bad], []), ([bad, good], []), ([good], [bad]),
                 ([{**good, 'distinct': 9}], []))
        source = self.root / 'bench/checked.json'
        for samples, warmups in cases:
            with self.subTest(samples=samples, warmups=warmups):
                raw = bench_suite.record_of(entry, samples, {}, warmups=warmups)
                self.assertTrue(raw['count_problems'])
                raw['content_digest'] = 'verified-input'
                h = {'suite': True, 'repeat': len(samples), 'commit': 'abc123',
                     'machine': 'x86_64 SA5.4XLARGE32', 'runs': {'M': raw}}
                source.write_text(json.dumps(h))
                r, = ingest(source, self.root)
                stored, = load_records(self.root)
                self.assertEqual(stored['provenance']['count_problems'], raw['count_problems'])
                self.assertEqual(stored['counts']['result'], samples[-1]['result'])
                self.assertEqual(stored['samples']['wall_s'], raw['walls'])
                self.assertFalse(br.eligible(stored))
                self.assertEqual(store.evidence(stored)[0], 0)
                report = br.render([stored], {'models': [{'id': entry['model']}]})
                self.assertIn('excluded expectation mismatches: 1', report)
                self.assertIn(br.store_file(stored), report)
                self.assertNotIn('| ' + entry['model'], report.split('## Coverage and gaps')[0])
                # Replay repairs a canonical row written by the old normalizer,
                # even when migration preserves its verified input identity.
                del r['provenance']['count_problems']
                write_records([r], self.root)
                (self.root / 'bench/suite.json').write_text(json.dumps({'models': []}))
                (self.root / 'bench/report-policy.json').write_text(
                    json.dumps({'stale_after_revisions': 20, 'ages': {}}))
                (self.root / 'docs/performance.md').write_text(br.render([r], {'models': []}, ages={}))
                self.assertTrue(any('expectation diagnostics differ' in p for p in br.check(self.root)))
                repaired, = migrate(self.root)
                self.assertEqual(repaired['provenance']['count_problems'], raw['count_problems'])
                self.assertFalse(br.eligible(repaired))
                # An explicit successful recheck can clear that diagnosis.
                h['runs']['M']['count_problems'] = []
                source.write_text(json.dumps(h))
                write_records([repaired], self.root)
                repaired, = migrate(self.root)
                self.assertEqual(repaired['provenance']['count_problems'], [])
                self.assertTrue(br.eligible(repaired))

    def test_expected_complete_verdicts_and_legacy_rows_remain_eligible(self):
        from benchmarking import bench_suite
        for verdict in ('success', 'safety failure', 'deadlock'):
            entry = {'size': 'small', 'model': 'M', 'mode': 'compile',
                     'workers': 1, 'expect': {'result': verdict}}
            raw = bench_suite.record_of(entry, [{'result': verdict, 'wall_s': 1}], {})
            self.assertEqual(raw['count_problems'], [])
            r = normalize({'commit': 'abc'}, raw, 'bench/checked.json', '/runs/M')
            self.assertTrue(br.eligible(r))
            self.assertEqual(store.evidence(r)[0], 2)
            del raw['count_problems']
            r = normalize({'commit': 'abc'}, raw, 'bench/old.json', '/runs/M')
            self.assertNotIn('count_problems', r['provenance'])
            self.assertTrue(br.eligible(r))

    def test_expectation_diagnostics_are_validated_and_cannot_replace_good_evidence(self):
        good = self.record()
        bad = copy.deepcopy(good)
        bad['id'] = 'rejected'
        bad['date'] = '2099-01-01'
        bad['provenance']['count_problems'] = ['result: safety failure != success']
        self.assertEqual(store.record_of_record([bad, good]), good)
        for malformed in (None, 'mismatch', [1], ['']):
            with self.subTest(value=malformed), self.assertRaisesRegex(ValueError, 'count_problems'):
                bad['provenance']['count_problems'] = malformed
                validate(bad)

    def test_embedded_raw_diagnostics_cannot_be_cleared_when_archiving_history(self):
        row = self.record()
        problems = ['result: safety failure != success']
        row['raw_result'] = {'count_problems': problems}
        row['provenance']['count_problems'] = list(problems)
        validate(row)
        row['provenance']['count_problems'] = []
        with self.assertRaisesRegex(ValueError, 'diagnostics disagree'):
            validate(row)

    def test_adaptive_default_cold_and_warm_records(self):
        h = {'commit': 'new-revision', 'machine': 'x86_64 SA5.4XLARGE32', 'date': 'today',
             'models': {'M': {'tlc': {'wall_s': 10, 'source': 'baseline'},
                              'bins': {'new': {'cold': {'wall_s': 2}, 'warm': {'wall_s': 1}},
                                       'old': {'cold': {'wall_s': 3}}}}}}
        rows = [normalize(h, r, 'bench/history/ttfr.json', ptr, **kw)
                for r, ptr, kw in legacy_rows(h)]
        self.assertEqual(len(rows), 4)
        tc = next(r for r in rows if r['tool'] == 'tlc')
        self.assertIsNone(tc['revision'])
        self.assertIsNone(tc['date'])
        cold = next(r for r in rows if r['configuration']['variant'] == 'new')
        self.assertEqual((cold['revision'], cold['mode']), ('new-revision', 'default'))
        self.assertIsNone(next(r for r in rows if r['configuration']['variant'] == 'old-cold')['revision'])
        self.assertEqual(next(r for r in rows if r['configuration']['variant'] == 'new-warm')['aggregation'], 'minimum')

    def test_seed_preserves_adopted_provenance_label(self):
        # The store carries no separate provenance status: a row's label is
        # derived from the measurement itself, so an adopted row keeps its
        # `provenance.adoption` through seeding, filed under its derived key,
        # and re-seeding a reusable row does not rewrite it.
        r = self.record(tool='tlc', mode='-tlc', content_digest='digest', tlc_version='version')
        r['provenance']['adoption'] = {'method': 'exact oracle match'}
        seed_baselines([r], self.root)
        path = next((self.root / 'bench/tlc-baselines').glob('*.json'))
        stored = json.loads(path.read_text())
        self.assertEqual(stored['measurement']['provenance']['adoption'], {'method': 'exact oracle match'})
        self.assertEqual(stored['key'], store.measurement_key(r))
        self.assertEqual(baselines.seeded_store([r], self.root)[path], stored)
        seed_baselines([r], self.root)
        self.assertEqual(json.loads(path.read_text()), stored)

    def test_store_replaces_a_non_reusable_row_with_a_reusable_one(self):
        # The key pins model digest/TLC version/workers/instance, so a timeout
        # (or error/skipped) row is not a measurement: a reusable one for the
        # same key must supersede it, or `find_baseline` reports the key missing
        # forever (the store is otherwise first-write-wins).
        stale = self.record(tool='tlc', mode='-tlc', content_digest='digest', tlc_version='version',
                            counts={'generated': None, 'distinct': None, 'depth': None, 'result': 'timeout'})
        stale['metrics']['wall_s'] = 1800.0
        fresh = self.record(tool='tlc', mode='-tlc', content_digest='digest', tlc_version='version')
        seed_baselines([stale], self.root)
        path = next((self.root / 'bench/tlc-baselines').glob('*.json'))
        self.assertFalse(baselines.reusable(json.loads(path.read_text())))
        seed_baselines([fresh], self.root)
        stored = json.loads(path.read_text())
        self.assertTrue(baselines.reusable(stored))
        self.assertEqual(stored['measurement']['counts']['result'], 'success')
        self.assertEqual(stored['measurement']['metrics']['wall_s'], 3)
        # A reusable row stays immutable: another reusable row does not replace it.
        other = copy.deepcopy(fresh)
        other['id'] = 'another'
        other['metrics']['wall_s'] = 1.0
        seed_baselines([other], self.root)
        self.assertEqual(json.loads(path.read_text())['measurement']['metrics']['wall_s'], 3)

    def test_store_keeps_the_stronger_unreusable_row(self):
        # An unreusable row is the record of why the key has no measurement, so
        # the store keeps the strongest record for it: a timeout measured at a
        # longer bound outranks a shorter one (a later re-run at the default
        # bound must not hide how long TLC really needed), and otherwise the
        # newer record is the current evidence.
        def timeout(bound, date, ident=None):
            r = self.record(tool='tlc', mode='-tlc', content_digest='digest', tlc_version='version', date=date,
                            counts={'generated': None, 'distinct': None, 'depth': None, 'result': 'timeout'})
            r['metrics']['wall_s'] = bound
            if ident:
                r['id'] = ident
            return r

        seed_baselines([timeout(1800.0, '2026-10-08 17:44:27', 'short')], self.root)
        path = next((self.root / 'bench/tlc-baselines').glob('*.json'))
        seed_baselines([timeout(14400.0, '2026-10-09 07:50:21', 'long')], self.root)
        self.assertEqual(json.loads(path.read_text())['measurement']['id'], 'long')
        # A re-run at the default bound states less: it does not replace it.
        seed_baselines([timeout(1800.0, '2026-10-10 09:00:00', 'rerun')], self.root)
        self.assertEqual(json.loads(path.read_text())['measurement']['id'], 'long')
        # Among equally long timeouts the newer date is the current evidence.
        seed_baselines([timeout(14400.0, '2026-10-10 11:00:00', 'newer')], self.root)
        self.assertEqual(json.loads(path.read_text())['measurement']['id'], 'newer')
        # An error row proves only that the run failed at once, so it never
        # outranks a timeout that burned its bound.
        failed = self.record(tool='tlc', mode='-tlc', content_digest='digest', tlc_version='version',
                             date='2026-10-11 09:00:00',
                             counts={'generated': None, 'distinct': None, 'depth': None, 'result': 'error'})
        seed_baselines([failed], self.root)
        self.assertEqual(json.loads(path.read_text())['measurement']['id'], 'newer')
        # Between two errors of the same key the newer record wins.
        older = self.record(tool='tlc', mode='-tlc', content_digest='digest2', tlc_version='version',
                            date='2026-10-11 09:00:00',
                            counts={'generated': None, 'distinct': None, 'depth': None, 'result': 'error'})
        older['id'] = 'older-error'
        newer_error = copy.deepcopy(older)
        newer_error['id'] = 'newer-error'
        newer_error['date'] = '2026-10-12 09:00:00'
        seed_baselines([older, newer_error], self.root)
        rows = [json.loads(f.read_text()) for f in (self.root / 'bench/tlc-baselines').glob('*.json')]
        other = next(r for r in rows if r['key']['content_digest'] == 'digest2')
        self.assertEqual(other['measurement']['id'], 'newer-error')

    def test_two_revisions_and_two_configurations_coexist_in_the_store(self):
        # The store's identity is the key, not the model or the source: a
        # re-measurement of one configuration at another commit, and a
        # measurement of another configuration at the same commit, are different
        # keys. Each keeps its own file, all of them stay retrievable, and none
        # is read as a supersession of another.
        first = self.record(revision='commit-a')
        first['id'] = 'commit-a'
        second = self.record(revision='commit-b')
        second['id'] = 'commit-b'
        other = copy.deepcopy(first)
        other['id'] = 'other-config'
        other['mode'] = '-tlc'
        write_records([first, second, other], self.root)
        loaded = {r['id']: r for r in load_records(self.root)}
        self.assertEqual(set(loaded), {'commit-a', 'commit-b', 'other-config'})
        paths = {r['id']: store.record_path(r) for r in loaded.values()}
        self.assertEqual(len(set(paths.values())), 3)
        for path in paths.values():
            self.assertTrue((self.root / path).is_file(), path)
        keys = {store.key_id(store.measurement_key(r)) for r in loaded.values()}
        self.assertEqual(len(keys), 3)
        self.assertEqual(store.measurement_key(loaded['commit-a'])['revision'], 'commit-a')

    def test_coverage_attributes_are_validated_and_null_is_absence(self):
        # A coverage census lives in the row it describes: its attributes pass
        # `validate`, an unknown field is refused, and an attribute that is
        # present but null is refused too - absent means "carried no census",
        # and null would be indistinguishable from "measured as nothing". A
        # metric present with value null is still the schema's "unmeasured".
        r = self.record()
        r.update({'native_share': 0.5, 'host_time_share': 0.25, 'host_s': 1.0,
                  'host_calls': 10, 'evaluations': 100, 'coverage': {'ops': [{'op': 'a', 'n': 1}]}})
        validate(r)
        self.assertEqual(r['native_share'], 0.5)
        r['metrics']['instructions'] = None
        validate(r)
        with self.assertRaises(ValueError):
            validate({**r, 'surprise': 1})
        for field in ('native_share', 'host_time_share', 'host_s', 'host_calls', 'evaluations'):
            with self.subTest(field=field), self.assertRaises(ValueError):
                validate({**r, field: None})

    def test_incompletely_keyed_rows_keep_their_own_identity(self):
        # A row whose key is not fully determined - a historical TLC row with no
        # recorded input digest or TLC version - cannot be filed under a key, so
        # it keeps its own `legacy-<id>` file. Two such rows from different
        # sources must not collapse into one, or the only record of one of them
        # is lost.
        def legacy(source):
            return normalize({'machine': 'x86_64 SA5.4XLARGE32', 'commit': 'abc'},
                             {'model': 'M', 'tool': 'tlc', 'mode': '-tlc', 'workers': 1, 'wall_s': 2,
                              'result': 'success'}, source, '/runs/M')
        a, b = legacy('bench/history/a.json'), legacy('bench/history/b.json')
        self.assertIsNone(store.key_id(store.measurement_key(a)))
        self.assertTrue(store.store_stem(a).startswith('legacy-'))
        self.assertNotEqual(store.store_stem(a), store.store_stem(b))
        write_records([a, b], self.root)
        self.assertEqual(len(store.store_files(self.root)), 2)
        self.assertEqual({r['id'] for r in load_records(self.root)}, {a['id'], b['id']})

    def test_load_records_refuses_a_file_that_drifts_from_its_key(self):
        # The store's identity is the key and the file name is that key's digest:
        # a file whose envelope key disagrees with its measurement, or whose name
        # does not identify it, is not readable under the contract the store
        # claims.
        r = self.record()
        write_records([r], self.root)
        path = self.root / store.record_path(r)
        entry = json.loads(path.read_text())
        path.write_text(json.dumps({**entry, 'key': {**entry['key'], 'revision': 'other'}}))
        with self.assertRaisesRegex(ValueError, 'differs from its measurement'):
            load_records(self.root)
        path.write_text(json.dumps(entry))
        renamed = path.with_name('wrong-name.json')
        renamed.write_text(json.dumps(entry))
        path.unlink()
        with self.assertRaisesRegex(ValueError, 'does not identify its key'):
            load_records(self.root)

    def test_layout_files_each_tool_in_its_own_container(self):
        # Two containers, one envelope: a TLC baseline is filed under
        # bench/tlc-baselines and a tlx row under bench/records, each holding
        # exactly {schema_version, key, measurement}, and `load_records` reads
        # both back.
        tlc = self.record(tool='tlc', mode='-tlc', content_digest='digest', tlc_version='version')
        tlc['id'] = 'tlc-row'
        tlx = self.record()
        tlx['id'] = 'tlx-row'
        write_records([tlc, tlx], self.root)
        tlc_path = self.root / store.record_path(tlc)
        tlx_path = self.root / store.record_path(tlx)
        self.assertEqual(tlc_path.relative_to(self.root).as_posix(),
                         f'bench/tlc-baselines/{store.store_stem(tlc)}.json')
        self.assertEqual(tlx_path.relative_to(self.root).as_posix(),
                         f'bench/records/{store.store_stem(tlx)}.json')
        for path in (tlc_path, tlx_path):
            self.assertTrue(path.is_file(), path)
            self.assertEqual(tuple(sorted(json.loads(path.read_text()))), ('key', 'measurement', 'schema_version'))
        self.assertEqual({r['id'] for r in load_records(self.root)}, {'tlc-row', 'tlx-row'})

    def test_repeated_tlc_baseline_roundtrip_and_immutable_reuse(self):
        samples = [dict(result='success', exit=0, distinct=10, wall_s=w, cpu_s=c)
                   for w, c in [(9, 8), (3, 2), (6, 5)]]
        collect = Mock(side_effect=samples)
        kw = dict(root=self.root, version='v', instance='i', repetitions=3)
        raw = cached_tlc(self.model, 1, collect, **kw)
        self.assertEqual((raw['wall_s'], raw['cpu_s']), (6, 5))
        self.assertEqual(raw['tlc_samples'], samples)
        row = load_records(self.root)[0]
        self.assertEqual(row['samples'], {'wall_s': [9, 3, 6], 'cpu_s': [8, 2, 5]})
        self.assertEqual(row['aggregation'], 'median')
        self.assertEqual(row['provenance']['sample_spread'], {'wall_s': 1, 'cpu_s': 1.2})
        before = {p: p.read_bytes() for p in store.store_files(self.root)}
        self.assertEqual(cached_tlc(self.model, 1, collect, **kw)['wall_s'], 6)
        self.assertEqual(collect.call_count, 3)
        self.assertEqual(before, {p: p.read_bytes() for p in store.store_files(self.root)})

    def test_repeated_tlc_rejects_partial_and_disagreeing_samples(self):
        good = dict(result='success', exit=0, distinct=10, wall_s=3, cpu_s=2)
        for bad in [dict(good, result='timeout'), dict(good, distinct=11), dict(good, exit=1)]:
            with self.subTest(bad=bad):
                raw = cached_tlc(self.model, 1, Mock(side_effect=[good, bad, good]),
                                 root=self.root, version='v', instance='i', repetitions=3)
                self.assertTrue(raw['count_problems'])
                self.assertFalse(store.store_files(self.root))

    def test_repeated_tlc_missing_cpu_and_parallel_violation_counts(self):
        samples = [dict(result='safety failure', exit=12, distinct=n, wall_s=w, cpu_s=c)
                   for n, w, c in [(4, 2, None), (5, 4, 1), (6, 6, 2)]]
        raw = cached_tlc(self.model, 2, Mock(side_effect=samples), root=self.root,
                         version='v', instance='i', repetitions=3)
        self.assertEqual(raw['wall_s'], 4)
        self.assertIsNone(raw['cpu_s'])
        self.assertIsNone(raw['sample_spread']['cpu_s'])
        row = load_records(self.root)[0]
        self.assertIsNone(row['metrics']['cpu_s'])
        self.assertEqual(row['samples']['cpu_s'], [None, 1, 2])

    def test_repetition_count_rejected_before_collection(self):
        from benchmarking.cli import parse_args
        for n in [0, -1]:
            with self.assertRaises(SystemExit):
                parse_args(['tlcbase', '--tlc-repetitions', str(n)])
            collect = Mock()
            with self.assertRaises(ValueError):
                cached_tlc(self.model, 1, collect, repetitions=n)
            collect.assert_not_called()

    def test_cache_provenance_is_optional_but_validated(self):
        raw = dict(tool='tlx', result='success', wall_s=1,
                   cache={'mode': 'fresh-per-model', 'initial_state': 'empty', 'warmup': True})
        row = normalize({}, raw, 'test', '/', model='M', mode='default', workers=1)
        validate(row)
        self.assertEqual(row['provenance']['cache'], raw['cache'])
        row['provenance']['cache']['initial_state'] = 'unknown'
        with self.assertRaisesRegex(ValueError, 'cache provenance'):
            validate(row)

    def test_baseline_cache_key_and_no_recollection(self):
        measured = Mock(return_value={'wall_s': 8, 'cpu_s': 9, 'result': 'success', 'distinct': 10})
        kw = dict(root=self.root, version='TLC-v', instance='SA5.4XLARGE32')
        one = cached_tlc(self.model, 1, measured, **kw)
        self.assertEqual(cached_tlc(self.model, 1, measured, repetitions=3, **kw)['wall_s'], one['wall_s'])
        self.assertEqual(measured.call_count, 1)
        for k, v in [('workers', 2), ('version', 'TLC-new'), ('instance', 'other')]:
            args = {**kw, k: v}
            workers = args.pop('workers', 1)
            cached_tlc(self.model, workers, measured, **args)
        self.assertEqual(measured.call_count, 4)
        Path(self.model['cfg']).write_text('INIT New\n')
        cached_tlc(self.model, 1, measured, **kw)
        self.assertEqual(measured.call_count, 5)

    def test_a_cache_miss_keeps_the_collected_peak_rss(self):
        # A cache miss runs the collector and stores its record; the peak RSS
        # the collector measured must reach both the returned row and the store.
        measured = Mock(return_value={'wall_s': 8, 'cpu_s': 9, 'maxrss_mib': 400,
                                      'result': 'success', 'distinct': 10})
        raw = cached_tlc(self.model, 1, measured, root=self.root, version='v', instance='SA5.4XLARGE32')
        self.assertEqual(raw['maxrss_mib'], 400)
        self.assertEqual(load_records(self.root)[0]['metrics']['rss_mib'], 400)

    def test_repeated_tlc_baseline_uses_the_positive_sample_median(self):
        # [0, 100] is one real 100 MiB measurement: the aggregate, the stored
        # record and the retained samples must all say 100, not the 50 MiB a
        # plain median including the unknown sample would publish.
        samples = [dict(result='success', exit=0, distinct=10, wall_s=1, cpu_s=1, maxrss_mib=0),
                   dict(result='success', exit=0, distinct=10, wall_s=1, cpu_s=1, maxrss_mib=100)]
        raw = cached_tlc(self.model, 1, Mock(side_effect=samples), root=self.root,
                         version='v', instance='SA5.4XLARGE32', repetitions=2)
        self.assertEqual(raw['maxrss_mib'], 100)
        row = load_records(self.root)[0]
        self.assertEqual(row['metrics']['rss_mib'], 100)
        self.assertEqual(raw_baseline({'measurement': row})['maxrss_mib'], 100)

    def test_collected_baseline_keeps_the_key_version(self):
        # (TLC prints its version as "2026.10.02.163556 (rev: 1813307)"; the
        # key names the tla2tools revision, and check() requires the
        # measurement to carry the same.)
        measured = Mock(return_value={'wall_s': 8, 'cpu_s': 9, 'result': 'success', 'distinct': 10,
                                      'tlc_version': '2026.10.02.163556 (rev: 1813307)'})
        cached_tlc(self.model, 1, measured, root=self.root, version='1813307068bb', instance='SA5.4XLARGE32')
        stored = json.loads(next((self.root / 'bench/tlc-baselines').glob('*.json')).read_text())
        self.assertEqual(stored['measurement']['tlc_version'], stored['key']['tlc_version'])
        self.assertEqual(stored['measurement']['raw_result']['tlc_version'], '2026.10.02.163556 (rev: 1813307)')

    def test_concurrent_collectors_share_one_baseline(self):
        from concurrent.futures import ThreadPoolExecutor
        import threading
        started, release = threading.Event(), threading.Event()
        def collect():
            started.set()
            self.assertTrue(release.wait(5))
            return {'wall_s': 1, 'result': 'success'}
        measured = Mock(side_effect=collect)
        kw = dict(root=self.root, version='v', instance='i')
        with ThreadPoolExecutor(max_workers=2) as pool:
            first = pool.submit(cached_tlc, self.model, 1, measured, **kw)
            self.assertTrue(started.wait(5))
            second = pool.submit(cached_tlc, self.model, 1, measured, **kw)
            release.set()
            self.assertEqual(first.result()['wall_s'], second.result()['wall_s'])
        self.assertEqual(measured.call_count, 1)

    def test_input_change_during_collection_cannot_enter_cache(self):
        def collect():
            Path(self.model['cfg']).write_text('INIT Changed\n')
            return {'wall_s': 1, 'result': 'success'}
        with self.assertRaisesRegex(ValueError, 'changed during'):
            cached_tlc(self.model, 1, collect, root=self.root, version='v', instance='i')
        self.assertEqual(list((self.root / 'bench/tlc-baselines').glob('*.json')), [])

    def test_source_sync_gate_rejects_unimported_history(self):
        (self.root / 'bench/suite.json').write_text(json.dumps({'models': []}))
        br.generate(self.root)
        (self.root / 'bench/new.json').write_text(json.dumps({'commit': 'r', 'runs': {
            'M': {'model': 'M', 'mode': 'compile', 'workers': 1, 'wall_s': 1, 'result': 'success'}}}))
        self.assertTrue(any('unimported' in p for p in br.check(self.root)))
        migrate(self.root)
        br.generate(self.root)
        self.assertEqual(br.check(self.root), [])

    def write_source(self, name, runs):
        p = self.root / 'bench' / name
        p.write_text(json.dumps({'commit': 'abc', 'date': '2026-10-07',
                                 'machine': 'x86_64 SA5.4XLARGE32', 'runs': runs}))
        return p

    def stored(self, source):
        # The store is one file per key, not one container per source, so a
        # source's rows are read back by their provenance rather than by a
        # container path.
        return [r for r in load_records(self.root) if r['provenance']['source'] == source]

    def test_empty_source_replacement_clears_the_owned_container(self):
        p = self.write_source('h.json', {'M': {'model': 'M', 'mode': 'compile', 'workers': 1,
                                               'wall_s': 1, 'result': 'success'}})
        self.assertEqual(len(ingest(p, self.root)), 1)
        self.assertEqual(len(self.stored('bench/h.json')), 1)
        p.write_text(json.dumps({'commit': 'abc', 'runs': {}}))
        self.assertEqual(ingest(p, self.root), [])
        self.assertEqual(self.stored('bench/h.json'), [])
        self.assertEqual([r for r in load_records(self.root) if r['provenance']['source'] == 'bench/h.json'], [])

    def test_partial_source_replacement_keeps_only_live_rows(self):
        rows = {name: {'model': name, 'mode': 'compile', 'workers': 1, 'wall_s': 1, 'result': 'success'}
                for name in ('M', 'N')}
        p = self.write_source('h.json', rows)
        ingest(p, self.root)
        self.assertEqual(len(self.stored('bench/h.json')), 2)
        del rows['N']
        p.write_text(json.dumps({'commit': 'abc', 'runs': rows}))
        ingest(p, self.root)
        self.assertEqual([r['model'] for r in self.stored('bench/h.json')], ['M'])

    def test_migration_clears_a_container_whose_source_vanished(self):
        p = self.write_source('old.json', {'M': {'model': 'M', 'mode': 'compile', 'workers': 1,
                                                 'wall_s': 1, 'result': 'success'}})
        self.assertEqual(len(migrate(self.root)), 1)
        self.assertEqual(len(self.stored('bench/old.json')), 1)
        p.unlink()
        migrate(self.root)
        self.assertEqual(self.stored('bench/old.json'), [])
        self.assertEqual(load_records(self.root), [])

    def test_ingest_keeps_independent_baselines_while_clearing_sources(self):
        baseline = cached_tlc(self.model, 1, lambda: {'wall_s': 8, 'result': 'success', 'distinct': 10},
                              root=self.root, version='v', instance='i')
        baseline_files = sorted((self.root / 'bench/tlc-baselines').glob('*.json'))
        self.assertEqual(len(baseline_files), 1)
        p = self.write_source('h.json', {'M': {'model': 'M', 'mode': 'compile', 'workers': 1,
                                               'wall_s': 1, 'result': 'success'}})
        ingest(p, self.root)
        p.write_text(json.dumps({'commit': 'abc', 'runs': {}}))
        ingest(p, self.root)
        self.assertEqual(self.stored('bench/h.json'), [])
        self.assertEqual(sorted((self.root / 'bench/tlc-baselines').glob('*.json')), baseline_files)
        self.assertIn(baseline['baseline_id'], [r['id'] for r in load_records(self.root)])

    def test_store_writes_are_serialized_by_the_lock(self):
        import threading
        entered, release = threading.Event(), threading.Event()

        def hold():
            with store_lock(self.root):
                entered.set()
                release.wait(5)

        holder = threading.Thread(target=hold)
        holder.start()
        self.assertTrue(entered.wait(5))
        p = self.write_source('h.json', {'M': {'model': 'M', 'mode': 'compile', 'workers': 1,
                                               'wall_s': 1, 'result': 'success'}})
        done = threading.Event()

        def run():
            ingest(p, self.root)
            done.set()

        worker = threading.Thread(target=run)
        worker.start()
        self.assertFalse(done.wait(0.5))  # blocked behind the held store lock
        release.set()
        self.assertTrue(done.wait(5))
        holder.join(5)
        worker.join(5)
        self.assertEqual(len(self.stored('bench/h.json')), 1)

    def test_concurrent_source_ingests_do_not_lose_measurements(self):
        # Two lanes ingest sources at once. Each source is a distinct
        # measurement (its own model), so the store lock must serialize the
        # whole read-modify-write: neither lane's rows are dropped by the other.
        import threading
        barrier = threading.Barrier(2)

        def run(prefix):
            barrier.wait()
            for i in range(5):
                model = f'{prefix}{i}'
                p = self.write_source(f'{model}.json', {model: {'model': model, 'mode': 'compile', 'workers': 1,
                                                                'wall_s': 1, 'result': 'success'}})
                ingest(p, self.root)

        threads = [threading.Thread(target=run, args=(prefix,)) for prefix in ('a', 'b')]
        for t in threads:
            t.start()
        for t in threads:
            t.join(15)
        for prefix in ('a', 'b'):
            for i in range(5):
                self.assertEqual(len(self.stored(f'bench/{prefix}{i}.json')), 1)
        self.assertEqual(len(load_records(self.root)), 10)

    def test_check_rejects_reverse_orphans_and_missing_sources(self):
        (self.root / 'bench/suite.json').write_text(json.dumps({'models': []}))
        br.generate(self.root)
        p = self.write_source('h.json', {'M': {'model': 'M', 'mode': 'compile', 'workers': 1,
                                               'wall_s': 1, 'result': 'success'}})
        ingest(p, self.root)
        br.generate(self.root)
        self.assertEqual(br.check(self.root), [])
        p.write_text(json.dumps({'commit': 'abc', 'runs': {}}))
        self.assertTrue(any('no longer produced by its source' in q for q in br.check(self.root)))
        ingest(p, self.root)
        br.generate(self.root)
        self.assertEqual(br.check(self.root), [])
        p.write_text(json.dumps({'commit': 'abc', 'runs': {'M': {'model': 'M', 'mode': 'compile', 'workers': 1,
                                                                'wall_s': 1, 'result': 'success'}}}))
        ingest(p, self.root)
        br.generate(self.root)
        self.assertEqual(br.check(self.root), [])
        p.unlink()
        self.assertTrue(any('source file is missing' in q for q in br.check(self.root)))

    def test_tlcbase_collection_ingestion_reuse_and_report_preserve_evidence(self):
        import argparse
        import platform
        import bench
        from benchmarking.commands import tlcbase
        path = self.root / 'bench/history/repeated.json'
        model = {**self.model, 'source': 'fixture', 'tlc': {}}
        a = argparse.Namespace(workers='1', missing=False, out=str(path), timeout=60, slice='', tlc_repetitions=3)
        samples = [dict(result='success', exit=0, distinct=10, wall_s=w, cpu_s=c, maxrss_mib=None)
                   for w, c in [(1, None), (2, 1), (4, 2)]]
        snapshots = []
        def import_history(path):
            before = {p: p.read_bytes() for p in store.store_files(self.root)}
            ingest(path, self.root)
            self.assertEqual(before, {p: p.read_bytes() for p in store.store_files(self.root)})
            snapshots.append(before)
        def cache(m, w, collect, **kw):
            return cached_tlc(m, w, collect, root=self.root, version='v', instance='SA5.4XLARGE32', **kw)
        with patch.object(bench, 'tlcbase_models', return_value={'M': model}), \
             patch.object(bench_machine, 'machine_desc', return_value=f'{platform.machine()} SA5.4XLARGE32'), \
             patch.object(bench_machine, 'tla2tools_info', return_value={'revision': 'v'}), \
             patch.object(bench_machine, 'jvm_info', return_value={}), \
             patch.object(baselines, 'cached_tlc', side_effect=cache), \
             patch.object(tlcbase, '_collect_tlc_measured', side_effect=samples) as collect, \
             patch.object(legacy, 'ingest', side_effect=import_history), \
             contextlib.redirect_stdout(io.StringIO()) as output:
            bench.cmd_tlcbase(a)
            migrate(self.root)
            self.assertEqual(snapshots[0], {p: p.read_bytes() for p in store.store_files(self.root)})
            bench.cmd_tlcbase(a)
            bench.cmd_tlcbase_report(argparse.Namespace(baseline=str(path), top=10))
        self.assertEqual(collect.call_count, 3)
        self.assertEqual(snapshots[0], snapshots[1])
        row = load_records(self.root)[0]
        self.assertEqual(row['raw_result']['tlc_samples'], samples)
        self.assertEqual(row['samples']['wall_s'], [1, 2, 4])
        self.assertEqual(row['provenance']['sample_spread']['wall_s'], 1.5)
        self.assertEqual(row['aggregation'], 'median')
        self.assertIn('n/a', output.getvalue())
        self.assertIn('CPU n/as', output.getvalue())
        history = json.loads(path.read_text())['models']['M']['runs']['1']
        self.assertIsNone(history['cpu_s'])
        self.assertEqual(history['tlc_samples'], samples)

    def test_history_owned_baseline_survives_reingestion_and_migration_until_removed(self):
        import platform
        path = self.root / 'bench/history/owned.json'
        path.parent.mkdir(parents=True, exist_ok=True)
        digest = content_digest(self.model)
        header = {'kind': 'tlc-baseline', 'machine': f'{platform.machine()} SA5.4XLARGE32',
                  'instance_type': 'SA5.4XLARGE32', 'tla2tools': {'revision': 'v'}, 'workers': [1]}
        run = {'result': 'success', 'exit': 0, 'distinct': 10, 'wall_s': 5.0, 'cpu_s': 4.0,
               'content_digest': digest, 'tlc_version': 'v'}
        path.write_text(json.dumps({**header, 'models': {'M': {'runs': {'1': run}}}}))
        ingest(path, self.root)
        before = {p: p.read_bytes() for p in store.store_files(self.root)}
        self.assertEqual(len(before), 1)
        collect = Mock(side_effect=AssertionError('should reuse history-owned baseline'))
        reused = cached_tlc(self.model, 1, collect, root=self.root, version='v', instance='SA5.4XLARGE32', repetitions=3)
        self.assertEqual(collect.call_count, 0)
        path.write_text(json.dumps({**header, 'models': {'M': {'runs': {'1': reused}}}}))
        ingest(path, self.root)
        self.assertEqual(before, {p: p.read_bytes() for p in store.store_files(self.root)})
        migrate(self.root)
        self.assertEqual(before, {p: p.read_bytes() for p in store.store_files(self.root)})
        # Removing the row from its owning history still deletes the stored file.
        path.write_text(json.dumps({**header, 'models': {}}))
        ingest(path, self.root)
        self.assertEqual(store.store_files(self.root), [])

    def test_cached_tlc_reuses_shipped_legacy_baseline_with_historical_revision(self):
        import argparse
        import bench
        from benchmarking.commands import tlcbase
        shipped = store.ROOT / 'bench/tlc-baselines/3f4ec027479e1fb9ca60dea542a93ca1101fff3aef7532868eeef0f6dae94079.json'
        entry = json.loads(shipped.read_bytes())
        key = entry['key']
        self.assertEqual(key['model'], 'DieHard/DieHard')
        self.assertIsNotNone(key['revision'])
        for subdir in ('bench/records', 'bench/tlc-baselines'):
            dst = self.root / subdir
            dst.mkdir(parents=True, exist_ok=True)
            for src in (store.ROOT / subdir).glob('*.json'):
                (dst / src.name).write_bytes(src.read_bytes())
        before = {p: p.read_bytes() for p in store.store_files(self.root)}
        model = {**self.model, 'id': key['model'], 'source': 'fixture', 'tlc': {}}
        out_path = self.root / 'bench/history/diehard.json'
        args = argparse.Namespace(workers=str(key['workers']), missing=False, out=str(out_path),
                                  timeout=60, slice='', tlc_repetitions=3)
        collect = Mock(side_effect=AssertionError('should reuse shipped legacy baseline'))
        def cache(m, w, fn, **kw):
            return cached_tlc(m, w, fn, root=self.root, version=key['tlc_version'],
                              instance=key['instance_type'], **kw)
        with patch.object(bench, 'tlcbase_models', return_value={key['model']: model}), \
             patch.object(bench_machine, 'machine_desc', return_value=f"x86_64 {key['instance_type']}"), \
             patch.object(bench_machine, 'tla2tools_info', return_value={'revision': key['tlc_version']}), \
             patch.object(bench_machine, 'jvm_info', return_value={}), \
             patch.object(baselines, 'content_digest', return_value=key['content_digest']), \
             patch.object(baselines, 'cached_tlc', side_effect=cache), \
             patch.object(tlcbase, '_collect_tlc_measured', side_effect=collect), \
             patch.object(legacy, 'ingest', side_effect=lambda p: ingest(p, self.root)), \
             patch('platform.machine', return_value='x86_64'), \
             contextlib.redirect_stdout(io.StringIO()):
            bench.cmd_tlcbase(args)
            self.assertIsNone(find_baseline(model, key['workers'], root=self.root,
                                            version=key['tlc_version'], instance=key['instance_type'], arch='aarch64'))
        self.assertEqual(collect.call_count, 0)
        self.assertEqual({p: p.read_bytes() for p in store.store_files(self.root)}, before)
        saved = json.loads(out_path.read_text())['models'][key['model']]['runs'][str(key['workers'])]
        self.assertEqual(saved['baseline_id'], entry['measurement']['id'])

    def test_merged_multi_sample_history_preserves_raw_attempts_across_stores(self):
        import argparse
        import platform
        import bench
        from benchmarking.commands import tlcbase
        src_out = self.root / 'bench/history/slice.json'
        model = {**self.model, 'source': 'fixture', 'tlc': {}}
        samples = [dict(result='success', exit=0, distinct=10, wall_s=w, cpu_s=c, maxrss_mib=r)
                   for w, c, r in [(3, 2, 100), (5, 4, 110), (7, 6, 120)]]
        def run_tlcbase(root, out_path, collector):
            args = argparse.Namespace(workers='1', missing=False, out=str(out_path),
                                      timeout=60, slice='', tlc_repetitions=3)
            with patch.object(bench, 'tlcbase_models', return_value={'M': model}), \
                 patch.object(bench_machine, 'machine_desc', return_value=f'{platform.machine()} SA5.4XLARGE32'), \
                 patch.object(bench_machine, 'tla2tools_info', return_value={'revision': 'v'}), \
                 patch.object(bench_machine, 'jvm_info', return_value={}), \
                 patch.object(baselines, 'cached_tlc',
                              side_effect=lambda m, w, fn, **kw: cached_tlc(m, w, fn, root=root, version='v',
                                                                            instance='SA5.4XLARGE32', **kw)), \
                 patch.object(tlcbase, '_collect_tlc_measured', side_effect=collector) as mocked, \
                 patch.object(legacy, 'ingest', side_effect=lambda p: ingest(p, root)), \
                 contextlib.redirect_stdout(io.StringIO()):
                bench.cmd_tlcbase(args)
            return mocked.call_count
        self.assertEqual(run_tlcbase(self.root, src_out, samples), 3)
        with tempfile.TemporaryDirectory() as td:
            dest_root = Path(td)
            merged = dest_root / 'bench/history/merged.json'
            merged.parent.mkdir(parents=True, exist_ok=True)
            with contextlib.redirect_stdout(io.StringIO()):
                bench.cmd_tlcbase_merge(argparse.Namespace(inputs=[str(src_out)], out=str(merged), set=[]))
            migrate(dest_root)
            before = {p: p.read_bytes() for p in store.store_files(dest_root)}
            self.assertEqual(len(before), 1)
            self.assertEqual(run_tlcbase(dest_root, merged, Mock(side_effect=AssertionError('unexpected recollect'))), 0)
            self.assertEqual({p: p.read_bytes() for p in store.store_files(dest_root)}, before)
            row = load_records(dest_root)[0]
            self.assertEqual(row['raw_result']['tlc_samples'], samples)
            reused = json.loads(merged.read_text())['models']['M']['runs']['1']
            self.assertEqual(reused['tlc_samples'], samples)
            self.assertEqual(reused['aggregation'], 'median')
            self.assertAlmostEqual(reused['sample_spread']['wall_s'], 0.8)

    def test_rejected_tlc_attempts_keep_timeout_bound_and_leave_timing_summary(self):
        import argparse
        import bench
        good = dict(result='success', exit=0, distinct=10, wall_s=20, cpu_s=1)
        timeout = dict(result='timeout', exit=124, wall_s=4, cpu_s=2)
        raw = cached_tlc(self.model, 1, Mock(side_effect=[good, timeout]), root=self.root,
                         version='v', instance='i', repetitions=3)
        self.assertEqual(raw['wall_s'], 4)
        self.assertEqual(raw['aggregation'], 'last-attempt')
        self.assertEqual(raw['tlc_samples'], [good, timeout])
        rejected = baselines.collect_samples(Mock(side_effect=[good, dict(good, distinct=11)]), 2, 1)
        paths = [self.root / 'first.json', self.root / 'second.json']
        for path, run in zip(paths, [raw, dict(timeout, wall_s=8)]):
            path.write_text(json.dumps({'kind': 'tlc-baseline', 'tla2tools': {}, 'workers': [1],
                                        'models': {'M': {'runs': {'1': run}}, 'bad': {'runs': {'1': rejected}}}}))
        merged = self.root / 'merged.json'
        with contextlib.redirect_stdout(io.StringIO()) as output:
            bench.cmd_tlcbase_merge(argparse.Namespace(inputs=list(map(str, paths)), out=str(merged), set=[]))
            bench.cmd_tlcbase_report(argparse.Namespace(baseline=str(merged), top=10))
        self.assertEqual(json.loads(merged.read_text())['models']['M']['runs']['1']['wall_s'], 8)
        self.assertIn('1 timeouts, 1 rejected; accepted timings: wall 0s', output.getvalue())
        self.assertIn('15-60s: 0', output.getvalue())

    def test_tlcbase_missing_ignores_stale_raw_history_shortcut(self):
        import argparse
        import bench
        path = self.root / 'old-baseline.json'
        path.write_text(json.dumps({'kind': 'tlc-baseline', 'models': {
            'M': {'runs': {'1': {'result': 'success', 'wall_s': 123}}}}}))
        model = {**self.model, 'source': 'fixture', 'tlc': {}}
        a = argparse.Namespace(workers='1', missing=True, collect=True, out=str(path), force=False, timeout=1, slice='')
        raw = {'result': 'success', 'distinct': 1, 'wall_s': 7, 'cpu_s': 8, 'maxrss_mib': 10}
        with patch.object(bench, 'tlcbase_models', return_value={'M': model}), patch.object(bench_machine, 'jvm_info', return_value={}), \
             patch.object(bench_machine, 'git_commit', return_value='fixture'), patch.object(bench, 'tlc_measured', return_value=raw) as collect:
            bench.cmd_tlcbase(a)
        self.assertEqual(collect.call_count, 1)
        self.assertEqual(json.loads(path.read_text())['models']['M']['runs']['1']['wall_s'], 7)

    def test_source_sync_rejects_relabelled_execution_mode(self):
        (self.root / 'bench/suite.json').write_text(json.dumps({'models': []}))
        # A machine is recorded so the row's key is complete: the mode is then a
        # key dimension, and relabelling it files the row elsewhere.
        self.write_source('history.json', {'M': {'model': 'M', 'mode': 'compile', 'workers': 1,
                                                 'wall_s': 1, 'result': 'success'}})
        records = migrate(self.root)
        records[0]['mode'] = 'default'
        # The store is derived, so a relabelled row is published as the whole
        # store (dropping the file the old mode named); check must see that the
        # source still derives `-compile` and no stored row carries it.
        store.realign_store(records, self.root)
        br.generate(self.root)
        self.assertTrue(any('unimported/changed' in p for p in br.check(self.root)))

    def test_cache_only_baseline_survives_migration_and_matches_new_tlx(self):
        import platform
        baseline = cached_tlc(self.model, 1, lambda: {'wall_s': 8, 'result': 'success', 'distinct': 10},
                              root=self.root, version='v', instance='i')
        raw = {'model': 'M', 'mode': 'compile', 'workers': 1, 'wall_s': 1, 'result': 'success', 'distinct': 10,
               'content_digest': content_digest(self.model), 'tlc_version': 'v'}
        (self.root / 'bench/new.json').write_text(json.dumps({'commit': 'new', 'machine': platform.machine(), 'instance_type': 'i', 'runs': {'M': raw}}))
        records = migrate(self.root)
        tx = next(r for r in records if r['tool'] == 'tlx')
        self.assertEqual(tx['baseline'], baseline['baseline_id'])
        self.assertEqual(len(records), 2)

    def test_timeout_is_not_valid_baseline(self):
        f = Mock(return_value={'wall_s': 3, 'result': 'timeout'})
        for _ in range(2):
            cached_tlc(self.model, 1, f, root=self.root, version='v', instance='i')
        self.assertEqual(f.call_count, 2)

    def test_digest_includes_imported_modules_and_flags(self):
        Path(self.model['tla']).write_text('---- MODULE M ----\nEXTENDS Other\n====\n')
        other = self.root / 'Other.tla'
        other.write_text('---- MODULE Other ----\nx == 1\n====\n')
        a = content_digest(self.model)
        other.write_text('---- MODULE Other ----\nx == 2\n====\n')
        self.assertNotEqual(a, content_digest(self.model))
        self.assertNotEqual(content_digest(self.model), content_digest({**self.model, 'flags': ['-simulate']}))

    def test_adoption_requires_exact_current_oracle_and_recorded_tlc_version(self):
        tc = self.record(tool='tlc', mode='-tlc', tlc_version='known')
        tc['counts']['depth'] = 2
        oracle = {'M': {'tlc': {'result': 'success', 'distinct': 10, 'depth': 2}}}
        models = {'M': self.model}
        adopted = adopt_legacy([copy.deepcopy(tc)], models, oracle, 'known-full')[0]
        self.assertEqual(adopted['content_digest'], content_digest(self.model))
        self.assertIn('matched_counts', adopted['provenance']['adoption'])
        for field, bad in [('depth', 3), ('distinct', 11), ('result', 'deadlock')]:
            changed = copy.deepcopy(tc)
            changed['counts'][field] = bad
            self.assertIsNone(adopt_legacy([changed], models, oracle, 'known-full')[0]['content_digest'])
        tc['tlc_version'] = None
        self.assertIsNone(adopt_legacy([tc], models, oracle, 'known-full')[0]['content_digest'])

    def test_remigration_never_readopts_changed_input_bytes(self):
        path = self.root / 'bench/legacy.json'
        raw = {'model': 'M', 'mode': 'tlc', 'workers': 1, 'wall_s': 1, 'result': 'success', 'distinct': 10, 'depth': 2, 'tlc_version': 'known'}
        path.write_text(json.dumps({'runs': {'M': raw}}))
        records = migrate(self.root)
        adopt_legacy(records, {'M': self.model}, {'M': {'tlc': raw}}, 'known')
        original_digest = records[0]['content_digest']
        self.assertIsNotNone(original_digest)
        write_records(records, self.root)
        Path(self.model['cfg']).write_text('INIT Changed\n')
        remigrated = migrate(self.root)
        self.assertEqual(remigrated[0]['content_digest'], original_digest)
        self.assertNotEqual(original_digest, content_digest(self.model))

    def test_suite_resolution_guard_rejects_misspelled_external_id(self):
        from benchmarking import bench_suite
        manifest = {'models': [{'id': 'ext/wrong/Trace'}]}
        self.assertIn('cannot be resolved', bench_suite.resolution_problems(manifest, {'ext/right/Trace': {}})[0])
        self.assertEqual(bench_suite.resolution_problems(manifest, {'ext/wrong/Trace': {}}), [])

    def test_report_sections_ratios_and_gaps(self):
        tx = self.record(category=['corpus', 'compiled'], content_digest='digest')
        tc = self.record(tool='tlc', mode='-tlc', content_digest='digest', tlc_version='v')
        tc['metrics']['wall_s'] = 9
        tc['id'] += '-tlc'
        tx['baseline'] = tc['id']
        text = br.render([tx, tc], {'models': [{'id': 'M'}, {'id': 'missing'}]}, stale_after=20)
        positions = [text.index('## ' + s) for s in br.SECTIONS]
        self.assertEqual(positions, sorted(positions))
        self.assertIn('3.00×', text)
        self.assertIn('missing', text)
        self.assertIn('No eligible records', text)  # no invented default result
        self.assertIn('../bench/records/', text)
        tc['workers'] = 8
        self.assertNotIn('3.00×', br.render([tx, tc], {'models': []}))

    def test_report_pairs_peak_rss_in_the_summary_and_detail_tables(self):
        # The stored RSS of both tools is published side by side: the summary's
        # cohort median and range, and each detail row's TLC footprint and ratio.
        tx = self.record(category=['corpus'], content_digest='digest')
        tx['metrics']['rss_mib'] = 100.0
        tc = self.record(tool='tlc', mode='-tlc', content_digest='digest', tlc_version='v')
        tc['metrics']['wall_s'] = 9
        tc['metrics']['rss_mib'] = 400.0
        tc['id'] += '-tlc'
        tx['baseline'] = tc['id']
        text = br.render([tx, tc], {'models': []})
        summary = text.split('## Summary')[1].split('## ')[0]
        self.assertIn('Median TLC / tlx RSS', summary)
        self.assertIn('| 3.00× | 3.00–3.00× | 4.00× | 4.00–4.00× |', summary)
        detail = text.split('## Compiled tier per model')[1].split('## ')[0]
        self.assertIn('TLC RSS MiB', detail)
        # TLC wall/CPU, TLC RSS, wall ratio, RSS ratio: a 400 MiB baseline
        # against a 100 MiB tlx row is a 4× footprint reduction.
        self.assertIn('| 9.00 / 2.00 | 400.00 | 3.00× | 4.00× |', detail)

    def test_missing_or_zero_peak_rss_stays_unknown_not_zero(self):
        # Unknown metadata stays unknown (never 0.00), on either side and in
        # the summary, which therefore says `—` rather than inventing a ratio.
        tx = self.record(category=['corpus'], content_digest='digest')
        tc = self.record(tool='tlc', mode='-tlc', content_digest='digest', tlc_version='v')
        tc['metrics']['wall_s'] = 9
        tc['id'] += '-tlc'
        tx['baseline'] = tc['id']
        for tlx_rss, tlc_rss in ((None, 400.0), (100.0, None), (0, 400.0), (100.0, 0)):
            with self.subTest(tlx_rss=tlx_rss, tlc_rss=tlc_rss):
                tx['metrics']['rss_mib'] = tlx_rss
                tc['metrics']['rss_mib'] = tlc_rss
                text = br.render([tx, tc], {'models': []})
                summary = text.split('## Summary')[1].split('## ')[0]
                self.assertIn('| 3.00× | 3.00–3.00× | — | — |', summary)
                detail = text.split('## Compiled tier per model')[1].split('## ')[0]
                # The tlx footprint cell follows the same unknown rule as the
                # ratio and the TLC cell: a stored zero is not 0.00 MiB.
                if tlx_rss in (None, 0):
                    self.assertIn('| 3.00 | 2.00 | — | — |', detail)
                else:
                    self.assertIn('| 3.00 | 2.00 | 100.00 | — |', detail)
                if tlc_rss in (None, 0):
                    self.assertIn('| 9.00 / 2.00 | — | 3.00× | — |', detail)
                else:
                    self.assertIn('| 9.00 / 2.00 | 400.00 | 3.00× | — |', detail)
                self.assertNotIn('0.00×', detail)

    def reduced_row(self, samples, **changes):
        """A measured row as the store writes it, its samples carrying the line.

        The `Optimizations:` line is the run's own statement that it reduced
        its search; the report has to label a published ratio from it. The
        fixtures below are the known-bad cases: before this label existed,
        `docs/performance.md` published such a ratio with nothing to say the
        tlx side was reduced. A sample that does not carry the key at all is a
        different case from one that records an empty list, and the fixtures
        cover both.
        """
        h = {'commit': 'abc123', 'date': '2026-10-07', 'machine': 'x86_64, tencent SA5.4XLARGE32'}
        raw = {'model': 'M', 'mode': 'default', 'workers': 1, 'walls': [1.0, 1.0, 1.0],
               'cpu': [1.0, 1.0, 1.0], 'result': 'success', 'distinct': 10, 'generated': 20, 'depth': 3,
               'content_digest': 'd', 'tlc_version': 'v',
               'raw_result': {'samples': [{'result': 'success', **s} for s in samples], 'warmups': []}}
        r = normalize(h, raw, 'bench/history/a.json', '/runs/M')
        r.update(changes)
        return r

    def test_reduced_rows_are_labelled_from_the_record_not_from_counts(self):
        baseline = self.record(tool='tlc', mode='-tlc', content_digest='d', tlc_version='v')
        baseline['id'] = 'baseline'
        baseline['metrics']['wall_s'] = 9.0
        line = ['symmetry Permutations(RM) (proven; safety checks only)']

        # A row whose record names the optimization is labelled with it, and the
        # group it belongs to counts it.
        tx = self.reduced_row([{'optimizations': line}], category=['corpus'], baseline='baseline')
        text = br.render([tx, baseline], {'models': []})
        self.assertIn('tlx optimizations', text)
        self.assertIn('| Models with recorded optimizations |', text)
        self.assertIn('| ' + line[0] + ' |', text)
        self.assertIn('| 1 |', text.split('## Summary')[1].split('##')[0])

        # The label is the record's statement, not a count difference: the same
        # counts with no recorded line are `none`, and a reduced row whose
        # counts happen to equal the baseline keeps its label.
        counts_unlike = self.reduced_row([{'optimizations': []}], category=['corpus'], baseline='baseline')
        counts_unlike['counts']['distinct'] = 11
        text = br.render([counts_unlike, baseline], {'models': []})
        self.assertIn('| none |', text)
        self.assertNotIn(line[0], text)

        counts_like = self.reduced_row([{'optimizations': line}], category=['corpus'], baseline='baseline')
        self.assertEqual(counts_like['counts']['distinct'], baseline['counts']['distinct'])
        self.assertIn(line[0], br.render([counts_like, baseline], {'models': []}))

    def test_a_sample_without_the_optimizations_key_is_unknown_not_none(self):
        # Older compatible samples simply do not carry the key. That is "the
        # record does not state it", which must not read as "the run used no
        # optimization" (unknown metadata stays unknown).
        baseline = self.record(tool='tlc', mode='-tlc', content_digest='d', tlc_version='v')
        baseline['id'] = 'baseline'
        baseline['metrics']['wall_s'] = 9.0
        for reason, samples in (
                ('absent key', [{'wall_s': 1.0}]),
                ('absent on one of two samples', [{'optimizations': []}, {'wall_s': 1.0}]),
                ('no sample detail', [])):
            with self.subTest(reason=reason):
                tx = self.reduced_row(samples, category=['corpus'], baseline='baseline')
                if not samples:
                    tx['raw_result'] = {}
                text = br.render([tx, baseline], {'models': []})
                self.assertIn('| unknown |', text)
                self.assertNotIn('| none |', text)

        # Explicitly recorded, and explicitly empty, is `none`.
        tx = self.reduced_row([{'optimizations': []}], category=['corpus'], baseline='baseline')
        self.assertIn('| none |', br.render([tx, baseline], {'models': []}))

        # A record with no per-sample detail at all is unknown too.
        tx['raw_result'] = {}
        self.assertIn('| unknown |', br.render([tx, baseline], {'models': []}))

    def test_report_states_the_timing_and_cache_conditions(self):
        # The timed value follows a discarded warm-up in the same process
        # sequence, and the native cache is not isolated per configuration, so
        # the report may not call the discarded run cold (benchmarking.md
        # section 1 owns the protocol).
        text = br.render([self.record(category=['corpus'])], {'models': []})
        self.assertIn('each timed sample is a separate process run that follows a discarded warm-up', text)
        self.assertIn('not a cold-cache measurement', text)
        self.assertIn('instead of being isolated per configuration', text)
        self.assertIn('A TLC time is its one process, including its own start-up.', text)
        # The label states the tlx side's record; it does not claim the TLC
        # baseline was unreduced (a TLC baseline may declare SYMMETRY too).
        self.assertIn('it does not claim the TLC baseline was unreduced', text)

    def test_incomplete_current_key_is_a_coverage_gap(self):
        tc = self.record(tool='tlc', mode='-tlc', content_digest='d', tlc_version='v')
        tc['counts']['result'] = 'timeout'
        text = br.render([tc], {'models': [{'id': 'M'}]}, baseline_inputs={'M': {'content_digest': 'd', 'tlc_version': 'v'}})
        self.assertIn('missing/stale baseline key', text)
        self.assertNotIn('current input key recorded', text)

    def test_scaling_separates_limits_and_sorts_nullable_metadata(self):
        records = []
        for group, cgroup in [('ordinary', None), ('limited', 1024)]:
            for workers in (1, 8):
                r = self.record(workers=workers, category=['scaling'], revision='same')
                r['id'] += group + str(workers)
                r['configuration']['cgroup_mib'] = cgroup
                r['metrics']['wall_s'] = 8 if workers == 1 else 2
                records.append(r)
        text = br.render(records, {'models': []})
        self.assertIn('50.00%', text)
        self.assertNotEqual(br.scaling_identity(records[0]), br.scaling_identity(records[2]))

    def test_historical_markdown_is_frozen_even_after_remigration(self):
        path = self.root / 'bench/results.md'
        path.write_text('# Original historical table\n')
        (self.root / 'bench/suite.json').write_text(json.dumps({'models': []}))
        migrate(self.root)
        br.generate(self.root)
        self.assertEqual(br.check(self.root), [])
        path.write_text('# New manual timings\n')
        migrate(self.root)
        br.generate(self.root)
        self.assertTrue(any('frozen' in p for p in br.check(self.root)))

    def test_enforcement_rejects_edited_report_and_ad_hoc_markdown(self):
        ingest(self.write_source('a.json', {'M': {'model': 'M', 'mode': 'compile', 'workers': 1,
                                                  'wall_s': 2, 'result': 'success'}}), self.root)
        (self.root / 'bench' / 'suite.json').write_text(json.dumps({'models': [{'id': 'M'}]}))
        br.generate(self.root)
        self.assertEqual(br.check(self.root), [])
        report = self.root / 'docs' / 'performance.md'
        report.write_text(report.read_text() + '\nhand written ratio\n')
        self.assertTrue(any('regenerate' in p for p in br.check(self.root)))
        br.generate(self.root)
        (self.root / 'bench' / 'random.md').write_text('# New timings\n')
        self.assertTrue(any('ad hoc' in p for p in br.check(self.root)))


class InputIdentityTest(unittest.TestCase):
    """A model's identity follows its run directory and the inputs staging reads.

    The measurement key used to omit the working directory and, with it, the
    trace data a staging resolves (docs/issues.md, "EWD benchmark input
    identity and expectations"): the same spec staged next to itself - where a
    relative ndjson input is not there - and staged in the corpus root - where
    it is - had one identity, so the failing staging's evidence could satisfy
    the corrected run. `content_digest` now carries a portable `layout`: `cwd`
    when a run does not start next to its spec, plus the resolved bytes of every
    input the model declares, and a missing declared input has no identity.
    """

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = os.path.join(self.tmp.name, 'Examples')
        self.spec = os.path.join(self.root, 'specifications', 'A')
        os.makedirs(self.spec)
        self.tla = os.path.join(self.spec, 'A.tla')
        self.cfg = os.path.join(self.spec, 'A.cfg')
        self.trace = os.path.join(self.spec, 'A.ndjson')
        for path, text in ((self.tla, '---- MODULE A ----\n====\n'), (self.cfg, 'INIT Init\n'), (self.trace, '{}\n')):
            with open(path, 'w') as stream:
                stream.write(text)

    def model(self, *, tla=None, cfg=None, root=None, cwd='root', inputs=('specifications/A/A.ndjson',)):
        """A model staged in `root` (`cwd: root`) or next to its spec (`cwd=None`)."""
        m = {'id': 'A', 'tla': tla or self.tla, 'cfg': cfg or self.cfg}
        if root is not None:
            m['root'] = root
        if cwd is not None:
            m['cwd'] = cwd
        if inputs is not None:
            m['inputs'] = list(inputs)
        return m

    def test_the_run_directory_is_part_of_the_identity(self):
        next_to_spec = self.model(cwd=None, inputs=None)
        self.assertEqual(baselines.input_layout(next_to_spec), {})
        self.assertNotEqual(content_digest(next_to_spec), content_digest(self.model(root=self.root)))
        self.assertEqual(baselines.input_layout(self.model(root=self.root))['cwd'], baselines.ROOT_CWD_TOKEN)

    def test_a_missing_declared_input_has_no_identity(self):
        model = self.model(root=self.root, inputs=('specifications/A/absent.ndjson',))
        self.assertIsNone(content_digest(model))

    def test_a_model_without_the_layout_keeps_its_identity(self):
        # Every other model keeps the digest it was measured under, so the
        # frozen report and its pinned input keys stay valid.
        plain = {'id': 'A', 'tla': self.tla, 'cfg': self.cfg}
        self.assertEqual(content_digest(plain), content_digest({**plain, 'flags': [], 'features': []}))

    def test_the_trace_bytes_are_part_of_the_identity(self):
        before = content_digest(self.model(root=self.root))
        with open(self.trace, 'w') as stream:
            stream.write('{"N": 1}\n')
        self.assertNotEqual(before, content_digest(self.model(root=self.root)))

    def test_the_oracle_tlc_arguments_are_part_of_the_identity(self):
        # The extra TLC arguments decide TLC's own counts, so two argument sets
        # are two inputs: the active pin's `generated` count stays deterministic
        # only while the key names the arguments (docs/compat.md D-25).
        base = self.model(root=self.root)
        self.assertNotEqual(content_digest(base), content_digest({**base, 'tlc_args': ['-fp', '0']}))
        self.assertNotEqual(content_digest({**base, 'tlc_args': ['-fp', '0']}),
                            content_digest({**base, 'tlc_args': ['-fp', '1']}))

    def test_relocated_identical_inputs_keep_their_identity(self):
        other = os.path.join(self.tmp.name, 'checkout')
        shutil.copytree(self.root, other)
        there = self.model(root=other, tla=os.path.join(other, 'specifications', 'A', 'A.tla'),
                           cfg=os.path.join(other, 'specifications', 'A', 'A.cfg'))
        self.assertEqual(content_digest(self.model(root=self.root)), content_digest(there))

    def test_the_working_directory_change_invalidates_reuse(self):
        # The pre-fix identity is spec, config and module closure, with no
        # layout: the model without the new fields still hashes to it, so the
        # old key matched the failing staging's evidence.
        without_layout = {k: v for k, v in self.model(root=self.root).items()
                          if k not in ('cwd', 'root', 'inputs')}
        next_to_spec = self.model(cwd=None, inputs=None)
        self.assertEqual(content_digest(without_layout), content_digest(next_to_spec))
        # With the layout the corrected staging is a different key, so a
        # collected baseline no longer satisfies it and the collection reruns.
        store_root = Path(self.tmp.name) / 'store'
        (store_root / 'bench').mkdir(parents=True)
        measured = Mock(return_value={'wall_s': 1, 'cpu_s': 1, 'result': 'success', 'distinct': 14})
        kw = dict(root=store_root, version='v', instance='SA5.4XLARGE32')
        cached_tlc(next_to_spec, 1, measured, **kw)
        cached_tlc(self.model(root=self.root), 1, measured, **kw)
        self.assertEqual(measured.call_count, 2)


class ArchivedSourceTest(unittest.TestCase):
    """A source retired from the tree keeps its provenance through the pin.

    Retiring a historical artifact is only sound because `bench/migration.json`
    pins the revision and the SHA-256 its bytes had there. Without a locator the
    gate refuses a stored measurement whose source is gone; with a locator that
    does not resolve it refuses that too, instead of reading the source as
    absent and quietly dropping the rows it still holds (HARNESS-18, DOC-06).
    """

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / 'bench').mkdir()
        (self.root / 'docs').mkdir()
        (self.root / 'bench/suite.json').write_text(json.dumps({'models': [{'id': 'M'}]}))
        self.git('-c', 'init.defaultBranch=main', 'init', '-q')
        self.git('config', 'user.name', 'Test Fixture')
        self.git('config', 'user.email', 'fixture@example.com')
        self.source = self.root / 'bench' / 'history' / 'old.json'
        self.source.parent.mkdir()
        self.source.write_text(json.dumps({'commit': 'abc', 'runs': {
            'M': {'model': 'M', 'mode': 'compile', 'workers': 1, 'wall_s': 2, 'result': 'success'}}}))
        ingest(self.source, self.root)
        br.generate(self.root)
        self.assertEqual(br.check(self.root), [])

    def git(self, *args):
        return subprocess.run(['git', *args], cwd=self.root, check=True,
                              capture_output=True, stdin=subprocess.DEVNULL)

    def commit_source(self):
        self.git('add', '-A')
        self.git('-c', 'commit.gpgsign=false', 'commit', '-qm', 'source')
        return self.git('rev-parse', 'HEAD').stdout.decode().strip()

    def pin(self, revision, sha):
        path = self.root / 'bench/migration.json'
        inventory = json.loads(path.read_text()) if path.exists() else {'schema_version': 1}
        inventory['archived_sources'] = {
            'revision': revision, 'sha256': {'bench/history/old.json': sha}}
        path.write_text(json.dumps(inventory, indent=2, sort_keys=True) + '\n')

    def refusal(self):
        """`check`'s problems, with a poisoned locator surfaced as its refusal.

        HARNESS-18: a retired source is only resolved provenance when its pinned
        revision and SHA-256 check out, so a locator that does not resolve is
        refused by name, never read as an absent source. `check` states that as
        a problem; when the forward source re-derivation reaches the poisoned
        locator before the reverse pass does, the same refusal is raised
        instead, so carry it through under the same name rather than letting it
        escape the report.
        """
        try:
            return br.check(self.root)
        except store.ArchiveError as error:
            return [f'archived provenance does not resolve ({error})']

    def test_pinned_locator_keeps_the_provenance_readable(self):
        revision = self.commit_source()
        self.pin(revision, hashlib.sha256(self.source.read_bytes()).hexdigest())
        self.source.unlink()
        self.assertEqual(self.refusal(), [])

    def test_a_locator_whose_bytes_differ_from_the_record_is_refused(self):
        revision = self.commit_source()
        self.pin(revision, '0' * 64)
        self.source.unlink()
        self.assertTrue(any('archived provenance does not resolve' in p for p in self.refusal()))

    def test_a_locator_whose_revision_does_not_resolve_is_refused(self):
        self.commit_source()
        self.pin('1' * 40, hashlib.sha256(self.source.read_bytes()).hexdigest())
        self.source.unlink()
        self.assertTrue(any('archived provenance does not resolve' in p for p in self.refusal()))

    def test_a_removed_source_without_a_locator_is_refused(self):
        self.source.unlink()
        self.assertTrue(any('source file is missing' in p for p in self.refusal()))


class LibraryBoundary(unittest.TestCase):
    """The store, its adapters and the baseline cache are a library, never the CLI.

    Entrypoints import them; they may not import an entrypoint back, directly or
    in a local import, or a benchmark lane would drag the whole command surface
    — its parser, its defaults and its module identity — into a measurement
    (HARNESS-03). The re-export list is asserted too: a name other callers still
    resolve through `bench_records` must not silently vanish from its imports.
    """

    ENTRYPOINTS = ('bench', 'benchmarking.bench_disk', 'benchmarking.bench_liveness', 'benchmarking.bench_profile', 'benchmarking.bench_records',
                   'benchmarking.bench_smoke', 'benchmarking.bench_suite', 'benchmarking.bench_ttfr', 'cloud_verify', 'coverage',
                   'doccheck', 'repr_check')

    def test_importing_the_library_loads_no_entrypoint(self):
        script = ('import sys; from benchmarking import baselines, legacy, records;'
                  ' loaded = sorted(m for m in sys.modules if m in %r); assert not loaded, loaded'
                  % (self.ENTRYPOINTS,))
        result = subprocess.run([sys.executable, '-c', script], cwd=Path(__file__).parent.parent,
                                capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)

    def test_library_modules_name_no_entrypoint(self):
        for module in (baselines, legacy, store):
            imported = set()
            for node in ast.walk(ast.parse(Path(module.__file__).read_text())):
                if isinstance(node, ast.Import):
                    imported.update(alias.name.split('.')[0] for alias in node.names)
                elif isinstance(node, ast.ImportFrom) and node.module:
                    imported.add(node.module.split('.')[0])
            self.assertEqual(imported & set(self.ENTRYPOINTS), set(), module.__name__)

    def test_entrypoint_reexports_the_library_names_callers_still_import(self):
        for name in ('ROOT', 'COMPLETE', 'load_records', 'validate', 'normalize', 'digest', 'dump',
                     'content_digest', 'cached_tlc', 'ingest', 'migrate',
                     'generate', 'check', 'render', 'eligible'):
            self.assertTrue(hasattr(br, name), name)



class StoreCoherenceTest(unittest.TestCase):
    """A baseline file must state as much as the source measurement it derives from.

    The store is derived: `migrate` reads the sources under `bench/` and writes
    the entry each TLC row implies, under the key's own file name. A file that is
    absent or weaker than the row it should hold means the store was edited by
    hand instead of re-derived, and every reader of the key (coverage by cause,
    A/B, `track`) would quote the wrong measurement. `benchmarking.bench_records.check` is the
    gate that says so, and it is what `doccheck` runs.

    The store read here is the one this test builds: the shipped measurement
    store is not part of the source tree, so a test that read `bench/records`
    would find nothing in a clone - and the coherence check would report no
    problem for an empty store, which is the failure mode this test exists to
    rule out.
    """

    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / 'bench').mkdir()
        (self.root / 'bench/suite.json').write_text(json.dumps({'models': [{'id': 'M'}]}))
        (self.root / 'bench/a.json').write_text(json.dumps(
            {'commit': 'abc', 'date': '2026-10-07', 'machine': 'x86_64, tencent SA5.4XLARGE32',
             'tla2tools': {'revision': '2026.10.02.163556'},
             'runs': {'M': {'model': 'M', 'mode': '-tlc', 'workers': 1, 'content_digest': 'digest',
                            'wall_s': 7, 'cpu_s': 5, 'result': 'success', 'distinct': 10}}}))
        migrate(self.root)
        br.generate(self.root)

    def baseline_file(self):
        """The one `bench/tlc-baselines/<key>.json` this test's source derives."""
        (path,) = sorted((self.root / 'bench/tlc-baselines').glob('*.json'))
        return path

    def test_migrated_store_is_coherent(self):
        self.assertTrue(self.baseline_file().is_file())
        self.assertEqual(br.check(self.root), [])

    def test_hand_weakened_baseline_is_reported(self):
        path = self.baseline_file()
        entry = json.loads(path.read_text())
        entry['measurement']['counts'] = {'generated': None, 'distinct': None, 'depth': None, 'result': 'timeout'}
        entry['measurement']['metrics']['wall_s'] = 1800.0
        path.write_text(json.dumps(entry))
        self.assertTrue(any('unimported/changed measurement' in p for p in br.check(self.root)),
                        'a baseline file that was weakened by hand must be a finding')

    def test_deleted_baseline_is_reported(self):
        self.baseline_file().unlink()
        self.assertTrue(any('unimported/changed measurement' in p for p in br.check(self.root)),
                        'a baseline file the source still produces must be a finding')


class TestStoreRootsTest(unittest.TestCase):
    """No test may point a store reader at the checkout.

    The shipped measurement store is not part of the source tree, so a test that
    reads `bench/records` or `bench/tlc-baselines` of the checkout finds nothing
    in a clone - and asserts nothing, or fails, there - while passing on a
    machine that still has the store on disk. That is the silent-skip failure
    mode this file's fixtures exist to rule out, so the shape is refused: every
    store reader takes a root, and the root a test passes must be its own.
    """

    # The modules whose callables read the store. A test that reaches one of
    # them and hands it the checkout root is the mistake this guards against;
    # `test_check_modes.check(root)` is a different `check` (a lint over
    # scripts/) and is not one of them.
    STORE_MODULES = ('benchmarking.bench_records', 'benchmarking.records', 'benchmarking.baselines', 'benchmarking.legacy')

    @classmethod
    def store_reachers(cls, tree):
        """(module aliases, directly imported names) through which a module reaches the store."""
        aliases, direct = set(), set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                aliases.update(a.asname or a.name.split('.')[0] for a in node.names
                               if a.name in cls.STORE_MODULES or a.name == 'benchmarking')
            elif isinstance(node, ast.ImportFrom):
                if node.module in cls.STORE_MODULES:
                    direct.update(a.asname or a.name for a in node.names)
                elif node.module == 'benchmarking' and any(a.name in ('records', 'baselines', 'legacy') for a in node.names):
                    aliases.update(a.asname or a.name for a in node.names if a.name in ('records', 'baselines', 'legacy'))
        return aliases, direct

    @staticmethod
    def checkout_paths(scope):
        """The names `scope` binds to a path derived from this repository's layout.

        A test usually does not pass the root expression straight to the reader -
        it binds `root = Path(__file__).resolve().parents[2]` first - so the
        names assigned from such an expression are followed to a fixed point,
        within the function that binds them (a name tainted in one test does not
        taint the same name in another).
        """
        names = set()

        def derived(expr):
            return ('parents' in ast.dump(expr)
                    or isinstance(expr, ast.Name) and expr.id in names
                    or isinstance(expr, ast.Attribute) and expr.attr in names)

        changed = True
        while changed:
            changed = False
            for node in ast.walk(scope):
                if isinstance(node, ast.Assign):
                    targets, value = node.targets, node.value
                elif isinstance(node, ast.AnnAssign) and node.value is not None:
                    targets, value = [node.target], node.value
                else:
                    continue
                if not derived(value):
                    continue
                for target in targets:
                    bound = target.id if isinstance(target, ast.Name) else \
                        target.attr if isinstance(target, ast.Attribute) else None
                    if bound and bound not in names:
                        names.add(bound)
                        changed = True
        return names

    def test_no_test_module_roots_a_store_reader_at_the_checkout(self):
        offenders = []
        for path in sorted(Path(__file__).parent.glob('test_*.py')):
            tree = ast.parse(path.read_text())
            aliases, direct = self.store_reachers(tree)
            scopes = [tree, *(n for n in ast.walk(tree) if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)))]
            for scope in scopes:
                checkout = self.checkout_paths(scope)
                for node in ast.walk(scope):
                    if not isinstance(node, ast.Call):
                        continue
                    func = node.func
                    reaches = ((isinstance(func, ast.Attribute) and isinstance(func.value, ast.Name)
                                and func.value.id in aliases)
                               or (isinstance(func, ast.Name) and func.id in direct))
                    if not reaches:
                        continue
                    roots = [*node.args, *(k.value for k in node.keywords if k.arg == 'root')]
                    if any(isinstance(a, ast.Name) and a.id in checkout for a in roots):
                        offenders.append(f'{path.name}:{node.lineno}: {ast.unparse(node)}')
        self.assertEqual(sorted(set(offenders)), [], 'a store reader is rooted at the checkout, not at a fixture')


if __name__ == '__main__':
    unittest.main()
