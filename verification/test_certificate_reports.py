#!/usr/bin/env python3
"""Test the rejection of incomplete and failed publication reports."""
import copy
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]


class CertificateReports(unittest.TestCase):
    def test_report_coverage(self):
        cases = [
            ('valid', None, None),
            ('partial alternative', 'permutation-alternative-finite.json',
             lambda d: d['results'].pop()),
            ('failed alternative', 'permutation-alternative-finite.json',
             lambda d: d['results'][0].update(negative=1)),
            ('empty permutation', 'independent_finite.json',
             lambda d: d.update(results=[])),
            ('missing circulant', 'circ_gap_n6_all_results.json',
             lambda d: d['chambers'].pop()),
            ('duplicate circulant', 'circ_gap_n7_all_results.json',
             lambda d: d['chambers'].__setitem__(0, copy.deepcopy(d['chambers'][1]))),
            ('sampled rank two', 'rank2_bernstein_certificate.json',
             lambda d: d.update(status='sampled')),
            ('partial rank two', 'rank2_bernstein_certificate.json',
             lambda d: d['records'].pop()),
            ('short coefficients', 'rank2_bernstein_certificate.json',
             lambda d: d['records'][0].update(coefficient_counts_strong_contraction=[17, 18])),
            ('failed cubic', 'deletion_n3_birkhoff.json',
             lambda d: d[0].update(negative=1)),
        ]
        for name, filename, change in cases:
            with self.subTest(case=name), tempfile.TemporaryDirectory() as tmp:
                directory = Path(tmp)
                for group, family in [('support', 'gyires-complete-support'),
                                      ('extensions', 'gyires-extensions')]:
                    (directory / group).mkdir()
                    for source in (ROOT / 'research-notes' / family / 'results').glob('*.json'):
                        shutil.copyfile(source, directory / group / source.name)
                if filename is not None:
                    path = next(directory.glob('*/' + filename))
                    report = json.loads(path.read_text())
                    change(report)
                    path.write_text(json.dumps(report))
                result = subprocess.run(
                    [sys.executable, str(ROOT / 'verification/check_gyires_certificates.py'),
                     '--support', str(directory / 'support'),
                     '--extensions', str(directory / 'extensions')],
                    capture_output=True, text=True, timeout=20)
                output = json.loads(result.stdout)
                self.assertEqual(result.returncode == 0, name == 'valid', result.stdout + result.stderr)
                self.assertEqual(output['status'], 'PASS' if name == 'valid' else 'FAIL')
                self.assertEqual(bool(output['errors']), name != 'valid')


if __name__ == '__main__':
    unittest.main()
