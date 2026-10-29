"""Exercise the published scoped-audit wrapper before expensive proof compilation."""
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
WRAPPER = ROOT / 'papers/mathematics/gyires/formalization/rank-two-eight-audit/check_audit.py'
ACCEPTED = ROOT / 'verification/records/gyires-rank-two-eight-scoped.log'


class RankTwoAuditTests(unittest.TestCase):
    def run_wrapper(self, log):
        return subprocess.run([sys.executable, '-B', str(WRAPPER), str(log)],
                              cwd=ROOT, capture_output=True, text=True, timeout=30)

    def test_published_wrapper_accepts_complete_record(self):
        result = self.run_wrapper(ACCEPTED)
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn('Six exact scoped audit reports passed.', result.stdout)

    def test_published_wrapper_rejects_missing_report(self):
        text = ACCEPTED.read_text()
        marker = "'RankTwoEightScopedAudit.strong_left_equality'"
        self.assertIn(marker, text)
        with tempfile.TemporaryDirectory() as directory:
            log = Path(directory) / 'incomplete.log'
            log.write_text(text[:text.index(marker)])
            result = self.run_wrapper(log)
        self.assertNotEqual(result.returncode, 0)
        self.assertNotIn('FileNotFoundError', result.stderr)
        self.assertIn('coverage', (result.stdout + result.stderr).lower())


if __name__ == '__main__':
    unittest.main()
