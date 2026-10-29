"""Check safe interpreter modes without running either arithmetic enumeration."""
from pathlib import Path
import os
import subprocess
import sys
import unittest

ROOT = Path(__file__).resolve().parent
MESSAGE = 'Optimization disables required arithmetic checks'


class OptimizationGuardTests(unittest.TestCase):
    def test_entry_points(self):
        for name in ('check_revision.py', 'check_original.py'):
            for options, optimization in (((), None), (('-O',), None),
                                          (('-OO',), None), ((), '1'), ((), '2')):
                with self.subTest(script=name, options=options, optimization=optimization):
                    environment = dict(os.environ)
                    environment.pop('PYTHONOPTIMIZE', None)
                    if optimization is not None:
                        environment['PYTHONOPTIMIZE'] = optimization
                    result = subprocess.run(
                        [sys.executable, *options, str(ROOT / name), '--help'],
                        env=environment, capture_output=True, text=True, timeout=10,
                        check=False)
                    if options or optimization:
                        self.assertNotEqual(result.returncode, 0)
                        self.assertIn(MESSAGE, result.stderr)
                        self.assertNotIn('PASS', result.stdout)
                    else:
                        self.assertEqual(result.returncode, 0, result.stderr)
                        self.assertIn('usage:', result.stdout)
                        self.assertNotIn(MESSAGE, result.stderr)


if __name__ == '__main__':
    unittest.main()
