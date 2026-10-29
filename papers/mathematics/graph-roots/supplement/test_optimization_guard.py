"""Check safe startup without running graph enumeration or arithmetic diagnostics."""
from pathlib import Path
import os
import subprocess
import sys
import unittest

SCRIPT = Path(__file__).with_name('checks.py')

class OptimizationGuard(unittest.TestCase):
    def test_startup_modes(self):
        clean = {k: v for k, v in os.environ.items() if k != 'PYTHONOPTIMIZE'}
        cases = [('normal', [], None, True), ('-O', ['-O'], None, False),
                 ('-OO', ['-OO'], None, False), ('env1', [], '1', False),
                 ('env2', [], '2', False)]
        for name, flags, setting, allowed in cases:
            with self.subTest(mode=name):
                env = clean.copy()
                if setting is not None:
                    env['PYTHONOPTIMIZE'] = setting
                run = subprocess.run([sys.executable, *flags, str(SCRIPT), '--help'],
                                     env=env, capture_output=True, text=True, timeout=30)
                output = run.stdout + run.stderr
                if allowed:
                    self.assertEqual(run.returncode, 0, output)
                    self.assertIn('--max-n', output)
                else:
                    self.assertNotEqual(run.returncode, 0)
                    self.assertIn('optimized Python is not supported', output)
                    self.assertNotIn('PASS', output)

if __name__ == '__main__':
    unittest.main()
