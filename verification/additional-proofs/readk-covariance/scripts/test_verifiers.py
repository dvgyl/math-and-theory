"""Test verifier failures with incomplete reports and corrupted witnesses."""

from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest

import check_audit

ROOT = Path(__file__).resolve().parents[1]


class VerifierTests(unittest.TestCase):
    def setUp(self):
        self.names = (ROOT / "verification/theorem-list.txt").read_text().splitlines()
        self.reports = [f"'{name}' depends on axioms: [propext,\n Classical.choice, Quot.sound]\n" for name in self.names]

    def test_complete_reports(self):
        self.assertEqual(check_audit.check("".join(self.reports)), len(self.names))
        empty = "\n".join(f"'{name}' does not depend on any axioms" for name in self.names)
        self.assertEqual(check_audit.check(empty), len(self.names))

    def test_invalid_reports(self):
        complete = "".join(self.reports)
        cases = {
            "missing": "".join(self.reports[1:]),
            "duplicate": complete + self.reports[0],
            "unexpected": complete + "'other' depends on axioms: [propext]\n",
            "names only": "\n".join(repr(name) for name in self.names) + "\n'other' depends on axioms: [propext]\n",
            "forbidden": complete.replace("propext", "sorryAx", 1),
            "malformed": complete.replace("[propext,", "[propext,,", 1),
            "truncated": complete[:-3],
            "compiler error": complete + "Audit.lean:1:0: error: failed\n",
        }
        for name, text in cases.items():
            with self.subTest(name=name), self.assertRaises(ValueError):
                check_audit.check(text)

    def test_corrupt_witness_always_fails(self):
        original = ROOT / "scripts/finite_checks.py"
        source = original.read_text()
        before = "got_covariance == expected_covariance"
        self.assertIn(before, source)
        with tempfile.TemporaryDirectory() as folder:
            corrupt = Path(folder) / "corrupt.py"
            corrupt.write_text(source.replace(before, "got_covariance == expected_covariance + 1"))
            for mode in ["normal", "-O", "environment"]:
                env = os.environ.copy()
                args = [sys.executable]
                if mode == "-O":
                    args.append("-O")
                if mode == "environment":
                    env["PYTHONOPTIMIZE"] = "1"
                with self.subTest(mode=mode):
                    good = subprocess.run(args + [str(original)], env=env, capture_output=True)
                    bad = subprocess.run(args + [str(corrupt)], env=env, capture_output=True)
                    self.assertEqual(good.returncode, 0, good.stderr)
                    self.assertNotEqual(bad.returncode, 0)


if __name__ == "__main__":
    unittest.main()
