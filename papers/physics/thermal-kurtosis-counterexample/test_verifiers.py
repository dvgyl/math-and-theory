"""Test failures for a corrupted thermal model and unverifiable dependencies."""

from pathlib import Path
import os
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parent


class VerifierTests(unittest.TestCase):
    def test_corrupt_model_always_fails(self):
        original = ROOT / "model_check.py"
        source = original.read_text()
        before = "ENERGY = [F(0), F(2), F(1)]"
        self.assertIn(before, source)
        with tempfile.TemporaryDirectory() as folder:
            corrupt = Path(folder) / "corrupt.py"
            corrupt.write_text(source.replace(before, "ENERGY = [F(0), F(2), F(2)]"))
            for mode in ["normal", "-O", "environment"]:
                args = [sys.executable]
                env = os.environ.copy()
                if mode == "-O":
                    args.append("-O")
                if mode == "environment":
                    env["PYTHONOPTIMIZE"] = "1"
                with self.subTest(mode=mode):
                    good = subprocess.run(args + [str(original)], env=env, capture_output=True)
                    bad = subprocess.run(args + [str(corrupt)], env=env, capture_output=True)
                    self.assertEqual(good.returncode, 0, good.stderr)
                    self.assertNotEqual(bad.returncode, 0)

    def test_missing_git_revision_fails(self):
        with tempfile.TemporaryDirectory() as folder:
            result = subprocess.run(["bash", str(ROOT / "verify.sh"), folder], capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(b"verifiable revision", result.stderr)

    def test_wrong_git_revision_fails(self):
        with tempfile.TemporaryDirectory() as folder:
            subprocess.run(["git", "init", "-q", folder], check=True)
            subprocess.run(["git", "-C", folder, "-c", "user.name=Test", "-c", "user.email=test@example.invalid",
                            "commit", "--allow-empty", "-qm", "Test revision"], check=True)
            result = subprocess.run(["bash", str(ROOT / "verify.sh"), folder], capture_output=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn(b"Wrong Mathlib revision", result.stderr)


if __name__ == "__main__":
    unittest.main()
