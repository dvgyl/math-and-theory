"""Check the numerical sampler's input and completion behavior."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


class SparseSamplerTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        compiler = shutil.which("c++")
        if compiler is None:
            raise RuntimeError("The sampler tests require a C++ compiler.")
        cls.directory = tempfile.TemporaryDirectory()
        cls.binary = str(Path(cls.directory.name) / "sampler")
        source = Path(__file__).resolve().parents[1] / "papers/mathematics/gyires/research-notes/complete-support/exploratory-data/sparse_regular_sampler.cpp"
        subprocess.run([compiler, "-std=c++17", "-O2", "-Wall", "-Wextra", "-Werror", str(source), "-o", cls.binary], check=True, capture_output=True)

    @classmethod
    def tearDownClass(cls):
        cls.directory.cleanup()

    def test_invalid_requests_fail(self):
        for arguments in [("4", "5", "1"), ("4", "0", "1"), ("4", "2", "0"), ("23", "2", "1"), ("0", "1", "1"), ("bad",), ("4x",), ("-1",), ("4", "2", "1", "extra")]:
            with self.subTest(arguments=arguments):
                result = subprocess.run([self.binary, *arguments], capture_output=True, text=True, timeout=5)
                self.assertEqual(result.returncode, 2)
                self.assertEqual(result.stdout, "")
                self.assertNotIn("Completed", result.stderr)

    def test_requested_samples_are_reported(self):
        result = subprocess.run([self.binary, "4", "2", "3"], capture_output=True, text=True, timeout=5)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(len(result.stdout.splitlines()), 3)
        for index, line in enumerate(result.stdout.splitlines()):
            self.assertTrue(line.startswith(f"4 2 {index} per="))
            self.assertGreaterEqual(float(line.split("ratio=")[1]), 1)
        self.assertIn("Completed 3 numerical samples.", result.stderr)


if __name__ == "__main__":
    unittest.main()
