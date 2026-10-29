"""Test the replay helper with synthetic output and a fake Lake executable.

These tests do not run Lean or establish formal verification.
"""
import importlib.util
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile
import unittest

PROJECT = Path(__file__).resolve().parents[1]
AUDIT_FILE = 'ReplayAudit.lean'
MODULES = ['KovacecCertificate', 'KovacecJordan', 'KovacecBoundary', 'RayExterior', 'RayComponent', 'KovacecGraph', 'KovacecLoop', 'KovacecResolution', 'Kovacec']
REPORT_COUNT = 6
spec = importlib.util.spec_from_file_location("replay_check_axioms", PROJECT / "check_axioms.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


def fixture():
    return "\n".join(
        f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
        for name in sorted(checker.EXPECTED)
    ) + "\n"


class ReplayHelperTests(unittest.TestCase):
    def test_exact_audit_name_coverage(self):
        names = re.findall(r"^#print axioms (\S+)", (PROJECT / AUDIT_FILE).read_text(), re.M)
        self.assertEqual(len(names), REPORT_COUNT)
        self.assertEqual(len(set(names)), REPORT_COUNT)
        self.assertEqual(set(names), checker.EXPECTED)
        self.assertEqual(set(checker.validate(fixture())), set(names))
        for name in names:
            with self.subTest(missing=name):
                reduced = "\n".join(line for line in fixture().splitlines()
                                    if not line.startswith(f"'{name}' "))
                with self.assertRaises(ValueError):
                    checker.validate(reduced)

    def run_wrapper(self, mode):
        with tempfile.TemporaryDirectory(prefix="replay-helper-test-") as temporary:
            root = Path(temporary)
            fake = root / "lake"
            calls = root / "calls.jsonl"
            reports = root / "synthetic-audit.txt"
            reports.write_text(fixture())
            fake.write_text(
                "#!/usr/bin/env python3\n"
                "import json, os, pathlib, sys\n"
                "args = sys.argv[1:]\n"
                "with open(os.environ['REPLAY_TEST_CALLS'], 'a') as stream:\n"
                "    stream.write(json.dumps(args) + '\\n')\n"
                "mode = os.environ['REPLAY_TEST_MODE']\n"
                "if args[:2] == ['--no-cache', 'build']:\n"
                "    sys.exit(23 if mode == 'build-failure' else 0)\n"
                "if args == ['env', 'lean', '--trust=0', os.environ['REPLAY_TEST_AUDIT']]:\n"
                "    if mode != 'empty-audit':\n"
                "        print(pathlib.Path(os.environ['REPLAY_TEST_REPORTS']).read_text(), end='')\n"
                "    sys.exit(37 if mode == 'audit-failure' else 0)\n"
                "sys.exit(91)\n"
            )
            fake.chmod(0o755)
            environment = dict(os.environ)
            environment.update({
                "PATH": str(root) + os.pathsep + environment.get("PATH", ""),
                "REPLAY_TEST_CALLS": str(calls),
                "REPLAY_TEST_REPORTS": str(reports),
                "REPLAY_TEST_MODE": mode,
                "REPLAY_TEST_AUDIT": AUDIT_FILE,
                "PYTHONDONTWRITEBYTECODE": "1",
            })
            result = subprocess.run(["bash", str(PROJECT / "build.sh")], env=environment,
                                    text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                    check=False)
            commands = [json.loads(line) for line in calls.read_text().splitlines()]
            return result, commands

    def test_complete_synthetic_audit_succeeds(self):
        result, commands = self.run_wrapper("success")
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn(f"{REPORT_COUNT} required declarations", result.stdout)
        expected = [["--no-cache", "build", module] for module in MODULES]
        expected += [["--no-cache", "build"], ["env", "lean", "--trust=0", AUDIT_FILE]]
        self.assertEqual(commands, expected)

    def test_failed_build_keeps_status_and_stops(self):
        result, commands = self.run_wrapper("build-failure")
        self.assertEqual(result.returncode, 23)
        self.assertEqual(commands, [["--no-cache", "build", MODULES[0]]])

    def test_failed_audit_keeps_status_despite_valid_reports(self):
        result, commands = self.run_wrapper("audit-failure")
        self.assertEqual(result.returncode, 37)
        self.assertEqual(len(commands), len(MODULES) + 2)
        self.assertNotIn("Axiom audit accepted", result.stdout)

    def test_empty_audit_is_rejected(self):
        result, commands = self.run_wrapper("empty-audit")
        self.assertEqual(result.returncode, 1)
        self.assertEqual(len(commands), len(MODULES) + 2)
        self.assertIn("empty axiom audit output", result.stderr)


if __name__ == "__main__":
    unittest.main()
