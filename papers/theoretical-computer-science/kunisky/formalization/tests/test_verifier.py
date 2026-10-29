"""Test audit coverage and wrapper failures with a fake Lake command.

These tests do not start Lean or establish a formal verification result.
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
spec = importlib.util.spec_from_file_location("kunisky_check_axioms", PROJECT / "check_axioms.py")
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)


def fixture():
    return "\n".join(
        f"'{name}' depends on axioms: [propext, Classical.choice, Quot.sound]"
        for name in sorted(checker.EXPECTED)
    ) + "\n"


class AuditCoverageTests(unittest.TestCase):
    def test_exact_audit_name_coverage(self):
        names = re.findall(r"^#print axioms (\S+)", (PROJECT / "FinalAudit.lean").read_text(), re.M)
        self.assertEqual(len(names), 12)
        self.assertEqual(len(set(names)), 12)
        self.assertEqual(set(names), checker.EXPECTED)
        reports = checker.validate(fixture())
        self.assertEqual(set(reports), set(names))
        for name in names:
            with self.subTest(missing=name):
                reduced = "\n".join(line for line in fixture().splitlines()
                                    if not line.startswith(f"'{name}' "))
                with self.assertRaises(ValueError):
                    checker.validate(reduced)

    def run_wrapper(self, mode):
        with tempfile.TemporaryDirectory(prefix="kunisky-verifier-test-") as temporary:
            root = Path(temporary)
            fake = root / "lake"
            calls = root / "calls.jsonl"
            reports = root / "synthetic-audit.txt"
            reports.write_text(fixture())
            fake.write_text(
                "#!/usr/bin/env python3\n"
                "import json, os, pathlib, sys\n"
                "args = sys.argv[1:]\n"
                "with open(os.environ['KUNISKY_TEST_CALLS'], 'a') as stream:\n"
                "    stream.write(json.dumps(args) + '\\n')\n"
                "mode = os.environ['KUNISKY_TEST_MODE']\n"
                "if args == ['--no-cache', 'build']:\n"
                "    sys.exit(23 if mode == 'build-failure' else 0)\n"
                "if args == ['env', 'lean', '--trust=0', 'FinalAudit.lean']:\n"
                "    if mode != 'empty-audit':\n"
                "        print(pathlib.Path(os.environ['KUNISKY_TEST_REPORTS']).read_text(), end='')\n"
                "    sys.exit(37 if mode == 'audit-failure' else 0)\n"
                "sys.exit(91)\n"
            )
            fake.chmod(0o755)
            environment = dict(os.environ)
            environment.update({
                "PATH": str(root) + os.pathsep + environment.get("PATH", ""),
                "KUNISKY_TEST_CALLS": str(calls),
                "KUNISKY_TEST_REPORTS": str(reports),
                "KUNISKY_TEST_MODE": mode,
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
        self.assertIn("12 required declarations", result.stdout)
        self.assertEqual(commands, [["--no-cache", "build"],
                                   ["env", "lean", "--trust=0", "FinalAudit.lean"]])

    def test_failed_build_keeps_status_and_stops(self):
        result, commands = self.run_wrapper("build-failure")
        self.assertEqual(result.returncode, 23)
        self.assertEqual(commands, [["--no-cache", "build"]])

    def test_failed_audit_keeps_status_despite_valid_reports(self):
        result, commands = self.run_wrapper("audit-failure")
        self.assertEqual(result.returncode, 37)
        self.assertEqual(len(commands), 2)
        self.assertNotIn("Axiom audit accepted", result.stdout)

    def test_zero_status_without_audit_reports_is_rejected(self):
        result, commands = self.run_wrapper("empty-audit")
        self.assertEqual(result.returncode, 1)
        self.assertEqual(len(commands), 2)
        self.assertIn("empty axiom audit output", result.stderr)


if __name__ == "__main__":
    unittest.main()
