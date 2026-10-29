#!/usr/bin/env python3
"""Parser controls and wrapper failure tests; no Lean process is run."""
import importlib.util
import os
import re
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("check_axioms", ROOT / "check_axioms.py")
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)
FIXTURE = (ROOT / "tests" / "axioms-fixture.txt").read_text()


class ParserTests(unittest.TestCase):
    def test_supplied_format_covers_all_twelve(self):
        reports = CHECK.validate(FIXTURE)
        self.assertEqual(len(reports), 12)
        self.assertEqual(set(reports), CHECK.EXPECTED)

    def test_expected_names_match_all_source_audits(self):
        names = re.findall(r"^#print axioms (\S+)$",
                           (ROOT / "AxiomAudit.lean").read_text(), re.MULTILINE)
        self.assertEqual(len(names), 12)
        self.assertEqual(len(set(names)), 12)
        self.assertEqual(set(names), CHECK.EXPECTED)

    def test_missing_report(self):
        with self.assertRaises(ValueError):
            CHECK.validate("\n".join(FIXTURE.splitlines()[:-1]))

    def test_duplicate_report(self):
        with self.assertRaises(ValueError):
            CHECK.validate(FIXTURE + FIXTURE.splitlines()[0] + "\n")

    def test_forbidden_axiom(self):
        for forbidden in ["sorryAx", "Custom.axiom", "Lean.ofReduceBool"]:
            with self.subTest(forbidden=forbidden), self.assertRaises(ValueError):
                CHECK.validate(FIXTURE.replace("propext", forbidden, 1))

    def test_empty_and_truncated(self):
        for output in ["", "  \n", "theorem header only", FIXTURE[:-3]]:
            with self.subTest(output=output[-50:]), self.assertRaises(ValueError):
                CHECK.validate(output)

    def test_unknown_and_malformed_report(self):
        for output in [FIXTURE.replace("SidonRenyi.power_difference_lt", "Other.theorem", 1),
                       FIXTURE.replace("depends on axioms:", "depends on axioms", 1),
                       FIXTURE.replace("propext,", "propext,,", 1)]:
            with self.subTest(output=output[:90]), self.assertRaises(ValueError):
                CHECK.validate(output)

    def test_no_axioms_and_allowed_subsets(self):
        first = FIXTURE.splitlines()[0]
        for replacement in [first.split(" depends")[0] + " does not depend on any axioms",
                            first.split("[")[0] + "[propext]"]:
            self.assertEqual(len(CHECK.validate(FIXTURE.replace(first, replacement, 1))), 12)


class WrapperTests(unittest.TestCase):
    def run_wrapper(self, output=FIXTURE, build_exit=0, audit_exit=0):
        with tempfile.TemporaryDirectory(prefix="sidon-audit-test-") as directory:
            folder = Path(directory)
            for name in ["verify.sh", "check_axioms.py"]:
                shutil.copy2(ROOT / name, folder / name)
            fixture = folder / "output.txt"
            fixture.write_text(output)
            bindir = folder / "bin"
            bindir.mkdir()
            fake = bindir / "lake"
            fake.write_text("#!" + sys.executable + "\n" +
                "import os, pathlib, sys\n" +
                "if sys.argv[1:] == ['build']:\n" +
                "    sys.exit(int(os.environ['SIDON_TEST_BUILD_EXIT']))\n" +
                "if sys.argv[1:] != ['env', 'lean', 'AxiomAudit.lean']:\n" +
                "    sys.exit(99)\n" +
                "print(pathlib.Path(os.environ['SIDON_TEST_OUTPUT']).read_text(), end='')\n" +
                "sys.exit(int(os.environ['SIDON_TEST_AUDIT_EXIT']))\n")
            fake.chmod(0o755)
            env = dict(os.environ, PATH=str(bindir) + os.pathsep + os.environ["PATH"],
                       SIDON_TEST_BUILD_EXIT=str(build_exit),
                       SIDON_TEST_AUDIT_EXIT=str(audit_exit), SIDON_TEST_OUTPUT=str(fixture))
            return subprocess.run(["bash", str(folder / "verify.sh")], env=env,
                                  text=True, capture_output=True, check=False)

    def test_success_only_with_complete_valid_output(self):
        result = self.run_wrapper()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("12 required declarations", result.stdout)

    def test_build_failure_preserves_exit_code(self):
        result = self.run_wrapper(build_exit=23)
        self.assertEqual(result.returncode, 23)
        self.assertNotIn("accepted", result.stdout)

    def test_audit_failure_preserves_exit_code_even_with_valid_reports(self):
        result = self.run_wrapper(audit_exit=37)
        self.assertEqual(result.returncode, 37)
        self.assertNotIn("accepted", result.stdout)

    def test_zero_exit_with_incomplete_output_is_rejected(self):
        for output in ["", FIXTURE[:-3], "\n".join(FIXTURE.splitlines()[:-1]),
                       FIXTURE + FIXTURE.splitlines()[0],
                       FIXTURE.replace("propext", "sorryAx", 1)]:
            with self.subTest(output=output[-50:]):
                result = self.run_wrapper(output=output)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn("rejected", result.stderr)


if __name__ == "__main__":
    unittest.main()
