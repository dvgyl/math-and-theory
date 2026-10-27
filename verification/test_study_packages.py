"""Reject incomplete or changed study proof records."""
from pathlib import Path
import copy
import json
import shutil
import tempfile
import unittest
from check_study_packages import check, check_audit

ROOT = Path(__file__).resolve().parent


class StudyPackageTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.package = Path(self.temp.name) / "sharp-eighth"
        shutil.copytree(ROOT / "additional-proofs/sharp-eighth", self.package)
        self.manifest = json.loads((self.package / "manifest.json").read_text())
        self.record = self.package / "verification/source-checks.json"
        self.evidence = json.loads(self.record.read_text())

    def test_complete_record_passes(self):
        check(self.package, "sharp-eighth", self.manifest)

    def test_incomplete_and_invalid_records_fail(self):
        mutations = {
            "incomplete": lambda x: x.update(complete=False),
            "missing source": lambda x: x["sources"].pop(),
            "repeated source": lambda x: x["sources"].__setitem__(1, copy.deepcopy(x["sources"][0])),
            "failed compiler": lambda x: x["sources"][0].update(compiler_exit_code=1),
            "boolean exit code": lambda x: x["sources"][0].update(compiler_exit_code=False),
            "float exit code": lambda x: x["sources"][0].update(compiler_exit_code=0.0),
            "boolean format": lambda x: x.update(format_version=True),
            "float count": lambda x: x.update(axiom_report_count=12.0),
            "wrong source": lambda x: x["sources"][0].update(source_sha256="0" * 64),
            "missing object": lambda x: x["sources"][0].pop("object_sha256"),
            "wrong log": lambda x: x["sources"][0].update(log_sha256="0" * 64),
            "missing report": lambda x: x["sources"][-1]["axiom_reports"].pop(),
            "wrong toolchain": lambda x: x.update(lean_version="4.0.0"),
        }
        for label, mutate in mutations.items():
            with self.subTest(label=label):
                evidence = copy.deepcopy(self.evidence)
                mutate(evidence)
                self.record.write_text(json.dumps(evidence))
                with self.assertRaises(ValueError):
                    check(self.package, "sharp-eighth", self.manifest)

    def test_missing_extra_and_unsafe_audit_reports_fail(self):
        output = (self.package / "verification/compile/Audit.txt").read_text()
        failures = ["", output + "\n'unexpected' does not depend on any axioms\n",
                    output.replace("propext", "sorryAx", 1), "warning: failed check\n" + output,
                    output + "\n'extra' depends on axioms: [sorryAx] trailing text\n",
                    output.replace("propext", "propext, propext", 1),
                    output.replace("propext", "propext, ", 1)]
        for value in failures:
            with self.subTest(output=value[:40]):
                with self.assertRaises(ValueError):
                    check_audit(self.package, "sharp-eighth", value)


class QuarticAuditTests(unittest.TestCase):
    def setUp(self):
        self.package = ROOT / "additional-proofs/quartic-rankings"
        self.output = (self.package / "verification/compile/PermEntropy.Verification.txt").read_text()

    def test_complete_kernel_audit_passes(self):
        self.assertEqual(check_audit(self.package, "quartic-rankings", self.output), 5)

    def test_incomplete_kernel_audits_fail(self):
        endpoint = next(line for line in self.output.splitlines() if line.startswith("Endpoint checked as theorem: "))
        summary = next(line for line in self.output.splitlines() if line.startswith("Verified transitive axiom whitelist for "))
        failures = {
            "missing endpoint": self.output.replace(endpoint, "", 1),
            "repeated endpoint": self.output + "\n" + endpoint + "\n",
            "missing summary": self.output.replace(summary, "", 1),
            "repeated summary": self.output + "\n" + summary + "\n",
            "wrong theorem count": self.output.replace("238 project theorem", "237 project theorem", 1),
            "wrong helper count": self.output.replace("17 private helper", "16 private helper", 1),
        }
        for label, output in failures.items():
            with self.subTest(label=label), self.assertRaises(ValueError):
                check_audit(self.package, "quartic-rankings", output)

if __name__ == "__main__":
    unittest.main()
