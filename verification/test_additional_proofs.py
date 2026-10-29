"""Reject changed packages and incomplete proof evidence."""
from repository_layout import family_root

import hashlib
import json
from pathlib import Path
import shutil
import tempfile
import unittest

from check_embedded_packages import (
    EXPECTED_MANIFESTS, check_manifest, check_readk, check_thermal, thermal_axioms,
)
from catalogue_paths import load_families


ROOT = Path(__file__).resolve().parents[1]



class AdditionalProofTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.readk = Path(self.temp.name) / "readk-covariance"
        self.thermal = Path(self.temp.name) / "thermal-kurtosis-counterexample"
        shutil.copytree(ROOT / family_root(self.readk.name), self.readk)
        shutil.copytree(ROOT / family_root(self.thermal.name), self.thermal)

    def test_release_members_and_evidence_pass(self):
        readk = check_manifest(self.readk, EXPECTED_MANIFESTS[self.readk.name])
        thermal = check_manifest(self.thermal, EXPECTED_MANIFESTS[self.thermal.name])
        check_readk(self.readk, readk)
        check_thermal(self.thermal, thermal)

    def test_changed_member_fails(self):
        proof = self.readk / "Research.lean"
        proof.write_bytes(proof.read_bytes() + b"\n")
        with self.assertRaisesRegex(ValueError, "Changed package file"):
            check_manifest(self.readk, EXPECTED_MANIFESTS[self.readk.name])

    def test_unlisted_file_and_symbolic_link_fail(self):
        (self.thermal / "extra.txt").write_text("unlisted")
        with self.assertRaisesRegex(ValueError, "coverage differs"):
            check_manifest(self.thermal, EXPECTED_MANIFESTS[self.thermal.name])
        (self.thermal / "extra.txt").unlink()
        (self.thermal / "extra.txt").symlink_to(self.thermal / "README.md")
        with self.assertRaisesRegex(ValueError, "Symbolic link"):
            check_manifest(self.thermal, EXPECTED_MANIFESTS[self.thermal.name])

    def test_readk_missing_source_record_fails(self):
        manifest = check_manifest(self.readk, EXPECTED_MANIFESTS[self.readk.name])
        path = self.readk / "verification/source-checks.json"
        record = json.loads(path.read_text())
        record["sources"].pop()
        path.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, "source count"):
            check_readk(self.readk, manifest)

    def test_thermal_failed_compiler_record_fails(self):
        manifest = check_manifest(self.thermal, EXPECTED_MANIFESTS[self.thermal.name])
        path = self.thermal / "source-checks.json"
        record = json.loads(path.read_text())
        record["compiler_exit_code"] = 1
        path.write_text(json.dumps(record))
        with self.assertRaisesRegex(ValueError, "compiler evidence"):
            check_thermal(self.thermal, manifest)

    def test_thermal_axiom_output_failures(self):
        source = (self.thermal / "ThermalKurtosis.lean").read_text()
        output = (self.thermal / "verification.log").read_text()
        self.assertEqual(thermal_axioms(source, output), 2)
        reports = [line for line in output.splitlines() if "depends on axioms" in line]
        for broken in (
            output.replace(reports[0], ""),
            output + reports[0] + "\n",
            output.replace("propext", "sorryAx", 1),
            output.replace("[propext,", "[propext,,", 1),
            output + "ThermalKurtosis.lean:1:1: error: failed\n",
        ):
            with self.subTest(broken=hashlib.sha256(broken.encode()).hexdigest()[:8]):
                with self.assertRaises(ValueError):
                    thermal_axioms(source, broken)

    def test_standalone_catalogue_rejects_cross_package_manuscript(self):
        root = Path(self.temp.name) / "catalogue-root"
        package = root / "papers/mathematics/example"
        package.mkdir(parents=True)
        (package / "report.pdf").write_bytes(b"PDF")
        (package / "report.tex").write_text("TeX")
        family = {"id": "example", "discipline": "Mathematics", "paper": "papers/mathematics/example/report.pdf",
                  "formalization": {"kind": "standalone", "root": "papers/mathematics/example"}}
        catalogue = {"schema_version": 1, "families": [family]}
        (root / "catalogue.json").write_text(json.dumps(catalogue))
        self.assertEqual(len(load_families(root)), 1)
        family["formalization"]["root"] = "papers/mathematics/other"
        (root / "catalogue.json").write_text(json.dumps(catalogue))
        with self.assertRaisesRegex(ValueError, "Invalid standalone route"):
            load_families(root)



if __name__ == "__main__":
    unittest.main()
