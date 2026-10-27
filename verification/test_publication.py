"""Check publication boundaries and archive integrity."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import zipfile

from build_archives import build
from publication_files import HASHES, MANIFEST, load_publication_files
from verify_hashes import verify


class PublicationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "source"
        (self.root / "verification/records").mkdir(parents=True)
        (self.root / "preprints/example").mkdir(parents=True)
        (self.root / "preprints/example/paper.pdf").write_bytes(b"PDF fixture")
        (self.root / "preprints/example/paper.tex").write_text("TeX fixture")
        (self.root / "catalogue.json").write_text(json.dumps({"schema_version": 1, "families": [
            {"id": "example", "paper": "preprints/example/paper.pdf",
             "formalization": {"kind": "comparator"}, "module": "Example", "namespace": "Example",
             "comparator": "lean/comparator/example.json", "theorems": []}]}))
        self.names = sorted([MANIFEST, HASHES, "catalogue.json", "preprints/example/paper.pdf",
                             "preprints/example/paper.tex"])
        self.record()

    def record(self):
        (self.root / MANIFEST).write_text(json.dumps({"format_version": 1, "files": self.names}))
        hashes = {name: hashlib.sha256((self.root / name).read_bytes()).hexdigest()
                  for name in self.names if name != HASHES}
        (self.root / HASHES).write_text(json.dumps({"files": hashes}))

    def test_complete_package_matches_sources(self):
        self.assertEqual(verify(self.root), 4)
        output = Path(self.temp.name) / "packages"
        first = build(self.root, output)
        second = build(self.root, output)
        self.assertEqual(first, second)
        with zipfile.ZipFile(output / first[0]["archive"]) as bundle:
            self.assertEqual(set(bundle.namelist()),
                             {"PACKAGE.json", *(f"math-and-theory/{name}" for name in self.names)})
            for name in self.names:
                self.assertEqual(bundle.read(f"math-and-theory/{name}"), (self.root / name).read_bytes())

    def test_archive_families_use_the_saved_catalogue(self):
        catalogue_path = self.root / "catalogue.json"
        catalogue = json.loads(catalogue_path.read_text())
        second = dict(catalogue["families"][0], id="second", paper="preprints/second/paper.pdf",
                      comparator="lean/comparator/second.json")
        catalogue["families"].append(second)
        (self.root / "preprints/second").mkdir()
        for suffix in ("pdf", "tex"):
            name = f"preprints/second/paper.{suffix}"
            (self.root / name).write_bytes(b"Second manuscript")
            self.names.append(name)
        self.names.sort()
        catalogue_path.write_text(json.dumps(catalogue))
        self.record()
        saved_catalogue = catalogue_path.read_bytes()
        read_bytes = Path.read_bytes

        def change_catalogue_after_snapshot(path):
            data = read_bytes(path)
            if path == (self.root / HASHES).resolve():
                changed = dict(catalogue, families=catalogue["families"][:1])
                catalogue_path.write_text(json.dumps(changed))
            return data

        output = Path(self.temp.name) / "packages"
        with patch.object(Path, "read_bytes", change_catalogue_after_snapshot):
            result = build(self.root, output)
        self.assertEqual({item["family"] for item in result}, {"example", "second"})
        self.assertNotEqual(catalogue_path.read_bytes(), saved_catalogue)
        for item in result:
            with zipfile.ZipFile(output / item["archive"]) as bundle:
                self.assertEqual(bundle.read("math-and-theory/catalogue.json"), saved_catalogue)

    def test_unlisted_file_fails(self):
        (self.root / "unlisted.txt").write_text("unlisted")
        with self.assertRaises(ValueError):
            load_publication_files(self.root)

    def test_missing_file_fails(self):
        (self.root / "preprints/example/paper.pdf").unlink()
        with self.assertRaises(ValueError):
            verify(self.root)

    def test_changed_file_fails(self):
        (self.root / "preprints/example/paper.pdf").write_bytes(b"changed")
        with self.assertRaises(ValueError):
            verify(self.root)

    def test_incomplete_hash_record_fails(self):
        (self.root / HASHES).write_text(json.dumps({"files": {}}))
        with self.assertRaises(ValueError):
            verify(self.root)

    def test_invalid_manifest_paths_fail(self):
        for names in [[], ["../escape"], ["/absolute"], [".git/config"], ["a\\b"],
                      [MANIFEST, MANIFEST]]:
            with self.subTest(names=names):
                (self.root / MANIFEST).write_text(json.dumps({"format_version": 1, "files": names}))
                with self.assertRaises(ValueError):
                    load_publication_files(self.root)

    def test_symbolic_link_fails(self):
        target = self.root / "preprints/example/paper.pdf"
        target.unlink()
        target.symlink_to(self.root / "catalogue.json")
        with self.assertRaises(ValueError):
            verify(self.root)

    def test_output_inside_source_fails(self):
        with self.assertRaises(ValueError):
            build(self.root, self.root / "packages")

    def test_output_links_cannot_modify_sources(self):
        output = Path(self.temp.name) / "packages"
        output.mkdir()
        source = self.root / "catalogue.json"
        before = source.read_bytes()
        for name in ["example.pdf", "example-archival-package.zip", "packages.json"]:
            with self.subTest(name=name):
                link = output / name
                link.symlink_to(source)
                with self.assertRaises(ValueError):
                    build(self.root, output)
                self.assertEqual(source.read_bytes(), before)
                link.unlink()

    def test_output_directory_link_cannot_target_sources(self):
        output = Path(self.temp.name) / "packages"
        output.symlink_to(self.root, target_is_directory=True)
        with self.assertRaises(ValueError):
            build(self.root, output)

    def test_invalid_family_identifiers_fail(self):
        output = Path(self.temp.name) / "packages"
        for names in [["../escape"], ["/absolute"], ["example", "example"], []]:
            with self.subTest(names=names):
                (self.root / "catalogue.json").write_text(json.dumps({"families": [{"id": name} for name in names]}))
                self.record()
                with self.assertRaises(ValueError):
                    build(self.root, output)

    def test_standalone_manuscript_outside_preprints(self):
        package = self.root / "verification/additional-proofs/example-standalone"
        package.mkdir(parents=True)
        (package / "report.pdf").write_bytes(b"Standalone PDF")
        (package / "report.tex").write_text("Standalone TeX")
        catalogue = json.loads((self.root / "catalogue.json").read_text())
        catalogue["families"].append({
            "id": "example-standalone",
            "paper": "verification/additional-proofs/example-standalone/report.pdf",
            "formalization": {"kind": "standalone", "root": "verification/additional-proofs/example-standalone"},
        })
        (self.root / "catalogue.json").write_text(json.dumps(catalogue))
        self.names.extend(["verification/additional-proofs/example-standalone/report.pdf",
                           "verification/additional-proofs/example-standalone/report.tex"])
        self.names.sort()
        self.record()
        output = Path(self.temp.name) / "packages"
        evidence = {"example-standalone": {"formal_scope": "Finite example.",
                                           "lean_version": "4.19.0", "mathlib_revision": "a" * 40}}
        with patch("build_archives.check_packages", return_value=evidence), \
             patch.dict("build_archives.EXPECTED_MANIFESTS", {"example-standalone": "b" * 64}):
            first = build(self.root, output)
            second = build(self.root, output)
        self.assertEqual(first, second)
        self.assertEqual(len(first), 2)
        self.assertEqual((output / "example-standalone.pdf").read_bytes(), b"Standalone PDF")
        with zipfile.ZipFile(output / "example-standalone-archival-package.zip") as bundle:
            metadata = json.loads(bundle.read("PACKAGE.json"))
            self.assertEqual(metadata["manuscript"],
                             "math-and-theory/verification/additional-proofs/example-standalone/report.pdf")
            self.assertEqual(metadata["formalization"]["kind"], "standalone")
            for name in self.names:
                self.assertEqual(bundle.read(f"math-and-theory/{name}"), (self.root / name).read_bytes())


if __name__ == "__main__":
    unittest.main()
