"""Check publication boundaries and archive integrity."""
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
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
        (self.root / "catalogue.json").write_text(json.dumps({"families": [{"id": "example"}]}))
        self.names = sorted([MANIFEST, HASHES, "catalogue.json", "preprints/example/paper.pdf"])
        self.record()

    def record(self):
        (self.root / MANIFEST).write_text(json.dumps({"format_version": 1, "files": self.names}))
        hashes = {name: hashlib.sha256((self.root / name).read_bytes()).hexdigest()
                  for name in self.names if name != HASHES}
        (self.root / HASHES).write_text(json.dumps({"files": hashes}))

    def test_complete_package_matches_sources(self):
        self.assertEqual(verify(self.root), 3)
        output = Path(self.temp.name) / "packages"
        first = build(self.root, output)
        second = build(self.root, output)
        self.assertEqual(first, second)
        with zipfile.ZipFile(output / first[0]["archive"]) as bundle:
            self.assertEqual(set(bundle.namelist()),
                             {"PACKAGE.json", *(f"math-and-theory/{name}" for name in self.names)})
            for name in self.names:
                self.assertEqual(bundle.read(f"math-and-theory/{name}"), (self.root / name).read_bytes())

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


if __name__ == "__main__":
    unittest.main()
