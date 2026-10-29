"""Check publication boundaries and archive integrity."""
import hashlib
import json
from pathlib import Path
import tempfile
import shutil
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
        (self.root / "papers/mathematics/example").mkdir(parents=True)
        (self.root / "papers/mathematics/example/paper.pdf").write_bytes(b"PDF fixture")
        (self.root / "papers/mathematics/example/paper.tex").write_text("TeX fixture")
        (self.root / "catalogue.json").write_text(json.dumps({"schema_version": 1, "families": [
            {"id": "example", "discipline": "Mathematics", "paper": "papers/mathematics/example/paper.pdf",
             "formalization": {"kind": "comparator"}, "module": "Example", "namespace": "Example",
             "comparator": "lean/comparator/mathematics/example.json", "theorems": []}]}))
        self.names = sorted([MANIFEST, HASHES, "catalogue.json", "papers/mathematics/example/paper.pdf",
                             "papers/mathematics/example/paper.tex"])
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
        second = dict(catalogue["families"][0], id="second", paper="papers/mathematics/second/paper.pdf",
                      comparator="lean/comparator/mathematics/second.json")
        catalogue["families"].append(second)
        (self.root / "papers/mathematics/second").mkdir()
        for suffix in ("pdf", "tex"):
            name = f"papers/mathematics/second/paper.{suffix}"
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
        (self.root / "papers/mathematics/example/paper.pdf").unlink()
        with self.assertRaises(ValueError):
            verify(self.root)

    def test_changed_file_fails(self):
        (self.root / "papers/mathematics/example/paper.pdf").write_bytes(b"changed")
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
        target = self.root / "papers/mathematics/example/paper.pdf"
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
        for name in ["example.pdf", "math-and-theory-source.zip", "packages.json"]:
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

    def test_real_legacy_and_curated_packages_share_one_complete_archive(self):
        # Exercise the actual package validators: mocking them hid missing
        # snapshot registry files and legacy-only metadata assumptions.
        source = Path(__file__).resolve().parents[1]
        selected = {"sharp-eighth", "projection-amgm"}
        source_catalogue = json.loads((source / "catalogue.json").read_text())
        families = [f for f in source_catalogue["families"] if f["id"] in selected]
        catalogue = json.loads((self.root / "catalogue.json").read_text())
        catalogue["families"].extend(families)
        (self.root / "catalogue.json").write_text(json.dumps(catalogue))
        for family in families:
            name = family["formalization"]["root"]
            shutil.copytree(source / name, self.root / name)
        registry = json.loads((source / "verification/curated-packages.json").read_text())
        registry["packages"] = {"projection-amgm": registry["packages"]["projection-amgm"]}
        (self.root / "verification/curated-packages.json").write_text(json.dumps(registry))
        self.names = sorted(p.relative_to(self.root).as_posix()
                            for p in self.root.rglob("*") if p.is_file())
        self.record()
        from check_embedded_packages import EXPECTED_MANIFESTS
        legacy = {"sharp-eighth": EXPECTED_MANIFESTS["sharp-eighth"]}
        output = Path(self.temp.name) / "packages"
        with patch.dict(EXPECTED_MANIFESTS, legacy, clear=True), \
             patch("check_curated_packages.CURATED_IDS", frozenset({"projection-amgm"})):
            first = build(self.root, output)
            second = build(self.root, output)
        self.assertEqual(first, second)
        self.assertEqual(len(first), 3)
        self.assertEqual(len(list(output.glob("*.zip"))), 1)
        self.assertEqual({row["archive"] for row in first}, {"math-and-theory-source.zip"})
        with zipfile.ZipFile(output / first[0]["archive"]) as bundle:
            metadata = json.loads(bundle.read("PACKAGE.json"))
            self.assertEqual(metadata["format_version"], 2)
            rows = {row["family"]: row for row in metadata["manuscripts"]}
            self.assertEqual(rows["sharp-eighth"]["formalization"]["manifest_sha256"],
                             legacy["sharp-eighth"])
            proof = rows["projection-amgm"]["formalization"]
            self.assertEqual(proof["manifest_sha256"],
                             registry["packages"]["projection-amgm"]["release_manifest_sha256"])
            self.assertEqual(proof["proof_roots"], registry["packages"]["projection-amgm"]["proof_roots"])
            for name in self.names:
                self.assertEqual(bundle.read(f"math-and-theory/{name}"), (self.root / name).read_bytes())
        # Refreshing the collection hash must not excuse a corrupted inner package.
        damaged = self.root / "papers/mathematics/projection-amgm/README.md"
        damaged.write_text(damaged.read_text() + "\nUnreviewed change.\n")
        self.record()
        with patch.dict(EXPECTED_MANIFESTS, legacy, clear=True), \
             patch("check_curated_packages.CURATED_IDS", frozenset({"projection-amgm"})):
            with self.assertRaisesRegex(ValueError, "Changed curated file"):
                build(self.root, output)


class LayoutTests(unittest.TestCase):
    def test_route_requires_registered_family_or_explicit_discipline(self):
        from repository_layout import family_root
        with self.assertRaisesRegex(ValueError, "Unregistered"):
            family_root("unregistered-result")
        self.assertEqual(family_root("unregistered-result", "Mathematics"),
                         "papers/mathematics/unregistered-result")

    def test_route_rejects_unsafe_names_and_unknown_subjects(self):
        from repository_layout import family_root
        for name in ("../outside", "UpperCase", "a/b", ""):
            with self.assertRaises(ValueError):
                family_root(name, "Mathematics")
        with self.assertRaisesRegex(ValueError, "Unknown discipline"):
            family_root("example", "Unknown")

    def test_companions_share_their_family(self):
        from repository_layout import family_root
        self.assertEqual(family_root("motzkin-bounded-forcing"),
                         family_root("alternating-motzkin") + "/bounded-forcing")


if __name__ == "__main__":
    unittest.main()
