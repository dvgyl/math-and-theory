"""Reject incomplete or changed curated releases without running Lean."""
import copy
import json
from pathlib import Path
import tempfile
import unittest

import check_curated_packages as curated

PIN = 'c44e0c8ee63ca166450922a373c7409c5d26b00b'


class CuratedPackageTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.package = Path(self.temp.name) / 'power-rank'
        self.formal = self.package / 'formalization'
        self.formal.mkdir(parents=True)
        (self.package / 'README.md').write_text('Scope and reproduction.\n')
        (self.formal / 'Main.lean').write_text('theorem endpoint : True := by trivial\n')
        (self.formal / 'lean-toolchain').write_text('leanprover/lean4:v4.19.0\n')
        (self.formal / 'lakefile.toml').write_text(
            'name = "fixture"\n[[require]]\nname = "mathlib"\n'
            'git = "https://github.com/leanprover-community/mathlib4.git"\n'
            'rev = "' + PIN + '"\n')
        (self.formal / 'lake-manifest.json').write_text(json.dumps({'packages': [
            {'name': 'mathlib', 'type': 'git', 'rev': PIN}]}))
        self.entry = {'root': 'verification/additional-proofs/power-rank',
                      'release_manifest_sha256': None,
                      'formal_scope': 'The endpoint theorem in Main.lean.',
                      'proof_roots': [{'path': 'formalization', 'lean_version': '4.19.0',
                                       'mathlib_revision': PIN, 'lakefile': 'lakefile.toml',
                                       'lockfile': 'lake-manifest.json'}],
                      'proof_sources': {'formalization/Main.lean': curated.digest(self.formal / 'Main.lean')},
                      'integrity_manifests': ['formalization/manifest.json']}
        self.inner()
        self.seal()

    def inner(self):
        names = curated.inventory(self.formal) - {'manifest.json'}
        (self.formal / 'manifest.json').write_text(json.dumps(
            {'format_version': 1, 'files': curated.file_records(self.formal, names)}))

    def seal(self):
        files = curated.inventory(self.package) - {'release-manifest.json'}
        record = {'format_version': 1, 'package_id': 'power-rank',
                  **{k: self.entry[k] for k in ('formal_scope', 'proof_roots', 'proof_sources', 'integrity_manifests')},
                  'files': curated.file_records(self.package, files)}
        (self.package / 'release-manifest.json').write_text(json.dumps(record))
        self.entry['release_manifest_sha256'] = curated.digest(self.package / 'release-manifest.json')

    def check(self):
        return curated.check(self.package, 'power-rank', self.entry)

    def test_complete_frozen_package_passes(self):
        self.assertEqual(self.check()['package_id'], 'power-rank')

    def test_missing_proof_fails(self):
        (self.formal / 'Main.lean').unlink()
        with self.assertRaisesRegex(ValueError, 'coverage differs'):
            self.check()

    def test_unlisted_file_fails(self):
        (self.package / 'extra.txt').write_text('unlisted')
        with self.assertRaisesRegex(ValueError, 'coverage differs'):
            self.check()

    def test_symbolic_link_fails(self):
        (self.package / 'linked').symlink_to(self.package / 'README.md')
        with self.assertRaisesRegex(ValueError, 'Symbolic link'):
            self.check()

    def test_linked_package_root_fails(self):
        link = self.package.with_name('linked-root')
        link.symlink_to(self.package, target_is_directory=True)
        with self.assertRaisesRegex(ValueError, 'linked curated package root'):
            curated.check(link, 'power-rank', self.entry)

    def test_changed_release_manifest_fails(self):
        with (self.package / 'release-manifest.json').open('a') as stream:
            stream.write('\n')
        with self.assertRaisesRegex(ValueError, 'Changed curated release manifest'):
            self.check()

    def test_changed_file_fails(self):
        (self.formal / 'Main.lean').write_text('theorem changed : False := by trivial\n')
        with self.assertRaisesRegex(ValueError, 'Changed curated file'):
            self.check()

    def test_changed_scope_cannot_be_rebound_by_outer_manifest(self):
        path = self.package / 'release-manifest.json'
        record = curated.read_json(path)
        record['formal_scope'] = 'A larger unsupported scope'
        path.write_text(json.dumps(record))
        self.entry['release_manifest_sha256'] = curated.digest(path)
        with self.assertRaisesRegex(ValueError, 'metadata differs: formal_scope'):
            self.check()

    def test_wrong_lean_pin_fails_even_after_file_rehash(self):
        (self.formal / 'lean-toolchain').write_text('leanprover/lean4:v4.35.0\n')
        self.inner(); self.seal()
        with self.assertRaisesRegex(ValueError, 'Wrong curated Lean pin'):
            self.check()

    def test_wrong_mathlib_requirement_fails_even_after_file_rehash(self):
        path = self.formal / 'lakefile.toml'
        path.write_text(path.read_text().replace(PIN, 'a' * 40))
        self.inner(); self.seal()
        with self.assertRaisesRegex(ValueError, 'Wrong curated Mathlib requirement'):
            self.check()

    def test_wrong_mathlib_lock_fails_even_after_file_rehash(self):
        path = self.formal / 'lake-manifest.json'
        path.write_text(path.read_text().replace(PIN, 'a' * 40))
        self.inner(); self.seal()
        with self.assertRaisesRegex(ValueError, 'Wrong curated Mathlib lock'):
            self.check()

    def test_proof_inventory_cannot_drop_a_covered_source(self):
        (self.formal / 'Second.lean').write_text('theorem second : True := by trivial\n')
        self.inner(); self.seal()
        with self.assertRaisesRegex(ValueError, 'proof source coverage differs'):
            self.check()

    def test_proof_hash_is_independently_bound(self):
        self.entry['proof_sources']['formalization/Main.lean'] = 'b' * 64
        self.seal()
        with self.assertRaisesRegex(ValueError, 'proof source hash differs'):
            self.check()

    def test_inner_integrity_is_checked_after_outer_hashes(self):
        path = self.formal / 'manifest.json'
        record = curated.read_json(path)
        record['files']['Main.lean']['sha256'] = 'c' * 64
        path.write_text(json.dumps(record))
        self.seal()
        with self.assertRaisesRegex(ValueError, 'Changed curated file: Main.lean'):
            self.check()

    def test_empty_proof_root_fails(self):
        empty = self.package / 'other'
        empty.mkdir()
        (empty / 'lean-toolchain').write_text('leanprover/lean4:v4.19.0\n')
        (empty / 'lakefile.toml').write_bytes((self.formal / 'lakefile.toml').read_bytes())
        self.entry['proof_roots'].append({**self.entry['proof_roots'][0], 'path': 'other', 'lockfile': None})
        self.seal()
        with self.assertRaisesRegex(ValueError, 'Empty curated proof root'):
            self.check()

    def test_overlapping_proof_roots_fail(self):
        self.entry['proof_roots'].append({**self.entry['proof_roots'][0], 'path': '.'})
        self.seal()
        with self.assertRaisesRegex(ValueError, 'Overlapping curated proof roots'):
            self.check()

    def test_pending_registry_entry_is_never_accepted(self):
        self.entry['release_manifest_sha256'] = None
        with self.assertRaisesRegex(ValueError, 'not frozen'):
            self.check()
        curated.validate_entry('power-rank', self.entry, allow_pending=True)

    def test_repeated_json_keys_fail(self):
        path = self.package / 'duplicate.json'
        path.write_text('{"key": 1, "key": 2}')
        with self.assertRaisesRegex(ValueError, 'Repeated JSON key'):
            curated.read_json(path)

    def test_invalid_paths_fail(self):
        for name in ('../proof.lean', '/proof.lean', 'x/../proof.lean', '.lake/proof.lean', 'x\\proof.lean', '.'):
            with self.subTest(name=name):
                self.assertFalse(curated.valid_path(name))

    def test_registry_requires_all_ten_ids(self):
        root = Path(self.temp.name) / 'repo'
        (root / 'verification').mkdir(parents=True)
        (root / 'verification/curated-packages.json').write_text(json.dumps(
            {'format_version': 1, 'packages': {'power-rank': self.entry}}))
        with self.assertRaisesRegex(ValueError, 'ID set differs'):
            curated.load_registry(root)


if __name__ == '__main__':
    unittest.main()
