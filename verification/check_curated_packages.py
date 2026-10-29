#!/usr/bin/env python3
"""Check frozen curated proof packages. This check does not run Lean."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import tomllib

CURATED_IDS = frozenset({
    'power-rank', 'admm-counterexample', 'graph-roots', 'motzkin-bounded-forcing',
    'sidon-renyi', 'ordered-allocation', 'kunisky', 'pure-ecqc', 'kovacec', 'leaf-deletion',
})
HASH = re.compile(r'[0-9a-f]{64}\Z')
REVISION = re.compile(r'[0-9a-f]{40}\Z')
BLOCKED = {'.git', '.lake', '.verification', '__pycache__', '.build'}
ENTRY_KEYS = {'root', 'release_manifest_sha256', 'formal_scope', 'proof_roots',
              'proof_sources', 'integrity_manifests'}


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def unique_object(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'Repeated JSON key: ' + key)
        result[key] = value
    return result


def read_json(path):
    return json.loads(Path(path).read_text(), object_pairs_hook=unique_object)


def valid_path(name, root=False):
    if root and name == '.':
        return True
    if not isinstance(name, str) or not name or '\\' in name:
        return False
    path = PurePosixPath(name)
    return (not path.is_absolute() and bool(path.parts) and path.as_posix() == name
            and all(part not in {'.', '..'} | BLOCKED for part in path.parts))


def inventory(package):
    package = Path(package).absolute()
    require(package.is_dir() and package.resolve() == package,
            'Invalid or linked curated package root')
    files = set()
    for path in package.rglob('*'):
        relative = path.relative_to(package).as_posix()
        require(not path.is_symlink(), 'Symbolic link in curated package: ' + relative)
        require(valid_path(relative), 'Invalid curated package path: ' + relative)
        require(path.is_file() or path.is_dir(), 'Special file in curated package: ' + relative)
        if path.is_file():
            files.add(relative)
    return files


def file_records(package, files):
    return {name: {'bytes': (package / name).stat().st_size,
                   'sha256': digest(package / name)} for name in sorted(files)}


def check_records(package, records):
    require(isinstance(records, dict) and bool(records), 'Empty curated file records')
    for name, row in records.items():
        require(valid_path(name) and isinstance(row, dict) and set(row) == {'bytes', 'sha256'},
                'Invalid curated file record: ' + str(name))
        require(type(row['bytes']) is int and row['bytes'] >= 0 and
                isinstance(row['sha256'], str) and HASH.fullmatch(row['sha256']),
                'Invalid curated size or hash: ' + name)
        path = package / name
        require(path.is_file() and not path.is_symlink(), 'Missing curated file: ' + name)
        require(path.stat().st_size == row['bytes'] and digest(path) == row['sha256'],
                'Changed curated file: ' + name)


def validate_entry(name, entry, allow_pending=False):
    require(name in CURATED_IDS and isinstance(entry, dict) and set(entry) == ENTRY_KEYS,
            'Invalid curated registry entry: ' + name)
    require(entry['root'] == 'verification/additional-proofs/' + name,
            'Wrong curated package route: ' + name)
    require(isinstance(entry['formal_scope'], str) and bool(entry['formal_scope'].strip()),
            'Missing curated formal scope: ' + name)
    frozen = entry['release_manifest_sha256']
    require((allow_pending and frozen is None) or
            (isinstance(frozen, str) and HASH.fullmatch(frozen)),
            'Curated package is not frozen: ' + name)
    roots = entry['proof_roots']
    require(isinstance(roots, list) and bool(roots), 'Missing curated proof roots: ' + name)
    paths = []
    for root in roots:
        require(isinstance(root, dict) and set(root) ==
                {'path', 'lean_version', 'mathlib_revision', 'lakefile', 'lockfile'},
                'Invalid curated proof-root record: ' + name)
        require(valid_path(root['path'], root=True) and
                isinstance(root['lean_version'], str) and
                re.fullmatch(r'\d+\.\d+\.\d+', root['lean_version']) and
                isinstance(root['mathlib_revision'], str) and REVISION.fullmatch(root['mathlib_revision']),
                'Invalid curated toolchain pin: ' + name)
        require(root['lakefile'] in {'lakefile.toml', 'lakefile.lean'} and
                root['lockfile'] in {None, 'lake-manifest.json'},
                'Invalid curated configuration paths: ' + name)
        paths.append(root['path'])
    require(len(set(paths)) == len(paths), 'Repeated curated proof root: ' + name)
    require(not any(a == '.' or b.startswith(a + '/') for a in paths for b in paths if a != b),
            'Overlapping curated proof roots: ' + name)
    proofs = entry['proof_sources']
    require(isinstance(proofs, dict) and (bool(proofs) or (allow_pending and frozen is None)),
            'Missing curated proof inventory: ' + name)
    require(all(valid_path(path) and path.endswith('.lean') and isinstance(value, str)
                and HASH.fullmatch(value) for path, value in proofs.items()),
            'Invalid curated proof inventory: ' + name)
    inner = entry['integrity_manifests']
    require(isinstance(inner, list) and len(inner) == len(set(inner)) and
            all(valid_path(path) and path != 'release-manifest.json' for path in inner),
            'Invalid curated inner manifests: ' + name)


def load_registry(root, allow_pending=False):
    registry = read_json(Path(root) / 'verification/curated-packages.json')
    require(isinstance(registry, dict) and set(registry) == {'format_version', 'packages'} and
            type(registry['format_version']) is int and registry['format_version'] == 1,
            'Invalid curated registry')
    entries = registry['packages']
    require(isinstance(entries, dict) and set(entries) == CURATED_IDS,
            'Curated package ID set differs')
    for name, entry in entries.items():
        validate_entry(name, entry, allow_pending)
    return entries


def check_pins(package, roots):
    for row in roots:
        root = package / row['path']
        require(root.is_dir() and not root.is_symlink(), 'Missing curated proof root')
        require((root / 'lean-toolchain').read_text().strip() ==
                'leanprover/lean4:v' + row['lean_version'], 'Wrong curated Lean pin')
        require({p.name for p in root.glob('lakefile.*') if p.name in {'lakefile.toml', 'lakefile.lean'}}
                == {row['lakefile']}, 'Curated Lake configuration coverage differs')
        require((root / 'lake-manifest.json').is_file() == (row['lockfile'] is not None),
                'Curated lockfile coverage differs')
        config = root / row['lakefile']
        revision = row['mathlib_revision']
        if config.suffix == '.toml':
            dependencies = tomllib.loads(config.read_text()).get('require', [])
            mathlib = [item for item in dependencies if item.get('name') == 'mathlib']
            require(len(mathlib) == 1 and mathlib[0].get('rev') == revision and
                    mathlib[0].get('git') == 'https://github.com/leanprover-community/mathlib4.git',
                    'Wrong curated Mathlib requirement')
        else:
            pins = re.findall(r'require\s+mathlib\s+from\s+git\s+'
                              r'"https://github.com/leanprover-community/mathlib4.git"\s*@\s*"([0-9a-f]{40})"',
                              config.read_text())
            require(pins == [revision], 'Wrong curated Mathlib requirement')
        if row['lockfile'] is not None:
            lock = read_json(root / row['lockfile'])
            packages = lock.get('packages')
            require(isinstance(packages, list) and bool(packages) and
                    len({item.get('name') for item in packages}) == len(packages),
                    'Invalid curated dependency lock')
            require(all(item.get('type') == 'git' and isinstance(item.get('rev'), str)
                        and REVISION.fullmatch(item['rev']) for item in packages),
                    'Unpinned curated dependency')
            mathlib = [item for item in packages if item.get('name') == 'mathlib']
            require(len(mathlib) == 1 and mathlib[0].get('rev') == revision,
                    'Wrong curated Mathlib lock')


def check_inner_manifest(package, name):
    path = package / name
    record = read_json(path)
    require(type(record.get('format_version')) is int and record['format_version'] == 1,
            'Invalid inner proof manifest')
    files = record.get('files')
    require(isinstance(files, dict), 'Missing inner proof file records')
    actual = inventory(path.parent)
    require(actual == set(files) | {path.name}, 'Inner proof manifest coverage differs')
    check_records(path.parent, files)


def check(package, name, entry):
    """Return a checked outer manifest; never compile or execute package code."""
    validate_entry(name, entry)
    package = Path(package).absolute()
    actual = inventory(package)
    manifest_path = package / 'release-manifest.json'
    require(digest(manifest_path) == entry['release_manifest_sha256'],
            'Changed curated release manifest: ' + name)
    manifest = read_json(manifest_path)
    require(set(manifest) == {'format_version', 'package_id', 'formal_scope', 'proof_roots',
                              'proof_sources', 'integrity_manifests', 'files'} and
            type(manifest['format_version']) is int and manifest['format_version'] == 1 and
            manifest['package_id'] == name, 'Invalid curated release manifest: ' + name)
    for key in ('formal_scope', 'proof_roots', 'proof_sources', 'integrity_manifests'):
        require(manifest[key] == entry[key], 'Curated registry metadata differs: ' + key)
    files = manifest['files']
    require(isinstance(files, dict) and actual == set(files) | {'release-manifest.json'},
            'Curated release-file coverage differs: ' + name)
    check_records(package, files)
    lean = {path for path in files if path.endswith('.lean') and Path(path).name != 'lakefile.lean'}
    require(lean == set(entry['proof_sources']), 'Curated proof source coverage differs: ' + name)
    require(all(files[path]['sha256'] == entry['proof_sources'][path] for path in lean),
            'Curated proof source hash differs: ' + name)
    for proof in lean:
        require(any(row['path'] == '.' or proof.startswith(row['path'] + '/')
                    for row in entry['proof_roots']), 'Proof outside curated roots: ' + proof)
    for row in entry['proof_roots']:
        require(any(row['path'] == '.' or proof.startswith(row['path'] + '/') for proof in lean),
                'Empty curated proof root')
    check_pins(package, entry['proof_roots'])
    for inner in entry['integrity_manifests']:
        require(inner in files, 'Missing curated inner manifest')
        check_inner_manifest(package, inner)
    return manifest


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--package', choices=sorted(CURATED_IDS))
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    try:
        entries = load_registry(root, allow_pending=bool(args.package))
        names = [args.package] if args.package else sorted(entries)
        for name in names:
            check(root / entries[name]['root'], name, entries[name])
    except (OSError, ValueError, KeyError, TypeError) as error:
        parser.exit(1, str(error) + '\n')
    print(json.dumps({'status': 'PASS', 'packages': len(names), 'fresh_lean_compilation': False}))
