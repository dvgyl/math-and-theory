#!/usr/bin/env python3
"""Check every file in the explicit publication manifest."""
import hashlib
import json
from pathlib import Path
import sys

from publication_files import HASHES, load_publication_files


def verify(root):
    names = load_publication_files(root)
    record = json.loads((root / HASHES).read_text())
    files = record.get('files')
    expected = set(names) - {HASHES}
    if not isinstance(files, dict) or set(files) != expected:
        raise ValueError('The hash record must cover every publication file except itself.')
    errors = []
    for name, digest in files.items():
        if hashlib.sha256((root / name).read_bytes()).hexdigest() != digest:
            errors.append(f'Changed file: {name}')
    if errors:
        raise ValueError('\n'.join(errors))
    return len(files)


if __name__ == '__main__':
    root = Path(__file__).resolve().parents[1]
    try:
        count = verify(root)
    except (ValueError, OSError) as error:
        print(json.dumps({'status': 'FAIL', 'error': str(error)}, indent=2))
        sys.exit(1)
    print(json.dumps({'status': 'PASS', 'checked_files': count}, indent=2))
