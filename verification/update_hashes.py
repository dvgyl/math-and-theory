#!/usr/bin/env python3
"""Record the current hashes of the listed publication files."""
import hashlib
import json
from pathlib import Path

from publication_files import HASHES, load_publication_files

root = Path(__file__).resolve().parents[1]
names = load_publication_files(root)
record = {
    "format_version": 1,
    "algorithm": "sha256",
    "files": {name: hashlib.sha256((root / name).read_bytes()).hexdigest()
              for name in names if name != HASHES},
}
(root / HASHES).write_text(json.dumps(record, indent=2) + "\n")
print(f"Recorded hashes for {len(record['files'])} publication files.")
