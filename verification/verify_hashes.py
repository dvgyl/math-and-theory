#!/usr/bin/env python3
"""Check the recorded hashes of the mathematical sources and proof inputs."""
import hashlib
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[1]
record = json.loads((root / "verification/records/source-hashes.json").read_text())
errors = []
for name, expected in record["files"].items():
    path = root / name
    if not path.is_file():
        errors.append(f"Missing file: {name}")
    elif hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        errors.append(f"Changed file: {name}")
print(json.dumps({"status": "FAIL" if errors else "PASS",
                  "checked_files": len(record["files"]), "errors": errors}, indent=2))
sys.exit(bool(errors))
