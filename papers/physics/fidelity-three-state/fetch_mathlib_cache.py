#!/usr/bin/env python3
"""Fetch the official cache for precisely the bundled files' mathlib imports."""
from pathlib import Path
import re
import subprocess

root = Path(__file__).resolve().parent
imports = set()
for name in ["QICFoundation.lean", "FullCandidate.lean"]:
    source = (root / name).read_text()
    imports.update(re.findall(r"^(?:public )?import (Mathlib[\w.]*)\s*$", source, re.MULTILINE))
if not imports:
    raise SystemExit("No mathlib imports found; refusing an unintended full-cache request.")
print(f"Fetching the pinned official mathlib cache for {len(imports)} root modules.", flush=True)
subprocess.run(["lake", "exe", "cache", "get", *sorted(imports)], cwd=root, check=True)
