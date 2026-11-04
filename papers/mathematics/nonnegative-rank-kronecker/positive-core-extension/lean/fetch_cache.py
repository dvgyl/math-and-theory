#!/usr/bin/env python3
"""Fetch exactly the pinned Mathlib import closure used by this project."""
from pathlib import Path
import os
import re
import subprocess

root = Path(__file__).resolve().parent
sources = [*root.glob('MatCKronecker/*.lean'), *root.glob('PositiveCore/*.lean')]
imports = sorted({module for path in sources
                  for module in re.findall(r'^(?:public )?(?:meta )?import (Mathlib[.\w]+)$',
                                           path.read_text(), re.M)})
if not imports:
    raise SystemExit('No Mathlib imports found')
lake = os.environ.get('POSITIVE_CORE_LAKE', 'lake')
print(f'Fetching the dependency closure of {len(imports)} Mathlib imports.', flush=True)
subprocess.run([lake, 'exe', 'cache', 'get', *imports], cwd=root, check=True)
