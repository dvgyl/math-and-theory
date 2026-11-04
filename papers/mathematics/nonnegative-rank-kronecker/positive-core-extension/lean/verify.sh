#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

positive_core_lake="${POSITIVE_CORE_LAKE:-lake}"
export MATHLIB_NO_CACHE_ON_UPDATE=1
export LAKE_ARTIFACT_CACHE=false
mkdir -p verification

{
  date -u '+UTC: %Y-%m-%dT%H:%M:%SZ'
  "$positive_core_lake" env lean --version
  "$positive_core_lake" --version
  python3 verify_record.py --environment
} 2>&1 | tee verification/environment.log

python3 generate_audit.py
python3 - <<'PY'
from pathlib import Path
import shutil
p = Path('.lake/build')
if p.exists():
    shutil.rmtree(p)
PY

"$positive_core_lake" --no-cache build MatCKronecker PositiveCore 2>&1 | tee verification/build.log
"$positive_core_lake" env lean AxiomAudit.lean 2>&1 | tee verification/axioms.log
python3 verify_record.py
