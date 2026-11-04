#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"

mat_c_nnr_lake="${MAT_C_NNR_LAKE:-lake}"
mat_c_nnr_mathlib="0db6cb99b412983de54b59ecc1b0b2747542cda3"
export MATHLIB_NO_CACHE_ON_UPDATE=1
# --no-cache disables downloads, but Lake 5 can still restore local artifacts.
# Disable that separate mechanism so every authored module is re-elaborated.
export LAKE_ARTIFACT_CACHE=false
mkdir -p verification

{
  date -u '+UTC: %Y-%m-%dT%H:%M:%SZ'
  "$mat_c_nnr_lake" env lean --version
  "$mat_c_nnr_lake" --version
  printf 'Expected mathlib: %s\n' "$mat_c_nnr_mathlib"
  mat_c_nnr_actual="$(git -C .lake/packages/mathlib rev-parse HEAD)"
  printf 'Actual mathlib: %s\n' "$mat_c_nnr_actual"
  printf 'Local Lake artifact cache: disabled for this verification\n'
  test "$mat_c_nnr_actual" = "$mat_c_nnr_mathlib"
} 2>&1 | tee verification/environment.log

python3 generate_audit.py

# Remove only this project's regenerable outputs. Dependency caches are retained.
python3 - <<'PY'
from pathlib import Path
import shutil
p = Path('.lake/build')
if p.exists():
    shutil.rmtree(p)
PY

"$mat_c_nnr_lake" --no-cache build MatCKronecker 2>&1 | tee verification/build.log
"$mat_c_nnr_lake" env lean AxiomAudit.lean 2>&1 | tee verification/axioms.log
python3 make_verification_record.py
printf 'Fresh full-family counterexample build and complete source-declaration axiom audit succeeded.\n'
