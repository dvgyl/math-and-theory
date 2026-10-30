#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"
mat_c_lake="${MAT_C_LAKE:-lake}"
mat_c_expected_mathlib="0db6cb99b412983de54b59ecc1b0b2747542cda3"
mkdir -p verification
command -v rg >/dev/null

{
  date -u '+UTC: %Y-%m-%dT%H:%M:%SZ'
  "$mat_c_lake" env lean --version
  printf 'Expected mathlib: %s\n' "$mat_c_expected_mathlib"
  mat_c_actual_mathlib="$(git -C .lake/packages/mathlib rev-parse HEAD)"
  printf 'Actual mathlib: %s\n' "$mat_c_actual_mathlib"
  test "$mat_c_actual_mathlib" = "$mat_c_expected_mathlib"
} 2>&1 | tee verification/environment.log

# The explicit package name preserves dependency build caches.
"$mat_c_lake" clean mat_c_p1
"$mat_c_lake" build 2>&1 | tee verification/build.log
"$mat_c_lake" env lean AxiomAudit.lean 2>&1 | tee verification/axioms.log

if rg -n '\b(sorry|admit|axiom|native_decide)\b' MatCP1.lean MatCP1; then
  printf 'Forbidden proof construct detected.\n' >&2
  exit 1
fi
if rg -n 'sorryAx|Lean\.ofReduceBool' verification/axioms.log; then
  printf 'Non-kernel proof dependency detected.\n' >&2
  exit 1
fi
printf 'Fresh build and endpoint axiom audit completed successfully.\n'
