#!/usr/bin/env bash
# Fresh Lean build, whole-project axiom audit, exact and numerical checks.
# Usage: bash scripts/verify.sh [output-directory]   (run in a fresh copy of the package)
set -euo pipefail
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
out="${1:-$root/verification-run}"
cd "$root/lean"
if [[ -e .lake/build ]]; then
  echo "A local project build already exists; use a fresh copy of the package." >&2
  exit 2
fi
mkdir -p "$out"
lake exe cache get
{ lake build && lake build ProjectAxiomAudit; } 2>&1 | tee "$out/build.log"
python3 "$root/scripts/check_axiom_audit.py" --log "$out/build.log" --project "$root/lean" \
  --output "$out/axiom-inventory.json"
python3 -I "$root/scripts/check_exact.py" > "$out/exact-checks.json"
python3 -I "$root/scripts/check_numeric.py" --quick > "$out/numeric-checks-quick.json"
