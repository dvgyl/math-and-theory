#!/usr/bin/env bash
# Fresh Lean build with the whole-project axiom audit, then the exact SymPy checks.
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
lake build Main ProjectAxiomAudit 2>&1 | tee "$out/build.log"
python3 "$root/scripts/check_axiom_audit.py" --log "$out/build.log" --project "$root/lean" \
  --output "$out/axiom-inventory.json"
lake env lean AxiomAudit.lean > "$out/selected-axioms.log" 2>&1
python3 -m venv "$out/venv"
"$out/venv/bin/pip" install --quiet -r "$root/verification/requirements.txt"
"$out/venv/bin/python" "$root/scripts/run_exact_checks.py" | tee "$out/exact-checks.json"
