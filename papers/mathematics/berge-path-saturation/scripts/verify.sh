#!/usr/bin/env bash
# Fresh build of the Lean project, strict axiom audit and exhaustive witness check.
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
lake build BergePath BergePath.AxiomAudit 2>&1 | tee "$out/build.log"
python3 "$root/scripts/check_axiom_audit.py" --log "$out/build.log" --project "$root/lean" \
  --output "$out/axiom-inventory.json"
python3 "$root/certificate/check_witness.py" --json > "$out/witness-check.json"
