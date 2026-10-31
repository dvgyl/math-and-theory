#!/usr/bin/env bash
# Fresh build of the Lean project, strict axiom audit, Lean-data check and certificate check.
set -euo pipefail
root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")/.." && pwd)"
out="${1:-$root/verification-run}"
cd "$root/lean"
if [[ -e .lake/build ]]; then
  echo "A local project build already exists; use a fresh copy of the package." >&2
  exit 2
fi
mkdir -p "$out"
python3 "$root/scripts/generate_lean_data.py" "$root/certificate/data/SHORT_CHAIN_CERTIFICATE.json.xz" \
  "$root/certificate/data/GAP_SOS_A4.json.xz" "$root/lean/ShortChain/Data.lean" --check
lake exe cache get
lake build ShortChain ShortChain.AxiomAudit 2>&1 | tee "$out/build.log"
python3 "$root/scripts/check_axiom_audit.py" --log "$out/build.log" --project "$root/lean" \
  --output "$out/axiom-inventory.json"
python3 "$root/certificate/check_certificates.py" --extra 3 --json "$out/certificate-check.json"
