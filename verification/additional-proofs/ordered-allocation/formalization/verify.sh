#!/usr/bin/env bash
set -euo pipefail
cd -- "$(dirname -- "${BASH_SOURCE[0]}")"
lake --no-cache build
allocation_audit_output="$(mktemp)"
trap 'rm -f -- "$allocation_audit_output"' EXIT
if lake env lean --trust=0 StatementAudit.lean >"$allocation_audit_output" 2>&1; then
  cat -- "$allocation_audit_output"
else
  allocation_audit_status=$?
  cat -- "$allocation_audit_output"
  exit "$allocation_audit_status"
fi
python3 check_axioms.py "$allocation_audit_output"
