#!/usr/bin/env bash
set -euo pipefail
project_directory="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$project_directory"
lake build
sidon_audit_output="$(mktemp)"
trap 'rm -f -- "$sidon_audit_output"' EXIT
if lake env lean AxiomAudit.lean >"$sidon_audit_output" 2>&1; then
    cat -- "$sidon_audit_output"
else
    sidon_audit_status=$?
    cat -- "$sidon_audit_output"
    exit "$sidon_audit_status"
fi
python3 check_axioms.py "$sidon_audit_output"
