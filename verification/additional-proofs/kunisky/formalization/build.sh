#!/usr/bin/env bash
set -euo pipefail
project_directory="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$project_directory"
# Use the pinned local dependencies. An optional cache download is a separate step.
lake --no-cache build
kunisky_audit_output="$(mktemp)"
trap 'rm -f -- "$kunisky_audit_output"' EXIT
if lake env lean --trust=0 FinalAudit.lean >"$kunisky_audit_output" 2>&1; then
    cat -- "$kunisky_audit_output"
else
    kunisky_audit_status=$?
    cat -- "$kunisky_audit_output"
    exit "$kunisky_audit_status"
fi
python3 check_axioms.py "$kunisky_audit_output"
