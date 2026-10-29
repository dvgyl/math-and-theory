#!/usr/bin/env bash
set -euo pipefail
project_directory="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$project_directory"
# Prepare the pinned external dependencies before building.
# These local module targets run in order to limit compiler concurrency.
for replay_module in \
    PureECQC.Foundation \
    PureECQC.Raw \
    PureECQC.Entropy \
    PureECQC.Main \
    PureECQC; do
    lake --no-cache build "$replay_module"
done
lake --no-cache build
replay_audit_output="$(mktemp)"
trap 'rm -f -- "$replay_audit_output"' EXIT
if lake env lean --trust=0 ReplayAudit.lean >"$replay_audit_output" 2>&1; then
    cat -- "$replay_audit_output"
else
    replay_audit_status=$?
    cat -- "$replay_audit_output"
    exit "$replay_audit_status"
fi
python3 check_axioms.py "$replay_audit_output"
