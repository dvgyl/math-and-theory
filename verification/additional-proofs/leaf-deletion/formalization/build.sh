#!/usr/bin/env bash
set -euo pipefail
project_directory="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
cd "$project_directory"
# Prepare the pinned external dependencies before building.
# These local module targets run in order to limit compiler concurrency.
for replay_module in \
    LeafMode.Graph \
    LeafMode.Counting \
    LeafMode.Semantics \
    LeafMode.IsoInvariance \
    LeafMode.Modes \
    LeafMode.ResultCore \
    LeafMode.CertificateSupport \
    LeafMode.FData \
    LeafMode.FCertificate \
    LeafMode.GData \
    LeafMode.GCertificate \
    LeafMode.HData \
    LeafMode.HCertificate \
    LeafMode.AlgebraCertificate \
    LeafMode.ShapeCertificate \
    LeafMode.Certificates \
    LeafMode.Result \
    LeafMode; do
    lake --no-cache build "$replay_module"
done
lake --no-cache build
replay_audit_output="$(mktemp)"
trap 'rm -f -- "$replay_audit_output"' EXIT
if lake env lean --trust=0 Audit.lean >"$replay_audit_output" 2>&1; then
    cat -- "$replay_audit_output"
else
    replay_audit_status=$?
    cat -- "$replay_audit_output"
    exit "$replay_audit_status"
fi
python3 check_axioms.py "$replay_audit_output"
