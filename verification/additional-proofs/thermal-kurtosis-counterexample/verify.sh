#!/usr/bin/env bash
set -euo pipefail

# Run from any directory. Argument: the pinned Mathlib checkout.
proof_root="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
mathlib_root="$(cd -- "${1:?Usage: bash verify.sh /absolute/path/to/mathlib4}" && pwd)"
expected_revision=c44e0c8ee63ca166450922a373c7409c5d26b00b

if [[ ! -e "$mathlib_root/.git" ]]; then
  printf 'Mathlib must be a Git checkout with a verifiable revision.\n' >&2
  exit 1
fi
actual_revision="$(git -C "$mathlib_root" rev-parse HEAD)"
if [[ "$actual_revision" != "$expected_revision" ]]; then
  printf 'Wrong Mathlib revision: %s\nExpected: %s\n' "$actual_revision" "$expected_revision" >&2
  exit 1
fi
if ! git -C "$mathlib_root" diff --quiet HEAD --; then
  printf 'The Mathlib checkout has modified tracked files.\n' >&2
  exit 1
fi

cd -- "$mathlib_root"
actual_lean_version="$(lake env lean --version)"
case "$actual_lean_version" in
  'Lean (version 4.19.0,'*) ;;
  *) printf 'Wrong Lean version: %s\n' "$actual_lean_version" >&2; exit 1 ;;
esac
printf '%s\nMathlib revision: %s\n' "$actual_lean_version" "$actual_revision"
lake env lean "$proof_root/ThermalKurtosis.lean"
python3 "$proof_root/model_check.py"
printf '\nVerification completed successfully.\n'
