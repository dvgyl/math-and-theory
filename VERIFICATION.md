# Verification status

This candidate has not been compiled. No Lean build, dependency download,
Comparator check, or Palomar preflight was run during preparation.
The candidate pins Lean 4.35.0 and Mathlib revision
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The dependency manifest is copied
from the Higuchi–Sudbery candidate for the same pins.

The foundation source is split at complete original-module boundaries.
All original QICLean blocks are byte-identical to the recorded source.
FullCandidate.lean retains its proof bodies and has an explicit Spectrum.Pi import. Public imports connect the parts in their original order. This static
integrity check does not establish kernel acceptance or correct exported interfaces.

The preserved manuscript describes historical Lean 4.35.0-rc3 verification.
It does not certify the changed package. Earlier audit logs, verification.json,
release-manifest.json, and version-specific build scripts are excluded.
source-sha256.json records integrity only. The complete pinned Palomar preflight
must check this exact candidate before intake. Permitted foundational axioms are
propext, Classical.choice, and Quot.sound. No passing result is claimed here.
