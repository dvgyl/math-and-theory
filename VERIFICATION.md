# Verification status

This candidate has not been compiled. No Lean build, dependency download,
Comparator check, or Palomar preflight ran during preparation. Static integrity
checks do not establish kernel acceptance.

The candidate pins Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The dependency manifest matches the Higuchi–Sudbery
candidate. All 34 proof modules have module, public import, and public exposed
section headers. Their proof mathematics is unchanged.

The selected statements prove the actual finite-matrix derivative interval and
local branch existence. Stochastic cumulant identification and universal
sharpness remain conventional manuscript proofs. The preserved manuscript
records historical Lean 4.19.0 verification and does not certify this candidate.
Old compiler reports, manifests, hashes, and the old verifier are excluded.
The retained exact certificate checker concerns algebra and is not compiler evidence.

The complete pinned Palomar preflight must check this exact candidate before
intake. Package-wide warnings are not errors because Challenge contains deliberate
theorem holes. Solution requires strict compilation and axiom checks. The permitted
foundational axioms are propext, Classical.choice, and Quot.sound. No passing
result is claimed. Source hashes certify integrity only.
