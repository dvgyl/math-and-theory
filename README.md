# Exact three-setting correlation bounds at fixed steering centre

A local source replay compiled all 18 proof modules and Solution with Lean 4.35.0
and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. Challenge also compiled
with its five deliberate theorem holes. The selected declarations and the audited
square-root support lemmas use only the permitted foundational axioms. Full
Palomar preflight and Comparator checks remain required. See the
[local replay summary](verification/local-replay-summary.json).

The selected theorems give the exact least upper bound of the squared Pauli
correlation value for actual two-qubit density matrices at each computed steering
centre c in [0,1]. The explicit piecewise envelope is attained below 2/3. It is
not attained on [2/3,1). It is attained at c=1. A value above one exists at a
specified centre exactly when c is below 2/3.

This threshold concerns the specified three-setting CJWR expression. It does
not characterize all steerable states. The CJWR measurement optimization and
steering-ellipsoid interpretation use credited external physics correspondences.
Lean does not optimize measurement settings or define local hidden-state models.

[Challenge.lean](Challenge.lean) imports only Mathlib. It uses actual density
matrices, partial traces, Pauli correlations, positive canonical filtering through CFC.sqrt, the
computed centre, and the explicit envelope. The short partial-trace positivity
proof supports the positive square root. No correlation inequality is assumed.
Its five deliberate theorem holes are separate from [Solution.lean](Solution.lean),
which imports all 18 local proof modules. The Comparator path is
[comparator/steering-bounds.json](comparator/steering-bounds.json).
The related fully entangled fraction maximum remains included in the proof.

The complete manuscript, figure, citation files, authorship disclosure, and
license are preserved. The manuscript's Lean 4.19.0 verification claims concern
the historical source. They do not certify this port. Earlier compiler receipts,
release hashes, dependency pins, and the version-specific verifier are excluded.
Current Lake files contain the pins. Source hashes certify integrity only.
See [VERIFICATION.md](VERIFICATION.md) for the current status.

The manuscript credits Milne and collaborators, Ducuara and collaborators,
Bravyi, and Costa and Angelo. Canonical filtering, canonical spectral bounds,
and the maximally obese witness family are credited prior ingredients.
No formal verification result certifies priority.

This work is fully autonomous agentic research. Automated systems produced the
mathematical arguments and formal proofs. Codex contributed mathematical checks,
verification software, and manuscript preparation. Dev D. Goyal is responsible
for publication. No expert validation or peer review is claimed. The materials
use [Apache-2.0](LICENSE). Imported libraries retain their own licenses.
