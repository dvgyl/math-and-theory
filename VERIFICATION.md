# Verification status

The complete proof and Solution compile with Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. The local check uses trust level
zero and one compiler process at a time. The proof has no compiler warnings.
Challenge compiles with its two intended theorem holes.

The bundled Comparator accepts both selected statements, their exact definition
constants, and the permitted axioms. The default Lean kernel accepts the exported
Solution. The local Comparator ran without a sandbox. No external kernel check
was used. This local check does not replace the complete pinned Palomar preflight.

The strict Audit checks eight theorem types and their axiom dependencies.
They use only `propext`, `Classical.choice`, and `Quot.sound`.
`verification/local-replay-summary.json` binds these results to the source hashes.
`verification/selected-types-and-axioms.txt` records the Audit output.

The original QICLean module blocks and legal notices remain byte-identical.
FullCandidate retains every existing formula and mathematical proof body.
It adds the explicit Spectrum.Pi import and three named, proved matrix instances.
Challenge uses the source scope order and copies weightedRoot as well as the
entropy, nuclear norm, ensemble average, and root-fidelity matrix definitions.
The named instances give independent exports the same proved instance constants.

The preserved manuscript describes historical Lean 4.35.0-rc3 verification.
It does not certify the changed package. Historical logs and release hashes are
excluded. `source-sha256.json` records package integrity only. The exact candidate
still requires full pinned Palomar preflight before intake.
