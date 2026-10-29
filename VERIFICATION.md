# Verification status

The complete proof closure compiles with Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`. It has 35 proof modules and Solution.
The local compiler uses trust level zero and one process at a time. It reports
101 proof-library warnings. Challenge compiles with its two intended theorem holes.

The bundled Comparator accepts both selected statements, their exact definition
constants, and the permitted axioms. The default Lean kernel accepts the exported
Solution. The local Comparator ran without a sandbox. No external kernel ran.
This check does not replace the complete pinned Palomar preflight.

A strict audit checks 80 recorded theorem endpoints with warnings as errors.
Each endpoint uses only propext, Classical.choice, and Quot.sound.
`verification/EndpointAudit.lean` gives the audit commands.
`verification/selected-types-and-axioms.txt` gives the output.
`verification/local-replay-summary.json` binds the result to source hashes.

All 34 original modules retain their declaration headers and mathematical
definition bodies. Imports and proof scripts use the current APIs. The added
PermutationCompat module proves two inverse-permutation cancellation identities.
Lake lists all 35 proof roots and build modules. Challenge imports only Mathlib.

The selected statements prove the actual finite-matrix derivative interval and
local branch existence. Stochastic cumulant identification and universal
sharpness remain conventional manuscript proofs. The preserved manuscript
records historical Lean 4.19.0 verification and does not certify this candidate.
Old compiler reports and release hashes are excluded. The retained exact
certificate checker concerns algebra and is not compiler evidence.

Full pinned Palomar preflight must check these bytes before intake.
`source-sha256.json` records integrity only.
