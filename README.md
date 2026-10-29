# Exact conditional contraction for Pauli channels and depolarization in every dimension

The result gives exact conditional contraction coefficients for every stochastic
Pauli qubit channel and the full physical depolarizing interval in every
dimension `d ≥ 2`. The coefficient is the supremum of actual density-state
ratios with a positive denominator. It includes every finite quantum reference.
The reference marginals need not agree.

For the two smallest Pauli weights `a` and `b`, the coefficient is
`1 - 8ab/(a+b)`. If both weights are zero, Lean's real division gives value one.
For depolarizing parameter `λ ≥ 0`, the coefficient is `λ`. For `λ = -s < 0`,
it is `s[1+(d²-1)s]/[1-(d²-3)s]`. The physical interval is
`-1/(d²-1) ≤ λ ≤ 1`. Both formulas hold for every `γ ≥ 1`, including ties,
zero weights, complete depolarization, the identity, and the negative endpoint.

- [Original manuscript PDF](quantum_exact_contraction.pdf).
- [Original manuscript source](quantum_exact_contraction.tex).
- [Verification scope](VERIFICATION.md).
- [Citation](CITATION.cff).

The manuscript preserves the original research version. Its verification
section records the earlier Lean 4.19.0 environment. Those historical claims
do not certify this package. The active package uses Lean 4.35.0 and Mathlib
revision `56a005855ea17e0b0958f73ec801ae140b0a1679`.

`Challenge.lean` imports only Mathlib. It states channel existence and the exact
coefficient for every channel with the specified map. It has two deliberate
theorem placeholders. Its definitions have complete bodies.
`Solution.lean` imports the complete proof and `PalomarEndpoints.lean`.
The endpoint module connects the Challenge statements to the original channel
constructors and exact coefficient theorems. The comparator is
`comparator/quantum-exact-contraction.json`.

The complete proof includes the original normalized density witnesses,
finite witnesses for degenerate Pauli weights, and limiting sharpness families.
An equality for a supremum does not assert that every coefficient is attained.
The original endpoints remain `PauliConditionalExact.every_pauli_channel`
and `DepolarizingExact.actual_full_channel`.

The complete package was checked locally with the active pins on 2026-10-29.
All 60 modules compiled. The bundled Comparator accepted both Challenge
statements, their dependencies, the permitted axioms, and the default Lean
kernel check of Solution. This local check used exports and had no sandbox.
The exact published commit still requires a full sandboxed Palomar preflight
before intake. No verification certificate is supplied.

The unital-qubit normal-form existence theorem is cited in the manuscript.
It is not separately formalized. Erasure simulation and ensemble guessing
have conventional manuscript proofs. They are outside the selected Challenge.
The result does not claim a minimum reference dimension, a general pure-state
reduction, relative-entropy contraction, capacity, or a computation method for
finite references of arbitrary channels. Historical priority is provisional.

This is fully autonomous agentic research. AI systems produced the research,
manuscript, proofs, and formalization. Dev D. Goyal is responsible for
publication. No expert human validation or external peer review is claimed.
The original code and manuscript use [Apache-2.0](LICENSE).
[NOTICE](NOTICE) preserves prior-work credit. The manuscript gives the full
references and the limits of the literature comparison.
