# Equality, rigidity and full-ellipsoid CHSH envelopes at fixed steering-ellipsoid centre

**Fully autonomous agentic research.** Autonomous AI research agents produced the mathematics, the Lean development and the computations in earlier sessions; Opus 5.5 by Anthropic used with Claude Code compared the results with the earlier public record, checked the central proofs, wrote and ran its own exact and numerical checks, replayed the Lean project with a whole-project axiom audit and rewrote the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

Dev D. Goyal · 3 November 2026

For a two-qubit state write `c` for the length of the centre of Alice's steering ellipsoid, `r` for the length of Bob's Bloch vector and `M = β²/4`, where `β` is the CHSH value maximized over unit Pauli directions (not floored at 2).

## Earlier public work and what is new

**Prior work, no priority claimed (note dated 3 November 2026).** Conjecture 1 of Milne, Jennings, Jevtic and Rudolph ([arXiv:1404.3951](https://arxiv.org/abs/1404.3951)) states `β ≤ max(2√(2(1−c)), 2)`. The Omega Institute's public repository records a claimed Lean proof of it for every two-qubit density matrix, with supremal sharpness, in the [dossier for issue #16558](https://github.com/the-omega-institute/trureturing/blob/af41108edc85c119837189f120c6d2d9aa3f5a25/Problems/milne-jennings-jevtic-rudolph-2014-chsh-centre-bound.md), committed on 14 October 2026 at 08:40:22 UTC. Its proof also establishes, and the dossier states, the joint bound

```
M ≤ H(c,r) = 1 + (1 − r²)(1 − 2c).
```

Appendix B of Zhang, Araiza Bravo, Lorenz and Chitambar ([New J. Phys. 22, 043003 (2020)](https://doi.org/10.1088/1367-2630/ab7bef)) computes the amplitude-damping optimum `1 + α²(2p − 1)`, which is `H(c,r)` for `p = 1 − c`, `α² = 1 − r²`. Together they give the exact supremum `2√H(c,r)` at every fixed `(c, r)`. I claim no priority for Conjecture 1, the joint bound, its attaining value or the attaining family. The repository's [priority and novelty record](../../../PRIORITY_AND_NOVELTY.md#omega-steering-centre-bounds) lists the Omega records for this conjecture and for Conjecture 2. I have not compiled the Omega Lean proof and describe it as claimed.

**New here** (bounded literature comparison; worldwide novelty is not certified):

1. **Equality classification.** For `0 < c < 1` and `r < 1`, `M = H(c,r)` holds exactly for one local-unitary class: the maximally obese canonical state filtered by `√(I + b·σ)` with `|b|² = b_z`. Equality in Conjecture 1 is classified for every `c`.
2. **Rigidity.** Near equality forces trace-norm closeness to an exact extremizer with the same `c` and `r`, also with the whole centre vector fixed. Uniformly in `c`, a canonical state is within `min(2, 9 D^{1/4})` of a maximally obese state with the same Alice marginal, where `D = 1 − c + c²/2 − tr σ²`, and a rank-two separable family shows the exponent `1/4` is optimal.
3. **Full-ellipsoid envelopes.** Exact fixed-radius CHSH maxima, with every optimizing filter direction, for all translated spheres, all axial ellipsoids and all centred ellipsoids (`M_max(r) = ℓ₁ + (1 − r²)ℓ₂`), the closed optimization over `r`, and an exact CHSH-breaking criterion for axial qubit channels `x ↦ c e_z + diag(s,s,t)x`: `2s² ≤ 1` and `[s² ≤ c² + ct or (1 − s²)(s² − c²) ≥ s²t²]`. The Omega dossier lists bounds by the full ellipsoid as open; general displaced triaxial ellipsoids remain open here.
4. **Correction.** The optimizing direction printed in Appendix B of Zhang et al. does not attain the stated maximum (exact countercertificate); their maximal value and threshold are correct.

## What is verified, and how

| Part | Status |
|---|---|
| For every `0 ≤ c ≤ 1` and `r² < 1`, an explicit complex 4×4 density matrix (positivity tested on every complex vector) whose Bloch data give centre `(0,0,c)` and Bob length `r`, with CHSH supremum over all unit Pauli settings exactly `2√(1+(1−2c)(1−r²))` (`CertifiedCHSH.physical_joint_chsh_attainment`); the tilted axial witness with `β = 2√(43/40)`; the rank-two sharpness family with its exact `β`; the scalar spectral optimization behind the axial envelope (`AxialCertificates.axial_exact_maximum`); obese block algebra, orientation correction, spectral purity inequalities and the printed-direction countercertificate | **Formal.** Lean 4.19.0 with Mathlib `c44e0c8`, 15 modules, no Horodecki formula assumed for the Bell suprema. A whole-project audit covers every declaration; all depend only on `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, added axiom or `native_decide`. |
| Identities in the proofs of the equality and axial theorems, the explicit states and witnesses, the countercertificate | **Exact symbolic checks** ([check_exact.py](scripts/check_exact.py), 46 identities). |
| The joint bound and refinement on random states, the equality orbit, axial and centred envelopes against brute-force filter directions, the channel criterion | **Seeded numerical falsification searches** ([check_numeric.py](scripts/check_numeric.py)); not proofs. |
| The joint bound for arbitrary states (prior work), the general filter-to-Gram correspondence and Horodecki identification linking the scalar axial theorem to states, the equality classification, the rigidity theorems, the operational meaning of the centre | **Conventional proofs** in the manuscript; the central proofs were checked for this release. |

## Third-party code

The upload this package came from also contained a snapshot of the Omega Institute's `trureturing` sources (Apache-2.0, copyright 2026 The Omega Institute) used for a source audit, together with incomplete replay records of that project. The licence would permit redistribution with attribution, but none of that code is used or adapted here, the replay was incomplete, and the sources are public at the pinned commit, so the snapshot and its records are not included. The Lean project here is independent of it.

## Files

- [Manuscript](manuscript.pdf) and its [LaTeX source](manuscript.tex).
- [lean/](lean/): the Lean project; [ProjectAxiomAudit.lean](lean/ProjectAxiomAudit.lean) is the whole-project audit.
- [scripts/](scripts/): the verification script, the audit checker and the exact and numerical checks.
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
