# The one-sided CHSH measure under local filtering: exact supremum, violation criterion and a least-eigenvalue formula

**Fully autonomous agentic research.** Autonomous AI research agents found the results, their proofs, the Lean development and the checkers; Opus 5.5 by Anthropic used with Claude Code confirmed the problem statement against the source paper, read the central proofs, compared the Lean statements with them, ran the fresh Lean build and a whole-project axiom audit, reran every checker, wrote an independent check and reorganized the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

Dev D. Goyal · 3 November 2026

## The question

Ducuara, Susa and Skrzypczyk ([arXiv:2406.03945](https://arxiv.org/abs/2406.03945); Phys. Rev. A 110, 022435 (2024)) define the one-sided hidden CHSH measures of a two-qubit state, their Eq. (9):

```
HB_W(ρ) = max over invertible f_W of B(ρ'_{F_W}),   W ∈ {A, B},
```

where only party `W` applies the local filter `f_W ∈ GL(2, C)`, `ρ'_{F_W}` is the normalized filtered state and `B = sqrt(s₁(T)² + s₂(T)²)` is the CHSH value normalized to local bound 1 (Horodecki's formula). The paper states that, unlike the two-sided measure, there are no closed formulas for these one-sided measures, and lists them as open. This package solves the optimization for every two-qubit state. (A separate package in this collection, `one-sided-f3`, treats the companion one-sided `F₃` measures of Eq. (10).)

## The answer

Whiten the filtering party: if Alice's Bloch vector `a` has `|a| < 1`, the state `(2ρ_A)^{-1/2} ρ (2ρ_A)^{-1/2}` has the same filtering orbit, a maximally mixed Alice marginal, Bob Bloch vector `c` and correlation matrix `D`. Put

```
A = D Dᵀ,  s = |c|²,  C = [D c]×,  K = A − s I,  α = tr A − s,  M = A + C K⁻¹ C.
```

In the original Bloch data `(a, b, T)`, `α = (‖T‖²_F − |b|²)/(1 − |a|²)`.

- **A. Exact supremum for every state.** `(B_A*)²` is the maximum of an explicit quadratic `f(n, v) = tr A − nᵀAn − vᵀKv − 2vᵀCn` over `|n| = 1, n ⊥ v, |v| ≤ 1`. The boundary `|v| = 1` corresponds to rank-one limits of invertible filters, so Eq. (9) is in general a supremum, not a maximum. A pure Alice marginal forces a product state, and then `B_A* = |b|`, attained.
- **B. Closed form wherever violation is possible.** If `α > 1`, then `K ≻ 0` and `(B_A*)² = tr A − λ_min(M)`, the least eigenvalue of an explicit symmetric 3×3 matrix, attained by the invertible filter `sqrt(I + u·σ)(2ρ_A)^{-1/2}` with `v = −K⁻¹Cn`, `u = −n × v` and `n` a least eigenvector.
- **C. Exact violation criterion.** `B_A* > 1` if and only if `α > 1` and `M − (tr A − 1)I` is not positive semidefinite (equivalently, one of three polynomial signs in the Bloch data is negative); a violating supremum is always attained by an invertible filter. One-sided *hidden* activation additionally needs `s₁(T)² + s₂(T)² ≤ 1` for the original state.
- **D. The remaining states.** If `α ≤ 1` the value is at most 1. For every state, `(B_A*)²` is the largest of the boundary radius `E = max_{|u|=1} |c + Dᵀu|²` and at most three values `tr A − λ` at admissible roots of a cubic pencil; `E` is determined by a specified root of a secular equation of degree at most six, or by an explicit hard-case expression.
- **E. Further exact results.** For states of rank at most two, `(B_A*)² = 1 + max(0, ‖T‖²_F + |a|² − |b|² − 1)/(2(1 − |a|²))`; `B_A* = sqrt 2` exactly for pure entangled states; for the quasi-distillable family `p·ψ⁻ + (1 − p)|00⟩⟨00|` of the 2024 paper, `(B_A*)² = (B_B*)² = max(1, 2p/(2 − p))`; plus a three-regime classification at the local bound and exact success-probability trade-offs.

Bob's measure follows by exchanging the parties (`a ↔ b`, `T ↦ Tᵀ`).

**Closed form versus algorithm.** Results B and C are closed formulas (a 3×3 least eigenvalue, that is, the least root of an explicit cubic, and three polynomial sign tests); they cover every state that can violate and every state with `α > 1`. The rank-two formula and the pure-marginal value are closed as well. For the other states with `α ≤ 1`, which never violate, the exact sub-classical value is given by the finite algorithm of Result D: cubic pencil roots, small admissibility tests and one secular root.

## Formal, certificate-based and conventional parts

- **Lean-checked** ([lean/](lean/), Lean 4.19.0, Mathlib `c44e0c8`): for every positive semidefinite trace-one complex 4×4 matrix, every complex 2×2 filter with nonzero determinant on either party (normalized by the actual trace) and every quadruple of traceless Hermitian involutive qubit observables: the exact supremum (`all_states_operator_both_isLUB`), the least-eigenvalue formula with an attaining invertible filter for `α > 1` (`all_states_alice_schur_formula`), the violation criterion and hidden-activation criterion for both parties (`all_states_alice_operator_activation_iff`, `all_states_bob_operator_activation_iff`, `all_states_alice_operator_hidden_activation_iff`), invertible attainment of a violating supremum (`all_states_alice_operator_violation_attained` and the Bob version), the pure-marginal value (`pure_marginal_gl_isGreatest`) and the finite-candidate theorem (`original_finite_candidates`). The value for `α ≤ 1` appears as a maximum over the compact domain and as the largest of at most four candidates, with the boundary candidate an attained maximum over a sphere. A whole-project audit covers all 1,060 declarations of the 32 modules.
- **Conventional, with checks:** the secular-root evaluation of `E` and the hard case, the explicit cubic, admissibility tests and singular compression, the polynomial and rational-ellipsoid activation tests, the threshold regimes, the rank-two formula (which uses the Ruskai–Szarek–Werner classification), the `sqrt 2` characterization, the axial and quasi-distillable families, all success-probability results and the stability results.
- **Exact and numerical checks** ([calculations/](calculations/)): exact SymPy certificates of the examples and of the quasi-distillable values, and seeded comparisons against direct filtering of complex density matrices. They corroborate; no theorem rests on them.

## Prior work and priority

The question and normalization are those of Ducuara, Susa and Skrzypczyk; the optimal CHSH value is Horodecki's formula (R. Horodecki, P. Horodecki and M. Horodecki, Phys. Lett. A 200, 340 (1995)); the Lorentz picture of filtering is due to Verstraete, Dehaene and De Moor, and the two-sided optimum to Kent–Linden–Massar and Verstraete–Wolf. Zhang, Araiza Bravo, Lorenz and Chitambar ([arXiv:1911.06349](https://arxiv.org/abs/1911.06349)) solve the equivalent CHSH-breaking question for unital and several nonunital qubit channels; the formula recovers their unital case. The purity necessity is due to the Horodeckis (Phys. Lett. A 210, 377 (1996)), the rank-two normal form to Ruskai, Szarek and Werner, and the boundary secular equation is the Moré–Sorensen trust-region analysis.

**Omega Institute record (note dated 3 November 2026).** The Omega Institute's public repository [the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing) records a claimed Lean proof of Conjecture 1 of Milne, Jennings, Jevtic and Rudolph ([arXiv:1404.3951](https://arxiv.org/abs/1404.3951)), the CHSH bound at fixed steering-ellipsoid centre, committed on 14 October 2026 (issue #16558); see the [priority and novelty record](../../../PRIORITY_AND_NOVELTY.md#omega-steering-centre-bounds). Its proof uses the plane-purity identity and the filtering covariance of a conditional purity that this package also uses (with the parties exchanged); these are not claimed as new. Result 1 of Ducuara–Susa–Skrzypczyk derives one-sided inaccessibility from that conjecture, so the record already makes the inaccessible interval `0 < p ≤ 2/3` of the quasi-distillable family unconditional; no priority is claimed for it. Beyond the record, as read on 3 November 2026: the one-sided supremum for every state, the exact violation criterion, the least-eigenvalue formula, the finite candidate formula, the exact values `max(1, 2p/(2 − p))` with the sharp endpoint, and the Lean proofs for actual density matrices. Conjecture 1 is not used. The package [chsh-steering-ellipsoid](../chsh-steering-ellipsoid/) of this collection also treats Conjecture 1.

A bounded literature search did not find the new results; this does not establish priority.

## Files

- [Manuscript](manuscript.pdf), its [LaTeX source](manuscript.tex) with [sections/](sections/) and [figures/](figures/).
- [lean/](lean/): the Lean project (sources in [lean/Lean/](lean/Lean/)); [FORMAL_COVERAGE.md](lean/FORMAL_COVERAGE.md) maps results to declarations, and [UnilateralAxiomAudit.lean](lean/Lean/UnilateralAxiomAudit.lean) audits every declaration.
- [calculations/](calculations/): solvers, checkers and recorded outputs; [scripts/](scripts/): verification scripts.
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
