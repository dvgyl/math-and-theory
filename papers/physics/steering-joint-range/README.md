# The full correlation range, filtering frontier and volume trade-off at fixed steering centre

**Fully autonomous agentic research.** Autonomous AI research agents found the results, their proofs, the Lean development and the checkers, starting from the earlier package [steering-bounds](../steering-bounds/); Opus 5.5 by Anthropic used with Claude Code read the central proofs, compared the Lean statements with them, reran the checkers, wrote an exact check and a whole-project axiom audit, ran the fresh Lean build and edited the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

Dev D. Goyal · 3 November 2026

For a two-qubit state with Pauli correlation matrix `T`, put `F₃ = ‖T‖_F`, the three-setting correlation value of Eq. (3) of Ducuara, Susa and Skrzypczyk ([arXiv:2406.03945](https://arxiv.org/abs/2406.03945)); violation means `F₃ > 1`. Let `c` be the centre length of Alice's steering ellipsoid and `r` the length of Bob's Bloch vector. The earlier package [steering-bounds](../steering-bounds/) (29 October 2026) proved that the supremum of `F₃²` at fixed `c` is `G(c) = 1 + (2−3c)²/(2−2c−c²)` for `c ≤ 2/3` and `1` above, so that violation is possible exactly when `c < 2/3`; it also proved the joint upper bound `F₃² ≤ H(c,r)` below and its attainment by one explicit family. This package determines the rest.

**Theorem 1 (joint range).** For `0 ≤ c ≤ 1` and `0 ≤ r < 1`, the values of `F₃²` over all two-qubit density matrices with centre length `c` and Bob Bloch length `r` form exactly the interval

```
[ max(0, c(1+r) − 1)² ,  H(c,r) ],   H(c,r) = (1 − r²)(3 − 4c) + (c + (1 − c)r)².
```

The lower endpoint is attained by states diagonal in a product basis, hence separable; every minimizer is locally unitarily equivalent to that witness; and a state with `F₃² = L + η` is within squared trace norm `(1 + r²)η` of an explicit minimizer with the same axes. At `r = 1` the only value is `c²`. In particular, a nonzero centre forces nonzero correlation exactly when `c(1+r) > 1`.

**Theorem 2 (volume–correlation trade-off).** For a canonical state (Bob maximally mixed) with centre `c n`, radial support half-width `t = |Sᵀn|` and squared correlation `τ = ‖S‖_F²`, the feasible values are exactly `0 ≤ t ≤ 1 − c` and `t² ≤ τ ≤ 1 − c² + 2t²`. The signed determinant fills `[−t((1+t)² − c²)/4, t((1−t)² − c²)/4]`, and at prescribed `(c, t, τ)` the largest steering-ellipsoid volume is

```
(4π/3) · (t/2) · min(τ − t², 1 + 2t + 2t² − c² − τ),
```

attained at every feasible triple. At `t = 1 − c` this recovers the fixed-centre maximum `(4π/3)(1 − c)²` of Milne, Jevtic, Jennings, Wiseman and Rudolph ([arXiv:1403.0418](https://arxiv.org/abs/1403.0418), Theorem 3). For some triples two maximizing local-unitary classes of opposite determinant sign exist.

**Theorem 3 (filtering with a success budget).** There is a canonical input of centre length `c` and a Bob Kraus operator succeeding with probability at least `p ∈ [1/2, 1]` whose normalized output has `F₃ > 1` exactly when `c < 2/(1 + p + √((1−p)² + 2))`; the thresholds are `2/3` at `p = 1/2` and `2 − √2` at `p = 1`. The best output value is `H(c, r̂)` with `r̂` the vertex of `H(c, ·)` clipped to `[0, (1−p)/p]`.

The manuscript also solves every one-sided filtering orbit of a canonical state exactly, by a spectral algorithm with at most seven algebraic candidates that covers singular and hard cases, classifies the maximizers of `G(c)` up to local unitaries with explicit trace-norm rigidity, and gives sharp stability exponents on the unattained branch. These results concern the matrix quantity `F₃`; they do not characterize steering under all measurements.

## What is new relative to steering-bounds

New here: the lower bound and the full joint interval with its endpoint classification and stability; the canonical `(c, t)` interval; the signed and three-parameter volume bounds; the probability-constrained frontier; the complete one-sided orbit solution; the classification and rigidity of the maximizers of `G(c)`; the flat-branch exponents. Carried over from steering-bounds and recalled in the manuscript: `G(c)`, the threshold `c < 2/3`, the upper bound `H(c,r)` with its attaining family, and the fully entangled fraction bound, whose eighteen Lean modules are included unchanged because the new modules import them. Trust-region theory (Moré–Sorensen, Fortin–Wolkowicz), the steering-ellipsoid framework and maximally obese states (Jevtic et al., Milne et al.), and the measurement optimization behind `F₃` (Costa–Angelo) are credited where used. A bounded literature search did not find the new frontiers; this does not establish priority.

## Earlier public work

On 31 October 2026 a check of public problem records found that the Omega Institute's public repository [the-omega-institute/trureturing](https://github.com/the-omega-institute/trureturing) records a claimed Lean proof of Conjecture 2 of Milne, Jennings, Jevtic and Rudolph ([arXiv:1404.3951](https://arxiv.org/abs/1404.3951)), the fully entangled fraction bound `f ≤ 1 − c/2`, committed on 8 October 2026 (issue #14206), and a proof of their Conjecture 1 on the CHSH value at fixed centre, committed on 14 October 2026 (issue #16558); see the [priority and novelty record](../../../PRIORITY_AND_NOVELTY.md#omega-steering-centre-bounds). This package includes, unchanged from steering-bounds, a Lean proof of the fully entangled fraction bound; no priority is claimed for it, and it is not a result of this package. The CHSH record concerns a different quantity; as an intermediate lemma it bounds the CHSH value in terms of both `c` and Bob's Bloch length, and it lists the `F₃` centre bound as open. As read on 3 November 2026, neither record contains the `F₃²` lower bound or interval, the probability frontier, the filtering orbits or the volume bounds.

## How it is checked

- [lean/](lean/): Lean 4.19.0 with Mathlib proves, for actual complex 4×4 density matrices, Kraus operators and local unitaries: the joint interval (`jointSteeringSpectrum_eq_Icc`), the lower-endpoint equality and trace-norm rigidity, the canonical `(c, t)` interval, the probability frontier from actual Kraus contractions (`successPhysicalSpectrum_isGreatest`, `successPhysicalSpectrum_violation_iff`), the complete orbit solution, the classification and rigidity of the maximizers (`global_steering_equality_iff`), and the signed and three-parameter volume maxima (`physicalTripleVolumeSpectrum_isGreatest`). The volume theorem fixes the marked Alice axis to `e_z`. [FORMAL_COVERAGE.md](lean/FORMAL_COVERAGE.md) maps results to declarations. A whole-project audit checks every declaration of the 70 modules.
- Conventional proofs only: the flat-branch exponents, the orbit classification and rank counts of the volume maximizers, attainment of every signed determinant, and the identification of `‖T‖_F` with the optimized CJWR expression and of the canonical centre with the steering-ellipsoid centre.
- [calculations/](calculations/): exact rational certificates and seeded numerical checks; `python3 scripts/run_checks.py` replays all of them and compares with the recorded outputs. They corroborate, and no theorem rests on them.

## Files

- [Manuscript](manuscript.pdf), its [LaTeX source](manuscript.tex) with [sections/](sections/) and [figures/](figures/).
- [lean/](lean/): the Lean project; [MilneAxiomAudit.lean](lean/Lean/MilneAxiomAudit.lean) audits it.
- [calculations/](calculations/): checkers and recorded outputs; [scripts/](scripts/): verification scripts.
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
