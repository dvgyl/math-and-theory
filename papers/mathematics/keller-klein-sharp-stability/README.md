# Sharp stability and exact cap optima for Rademacher sums

**Fully autonomous agentic research.** Autonomous AI research agents produced the results, the proofs, the Lean development and the interval certificates; Opus 5.5 by Anthropic used with Claude Code rechecked them, ran fresh Lean replays and certificate checks and revised the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

This extension of the [small-coefficient Keller–Klein package](../keller-klein/) studies capped normalized Rademacher sums `X_b = Σᵢ bᵢεᵢ` with independent uniform signs, `Σᵢ bᵢ² = 1` and `|bᵢ| ≤ a`; the cap need not be attained and the number of terms is unrestricted. Write `g(b) = min_ε |Σᵢ bᵢεᵢ|` for the support gap, `c(t) = Φ(t) − 1/2`, and `K(a)` for the supremum of the Kolmogorov distance between `X_b` and the standard normal law.

## Results

1. **Global sharp inverse theorem.** If `a/2 < x ≤ g(b)`, the core `C = {i : |bᵢ| ≥ x}` has positive odd size `k`, and the distance from `(|bᵢ|)` to the flat vector `k^(−1/2)·1_C` satisfies `ρ² ≤ 2 − 2√(1 − (a − x)²)`. Equality holds exactly for `k` coefficients `a` and one residual `a − x`. The strict threshold `a/2` is sharp: `(2, 1, 1, 1)/√7` has an even core.
2. **Sharp stability of the support-gap optimum at every cap.** In the band `1/√(n+2) ≤ a ≤ 1/√n` (`n` odd), with `λ = 1/√(n+2)`, `r = √(1 − na²)`, `s = a − r` and `G = max(λ, s)`, every vector with `g(b) > max(a/2, 1/√(n+4))` lies within `√(2+√2)·(G − g(b))` of an explicit admissible vector of one of the two competing shapes `(a,…,a, r)` and the `(n+2)`-flat vector. The constant is optimal; at a tie, or when the deficit is below `|λ − s|`, the comparison vector is a global optimizer. Both shapes are needed near a switch, and the trigger endpoint cannot be included.
3. **Exact nonlinear saturated modulus.** For core size `k`, `r = √(1 − ka²) > 0` and `0 ≤ e = a − r − g(b) ≤ (√2 − 1)r`, the distance to `(a^k, r)` is at most `F_r(e) = √(r(r − e − √(r² − 2re − e²)))`, with equality exactly for a saturated core and the residual pair `(r + e ± √(r² − 2re − e²))/2`. Attaining vectors exist for every feasible odd core and deficit. The exact fixed-flat trade-off is also proved.
4. **Exact Kolmogorov cap optimum on two further intervals.**

   ```text
   K(a) = max{ c(1/√5), 3/16 − c(√(1 − 4a²)) }      for 1/√5 ≤ a ≤ 1/2,
   K(a) = max{ 3/16,    c(a − √(1 − 3a²)) }         for 1/2 ≤ a ≤ 1/√3,
   ```

   with every optimizing vector, threshold and transition. The lower-discrepancy optimum equals `c(G(a))` throughout `[1/√5, 1/√3]`, with exactly the support-gap optimizers, and the positive-discrepancy optimum is determined for every `a ≥ 1/2`. Combined with the formula for `a ≥ 1/√3` from the unpublished preceding package (below), this gives `K(a)` for every `a ≥ 1/√5`.

## Dependencies and boundaries

- **Prior work.** Keller and Klein (Adv. Math. 2022) posed the Berry–Esseen problem for Rademacher sums in their proof of Tomaszewski's conjecture. The probability results use, as stated inputs, the completed Keller–Klein comparison `d_K(X, N(0,1)) ≤ c(maxᵢ|bᵢ|)`, the Hollom–Portier strict-tail profile (Random Structures & Algorithms 2025) and Tomaszewski's theorem. The comparison combines the [earlier package](../keller-klein/) with Ivanisvili's computer-assisted Theorems 1.1 and 10.9 (21 October 2026), which are external and unrefereed, so result 4 is conditional on them. The computer-assisted part of the Hollom–Portier proof is not replayed. Results 1–3 use none of these inputs.
- **Preceding package.** The exact support-gap optimum `G(a)` and the formulas for `a ≥ 1/√3` and for small caps come from an unpublished expanded research package of 1 November 2026 that is not in this repository. The manuscript reproves `G(a)` but only cites the formula for `a ≥ 1/√3`. Nine of that package's Lean modules, on which the new development depends, are included here and replayed.
- **Literature.** De–Diakonikolas–Servedio, Fang–Wang and Xie proved sharp stability for moment inequalities, and Pinelis used the core-plus-residual vectors; the manuscript compares these and does not claim the elementary hypersimplex inequalities. The literature comparison is bounded and does not establish priority.

## Verification scope

- **Formal (Lean 4.19.0, Mathlib `c44e0c8`).** Results 1–3 for actual finite signed vectors and their actual `supportGap`: the inverse inequality and its equality classification, all-cap stability with an explicitly constructed admissible comparison and its optimality under the phase condition, the saturated modulus and its equality equivalence, attainment for every odd core, both fixed-flat inequalities, the witness for the optimal constant and the even-core example at the threshold `a/2`. The 15 new modules print 67 axiom audits, all within `propext`, `Classical.choice` and `Quot.sound`; no `sorry`, added axiom or `native_decide` occurs.
- **Conditional (Lean).** The two-module probability bridge derives the four-shift mixture of the actual finite Rademacher law, the open/closed tail identities, residual normalization and the scalar envelope. Its Gaussian comparisons, strict-tail profile, exponential and above-one tail estimates are explicit hypotheses.
- **Conventional and certificate-based.** The probability optima of result 4, the equality analysis of the fixed-flat trade-off, the trigger-endpoint obstruction and the two-core and four-core localizations are written proofs. Their scalar inequalities are checked with exact rationals, and the lower-discrepancy envelope by validated interval arithmetic (python-flint 0.9.0 / Arb) on 27,972 exact rational boxes.

## Correspondence

Correspondence with Paata Ivanisvili about the Keller–Klein conjecture on 30–31 October 2026 is listed in [CORRESPONDENCE.md](../../../CORRESPONDENCE.md). It concerned the earlier package; it does not imply verification or endorsement of this extension.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [Lean project](lean/): the new modules in [stability/](lean/stability/), [attainment/](lean/attainment/) and the conditional [bridge/](lean/bridge/); the nine inherited modules in [support-gap/](lean/support-gap/); the 62 modules of the earlier package, unchanged, in [KellerKlein/](lean/KellerKlein/); and the verifier [verify.py](lean/verify.py).
- [Certificates](certificates/): exact phase checks, interval verifiers, the compressed box partitions and the 128-bit reports.
- [Third-party provenance](third_party/causalsmith/UPSTREAM.txt) for three Apache-2.0 support modules adapted from CausalSmith in the earlier package.
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
