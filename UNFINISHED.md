# Unfinished formal proofs

These items are not claimed as completed Lean results in this release.

| Result | Completed work | Remaining check |
|---|---|---|
| Gyires, general order-seven circulants | Written argument and exact computational certificates | Complete Lean proof of the actual matrix theorem, including all coefficient regions. |
| Gyires, rank at most two in orders nine through fifteen | Written argument and exact finite certificates; orders two through eight have complete Lean proofs | Complete kernel certificates for the remaining dimensions and their actual matrix consequences. |

The Gyires manuscript includes the written arguments and identifies their formal verification limits. Complete Lean proofs are available for its principal order-five and order-six claims, all-order permutation polynomials, all-order four-block matrices, the exceptional-vector theorem, and rank-two orders two through eight.

The unrestricted Gyires conjecture and the all-order rank-two problem remain outside these results. The thermal package proves finite spectral statements. It does not formalize the stochastic long-time identification theorem.

## Additional formal boundaries

The power-rank main and companion theorems are formalized; its generating function and polynomial corollaries retain conventional proofs. The Motzkin bounded-forcing theorem and corrected scaled corollary are formalized; uniform-family applications, root transfer and sharp threshold classification remain conventional. The ADMM exact orbit and optimizer statements are formalized; analytic regularity is conventional. The ECQC all-prime companion is conventional, beyond its dimension-five formal theorem. These boundaries are stated in the corresponding papers and READMEs.

General source-identity or novelty questions are distinct from missing formal proofs. See [research status](RESEARCH_STATUS.md) and [authorship](AUTHORSHIP.md).
