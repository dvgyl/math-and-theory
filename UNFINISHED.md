# Unfinished formal proofs

These items are not claimed as completed Lean results in this release.

| Result | Completed work | Remaining check |
|---|---|---|
| Gyires, general order-seven circulants | Written argument and exact computational certificates | Complete Lean proof of the actual matrix theorem, including all coefficient regions. |
| Gyires, rank at most two in orders nine through fifteen | Written argument and exact finite certificates; orders two through eight have complete Lean proofs | Complete kernel certificates for the remaining dimensions and their actual matrix consequences. |

The Gyires manuscript includes the written arguments and identifies their formal verification limits. Complete Lean proofs are available for its principal order-five and order-six claims, all-order permutation polynomials, all-order four-block matrices, the exceptional-vector theorem, and rank-two orders two through eight.

The unrestricted Gyires conjecture and the all-order rank-two problem remain outside these results. The thermal package proves finite spectral statements. It does not formalize the stochastic long-time identification theorem.

## Additional formal boundaries

The power-rank main and companion theorems are formalized; its generating function and polynomial corollaries retain conventional proofs. The Motzkin bounded-forcing theorem and corrected scaled corollary are formalized; uniform-family applications, root transfer and sharp threshold classification remain conventional. The ADMM exact orbit and optimizer statements are formalized; analytic regularity is conventional. The ECQC all-prime companion is conventional, beyond its dimension-five formal theorem. For the ADMM multiplier-step interval, individual objective-value limits and attainment for proper closed convex functions are conventional; the exact threshold between 1.886 and 1.8868954… is open. For subcritical Nesterov flows, the planar escape for 0 < r ≤ 1 with the explicit valley, its boundedness for r > 2 and existence for r ≤ 1 are conventional, and the finite-dimensional range 2 < r < 3 is open. The Chambolle–Pock limsup bound is a direct consequence of the formal family, not a separate Lean theorem. The critical hard-core mixing-time corollary rests on a published proposition and is not formalized. For the binary spectral tile, minimality of dimension nine rests on an external dimension-eight theorem, and whether every spectral 64-point subset of F₂⁹ tiles is open. For the Tiles-state Schmidt numbers, the zero-error LOCC cost and the rank-four two-qutrit class use published results and are not formalized. These boundaries are stated in the corresponding papers and READMEs.

General source-identity or novelty questions are distinct from missing formal proofs. Each entry in the [catalogue](CONTENTS.md) states its scope; [authorship](AUTHORSHIP.md) explains the review limits.
