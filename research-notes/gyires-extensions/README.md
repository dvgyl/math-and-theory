# Supporting records for the all-order Gyires results

This directory contains the proofs and certificates for two results in arbitrary dimensions. Both appear in the [Gyires preprint](../../preprints/gyires-circulant-five/paper.pdf). The four-block theorem has a complete Lean proof and four selected Comparator statements. The permutation-polynomial theorem has a complete Lean proof in the separate `verification/gyires-permutation-polynomial` package. No novelty or independent human expert review is claimed.

| Result | Scope and proof record |
|---|---|
| [All-order permutation-polynomial inequality](permutation-polynomial.md) | A=aI+bQ+cQ^2 for any permutation matrix Q and nonnegative a,b,c. The proof uses an analytic bound and exact polynomial certificates. |
| [Four-block theorem](four-block.md) | Doubly stochastic matrices with at most two row types and two column types. The proof permits unequal block sizes and zero block entries. It gives three contraction bounds and a strict Gyires margin away from the uniform matrix. |

The principal order-five results and the all-order four-block theorem in the [paper](../../preprints/gyires-circulant-five/README.md) have complete Lean proofs. That verification does not cover the permutation-polynomial theorem. Neither argument establishes the unrestricted Gyires conjecture or the all-order rank-two assertion. The [complete supporting record](../gyires-complete-support/README.md) covers the other matrix and polynomial results in the manuscript.

The [reproduction guide](verification.md) gives the programs and recorded results. The [file record](provenance.json) lists the programs and mathematical reports. The collection integrity manifest gives their SHA-256 hashes.

## Authorship

The [authorship disclosure](../../AUTHORSHIP.md) states autonomous AI research. These results have not been peer reviewed. The proofs cite the classical results that they use.

[Return to the catalogue](../../CONTENTS.md).
