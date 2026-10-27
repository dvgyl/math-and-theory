# Supporting records for the all-order Gyires results

This directory contains the proofs and certificates for two results in arbitrary dimensions. Both appear in the [Gyires preprint](../../preprints/gyires-circulant-five/paper.pdf). Lean formalization, a full prior-work assessment, and independent human expert review remain incomplete. Neither result is among the 21 selected Comparator statements.

| Result | Scope and proof record |
|---|---|
| [All-order permutation-polynomial inequality](permutation-polynomial.md) | A=aI+bQ+cQ^2 for any permutation matrix Q and nonnegative a,b,c. The proof uses an analytic bound and exact polynomial certificates. |
| [Four-block theorem](four-block.md) | Doubly stochastic matrices with at most two row types and two column types. The proof permits unequal block sizes and zero block entries. It gives three contraction bounds and a strict Gyires margin away from the uniform matrix. |

The principal order-five results in the [paper](../../preprints/gyires-circulant-five/README.md) have complete Lean proofs. That verification does not cover these all-order arguments. Neither argument establishes the unrestricted Gyires conjecture or the all-order rank-two assertion. The [complete supporting record](../gyires-complete-support/README.md) covers the other matrix and polynomial results in the manuscript.

The [reproduction guide](verification.md) gives the programs and recorded results. The [file record](provenance.json) lists the programs and mathematical reports. The collection integrity manifest gives their SHA-256 hashes.

## Authorship

The [authorship disclosure](../../AUTHORSHIP.md) states the use of AI assistance. These results have not been peer reviewed. The proofs cite the classical results that they use.

[Return to the catalogue](../../CONTENTS.md).
