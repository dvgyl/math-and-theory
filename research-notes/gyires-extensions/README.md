# Supporting records for the all-order Gyires results

This directory contains the proofs and certificates for two results in arbitrary dimensions. Both appear in the [Gyires preprint](../../preprints/gyires-circulant-five/paper.pdf). Lean formalization, a full prior-work assessment, and independent human expert review remain incomplete. Neither result is among the 21 selected Comparator statements.

| Result | Scope and proof record |
|---|---|
| [All-order permutation-polynomial inequality](permutation-polynomial.md) | A=aI+bQ+cQ^2 for any permutation matrix Q and nonnegative a,b,c. The proof uses an analytic bound and exact polynomial certificates. |
| [Four-block theorem](four-block.md) | Doubly stochastic matrices with at most two row types and two column types. The proof permits unequal block sizes and zero block entries. It gives three contraction bounds and a strict Gyires margin away from the uniform matrix. |

The principal order-five results in the [paper](../../preprints/gyires-circulant-five/README.md) have complete Lean proofs. That verification does not cover these all-order arguments. Neither argument establishes the unrestricted Gyires conjecture or the all-order rank-two assertion. The [complete supporting record](../gyires-complete-support/README.md) covers the other matrix and polynomial results in the manuscript.

The [reproduction guide](verification.md) gives the programs and recorded results. The [source record](provenance.json) identifies the research archive and source files by SHA-256 hash. The [review record](review.md) states the scope of the AI review.

## Historical source record

The collection at commit `568a20f7e29db12a7890f695a296734780ce71c5` contained the formally verified subset. These two all-order arguments were added after that version. Its review approval therefore does not cover them.

The permutation-polynomial proof is recorded in round 2 and uses the later sharp spectral bound. The four-block proof is recorded in round 5. The consolidated source retains both. The finite rank-two results through order fifteen have a different scope.

## Authorship and review

Dev D. Goyal directed the AI-generated research and is responsible for publication. The [collection authorship record](../../AUTHORSHIP.md) identifies the human and AI contributions. These arguments have a separate AI review record. They have not been peer reviewed by human experts. No novelty or first-priority claim is made. The proofs credit the classical results that they use.

[Return to the catalogue](../../CONTENTS.md).
