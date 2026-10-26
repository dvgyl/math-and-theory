The expanded [continuous preprint](../../preprints/gyires-circulant-five/paper.pdf) now includes all completed arguments from the supplied Gyires materials. See the [complete supporting record](../gyires-complete-support/README.md). This directory preserves the earlier all-order source and certificate record.

# Later Gyires results

This research record contains two claimed results in arbitrary dimensions. Both have complete written arguments in the supplied research materials. Their Lean formalizations, novelty assessment, and independent human expert review remain incomplete. They are included with the earlier order-five result in the [continuous Gyires preprint](../../preprints/gyires-circulant-five/paper.pdf). They are outside the 21 selected Comparator statements.

| Claimed result | Scope and proof record |
|---|---|
| [All-order permutation-polynomial inequality](permutation-polynomial.md) | A=aI+bQ+cQ^2 for any permutation matrix Q and nonnegative a,b,c. The argument uses an analytic bound and exact polynomial certificates. |
| [Four-block theorem](four-block.md) | Doubly stochastic matrices with at most two row types and two column types. The argument includes unequal block sizes, zero block entries, three contraction bounds, and a strict Gyires margin away from the uniform matrix. |

The principal order-five results in the [combined paper](../../preprints/gyires-circulant-five/README.md) have completed Lean verification. Those checks do not extend to these two later arguments. Conversely, these arguments are not limited to order five. Neither argument establishes the unrestricted Gyires conjecture or the arbitrary-rank-two all-order claim.

The [reproduction record](verification.md) gives the exact programs and current results. The [source record](provenance.json) identifies the supplied archive and the source files by SHA-256 hash. The [review record](review.md) states the scope of the correction review.

## Relation to the earlier collection

The initial public collection at commit `568a20f7e29db12a7890f695a296734780ce71c5` included the formally verified subset. Its private inventory also recorded these later arguments, but the public collection omitted them. This correction makes both developments available with their actual verification status. It does not report a defect in the earlier order-five Lean theorem.

The permutation argument comes from round 2, with the later sharp spectral bound. The four-block argument comes from round 5. The final consolidated source retains both. The round-6 finite-order rank-two work does not supersede either all-order result.

## Authorship and review limits

Dev D. Goyal directed the AI-generated research and is responsible for publication. The supplied materials record AI-generated mathematical arguments. The present correction edits those arguments, expands the matrix identities, and supplies reproduction instructions. The [collection authorship record](../../AUTHORSHIP.md) states the broader contribution history.

The existing two-pass review of the seven formalized families did not approve these extensions. The correction has a separate AI review record. AI review is not independent human expert validation or peer review. These arguments have not been peer reviewed. No novelty or first-priority claim is made. The proofs credit the classical results that they use.

[Return to the catalogue](../../CONTENTS.md).
