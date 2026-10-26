# Review of the complete Gyires preprint

Two separate GPT-6.1 Sol reviews approved the complete 101-page manuscript on 26 October 2026. Both final verdicts are PASS within the stated ordinary-proof scope. No blocking review finding remains. The earlier three-case edition is preserved at commit `08a3237cf70f64c1f9157ad1962585bad4040bbb`.

## Scope

Both reviews read the complete mathematical argument. The second review also compared all 45 positive entries in the [source map](../../research-notes/gyires-complete-support/source-map.md) with the manuscript. All entries are included or explicitly subsumed. The nine central limitations are covered. The remaining historical failures of auxiliary approaches are identified in the source map. They are not presented as positive theorems.

The manuscript includes order-five, order-six, and order-seven circulants; all-order permutation polynomials; all-order four-block matrices; one exceptional column or row; rank-at-most-two matrices through order fifteen; and the completed structural, scalar, deletion, balancing, local polynomial, and counting arguments. Reductions retain their unproved final targets.

Only the stated order-five principal claims have completed Lean verification. The broader arguments remain ordinary proofs or exact computational proofs. The reviews do not establish novelty, priority, independent human expert validation, or peer review.

## Findings and corrections

The subgroup-coset corollary needed an explicit normalization before the stochastic direct-sum lemma. The final proof handles the zero matrix separately, divides nonzero blocks by their common row sum, and restores the scale by homogeneity.

A scalar subsection contained a literal Markdown heading. The final source uses a LaTeX heading.

The coverage review identified a missing multivariate localization obstruction. The uniform-cubic example did not establish that distinct result. The final manuscript now proves the supported-direction restriction for `(x+y)(y+z)(z+x)`, the Hessian determinant obstruction, the binary marginal properties, the exact norm failure, and the one-sided Lorentzian path. Both reviewers independently checked the added proof and reran its exact checker.

The source map now gives the sharp transfer constant as `1+sqrt(2)`. The verification guide now describes all broader additions, rather than only the earlier two all-order arguments.

Both reviewers checked the final corrected manuscript and bibliography hashes. The second review did not read the first review's findings or verdict before its independent assessment.

## Independent computations

The reviews reran the order-five checker over all 120 sorting orders; the independent order-six and order-seven checks over all 60 and 120 chambers; the permutation certificate through order 47; the exhaustive rank-two certificate through order 15; and the cubic deletion checks through all 720 sorting orders.

The order-six and order-seven certificates cover 5,022,480 coefficient positions. The rank-two certificate covers 33,607 whole parameter intervals and 3,524,206 coefficient positions. The permutation certificate covers 135 chamber records and 224,550 coefficient positions. Mathematical output fields matched the supplied records. Timing fields were excluded from equality comparisons.

The independent checks also covered the one-special-column algebra, the order-four two-shift deletion polynomial, configuration-model expectations, rank-two closure examples, local polynomial identities, the new multivariate obstruction, and the exact rational limitations. The second review compared 23 regenerated reports with the publication records and found no mathematical difference. It also checked all 86 support-manifest hashes. The order-five report matched exactly.

The primary citation checks covered the Lorentzian closure results, the hyperbolicity-to-stability result, and the Schur–Szegő composition theorem. The prior-work search limits in the manuscript remain in force.

## Reviewed files

| File | SHA-256 |
|---|---|
| `paper.tex` | `3a087dbc921ebe72680b894cf970ce0cfad47f3aa070aab47d48d77b031c498d` |
| `references.bib` | `4b318b6fb12c6934ca4d245fdefaa240f0460aa6641b19bbcd6395bd7cc504be` |
| `paper.pdf` | `6e02b05f297ff7f59af323016025f0dec032b9038c9ae245c9432af9f56f8114` |

The final manuscript and collection overview compiled with Tectonic 0.17.0. No undefined reference, citation error, duplicate bibliography entry, or overfull box remains. The manuscript has one underfull paragraph warning. Visual inspection found no clipping. All 101 manuscript pages and all four overview pages were rendered and inspected.

The Lean tree and the other six papers are unchanged from the reviewed baseline. No new Lean build, axiom audit, Comparator run, or independent-kernel run is claimed for this expansion. Their existing records retain their original scope.
