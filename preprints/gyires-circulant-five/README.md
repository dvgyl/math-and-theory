# Gyires's permanent inequality for structured matrices

I present proofs of Gyires's permanent inequality for several structured matrix classes. I also include scalar and polynomial inequalities that support further extensions.

| Result | Scope | Verification status |
|---|---|---|
| Order-five circulants | All nonnegative weights, equality, and sharp margin 484 | Principal claims have complete Lean proofs. |
| Order-six circulants | All nonnegative weights, equality, and sharp reduced margin 296 | Complete Lean proof and exhaustive exact certificates. |
| Order-seven circulants | All nonnegative weights, equality, and sharp reduced margin 116929 | Ordinary proof with exhaustive exact certificates; Lean proof incomplete. |
| Permutation polynomials | A=aI+bQ+cQ² for any permutation matrix Q and nonnegative coefficients, in every dimension | Complete Lean proof with exact certificates and an analytic tail. |
| Four-block matrices | At most two row types and two column types, with unequal sizes and boundary entries | Complete ordinary proof and complete Lean proof of the matrix theorem. |
| One exceptional vector | All columns but one identical, or all rows but one identical, for every order n ≥ 2 | Complete ordinary and Lean proofs of both strong bounds, Gyires’s inequality, and equality exactly at the uniform matrix. |
| Rank at most two | Every doubly stochastic matrix of rank at most two through order fifteen | Complete ordinary proof with exhaustive interval certificates. Complete Lean proof for orders two through eight. |
| Structural and polynomial results | Sparse perturbations, closure, boundary reduction, scalar inequalities, deletion, balanced limits, local stable and Lorentzian results, and configuration identities | Complete ordinary arguments within their stated hypotheses. |

The rank-two theorem has a complete Lean proof for orders 2 through 8. The general order-seven circulant theorem and rank-two orders 9 through 15 remain incomplete in Lean. Separate Lean packages prove the principal order-six and all-order permutation-polynomial theorems. The paper states which inequalities remain unproved after each reduction. Exact counterexamples identify failed auxiliary assertions. The [source map](../../research-notes/gyires-complete-support/source-map.md) records inclusion and subsumption.

The manuscript includes the full arguments, boundary cases, equality statements where proved, exact certificate recurrences, and the order-five, order-six, permutation-polynomial, four-block, and exceptional-vector Lean correspondences. It does not prove the unrestricted Gyires conjecture. I make no novelty or first-priority claim.

- [Compiled preprint](paper.pdf).
- [Manuscript source](paper.tex) and [references](references.bib).
- [Suggested citation](citation.bib).
- [Formal proof guide](../../lean/docs/gyires-circulant-five.md).
- [Formal verification](../../verification/gyires-circulant-five/README.md).
- [Supporting proofs and certificates](../../research-notes/gyires-complete-support/README.md).
- [All-order proofs and certificates](../../research-notes/gyires-extensions/README.md).
- [Attribution notice](NOTICE).

The [authorship disclosure](../../AUTHORSHIP.md) states autonomous AI research. This preprint has not been peer reviewed.

Rebuild the preprint with `tectonic paper.tex`. The bibliography is a separate BibTeX file.

## Research process and review

The initial research and proofs were generated autonomously by GPT 6 with Pro Reasoning in ChatGPT. GPT 6 Astra in Codex autonomously produced the formalizations and corrections. I checked the proofs to the best of my mathematical abilities. This check is not expert validation or peer review. I am responsible for publication.
