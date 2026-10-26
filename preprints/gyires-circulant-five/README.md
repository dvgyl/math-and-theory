# Gyires's permanent inequality for structured matrices

This preprint proves Gyires's permanent inequality for several structured matrix classes. It also develops scalar and polynomial inequalities that support further extensions.

| Result | Scope | Verification status |
|---|---|---|
| Order-five circulants | All nonnegative weights, equality, and sharp margin 484 | Principal claims have complete Lean proofs. |
| Order-six and order-seven circulants | All nonnegative weights, equality, and sharp reduced margins 296 and 116929 | Complete ordinary proofs with exhaustive exact certificates. |
| Permutation polynomials | A=aI+bQ+cQ² for any permutation matrix Q and nonnegative coefficients, in every dimension | Complete ordinary proof with exact certificates and an analytic tail. |
| Four-block matrices | At most two row types and two column types, with unequal sizes and boundary entries | Complete ordinary probability proof. |
| One exceptional vector | All columns but one identical, or all rows but one identical, in every order | Complete ordinary proof of both strong bounds. |
| Rank at most two | Every doubly stochastic matrix of rank at most two through order fifteen | Complete ordinary proof with exhaustive interval certificates. |
| Structural and polynomial results | Sparse perturbations, closure, boundary reduction, scalar inequalities, deletion, balanced limits, local stable and Lorentzian results, and configuration identities | Complete ordinary arguments within their stated hypotheses. |

Lean formalization of the broader results is incomplete. The paper states which inequalities remain unproved after each reduction. Exact counterexamples identify failed auxiliary assertions. The [source map](../../research-notes/gyires-complete-support/source-map.md) records inclusion and subsumption.

The manuscript includes the full arguments, boundary cases, equality statements where proved, exact certificate recurrences, and the order-five Lean correspondence. It does not prove the unrestricted Gyires conjecture. It makes no novelty or first-priority claim.

- [Compiled preprint](paper.pdf).
- [Manuscript source](paper.tex) and [references](references.bib).
- [Suggested citation](citation.bib).
- [Integrated preprint review](review.md).
- [Order-five formal proof guide](../../lean/docs/gyires-circulant-five.md).
- [Order-five verification](../../verification/gyires-circulant-five/README.md).
- [Complete source records and certificates](../../research-notes/gyires-complete-support/README.md).
- [Earlier all-order extension records](../../research-notes/gyires-extensions/README.md).
- [Attribution notice](NOTICE).

The directory name remains stable to preserve existing links and formal identifiers. The [earlier order-five-only manuscript](https://github.com/dvgyl/math-and-theory/blob/b7e67bf67df0e2476a499f2de5df3cb274672484/preprints/gyires-circulant-five/paper.pdf) remains available in Git history. Its result revises the [original order-five development](https://github.com/dvgyl/gyires-circulant-5/tree/72cf49a51be42cf15592f91d991f0b0c76f58448).

Dev D. Goyal directed the AI-assisted research and accepts responsibility for publication. The manuscript discloses the use of GPT-6, Claude Opus 5.5, and Codex. It has not received independent human expert review or peer review. The author's recorded personal review covers the earlier order-five proofs only.

Rebuild the preprint with `tectonic paper.tex`. The bibliography is a separate BibTeX file.
