# Gyires's permanent inequality for structured matrices

This is one continuous preprint. It combines the earlier order-five result with the two later all-order arguments. Shared definitions and permanent identities connect the three proof sections.

| Result | Scope | Verification status |
|---|---|---|
| Order-five circulants | All nonnegative weights, equality, and a sharp sorted-gap margin with coefficient 484 | Principal claims have complete Lean proofs. |
| Permutation polynomials | A=aI+bQ+cQ² for any permutation matrix Q and nonnegative a,b,c in every dimension | Complete ordinary argument with exact polynomial certificates. Lean verification is incomplete. |
| Four-block matrices | Doubly stochastic matrices with at most two row types and two column types, including unequal block sizes and zero entries | Complete ordinary probability argument. Lean verification is incomplete. |

The manuscript includes the full arguments, boundary cases, equality statements where proved, exact certificate recurrences, and the order-five Lean correspondence. It does not prove the unrestricted Gyires conjecture. It makes no novelty or first-priority claim.

- [Compiled preprint](paper.pdf).
- [Manuscript source](paper.tex) and [references](references.bib).
- [Suggested citation](citation.bib).
- [Integrated preprint review](review.md).
- [Order-five formal proof guide](../../lean/docs/gyires-circulant-five.md).
- [Order-five verification](../../verification/gyires-circulant-five/README.md).
- [All-order source notes and certificates](../../research-notes/gyires-extensions/README.md).
- [Attribution notice](NOTICE).

The directory name remains stable to preserve existing links and formal identifiers. The [earlier order-five-only manuscript](https://github.com/dvgyl/math-and-theory/blob/b7e67bf67df0e2476a499f2de5df3cb274672484/preprints/gyires-circulant-five/paper.pdf) remains available in Git history. Its result revises the [original order-five development](https://github.com/dvgyl/gyires-circulant-5/tree/72cf49a51be42cf15592f91d991f0b0c76f58448).

Dev D. Goyal directed the AI-assisted research and accepts responsibility for publication. The manuscript records the original GPT-6 and Claude Opus 5.5 contributions, the later supplied proofs, and the Codex audit and integration. It has not received independent human expert or journal peer review. The earlier personal review applies only to the original order-five proofs.

Rebuild the preprint with `tectonic paper.tex`. The bibliography is a separate BibTeX file.
