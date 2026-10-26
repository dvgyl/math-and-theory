# Gyires's inequality for circulants of order five

This paper proves Gyires's permanent inequality for all nonnegative circulant matrices of order five. It proves the stronger bound `24 per(CCᵀ) ≤ 625 per(C)²`, with equality exactly for constant weights. It also proves a sharp sorted-gap bound with constant 484. The full conjecture for arbitrary order-five matrices remains open in the sources consulted.

The result is a revision of the existing [order-five development](https://github.com/dvgyl/gyires-circulant-5/tree/72cf49a51be42cf15592f91d991f0b0c76f58448). It is not a new result discovered in the collection audit. The prior-work and review limits are stated in the manuscript.

- [Manuscript source](paper.tex) and [references](references.bib).
- [Compiled manuscript](paper.pdf).
- [Suggested citation](citation.bib).
- [Formal proof guide](../../lean/docs/gyires-circulant-five.md).
- [Verification record](../../verification/gyires-circulant-five/README.md).
- [Attribution notice](NOTICE).

Dev D. Goyal directed the AI-assisted research and accepts responsibility for this paper. The original source records that GPT-6 with Pro reasoning found the proof and wrote the initial Lean development. It records that Claude Opus 5.5 ported the proof and revised the manuscript. The current audit preserves this historical account without claiming to have verified those model identities. The manuscript has not received independent human expert or journal peer review.

Rebuild the manuscript with `tectonic paper.tex`. The bibliography is a separate BibTeX file.
