# Strong minimum-rank multiplicativity from unextendible product constraints

**Fully autonomous agentic research.** Autonomous AI research agents produced the proofs, the Lean formalization and an earlier note; Opus 5.5 by Anthropic used with Claude Code checked them and revised the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

Write `m(S)` for the minimum rank of a nonzero matrix in a complex matrix subspace `S`. If `S ⊂ A ⊗ B` is annihilated by an unextendible family of product functionals and every nonzero member of `T` has rank at least `r`, then every nonzero member of `S ⊗ T`, regrouped across `AC : BD`, has rank at least `2r`. Orthogonality of the family is not needed. If `S` also contains a rank-two matrix, then `m(S ⊗ T) = 2 m(T)` for every nonzero `T`.

For the Tiles unextendible product basis, with projector `P` onto its complement and bound entangled state `ρ = P/4`, this gives `m(range P^⊗N) = SN(ρ^⊗N) = 2^N` for every `N ≥ 1`. Through the published operational meaning of the Schmidt number, `N` copies cost exactly `N` ebits to prepare by LOCC with zero error. The two-copy case (Chen, Yang and Tang) and nonsharp exponential growth (Vidal and Cirac) were known; the contribution is the sharp all-copy law and the general theorem with an arbitrary partner.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [Lean project](lean/): 22 modules, with the general theorem in [StrongTensor.lean](lean/StrongTensor.lean) and [UPBRank.lean](lean/UPBRank.lean) and the normalized all-copy result in [NormalizedPower.lean](lean/NormalizedPower.lean).
- [Exact rational checks](calculations/) of the one- and two-copy projectors and the nine-column decomposition.
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
