# Diagonal concavity does not imply concavity for sums of elementary symmetric polynomials

The paper disproves Lachaume's Conjecture 1. It gives a complete parameter classification for a family in four variables. Concavity on the positive diagonal holds for more parameters than concavity on the whole positive orthant.

Read the [paper](paper.pdf), [LaTeX source](paper.tex), or [references](references.bib). Use [citation.bib](citation.bib) to cite this paper. The [Lean guide](../../lean/docs/diagonal-concavity.md) gives the theorem map. The [verification guide](../../verification/diagonal-concavity/README.md) gives reproduction commands and test limits.

## Exact scope

Let `σ_j` be the unnormalized elementary symmetric polynomial of degree `j` in four variables. For `M>0`, set

`f_M = 1 + Mσ_1 + σ_2 + Mσ_3 + σ_4`.

The theorem concerns the real fourth root of `f_M`:

- It is concave on the positive diagonal exactly when `M≥1`.
- It is concave on the whole positive orthant exactly when `M=1`.

Thus every `M>1` gives a counterexample to diagonal testing. At `M=2`, a separate rational midpoint certificate gives a finite strict violation. The result does not classify arbitrary coefficient vectors or other dimensions.

## Source and prior work

[Lachaume, Conjecture 1](https://arxiv.org/html/1712.10327v1) uses nonnegative coefficients, the positive orthant, and concavity after the `1/p` power. Here `n=p=4`, and every coefficient is positive. The formal definitions use the same convention for elementary symmetric polynomials.

The new content is the degree-four counterexample and its full one-parameter classification. The known geometric-mean argument at `M=1` is supporting material. Lachaume's Theorem 3.3 treats `sqrt(a_0+a_1σ_1+a_2σ_2)` and gives a degree-two criterion. It does not yield this degree-four counterexample. For `M>1`, the diagonal quartic has a nonreal root pair, so a sufficient criterion requiring a real-rooted diagonal does not apply either.

The inspected [Carptopus note](https://github.com/Carptopus/MathExplore-Notes/blob/6e96176abbbb884906b2235b418d2315908bb5bd/research/lachaume-walsh-convolution/README.md), dated 4 September 2026, addresses Lachaume's Conjectures 4 and 5. It expressly separates them from Conjectures 1 and 3. Searches by the diagonal statement and equivalent fourth-root terminology found no prior same result. A 2019 chapter, *Some New Methods for Generating Convex Functions*, appeared in citation searches, but its complete text was not accessible in this audit. This access limit and the bounded search prevent a claim of first priority.

## Authorship and review

Dev D. Goyal directed the research. The proofs and formalizations were produced with AI systems. See [AUTHORSHIP.md](../../AUTHORSHIP.md). This paper has NOT been peer reviewed. The [verification records](../../verification/README.md) distinguish proof compilation, statement comparison, independent kernel checks, computations, and review.
