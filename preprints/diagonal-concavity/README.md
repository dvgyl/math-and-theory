# Diagonal concavity does not imply concavity for sums of elementary symmetric polynomials

[Zenodo record](https://zenodo.org/records/23679302) · [DOI: 10.5281/zenodo.23679302](https://doi.org/10.5281/zenodo.23679302) · Version 1.0.0. Published 26 October 2026.

The paper disproves Lachaume's Conjecture 1. It classifies concavity for a family in four variables. Concavity on the positive diagonal holds for more parameter values than concavity on the whole positive orthant. The positive orthant is the set of vectors with all coordinates positive. Its positive diagonal consists of vectors whose coordinates are equal.

Read the [paper](paper.pdf), [LaTeX source](paper.tex), or [references](references.bib). Use [citation.bib](citation.bib) to cite the paper. The [Lean guide](../../lean/docs/diagonal-concavity.md) maps the results to formal declarations. The [verification guide](../../verification/diagonal-concavity/README.md) gives commands to reproduce the checks and states their limits.

## Scope

Let `σ_j` be the unnormalized elementary symmetric polynomial of degree `j` in four variables. It sums the products over all subsets of `j` distinct coordinates, with `σ_0=1`. For `M>0`, set

`f_M = 1 + Mσ_1 + σ_2 + Mσ_3 + σ_4`.

The theorem concerns the real fourth root of `f_M`:

- It is concave on the positive diagonal exactly when `M≥1`.
- It is concave on the whole positive orthant exactly when `M=1`.

Thus every `M>1` gives a counterexample to the proposed diagonal criterion. At `M=2`, a separate rational certificate gives a strict violation of the concavity inequality at a midpoint. The result does not classify arbitrary coefficient vectors or other dimensions.

## Source and prior work

[Lachaume's Conjecture 1](https://arxiv.org/html/1712.10327v1) concerns nonnegative coefficients, the positive orthant, and concavity after the `1/p` power. Here `n=p=4`, and every coefficient is positive. The formal definitions use the same convention for elementary symmetric polynomials.

The paper gives the degree-four counterexample and its full one-parameter classification. The case `M=1` uses the known concavity of the geometric mean. Lachaume's Theorem 3.3 treats `sqrt(a_0+a_1σ_1+a_2σ_2)` and gives a degree-two criterion. It does not give this degree-four counterexample. For `M>1`, the diagonal quartic has a nonreal root pair. The separate sufficient criterion that requires a real-rooted diagonal therefore does not apply.

The [Carptopus note](https://github.com/Carptopus/MathExplore-Notes/blob/6e96176abbbb884906b2235b418d2315908bb5bd/research/lachaume-walsh-convolution/README.md), dated 4 September 2026, addresses Lachaume's Conjectures 4 and 5. It makes no claim for Conjectures 1 and 3. No claim of first priority is made here.

## AI assistance

Dev D. Goyal directed the research and is responsible for publication. ChatGPT (OpenAI), using GPT-6 with Pro reasoning, generated the mathematical arguments and Lean formalizations. Codex assisted with formalization, computations, and editing. [AUTHORSHIP.md](../../AUTHORSHIP.md) gives the collection disclosure. This preprint has not been peer reviewed.