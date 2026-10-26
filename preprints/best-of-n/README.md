# Counterexamples to a best-of-n win-rate bound at every budget

The paper disproves a proposed relation between the win rate and Kullback–Leibler divergence of best-of-n sampling. A four-response example disproves the bound at budget two. A second theorem gives a finite counterexample at every integer budget `n≥2`, with every reference probability below any prescribed positive cap.

Read the [paper](paper.pdf), [LaTeX source](paper.tex), or [references](references.bib). Use [citation.bib](citation.bib) to cite this paper. The [Lean guide](../../lean/docs/best-of-n.md) maps the claims to formal declarations. The [verification guide](../../verification/best-of-n/README.md) gives reproduction commands and test limits.

## Exact scope

Responses have strictly ordered rewards. Comparisons give one point for a strict win and half a point for equality. If `p` is the reference law and `q` is the selected law, define

- `W = Σ q_i(F_(i−1)+p_i/2)`;
- `D = Σ q_i log(q_i/p_i)`;
- `ell(w) = log(w/(1−w))+1/w−2`.

All logarithms are natural. The finite example uses `p=(2/5,1/5,1/5,1/5)`. It has `q=(4/25,5/25,7/25,9/25)`, `W=163/250`, and `ell(W)−D>1/2445`. The formal proof also establishes an inverse-curve point and proves that it is below the true win rate.

For every `n≥2` and `δ>0`, the construction uses

`a=min(δ,1/(8(n+1)))`, `T=a^n/(48(n+1))`, `m>(1−a)/T`, and `h=(1−a)/m`.

The reference law is `(a,h,…,h)`, with `m` high atoms. The proof establishes positivity, normalization, the atom cap, `1/2≤W<1`, and `D<ell(W)`. It does not determine the sharp replacement curve or an optimal support size.

## Source and prior work

The target is Conjecture 7.2 in [Beirami et al., ICML 2025](https://proceedings.mlr.press/v267/beirami25a.html), also available in [arXiv v3](https://arxiv.org/html/2401.01879v3). Source equation (28) uses the same half-credit convention. Lemma 5.2 gives the cumulative-probability formula used here. The result does not contradict the source's proved upper bounds on divergence and win rate.

The direct follow-up [Aminian et al., arXiv:2507.05913v1](https://arxiv.org/html/2507.05913v1) studies smoothing, divergence, and regret bounds. Its inspected statements do not resolve this conjecture. Searches by the conjecture number, formula, and finite witness found no earlier disproof. This was a bounded search on 26 October 2026. It was not an exhaustive citation-graph review and does not establish first priority.

## Authorship and review

Dev D. Goyal directed the research. The proofs and formalizations were produced with AI systems. See [AUTHORSHIP.md](../../AUTHORSHIP.md) for the full disclosure. This paper has NOT been peer reviewed. Compilation, computational checks, independent AI review, and human expert review are different forms of evidence. See the [verification records](../../verification/README.md) for the checks recorded for this revision.
