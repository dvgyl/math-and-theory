# Counterexamples to a best-of-n win-rate bound at every budget

The paper disproves a proposed relation between the win rate and Kullback–Leibler divergence of best-of-n sampling. The sampling budget is the number of independent draws. A distribution on four responses disproves the bound at budget two. A second theorem gives a finite counterexample for every integer budget `n≥2`. Each reference probability can be at most any prescribed positive cap.

Read the [paper](paper.pdf), [LaTeX source](paper.tex), or [references](references.bib). Use [citation.bib](citation.bib) to cite the paper. The [Lean guide](../../lean/docs/best-of-n.md) maps the claims to formal declarations. The [verification guide](../../verification/best-of-n/README.md) gives commands to reproduce the checks and states their limits.

## Scope

Responses have strictly ordered rewards. A comparison with an independent reference draw gives one point for a strict win and half a point for equality. Let `p` be the reference distribution and `q` the selected distribution. Let `F_(i−1)` be the reference probability of responses with lower reward than response `i`. Define

- `W = Σ q_i(F_(i−1)+p_i/2)`;
- `D = Σ q_i log(q_i/p_i)`;
- `ell(w) = log(w/(1−w))+1/w−2`.

All logarithms are natural. The finite example uses `p=(2/5,1/5,1/5,1/5)`. It has `q=(4/25,5/25,7/25,9/25)`, `W=163/250`, and `ell(W)−D>1/2445`. The formal proof also proves that the inverse-curve value exists and is less than the win rate.

For every `n≥2` and `δ>0`, the construction uses

`a=min(δ,1/(8(n+1)))`, `T=a^n/(48(n+1))`, `m>(1−a)/T`, and `h=(1−a)/m`.

The reference distribution is `(a,h,…,h)`. It has one response of probability `a` and `m` responses of probability `h` with higher rewards. The proof establishes positivity, normalization, the probability cap, `1/2≤W<1`, and `D<ell(W)`. It does not determine the sharp replacement curve or an optimal support size.

## Source and prior work

The result refutes Conjecture 7.2 in [Beirami et al., ICML 2025](https://proceedings.mlr.press/v267/beirami25a.html), also available in [arXiv v3](https://arxiv.org/html/2401.01879v3). Equation (28) uses the same half-credit convention. Lemma 5.2 gives the cumulative-probability formula used here. The source's proved upper bounds on divergence and win rate remain valid.

The follow-up by [Aminian et al., arXiv:2507.05913v1](https://arxiv.org/html/2507.05913v1) studies smoothing, divergence, and regret bounds. Its inspected statements do not resolve this conjecture. Searches on 26 October 2026 used the conjecture number, formula, and finite counterexample. No earlier disproof was found. The search did not cover the full citation graph and does not establish priority.

## Authorship and review

Dev D. Goyal directed the research. ChatGPT (OpenAI), using the GPT-6 model with Pro reasoning, generated the proof and Lean formalization. Further mathematical checks and editing used AI assistance. See [AUTHORSHIP.md](../../AUTHORSHIP.md) for the full disclosure. Machine verification and AI review do not constitute independent human expert peer review. This paper has not been peer reviewed. The [verification records](../../verification/README.md) describe the checks for this version.
