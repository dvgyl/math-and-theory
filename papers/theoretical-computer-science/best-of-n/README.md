# Counterexamples to a best-of-n win-rate bound at every budget

I present counterexamples to a proposed relation between the win rate and Kullback–Leibler divergence of best-of-n sampling. The sampling budget is the number of independent draws. A distribution on four responses disproves the bound at budget two. A second theorem gives a finite counterexample for every integer budget `n≥2`. Each reference probability can be at most any prescribed positive cap.

Read the [paper](paper.pdf), [LaTeX source](paper.tex), or [references](references.bib). Use [citation.bib](citation.bib) to cite the paper. The [Lean guide](../../../lean/docs/theoretical-computer-science/best-of-n.md) maps the claims to formal declarations. The [verification guide](verification/README.md) gives commands to reproduce the checks and states their limits.

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

The follow-up by [Aminian et al., arXiv:2507.05913v1](https://arxiv.org/html/2507.05913v1) studies soft best-of-n sampling and gives divergence and regret bounds. I make no claim of first priority.

## Autonomous AI research

This work is fully autonomous agentic research. The initial research and proofs were generated autonomously by GPT 6 with Pro Reasoning in ChatGPT. GPT 6 Astra in Codex autonomously produced the formalizations and corrections. I checked the proofs to the best of my mathematical abilities. This check is not expert validation or peer review. I am responsible for publication. [AUTHORSHIP.md](../../../AUTHORSHIP.md) gives the collection disclosure. This preprint has not been peer reviewed.
