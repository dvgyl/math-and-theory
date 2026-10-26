# Counterexamples to a late-iterate ordering conjecture for generalized Hofstadter functions

The paper disproves a comparison conjecture for composition powers of generalized Hofstadter functions. It gives exact finite witnesses and a counterexample for every parameter `k≥4` at iteration index `2k+1`.

Read the [paper](paper.pdf), [LaTeX source](paper.tex), or [references](references.bib). Use [citation.bib](citation.bib) to cite this paper. The [Lean guide](../../lean/docs/hofstadter-iteration.md) gives the theorem map. The [verification guide](../../verification/hofstadter-iteration/README.md) gives reproduction commands and test limits.

## Exact scope

The functions satisfy `F_k(0)=0` and `F_k(n+1)=n+1−F_k^k(n)`. A superscript denotes repeated composition.

The finite witnesses are

- `F_4^9(132)=8>7=F_5^10(132)`;
- `F_4^9(36)=2<3=F_5^10(36)`.

For every `k≥4`, the paper constructs an input `N_k` such that

`F_(k+1)^(2k+2)(N_k) < F_k^(2k+1)(N_k)`.

The mechanism is the exact inverse-orbit gap

`L_(k+1)^(2k+2)(k+3)−L_k^(2k+1)(k+3)=k−3`,

where `L_k(n)=n+F_k^(k−1)(n)`. The infinite family varies `k`. The result does not assert infinitely many violating inputs for each fixed `k` or classify all iteration indices.

## Source and prior work

The target is the conjecture immediately before Lemma 7.6 in [Letouzey, Li, and Steiner, Journal of Integer Sequences 29 (2026), Article 26.3.3](https://cs.uwaterloo.ca/journals/JIS/VOL29/Letouzey/letouzey3.pdf). The [arXiv v2](https://arxiv.org/html/2410.00529v2) gives the same comparison for `j>2k`. This question is separate from the proved order between the base functions.

The full [Letouzey preprint deposited on 26 October 2026](https://inria.hal.science/hal-05839193v1) was retrieved and its relevant statements were checked. Section 7.2 concerns the earlier index `j=k+1`. It does not give the late-iterate disproof stated here. The associated [Rocq source at the inspected commit](https://github.com/letouzey/hofstadter_g/tree/de2bc29a0b3a7dc1f57baf1131353856ee74ddf7) proves known comparisons and witnesses. Its witness in the direction needed here has the restriction `j≤2k`. That restriction does not include `j=2k+1`.

The inverse relations and earlier comparisons are prior work, even where this Lean development proves them again. The claimed contribution is the explicit late-iterate failure and the uniform parameter family. The search found no earlier proof of that family. It was a bounded investigation on 26 October 2026, not a proof of first priority.

## Authorship and review

Dev D. Goyal directed the research. The proofs and formalizations were produced with AI systems. See [AUTHORSHIP.md](../../AUTHORSHIP.md). This paper has NOT been peer reviewed. The [verification records](../../verification/README.md) distinguish proof compilation, statement comparison, independent kernel checks, computations, and review.
