# Counterexamples to a late-iterate ordering conjecture for generalized Hofstadter functions

[Zenodo record](https://zenodo.org/records/23679312) · [DOI: 10.5281/zenodo.23679312](https://doi.org/10.5281/zenodo.23679312) · Version 1.0.0. Published 26 October 2026.

This paper disproves a conjectured order between iterates of generalized Hofstadter functions. It gives exact finite witnesses and a counterexample for every parameter `k≥4` at iteration index `2k+1`.

Read the [paper](paper.pdf), [LaTeX source](paper.tex), or [references](references.bib). Use [citation.bib](citation.bib) to cite this paper. The [Lean guide](../../lean/docs/hofstadter-iteration.md) gives the theorem map. The [verification guide](../../verification/hofstadter-iteration/README.md) gives reproduction commands and test limits.

## Result

The functions satisfy `F_k(0)=0` and `F_k(n+1)=n+1−F_k^k(n)`. A superscript denotes repeated composition.

The finite witnesses are

- `F_4^9(132)=8>7=F_5^10(132)`;
- `F_4^9(36)=2<3=F_5^10(36)`.

For every `k≥4`, the paper constructs an input `N_k` such that

`F_(k+1)^(2k+2)(N_k) < F_k^(2k+1)(N_k)`.

The proof uses the exact difference between inverse iterates

`L_(k+1)^(2k+2)(k+3)−L_k^(2k+1)(k+3)=k−3`,

where `L_k(n)=n+F_k^(k−1)(n)`. The family gives one input for each parameter `k`. It does not assert infinitely many violating inputs for each fixed `k` or classify all iteration indices.

## Source and prior work

The conjecture appears immediately before Lemma 7.6 in [Letouzey, Li, and Steiner, Journal of Integer Sequences 29 (2026), Article 26.3.3](https://cs.uwaterloo.ca/journals/JIS/VOL29/Letouzey/letouzey3.pdf). [ArXiv version 2](https://arxiv.org/html/2410.00529v2) gives the same comparison for `j>2k`. The conjecture concerns more iterations than the proved order between the base functions.

[Letouzey's preprint of 26 October 2026](https://inria.hal.science/hal-05839193v1), Section 7.2, concerns the earlier index `j=k+1`. The associated [Rocq source](https://github.com/letouzey/hofstadter_g/tree/de2bc29a0b3a7dc1f57baf1131353856ee74ddf7) proves known comparisons and gives witnesses. Its witness in the direction needed here has the restriction `j≤2k`. That restriction excludes the index `j=2k+1` in the present theorem.

The inverse relations and earlier comparisons are due to this prior work. The Lean formalization proves the inverse relations again from the recurrence. The contribution is the explicit late-iterate failure and the family for every `k≥4`. The bounded search of 26 October 2026 found no earlier proof of that family. It does not establish first priority.

## Authorship and AI use

Dev D. Goyal directed the research. AI systems produced the proofs and formalizations under his direction. [AUTHORSHIP.md](../../AUTHORSHIP.md) gives the full disclosure. The [verification records](../../verification/README.md) give the scope of proof compilation, statement comparison, independent kernel checks, computations, and AI review. These checks do not constitute independent human expert review. This paper has not been peer reviewed.
