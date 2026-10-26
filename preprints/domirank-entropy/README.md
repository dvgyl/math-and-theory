# An entropy increase for a structurally disassortative DomiRank graph

A connected graph with 14 vertices and 32 edges has negative degree-log-degree edge covariance. All DomiRank scores are positive on [251/1000,63/250], inside the stable spectral domain. The entropy increases between the endpoints by more than 1/10000 in natural-logarithm units.

[Paper](paper.pdf) · [LaTeX source](paper.tex) · [Bibliography](references.bib) · [BibTeX citation](citation.bib)

[Formal statement and prior work](../../lean/docs/domirank-entropy.md) · [Independent checks](../../verification/domirank-entropy/README.md) · [Verification record](../../verification/README.md)

This counterexample refutes [Zhang and Zhao, arXiv:2610.00107v4, Conjecture 4.9](https://arxiv.org/html/2610.00107v4). The conjecture asserts that entropy decreases on every interval of positive scores for a structurally disassortative graph. It does not restrict the interval to the first component of the positive-score set. The theorem does not settle that narrower question or assess empirical performance on networks.

The proof uses exact rational score formulas and rational bounds for logarithms. Lean proves the graph properties, the covariance sign, stability and positivity on the whole interval, and the entropy increase. The independent program reconstructs the graph and checks the formulas and bounds. The bounded literature search does not establish first priority.

Compile from this directory with `tectonic paper.tex`.

Dev D. Goyal directed the research. ChatGPT (OpenAI), using the GPT-6 model with Pro reasoning, produced the construction and proof development. Codex audited the sources, adapted the formalization, performed independent computations, and prepared the manuscript. [AUTHORSHIP.md](../../AUTHORSHIP.md) gives the full disclosure. Machine verification and AI review do not constitute independent human expert review. This paper has not been peer reviewed.
