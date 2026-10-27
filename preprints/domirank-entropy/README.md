# An entropy increase for a structurally disassortative DomiRank graph

I present a connected graph with 14 vertices and 32 edges that has negative degree-log-degree edge covariance. All DomiRank scores are positive on [251/1000,63/250], inside the stable spectral domain. The entropy increases between the endpoints by more than 1/10000 in natural-logarithm units.

[Paper](paper.pdf) · [LaTeX source](paper.tex) · [Bibliography](references.bib) · [BibTeX citation](citation.bib)

[Formal statement and prior work](../../lean/docs/domirank-entropy.md) · [Independent checks](../../verification/domirank-entropy/README.md) · [Verification record](../../verification/README.md)

This counterexample refutes [Zhang and Zhao, arXiv:2610.00107v4, Conjecture 4.9](https://arxiv.org/html/2610.00107v4). The conjecture asserts that entropy decreases on every interval of positive scores for a structurally disassortative graph. It does not restrict the interval to the first component of the positive-score set. The theorem does not settle that narrower question or assess empirical performance on networks.

The proof uses exact rational score formulas and rational bounds for logarithms. Lean proves the graph properties, the covariance sign, stability and positivity on the whole interval, and the entropy increase. The independent program reconstructs the graph and checks the formulas and bounds. I make no claim of first priority.

Compile from this directory with `tectonic paper.tex`.

This work is fully autonomous agentic research. The initial research and proofs were generated autonomously by GPT 6 with Pro Reasoning in ChatGPT. GPT 6 Astra in Codex autonomously produced the formalizations and corrections. I checked the proofs to the best of my mathematical abilities. This check is not expert validation or peer review. I am responsible for publication. [AUTHORSHIP.md](../../AUTHORSHIP.md) gives the collection disclosure. This preprint has not been peer reviewed.
