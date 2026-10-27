# Real positive-definite counterexamples to extended q-permanent monotonicity

[Zenodo record](https://zenodo.org/records/23679243) · [DOI: 10.5281/zenodo.23679243](https://doi.org/10.5281/zenodo.23679243) · Version 1.0.0. Published 26 October 2026.

For every real parameter `q>1`, there is a real symmetric positive-definite matrix whose q-permanent has a negative derivative at `q`. The dimension can depend on `q`. An explicit matrix of order five gives a decrease from `q=14` to `q=15`.

Read the [paper](paper.pdf), [LaTeX source](paper.tex), or [bibliography](references.bib). Use the [BibTeX citation](citation.bib) to cite the paper. The [formal guide](../../lean/docs/q-permanent.md) maps the results to Lean declarations and describes prior work. The [independent checks](../../verification/q-permanent/README.md) and [verification record](../../verification/README.md) give commands and recorded results.

## Scope

The q-permanent weights each permutation product by `q` raised to its inversion count in the fixed coordinate order. All matrices in the main theorems are real, symmetric, and positive definite.

The construction also gives correlation matrices with no zero entries and examples with integer entries. These are separate conclusions. The theorem does not assert that a correlation matrix can also have integer entries. The real-symmetric monotonicity question on `[−1,1]` remains outside the result.

The results refute da Fonseca's 2010 Conjecture 1 and its [2018 restatement as Conjecture 2](https://arxiv.org/abs/1804.02231). No claim of first priority is made.

## AI assistance

Dev D. Goyal directed the research and is responsible for publication. ChatGPT (OpenAI), using GPT-6 with Pro reasoning, generated the mathematical arguments and Lean formalizations. Codex assisted with formalization, computations, and editing. [AUTHORSHIP.md](../../AUTHORSHIP.md) gives the collection disclosure. This preprint has not been peer reviewed.

## Build

Run `tectonic paper.tex` from this directory.
