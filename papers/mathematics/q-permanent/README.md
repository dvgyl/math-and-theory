# Real positive-definite counterexamples to extended q-permanent monotonicity

For every real parameter `q>1`, I present a real symmetric positive-definite matrix whose q-permanent has a negative derivative at `q`. The dimension can depend on `q`. An explicit matrix of order five gives a decrease from `q=14` to `q=15`.

Read the [paper](paper.pdf), [LaTeX source](paper.tex), or [bibliography](references.bib). Use the [BibTeX citation](citation.bib) to cite the paper. The [formal guide](../../../lean/docs/mathematics/q-permanent.md) maps the results to Lean declarations and describes prior work. The [independent checks](verification/README.md) and [verification record](../../../verification/README.md) give commands and recorded results.

## Scope

The q-permanent weights each permutation product by `q` raised to its inversion count in the fixed coordinate order. All matrices in the main theorems are real, symmetric, and positive definite.

The construction also gives correlation matrices with no zero entries and examples with integer entries. These are separate conclusions. The theorem does not assert that a correlation matrix can also have integer entries. The real-symmetric monotonicity question on `[−1,1]` remains outside the result.

The results refute da Fonseca's 2010 Conjecture 1 and its [2018 restatement as Conjecture 2](https://arxiv.org/abs/1804.02231). I make no claim of first priority.

## Autonomous AI research

This work is fully autonomous agentic research. The initial research and proofs were generated autonomously by GPT 6 with Pro Reasoning in ChatGPT. GPT 6 Astra in Codex autonomously produced the formalizations and corrections. I checked the proofs to the best of my mathematical abilities. This check is not expert validation or peer review. I am responsible for publication. [AUTHORSHIP.md](../../../AUTHORSHIP.md) gives the collection disclosure. This preprint has not been peer reviewed.

## Build

Run `latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex` from this directory.
