# Math and Theory

Seven preprints by Dev D. Goyal present results in mathematics and theoretical computer science.

This collection contains seven preprints. Six have complete Lean proofs of their principal claims. The Gyires preprint proves inequalities for several structured matrix classes and develops related polynomial bounds. Its principal order-five claims, the all-order four-block theorem, and the exceptional-vector theorem have Lean proofs. Lean formalization of the other principal Gyires results is incomplete. The collection does not claim a general solution when a proof covers only a special case.

Start with the [manuscript catalogue](CONTENTS.md) or the [overview](overview.pdf). The [Lean guide](lean/README.md) explains the formal statements. The [verification guide](verification/README.md) gives the commands and recorded results. [AUTHORSHIP.md](AUTHORSHIP.md) identifies the human and AI contributions.

## Zenodo preprints

Five preprints are available on Zenodo. Each record contains a manuscript PDF and its archival package. The links below identify version 1.0.0, published on 26 October 2026.

| Preprint | Zenodo record | DOI |
|---|---|---|
| [q-permanent](preprints/q-permanent/README.md) | [Record](https://zenodo.org/records/23679243) | [10.5281/zenodo.23679243](https://doi.org/10.5281/zenodo.23679243) |
| [Gyires](preprints/gyires-circulant-five/README.md) | [Record](https://zenodo.org/records/23679286) | [10.5281/zenodo.23679286](https://doi.org/10.5281/zenodo.23679286) |
| [Diagonal concavity](preprints/diagonal-concavity/README.md) | [Record](https://zenodo.org/records/23679302) | [10.5281/zenodo.23679302](https://doi.org/10.5281/zenodo.23679302) |
| [Hofstadter iteration](preprints/hofstadter-iteration/README.md) | [Record](https://zenodo.org/records/23679312) | [10.5281/zenodo.23679312](https://doi.org/10.5281/zenodo.23679312) |
| [Best-of-n](preprints/best-of-n/README.md) | [Record](https://zenodo.org/records/23679329) | [10.5281/zenodo.23679329](https://doi.org/10.5281/zenodo.23679329) |

Each revised archival package contains an explicit publication file list and a SHA-256 integrity record. Use each paper's `citation.bib` file to cite its published version.

## Results

The catalogue groups related results by subject. The mathematics papers concern matrix inequalities, concavity, and integer sequences. The theoretical computer science paper concerns a sampling-policy inequality.

| Result family | Established result |
|---|---|
| [q-permanent](preprints/q-permanent/README.md) | Counterexamples at every real parameter greater than one. |
| [Gyires](preprints/gyires-circulant-five/README.md) | Circulants of orders five through seven, all-order structured matrix results, rank two through order fifteen, and supporting polynomial results. Order-five, four-block, and exceptional-vector claims have Lean proofs. The other principal Gyires results remain incomplete in Lean. |
| [DomiRank entropy](preprints/domirank-entropy/README.md) | A 14-vertex counterexample with positive scores on the whole comparison interval. |
| [Diagonal concavity](preprints/diagonal-concavity/README.md) | A counterexample and complete classification of a positive one-parameter family. |
| [Alternating Motzkin sums](preprints/alternating-motzkin/README.md) | Strict root log-concavity with the optimal tail start. |
| [Hofstadter iteration](preprints/hofstadter-iteration/README.md) | Late-iterate ordering fails for every parameter at least four. |
| [Best-of-n sampling](preprints/best-of-n/README.md) | The proposed bound fails at every budget at least two, with arbitrarily small atom caps. |

## The Gyires preprint

The [Gyires preprint](preprints/gyires-circulant-five/paper.pdf) proves the order-five circulant inequality and extends the analysis to other structured matrix classes. It includes circulants of orders six and seven, all-order permutation polynomials, all-order four-block matrices, one exceptional column or row, and rank-two matrices through order fifteen. It also proves structural, scalar, deletion, balancing, local polynomial, and counting results. Exact counterexamples identify the limits of proposed extensions. The [complete supporting record](research-notes/gyires-complete-support/README.md) gives the source map, certificate files, and reproduction commands. The all-order four-block and exceptional-vector theorems have complete Lean proofs. The principal higher-order circulant, permutation-polynomial, and finite rank-two theorems remain incomplete in Lean. The manuscript does not establish the unrestricted conjecture.

## Verification

The formal library uses Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. The proof audit permits only `propext`, `Classical.choice`, and `Quot.sound`. Separate Challenge and Solution modules make each submitted statement auditable. The Challenge proof holes are specifications. They are excluded from the proved library and its axiom audit.

The [verification guide](verification/README.md) gives commands for compilation, statement comparison, proof checking, and exact computation. A successful computation over finitely many inputs does not prove a universal theorem.

The automatic workflow checks source integrity, manuscript builds, and Lean proofs on pushes and pull requests. The full Palomar mechanical preflight remains available by manual dispatch.

## Authorship and use

The [authorship disclosure](AUTHORSHIP.md) states the use of AI assistance. These preprints have not been peer reviewed.

Cite an individual paper with its `citation.bib` file. Each paper directory contains its source, bibliography, PDF, and links to its formal proof. The root [Apache-2.0 license](LICENSE) applies except where [NOTICE](NOTICE) identifies third-party material.

For a later result family, follow [the contribution procedure](lean/docs/adding-a-family.md). Each addition must satisfy the same mathematical, source-fidelity, prior-work, formalization, and reproducibility requirements.
