# Math and Theory

I publish fifteen preprints from fully autonomous agentic research in mathematics, theoretical computer science, and mathematical physics. AI agents generated the research, proofs, computations, and manuscripts. I am responsible for publication.

Each paper states its formal verification scope. The thermal proof covers finite spectral statements. It does not formalize the theorem that identifies them with long-time stochastic cumulants. The Gyires preprint proves inequalities for several structured matrix classes and develops related polynomial bounds. Its order-five and order-six results, all-order permutation-polynomial theorem, all-order four-block theorem, and exceptional-vector theorem have Lean proofs. The rank-two theorem also has a Lean proof for orders 2 through 8. Lean formalization of general order-seven circulants and rank-two orders 9 through 15 is incomplete. I do not claim a general solution when a proof covers only a special case.

Start with the [manuscript catalogue](CONTENTS.md) or the [overview](overview.pdf). The [Lean guide](lean/README.md) explains the formal statements. The [verification guide](verification/README.md) gives the commands and recorded results. [AUTHORSHIP.md](AUTHORSHIP.md) identifies the autonomous research process.

## Files and citations

I include the manuscript, source files, and citation metadata for each preprint. The [catalogue](CONTENTS.md) links to each result. I include an explicit publication file list and a SHA-256 integrity record.

## Results

I group related results by subject in the catalogue. The mathematics papers concern matrix inequalities, concavity, and integer sequences. The theoretical computer science papers concern sampling and Boolean decision trees. The mathematical physics papers cover a thermal spectral counterexample, universal entanglement embezzlement, and the four-qubit Higuchi–Sudbery entropy bound.

### Mathematical physics

| Result family | Established result |
|---|---|
| [A sum-of-squares proof of the four-qubit Higuchi–Sudbery entropy bound](verification/additional-proofs/higuchi-sudbery/manuscript.pdf) | The average von Neumann entropy of the three two-qubit marginals of a pure four-qubit state is at most log(2) + log(3)/2. The Higuchi–Sudbery state attains this bound. |
| [Universal entanglement embezzlement with inverse-quadratic logarithmic infidelity](verification/additional-proofs/universal-embezzlement/manuscript.pdf) | A target-independent catalyst with local dimension 2^(4L) gives root infidelity at most 125m/L² for every Schmidt probability vector on m entries. |
| [Thermal current kurtosis](verification/additional-proofs/thermal-kurtosis-counterexample/report.pdf) | A three-state, two-temperature model has a negative fourth-to-second spectral heat-cumulant ratio. The long-time stochastic identification is outside the formal proof. |

### Theoretical computer science

| Result family | Established result |
|---|---|
| [Decision-tree covariance](verification/additional-proofs/readk-covariance/docs/manuscript.pdf) | A sharp logarithmic influence bound and two counterexamples to the proposed logarithmic variance bound. No Fourier-entropy theorem is formalized. |
| [Best-of-n sampling](preprints/best-of-n/README.md) | The proposed bound fails at every budget at least two, with arbitrarily small atom caps. |

### Mathematics: extremal bounds and combinatorics

| Result family | Established result |
|---|---|
| [The sharp level-one Fourier weight at density one eighth](verification/additional-proofs/sharp-eighth/manuscript.pdf) | For every Boolean indicator of mean 1/8 on a finite uniform cube, the level-one Fourier weight is at most 3/64. A codimension-three subcube attains the bound in every dimension at least three. |
| [A quartic entropy deficit for random rankings](verification/additional-proofs/quartic-rankings/manuscript.pdf) | A distribution on rankings of n labels has entropy at most (1 − ε⁴/144) log(n!) if every pairwise comparison has probability at distance at least ε > 0 from 1/2. |
| [The exact asymmetric Merino–Welsh region for finite matroids](verification/additional-proofs/asymmetric-tutte/manuscript.pdf) | The theorem characterizes all nonnegative pairs (x,y) for which T_M(x,0) T_M(0,y) ≥ T_M(1,1)² holds for every finite matroid without loops or coloops. |
| [Ultra-log-concavity of domination sequences of powers of paths and cycles](verification/additional-proofs/galvin-zhang/manuscript.pdf) | The domination counts of every natural power of a path or cycle form an ultra-log-concave sequence. The proof includes all natural graph orders and powers, the binomial normalization, and the boundary graph cases. |

### Mathematics: matrix inequalities and concavity

| Result family | Established result |
|---|---|
| [Gyires](preprints/gyires-circulant-five/README.md) | Circulants of orders five through seven, all-order structured matrix results, rank two through order fifteen, and supporting polynomial results. Order-five, order-six, permutation-polynomial, four-block, and exceptional-vector claims have Lean proofs. Rank-two orders 2–8 have Lean proofs. General order-seven circulants and rank-two orders 9–15 remain incomplete in Lean. |
| [q-permanent](preprints/q-permanent/README.md) | Counterexamples at every real parameter greater than one. |
| [Diagonal concavity](preprints/diagonal-concavity/README.md) | A counterexample and complete classification of a positive one-parameter family. |

### Mathematics: graph entropy and integer sequences

| Result family | Established result |
|---|---|
| [DomiRank entropy](preprints/domirank-entropy/README.md) | A 14-vertex counterexample with positive scores on the whole comparison interval. |
| [Alternating Motzkin sums](preprints/alternating-motzkin/README.md) | Strict root log-concavity with the optimal tail start. |
| [Hofstadter iteration](preprints/hofstadter-iteration/README.md) | Late-iterate ordering fails for every parameter at least four. |

## The Gyires preprint

The [Gyires preprint](preprints/gyires-circulant-five/paper.pdf) proves the order-five circulant inequality and extends the analysis to other structured matrix classes. It includes circulants of orders six and seven, all-order permutation polynomials, all-order four-block matrices, one exceptional column or row, and rank-two matrices through order fifteen. It also proves structural, scalar, deletion, balancing, local polynomial, and counting results. Exact counterexamples identify the limits of proposed extensions. The [complete supporting record](research-notes/gyires-complete-support/README.md) gives the source map, certificate files, and reproduction commands. The all-order four-block and exceptional-vector theorems have complete Lean proofs. The general order-six and all-order permutation-polynomial theorems have separate Lean source packages. The rank-two theorem has a complete Lean proof for orders 2 through 8. The general order-seven circulant theorem and rank-two orders 9 through 15 remain incomplete in Lean. The manuscript does not establish the unrestricted conjecture.

The Gyires [order-six package](verification/gyires-circulant-six/README.md) and [permutation-polynomial package](verification/gyires-permutation-polynomial/README.md) contain the additional formal proofs. Each package has its own pinned build and theorem map. The [rank-two package](verification/gyires-rank-two/README.md) proves the actual matrix theorem in orders 2 through 8.

## Unfinished formal proofs

[UNFINISHED.md](UNFINISHED.md) lists the remaining verification gaps. The Gyires general order-seven circulant and rank-two orders 9–15 Lean proofs remain unfinished.

## Verification

The shared formal library covers seven families and 29 selected Comparator statements. It uses Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. The proof audit permits only `propext`, `Classical.choice`, and `Quot.sound`. Separate Challenge and Solution modules make each submitted statement auditable. The Challenge proof holes are specifications. They are excluded from the proved library and its axiom audit.

The [decision-tree package](verification/additional-proofs/readk-covariance/README.md) and [thermal package](verification/additional-proofs/thermal-kurtosis-counterexample/README.md) use separate Lean 4.19.0 environments with Mathlib revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`. They are not part of the shared Comparator selection. The decision-tree package has its own 29 axiom reports; this is a separate count.

The [verification guide](verification/README.md) gives commands for compilation, statement comparison, proof checking, and exact computation. A successful computation over finitely many inputs does not prove a universal theorem.

The automatic workflow checks source integrity and all fifteen manuscripts on pushes and pull requests. It has separate Lean jobs for the shared library and all eight standalone study packages. The large separate Gyires packages have automatic source checks and a manual full-build workflow. The full Palomar mechanical preflight remains available by manual dispatch.

## Authorship and use

I describe the fully autonomous agentic research process in [AUTHORSHIP.md](AUTHORSHIP.md). These preprints have not been peer reviewed.

Cite an individual paper with its `citation.bib` file, or `CITATION.bib` for a standalone package. For the repository, use [CITATION.cff](CITATION.cff) or [CITATION.bib](CITATION.bib). The catalogue links each manuscript to its source, citation metadata, and verification instructions. The root [Apache-2.0 license](LICENSE) applies except where [NOTICE](NOTICE) identifies third-party material.

For a later result family, follow [the contribution procedure](lean/docs/adding-a-family.md). Each addition must satisfy the same mathematical, source-fidelity, prior-work, formalization, and reproducibility requirements.

## Research process and review

The initial research and proofs were generated autonomously by GPT 6 with Pro Reasoning in ChatGPT. GPT 6 Astra in Codex autonomously produced the formalizations and corrections. I checked the proofs to the best of my mathematical abilities. This check is not expert validation or peer review. I am responsible for publication.
