# Manuscript catalogue

The catalogue contains fifteen result families and fifteen manuscripts. Seven families use the shared Lean 4.35.0 library. Its 29 selected Comparator declarations include equality, positivity, sharpness, and generalization statements. The decision-tree and thermal packages use separate Lean 4.19.0 environments. Supporting lemmas are not separate research contributions.

Each paper states its formal verification scope. The thermal formalization covers finite spectral statements, with no formal stochastic long-time identification theorem. The Gyires preprint has complete Lean proofs for its principal order-five and order-six claims, its all-order permutation-polynomial and four-block theorems, and its exceptional-vector theorem. The rank-two result has a complete Lean proof for orders 2 through 6. The principal order-seven result and rank-two orders 7 through 15 remain incomplete in Lean. The verification record gives the checks actually completed. The papers have not been peer reviewed. The prior-work assessment is bounded and makes no first-priority claim.

## Mathematics

### Matrix theory

#### Real positive-definite counterexamples to extended q-permanent monotonicity

**Family:** `q-permanent`. **Result:** Counterexample and all-parameter extension.

**Abstract.** For every real parameter q>1, a real symmetric positive-definite matrix has a negative q-permanent derivative at q. An explicit matrix of order five decreases from q=14 to q=15. Correlation matrices with no zero entries and integer-entry examples are also obtained. The dimension can depend on q. The real-symmetric question on [−1,1] remains outside the result.

**Original problem.** [Da Fonseca, 2010, Conjecture 1; 2018, Conjecture 2.](https://arxiv.org/abs/1804.02231)

[Paper PDF](preprints/q-permanent/paper.pdf) · [LaTeX](preprints/q-permanent/paper.tex) · [Bibliography](preprints/q-permanent/references.bib) · [Citation](preprints/q-permanent/citation.bib) · [Formal statement and prior work](lean/docs/q-permanent.md) · [Reproduction](verification/q-permanent/README.md)

#### Gyires's permanent inequality for structured matrices

**Family:** `gyires-circulant-five`. **Result:** Structured matrix inequalities and related polynomial bounds. The principal order-five and order-six claims, the all-order permutation-polynomial and four-block theorems, the exceptional-vector theorem, and rank-two orders 2–6 have Lean proofs.

**Abstract.** The preprint proves Gyires's permanent inequality for several structured matrix classes. These include nonnegative circulants of orders five through seven, all-order permutation polynomials A=aI+bQ+cQ², and all-order four-block doubly stochastic matrices. Here Q is any permutation matrix and a,b,c are nonnegative. The four-block result permits unequal block sizes and zero entries. Further results cover one exceptional column or row and every rank-at-most-two doubly stochastic matrix through order fifteen. The supporting sections prove structural, scalar, deletion, balancing, local polynomial, and counting results. Exact counterexamples identify the limits of auxiliary assertions. The principal order-five claims include equality and a sharp sorted-gap bound with coefficient 484. The principal order-five and order-six claims, the all-order permutation-polynomial and four-block theorems, and the exceptional-vector theorem have complete Lean proofs. The rank-two result has a complete Lean proof for orders 2 through 6. The principal order-seven result and rank-two orders 7 through 15 remain incomplete in Lean. The unrestricted conjecture remains outside these results.

**Original problem.** [Gyires, 1978; Cheon and Wanless, 2005, Conjecture 20. Earlier formalization at the pinned Gyires repository.](https://github.com/dvgyl/gyires-circulant-5/tree/72cf49a51be42cf15592f91d991f0b0c76f58448)

[Paper PDF](preprints/gyires-circulant-five/paper.pdf) · [LaTeX](preprints/gyires-circulant-five/paper.tex) · [Bibliography](preprints/gyires-circulant-five/references.bib) · [Citation](preprints/gyires-circulant-five/citation.bib) · [Formal statement and prior work](lean/docs/gyires-circulant-five.md) · [Reproduction](verification/gyires-circulant-five/README.md)

#### Supporting records for the all-order Gyires arguments

The preprint includes both all-order arguments. This [supporting record](research-notes/gyires-extensions/README.md) gives their proofs, programs, and outputs. The four-block theorem has a complete Lean proof. The permutation-polynomial theorem has a complete Lean proof in the separate `verification/gyires-permutation-polynomial` package. No novelty or independent human expert review is claimed.

- [Permutation-polynomial claim](research-notes/gyires-extensions/permutation-polynomial.md). For every dimension, A=aI+bQ+cQ² with Q a permutation matrix and a,b,c nonnegative satisfies the stronger Gram-permanent bound. The argument combines exact polynomial certificates with an analytic tail.
- [Four-block claim](research-notes/gyires-extensions/four-block.md). At most two row types and two column types suffice for three permanent contraction bounds and a strict Gyires margin away from the uniform matrix. Unequal block sizes and zero block entries are included.

[Certificate reproduction](research-notes/gyires-extensions/verification.md) · [Source hashes](research-notes/gyires-extensions/provenance.json)

### Graph theory and matrix analysis

#### An entropy increase for a structurally disassortative DomiRank graph

**Family:** `domirank-entropy`. **Result:** Counterexample to an interval monotonicity conjecture.

**Abstract.** A connected graph with 14 vertices and 32 edges has negative degree–log-degree edge covariance. All resolvent scores are positive on [251/1000,63/250] inside the stable domain. Its entropy nevertheless increases by more than 1/10000 in natural-logarithm units. This refutes the source’s assertion for every positive-score interval.

**Original problem.** [Zhang and Zhao, arXiv:2610.00107v4, Conjecture 4.9.](https://arxiv.org/html/2610.00107v4)

[Paper PDF](preprints/domirank-entropy/paper.pdf) · [LaTeX](preprints/domirank-entropy/paper.tex) · [Bibliography](preprints/domirank-entropy/references.bib) · [Citation](preprints/domirank-entropy/citation.bib) · [Formal statement and prior work](lean/docs/domirank-entropy.md) · [Reproduction](verification/domirank-entropy/README.md)

### Inequalities and real analysis

#### Diagonal concavity does not imply concavity for sums of elementary symmetric polynomials

**Family:** `diagonal-concavity`. **Result:** Counterexample and complete parameter classification.

**Abstract.** For positive M, let f=1+Mσ₁+σ₂+Mσ₃+σ₄ in four variables. Its fourth root is concave on the positive diagonal exactly when M≥1. It is concave on the full positive orthant exactly when M=1. Every M>1 therefore disproves Lachaume’s diagonal criterion with strictly positive coefficients.

**Original problem.** [Lachaume, arXiv:1712.10327v1, Conjecture 1.](https://arxiv.org/abs/1712.10327v1)

[Paper PDF](preprints/diagonal-concavity/paper.pdf) · [LaTeX](preprints/diagonal-concavity/paper.tex) · [Bibliography](preprints/diagonal-concavity/references.bib) · [Citation](preprints/diagonal-concavity/citation.bib) · [Formal statement and prior work](lean/docs/diagonal-concavity.md) · [Reproduction](verification/diagonal-concavity/README.md)

### Integer sequences and combinatorics

#### Sharp root log-concavity of alternating Motzkin sums

**Family:** `alternating-motzkin`. **Result:** Conjecture resolution with an optimal threshold.

**Abstract.** Let Tₙ be the alternating sum of Motzkin numbers through index n. The sequence Tₙ^(1/n) is strictly log-concave on its tail starting at five. The inequality reverses at center five, so no earlier tail is log-concave. This strengthens Zhao’s proposed tail starting at nine. The source recurrence and finite sum are linked in Lean.

**Original problem.** [Zhao, INTEGERS 26 (2026), A55, Conjecture 1; OEIS A187306.](https://math.colgate.edu/~integers/aa55/aa55.pdf)

[Paper PDF](preprints/alternating-motzkin/paper.pdf) · [LaTeX](preprints/alternating-motzkin/paper.tex) · [Bibliography](preprints/alternating-motzkin/references.bib) · [Citation](preprints/alternating-motzkin/citation.bib) · [Formal statement and prior work](lean/docs/alternating-motzkin.md) · [Reproduction](verification/alternating-motzkin/README.md)

#### Counterexamples to a late-iterate ordering conjecture for generalized Hofstadter functions

**Family:** `hofstadter-iteration`. **Result:** Counterexamples for every parameter k≥4.

**Abstract.** For every k≥4, some input n satisfies Fₖ^(2k+1)(n)>Fₖ₊₁^(2k+2)(n). The proof constructs inverse iterates whose exact gap is k−3. The finite witness F₄⁹(132)=8>7=F₅¹⁰(132) gives the first instance. The result concerns infinitely many parameters, not infinitely many violating inputs for each fixed parameter.

**Original problem.** [Letouzey, Li, and Steiner, Journal of Integer Sequences 29 (2026), 26.3.3, conjecture before Lemma 7.6.](https://cs.uwaterloo.ca/journals/JIS/VOL29/Letouzey/letouzey3.pdf)

[Paper PDF](preprints/hofstadter-iteration/paper.pdf) · [LaTeX](preprints/hofstadter-iteration/paper.tex) · [Bibliography](preprints/hofstadter-iteration/references.bib) · [Citation](preprints/hofstadter-iteration/citation.bib) · [Formal statement and prior work](lean/docs/hofstadter-iteration.md) · [Reproduction](verification/hofstadter-iteration/README.md)

## Theoretical computer science

### Sampling algorithms and information theory

#### Counterexamples to a best-of-n win-rate bound at every budget

**Family:** `best-of-n`. **Result:** Disproof for every budget n≥2 and every positive atom cap.

**Abstract.** For every n≥2 and δ>0, there is a finite positive reference distribution whose largest atom is at most δ and whose best-of-n policy violates the proposed divergence–win-rate curve. A four-response best-of-two example gives exact probabilities and a strict logarithmic certificate. The proof uses finite interval bounds and gives a quantitative positive gap. It does not determine the sharp replacement curve.

**Original problem.** [Beirami et al., ICML 2025, Conjecture 7.2 and equation (28).](https://proceedings.mlr.press/v267/beirami25a.html)

[Paper PDF](preprints/best-of-n/paper.pdf) · [LaTeX](preprints/best-of-n/paper.tex) · [Bibliography](preprints/best-of-n/references.bib) · [Citation](preprints/best-of-n/citation.bib) · [Formal statement and prior work](lean/docs/best-of-n.md) · [Reproduction](verification/best-of-n/README.md)

### Boolean decision trees

#### Logarithmic influence bounds and variance counterexamples for Boolean decision-tree covariance

**Family:** `readk-covariance`. **Result:** A sharp logarithmic influence bound and two variance counterexamples.

**Abstract.** For a finite Boolean decision tree under uniform independent bits, the sum of absolute child covariances, weighted by node reach probabilities, is at most the sum of each coordinate influence times the base-two logarithm of its global query-node count. Counts zero and one receive weight zero. No coordinate repeats on a root-to-leaf path. A read-k tree therefore has absolute covariance at most I(f) log₂ k. The known dummy-prefix construction attains equality for powers of two. A four-variable witness and a nine-variable witness refute the coefficient-one logarithmic variance proposal. Every query in the latter witness is relevant. The formalization contains no Fourier-entropy theorem.

**Prior results.** [Wan, Wright, and Wu, ITCS 2014](https://doi.org/10.1145/2554797.2554806), introduced the covariance and the dummy-prefix construction. [Shalev, Section 6.2, Theorem 31](https://arxiv.org/abs/1806.03646v2), proved the square-root influence bound and proposed the logarithmic potential.

**Formal scope.** The standalone package uses Lean 4.19.0. Its 29 axiom reports are separate from the shared library's 29 Comparator declarations.

[Paper PDF](verification/additional-proofs/readk-covariance/docs/manuscript.pdf) · [LaTeX](verification/additional-proofs/readk-covariance/docs/manuscript.tex) · [Citation](verification/additional-proofs/readk-covariance/CITATION.bib) · [Related work](verification/additional-proofs/readk-covariance/docs/related-work.md) · [Reproduction](verification/additional-proofs/readk-covariance/README.md)

## Mathematical physics

### Stochastic thermal models

#### A three-state thermal counterexample to a heat-current kurtosis conjecture

**Family:** `thermal-kurtosis-counterexample`. **Result:** An exact negative spectral heat-cumulant ratio.

**Abstract.** A three-state model with two positive-temperature baths satisfies local detailed balance and has positive total off-diagonal transition rates. Its dominant tilted-generator eigenvalue has fourth-to-second derivative ratio −3470947982622836/176627429595846691. This refutes the thermal nonnegativity proposal in its finite spectral formulation. The proof constructs a smooth local eigenvalue branch, proves strict dominance over distinct complex eigenvalues, and calculates the exact derivatives.

**Original problem.** [Ptaszyński, Physical Review E 106, 024119 (2022), Eq. (19)](https://doi.org/10.1103/PhysRevE.106.024119). The finite thermal spectral model is specified in Eqs. (63)–(70).

**Formal scope.** The standalone package uses Lean 4.19.0. It does not formalize the stochastic long-time theorem that identifies the eigenvalue branch with a cumulant generating function. The witness does not refute the separate skewness conjecture or establish a minimal number of states.

[Paper PDF](verification/additional-proofs/thermal-kurtosis-counterexample/report.pdf) · [LaTeX](verification/additional-proofs/thermal-kurtosis-counterexample/report.tex) · [Citation](verification/additional-proofs/thermal-kurtosis-counterexample/CITATION.bib) · [Related work](verification/additional-proofs/thermal-kurtosis-counterexample/RELATED_WORK.md) · [Reproduction](verification/additional-proofs/thermal-kurtosis-counterexample/README.md)

## Discrete analysis

### The sharp level-one Fourier weight at density one eighth

For every Boolean indicator of mean 1/8 on a finite uniform cube, the level-one Fourier weight is at most 3/64. A codimension-three subcube attains the bound in every dimension at least three.

**Formal scope.** The formal proof includes arbitrary dimensions, the exact moment identities, the Hamming-distance bound, and sharpness witnesses.

**Prior work.** [Yu, On Average Distance, Level-1 Fourier Weight, and Chang’s Lemma, 2026 revision.](https://arxiv.org/abs/2504.02593v2)

[Paper PDF](verification/additional-proofs/sharp-eighth/manuscript.pdf) · [LaTeX](verification/additional-proofs/sharp-eighth/manuscript.tex) · [Citation](verification/additional-proofs/sharp-eighth/CITATION.bib) · [Reproduction](verification/additional-proofs/sharp-eighth/README.md)

## Graph theory

### Ultra-log-concavity of domination sequences of powers of paths and cycles

The domination counts of every natural power of a path or cycle form an ultra-log-concave sequence. The proof includes all natural graph orders and powers, the binomial normalization, and the boundary graph cases.

**Formal scope.** Actual finite graph domination counts for powers of paths and cycles. No theorem for arbitrary graphs or real-rootedness is asserted.

**Prior work.** [Galvin and Zhang, Conjecture 1.8.](https://arxiv.org/abs/2408.12731)

[Paper PDF](verification/additional-proofs/galvin-zhang/manuscript.pdf) · [LaTeX](verification/additional-proofs/galvin-zhang/manuscript.tex) · [Citation](verification/additional-proofs/galvin-zhang/CITATION.bib) · [Reproduction](verification/additional-proofs/galvin-zhang/README.md)

## Quantum information

### Universal entanglement embezzlement with inverse-quadratic logarithmic infidelity

A target-independent catalyst with local dimension 2^(4L) gives root infidelity at most 125m/L² for every Schmidt probability vector on m entries.

**Formal scope.** The proof constructs local basis permutations and establishes their finite complex Hilbert-space interpretation. Arbitrary changes to an external Schmidt basis are not separately formalized.

**Prior work.** [Van Dam and Hayden, 2003; Leung and Wang, 2014.](https://arxiv.org/abs/1311.6842)

[Paper PDF](verification/additional-proofs/universal-embezzlement/manuscript.pdf) · [LaTeX](verification/additional-proofs/universal-embezzlement/manuscript.tex) · [Citation](verification/additional-proofs/universal-embezzlement/CITATION.bib) · [Reproduction](verification/additional-proofs/universal-embezzlement/README.md)

## Matroid theory

### The exact asymmetric Merino–Welsh region for finite matroids

The theorem characterizes all nonnegative pairs (x,y) for which T_M(x,0) T_M(0,y) ≥ T_M(1,1)² holds for every finite matroid without loops or coloops.

**Formal scope.** The statement uses actual Mathlib matroids and the literal subset rank sum. It includes empty ground sets and finite ground sets in arbitrary ambient types.

**Prior work.** [Liu, 2026; Chen and Xie, 2026. The manuscript states the relation to the diagonal theorem.](https://github.com/michaeliu4/tutte-threshold)

[Paper PDF](verification/additional-proofs/asymmetric-tutte/manuscript.pdf) · [LaTeX](verification/additional-proofs/asymmetric-tutte/manuscript.tex) · [Citation](verification/additional-proofs/asymmetric-tutte/CITATION.bib) · [Reproduction](verification/additional-proofs/asymmetric-tutte/README.md)

## A sum-of-squares proof of the four-qubit Higuchi–Sudbery entropy bound

The average von Neumann entropy of the three two-qubit marginals of a pure four-qubit state is at most log(2) + log(3)/2. The Higuchi–Sudbery state attains this bound.

The proof uses all sixteen complex amplitudes, actual reduced-matrix eigenvalues, an exact sum-of-squares identity, and an explicit maximizing state.

[Paper](verification/additional-proofs/higuchi-sudbery/manuscript.pdf) · [Source](verification/additional-proofs/higuchi-sudbery/manuscript.tex) · [Citation](verification/additional-proofs/higuchi-sudbery/CITATION.bib) · [Proof and verification](verification/additional-proofs/higuchi-sudbery/README.md)

## A quartic entropy deficit for random rankings

A distribution on rankings of n labels has entropy at most (1 − ε⁴/144) log(n!) if every pairwise comparison has probability at distance at least ε > 0 from 1/2.

The proof includes all finite sizes and actual position-valued permutations. It assumes neither independent comparisons nor transitive preferred directions.

[Paper](verification/additional-proofs/quartic-rankings/manuscript.pdf) · [Source](verification/additional-proofs/quartic-rankings/manuscript.tex) · [Citation](verification/additional-proofs/quartic-rankings/CITATION.bib) · [Proof and verification](verification/additional-proofs/quartic-rankings/README.md)

## Research process and review

The initial research and proofs were generated autonomously by GPT 6 with Pro Reasoning in ChatGPT. GPT 6 Astra in Codex autonomously produced the formalizations and corrections. The authors checked the proofs to the best of their mathematical abilities. This check is not expert validation or peer review. See [AUTHORSHIP.md](AUTHORSHIP.md).
