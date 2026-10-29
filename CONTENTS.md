# Manuscript collection

**30 manuscripts and research notes across 29 result families in mathematics, theoretical computer science, and mathematical physics.**

[**Read the overview PDF**](overview.pdf).

## Manuscript map

Each family description links directly to its manuscripts and supporting materials. Related papers appear together under one subject. Each entry states the contribution and its formal verification limits. Supporting lemmas are not separate research contributions. The papers have not been peer reviewed. Formal verification does not establish historical priority.

## Mathematics

### Matrix theory

#### [Real positive-definite counterexamples to extended q-permanent monotonicity](preprints/q-permanent/paper.pdf)

**Family:** `q-permanent`. **Result:** Counterexample and all-parameter extension.

**Abstract.** For every real parameter q>1, a real symmetric positive-definite matrix has a negative q-permanent derivative at q. An explicit matrix of order five decreases from q=14 to q=15. Correlation matrices with no zero entries and integer-entry examples are also obtained. The dimension can depend on q. The real-symmetric question on [−1,1] remains outside the result.

**Original problem.** [Da Fonseca, 2010, Conjecture 1; 2018, Conjecture 2.](https://arxiv.org/abs/1804.02231)

[Paper PDF](preprints/q-permanent/paper.pdf) · [LaTeX](preprints/q-permanent/paper.tex) · [Bibliography](preprints/q-permanent/references.bib) · [Citation](preprints/q-permanent/citation.bib) · [Formal statement and prior work](lean/docs/q-permanent.md) · [Reproduction](verification/q-permanent/README.md)

#### [Gyires's permanent inequality for structured matrices](preprints/gyires-circulant-five/paper.pdf)

**Family:** `gyires-circulant-five`. **Result:** Structured matrix inequalities and related polynomial bounds. The principal order-five and order-six claims, the all-order permutation-polynomial and four-block theorems, the exceptional-vector theorem, and rank-two orders 2–8 have Lean proofs.

**Abstract.** The preprint proves Gyires's permanent inequality for several structured matrix classes. These include nonnegative circulants of orders five through seven, all-order permutation polynomials A=aI+bQ+cQ², and all-order four-block doubly stochastic matrices. Here Q is any permutation matrix and a,b,c are nonnegative. The four-block result permits unequal block sizes and zero entries. Further results cover one exceptional column or row and every rank-at-most-two doubly stochastic matrix through order fifteen. The supporting sections prove structural, scalar, deletion, balancing, local polynomial, and counting results. Exact counterexamples identify the limits of auxiliary assertions. The principal order-five claims include equality and a sharp sorted-gap bound with coefficient 484. The principal order-five and order-six claims, the all-order permutation-polynomial and four-block theorems, and the exceptional-vector theorem have complete Lean proofs. The rank-two result has a complete Lean proof for orders 2 through 8. The general order-seven circulant result and rank-two orders 9 through 15 remain incomplete in Lean. The unrestricted conjecture remains outside these results.

**Original problem.** [Gyires, 1978; Cheon and Wanless, 2005, Conjecture 20. Earlier formalization at the pinned Gyires repository.](https://github.com/dvgyl/gyires-circulant-5/tree/72cf49a51be42cf15592f91d991f0b0c76f58448)

[Paper PDF](preprints/gyires-circulant-five/paper.pdf) · [LaTeX](preprints/gyires-circulant-five/paper.tex) · [Bibliography](preprints/gyires-circulant-five/references.bib) · [Citation](preprints/gyires-circulant-five/citation.bib) · [Formal statement and prior work](lean/docs/gyires-circulant-five.md) · [Reproduction](verification/gyires-circulant-five/README.md)

#### [A polygon enclosure fails for sums of normal matrices](verification/additional-proofs/kovacec/manuscript/manuscript.pdf)

**Family:** `kovacec`.

A polygon enclosure fails for a specified pair of normal matrices and its complete transposition graph.

**Formal scope.** Actual normal matrices, determinants, straight-segment exterior and component exclusion are formalized. Correspondence with an external source conjecture is conditional.

[Paper PDF](verification/additional-proofs/kovacec/manuscript/manuscript.pdf) · [LaTeX](verification/additional-proofs/kovacec/manuscript/manuscript.tex) · [Reproduction and source context](verification/additional-proofs/kovacec/README.md) · [Citation](verification/additional-proofs/kovacec/CITATION.bib)

#### [An unbounded obstruction to projection AM–GM in Loewner order](verification/additional-proofs/projection-amgm/paper.pdf)

**Family:** `projection-amgm`.

Three rank-one orthogonal projections in dimension three violate the symmetrized-product Loewner AM–GM bound. No finite real multiplier repairs it, even with a positive-definite mean. The examples do not satisfy the additional nonsingular block structure of the motivating coordinate-descent application.

**Formal scope.** Lean verifies a rational three-projection matrix obstruction and a parameterized obstruction for every real multiplier in dimension three; rank-one, positive-definite mean, rational all-multiplier choices, and the standard minimal-factor observation have complete conventional proofs.

[Paper PDF](verification/additional-proofs/projection-amgm/paper.pdf) · [LaTeX](verification/additional-proofs/projection-amgm/paper.tex) · [Citation](verification/additional-proofs/projection-amgm/CITATION.bib) · [Proof and reproduction](verification/additional-proofs/projection-amgm/README.md)

### Graph theory and graph polynomials

#### [An entropy increase for a structurally disassortative DomiRank graph](preprints/domirank-entropy/paper.pdf)

**Family:** `domirank-entropy`. **Result:** Counterexample to an interval monotonicity conjecture.

**Abstract.** A connected graph with 14 vertices and 32 edges has negative degree–log-degree edge covariance. All resolvent scores are positive on [251/1000,63/250] inside the stable domain. Its entropy nevertheless increases by more than 1/10000 in natural-logarithm units. This refutes the source’s assertion for every positive-score interval.

**Original problem.** [Zhang and Zhao, arXiv:2610.00107v4, Conjecture 4.9.](https://arxiv.org/html/2610.00107v4)

[Paper PDF](preprints/domirank-entropy/paper.pdf) · [LaTeX](preprints/domirank-entropy/paper.tex) · [Bibliography](preprints/domirank-entropy/references.bib) · [Citation](preprints/domirank-entropy/citation.bib) · [Formal statement and prior work](lean/docs/domirank-entropy.md) · [Reproduction](verification/domirank-entropy/README.md)

#### [Ultra-log-concavity of domination sequences of powers of paths and cycles](verification/additional-proofs/galvin-zhang/manuscript.pdf)

**Family:** `galvin-zhang`.

The domination counts of every natural power of a path or cycle form an ultra-log-concave sequence. The proof includes all natural graph orders and powers, the binomial normalization, and the boundary graph cases.

**Formal scope.** Actual finite graph domination counts for powers of paths and cycles. No theorem for arbitrary graphs or real-rootedness is asserted.

**Prior work.** [Galvin and Zhang, Conjecture 1.8.](https://arxiv.org/abs/2408.12731)

[Paper PDF](verification/additional-proofs/galvin-zhang/manuscript.pdf) · [LaTeX](verification/additional-proofs/galvin-zhang/manuscript.tex) · [Citation](verification/additional-proofs/galvin-zhang/CITATION.bib) · [Reproduction](verification/additional-proofs/galvin-zhang/README.md)

#### [Sharp escape of complex domination roots in square flowers](verification/additional-proofs/graph-roots/manuscript.pdf)

**Family:** `graph-roots`.

Sharp complex-root escape for square flowers, with complete flower and book real-root classifications and multiplicities.

**Formal scope.** All numbered manuscript conclusions are formalized in seventy modules with 258 endpoint audits. Historical novelty and exact external-source correspondence remain provisional.

[Paper PDF](verification/additional-proofs/graph-roots/manuscript.pdf) · [LaTeX](verification/additional-proofs/graph-roots/manuscript.tex) · [Reproduction and source context](verification/additional-proofs/graph-roots/README.md) · [Citation](verification/additional-proofs/graph-roots/CITATION.bib)

#### [Leaf deletion can move the unique mode of a tree domination polynomial by two](verification/additional-proofs/leaf-deletion/manuscript/manuscript.pdf)

**Family:** `leaf-deletion`.

Deleting a leaf can move the unique mode of an explicit tree domination polynomial by two.

**Formal scope.** The fixed tree, deletion, actual domination counts and unique-mode movement are formalized. External question identity and historical priority remain provisional.

[Paper PDF](verification/additional-proofs/leaf-deletion/manuscript/manuscript.pdf) · [LaTeX](verification/additional-proofs/leaf-deletion/manuscript/manuscript.tex) · [Reproduction and source context](verification/additional-proofs/leaf-deletion/README.md) · [Citation](verification/additional-proofs/leaf-deletion/CITATION.bib)

### Inequalities and real analysis

#### [Diagonal concavity does not imply concavity for sums of elementary symmetric polynomials](preprints/diagonal-concavity/paper.pdf)

**Family:** `diagonal-concavity`. **Result:** Counterexample and complete parameter classification.

**Abstract.** For positive M, let f=1+Mσ₁+σ₂+Mσ₃+σ₄ in four variables. Its fourth root is concave on the positive diagonal exactly when M≥1. It is concave on the full positive orthant exactly when M=1. Every M>1 therefore disproves Lachaume’s diagonal criterion with strictly positive coefficients.

**Original problem.** [Lachaume, arXiv:1712.10327v1, Conjecture 1.](https://arxiv.org/abs/1712.10327v1)

[Paper PDF](preprints/diagonal-concavity/paper.pdf) · [LaTeX](preprints/diagonal-concavity/paper.tex) · [Bibliography](preprints/diagonal-concavity/references.bib) · [Citation](preprints/diagonal-concavity/citation.bib) · [Formal statement and prior work](lean/docs/diagonal-concavity.md) · [Reproduction](verification/diagonal-concavity/README.md)

### Integer sequences and combinatorics

#### Alternating Motzkin sums

**Family:** `alternating-motzkin`. The principal root bound and bounded-forcing companion belong to one sequence family.

##### [Sharp root log-concavity of alternating Motzkin sums](preprints/alternating-motzkin/paper.pdf)

**Result:** Conjecture resolution with an optimal threshold.

**Abstract.** Let Tₙ be the alternating sum of Motzkin numbers through index n. The sequence Tₙ^(1/n) is strictly log-concave on its tail starting at five. The inequality reverses at center five, so no earlier tail is log-concave. This strengthens Zhao’s proposed tail starting at nine. The source recurrence and finite sum are linked in Lean.

**Original problem.** [Zhao, INTEGERS 26 (2026), A55, Conjecture 1; OEIS A187306.](https://math.colgate.edu/~integers/aa55/aa55.pdf)

[Paper PDF](preprints/alternating-motzkin/paper.pdf) · [LaTeX](preprints/alternating-motzkin/paper.tex) · [Bibliography](preprints/alternating-motzkin/references.bib) · [Citation](preprints/alternating-motzkin/citation.bib) · [Formal statement and prior work](lean/docs/alternating-motzkin.md) · [Reproduction](verification/alternating-motzkin/README.md)

##### [Sharp log-concavity for alternating Motzkin sums](verification/additional-proofs/motzkin-bounded-forcing/manuscript.pdf)

A robust bounded-forcing recurrence theorem and corrected scaled corollary, with applications to alternating Motzkin-type sums.

**Formal scope.** The arbitrary-real recurrence theorem and scaled corollary, including zero forcing, are formalized. Concrete sequences, uniform-family applications, root transfer and threshold classification retain conventional proofs.

[Paper PDF](verification/additional-proofs/motzkin-bounded-forcing/manuscript.pdf) · [LaTeX](verification/additional-proofs/motzkin-bounded-forcing/manuscript.tex) · [Reproduction and source context](verification/additional-proofs/motzkin-bounded-forcing/README.md) · [Citation](verification/additional-proofs/motzkin-bounded-forcing/CITATION.bib)

#### [Counterexamples to a late-iterate ordering conjecture for generalized Hofstadter functions](preprints/hofstadter-iteration/paper.pdf)

**Family:** `hofstadter-iteration`. **Result:** Counterexamples for every parameter k≥4.

**Abstract.** For every k≥4, some input n satisfies Fₖ^(2k+1)(n)>Fₖ₊₁^(2k+2)(n). The proof constructs inverse iterates whose exact gap is k−3. The finite witness F₄⁹(132)=8>7=F₅¹⁰(132) gives the first instance. The result concerns infinitely many parameters, not infinitely many violating inputs for each fixed parameter.

**Original problem.** [Letouzey, Li, and Steiner, Journal of Integer Sequences 29 (2026), 26.3.3, conjecture before Lemma 7.6.](https://cs.uwaterloo.ca/journals/JIS/VOL29/Letouzey/letouzey3.pdf)

[Paper PDF](preprints/hofstadter-iteration/paper.pdf) · [LaTeX](preprints/hofstadter-iteration/paper.tex) · [Bibliography](preprints/hofstadter-iteration/references.bib) · [Citation](preprints/hofstadter-iteration/citation.bib) · [Formal statement and prior work](lean/docs/hofstadter-iteration.md) · [Reproduction](verification/hofstadter-iteration/README.md)

#### [A positive constant-recursive sequence with nonquasipolynomial power ranks](verification/additional-proofs/power-rank/manuscript.pdf)

**Family:** `power-rank`.

Exact minimal recurrences for every power of a rank-thirteen sequence, nonquasipolynomial ranks, and infinitely many power-rank profiles at each rank at least three.

**Formal scope.** The main and arbitrary-rank companion theorems are formalized. Generating-function and polynomial corollaries retain conventional proofs.

[Paper PDF](verification/additional-proofs/power-rank/manuscript.pdf) · [LaTeX](verification/additional-proofs/power-rank/manuscript.tex) · [Reproduction and source context](verification/additional-proofs/power-rank/README.md) · [Citation](verification/additional-proofs/power-rank/CITATION.bib)

### Discrete analysis, probability and entropy

#### [The sharp level-one Fourier weight at density one eighth](verification/additional-proofs/sharp-eighth/manuscript.pdf)

**Family:** `sharp-eighth`.

For every Boolean indicator of mean 1/8 on a finite uniform cube, the level-one Fourier weight is at most 3/64. A codimension-three subcube attains the bound in every dimension at least three.

**Formal scope.** The formal proof includes arbitrary dimensions, the exact moment identities, the Hamming-distance bound, and sharpness witnesses.

**Prior work.** [Yu, On Average Distance, Level-1 Fourier Weight, and Chang’s Lemma, 2026 revision.](https://arxiv.org/abs/2504.02593v2)

[Paper PDF](verification/additional-proofs/sharp-eighth/manuscript.pdf) · [LaTeX](verification/additional-proofs/sharp-eighth/manuscript.tex) · [Citation](verification/additional-proofs/sharp-eighth/CITATION.bib) · [Reproduction](verification/additional-proofs/sharp-eighth/README.md)

#### [A quartic entropy deficit for random rankings](verification/additional-proofs/quartic-rankings/manuscript.pdf)

**Family:** `quartic-rankings`.

A distribution on rankings of n labels has entropy at most (1 − ε⁴/144) log(n!) if every pairwise comparison has probability at distance at least ε > 0 from 1/2.

The proof includes all finite sizes and actual position-valued permutations. It assumes neither independent comparisons nor transitive preferred directions.

[Paper](verification/additional-proofs/quartic-rankings/manuscript.pdf) · [Source](verification/additional-proofs/quartic-rankings/manuscript.tex) · [Citation](verification/additional-proofs/quartic-rankings/CITATION.bib) · [Proof and verification](verification/additional-proofs/quartic-rankings/README.md)

#### [Sharp universal Rényi threshold for iid sums on finite Sidon sets](verification/additional-proofs/sidon-renyi/manuscript.pdf)

**Family:** `sidon-renyi`.

A sharp universal Renyi-order threshold for iid sums supported on finite strong-B2 sets.

**Formal scope.** The finite-support iid theorem, zero probabilities and critical endpoint are formalized. Comparison with unverified source definitions is conditional.

[Paper PDF](verification/additional-proofs/sidon-renyi/manuscript.pdf) · [LaTeX](verification/additional-proofs/sidon-renyi/manuscript.tex) · [Reproduction and source context](verification/additional-proofs/sidon-renyi/README.md) · [Citation](verification/additional-proofs/sidon-renyi/CITATION.bib)

### Matroid theory

#### [The exact asymmetric Merino–Welsh region for finite matroids](verification/additional-proofs/asymmetric-tutte/manuscript.pdf)

**Family:** `asymmetric-tutte`.

The theorem characterizes all nonnegative pairs (x,y) for which T_M(x,0) T_M(0,y) ≥ T_M(1,1)² holds for every finite matroid without loops or coloops.

**Formal scope.** The statement uses actual Mathlib matroids and the literal subset rank sum. It includes empty ground sets and finite ground sets in arbitrary ambient types.

**Prior work.** [Liu, 2026; Chen and Xie, 2026. The manuscript states the relation to the diagonal theorem.](https://github.com/michaeliu4/tutte-threshold)

[Paper PDF](verification/additional-proofs/asymmetric-tutte/manuscript.pdf) · [LaTeX](verification/additional-proofs/asymmetric-tutte/manuscript.tex) · [Citation](verification/additional-proofs/asymmetric-tutte/CITATION.bib) · [Reproduction](verification/additional-proofs/asymmetric-tutte/README.md)

### Optimization

#### [A rational five-cycle for two-block ADMM with multiplier step below two](verification/additional-proofs/admm-counterexample/paper/admm_counterexample.pdf)

**Family:** `admm-counterexample`.

An exact period-five orbit for multiplier-only two-block ADMM at step 199/100.

**Formal scope.** Seven modules and eleven endpoint audits cover the orbit, minimizers and optimizer. Analytic regularity of the finite strongly convex extension retains a conventional proof.

[Paper PDF](verification/additional-proofs/admm-counterexample/paper/admm_counterexample.pdf) · [LaTeX](verification/additional-proofs/admm-counterexample/paper/admm_counterexample.tex) · [Reproduction and source context](verification/additional-proofs/admm-counterexample/README.md) · [Citation](verification/additional-proofs/admm-counterexample/CITATION.bib)

#### [The exact last-gradient bound for constant-step gradient descent in the strongly convex case](verification/additional-proofs/strong-gradient/manuscript.pdf)

**Family:** `strong-gradient`.

The exact final-gradient guarantee holds on every real Hilbert space for L > 0, 0 ≤ μ ≤ L, normalized step 0 ≤ h ≤ 2 and every natural horizon. Actual one-dimensional Huber and quadratic functions attain its two branches.

**Formal scope.** The actual-function upper bound and normalized actual-function attainment are formalized, including every horizon and closed parameter boundary. Sharpness for arbitrary L > 0 and radius R > 0 is proved by rescaling in the manuscript, without a separate Lean wrapper.

[Paper PDF](verification/additional-proofs/strong-gradient/manuscript.pdf) · [LaTeX](verification/additional-proofs/strong-gradient/manuscript.tex) · [Citation](verification/additional-proofs/strong-gradient/CITATION.bib) · [Proof and reproduction](verification/additional-proofs/strong-gradient/README.md)

## Theoretical computer science

### Sampling algorithms and information theory

#### [Counterexamples to a best-of-n win-rate bound at every budget](preprints/best-of-n/paper.pdf)

**Family:** `best-of-n`. **Result:** Disproof for every budget n≥2 and every positive atom cap.

**Abstract.** For every n≥2 and δ>0, there is a finite positive reference distribution whose largest atom is at most δ and whose best-of-n policy violates the proposed divergence–win-rate curve. A four-response best-of-two example gives exact probabilities and a strict logarithmic certificate. The proof uses finite interval bounds and gives a quantitative positive gap. It does not determine the sharp replacement curve.

**Original problem.** [Beirami et al., ICML 2025, Conjecture 7.2 and equation (28).](https://proceedings.mlr.press/v267/beirami25a.html)

[Paper PDF](preprints/best-of-n/paper.pdf) · [LaTeX](preprints/best-of-n/paper.tex) · [Bibliography](preprints/best-of-n/references.bib) · [Citation](preprints/best-of-n/citation.bib) · [Formal statement and prior work](lean/docs/best-of-n.md) · [Reproduction](verification/best-of-n/README.md)

### Boolean functions and decision trees

#### [Logarithmic influence bounds and variance counterexamples for Boolean decision-tree covariance](verification/additional-proofs/readk-covariance/docs/manuscript.pdf)

**Family:** `readk-covariance`. **Result:** A sharp logarithmic influence bound and two variance counterexamples.

**Abstract.** For a finite Boolean decision tree under uniform independent bits, the sum of absolute child covariances, weighted by node reach probabilities, is at most the sum of each coordinate influence times the base-two logarithm of its global query-node count. Counts zero and one receive weight zero. No coordinate repeats on a root-to-leaf path. A read-k tree therefore has absolute covariance at most I(f) log₂ k. The known dummy-prefix construction attains equality for powers of two. A four-variable witness and a nine-variable witness refute the coefficient-one logarithmic variance proposal. Every query in the latter witness is relevant. The formalization contains no Fourier-entropy theorem.

**Prior results.** [Wan, Wright, and Wu, ITCS 2014](https://doi.org/10.1145/2554797.2554806), introduced the covariance and the dummy-prefix construction. [Shalev, Section 6.2, Theorem 31](https://arxiv.org/abs/1806.03646v2), proved the square-root influence bound and proposed the logarithmic potential.

**Formal scope.** The standalone package uses Lean 4.19.0. Its 29 axiom reports are separate from the shared library's 29 Comparator declarations.

[Paper PDF](verification/additional-proofs/readk-covariance/docs/manuscript.pdf) · [LaTeX](verification/additional-proofs/readk-covariance/docs/manuscript.tex) · [Citation](verification/additional-proofs/readk-covariance/CITATION.bib) · [Related work](verification/additional-proofs/readk-covariance/docs/related-work.md) · [Reproduction](verification/additional-proofs/readk-covariance/README.md)

### Fair division

#### [Ordered-instance allocation transfer with exact extra-copy preservation](verification/additional-proofs/ordered-allocation/manuscript.pdf)

**Family:** `ordered-allocation`.

A set-valued ordered-instance transfer preserving utility improvement, the exact extra-copy count, per-good caps and coverage.

**Formal scope.** The transfer theorem is formalized. Existence of a fair allocation before transfer is outside the result; external source comparison is provisional.

[Paper PDF](verification/additional-proofs/ordered-allocation/manuscript.pdf) · [LaTeX](verification/additional-proofs/ordered-allocation/manuscript.tex) · [Reproduction and source context](verification/additional-proofs/ordered-allocation/README.md) · [Citation](verification/additional-proofs/ordered-allocation/CITATION.bib)

### Proof complexity

#### [Unbounded coalesced-mass certificates for resolution trees](verification/additional-proofs/kunisky/paper.pdf)

**Family:** `kunisky`.

A coalesced dyadic clause-mass functional has exact supremum n+1 on the stated unrestricted resolution-tree class and is unbounded across dimensions.

**Formal scope.** The internally defined resolution-tree functional and proof class are formalized. No unconditional identification with an external conjecture or a regular proof class is claimed.

[Paper PDF](verification/additional-proofs/kunisky/paper.pdf) · [LaTeX](verification/additional-proofs/kunisky/paper.tex) · [Reproduction and source context](verification/additional-proofs/kunisky/README.md) · [Citation](verification/additional-proofs/kunisky/CITATION.bib)

## Mathematical physics

### Stochastic thermodynamics

#### [A three-state thermal counterexample to a heat-current kurtosis conjecture](verification/additional-proofs/thermal-kurtosis-counterexample/report.pdf)

**Family:** `thermal-kurtosis-counterexample`. **Result:** An exact negative spectral heat-cumulant ratio.

**Abstract.** A three-state model with two positive-temperature baths satisfies local detailed balance and has positive total off-diagonal transition rates. Its dominant tilted-generator eigenvalue has fourth-to-second derivative ratio −3470947982622836/176627429595846691. This refutes the thermal nonnegativity proposal in its finite spectral formulation. The proof constructs a smooth local eigenvalue branch, proves strict dominance over distinct complex eigenvalues, and calculates the exact derivatives.

**Original problem.** [Ptaszyński, Physical Review E 106, 024119 (2022), Eq. (19)](https://doi.org/10.1103/PhysRevE.106.024119). The finite thermal spectral model is specified in Eqs. (63)–(70).

**Formal scope.** The standalone package uses Lean 4.19.0. It does not formalize the stochastic long-time theorem that identifies the eigenvalue branch with a cumulant generating function. The witness does not refute the separate skewness conjecture or establish a minimal number of states.

[Paper PDF](verification/additional-proofs/thermal-kurtosis-counterexample/report.pdf) · [LaTeX](verification/additional-proofs/thermal-kurtosis-counterexample/report.tex) · [Citation](verification/additional-proofs/thermal-kurtosis-counterexample/CITATION.bib) · [Related work](verification/additional-proofs/thermal-kurtosis-counterexample/RELATED_WORK.md) · [Reproduction](verification/additional-proofs/thermal-kurtosis-counterexample/README.md)

#### [A sharp universal skewness bound for unicyclic currents](verification/additional-proofs/unicyclic-skewness/manuscript.pdf)

**Family:** `unicyclic-skewness`.

The net marked-edge current on every finite bidirectional Markov ring with at least three states, positive rates and unequal forward and reverse rate products satisfies −1/16 ≤ C₃/C₁ ≤ 1. The two-channel two-state case has the stronger interval [1/4,1]. This ratio is not standardized skewness.

**Formal scope.** The interval for actual tilted-matrix derivatives and a local branch is formalized. Identification with long-time stochastic cumulants and sharpness have conventional proofs. Lean does not construct a continuous-time sample-path probability space or a separate optimizing-sequence theorem.

[Paper PDF](verification/additional-proofs/unicyclic-skewness/manuscript.pdf) · [LaTeX](verification/additional-proofs/unicyclic-skewness/manuscript.tex) · [Citation](verification/additional-proofs/unicyclic-skewness/CITATION.bib) · [Proof and reproduction](verification/additional-proofs/unicyclic-skewness/README.md)

### Quantum information

#### [Universal entanglement embezzlement with inverse-quadratic logarithmic infidelity](verification/additional-proofs/universal-embezzlement/manuscript.pdf)

**Family:** `universal-embezzlement`.

A target-independent catalyst with local dimension 2^(4L) gives root infidelity at most 125m/L² for every Schmidt probability vector on m entries.

**Formal scope.** The proof constructs local basis permutations and establishes their finite complex Hilbert-space interpretation. Arbitrary changes to an external Schmidt basis are not separately formalized.

**Prior work.** [Van Dam and Hayden, 2003; Leung and Wang, 2014.](https://arxiv.org/abs/1311.6842)

[Paper PDF](verification/additional-proofs/universal-embezzlement/manuscript.pdf) · [LaTeX](verification/additional-proofs/universal-embezzlement/manuscript.tex) · [Citation](verification/additional-proofs/universal-embezzlement/CITATION.bib) · [Reproduction](verification/additional-proofs/universal-embezzlement/README.md)

#### [A sum-of-squares proof of the four-qubit Higuchi–Sudbery entropy bound](verification/additional-proofs/higuchi-sudbery/manuscript.pdf)

**Family:** `higuchi-sudbery`.

The average von Neumann entropy of the three two-qubit marginals of a pure four-qubit state is at most log(2) + log(3)/2. The Higuchi–Sudbery state attains this bound.

The proof uses all sixteen complex amplitudes, actual reduced-matrix eigenvalues, an exact sum-of-squares identity, and an explicit maximizing state.

[Paper](verification/additional-proofs/higuchi-sudbery/manuscript.pdf) · [Source](verification/additional-proofs/higuchi-sudbery/manuscript.tex) · [Citation](verification/additional-proofs/higuchi-sudbery/CITATION.bib) · [Proof and verification](verification/additional-proofs/higuchi-sudbery/README.md)

#### [A pure-state matched-basis information inequality violation in dimension five](verification/additional-proofs/pure-ecqc/manuscript/manuscript.pdf)

**Family:** `pure-ecqc`.

A dimension-five pure-state matched-basis information inequality violation, with a conventional all-prime companion.

**Formal scope.** The dimension-five identical-local-basis theorem is formalized. The prime-family extension is conventional; arbitrary or independently optimized basis choices are outside the result.

[Paper PDF](verification/additional-proofs/pure-ecqc/manuscript/manuscript.pdf) · [LaTeX](verification/additional-proofs/pure-ecqc/manuscript/manuscript.tex) · [Reproduction and source context](verification/additional-proofs/pure-ecqc/README.md) · [Citation](verification/additional-proofs/pure-ecqc/CITATION.bib)

#### [Exact three-setting correlation bounds at fixed steering centre](verification/additional-proofs/steering-bounds/paper/steering_bounds.pdf)

**Family:** `steering-bounds`.

The exact least upper bound of the optimized three-setting squared correlation value is determined for every two-qubit steering-centre length. The threshold for a value greater than one is c < 2/3. Attainment, nonattainment and the singular marginal boundary are included.

**Formal scope.** Actual two-qubit density matrices, canonical filters, Pauli correlations, the exact least upper bound, attainment and nonattainment, and fully entangled fraction are formalized. The steering-ellipsoid and optimized CJWR measurement interpretations use cited external correspondences; general steerability is outside the result.

[Paper PDF](verification/additional-proofs/steering-bounds/paper/steering_bounds.pdf) · [LaTeX](verification/additional-proofs/steering-bounds/paper/steering_bounds.tex) · [Citation](verification/additional-proofs/steering-bounds/CITATION.bib) · [Proof and reproduction](verification/additional-proofs/steering-bounds/README.md)

#### [The three-state root-fidelity entropy bound](verification/additional-proofs/fidelity-three-state/manuscript.pdf)

**Family:** `fidelity-three-state`.

The entropy of the weighted three-by-three root-fidelity matrix bounds the Holevo quantity of every three-state ensemble in arbitrary finite dimension. The result includes mixed and singular states and zero probabilities.

**Formal scope.** The unrestricted three-state ensemble theorem is formalized for actual positive semidefinite complex matrices of trace one, nonnegative weights summing to one, spectral entropy and nuclear-norm root fidelity. Credited QICLean foundations and prior-work adapters retain their attribution.

[Paper PDF](verification/additional-proofs/fidelity-three-state/manuscript.pdf) · [LaTeX](verification/additional-proofs/fidelity-three-state/manuscript.tex) · [Citation](verification/additional-proofs/fidelity-three-state/CITATION.bib) · [Proof and reproduction](verification/additional-proofs/fidelity-three-state/README.md)

## Proof status and authorship

The [verification guide](verification/README.md) records completed checks and reproduction commands. [Research status](RESEARCH_STATUS.md) and [unfinished formal proofs](UNFINISHED.md) identify limitations. The [authorship disclosure](AUTHORSHIP.md) describes fully autonomous agentic research and its supported contribution history.
