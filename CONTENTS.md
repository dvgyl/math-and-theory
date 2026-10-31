# Manuscript collection

**51 manuscripts and research notes across 50 result families in mathematics, theoretical computer science, and mathematical physics.**

[**Read the overview PDF**](overview.pdf).

## Manuscript map

Each family description links directly to its manuscripts and supporting materials. Related papers appear together under one subject. Each entry states the contribution and its formal verification limits. Supporting lemmas are not separate research contributions. The papers have not been peer reviewed. Formal verification does not establish historical priority.

## Mathematics

### Matrix theory

#### [Real positive-definite counterexamples to extended q-permanent monotonicity](papers/mathematics/q-permanent/paper.pdf)

**Family:** `q-permanent`. **Result:** Counterexample and all-parameter extension.

**Abstract.** For every real parameter q>1, a real symmetric positive-definite matrix has a negative q-permanent derivative at q. An explicit matrix of order five decreases from q=14 to q=15. Correlation matrices with no zero entries and integer-entry examples are also obtained. The dimension can depend on q. The real-symmetric question on [−1,1] remains outside the result.

**Original problem.** [Da Fonseca, 2010, Conjecture 1; 2018, Conjecture 2.](https://arxiv.org/abs/1804.02231)

[Paper PDF](papers/mathematics/q-permanent/paper.pdf) · [LaTeX](papers/mathematics/q-permanent/paper.tex) · [Bibliography](papers/mathematics/q-permanent/references.bib) · [Citation](papers/mathematics/q-permanent/citation.bib) · [Formal statement and prior work](lean/docs/mathematics/q-permanent.md) · [Reproduction](papers/mathematics/q-permanent/verification/README.md)

#### [Gyires's permanent inequality for structured matrices](papers/mathematics/gyires/paper.pdf)

**Family:** Gyires. **Result:** Structured matrix inequalities and related polynomial bounds. The principal order-five and order-six claims, the all-order permutation-polynomial and four-block theorems, the exceptional-vector theorem, and rank-two orders 2–8 have Lean proofs.

**Abstract.** The preprint proves Gyires's permanent inequality for several structured matrix classes. These include nonnegative circulants of orders five through seven, all-order permutation polynomials A=aI+bQ+cQ², and all-order four-block doubly stochastic matrices. Here Q is any permutation matrix and a,b,c are nonnegative. The four-block result permits unequal block sizes and zero entries. Further results cover one exceptional column or row and every rank-at-most-two doubly stochastic matrix through order fifteen. The supporting sections prove structural, scalar, deletion, balancing, local polynomial, and counting results. Exact counterexamples identify the limits of auxiliary assertions. The principal order-five claims include equality and a sharp sorted-gap bound with coefficient 484. The principal order-five and order-six claims, the all-order permutation-polynomial and four-block theorems, and the exceptional-vector theorem have complete Lean proofs. The rank-two result has a complete Lean proof for orders 2 through 8. The general order-seven circulant result and rank-two orders 9 through 15 remain incomplete in Lean. The unrestricted conjecture remains outside these results.

**Original problem.** [Gyires, 1978; Cheon and Wanless, 2005, Conjecture 20. Earlier formalization at the pinned Gyires repository.](https://github.com/dvgyl/gyires-circulant-5/tree/72cf49a51be42cf15592f91d991f0b0c76f58448)

[Paper PDF](papers/mathematics/gyires/paper.pdf) · [LaTeX](papers/mathematics/gyires/paper.tex) · [Bibliography](papers/mathematics/gyires/references.bib) · [Citation](papers/mathematics/gyires/citation.bib) · [Formal statement and prior work](lean/docs/mathematics/gyires.md) · [Reproduction](papers/mathematics/gyires/verification/README.md)

#### [A polygon enclosure fails for sums of normal matrices](papers/mathematics/kovacec/manuscript/manuscript.pdf)

**Family:** `kovacec`.

A polygon enclosure fails for a specified pair of normal matrices and its complete transposition graph.

**Formal scope.** Actual normal matrices, determinants, straight-segment exterior and component exclusion are formalized. Correspondence with an external source conjecture is conditional.

**Priority and subsequent correspondence.** On 29 October 2026, through correspondence with Professor Alexander Kovačec, I learned of his own June 2026 counterexample, documented in an unpublished preprint, and of another counterexample sent to him by Wenlin Zhang. Equivalence with this construction has not been established. [Priority and novelty record](PRIORITY_AND_NOVELTY.md#kovačec-polygon-enclosure).

[Paper PDF](papers/mathematics/kovacec/manuscript/manuscript.pdf) · [LaTeX](papers/mathematics/kovacec/manuscript/manuscript.tex) · [Reproduction and source context](papers/mathematics/kovacec/README.md) · [Citation](papers/mathematics/kovacec/CITATION.bib)

#### [An unbounded obstruction to projection AM–GM in Loewner order](papers/mathematics/projection-amgm/paper.pdf)

**Family:** `projection-amgm`.

Three rank-one orthogonal projections in dimension three violate the symmetrized-product Loewner AM–GM bound. No finite real multiplier repairs it, even with a positive-definite mean. The examples do not satisfy the additional nonsingular block structure of the motivating coordinate-descent application.

**Formal scope.** Lean verifies a rational three-projection matrix obstruction and a parameterized obstruction for every real multiplier in dimension three; rank-one, positive-definite mean, rational all-multiplier choices, and the standard minimal-factor observation have complete conventional proofs.

**Prior work.** The Omega Institute's public repository records a refutation with the same three projections and form −8/243, committed on 12 October 2026 (issue #15647), and a block-structured counterexample (issue #17674). No priority is claimed for the three-projection counterexample; the unbounded-multiplier theorem is not in that record. [Priority and novelty record](PRIORITY_AND_NOVELTY.md#omega-projection-amgm).

[Paper PDF](papers/mathematics/projection-amgm/paper.pdf) · [LaTeX](papers/mathematics/projection-amgm/paper.tex) · [Citation](papers/mathematics/projection-amgm/CITATION.bib) · [Proof and reproduction](papers/mathematics/projection-amgm/README.md)

#### [Matrix-pencil rank distance as an explicit completion problem](papers/mathematics/matrix-pencil-completion/manuscript.pdf)

**Family:** `matrix-pencil-completion`.

Let A and B be m × n matrix pencils over an infinite field and δ(A, B) the least normal rank of A′ − B′ over pencils A′, B′ strictly equivalent to A, B. For distinct c, d and every x ≥ 0, δ(A, B) ≤ x exactly when an explicit (2m+n) × (2n+m) dilation K_{c,d}(A) is obtained from K_{c,d}(B) ⊕ (t − d)I_x by one constant full-row-rank and one constant full-column-rank matrix. No regularity, rank or spectral condition is imposed, and the anchors may be eigenvalues. Over an algebraically closed field and at anchors outside the spectra, a known block minimal bases theorem turns this into Conjecture 1 of Dodig and Stošić: the bounded rank perturbation problem for matrix pencils is a completion problem.

**Formal scope.** The explicit equivalence over every infinite field, for arbitrary rectangular pencils, every border size and distinct anchors including eigenvalues, and the common-summand cancellation are formalized in two Lean projects. The identification with the barred pencils of the conjecture uses a published linearization theorem and is not formalized.

**Prior work.** [Dodig and Stošić, 2025.](https://doi.org/10.13001/ela.2025.9593)

[Paper PDF](papers/mathematics/matrix-pencil-completion/manuscript.pdf) · [LaTeX](papers/mathematics/matrix-pencil-completion/manuscript.tex) · [Proof and reproduction](papers/mathematics/matrix-pencil-completion/README.md) · [Citation](papers/mathematics/matrix-pencil-completion/CITATION.bib)

#### [Counterexamples to the Kronecker-square lower bound for nonnegative rank](papers/mathematics/nonnegative-rank-kronecker/manuscript.pdf)

**Family:** `nonnegative-rank-kronecker`.

Vandaele, Gillis, Glineur and Tuyttens conjectured in 2016 that every nonnegative matrix M satisfies rank₊(M ⊗ M) ≥ rank₊(M) rank(M). For every k ≥ 0 an explicit rational nonnegative matrix C of order k + 11, rank k + 10 and nonnegative rank k + 11 has rank₊(C ⊗ C) ≤ (k + 10)² + 9, so the conjecture fails by at least k + 1. The matrix is the direct sum of a classical 4 × 4 matrix of rank three and nonnegative rank four with a small diagonal perturbation of an all-ones matrix; in the mixed Kronecker blocks a positive rank-one term absorbs a small real perturbation of rank q with only q + 1 nonnegative terms. At k = 0 an exact rational factorization of width 109 beats the conjectured bound 110.

**Formal scope.** The whole family is formalized in Lean, with nonnegative rank minimized over all real nonnegative factorizations, together with a literal negation of the conjecture over all finite rectangular nonnegative real matrices. The width-109 factorization of the order-11 witness is also checked in exact rational arithmetic. The exact nonnegative rank of the squares is not determined.

**Prior work.** [Vandaele, Gillis, Glineur and Tuyttens, 2016.](https://doi.org/10.1007/s10898-015-0350-z)

[Paper PDF](papers/mathematics/nonnegative-rank-kronecker/manuscript.pdf) · [LaTeX](papers/mathematics/nonnegative-rank-kronecker/manuscript.tex) · [Proof and reproduction](papers/mathematics/nonnegative-rank-kronecker/README.md) · [Citation](papers/mathematics/nonnegative-rank-kronecker/CITATION.bib)

### Graph theory and graph polynomials

#### [An entropy increase for a structurally disassortative DomiRank graph](papers/mathematics/domirank-entropy/paper.pdf)

**Family:** `domirank-entropy`. **Result:** Counterexample to an interval monotonicity conjecture.

**Abstract.** A connected graph with 14 vertices and 32 edges has negative degree–log-degree edge covariance. All resolvent scores are positive on [251/1000,63/250] inside the stable domain. Its entropy nevertheless increases by more than 1/10000 in natural-logarithm units. This refutes the source’s assertion for every positive-score interval.

**Original problem.** [Zhang and Zhao, arXiv:2610.00107v4, Conjecture 4.9.](https://arxiv.org/html/2610.00107v4)

**Prior work.** The Omega Institute's public repository records a refutation of the broader unconditional assertion of version 1, committed on 5 October 2026 (issue #13267), with a graph that does not satisfy the hypothesis of Conjecture 4.9. [Priority and novelty record](PRIORITY_AND_NOVELTY.md#omega-domirank-entropy).

[Paper PDF](papers/mathematics/domirank-entropy/paper.pdf) · [LaTeX](papers/mathematics/domirank-entropy/paper.tex) · [Bibliography](papers/mathematics/domirank-entropy/references.bib) · [Citation](papers/mathematics/domirank-entropy/citation.bib) · [Formal statement and prior work](lean/docs/mathematics/domirank-entropy.md) · [Reproduction](papers/mathematics/domirank-entropy/verification/README.md)

#### [Ultra-log-concavity of domination sequences of powers of paths and cycles](papers/mathematics/galvin-zhang/manuscript.pdf)

**Family:** `galvin-zhang`.

The domination counts of every natural power of a path or cycle form an ultra-log-concave sequence. The proof includes all natural graph orders and powers, the binomial normalization, and the boundary graph cases.

**Formal scope.** Actual finite graph domination counts for powers of paths and cycles. No theorem for arbitrary graphs or real-rootedness is asserted.

**Prior work.** [Galvin and Zhang, Conjecture 1.8.](https://arxiv.org/abs/2408.12731)

[Paper PDF](papers/mathematics/galvin-zhang/manuscript.pdf) · [LaTeX](papers/mathematics/galvin-zhang/manuscript.tex) · [Citation](papers/mathematics/galvin-zhang/CITATION.bib) · [Reproduction](papers/mathematics/galvin-zhang/README.md)

#### [Sharp escape of complex domination roots in square flowers](papers/mathematics/graph-roots/manuscript.pdf)

**Family:** `graph-roots`.

Sharp complex-root escape for square flowers, with complete flower and book real-root classifications and multiplicities.

**Formal scope.** All numbered manuscript conclusions are formalized in seventy modules with 258 endpoint audits. Historical novelty and exact external-source correspondence remain provisional.

**Prior work.** The Omega Institute's public repository records a refutation of Rather's book-graph Conjecture 5.4 at n = 1, committed on 28 October 2026 (issue #23025), about 17 hours before my first commit. No priority is claimed for it. [Priority and novelty record](PRIORITY_AND_NOVELTY.md#omega-book-graph-domination-roots).

[Paper PDF](papers/mathematics/graph-roots/manuscript.pdf) · [LaTeX](papers/mathematics/graph-roots/manuscript.tex) · [Reproduction and source context](papers/mathematics/graph-roots/README.md) · [Citation](papers/mathematics/graph-roots/CITATION.bib)

#### [Leaf deletion can move the unique mode of a tree domination polynomial by two](papers/mathematics/leaf-deletion/manuscript/manuscript.pdf)

**Family:** `leaf-deletion`.

Deleting a leaf can move the unique mode of an explicit tree domination polynomial by two.

**Formal scope.** The fixed tree, deletion, actual domination counts and unique-mode movement are formalized. External question identity and historical priority remain provisional.

[Paper PDF](papers/mathematics/leaf-deletion/manuscript/manuscript.pdf) · [LaTeX](papers/mathematics/leaf-deletion/manuscript/manuscript.tex) · [Reproduction and source context](papers/mathematics/leaf-deletion/README.md) · [Citation](papers/mathematics/leaf-deletion/CITATION.bib)

#### [The upper saturation spectrum of Berge triangles in triple systems](papers/mathematics/berge-triangle-spectrum/manuscript.pdf)

**Family:** `berge-triangle-spectrum`.

For every n ≥ 8, a Berge-triangle-free triple system on n vertices with more than ⌊(n−1)²/8⌋ edges lies inside a paired product F(n,p): p disjoint pairs, the other n − 2p vertices, and all triples formed by one pair and one other vertex. Saturated systems above this threshold are therefore paired products, and the saturation spectrum there consists exactly of the sizes p(n − 2p) up to Győri's maximum ⌊n²/8⌋. The threshold is sharp, since a saturated system with exactly ⌊(n−1)²/8⌋ edges that is not a paired product exists for every n ≥ 8. About n/4 sizes lie in the window and n/4 − O(√n) of them are missing, so the missing sizes near the top are not finitely many uniformly in n.

**Formal scope.** Lean 4.35.0 proves that paired products are Berge-triangle-free and saturated with p(n−2p) edges, that for every n ≥ 8 the explicit system J(⌊n/4⌋, n−2⌊n/4⌋) is saturated, is not a paired product and has exactly ⌊(n−1)²/8⌋ edges, and the arithmetic of the window, including the explicit deficits and at least ⌊n/4⌋ − ⌊√(2n)⌋/2 − 1 sizes there that are not of the form p(n−2p). It derives the upper spectrum and the maximum ⌊(n−1)²/8⌋ for saturated nonproducts from the containment theorem, which enters as a hypothesis and has a conventional proof, checked computationally for small orders.

**Prior work.** [Bushaw, English, Heath, Johnston and Rombach, 2025.](https://arxiv.org/abs/2502.17686) · [Frankl, Füredi, Goorevitch, Holzman and Simonyi, 2026.](https://doi.org/10.37236/14115)

[Paper PDF](papers/mathematics/berge-triangle-spectrum/manuscript.pdf) · [LaTeX](papers/mathematics/berge-triangle-spectrum/manuscript.tex) · [Proof and reproduction](papers/mathematics/berge-triangle-spectrum/README.md) · [Citation](papers/mathematics/berge-triangle-spectrum/CITATION.bib)
#### [Exact three-uniform Berge-path saturation numbers and a counterexample to a conjectured formula](papers/mathematics/berge-path-saturation/manuscript.pdf)

**Family:** `berge-path-saturation`.

English, Graber, Kirkpatrick, Methuku and Sullivan conjectured that the three-uniform Berge-P_m saturation number is ⌈(n − ⌊n/b⌋)/2⌉ for all m ≥ 10 and n ≥ b = 2a_m + 1. Two disjoint loose 8-cycles with two isolated vertices form a Berge-P₁₀-saturated hypergraph on 34 vertices with 16 hyperedges, one below the conjectured 17. The preprint determines the saturation number on the whole conjectured range: it is one less than the conjectured value exactly when b < n < 2b and n ≡ 2 (mod 2(m − 2)), and the extremal hypergraph at those orders is unique.

**Formal scope.** Lean 4.35.0 proves, for actual three-uniform hypergraphs, Berge paths and saturation under every absent triple, that t disjoint loose d-cycles with two isolated vertices are Berge-P_{d+2}-saturated for every d ≥ 3, that the explicit 34-vertex hypergraph is Berge-P₁₀-saturated with 16 hyperedges, and that the three-uniform case of the conjecture fails for every m ≥ 10. The matching lower bound, the exact formula and the uniqueness of extremal hypergraphs have conventional proofs that use two results of the source paper.

**Prior work.** [English, Graber, Kirkpatrick, Methuku and Sullivan, arXiv:1710.03735v1, Conjecture 2.4.](https://arxiv.org/abs/1710.03735v1)

[Paper PDF](papers/mathematics/berge-path-saturation/manuscript.pdf) · [LaTeX](papers/mathematics/berge-path-saturation/manuscript.tex) · [Proof and reproduction](papers/mathematics/berge-path-saturation/README.md) · [Citation](papers/mathematics/berge-path-saturation/CITATION.bib)

#### [Three-uniform Berge-C₄ saturation: linear bounds with coefficients 5/8 and 3/4, the cone spectrum and exact small values](papers/mathematics/berge-c4-saturation/manuscript.pdf)

**Family:** `berge-c4-saturation`.

The three-uniform Berge-C₄ saturation number s(n), in which any absent triple may be added, satisfies max(⌈(n − 1)/2⌉, ⌈(5n − 3623)/8⌉, ⌈(5n + 89)/8 − √(270n + 1891)/4⌉) ≤ s(n) ≤ ⌈(3n − 9)/4⌉ for every n ≥ 9, so 5/8 ≤ liminf s(n)/n ≤ limsup s(n)/n ≤ 3/4; the previous explicit upper bound was n − 2. The preprint classifies the saturated cones for n ≥ 5, whose sizes are exactly the integers from ⌈(3n − 5)/4⌉ to n − 2 together with n − 1 when n ≡ 1 (mod 3), proves that a vertex reached from every other vertex by paths of lengths one and two forces 3(n − 1)/4 hyperedges, and gives s(n) for n ≤ 13 from exhaustive certificates.

**Formal scope.** Lean 4.35.0 proves, for actual three-uniform hypergraphs, Berge-C₄s with distinct vertices and hyperedges, and saturation under every absent triple, that a saturated hypergraph with ⌈(3n − 9)/4⌉ hyperedges exists for every n ≥ 9, together with the exact values for n ≤ 5. The lower bound, the cone results and the flexible-root theorem are conventional; the values for 6 ≤ n ≤ 13 rest on certificates checked by an independent C++ verifier.

**Prior work.** [English, Graber, Kirkpatrick, Methuku and Sullivan, arXiv:1710.03735v1, Theorem 5.7.](https://arxiv.org/abs/1710.03735v1) · [English, Gerbner, Methuku and Tait, 2019.](https://arxiv.org/abs/1807.06947)

[Paper PDF](papers/mathematics/berge-c4-saturation/manuscript.pdf) · [LaTeX](papers/mathematics/berge-c4-saturation/manuscript.tex) · [Proof and reproduction](papers/mathematics/berge-c4-saturation/README.md) · [Citation](papers/mathematics/berge-c4-saturation/CITATION.bib)

#### [Three-uniform Berge-C₅ saturation: a two-thirds upper bound, the cone spectrum and exact small values](papers/mathematics/berge-c5-saturation/manuscript.pdf)

**Family:** `berge-c5-saturation`.

For every n ≥ 47 every integer from ⌈(2n − 8)/3⌉ to n − 2 is the size of a three-uniform Berge-C₅-saturated hypergraph on n vertices, in which any absent triple may be added, so s(n) = sat₃(n, Berge-C₅) ≤ ⌈(2n − 8)/3⌉; the previous explicit upper bound had leading coefficient 4/3, and the simplest new construction glues seven-vertex blocks with four hyperedges at one vertex. No lower bound beyond small orders is proved. The preprint classifies the saturated cones for n ≥ 5, whose sizes are exactly the integers from ⌈6(n − 1)/7⌉ to n − 2 together with n − 1 when 4 divides n − 1 (for n ≥ 8), characterises the saturated loose expansions of bipartite graphs with a degree-two side, and gives s(n) for n ≤ 11 from exhaustive certificates.

**Formal scope.** Lean 4.35.0 proves, for actual three-uniform hypergraphs, Berge-C₅s with distinct vertices and hyperedges, and saturation under every absent triple, that every size from ⌈2(n − 1)/3⌉ to n − 2 is realized for n ≥ 14, that s(n) ≤ ⌈2(n − 1)/3⌉ for n ≥ 7, and the exact values for n ≤ 7. The two lowest endpoints for n ≥ 47, the cone classification and the expansion theorems are conventional, with exhaustive construction checks; the values for 8 ≤ n ≤ 11 rest on certificates checked by an independent C++ verifier.

**Prior work.** [English, Graber, Kirkpatrick, Methuku and Sullivan, arXiv:1710.03735v1, Theorem 5.7(2).](https://arxiv.org/abs/1710.03735v1) · [English, Gerbner, Methuku and Tait, 2019.](https://arxiv.org/abs/1807.06947)

[Paper PDF](papers/mathematics/berge-c5-saturation/manuscript.pdf) · [LaTeX](papers/mathematics/berge-c5-saturation/manuscript.tex) · [Proof and reproduction](papers/mathematics/berge-c5-saturation/README.md) · [Citation](papers/mathematics/berge-c5-saturation/CITATION.bib)

### Inequalities and real analysis

#### [Diagonal concavity does not imply concavity for sums of elementary symmetric polynomials](papers/mathematics/diagonal-concavity/paper.pdf)

**Family:** `diagonal-concavity`. **Result:** Counterexample and complete parameter classification.

**Abstract.** For positive M, let f=1+Mσ₁+σ₂+Mσ₃+σ₄ in four variables. Its fourth root is concave on the positive diagonal exactly when M≥1. It is concave on the full positive orthant exactly when M=1. Every M>1 therefore disproves Lachaume’s diagonal criterion with strictly positive coefficients.

**Original problem.** [Lachaume, arXiv:1712.10327v1, Conjecture 1.](https://arxiv.org/abs/1712.10327v1)

[Paper PDF](papers/mathematics/diagonal-concavity/paper.pdf) · [LaTeX](papers/mathematics/diagonal-concavity/paper.tex) · [Bibliography](papers/mathematics/diagonal-concavity/references.bib) · [Citation](papers/mathematics/diagonal-concavity/citation.bib) · [Formal statement and prior work](lean/docs/mathematics/diagonal-concavity.md) · [Reproduction](papers/mathematics/diagonal-concavity/verification/README.md)

### Integer sequences and combinatorics

#### Alternating Motzkin sums

**Family:** `alternating-motzkin`. The principal root bound and bounded-forcing companion belong to one sequence family.

##### [Sharp root log-concavity of alternating Motzkin sums](papers/mathematics/motzkin/paper.pdf)

**Result:** Conjecture resolution with an optimal threshold.

**Abstract.** Let Tₙ be the alternating sum of Motzkin numbers through index n. The sequence Tₙ^(1/n) is strictly log-concave on its tail starting at five. The inequality reverses at center five, so no earlier tail is log-concave. This strengthens Zhao’s proposed tail starting at nine. The source recurrence and finite sum are linked in Lean.

**Original problem.** [Zhao, INTEGERS 26 (2026), A55, Conjecture 1; OEIS A187306.](https://math.colgate.edu/~integers/aa55/aa55.pdf)

[Paper PDF](papers/mathematics/motzkin/paper.pdf) · [LaTeX](papers/mathematics/motzkin/paper.tex) · [Bibliography](papers/mathematics/motzkin/references.bib) · [Citation](papers/mathematics/motzkin/citation.bib) · [Formal statement and prior work](lean/docs/mathematics/motzkin.md) · [Reproduction](papers/mathematics/motzkin/verification/README.md)

##### [Sharp log-concavity for alternating Motzkin sums](papers/mathematics/motzkin/bounded-forcing/manuscript.pdf)

A robust bounded-forcing recurrence theorem and corrected scaled corollary, with applications to alternating Motzkin-type sums.

**Formal scope.** The arbitrary-real recurrence theorem and scaled corollary, including zero forcing, are formalized. Concrete sequences, uniform-family applications, root transfer and threshold classification retain conventional proofs.

[Paper PDF](papers/mathematics/motzkin/bounded-forcing/manuscript.pdf) · [LaTeX](papers/mathematics/motzkin/bounded-forcing/manuscript.tex) · [Reproduction and source context](papers/mathematics/motzkin/bounded-forcing/README.md) · [Citation](papers/mathematics/motzkin/bounded-forcing/CITATION.bib)

#### [Counterexamples to a late-iterate ordering conjecture for generalized Hofstadter functions](papers/mathematics/hofstadter-iteration/paper.pdf)

**Family:** `hofstadter-iteration`. **Result:** Counterexamples for every parameter k≥4.

**Abstract.** For every k≥4, some input n satisfies Fₖ^(2k+1)(n)>Fₖ₊₁^(2k+2)(n). The proof constructs inverse iterates whose exact gap is k−3. The finite witness F₄⁹(132)=8>7=F₅¹⁰(132) gives the first instance. The result concerns infinitely many parameters, not infinitely many violating inputs for each fixed parameter.

**Original problem.** [Letouzey, Li, and Steiner, Journal of Integer Sequences 29 (2026), 26.3.3, conjecture before Lemma 7.6.](https://cs.uwaterloo.ca/journals/JIS/VOL29/Letouzey/letouzey3.pdf)

[Paper PDF](papers/mathematics/hofstadter-iteration/paper.pdf) · [LaTeX](papers/mathematics/hofstadter-iteration/paper.tex) · [Bibliography](papers/mathematics/hofstadter-iteration/references.bib) · [Citation](papers/mathematics/hofstadter-iteration/citation.bib) · [Formal statement and prior work](lean/docs/mathematics/hofstadter-iteration.md) · [Reproduction](papers/mathematics/hofstadter-iteration/verification/README.md)

#### [A positive constant-recursive sequence with nonquasipolynomial power ranks](papers/mathematics/power-rank/manuscript.pdf)

**Family:** `power-rank`.

Exact minimal recurrences for every power of a rank-thirteen sequence, nonquasipolynomial ranks, and infinitely many power-rank profiles at each rank at least three.

**Formal scope.** The main and arbitrary-rank companion theorems are formalized. Generating-function and polynomial corollaries retain conventional proofs.

**Priority and subsequent correspondence.** On 29 October 2026, through correspondence with Professor Eric Rowland, I learned that he had independently obtained an infinite family of rank sequences for rank-three recurrences while experimenting with an LLM. The constructions have not been compared. [Priority and novelty record](PRIORITY_AND_NOVELTY.md#power-ranks-of-a-constant-recursive-sequence).

[Paper PDF](papers/mathematics/power-rank/manuscript.pdf) · [LaTeX](papers/mathematics/power-rank/manuscript.tex) · [Reproduction and source context](papers/mathematics/power-rank/README.md) · [Citation](papers/mathematics/power-rank/CITATION.bib)

#### [Order-polynomial positivity for width-two posets with a chain of at most five elements](papers/mathematics/width-two-order-polynomial/manuscript.pdf)

**Family:** `width-two-order-polynomial`.

For every finite poset P that is the union of two chains A and B with |A| ≤ 5, the chain B being arbitrarily long and the comparabilities between the chains arbitrary, every coefficient of |P|! Ω_P(t) is a nonnegative integer, where Ω_P is the order polynomial; this is a case of Conjecture 7.1 of Ferroni, Morales and Panova. The linear coefficient is at least (a − 1)!(b − 1)! m/(a + b)!, with m the number of elements of B comparable with some element of A, so it is positive exactly when the comparability graph is connected. The proof reduces the linear coefficient on each of 64 chambers to a polynomial in the gaps between boundaries, certified nonnegative by exact square certificates and 194,112 point identities, and lifts it to all coefficients by the ideal–filter reduction of Ferroni, Morales and Panova.

**Formal scope.** Lean 4.35.0 checks the square certificates and proves nonnegativity and the linear lower bound for the 22 chamber polynomials with a short chain of size at most four. The link between the chamber polynomials and the order polynomial, the size-five chambers and the reduction to the linear coefficient have conventional proofs or certificates checked by an independent program.

**Prior work.** [Ferroni, Morales and Panova, arXiv:2503.16403v3, Conjecture 7.1.](https://arxiv.org/abs/2503.16403v3) · [Alexandersson and Jal, arXiv:2410.00127v3.](https://arxiv.org/abs/2410.00127v3) Public partial results on the same conjecture, for ordinal sums of one- and two-element antichains ([10m-u/open-problems-catalog](https://github.com/10m-u/open-problems-catalog/tree/ca8d4d44ba3db527f19f28928c240168f545ecfe)) and for single cross-link factors ([chris-hadad/lr-stretching-results](https://github.com/chris-hadad/lr-stretching-results/blob/0677a8b4bda0db770ad690824c236222783eeb95/results/overlap-families/proofs/A58-COUPLED-PROOF.md)), cover classes that neither contain nor are contained in this one.

[Paper PDF](papers/mathematics/width-two-order-polynomial/manuscript.pdf) · [LaTeX](papers/mathematics/width-two-order-polynomial/manuscript.tex) · [Proof and reproduction](papers/mathematics/width-two-order-polynomial/README.md) · [Citation](papers/mathematics/width-two-order-polynomial/CITATION.bib)
### Finite geometry

#### [Blocking sets of PG(2,13) invariant under a fixed-point-free Singer subgroup meet some line in five points](papers/mathematics/singer-orbit-blocking/manuscript.pdf)

**Family:** `singer-orbit-blocking`.

Let H be the subgroup of order three of a Singer cycle group of PG(2,13); it fixes no point. Every H-invariant blocking set of PG(2,13) meets some line in at least five points, and the 21-point blocking set of Blokhuis, Brouwer and Wilbrink, invariant under a conjugate of H, meets every line in at most five points. So five is the least possible largest line intersection of an H-invariant blocking set, for every fixed-point-free collineation of order three. This settles a symmetric case of the plane of order 13 in Erdős Problem 1159; blocking sets without this symmetry are not covered.

**Formal scope.** Lean 4.35.0 models PG(2,13) with Mathlib's projectivization of F₁₃³ and proves the order of the Singer cycle, the fixed-point-free subgroup, the 21-point witness, the reduction to 61 orbit conditions and the nonexistence of a solution with intersections at most four, by a kernel-checked search with a soundness proof. The conjugacy of all fixed-point-free subgroups of order three is conventional.

**Prior work.** [Erdős Problem #1159.](https://www.erdosproblems.com/1159) · [Blokhuis, Brouwer and Wilbrink, 2003.](https://doi.org/10.1515/advg.2003.2003.s1.245)

[Paper PDF](papers/mathematics/singer-orbit-blocking/manuscript.pdf) · [LaTeX](papers/mathematics/singer-orbit-blocking/manuscript.tex) · [Proof and reproduction](papers/mathematics/singer-orbit-blocking/README.md) · [Citation](papers/mathematics/singer-orbit-blocking/CITATION.bib)

### Quadratic forms and number theory

#### [A rank bound for represented totally positive unit squareclasses](papers/mathematics/unit-squareclasses/manuscript.pdf)

**Family:** `unit-squareclasses`.

Let K be a totally real algebraic field, possibly of infinite degree, and L a totally positive definite quadratic lattice over its ring of integers with Q(L) ⊆ O_K, not necessarily classical. Then every family of pairwise distinct classes of totally positive units modulo squares of units represented by L has at most rank L members, and the bound is attained when the field has enough classes. This answers negatively Question 3.4 of Daans, Kala, Man, Widmer and Yatsyna, who proved the bound 2n − 2 and asked whether n + 1 classes can occur. The bound is a short consequence of standard facts on finite reflection groups: unit-valued vectors give integral reflections, and conjugate reflections carry the same unit class. As a corollary, a universal lattice has rank at least the number of totally positive unit classes.

**Formal scope.** The bound for every algebraic totally real field, including infinite extensions, every O_K-submodule with integral norms in a finite-dimensional totally positive definite space, and actual units of the ring of integers is formalized in 11 Lean modules. The derivation from finite reflection groups, sharpness and the universality corollary are conventional.

[Paper PDF](papers/mathematics/unit-squareclasses/manuscript.pdf) · [LaTeX](papers/mathematics/unit-squareclasses/manuscript.tex) · [Proof and reproduction](papers/mathematics/unit-squareclasses/README.md) · [Citation](papers/mathematics/unit-squareclasses/CITATION.bib)

### Valuation theory

#### [Depth-one Artin–Schreier defect towers are composita](papers/mathematics/artin-schreier-depth/manuscript.pdf)

**Family:** `artin-schreier-depth`.

Let k be algebraically closed of characteristic p > 0 and K a perfect henselian subfield of the Hahn field k((y^ℚ)) that contains k(y) and whose elements have no finite accumulation points in their supports. If a nontrivial finite Artin–Schreier tower M/K has depth one, then M is a compositum of Artin–Schreier extensions of K. Nart and Novacoski proved the reverse implication and conjectured this one. For every θ in M outside K, the truncation of θ at the first finite accumulation point of its support generates a nontrivial elementary abelian subextension of K(θ)/K; the extraction adapts an Ore-relation argument of Kedlaya.

**Formal scope.** Both implications are formalized in two Lean projects. The Lean 4.35 project states the conjecture for every finite Artin–Schreier tower over a base whose valuation ring is henselian in Mathlib's sense, with depth one defined as the least length of a complete Mac Lane–Vaquié chain over all primitive generators; it compares these chains with Okutsu sequences at length one only. The Lean 4.19 project states depth one through Okutsu sequences in the algebraic closure of K inside the Hahn field.

**Prior work.** [Nart and Novacoski, 2026.](https://doi.org/10.1016/j.jpaa.2026.108184)

[Paper PDF](papers/mathematics/artin-schreier-depth/manuscript.pdf) · [LaTeX](papers/mathematics/artin-schreier-depth/manuscript.tex) · [Proof and reproduction](papers/mathematics/artin-schreier-depth/README.md) · [Citation](papers/mathematics/artin-schreier-depth/CITATION.bib)

### Discrete analysis, tilings, probability and entropy

#### [The sharp level-one Fourier weight at density one eighth](papers/mathematics/sharp-eighth/manuscript.pdf)

**Family:** `sharp-eighth`.

For every Boolean indicator of mean 1/8 on a finite uniform cube, the level-one Fourier weight is at most 3/64. A codimension-three subcube attains the bound in every dimension at least three.

**Formal scope.** The formal proof includes arbitrary dimensions, the exact moment identities, the Hamming-distance bound, and sharpness witnesses.

**Prior work.** [Yu, On Average Distance, Level-1 Fourier Weight, and Chang’s Lemma, 2026 revision.](https://arxiv.org/abs/2504.02593v2)

**Priority and subsequent correspondence.** On 30 October 2026, Professor Lei Yu informed me that Yijia Fang and Hao Huang had already proved this bound, with the equality cases, in a manuscript shared privately about a month earlier and submitted to arXiv on 29 October 2026 ([arXiv:2610.40486](https://arxiv.org/abs/2610.40486)). I make no originality or priority claim for the bound. [Priority and novelty record](PRIORITY_AND_NOVELTY.md#sharp-level-one-fourier-weight-at-density-one-eighth).

[Paper PDF](papers/mathematics/sharp-eighth/manuscript.pdf) · [LaTeX](papers/mathematics/sharp-eighth/manuscript.tex) · [Citation](papers/mathematics/sharp-eighth/CITATION.bib) · [Reproduction](papers/mathematics/sharp-eighth/README.md)

#### [A quartic entropy deficit for random rankings](papers/mathematics/quartic-rankings/manuscript.pdf)

**Family:** `quartic-rankings`.

A distribution on rankings of n labels has entropy at most (1 − ε⁴/144) log(n!) if every pairwise comparison has probability at distance at least ε > 0 from 1/2.

The proof includes all finite sizes and actual position-valued permutations. It assumes neither independent comparisons nor transitive preferred directions.

[Paper](papers/mathematics/quartic-rankings/manuscript.pdf) · [Source](papers/mathematics/quartic-rankings/manuscript.tex) · [Citation](papers/mathematics/quartic-rankings/CITATION.bib) · [Proof and verification](papers/mathematics/quartic-rankings/README.md)

#### [Sharp universal Rényi threshold for iid sums on finite Sidon sets](papers/mathematics/sidon-renyi/manuscript.pdf)

**Family:** `sidon-renyi`.

A sharp universal Renyi-order threshold for iid sums supported on finite strong-B2 sets.

**Formal scope.** The finite-support iid theorem, zero probabilities and critical endpoint are formalized. Comparison with unverified source definitions is conditional.

[Paper PDF](papers/mathematics/sidon-renyi/manuscript.pdf) · [LaTeX](papers/mathematics/sidon-renyi/manuscript.tex) · [Reproduction and source context](papers/mathematics/sidon-renyi/README.md) · [Citation](papers/mathematics/sidon-renyi/CITATION.bib)

#### [A 64-point spectral tile in F₂⁹ with no periodic complement](papers/mathematics/binary-spectral-tile/manuscript.pdf)

**Family:** `binary-spectral-tile`.

An explicit 64-point set E ⊂ F₂⁹ is spectral and tiles by translation, but has no periodic tiling complement: its complements are exactly the 512 translates of one aperiodic eight-point set. In particular no linear subspace complements E, and F₂⁹ fails the periodic tiling property of Fan and Zhang. The construction places eight three-dimensional subspaces in parallel six-dimensional fibres; the shifts disjoint from E are the 28 pair sums of an affine eight-circuit, which form the line graph of K₈ and contain no three-dimensional subspace. This answers negatively the stronger subspace-complement part of Question 8.1 of Ferguson and Iosevich and its equivalent Question 8.2. Whether every spectral 64-point subset of F₂⁹ tiles remains open.

**Formal scope.** Spectrality with an actual basis of all complex functions on E, the tiling E ⊕ T = F₂⁹, aperiodicity of E, the exclusion of every periodic and every subspace complement, the classification of all complements as the 512 translates of T, and the failure of the periodic tiling property for F₂⁹ are formalized in 16 Lean modules. Minimality of dimension nine depends on an external dimension-eight theorem and is not formalized.

**Priority and subsequent correspondence.** On 30 October 2026, through correspondence with Dr. Samuel Ferguson, I learned that he and Professor Joshua Iosevich had become aware of counterexamples to the stronger statement shortly after submitting their arXiv paper. Whether their examples are equivalent to this construction has not been established; an AI-generated comparison he shared later that day provisionally suggests that they are not affinely equivalent, but it has not been verified. [Priority and novelty record](PRIORITY_AND_NOVELTY.md#binary-spectral-tile-in-dimension-nine).

[Paper PDF](papers/mathematics/binary-spectral-tile/manuscript.pdf) · [LaTeX](papers/mathematics/binary-spectral-tile/manuscript.tex) · [Proof and reproduction](papers/mathematics/binary-spectral-tile/README.md) · [Citation](papers/mathematics/binary-spectral-tile/CITATION.bib)

#### [The small-coefficient upper half of the Keller–Klein conjecture](papers/mathematics/keller-klein/manuscript.pdf)

**Family:** `keller-klein`.

Let X = Σ vᵢεᵢ with independent uniform signs, real coefficients, Σ vᵢ² = 1 and |vᵢ| ≤ a, where 0 < a ≤ 7/100. For every x ≥ 0, P(|X| ≤ x) ≤ 2Φ(x) + 2Φ(a) − 2, equivalently P(X ≤ x) − Φ(x) ≤ Φ(a) − 1/2. Keller and Klein conjectured the two-sided bound |P(X ≤ x) − Φ(x)| ≤ Φ(a₁) − 1/2 with a₁ the largest coefficient; Ivanisvili's computer-assisted manuscript of 21 October 2026 proves the lower half and the full conjecture for a₁ ≥ 0.07, and leaves this range open. The proof follows the analytic route his manuscript proposes, using Prawitz smoothing, coefficient profiles and a compensated alias estimate. Together with his results it implies the full conjecture, conditionally on those unrefereed external results.

**Formal scope.** The theorem for every finite vector of real coefficients, with the exact count of sign vectors and Mathlib's standard normal distribution function, is formalized in 62 Lean modules, including Prawitz smoothing, the characteristic-function envelopes and both analytic zones. Ivanisvili's Theorems 1.1 and 10.9, needed for the full conjecture, are external computer-assisted results and are not formalized.

[Paper PDF](papers/mathematics/keller-klein/manuscript.pdf) · [LaTeX](papers/mathematics/keller-klein/manuscript.tex) · [Proof and reproduction](papers/mathematics/keller-klein/README.md) · [Citation](papers/mathematics/keller-klein/CITATION.bib)

#### [Structural selfadhesivity does not imply a numerically selfadhesive realization](papers/mathematics/structural-selfadhesivity/manuscript.pdf)

**Family:** `structural-selfadhesivity`.

An explicit conditional-independence model on five variables, with 26 of the 80 elementary statements, admits for every overlap an adhesive polymatroid gluing whose two restrictions both induce it, yet no real polymatroid inducing it is selfadhesive in Matúš's numerical sense. This answers negatively Question 4.18 of Boege, who asked whether every structurally selfadhesive structural semigraphoid is induced by a selfadhesive polymatroid; his computation gave a positive answer for four variables. The positive part is certified by 32 integer polymatroids, the negative part by an exact identity among 51 nonnegative conditional mutual informations valid for every real inducing profile.

**Formal scope.** Both parts are formalized in Lean for arbitrary real polymatroids, with actual subset and relabeling semantics, all 32 overlap witnesses and the exact separating identity. The minimality suggested by Boege's four-variable computation is a literature consequence and is not formalized.

**Prior work.** [Boege, 2023.](https://doi.org/10.1016/j.ijar.2023.109027)

[Paper PDF](papers/mathematics/structural-selfadhesivity/manuscript.pdf) · [LaTeX](papers/mathematics/structural-selfadhesivity/manuscript.tex) · [Proof and reproduction](papers/mathematics/structural-selfadhesivity/README.md) · [Citation](papers/mathematics/structural-selfadhesivity/CITATION.bib)

### Matroid theory

#### [The exact asymmetric Merino–Welsh region for finite matroids](papers/mathematics/asymmetric-tutte/manuscript.pdf)

**Family:** `asymmetric-tutte`.

The theorem characterizes all nonnegative pairs (x,y) for which T_M(x,0) T_M(0,y) ≥ T_M(1,1)² holds for every finite matroid without loops or coloops.

**Formal scope.** The statement uses actual Mathlib matroids and the literal subset rank sum. It includes empty ground sets and finite ground sets in arbitrary ambient types.

**Prior work.** [Liu, 2026; Chen and Xie, 2026. The manuscript states the relation to the diagonal theorem.](https://github.com/michaeliu4/tutte-threshold)

[Paper PDF](papers/mathematics/asymmetric-tutte/manuscript.pdf) · [LaTeX](papers/mathematics/asymmetric-tutte/manuscript.tex) · [Citation](papers/mathematics/asymmetric-tutte/CITATION.bib) · [Reproduction](papers/mathematics/asymmetric-tutte/README.md)

### Optimization

#### [A rational five-cycle for two-block ADMM with multiplier step below two](papers/mathematics/admm-counterexample/paper/admm_counterexample.pdf)

**Family:** `admm-counterexample`.

An exact period-five orbit for multiplier-only two-block ADMM at step 199/100.

**Formal scope.** Seven modules and eleven endpoint audits cover the orbit, minimizers and optimizer. Analytic regularity of the finite strongly convex extension retains a conventional proof.

[Paper PDF](papers/mathematics/admm-counterexample/paper/admm_counterexample.pdf) · [LaTeX](papers/mathematics/admm-counterexample/paper/admm_counterexample.tex) · [Reproduction and source context](papers/mathematics/admm-counterexample/README.md) · [Citation](papers/mathematics/admm-counterexample/CITATION.bib)

#### [A narrow interval for the universal multiplier step of two-block ADMM](papers/mathematics/admm-multiplier-step/manuscript.pdf)

**Family:** `admm-multiplier-step`.

Two-block ADMM with relaxation only in the multiplier update converges for every constant step 0 < τ ≤ 1.886795 on finite-dimensional convex problems whose proximal subproblems attain their minima and which have a saddle point. Both primal blocks, the multiplier and the objective values converge, with no smoothness, strong convexity or bounded-iterate assumption. Fixed compact polytopes in R¹²⁸ have a nonconstant periodic ADMM orbit for every τ ≥ 1.8868840…, so the largest step with universal convergence lies in an interval of width below 0.00009, about a tenth of the version 1.0 interval. For scalar problems the universal range is exactly 0 < τ < 2. Affine-constraint versions are also proved. The earlier assertion of convergence up to τ = 2 by Gao et al. (2022) is shown to be false.

**Formal scope.** The consensus convergence theorem for 0 < τ ≤ 377359/200000, the arbitrary-rank and full-rank affine-constraint theorems, all seven finite-memory interval certificates and the periodic orbit in R^128 for τ ≥ 1.8868840… are formalized in 301 Lean modules. The scalar theorem, individual objective-value limits, the reduction from proper closed convex functions to proximal attainment, and penalty rescaling are conventional.

[Paper PDF](papers/mathematics/admm-multiplier-step/manuscript.pdf) · [LaTeX](papers/mathematics/admm-multiplier-step/manuscript.tex) · [Proof and reproduction](papers/mathematics/admm-multiplier-step/README.md) · [Citation](papers/mathematics/admm-multiplier-step/CITATION.bib)

#### [Escaping Nesterov flows and iterates below critical damping](papers/mathematics/nesterov-subcritical/manuscript.pdf)

**Family:** `nesterov-subcritical`.

For zero-velocity solutions of X″ + (r/t)X′ + ∇F(X) = 0 and for the Nesterov iteration with momentum k/(k+r), with F convex, its gradient 1-Lipschitz and its minimum attained, boundedness holds for r ≥ 3. On the Hilbert space ℓ²(ℕ;ℝ²) this threshold is sharp for both: for every 0 < r < 3 an explicit block sum of smoothed valleys has a trajectory, and another has iterates, with norms tending to infinity. In the plane, the potential h(√(x²+y²)) − x with the Huber function h has an escaping trajectory from (2,1) for every 0 < r ≤ 2 and bounded trajectories for r > 2. The finite-dimensional range 2 < r < 3 is open.

**Formal scope.** The continuous-time Hilbert-space threshold, the discrete threshold and the planar escape for 1 < r ≤ 2, including actual gradients, global solutions from rest and norm divergence, are formalized. The planar escape of the same potential for 0 < r ≤ 1, its boundedness for r > 2 and existence of solutions for r ≤ 1 are conventional.

[Paper PDF](papers/mathematics/nesterov-subcritical/manuscript.pdf) · [LaTeX](papers/mathematics/nesterov-subcritical/manuscript.tex) · [Proof and reproduction](papers/mathematics/nesterov-subcritical/README.md) · [Citation](papers/mathematics/nesterov-subcritical/CITATION.bib)

#### [Periodic obstructions to small-extrapolation Chambolle–Pock](papers/mathematics/chambolle-pock-cycles/manuscript.pdf)

**Family:** `chambolle-pock-cycles`.

For the unmodified primal-first Chambolle–Pock iteration with extrapolation θ and step product κ = τσ‖L‖², every κ > 2 admits fixed compact polytopes in R⁴ whose iteration cycles without converging for all sufficiently small θ ≥ 0. Any universal sufficient condition κ < c(θ) therefore satisfies limsup c(θ) ≤ 2 as θ ↓ 0, while bilinear and quadratic problems allow κ < 4/(1+2θ). A nonconstant three-cycle of actual proximal updates exists exactly when κ²(1+θ)² − 2κ(1+3θ) − 3 ≥ 0, attained by compact triangles, and a rational seven-cycle has an open set of nonconvergent starting points. The obstructing θ-intervals are very small and the bound two is not shown to be sharp.

**Formal scope.** The universal three-cycle threshold and its attainment, the seven-cycle with its open basin, the four-dimensional family for every κ > 2 and the quadratic eigenmode comparison are formalized in 21 Lean modules. The limsup consequence, numerical observations of larger θ-intervals and basin sizes, and the finite-dimensional matrix-convergence bridge are conventional or observational.

[Paper PDF](papers/mathematics/chambolle-pock-cycles/manuscript.pdf) · [LaTeX](papers/mathematics/chambolle-pock-cycles/manuscript.tex) · [Proof and reproduction](papers/mathematics/chambolle-pock-cycles/README.md) · [Citation](papers/mathematics/chambolle-pock-cycles/CITATION.bib)

#### [The multi-marginal converse of Minty's theorem fails in the plane](papers/mathematics/multimarginal-minty/manuscript.pdf)

**Family:** `multimarginal-minty`.

Bartz, Bauschke, Phan and Wang asked whether the converse half of Minty's theorem extends to several marginals: does maximal c-monotonicity for the cost Σ⟨xᵢ, xⱼ⟩ force the sum image to be the whole space? For three marginals on ℝ², three integer points form a c-monotone set to which no tuple with sum zero can be added, because four compatibility inequalities have a positive weighted sum equal to a sum of squares plus 23/26. Every maximal extension, which exists by Zorn's lemma, therefore has a sum image that omits the origin and is not convex.

**Formal scope.** The whole argument is formalized in Lean for the actual two-point swap condition and maximality among all subsets of (ℝ²)³: the finite obstruction over arbitrary real tuples, the Zorn extension and the nonconvexity of the sum image. The reformulation through firmly nonexpansive maps is proved in the text only.

**Prior work.** [Bartz, Bauschke, Phan and Wang, 2021.](https://doi.org/10.1007/s10107-019-01433-9)

[Paper PDF](papers/mathematics/multimarginal-minty/manuscript.pdf) · [LaTeX](papers/mathematics/multimarginal-minty/manuscript.tex) · [Proof and reproduction](papers/mathematics/multimarginal-minty/README.md) · [Citation](papers/mathematics/multimarginal-minty/CITATION.bib)

#### [The exact last-gradient bound for constant-step gradient descent in the strongly convex case](papers/mathematics/strong-gradient/manuscript.pdf)

**Family:** `strong-gradient`.

The exact final-gradient guarantee holds on every real Hilbert space for L > 0, 0 ≤ μ ≤ L, normalized step 0 ≤ h ≤ 2 and every natural horizon. Actual one-dimensional Huber and quadratic functions attain its two branches.

**Formal scope.** The actual-function upper bound and normalized actual-function attainment are formalized, including every horizon and closed parameter boundary. Sharpness for arbitrary L > 0 and radius R > 0 is proved by rescaling in the manuscript, without a separate Lean wrapper.

[Paper PDF](papers/mathematics/strong-gradient/manuscript.pdf) · [LaTeX](papers/mathematics/strong-gradient/manuscript.tex) · [Citation](papers/mathematics/strong-gradient/CITATION.bib) · [Proof and reproduction](papers/mathematics/strong-gradient/README.md)

## Theoretical computer science

### Sampling algorithms and information theory

#### [Critical hard-core influence bounds via nonbacktracking collisions](papers/theoretical-computer-science/critical-hardcore/manuscript.pdf)

**Family:** `critical-hardcore`.

For each fixed Δ ≥ 3, every row of the hard-core influence matrix has absolute sum O_Δ(√n log n) on every n-vertex graph of maximum degree at most Δ, at every activity up to the uniqueness threshold λ_c(Δ) and under every feasible pinning, with an explicit constant. The proof combines exact vertex-deletion identities, a known local squared-message contraction, a self-avoiding-walk transfer in the style of Sinclair, Srivastava, Štefankovič and Yin, and a finite form of the nonbacktracking collision argument of Bencs et al. It recovers, up to a logarithm, an O(√n) bound that was stated in 2025 and withdrawn in 2026. The constant is large, and the mixing-time consequence for Glauber dynamics is conditional on a published proposition.

**Formal scope.** The influence bound for the actual hard-core Gibbs measure on every finite simple graph of maximum degree at most Δ, all activities up to λ_c(Δ) and all feasible pinnings is formalized in 32 Lean modules, including the regular completion and the nonbacktracking collision estimate. The Glauber-dynamics mixing corollary and the numerical observations on the constant are not formalized.

[Paper PDF](papers/theoretical-computer-science/critical-hardcore/manuscript.pdf) · [LaTeX](papers/theoretical-computer-science/critical-hardcore/manuscript.tex) · [Proof and reproduction](papers/theoretical-computer-science/critical-hardcore/README.md) · [Citation](papers/theoretical-computer-science/critical-hardcore/CITATION.bib)

#### [Counterexamples to a best-of-n win-rate bound at every budget](papers/theoretical-computer-science/best-of-n/paper.pdf)

**Family:** `best-of-n`. **Result:** Disproof for every budget n≥2 and every positive atom cap.

**Abstract.** For every n≥2 and δ>0, there is a finite positive reference distribution whose largest atom is at most δ and whose best-of-n policy violates the proposed divergence–win-rate curve. A four-response best-of-two example gives exact probabilities and a strict logarithmic certificate. The proof uses finite interval bounds and gives a quantitative positive gap. It does not determine the sharp replacement curve.

**Original problem.** [Beirami et al., ICML 2025, Conjecture 7.2 and equation (28).](https://proceedings.mlr.press/v267/beirami25a.html)

[Paper PDF](papers/theoretical-computer-science/best-of-n/paper.pdf) · [LaTeX](papers/theoretical-computer-science/best-of-n/paper.tex) · [Bibliography](papers/theoretical-computer-science/best-of-n/references.bib) · [Citation](papers/theoretical-computer-science/best-of-n/citation.bib) · [Formal statement and prior work](lean/docs/theoretical-computer-science/best-of-n.md) · [Reproduction](papers/theoretical-computer-science/best-of-n/verification/README.md)

### Boolean functions and decision trees

#### [Logarithmic influence bounds and variance counterexamples for Boolean decision-tree covariance](papers/theoretical-computer-science/readk-covariance/docs/manuscript.pdf)

**Family:** `readk-covariance`. **Result:** A sharp logarithmic influence bound and two variance counterexamples.

**Abstract.** For a finite Boolean decision tree under uniform independent bits, the sum of absolute child covariances, weighted by node reach probabilities, is at most the sum of each coordinate influence times the base-two logarithm of its global query-node count. Counts zero and one receive weight zero. No coordinate repeats on a root-to-leaf path. A read-k tree therefore has absolute covariance at most I(f) log₂ k. The known dummy-prefix construction attains equality for powers of two. A four-variable witness and a nine-variable witness refute the coefficient-one logarithmic variance proposal. Every query in the latter witness is relevant. The formalization contains no Fourier-entropy theorem.

**Prior results.** [Wan, Wright, and Wu, ITCS 2014](https://doi.org/10.1145/2554797.2554806), introduced the covariance and the dummy-prefix construction. [Shalev, Section 6.2, Theorem 31](https://arxiv.org/abs/1806.03646v2), proved the square-root influence bound and proposed the logarithmic potential.

**Formal scope.** The standalone package uses Lean 4.19.0. Its 29 axiom reports are separate from the shared library's 29 Comparator declarations.

[Paper PDF](papers/theoretical-computer-science/readk-covariance/docs/manuscript.pdf) · [LaTeX](papers/theoretical-computer-science/readk-covariance/docs/manuscript.tex) · [Citation](papers/theoretical-computer-science/readk-covariance/CITATION.bib) · [Related work](papers/theoretical-computer-science/readk-covariance/docs/related-work.md) · [Reproduction](papers/theoretical-computer-science/readk-covariance/README.md)

### Fair division

#### [Ordered-instance allocation transfer with exact extra-copy preservation](papers/theoretical-computer-science/ordered-allocation/manuscript.pdf)

**Family:** `ordered-allocation`.

A set-valued ordered-instance transfer preserving utility improvement, the exact extra-copy count, per-good caps and coverage.

**Formal scope.** The transfer theorem is formalized. Existence of a fair allocation before transfer is outside the result; external source comparison is provisional.

[Paper PDF](papers/theoretical-computer-science/ordered-allocation/manuscript.pdf) · [LaTeX](papers/theoretical-computer-science/ordered-allocation/manuscript.tex) · [Reproduction and source context](papers/theoretical-computer-science/ordered-allocation/README.md) · [Citation](papers/theoretical-computer-science/ordered-allocation/CITATION.bib)

### Proof complexity

#### [Unbounded coalesced-mass certificates for resolution trees](papers/theoretical-computer-science/kunisky/paper.pdf)

**Family:** `kunisky`.

A coalesced dyadic clause-mass functional has exact supremum n+1 on the stated unrestricted resolution-tree class and is unbounded across dimensions.

**Formal scope.** The internally defined resolution-tree functional and proof class are formalized. No unconditional identification with an external conjecture or a regular proof class is claimed.

[Paper PDF](papers/theoretical-computer-science/kunisky/paper.pdf) · [LaTeX](papers/theoretical-computer-science/kunisky/paper.tex) · [Reproduction and source context](papers/theoretical-computer-science/kunisky/README.md) · [Citation](papers/theoretical-computer-science/kunisky/CITATION.bib)

## Mathematical physics

### Stochastic thermodynamics

#### [A three-state thermal counterexample to a heat-current kurtosis conjecture](papers/physics/thermal-kurtosis-counterexample/report.pdf)

**Family:** `thermal-kurtosis-counterexample`. **Result:** An exact negative spectral heat-cumulant ratio.

**Abstract.** A three-state model with two positive-temperature baths satisfies local detailed balance and has positive total off-diagonal transition rates. Its dominant tilted-generator eigenvalue has fourth-to-second derivative ratio −3470947982622836/176627429595846691. This refutes the thermal nonnegativity proposal in its finite spectral formulation. The proof constructs a smooth local eigenvalue branch, proves strict dominance over distinct complex eigenvalues, and calculates the exact derivatives.

**Original problem.** [Ptaszyński, Physical Review E 106, 024119 (2022), Eq. (19)](https://doi.org/10.1103/PhysRevE.106.024119). The finite thermal spectral model is specified in Eqs. (63)–(70).

**Formal scope.** The standalone package uses Lean 4.19.0. It does not formalize the stochastic long-time theorem that identifies the eigenvalue branch with a cumulant generating function. The witness does not refute the separate skewness conjecture or establish a minimal number of states.

**Prior work.** A Zenodo record (10.5281/zenodo.23689958), created on 27 October 2026 at 12:29 UTC, refutes the signs of both C₃/C₁ and C₄/C₂; my first commit of this result is about six and a half hours earlier. No priority is claimed. [Priority and novelty record](PRIORITY_AND_NOVELTY.md#zenodo-thermal-heat-current-kurtosis).

[Paper PDF](papers/physics/thermal-kurtosis-counterexample/report.pdf) · [LaTeX](papers/physics/thermal-kurtosis-counterexample/report.tex) · [Citation](papers/physics/thermal-kurtosis-counterexample/CITATION.bib) · [Related work](papers/physics/thermal-kurtosis-counterexample/RELATED_WORK.md) · [Reproduction](papers/physics/thermal-kurtosis-counterexample/README.md)

#### [A sharp universal skewness bound for unicyclic currents](papers/physics/unicyclic-skewness/manuscript.pdf)

**Family:** `unicyclic-skewness`.

The net marked-edge current on every finite bidirectional Markov ring with at least three states, positive rates and unequal forward and reverse rate products satisfies −1/16 ≤ C₃/C₁ ≤ 1. The two-channel two-state case has the stronger interval [1/4,1]. This ratio is not standardized skewness.

**Formal scope.** The interval for actual tilted-matrix derivatives and a local branch is formalized. Identification with long-time stochastic cumulants and sharpness have conventional proofs. Lean does not construct a continuous-time sample-path probability space or a separate optimizing-sequence theorem.

**Prior work.** The Omega Institute's public repository records the minimum skewness for unidirectional cycles, with infimum −1/16, committed on 26 October 2026 (issue #22468). The bidirectional two-sided interval here is a different question. [Priority and novelty record](PRIORITY_AND_NOVELTY.md#omega-unicyclic-skewness).

[Paper PDF](papers/physics/unicyclic-skewness/manuscript.pdf) · [LaTeX](papers/physics/unicyclic-skewness/manuscript.tex) · [Citation](papers/physics/unicyclic-skewness/CITATION.bib) · [Proof and reproduction](papers/physics/unicyclic-skewness/README.md)

### Quantum information

#### [Universal entanglement embezzlement with inverse-quadratic logarithmic infidelity](papers/physics/universal-embezzlement/manuscript.pdf)

**Family:** `universal-embezzlement`.

A target-independent catalyst with local dimension 2^(4L) gives root infidelity at most 125m/L² for every Schmidt probability vector on m entries.

**Formal scope.** The proof constructs local basis permutations and establishes their finite complex Hilbert-space interpretation. Arbitrary changes to an external Schmidt basis are not separately formalized.

**Prior work.** [Van Dam and Hayden, 2003; Leung and Wang, 2014.](https://arxiv.org/abs/1311.6842)

[Paper PDF](papers/physics/universal-embezzlement/manuscript.pdf) · [LaTeX](papers/physics/universal-embezzlement/manuscript.tex) · [Citation](papers/physics/universal-embezzlement/CITATION.bib) · [Reproduction](papers/physics/universal-embezzlement/README.md)

#### [A sum-of-squares proof of the four-qubit Higuchi–Sudbery entropy bound](papers/physics/higuchi-sudbery/manuscript.pdf)

**Family:** `higuchi-sudbery`.

The average von Neumann entropy of the three two-qubit marginals of a pure four-qubit state is at most log(2) + log(3)/2. The Higuchi–Sudbery state attains this bound.

The proof uses all sixteen complex amplitudes, actual reduced-matrix eigenvalues, an exact sum-of-squares identity, and an explicit maximizing state.

**Priority and subsequent correspondence.** On 30 October 2026, through correspondence with Dr. Jef Pauwels, I learned that the Omega Institute had registered this problem on 5 October 2026 and publicly committed a claimed Lean proof on 7 October 2026. Our 272-term sum-of-squares certificates are algebraically equivalent, and I make no originality or priority claim. [Priority and novelty record](PRIORITY_AND_NOVELTY.md#higuchisudbery-four-qubit-entropy-bound).

[Paper](papers/physics/higuchi-sudbery/manuscript.pdf) · [Source](papers/physics/higuchi-sudbery/manuscript.tex) · [Citation](papers/physics/higuchi-sudbery/CITATION.bib) · [Proof and verification](papers/physics/higuchi-sudbery/README.md)

#### [A pure-state matched-basis information inequality violation in dimension five](papers/physics/pure-ecqc/manuscript/manuscript.pdf)

**Family:** `pure-ecqc`.

A dimension-five pure-state matched-basis information inequality violation, with a conventional all-prime companion.

**Formal scope.** The dimension-five identical-local-basis theorem is formalized. The prime-family extension is conventional; arbitrary or independently optimized basis choices are outside the result.

**Prior work.** The Omega Institute's public repository records the same dimension-five counterexample, with the same state and bases, first committed on 4 October 2026 (issue #12896), about 25 days before my first commit. No priority is claimed for it. [Priority and novelty record](PRIORITY_AND_NOVELTY.md#omega-pure-state-ecqc-in-dimension-five).

[Paper PDF](papers/physics/pure-ecqc/manuscript/manuscript.pdf) · [LaTeX](papers/physics/pure-ecqc/manuscript/manuscript.tex) · [Reproduction and source context](papers/physics/pure-ecqc/README.md) · [Citation](papers/physics/pure-ecqc/CITATION.bib)

#### [Exact three-setting correlation bounds at fixed steering centre](papers/physics/steering-bounds/paper/steering_bounds.pdf)

**Family:** `steering-bounds`.

The exact least upper bound of the optimized three-setting squared correlation value is determined for every two-qubit steering-centre length. The threshold for a value greater than one is c < 2/3. Attainment, nonattainment and the singular marginal boundary are included.

**Formal scope.** Actual two-qubit density matrices, canonical filters, Pauli correlations, the exact least upper bound, attainment and nonattainment, and fully entangled fraction are formalized. The steering-ellipsoid and optimized CJWR measurement interpretations use cited external correspondences; general steerability is outside the result.

**Prior work.** The fully-entangled-fraction companion bound is Conjecture 2 of Milne et al.; the Omega Institute's public repository records a claimed Lean proof committed on 8 October 2026 (issue #14206), and a CHSH bound at fixed centre (issue #16558). No priority is claimed for the companion bound. [Priority and novelty record](PRIORITY_AND_NOVELTY.md#omega-steering-centre-bounds).

[Paper PDF](papers/physics/steering-bounds/paper/steering_bounds.pdf) · [LaTeX](papers/physics/steering-bounds/paper/steering_bounds.tex) · [Citation](papers/physics/steering-bounds/CITATION.bib) · [Proof and reproduction](papers/physics/steering-bounds/README.md)

#### [The three-state root-fidelity entropy bound](papers/physics/fidelity-three-state/manuscript.pdf)

**Family:** `fidelity-three-state`.

The entropy of the weighted three-by-three root-fidelity matrix bounds the Holevo quantity of every three-state ensemble in arbitrary finite dimension. The result includes mixed and singular states and zero probabilities.

**Formal scope.** The unrestricted three-state ensemble theorem is formalized for actual positive semidefinite complex matrices of trace one, nonnegative weights summing to one, spectral entropy and nuclear-norm root fidelity. Credited QICLean foundations and prior-work adapters retain their attribution.

**Priority and subsequent correspondence.** On 29 October 2026, through correspondence with Dr. Wojciech Roga, I learned that another group had contacted him several days earlier claiming a solution of the same conjecture using AI and Lean. The two proofs have not been compared, and neither mathematical equivalence nor priority has been conclusively established. [Priority and novelty record](PRIORITY_AND_NOVELTY.md#three-state-root-fidelity-entropy-bound).

**Prior work.** On 31 October 2026, a check of public records found a claimed Lean proof of the same conjecture in the Omega Institute's public repository, first committed on 19 October 2026 (issue #19184), about nine days before my first commit. The proofs have not been compared; no priority is claimed. [Priority and novelty record](PRIORITY_AND_NOVELTY.md#omega-root-fidelity-entropy-bound).

[Paper PDF](papers/physics/fidelity-three-state/manuscript.pdf) · [LaTeX](papers/physics/fidelity-three-state/manuscript.tex) · [Citation](papers/physics/fidelity-three-state/CITATION.bib) · [Proof and reproduction](papers/physics/fidelity-three-state/README.md)


#### [Exact conditional contraction for Pauli channels and depolarization in every dimension](papers/physics/quantum-exact-contraction/quantum_exact_contraction.pdf)

**Family:** `quantum-exact-contraction`.

The conditional hockey-stick contraction coefficient is determined exactly for every stochastic Pauli qubit channel and for depolarization throughout its physical parameter interval in every dimension. The formulas include all boundary cases and every hockey-stick parameter γ ≥ 1, with arbitrary finite quantum references.

**Formal scope.** The exact conditional hockey-stick contraction coefficients are formalized for actual finite-reference density states, every stochastic Pauli qubit channel, the full physical signed depolarizing family in every dimension d ≥ 2, and every γ ≥ 1. Channel constructors, unrestricted upper bounds and matching supremum witnesses are included. Unital-qubit normal-form existence is cited; erasure-simulation and ensemble-guessing consequences retain conventional proofs.

**Prior work.** The Omega Institute's public repository records a claimed general proof that the conditional hockey-stick coefficient does not depend on γ ≥ 1, committed on 16 October 2026 (issue #17637). The exact Pauli and depolarizing values here are not in that record. [Priority and novelty record](PRIORITY_AND_NOVELTY.md#omega-conditional-hockey-stick-contraction).

[Paper PDF](papers/physics/quantum-exact-contraction/quantum_exact_contraction.pdf) · [LaTeX](papers/physics/quantum-exact-contraction/quantum_exact_contraction.tex) · [Citation](papers/physics/quantum-exact-contraction/CITATION.bib) · [Proof and reproduction](papers/physics/quantum-exact-contraction/README.md)

#### [Strong minimum-rank multiplicativity from unextendible product constraints](papers/physics/upb-tensor-rank/manuscript.pdf)

**Family:** `upb-tensor-rank`.

A complex matrix subspace annihilated by an unextendible family of product functionals doubles minimum rank under tensor products: if every nonzero member of T has rank at least r, every nonzero member of S ⊗ T has rank at least 2r, and the minimum rank is exactly doubled when S contains a rank-two matrix. For the Tiles bound entangled state ρ, this gives Schmidt number SN(ρ^⊗N) = 2^N for every N ≥ 1, so N copies cost exactly N ebits to prepare by LOCC with zero error. The two-copy case and nonsharp exponential growth were known.

**Formal scope.** The rank-doubling theorem with an arbitrary partner, strong minimum-rank multiplicativity, the Tiles support and normalized density operators, and the exact all-copy Schmidt-number equivalence are formalized in 22 Lean modules. The zero-error LOCC cost, the rank-four two-qutrit PPT class and the channel interpretation combine the formal theorem with published results.

[Paper PDF](papers/physics/upb-tensor-rank/manuscript.pdf) · [LaTeX](papers/physics/upb-tensor-rank/manuscript.tex) · [Proof and reproduction](papers/physics/upb-tensor-rank/README.md) · [Citation](papers/physics/upb-tensor-rank/CITATION.bib)

#### [No universal finite collapse of the upper PPT entanglement-cost hierarchy](papers/physics/upper-ppt-hierarchy/manuscript.pdf)

**Family:** `upper-ppt-hierarchy`.

For every integer q ≥ 1 there is a bipartite density matrix ρ_q with κ_{q+1}(ρ_q) < κ_q(ρ_q) in the upper hierarchy of semidefinite programs of Lami, Mele and Regula, whose logarithms converge to the exact entanglement cost under PPT operations. The witnesses are full-rank product-Bell-diagonal states in local dimension 2^((2q+4)4^q), and the auxiliary matrices are unrestricted. Hence no fixed finite upper level is exact for all states. The proof builds arbitrarily long strictly positive reverse orbits of the absolute partial transpose by a weighted-sign argument and converts full support into a quantitative gap for every shorter chain. Brinster et al. had proved the corresponding all-depth statement for the lower χ hierarchy and left the upper question open. The theorem does not give one fixed state or dimension with infinitely many strict levels.

**Formal scope.** The strict separation at every adjacent level, for the actual semidefinite programs with unrestricted complex auxiliaries and positive-definite trace-one states with positive Bell coefficients, and the absence of a universal finite collapse are formalized in 17 Lean modules. The operational exact-cost and tensor-multiplicativity consequences use published theorems of Lami, Mele and Regula.

**Prior work.** [Lami, Mele and Regula, 2025; Brinster, Kondra, Kampermann, Bruß and Wyderka, 2026.](https://arxiv.org/abs/2609.20698)

[Paper PDF](papers/physics/upper-ppt-hierarchy/manuscript.pdf) · [LaTeX](papers/physics/upper-ppt-hierarchy/manuscript.tex) · [Proof and reproduction](papers/physics/upper-ppt-hierarchy/README.md) · [Citation](papers/physics/upper-ppt-hierarchy/CITATION.bib)

## Proof status and authorship

The [verification guide](verification/README.md) records completed checks and reproduction commands. [Unfinished formal proofs](UNFINISHED.md) identifies the remaining formalization limits. The [authorship disclosure](AUTHORSHIP.md) describes fully autonomous agentic research and its supported contribution history.
