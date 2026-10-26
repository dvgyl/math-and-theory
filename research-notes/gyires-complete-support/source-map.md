# Source map for the complete Gyires preprint

The [continuous manuscript](../../preprints/gyires-circulant-five/paper.pdf) contains the completed positive arguments listed below. This map records the actual scope of each result. A completed reduction does not establish its remaining target inequality.

Source paths refer to the supplied Gyires bundle. Each historical text is preserved under `sources/`, with `.txt` added to its original filename. The [provenance manifest](provenance.json) gives exact paths and hashes. Repeated notes and weaker arguments are identified below. The original order-five sources retain their separate formal record.

Only the principal order-five claims have completed Lean verification. The other entries are ordinary proofs or exact computational proofs. This source map does not claim novelty, human expert review, or peer review.

| Completed result | Source | Manuscript section |
|---|---|---|
| Nonnegative circulants of order five; strong bound, equality, sharp gap margin 484; original Gyires after normalization | Original order-five sources; current public manuscript, order-five section | Order-five circulants |
| Nonnegative circulants of order six; sharp reduced sorted-gap constant 296; equality only at constant weights | `research/round_1/circ_findings.md` §1; `circ_gap_test.py`, `independent_certificate_check.py` and their order-six reports | Orders six and seven |
| Nonnegative circulants of order seven; sharp reduced sorted-gap constant 116929 | Same note §1 and order-seven reports | Orders six and seven |
| All-order `aI+bQ+cQ²`, with nonnegative coefficients and arbitrary permutation matrix Q | `research/round_2/round2_circulant.md` §§1–8; `round2_analytic.md` §§1–5; `round2_sharp_spectral_lemma.md`; `PROOF_AND_STATUS.md` | Permutation polynomials |
| General direct-sum closure and independent row/column permutation closure of both strong bounds; strictness for at least two nonempty blocks | `research/round_2/round2_combinatorial.md` §5 | Closure and sparse perturbations |
| Circulants with support in a coset of a cyclic subgroup of order 5, 6 or 7, in arbitrarily large ambient dimensions | `research/round_1/circ_findings.md` §4 | Orders six and seven |
| Symmetric positive-semidefinite doubly stochastic matrices, and their independent row/column relabelings | `research/round_1/analytic_findings.md` §4 | Closure and sparse perturbations |
| R3: at most three exceptional rows, n≥5; one-sided strong bound with explicit positive K_n | `research/round_1/combinatorial_findings.md`, “Exact statement” and “Proof of Theorem A” | Closure and sparse perturbations |
| B3: A−J supported on at most three rows and three columns, n≥5; both strong bounds and Gyires margin 4c_n²K_n‖A−J‖² | Same note, “Proof of Theorem B” | Closure and sparse perturbations |
| R31: at most three exceptional rows or at most three exceptional columns, n≥31; both strong bounds and Gyires with gamma=9301/445904 | Same note, “Proof of Theorem C”; audit in `research/round_1/analytic_findings.md` §5 | Closure and sparse perturbations |
| At most two distinct column types: `per(AAᵀ)≤per(A)` in every order | `research/round_5/round5_scalar.md` §§6,8; `round5_rank2.md` §3 | Four-block matrices |
| At most two distinct row types and two distinct column types, with unequal block sizes and boundary cases; both strong bounds and Gyires margin 4d(d−c_n) | `research/round_5/round5_scalar.md` §8 | Four-block matrices |
| One exceptional column with all other columns identical, or the transpose, in every n≥2; both strong bounds and equality only at J | `research/round_4/round4_one_special_matrix.md` §§1–5; `round4_one_special_matrix_audit.md` | One exceptional column or row |
| All rank-at-most-two doubly stochastic matrices in orders 2–15; stronger Gram contraction and hence Gyires | `research/round_6/round6_rank2_bernstein.md`; generator, fraction checker and two audits in the same directory | Rank two through order fifteen |
| Factorial coefficient inner product equals the permanent of the cross Gram matrix; permanent Cauchy–Schwarz; both strong bounds imply original Gyires | `research/round_1/common_reduction.md`; later notes | Common permanent identities |
| Zero-sum minor expansion, exact quadratic/cubic coefficients, three-coordinate PSD cubic bound | `research/round_1/combinatorial_findings.md`, proof of Theorem A | Closure and sparse perturbations |
| Centered PSD trace estimate for per(J+D), using complex Gaussian coefficients, Cauchy estimates and a geometric tail | Same note, “A dimension-independent trace estimate…” | Closure and sparse perturbations |
| Symmetrized polynomial formulation of the original denominator; nonnegative even radial expansion; explicit strictly positive first coefficient for nonzero centered direction | `research/round_3/round3_original.md` §§1–2 | Closure and sparse perturbations |
| Direct matrix boundary reduction in each fixed order; all maximizers of the square-root deficit have identical rows in each row-support class | `research/round_5/round5_matrix_boundary.md`; `PROOF_AND_STATUS.md` §4 | Closure and sparse perturbations |
| Mean-one ULC scalar inequality, including all boundary supports and equality only at the reference binomial law | `research/round_4/round4_scalar_ulc.md` §§1–6; independent audit in the same round | Scalar and two-group polynomials |
| General finite-reference localization under two linear constraints | `research/round_5/round5_scalar.md` §2; earlier version in `research/round_4/round4_rank2_localization.md` §6 | Scalar and two-group polynomials |
| Symmetric-reference scalar norm inequality and equality case; central binomial consequence; two-group polynomial interpretation | `research/round_5/round5_scalar.md` §§3–5 | Scalar and two-group polynomials |
| Integer-mean Poisson-binomial likelihood peak and stronger norm inequality | `research/round_5/round5_scalar.md` §6; alternative proof in `round5_rank2.md` §3 | Four-block matrices |
| One-special-variable balanced Lorentzian polynomial norm bound | `research/round_4/round4_scalar_ulc.md`, polynomial consequence | Scalar and two-group polynomials |
| Duplication-to-Gram bridge for the mean-one Lorentzian family | `research/round_5/round5_scalar.md` §7 | Scalar and two-group polynomials |
| Common-mean factorization of every nonnegative rank-two doubly stochastic matrix; exact permanent and Gram/noise formulas | `research/round_4/round4_rank2_localization.md` §§1–3; `research/round_5/round5_rank2.md` §1 | Rank two and two-law reduction |
| Separate convexity and localization within the Poisson-binomial class to pairs of shifted binomials | `research/round_5/round5_rank2.md` §§1–2; `research/round_6/round6_boundary_induction.md` §7 | Rank two through order fifteen |
| Wider ULC variance bound and separately convex squared-target reduction to geometric likelihood ratios on intervals | `research/round_4/round4_rank2_localization.md` §§4–7 | Two-law scalar reduction |
| Singleton deletion closure for rank-two matrix products, including capacity-balanced limits | `research/round_5/round5_rank2.md` §6; `round5_rank2_closure_audit.md` §§1–3 | Rank-two deletion and limits |
| Existence and uniqueness of the determinant-one balanced polynomial limit for nonnegative degree-m polynomials in m variables with positive central coefficient | `research/round_5/round5_rank2_closure_audit.md` §4 | Rank-two deletion and limits |
| Real-rooted univariate collision marginal for a nonzero zero-containing column of a rank-two nonnegative matrix | `research/round_5/round5_rank2.md` §7 | Rank-two deletion and limits |
| Exact cubic capacity-balanced average-deletion inequality for doubly stochastic matrix products; equality only at J3 | `research/round_3/round3_original.md` §9; `round3_combinatorial.md` §7; `round3_deletion_audit.md` | Coordinate deletion |
| Exact permanent-gradient formula for a scaled singleton deletion norm | `research/round_3/round3_all_circulants.md` §8 | Coordinate deletion |
| Capacity-balanced deletion on a two-shift cycle in every order; stronger factor sqrt(2)−1 above the small-order range, with explicit checks for n=2,3,4 | `research/round_3/round3_all_circulants.md` §9 | Coordinate deletion |
| Exact expectation of per(GGᵀ) and exact second moment of per(G) for the regular bipartite configuration model | `research/round_3/round3_combinatorial.md` §3 | Configuration model |
| Analytic capacity balancing near the uniform deletion; full first and second variation formulas | `research/round_4/round4_local.md` §§2–3 | Local polynomial results |
| Exact stable tangent cone; realizability; stable first variations and second coefficient; strict neighborhood theorems with sharp asymptotic constants | Same note §§4–7 | Local polynomial results |
| Global stable variance-deficit energy, rigidity at zero, exact uniform-mixing scaling, higher contrast-grade estimates | Same note §8, before “The deletion ratio is not globally monotone…” | Local polynomial results |
| Lorentzian tangent-cone constraints and positive first variation for deletion and norm deficits | Same note §9 | Local polynomial results |
| Fischer operator identities for the remaining global question | Same note §10 | Local polynomial results |
| Uniform-power subtraction to a Lorentzian coefficient boundary; preservation of real stability in degree three; cubic deletion boundary reduction | `research/round_4/round4_analytic.md` §§1–3; duplicate derivation in `round4_local.md` §11 | Local polynomial results |
| Stable cubic boundary rigidity | `research/round_4/round4_analytic.md` §8 | Local polynomial results |
| Highest-coordinate-layer attenuation preserves Lorentzianity | `research/round_5/round5_combinatorial.md` §2 | Local polynomial results |
| Balanced exponential tilt on an M-convex support: exact norm reformulation F_S(2z*)≤1, and exact entropy identities | `research/round_5/round5_combinatorial.md` §1 | Local polynomial results |
| Stochastic complement of an admissible pivot is doubly stochastic | `research/round_6/round6_boundary_induction.md` §1 | Exact limitations |

## Exact limitations

The manuscript proves exact counterexamples to general Birkhoff-gap coefficient positivity, radial and deletion-ratio monotonicity, a wider ultra-log-concave contraction, prescribed deletion columns, natural stochastic-complement pivot rules, averaged minimum-norm deletion, iterative subtraction, layer-attenuation monotonicity and convexity, and a support-only norm bound. It also gives the multivariate Vandermonde obstruction and collision-law balance failures. Each example retains its precise target. None refutes Gyires's conjecture.

The source notes contain further exact failures of auxiliary approaches. These are retained as historical records. They include repeated-column coefficient comparison, pairwise averaging, Jensen concavity, collision stability, trace comparison, operator compression, transpose averaging, phase independence, support-width spectral bounds, and proposed information-theoretic bridges. The manuscript does not depend on those failed assertions.

## Subsumed arguments and open steps

The repeated scalar and localization notes are integrated once. The earlier transfer constant 51/20 is superseded by the sharper 1+sqrt(2) proof. Repeated occupancy, tensor, and coefficient-pairing identities use the common permanent identity. Repeated cubic deletion derivations use one proof and three independent certificate constructions.

Nonexhaustive checks in circulant orders eight, nine, and twelve do not establish a theorem in those orders. Sampled matrix searches and candidate sum-of-squares searches are exploratory. They are not used as proofs.

The all-order arbitrary-circulant and arbitrary-rank-two assertions remain unproved here. The asymmetric integer-mean ultra-log-concave target, full balanced stable or Lorentzian norm inequality, general capacity-balanced deletion bound, useful-pivot existence claim, and M-convex entropy target also remain open in this account. The manuscript states the completed reductions without assuming these targets.
