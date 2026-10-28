# Gyires results and evidence

The [manuscript](../../preprints/gyires-circulant-five/paper.pdf) contains the arguments listed below. A reduction proves a relationship between statements. It does not prove an unresolved target inequality.

The principal order-five and order-six claims, the all-order permutation-polynomial and four-block theorems, the exceptional-vector theorem, and rank-two orders 2 through 8 have complete Lean proofs. The general order-seven circulant theorem and rank-two orders 9 through 15 remain incomplete in Lean. The other matrix classes have ordinary proofs and the stated exact certificates. The [formal guide](../../lean/docs/gyires-circulant-five.md) gives the exact formal scope.

| Result | Manuscript section |
|---|---|
| Nonnegative circulants of order five; strong bound, equality, sharp gap margin 484; Gyires inequality after normalization | Order-five circulants |
| Nonnegative circulants of order six; sharp reduced sorted-gap constant 296; equality only at constant weights | Orders six and seven |
| Nonnegative circulants of order seven; sharp reduced sorted-gap constant 116929 | Orders six and seven |
| All-order `aI+bQ+cQ²`, with nonnegative coefficients and arbitrary permutation matrix Q | Permutation polynomials |
| General direct-sum closure and independent row/column permutation closure of both strong bounds; strictness for at least two nonempty blocks | Closure and sparse perturbations |
| Circulants with support in a coset of a cyclic subgroup of order 5, 6 or 7, in arbitrarily large ambient dimensions | Orders six and seven |
| Symmetric positive-semidefinite doubly stochastic matrices, and their independent row/column relabelings | Closure and sparse perturbations |
| R3: at most three exceptional rows, n≥5; one-sided strong bound with explicit positive K_n | Closure and sparse perturbations |
| B3: A−J supported on at most three rows and three columns, n≥5; both strong bounds and Gyires margin 4c_n²K_n‖A−J‖² | Closure and sparse perturbations |
| R31: at most three exceptional rows or at most three exceptional columns, n≥31; both strong bounds and Gyires with gamma=9301/445904 | Closure and sparse perturbations |
| At most two distinct column types: `per(AAᵀ)≤per(A)` in every order | Four-block matrices |
| At most two distinct row types and two distinct column types, with unequal block sizes and boundary cases; both strong bounds and Gyires margin 4d(d−c_n) | Four-block matrices |
| One exceptional column with all other columns identical, or the transpose, in every n≥2; both strong bounds and equality only at J | One exceptional column or row |
| All rank-at-most-two doubly stochastic matrices in orders 2–15; stronger Gram contraction and hence Gyires | Rank two through order fifteen |
| Factorial coefficient inner product equals the permanent of the cross Gram matrix; permanent Cauchy–Schwarz; both strong bounds imply original Gyires | Common permanent identities |
| Zero-sum minor expansion, exact quadratic/cubic coefficients, three-coordinate PSD cubic bound | Closure and sparse perturbations |
| Centered PSD trace estimate for per(J+D), using complex Gaussian coefficients, Cauchy estimates and a geometric tail | Closure and sparse perturbations |
| Symmetrized polynomial formulation of the original denominator; nonnegative even radial expansion; explicit strictly positive first coefficient for nonzero centered direction | Closure and sparse perturbations |
| Direct matrix boundary reduction in each fixed order; all maximizers of the square-root deficit have identical rows in each row-support class | Closure and sparse perturbations |
| Mean-one ULC scalar inequality, including all boundary supports and equality only at the reference binomial law | Scalar and two-group polynomials |
| General finite-reference localization under two linear constraints | Scalar and two-group polynomials |
| Symmetric-reference scalar norm inequality and equality case; central binomial consequence; two-group polynomial interpretation | Scalar and two-group polynomials |
| Integer-mean Poisson-binomial likelihood peak and stronger norm inequality | Four-block matrices |
| One-special-variable balanced Lorentzian polynomial norm bound | Scalar and two-group polynomials |
| Duplication-to-Gram bridge for the mean-one Lorentzian family | Scalar and two-group polynomials |
| Common-mean factorization of every nonnegative rank-two doubly stochastic matrix; exact permanent and Gram/noise formulas | Rank two and two-law reduction |
| Separate convexity and localization within the Poisson-binomial class to pairs of shifted binomials | Rank two through order fifteen |
| Wider ULC variance bound and separately convex squared-target reduction to geometric likelihood ratios on intervals | Two-law scalar reduction |
| Singleton deletion closure for rank-two matrix products, including capacity-balanced limits | Rank-two deletion and limits |
| Existence and uniqueness of the determinant-one balanced polynomial limit for nonnegative degree-m polynomials in m variables with positive central coefficient | Rank-two deletion and limits |
| Real-rooted univariate collision marginal for a nonzero zero-containing column of a rank-two nonnegative matrix | Rank-two deletion and limits |
| Exact cubic capacity-balanced average-deletion inequality for doubly stochastic matrix products; equality only at J3 | Coordinate deletion |
| Exact permanent-gradient formula for a scaled singleton deletion norm | Coordinate deletion |
| Capacity-balanced deletion on a two-shift cycle in every order; stronger factor sqrt(2)−1 above the small-order range, with explicit checks for n=2,3,4 | Coordinate deletion |
| Exact expectation of per(GGᵀ) and exact second moment of per(G) for the regular bipartite configuration model | Configuration model |
| Analytic capacity balancing near the uniform deletion; full first and second variation formulas | Local polynomial results |
| Exact stable tangent cone; realizability; stable first variations and second coefficient; strict neighborhood theorems with sharp asymptotic constants | Local polynomial results |
| Global stable variance-deficit energy, rigidity at zero, exact uniform-mixing scaling, higher contrast-grade estimates | Local polynomial results |
| Lorentzian tangent-cone constraints and positive first variation for deletion and norm deficits | Local polynomial results |
| Fischer operator identities for the remaining global question | Local polynomial results |
| Uniform-power subtraction to a Lorentzian coefficient boundary; preservation of real stability in degree three; cubic deletion boundary reduction | Local polynomial results |
| Stable cubic boundary rigidity | Local polynomial results |
| Highest-coordinate-layer attenuation preserves Lorentzianity | Local polynomial results |
| Balanced exponential tilt on an M-convex support: exact norm reformulation F_S(2z*)≤1, and exact entropy identities | Local polynomial results |
| Stochastic complement of an admissible pivot is doubly stochastic | Exact limitations |

## Exact limitations

The manuscript gives exact counterexamples to Birkhoff-gap coefficient positivity, radial and deletion-ratio monotonicity, and a wider ultra-log-concave contraction. It also treats prescribed deletion columns, stochastic-complement pivot rules, averaged minimum-norm deletion, iterative subtraction, and layer attenuation. Further examples concern support-only norm bounds, multivariate Vandermonde comparisons, and collision-law balance. Each example refutes only its stated auxiliary assertion. None refutes Gyires's conjecture.

## Additional arguments and computations

Appendix A of the manuscript contains 28 sections of exact examples and supporting arguments. These include scalar entropy and tensor reductions, Latin-square coefficient layers, a ternary-cubic relaxation, and alternative transfer bounds. Each reduction states its unresolved target.

Appendix B contains 14 groups of finite computational observations. The [data guide](exploratory-data/README.md) identifies their scientific records and limits. Numerical searches do not establish the unrestricted conjectures.

## Unresolved statements

The results do not cover all circulants in arbitrary order or all rank-two matrices above order fifteen. The asymmetric integer-mean ultra-log-concave target also remains unresolved. Other unresolved targets concern balanced stable or Lorentzian norms, general capacity-balanced deletion, useful stochastic-complement pivots, and an M-convex entropy bound.

Finite samples in circulant orders eight, nine, and twelve do not establish theorems in those orders. The stated all-order results use proofs beyond finite computation.
