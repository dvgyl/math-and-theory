# Gyires generalization research — 26 October 2026

## Outcome and scope

**The unrestricted Gyires conjecture is not solved in this package. Neither is the circulant conjecture in arbitrary order.**

Starting point: [dvgyl/gyires-circulant-5](https://github.com/dvgyl/gyires-circulant-5), commit `72cf49a51be42cf15592f91d991f0b0c76f58448`. The existing result covers every nonnegative circulant of order five. The new work here extends its finite certificate method to orders six and seven, proves restricted noncirculant families in unbounded dimensions, and identifies exact obstructions to several proposed general proofs.

Write `c_n=n!/n^n`, and let `J_n` mean the matrix whose entries all equal `1/n`. All doubly stochastic matrices here are real and nonnegative. Define

\[
\begin{aligned}
F_L(A)&=\operatorname{per}(A)^2-c_n\operatorname{per}(AA^T),\\
F_R(A)&=\operatorname{per}(A)^2-c_n\operatorname{per}(A^TA),\\
G(A)&=4\operatorname{per}(A)^2-c_n\{\operatorname{per}(AA^T)+\operatorname{per}(A^TA)+2\operatorname{per}(A^2)\}.
\end{aligned}
\]

Gyires asks for `G(A)>=0`, with equality only at `J_n`. Its statement and prior partial results are recorded on [Yair Lavi's Conjecture 20 page](https://yair-lavi.com/mincs-list/conjecture-20/index.html). That page is a prior-work source, not a source for the new derivations below. Limited searches do not establish novelty or priority.

| Result | Scope | Outcome | Verification in this package |
|---|---|---|---|
| C6 | Every nonnegative 6-by-6 circulant | Strong inequality, sharp sorted-gap margin, equality case; hence Gyires after normalization | Exhaustive exact certificate and independently reconstructed polynomial/identity checks |
| C7 | Every nonnegative 7-by-7 circulant | Same | Same |
| R3 | At most three nonuniform rows, any `n>=5` | `F_L(A)>=c_n^2 K_n ||A-J_n||_F^2` | Ordinary analytic proof, separately reviewed by AI agents; exact finite diagnostics |
| B3 | Perturbation of `J_n` supported in at most three rows and three columns, any `n>=5` | Both strong bounds and `G(A)>=4c_n^2 K_n ||A-J_n||_F^2` | Same analytic proof and its transpose |
| R31 | At most three nonuniform rows, any `n>=31` | Both strong bounds and `G(A)>=4c_n^2 gamma ||A-J_n||_F^2`, `gamma=9301/445904` | Analytic proof using a generic centered-PSD Gaussian coefficient bound; separately reviewed |
| General | Arbitrary doubly stochastic matrices; arbitrary-order circulants | **Unresolved here** | No general proof and no counterexample obtained |

Here

\[
K_n=\frac{6(n-5)^4+77(n-5)^3+333(n-5)^2+515(n-5)+149}{6(n-1)^2(n-2)^2}>0.
\]

For all proved doubly stochastic families the stated positive margin implies equality only at `J_n`. R3 is one-sided: for `5<=n<31`, this proof does not automatically establish original Gyires for arbitrary matrices with three nonuniform rows. B3 imposes the extra column condition to justify the transpose bound. R31 removes that restriction only for its stated dimension range.

## Exact circulant results

Let `z_1,...,z_(n-1)` be the consecutive gaps between the sorted weights in the first row of a circulant `C`.

\[
324\operatorname{per}(C)^2-5\operatorname{per}(CC^T)
\ge296\sum_{j=1}^{5}z_j^{12}\qquad(n=6),
\]

\[
117649\operatorname{per}(C)^2-720\operatorname{per}(CC^T)
\ge116929\sum_{j=1}^{6}z_j^{14}\qquad(n=7).
\]

The first constant is attained by weights `(1,1,0,0,0,0)`; the second by `(1,0,0,0,0,0,0)`. Both are sharp. Equality in each un-margined strong inequality occurs exactly at constant weights, including the zero vector.

| Order | Affine chambers | Coefficient positions per chamber | Positive | Zero | Least positive coefficient of `n^n per(C)^2-n! per(CC^T)` |
|---|---:|---:|---:|---:|---:|
| 6 | 60 | 6,188 | 6,182 | 6 | 42,624 |
| 7 | 120 | 38,760 | 38,753 | 7 | 818,503 |

There are **5,022,480 coefficient positions** across these representative chambers. The independent checker also checks that the affine images cover all 720 and 5,040 weight orderings respectively. It reconstructs the original polynomial using permutation enumeration and grouped autocorrelations, compares it exactly with the generator, then applies inverse substitutions to verify every full chamber polynomial. Python integers are unbounded; floating-point arithmetic is not used in any certificate assertion.

Full coefficient tables need not be stored: the generator and checker reproduce them. The JSON files contain statistics, pure-gap coefficients and exact examples, not a list of millions of coefficients. These are computer-assisted algebraic proofs, **not newly completed Lean formalizations**.

## Analytic results

The complete proofs of R3, B3 and R31 are in `combinatorial_findings.md`. An independent AI review is recorded in `analytic_findings.md`. Their core ingredients are:

1. A centered matrix with at most three nonzero rows has a permanent expansion terminating at degree three.
2. Stochasticity gives explicit lower bounds for its cubic moment and an upper bound on its squared Frobenius norm.
3. A centered positive semidefinite matrix supported on three coordinates has a sharp cubic-moment bound.
4. For arbitrary support, a complex Gaussian representation and a Cauchy coefficient estimate control the remaining permanent coefficients. This gives R31.

For an example of B3, choose any 3-by-3 doubly stochastic matrix `S`, choose three rows and three columns of `J_n`, and replace that block by `(3/n)S`. This preserves all row/column sums. The selected row and column sets need not coincide. This four-dimensional family includes matrices with zero entries and is generally noncirculant.

## What blocks the full proof

The proposed extension of sorted coefficient positivity to arbitrary Birkhoff decompositions is false. If `E` is the 4-by-4 all-ones matrix,

\[
A(t,u,v)=6tE+u(3E-2I)+vI
\]

comes from nested tails of the 24 permutation matrices, but the coefficient of `t^6uv` in `4^4 per(A)^2-4!per(AA^T)` is `-6,879,707,136`. Both a direct exact expansion and a separate quadratic-at-uniform derivation give that value. This is a counterexample to a proof strategy, not to Gyires.

Other exact examples show that averaging two rows or columns need not decrease the strong ratio, and a repeated-column permanent can exceed the original permanent. See `check_obstructions.py`, `obstruction_checks.json` and the findings notes.

The still-unproved all-order circulant route is the coefficient nonnegativity statement restricted to disjoint cyclic permutation layers. Selected chambers in orders eight and nine support it, but those orders were not exhaustively checked. No finite set of checks is asserted to prove the all-order statement.

## Reproduce the exact checks

Use Python 3.10 or later from this directory. The exact certificate and analytic diagnostic scripts use only the standard library. Do not invoke Python with `-O`, because it disables their assertions.

```bash
python circ_gap_test.py 6 all
python circ_gap_test.py 7 all
python independent_certificate_check.py 6
python independent_certificate_check.py 7
python check_three_row_theorem.py
python check_obstructions.py
```

The independent certificate checker took about 5 seconds for order six and 100 seconds for order seven in the research environment. These are observed run times, not guarantees. See `independent_certificate_n6.json`, `independent_certificate_n7.json` and corresponding logs for actual results.

The analytic diagnostic script verifies 360 exact matrices of orders five through ten and 51 matrices of orders 31, 32, 33, 40 and 64. The larger-order calculation uses a rank-three permanent evaluator that was cross-checked against direct subset dynamic programming in orders five through seven. Those examples test identities and detect transcription mistakes; they are **not** the proofs of the quantified analytic theorems. The analytic proofs are in the note. `check_obstructions.py` also verifies the exact rational constant used at the R31 threshold.

`circ_strategic.py` reproduces selected higher-order chamber experiments. These can be much more expensive, especially order nine. They are optional exploratory computations and do not certify either full order. Their cached pickle files are omitted; the script reconstructs them when needed. Only use caches produced locally by the supplied script.

## Numerical exploration, explicitly not a proof

The separate `ratio_search.py` and `ratio_search.cpp` implement positive-term permanents, gradients and constrained local minimization of `per(A)^2/(c_n per(AA^T))`. There were 30 starting matrices in each of orders five, six and seven. All 90 optimization runs terminated successfully; no value below one was found beyond numerical precision. Sparse regular examples of orders sixteen and twenty were also explored, as recorded in the analytic findings.

These finite numerical searches do not rule out counterexamples and do not certify global minima. The numerical script requires NumPy, SciPy and a C++ compiler:

```bash
g++ -O3 -shared -fPIC ratio_search.cpp -o permanent_numeric.so
python ratio_search.py 5 30
```

The gradient implementation was checked against finite differences, and one permanent against direct permutation enumeration. No compiled binary is distributed.

## Files and continuation

- `circ_findings.md`: finite circulant results, larger-order evidence, exact obstruction, and an elementary subgroup-support consequence in unbounded dimensions.
- `combinatorial_findings.md`: complete analytic proofs and the occupancy reformulation of the missing unrestricted estimate.
- `analytic_findings.md`: separate proof review, unsuccessful rank-two route, and other exact obstructions.
- `common_reduction.md`: the permanent Gram comparison used to pass from strong bounds to Gyires.
- Python/C++ source and JSON/log files: reproducible computations and their status.
- `STATUS.json`: machine-readable scope and verification limits.
- `SHA256SUMS`: file-integrity manifest.

The most concrete next mathematical target is an all-order proof for disjoint circulant layers. The broader arbitrary-permutation coefficient assertion must not be reused, because the exact order-four obstruction refutes it. Formalizing C6/C7 and the analytic theorems would strengthen verification, but would not fill the unrestricted mathematical gap.

## Authorship, review and novelty

This is AI-generated research produced by ChatGPT from Dev D. Goyal's request to continue the project and seek a general solution. Multiple AI agents explored independent approaches and reviewed derivations. Dev directed the research request; this package does not attribute mathematical proof ideas or new verification work to him.

The existing repository's AI disclosures remain applicable to its previous work. The new work here has not been independently reviewed by a human specialist, peer reviewed, or formalized and checked in Lean. Agreement between AI derivations and exact computer checks is not represented as human peer review. No claim of novelty or priority is made. The full conjecture is explicitly left unresolved.

No changes were published to GitHub in this session.
