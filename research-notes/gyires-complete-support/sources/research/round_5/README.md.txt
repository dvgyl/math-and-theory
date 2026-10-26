# Gyires general-case investigation — research round 5

Date: 2026-10-26. Continuation of the investigation starting from [dvgyl/gyires-circulant-5](https://github.com/dvgyl/gyires-circulant-5).

## Current mathematical status

**The unrestricted conjecture is not proved. The unrestricted rank-two case is also not proved.** This package contains all-order proofs on specified families, exact structural reductions, exact counterexamples to auxiliary claims, and numerical exploration. These categories must not be conflated.

Put $c_n=n!/n^n$. The original target, for a doubly stochastic matrix $A$, is

\[
4\operatorname{per}(A)^2\ge c_n\left[
\operatorname{per}(AA^T)+\operatorname{per}(A^TA)
+2\operatorname{per}(A^2)\right],
\]

with equality only at $J_n$, whose entries are all $1/n$. The stronger one-sided target is

\[
\operatorname{per}(A)^2\ge c_n\operatorname{per}(AA^T).
\]

For $p_A(x)=\prod_i(Ax)_i$ and $N(p)=\sum_\alpha\alpha!p_\alpha^2$, the identities are $[x_1\cdots x_n]p_A=\operatorname{per}(A)$ and $N(p_A)=\operatorname{per}(AA^T)$.

## What is proved in this round

| Result | Exact scope | Main proof |
| --- | --- | --- |
| Integer-mean likelihood peak | If $P$ is a sum of $n$ independent Bernoulli variables with integer mean $m$ and $B=\operatorname{Bin}(n,m/n)$, then $P_k/B_k\le P_m/B_m$ for every $k$ | `round5_scalar.md`, Section 6; alternative proof in `round5_rank2.md`, Section 3 |
| Stronger scalar norm bound | $\sum_k P_k^2/B_k\le P_m/B_m\le(P_m/B_m)^2$; first equality exactly for $P=B$ or $\delta_m$, squared-bound equality only for $P=B$ | `round5_scalar.md`, Section 6 |
| Two-column-type Gram contraction | $\operatorname{per}(AA^T)\le\operatorname{per}(A)$ in every order when $A$ has at most two distinct columns | `round5_scalar.md`, Section 8 |
| Original Gyires with a margin | Every doubly stochastic matrix with at most two row types and at most two column types satisfies the original inequality; its deficit is at least $4d(d-c_n)$, $d=\operatorname{per}(A)$, with equality only at $J_n$ | `round5_scalar.md`, Section 8 |
| Direct matrix boundary reduction | The strong inequality in each fixed order is equivalent to its restriction to matrices with a zero entry; any global maximizer of the square-root deficit has identical rows within each row-support class | `round5_matrix_boundary.md` |
| Symmetric-reference scalar theorem | For any positive finite symmetric reference law $B$ and a mean-centered $P$ with log-concave ratio $P/B$, $\sum P^2/B\le(P_0/B_0)^2$, equality only at $P=B$ | `round5_scalar.md`, Sections 2–5 |
| Mean-one duplication bridge | The proposed duplication-to-Gram coefficient comparison holds for every balanced one-special-variable Lorentzian polynomial, in all degrees | `round5_scalar.md`, Section 7, using the included round-4 mean-one proof |
| Rank-two profile reduction | For each fixed mean, the strong rank-two inequality is equivalent to its restriction to pairs of shifted binomial laws, leaving integer multiplicities and one real parameter | `round5_rank2.md`, Sections 1–4 |
| Rank-two deletion closure | Extracting exactly one copy of a variable, then capacity balancing or taking its unique capacity limit, stays within rank-two matrix products | `round5_rank2_closure_audit.md` |
| Real-rooted collision marginal | For a nonnegative rank-two matrix, a nonzero column containing a zero has a real-rooted univariate Fock collision polynomial | `round5_rank2.md`, Section 7 |
| Lorentzian top-layer attenuation | Scaling down the coefficients of highest degree in one variable preserves Lorentzianity | `round5_combinatorial.md`, Section 2 |

“Two row types and two column types” means a matrix constant on four rectangular blocks after independent row and column relabeling. The sizes of the two row groups and two column groups may differ. It is a proper subclass of rank-two matrices.

## Precisely what is missing

For rank two, write

\[
A_{ij}=x_i y_j/t+(1-x_i)(1-y_j)/(n-t),
\quad x,y\in[0,1]^n,\quad\sum x_i=\sum y_i=t.
\]

Let $P_x,P_y$ be the two Poisson-binomial laws, $B=\operatorname{Bin}(n,t/n)$, $r=P_x/B$, $s=P_y/B$, and $T_\kappa$ the binomial noise operator defined in the rank-two note. The strong target is exactly

\[
\langle r,s\rangle_B^2\ge
\langle r,T_{\kappa(s)}r\rangle_B,
\qquad
\kappa(s)=1-\frac{\operatorname{Var}(P_y)}{t(1-t/n)}.
\]

The proof reduces both laws to shifted binomials, but does not prove the resulting inequality uniformly in the multiplicities and mean. The stronger contraction without the square on the left is also unproved.

An alternative rank-two induction would follow from this additional estimate: for every rank-two doubly stochastic matrix with a zero, at least one column $j$ containing a zero satisfies

\[
H([x_j]p_A)\ge
\left(\frac{n-1}{n}\right)^{n-1}N(p_A),
\]

where $H$ is the norm of the unique determinant-one capacity-balanced polynomial limit. Closure and existence of that limit are proved. This norm comparison is not. Neither rank-two route by itself addresses higher rank.

The broader scalar Lorentzian inequality at an arbitrary asymmetric integer mean also remains open in this work. It is proved here for Poisson-binomial laws at every integer mean, for arbitrary log-concave likelihood ratios at a symmetric reference, and in the prior round at mean one and its reflection.

## Exact obstructions

The package includes explicit certificates that the following auxiliary assertions are false. None is a counterexample to Gyires.

- Arbitrary column averaging decreases the permanent, even when restricted to rank-two doubly stochastic matrices: false in order three.
- The multivariate occupancy likelihood ratio is always largest at the all-ones occupancy: false even in rank two, using the same order-three example.
- The balanced deletion comparison holds for every column: false exactly in order three for a column without a zero. The zero-containing-column version remains unrefuted.
- A global Fock-capacity comparison $\mathcal C_F(p)/N(p)\ge g_n/g_d$ repairs the deletion induction: false in order 50 with one zero entry, proved by rational inequalities.
- The proposed rank-two contraction extends to all ultra-log-concave laws: false in an exact order-four example. The squared target is not refuted by that example.
- Filling a missing Lorentzian coefficient makes the capacity-balanced Fock norm increase continuously or makes it convex in the filling parameter: both assertions are false.
- A product polynomial is dominated by the exponential-generating polynomial of its support in the required normalized norm: false for the support from $I+P_4$.

Full examples and derivations are in `round5_matrix_boundary.md`, `round5_rank2.md`, `round5_fock_capacity_obstruction.md`, and `round5_combinatorial.md`.

## Reading order

1. `round5_scalar.md`: the all-order scalar and matrix family proofs, including equality.
2. `round5_matrix_boundary.md`: short all-order boundary reduction and exact averaging obstruction.
3. `round5_rank2.md`: exact formulation, profile localization, closure, and remaining gaps.
4. `round5_rank2_closure_audit.md` and `round5_scalar_independent_audit.md`: independent AI proof audits.
5. `round5_combinatorial.md`: the multivariate Lorentzian route and the interpolation obstructions.
6. `round5_fock_capacity_obstruction.md`: the exact order-50 refutation of the scaling shortcut.

The round-4 scalar proof, its independent audit, and rank-two identities are included as mathematical dependencies. The round-3 deletion implementation and earlier permanent helper source are included only to reproduce this round's numerical scripts.

## Verification and reproduction

The standard-library exact checker is:

```bash
python3 round5_verify.py
```

Run it from the extracted package directory and do not use `python -O`, which disables assertions. It checks exact rational identities and examples, including:

- 405 Poisson-binomial laws with integer means in orders 2–10;
- 28 two-column matrix identity examples;
- 184 four-block doubly stochastic matrices in orders 2–8, including boundary parameters and independent row and column relabelings;
- six row-pair affine polynomial identities;
- the explicit averaging, repeated-column, arbitrary-column deletion, coefficient-interpolation, and order-50 Fock-capacity obstructions.

All assertions passed. `round5_VERIFICATION.json` records the output. **These finite checks do not prove the all-order theorems.** The quantified proofs are in the mathematical notes. No Lean files or proof-assistant verification are supplied in this round.

The numerical investigations use NumPy and SciPy. Examples:

```bash
python3 round5_rank2_profiles.py
python3 round5_rank2_deletion_probe.py --mode zero
python3 round5_rank2_deletion_probe.py --mode profiles
python3 round5_combinatorial.py --n 3
python3 round5_combinatorial.py --n 4
OPENBLAS_NUM_THREADS=1 python3 round5_support_paths.py --n 5 --width 9 --depth 45
python3 round5_support_comparisons.py
```

For the structural matrix search, first build the included permanent helper:

```bash
g++ -O3 -shared -fPIC ratio_search.cpp -o permanent_numeric.so
python3 round5_structural_probe.py
```

For the shifted-binomial profile search recorded through order 22:

```bash
g++ -O3 -std=c++17 round5_rank2_profile_min.cpp -o round5_rank2_profile_min
./round5_rank2_profile_min 16 22
```

The recorded profile run covered 175,574 ordered profile pairs and logged 5,723,130 initial trial means, plus local refinements. It did not certify every parameter value and is not a general proof. The saved JSON files likewise distinguish exact combinatorial support checks from numerical balancing and norm evaluation.

The archive contains source and records, not compiled binaries or environment caches. `SHA256SUMS.txt` hashes the package files; `PACKAGE_MANIFEST.json` records their sizes and hashes.

## Sources, credit, and review status

The source repository currently reports the general order-four strong inequality as proved by Chris Ozols's project and the unrestricted problem in higher orders as open. This package does not claim a new unrestricted order-four result. Read on 2026-10-26:

- [dvgyl/gyires-circulant-5 README](https://github.com/dvgyl/gyires-circulant-5/blob/main/README.md), content SHA `ea99cedb91ae60ba933a6544c1365409875cac33`.
- [cozuya/gyires-permanent-4x4 README](https://github.com/cozuya/gyires-permanent-4x4/blob/main/README.md), content SHA `11a57f4a7373f898f9b3d31d8bc96a95ab363906`. Its finite certificate uses `native_decide`; that project's trust model should be read separately.

Classical ingredients are credited where used, including Hoeffding's fixed-mean shifted-binomial extremal reduction, Newton's inequalities, Schur–Szegő composition, and Brändén–Huh's Lorentzian theory. A limited primary-source search did not establish historical priority for the derived likelihood comparison or its matrix consequence. **No novelty or priority claim is made.**

These notes and scripts were developed by ChatGPT in response to the user's request, with parallel AI agents and cross-checks of the mathematical derivations. The audits are independent AI derivations, not human specialist peer review. No result in this new package has been formalized in Lean. The user's GitHub repository was not modified or published to during this round.
