# Gyires conjecture: fourth research checkpoint

26 October 2026. Continuation of the work starting from
https://github.com/dvgyl/gyires-circulant-5.

## Status

**The unrestricted Gyires conjecture is not proved or disproved here.**

This checkpoint contains a proved all-order matrix family, a stronger scalar
ultra-log-concave theorem, local results for the unrestricted stable/Lorentzian
classes, a global boundary reduction, and exact obstructions to several proposed
ways of completing the induction. The numerical searches are exploratory and
are clearly separated from proofs. No claim of priority in the literature or
formal proof-assistant verification is made.

For a nonnegative doubly stochastic matrix A of order n, put c_n=n!/n^n.
The original conjecture is

\[
4\operatorname{per}(A)^2\ge c_n\bigl(
\operatorname{per}(AA^T)+\operatorname{per}(A^TA)
+2\operatorname{per}(A^2)\bigr),
\]

with equality only at the matrix J_n whose entries are 1/n.

The stronger sufficient inequality studied here is

\[
\operatorname{per}(A)^2\ge c_n\operatorname{per}(AA^T).
\]

Applying it to A and A^T, then using permanent Cauchy--Schwarz, proves the
original inequality. A failure of an auxiliary polynomial statement is not
automatically a failure of either matrix statement.

## 1. Main proved all-order matrix theorem

If A has n-1 identical columns, or n-1 identical rows, then both

\[
\operatorname{per}(A)^2\ge c_n\operatorname{per}(AA^T),\qquad
\operatorname{per}(A)^2\ge c_n\operatorname{per}(A^TA)
\]

hold in every order n>=2. Consequently the original conjecture holds for this
family, with equality only at J_n.

For the column version, the full family is

\[
A_{i1}=u_i,\qquad A_{ij}=\frac{1-u_i}{n-1}\quad(j\ge2),
\qquad u_i\ge0,\quad\sum_i u_i=1.
\]

The vector u is arbitrary subject to these conditions; the result is not
restricted to a one-parameter symmetric segment. Column/row relabeling and
transposition are covered in the proof. This does not establish the conjecture
for arbitrary rank-two matrices.

Read **round4_one_special_matrix.md** and its independent review
**round4_one_special_matrix_audit.md**.

## 2. The scalar theorem behind the matrix result

Let B be Bin(n,1/n). If P is a probability law on {0,...,n} with mean one and
r_k=P_k/B_k is log-concave with interval support, then

\[
\sum_{k=0}^n B_k r_k^2\le r_1^2.
\]

Equality holds only at P=B. This is proved for every n>=2, including boundary
distributions. The proof first localizes the maximization to geometrically
tilted binomials truncated to initial intervals. It then bounds the balancing
tilt by t_L-1<=1/L! and compares the squared-norm excess with the removed tail.

For a homogeneous polynomial p, define

\[
N(p)=\sum_{|\alpha|=n}\alpha!p_\alpha^2.
\]

The scalar theorem proves the stronger polynomial inequality

\[
p_{(1,\ldots,1)}^2\ge c_nN(p)
\]

for every normalized balanced Lorentzian polynomial of the form

\[
p(x)=\sum_{k=0}^n a_kx_1^k(x_2+\cdots+x_n)^{n-k}.
\]

The first matrix Gram inequality is a special case. The transpose Gram
inequality has a separate elementary proof using the exactly-one-success
probability Q of independent Bernoulli(u_i) variables and a=sum u_i^2:

\[
Q\ge a,\qquad Q^2\ge g_n^2e^{a-1/n},\qquad
g_n=((n-1)/n)^{n-1}.
\]

These bounds dominate the explicit required function

\[
R_n(a)=n^{1-n}(n-2+a)^{n-2}(n-1-na+na^2).
\]

Read **round4_scalar_ulc.md** and
**round4_scalar_ulc_independent_audit.md**.

## 3. Local results without the special form

For every degree n, the polynomial norm target and the average
capacity-balanced deletion inequality hold strictly in some punctured
neighborhood of p_0=((sum x_i)/n)^n among normalized balanced stable
polynomials. The statements extend to balanced Lorentzian polynomials, without
the same explicit sharp constants.

For the stable class, all normalized first-order tangent directions are

\[
h=-R^{n-2}x^TBx,\qquad B\succeq0,\quad B\mathbf1=0.
\]

Their first variations are strictly favorable, and a compactness argument
upgrades this to a neighborhood theorem for arbitrary approaching sequences.
The proofs include sharp asymptotic constants in Fischer distance, a global
variance-deficit parameter, and exact second variations. The deletion ratio is
not globally monotone under uniform mixing, and it is not convex along the
straight stable tangent rays in degrees at least three.

Read **round4_local.md**. The finite-difference script
**round4_local_check.py** checks arithmetic, not the neighborhood theorem.

## 4. Global boundary reduction, with a genuine remaining boundary problem

For a balanced Lorentzian polynomial p, let m=min_i p_(n e_i). Then
p-m(sum x_i)^n is nonnegative, balanced up to normalization, Lorentzian, and has
at least one zero pure-power coefficient. The proof uses normalized coefficient
log-concavity and the subtraction of a positive rank-one matrix from each
quadratic derivative Hessian.

The desired norm inequality defines a convex cone, and the uniform power lies
on its boundary. Therefore a counterexample in the balanced Lorentzian class
would imply one on the zero-pure-coefficient boundary. This is a sufficient
global reduction; it does not solve that boundary problem. Subtraction need not
preserve real stability in arbitrary degree. The stable ternary cubic case has
a separate preservation proof.

Read **round4_analytic.md**, together with the boundary discussion in
**round4_local.md**.

## 5. Exact obstructions to proposed completion steps

### Deleting a zero-pure coordinate does not always give the needed bound

The rational doubly stochastic matrix

\[
\frac1{7200}\begin{pmatrix}
0&24&4479&2697\\
2697&16&16&4471\\
1806&2689&2689&16\\
2697&4471&16&16
\end{pmatrix}
\]

has only one zero entry. Its product polynomial has only one missing degree-four
monomial, x_1^4. Nevertheless the capacity-balanced deletion of coordinate one
satisfies

\[
0.9555806993<\frac{H_1}{g_4N(p)}<0.9558746601<1.
\]

Thus even taking the maximum only over zero-pure coordinates fails. The matrix
itself satisfies both strong Gram inequalities and original Gyires, checked
exactly. The base example with denominator 8 has a simpler quartic capacity
root and ratio about 0.94975859.

Read **round4_combinatorial.md**. Reproduce the rational certificates with
**round4_zero_pure_certificate.py**.

### Marginal ULC and binary coefficient inequalities are insufficient

Set

\[
p_t=(x+y)(y+z)(z+x)+t(x-y)(x-z)(y-z).
\]

For |t|<1, coefficients are nonnegative and balance is preserved. All coordinate
marginals are unchanged. The binary coefficient-line log-concavity inequalities
hold, but each quadratic derivative Hessian has determinant -64t^2 and two
positive eigenvalues for t!=0. At t=1/2,

\[
[xyz]p_t=2,\quad N(p_t)=19,\quad (2/9)N(p_t)>4.
\]

This is a counterexample only to the weaker marginal/binary class, not to the
Lorentzian or matrix claims. The same example exhibits the second-order
range--kernel obstruction to directly transferring scalar localization.

Read **round4_multivariate_localization.md**. Reproduce its exact polynomial
identities with **round4_localization_obstruction.py**.

## 6. Rank-two frontier

**round4_rank2_localization.md** gives an exact reformulation through two
Poisson-binomial likelihood ratios with the same mean and a binomial noise
operator. A sufficient extension to all ULC laws can be localized to pairs of
geometric binomial tilts restricted to intervals. The resulting two-interval
inequality is **unproved**. Numerical probes do not establish it.

**round4_rank2_identity_check.py** verifies the permanent and noise identities
over exact rational numbers in three examples, including a noninteger mean.

Even proving this additional scalar inequality would address rank-two matrices,
not the full arbitrary-rank conjecture.

## Reproduction

Run the decisive exact checks, using only Python's standard library:

```sh
python3 round4_verify.py --exact-only
```

With NumPy and SciPy installed, also reproduce the local derivative arithmetic:

```sh
python3 round4_verify.py
```

The verification report is **round4_VERIFICATION.json**. It includes a formal
polynomial identity check for the transpose-Gram proof and exact identity
checks on 28 rational matrix examples. The all-order conclusions come from the
written proofs, not from these finite examples.

The exploratory search scripts require NumPy/SciPy. The nested-product and
Lorentzian barrier searches also need the included C++ kernel built locally:

```sh
g++ -O3 -std=c++17 -shared -fPIC round4_nested_product.cpp -o round4_nested_product.so
```

Compiled binaries and Python caches are intentionally absent from this source
archive. The support module round3_deletion_probe.py is included because the
quartic/quintic exploratory scripts import its polynomial utilities.

The files from failed SLSQP attempts retain their feasibility flags. Invalid
optimizer outputs must not be interpreted as counterexamples. Later barrier
runs maintain feasible Hessian signatures; they still provide numerical
evidence only. No general theorem is inferred from the number of passed runs.

## Background references

- The original statement and current project context:
  https://yair-lavi.com/mincs-list/conjecture-20/index.html
- Branden and Huh, *Lorentzian polynomials*, Annals of Mathematics 192 (2020),
  821--891. Used for the standard Hessian/support characterization and closure
  properties:
  https://annals.math.princeton.edu/wp-content/uploads/annals-v192-n3-p04-s.pdf

The new arguments, countercertificates, and limitations are documented in the
notes above. No changes have been published to the linked GitHub repository.
