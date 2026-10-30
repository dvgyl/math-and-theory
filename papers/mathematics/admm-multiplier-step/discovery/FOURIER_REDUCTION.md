# Why the cyclic Fourier search addresses every fixed-period convex ADMM orbit

> Historical discovery-method record. References to ongoing formal verification
> describe the stage when this note was written. Current central-theorem status
> is recorded in `../verification/fresh/verification.json`. The Fourier search
> reduction itself is explanatory mathematics, not a premise of the final
> exact certificates or a claimed Lean-formalized theorem.

This is a mathematical explanation of the discovery reduction. The accepted
lower bounds and the exact integer counterexample are verified independently;
their validity does not depend on the floating-point searches described here.

## Convex functions can be replaced by orbit polytopes for cycle search

Suppose a multiplier-only ADMM trajectory has period K. Write v_i=u_i/tau,
with indices taken modulo K. Its two sampled primal points and normals are

\[
x_i=z_i+v_i-v_{i-1},\qquad
a_i=z_{i-1}-\tau v_{i-1}-x_i\in\partial f(x_i),\qquad
b_i=x_i+\tau v_{i-1}-z_i\in\partial g(z_i).
\]

Form the direct sums of all cyclic time shifts, for example

\[
\widehat x_i=(x_i,x_{i+1},\ldots,x_{i+K-1}),
\quad
\widehat a_i=(a_i,a_{i+1},\ldots,a_{i+K-1}).
\]

For every i,j, convexity gives

\[
\begin{aligned}
\langle\widehat a_i,\widehat x_j-\widehat x_i\rangle
&=\sum_{\ell=0}^{K-1}\langle a_{i+\ell},x_{j+\ell}-x_{i+\ell}\rangle\\
&\le\sum_{\ell=0}^{K-1}\bigl(f(x_{j+\ell})-f(x_{i+\ell})\bigr)=0.
\end{aligned}
\]

The final equality is cancellation of the same K function values. The
corresponding inequality holds for the g block. Consequently the direct-sum
points are exact projections onto their orbit polytopes, and they satisfy
the same ADMM recurrence coordinate by coordinate. The polytope orbit has
the same stepsize and remains nonconstant if the original orbit was
nonconstant.

Thus restricting a search for K-periodic obstructions to indicator functions
of orbit polytopes loses no possible obstruction, provided arbitrary ambient
dimension is allowed. This statement concerns finite periodic orbits. It does
not show that every failure of convergence is periodic.

The direct-sum cyclic shift is an orthogonal operator T with T^K=I. Averaging
the states removes its fixed subspace. In particular, the mean x and mean z
coincide because the multiplier increments telescope. Subtracting the means
does not change any of the normal margins: vectors in the fixed subspace are
orthogonal to differences of two orbit points. The centered orbit polytopes
therefore contain zero, providing an actual saddle point for the constructed
feasibility problem.

## Fourier mode formulas

Diagonalize T into its real Fourier subspaces. On a positive complex frequency
theta=2*pi*j/K, use r=exp(-i*theta), delta=1-r, c=1+(tau-1)r. If z,v are the
complex components of the two state vectors at that frequency, then

\[
x=z+\delta v,\qquad a=-\delta z-cv,\qquad b=cv.
\]

The Hermitian Gram block for z,v is

\[
H=\begin{pmatrix}\alpha&\gamma\\\overline\gamma&\beta\end{pmatrix},
\qquad
\alpha=\|z\|^2,\quad\beta=\|v\|^2,\quad\gamma=\langle z,v\rangle.
\]

Its realizability condition is H positive semidefinite, equivalently
alpha,beta nonnegative and |gamma|^2 at most alpha*beta. Writing gamma=p+iq,
this is the second-order cone condition

\[
\alpha+\beta\ge\sqrt{(\alpha-\beta)^2+4p^2+4q^2}.
\]

The two complex inner products relevant to the normals are

\[
\begin{aligned}
L_f&=-\overline\delta\alpha-|\delta|^2\gamma
      -\overline c\overline\gamma-\overline c\delta\beta,\\
L_g&=\overline c\overline\gamma.
\end{aligned}
\]

For each offset k=1,...,K-1, the complete polytope support conditions are

\[
\sum_j\operatorname{Re}\bigl[(1-e^{ik\theta_j})L_{f,j}\bigr]\ge0,
\qquad
\sum_j\operatorname{Re}\bigl[(1-e^{ik\theta_j})L_{g,j}\bigr]\ge0.
\]

They are linear in the entries of the Hermitian Gram blocks. The frequency
pi, when present, has real gamma; conjugate frequencies are represented by
one complex block with its Euclidean normalization absorbed into that block.
The zero frequency contributes neither margins nor residual and is omitted.

Conversely, any family of positive-semidefinite mode blocks satisfying these
inequalities factors into real Euclidean state vectors. The orbit polytopes
then give an actual ADMM cycle by the projection characterization. Therefore
these second-order cone constraints characterize possible centered cycles
of the specified period, independent of ambient dimension.

## Removing the trivial orbit

The useful normalization is

\[
\sum_j |1-e^{-i\theta_j}|^2\beta_j=1,
\]

which sets the squared primal residual to one. A nonconstant finite cycle
cannot have identically zero residual. Indeed, zero residual forces constant
v. Summing the f-side support inequalities comparing x_i=z_i with
x_(i-1)=z_(i-1) then gives

\[
0\le\sum_i\langle z_{i-1}-z_i-\tau v,\;z_i-z_{i-1}\rangle
=-\sum_i\|z_i-z_{i-1}\|^2,
\]

so z is constant too. Thus residual normalization excludes exactly the
irrelevant constant solutions when searching for genuine periodic failures.

## What the computation establishes, and what it does not

The numerical searches located cycles near tau=1.8869 and suggested a
limiting periodic obstruction threshold near 1.88688. Those approximate
thresholds are exploratory evidence. Neither a scan over periods nor an
approximately feasible cone program proves a universal convergence range.

The accepted upper bound instead comes from rounding a candidate into two
integer base vectors and checking every necessary support inequality exactly.
The accepted lower bound comes from separate finite-memory Lyapunov
certificates with exact nonnegative interpolation weights and positive
rational matrix factorizations. These two independently checkable objects,
rather than the numerical boundary estimates, are the research result under
formal verification.
