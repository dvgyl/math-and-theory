# An exact circulant upper-bound witness for the ADMM dual stepsize

> Historical discovery record. The status statements below describe a stage
> when the central Lean formalization was still pending, and are retained as
> provenance. The current build status is reported separately in
> `../verification/fresh/verification.json`; this note does not assert that
> the final build has passed.

## Status and scope

This is an exact-arithmetic mathematical certificate, not yet a Lean certificate.
It gives an upper bound on the universal convergence range; it does not identify
the sharp threshold. The earlier user repository already contains an ADMM
five-cycle valid from approximately 1.98353554 onward. An earlier user thread
also already proves universal convergence through 7/4. Those results are prior
work for the present investigation.

The new candidate was located by floating-point Fourier optimization, but the
certificate below is accepted using integers and rational numbers only. No
floating-point feasibility status is used in its mathematical verification.

## Precise statement certified by the data

Put

\[
\tau_0=\frac{897744153596994489}{475778439151265168}
       \approx 1.8868954112306315.
\]

There are two fixed, nonempty, compact convex polytopes C,D in R^128, with
0 in C intersection D, such that for every real tau at least tau_0 the
multiplier-relaxed two-block ADMM for

\[
\min_{x=z}\;\iota_C(x)+\iota_D(z)
\]

has a nonconstant periodic trajectory. This is the update

\[
x_i=\operatorname{proj}_C(z_{i-1}-u_{i-1}),\qquad
z_i=\operatorname{proj}_D(x_i+u_{i-1}),\qquad
u_i=u_{i-1}+\tau(x_i-z_i),
\]

with penalty parameter one. It is not an assertion about other algorithms
also called relaxed ADMM that change the primal argument in a different way.

## The exact construction

The JSON file `exact_cycle_18869_10000_K128.json` contains two length-128
integer arrays z and v. Let T be the left cyclic coordinate shift, so T^128=I.
Define

\[
x=z+v-T^{-1}v,\qquad
C=\operatorname{conv}\{T^i x:0\le i<128\},\qquad
D=\operatorname{conv}\{T^i z:0\le i<128\}.
\]

Set z_i=T^i z, v_i=T^i v, x_i=T^i x, and u_i=tau v_i. The starting
state can be any member of this periodic sequence.

Both base arrays sum to zero, so averaging their cyclic shifts gives zero.
The same is true of x. Thus 0 belongs to both polytopes, and the original
optimization problem is feasible and has a primal-dual solution (0,0,0).

For each j=1,...,127, the checker verifies

\[
\begin{aligned}
\langle T^{-1}z-\tau T^{-1}v-x,\;x-T^j x\rangle&\ge0,\\
\langle x+\tau T^{-1}v-z,\;z-T^j z\rangle&\ge0.
\end{aligned}
\]

These are precisely the normal inequalities characterizing the two Euclidean
projections. They hold at every vertex and hence everywhere on the convex
hull. Applying T^i preserves inner products, so the inequalities certify every
step of the entire cycle.

For completeness, if p is in a convex set K and
\(\langle y-p,w-p\rangle\le0\) for all w in K, then

\[
\|y-w\|^2
=\|y-p\|^2+\|w-p\|^2-2\langle y-p,w-p\rangle
\ge\|y-p\|^2+\|w-p\|^2.
\]

Therefore p is the unique Euclidean projection of y. Strict inequalities at
distinct vertices are not required. This matters at the exact endpoint tau_0.

The dual update is an identity because x_i-z_i=v_i-v_(i-1). The z orbit is
nonconstant: the base vector z has mean zero but positive squared norm.
Consequently a periodic z orbit cannot converge. Also

\[
\|x_i-z_i\|^2
=16383999960516622876672>0
\]

at every iteration, providing a separate exact obstruction to feasibility
residual convergence.

## Why one example works for every tau at least tau_0

Every displayed normal margin is affine in tau, with an integer intercept
and an integer slope. The checker verifies that all 254 slopes are
nonnegative. The largest required lower endpoint is tau_0, attained by the
f-side inequality with offset j=3. At tau_0 all margins are verified
nonnegative by exact rational arithmetic. Hence every larger tau is valid
for the same two polytopes (the dual initialization changes as u=tau v).

For the convenient rational parameter 18869/10000, after clearing its
denominator, the least f-side margin is 357701636547624828928 and the least
g-side margin is 357675255055329427456. These large integers arise from a
common scaling of the construction and do not claim a meaningful geometric
condition number or robustness radius.

## Reproduction

The independent verification path needs only the Python standard library:

```bash
python second-round/spectral/admm/exact_circulant_cycle.py \
  --check second-round/spectral/admm/exact_cycle_18869_10000_K128.json
```

The optional candidate-generation path uses the pinned numerical dependencies
in `requirements.txt`. It factors Fourier Gram matrices, projects each block
onto rank one, rounds coordinates, and centers the arrays exactly. Each of
these operations is merely candidate generation. The resulting candidate is
retained only if the exact integer checker proves all required inequalities.

The finite-frequency optimization data, including primal Gram blocks and dual
multipliers, are preserved in `fourier_residual_boundary.json`. The broader
period-boundary numerical diagnostics are in `period_boundaries.json`.

## Limitations

This note does not establish novelty against all literature by itself. It
does not prove convergence below tau_0 and does not claim that the actual
sharp threshold equals the numerical Fourier transition near 1.88688. The
128-cycle may have a smaller minimal period; exact period 128 is unnecessary
for nonconvergence. A central Lean formalization remains required before
presenting this as a fully verified successful research result.
