# Formal statement correspondence

This document distinguishes the actual algorithmic conclusions from intermediate algebraic certificates. The final verifier prints the central theorem types as well as their transitive axiom sets.

## Actual proximal minimization

`CPSharpness.IsProx C f c x` means that x belongs to C and globally minimizes `f(z) + (1/2)||z-c||^2` over every z in C. `Supports` is the usual convex subgradient inequality on the same domain. `supports_iff_isProx` proves their equivalence for convex functions. No assumed proximal selector occurs in the explicit examples: existence follows from compactness, and uniqueness is proved from convexity.

For a standard extended-valued proper convex function, take C to be its effective domain and f to be its finite values on C. Values of f outside C are irrelevant. The necessity theorem does not need a global existence theorem for a proximal map: its hypotheses are the six actual minimizations along a supposed three-cycle. For the counterexamples, global minimizers exist at every center.

## Exact three-cycle obstruction

`CPSharpness.step_product_three_cycle_polynomial_nonneg` has arbitrary complete real inner-product spaces, arbitrary bounded linear L, positive tau and sigma, nonnegative theta, convex functions on convex domains, six actual proximal-step equations, and a nonconstant full primal-dual state. Its conclusion is precisely

    (tau*sigma*||L||^2)^2*(1+theta)^2
      - 2*(tau*sigma*||L||^2)*(1+3*theta) - 3 >= 0.

It has neither a contraction hypothesis nor a nonzero-operator hypothesis. The proof handles L=0 separately. Normalization of the true steps and operator norm is verified in `GeneralSteps.lean`.

`threeCycle_sos_identity` is an intermediate identity. It is not presented alone as the algorithmic result: `ThreeCycleFunctions.lean` and `GeneralSteps.lean` derive every sign condition from the actual convex proximal updates.

`sharp_three_cycle_iff` states an exact existence equivalence for identity-coupling three-cycles in the formal R^3 model. Its sufficiency is realized by the explicit compact triangles. `sharp_three_cycle_counterexample` additionally bundles compactness, convexity, a saddle, the actual recurrence, and nonconvergence of the iterated globally defined map.

The universal necessity theorem and the explicit attainment together establish the universal exact period-three boundary. The formal example's ambient space is R^3, not literally R^2; the vertices all lie in the zero-sum plane.

## Seven-cycle and attraction

`FiniteCP.project` is chosen from actual global minimizers; `project_isProx` and uniqueness identify it as metric projection onto the stated finite convex hull. `FiniteCP.cpMap` applies these two projections in the exact CP order, with tau=1, sigma=kappa, L=I.

`SevenCP.strict_normal_certificate` proves every strict off-diagonal supporting inequality for all real parameters satisfying

    2499/1000 <= kappa <= 2501/1000,
    0 <= theta <= 1/400.

The source contains the integer coordinates. There are no certificates imported from a numerical oracle. `compact_saddle` proves convexity, compactness and the saddle (0,0). `actual_seven_cycle` proves equality of the actual iterates with the periodic orbit and absence of any norm limit. `below_three_cycle_and_quadratic` verifies both comparisons over the entire rectangle.

`seven_cycle_one_step_capture` proves that, in a neighborhood of each orbit state, all initial points have exactly the same iterates from the first update onward. `seven_cycle_open_basin` consequently proves nonconvergence in a full neighborhood in R^4 x R^4. The neighborhood is expressed using the standard neighborhood filter; its nonemptiness is not an extra premise. `rational_example_open_basin` specializes the theorem to kappa=5/2 and theta=1/1000, explicitly discharging every numerical premise.

The formal orbit is seven-periodic and nonconstant. Since seven is prime, its minimal period is seven by elementary periodicity; the separate minimal-period-number theorem is not needed for nonconvergence and is not named as a formal endpoint.

## Fourier family for every product above two

`AsymptoticCP.counterexamples_for_every_product_above_two` has only the final hypothesis `2 < kappa`. Its conclusion first chooses an integer N>=4, then a positive epsilon, and then proves the properties of the explicitly defined primal and dual finite hulls in `EuclideanSpace R (Fin 4)`. The quantifier over theta comes afterward. Thus the domains, vertices, and starting state are fixed throughout [0,epsilon], rather than selected separately for each theta.

The formal update is `FiniteCP.cpMap`: `x_next = project C (x-y)`, followed by `y_next = project D (y + kappa*((1+theta)*x_next-theta*x))`. This is exactly CP with L=I, tau=1, sigma=kappa; the identity has norm one on this nonzero Euclidean space. `project_isProx` proves that these global maps are the actual indicator proximal minimizers. No extrapolation-dependent objective or fitted finite-only map is used.

The construction chain is fully discharged:

1. `FourierModes.lean` defines two actual rotation modes and proves their full-period closure, including the last-to-first step.
2. `FourierAlgebra.lean` proves positivity, the constant dual squared norm M, and the exact supporting inner-product identity with its factor kappa.
3. `TrigSupport.lean` proves the polynomial inequality for the exceptional residue; `TrigGrid.fourier_support` proves the complete grid inequality without an assumed scalar-bound premise.
4. `FourierCertificates.lean` translates every off-diagonal vertex pair to a positive cyclic lag and proves the actual dual support bound. It proves x_0 != x_1 from the positive identity ||y_0||^2=M.
5. `FourierSums.lean` proves both vertex sums vanish, hence the origin belongs to both hulls. `FiniteCP.origin_saddle` supplies the actual saddle predicate, including membership.
6. `FourierRobustness.lean` bounds the positive-theta perturbation of the dual supporting values. The primal centers are already the desired vertices, because y_i=x_i-x_(i+1).
7. `AsymptoticParameters.lean` proves existence of an admissible period for every kappa>2. `AsymptoticCycle.lean` proves epsilon=sin(t)^3/M>0 and combines the chain into periodicity and failure of convergence of the actual iterates.

The final theorem contains no assumed support certificate, no unresolved trigonometric inequality, no nonconstancy premise, and no conditional solver certificate. The topology is the ordinary full Euclidean product topology. The stated period is 4N+3; its minimality is not claimed. The Fourier family does not have a formal open-basin endpoint.

The manuscript's limsup restriction is a direct consequence: for any a>2, the fixed-a example precludes a universal guarantee c(theta)>a for every sufficiently small positive theta. There is no separate formal `limsup` theorem in this package; the underlying quantified existence and nonconvergence theorem is formalized in full.

## Quadratic comparison

`CPQuadratic.IsCPEigenmode` is the pair of actual linear resolvent eigenmode equations, not an assumed scalar characteristic polynomial. `eigenmode_characteristic` derives the scalar polynomial by taking inner products, with the conjugations treated explicitly.

`cp_positive_quadratic_eigenmode_stable` proves that every nonzero mode has modulus below one for positive-definite self-adjoint Hessians and the stated parameter bound. `cp_nonnegative_quadratic_eigenmode_stable_or_one` covers positive-semidefinite Hessians and proves strict stability or the eigenvalue one, including zero primal or dual components.

The formal space is complex Hilbert space, appropriate for eigenmode analysis. Translating a finite-dimensional real Hessian to its complexification and invoking the matrix-power characterization of convergence are standard mathematical implications, but are not formalized here. In particular, the theorem for semidefinite Hessians is not advertised as a complete proof of convergence of their iterations.

## Trust and semantic review

The clean build checks the actual source files, with fresh local objects and pinned dependency versions. It cannot by itself establish originality, significance, or that an informal manuscript accurately describes the formal types. Those are separate questions. The independent AI referee checks described in the manuscript examined the sign conventions, original step-size product, existence of a saddle, nonconstant states, full-state topology, and positivity and satisfiability of the parameter hypotheses; they are not human peer review.
