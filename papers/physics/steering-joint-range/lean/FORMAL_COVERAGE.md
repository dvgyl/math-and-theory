# Formal coverage

Every theorem listed as complete below has a Lean proof in `Lean/` and is
covered by the whole-project axiom audit `Lean/MilneAxiomAudit.lean`. The
fresh build and audit of this release are recorded in `../verification/`.
All declarations are in namespace `Milne`.

## Conventions and actual objects

- `CMatrix` is a complex matrix indexed by `Fin 2 × Fin 2` in each dimension.
- `Density M` means `M.PosSemidef ∧ Matrix.trace M = 1`.
- `correlation M` consists of actual Pauli expectation values.
- `correlationSq M` is the sum of their squares; `steeringValue M` is its square root.
- `steeringCenter M hM` uses positive canonicalization when Bob is nonsingular
  and the point-centre convention when Bob is pure. The coordinate bridge is proved.
- `hermitianTraceNorm` is the sum of absolute real eigenvalues. This is the full
  trace norm. The usual trace distance is half this quantity.
- `localConjugate U V M` uses actual qubit unitaries.
- Physical filter and success-probability theorems quantify actual complex matrices.

## Complete central statements

| Result | Principal declarations | Actual formal domain and endpoints |
|---|---|---|
| Exact global envelope and 2/3 threshold | `steeringEnvelope_isLUB`, `three_setting_violation_possible_iff`, `no_maximizer_on_flat_branch` | Every actual two-qubit density matrix; all global ranks; pure Bob marginals treated separately. |
| Centre identity | `steeringCenter_coordinates`, `coordinate_steering_threshold` | Actual measured `(a-Tb)/(1-|b|²)` in the nonsingular Bob case; no inversion of the joint state. |
| Complete global maximizing orbits | `global_steering_equality_iff`, `global_endpoint_equality_iff` | Actual local unitary equivalence for c<2/3 and c=1. The baseline proves no maximizer in [2/3,1). Bob invertibility on the curved branch is derived from violation. |
| Unique optimal effect of the canonical maximizer | `alignedObese_optimal_effect`, `alignedObese_optimal_positive_filter` | Every normalized complex filter; exact three-dimensional completed square; PSD square-root uniqueness for the reconstruction filter. |
| Entire joint correlation interval | `jointSteeringSpectrum_eq_Icc`, `actual_joint_value_iff` | Exact equality between actual-density correlation values at specified c,r and `[max(0,c(1+r)-1)^2,H(c,r)]`, for r<1. Explicit density interpolation witnesses attain every value. |
| Joint lower bound | `arbitrary_joint_correlation_lower_bound`, `jointSteeringLower_isLeast` | Actual Density input and actual steering centre; no supplied scalar surrogate. |
| Lower endpoint equality | `joint_lower_equality_iff` | Necessary and sufficient equality in actual Bloch coordinates, including x=0 and zero local vectors. |
| Lower endpoint trace-norm rigidity | `joint_physical_trace_rigidity`, `arbitrary_joint_trace_rigidity` | Actual spectral norm of the difference from a certified physical reference. The arbitrary-state wrapper derives axes and centre identities internally. |
| Physical reference positivity | `jointLowerRotated_density` | Explicit positive product decomposition for all unit axes and 0<=c,r<=1; no inverse and no rank assumption. |
| Geometric PSD inequality | `all_density_geometry_matrix_psd` | Actual arbitrary density matrices, exact Pauli reconstruction and directional spin-flip identity. |
| Canonical full c,t interval | `geometryPhysicalSkewSpectrum_eq_interval`, `geometry_radial_lower_equality_iff` | Complete actual-state interval `[t²,1-c²+2t²]`; explicit PSD witnesses including c=1,t=0. |
| Constructive canonical normal form | `canonical_aligned_normal_form`, `canonical_positive_aligned_normal_form` | Two ordered qubit spectral diagonalizations; actual unitaries; repeated eigenvalues and zero coherence included. |
| Prescribed radial axis and upper equality | `physical_bob_radial_normal_form`, `physical_radial_equality_iff` | Arbitrary actual density matrices with Alice vector c ez and Bob vector zero. Bob-only normalization retains the marked Alice axis even at c=0. Algebraic equality conditions are complete, including t=0. |
| Canonical full equality and trace rigidity | `canonical_obese_equality_iff`, `canonical_hs_rigidity`, `canonical_trace_rigidity_capped` | Actual local unitaries and actual matrix norms. Canonical equality includes c=1; stability uses c<1 and the norm-diameter cap. |
| Success probability from actual filters | `canonicalKrausProbability_is_actual`, `normalizedKrausOutput_density`, `scaledKraus_admissible_iff`, `fixed_filter_maximal_success` | Actual complex contracting Kraus matrices, actual success trace, positive normalized output, and exact radius constraint. |
| Exact probability frontier | `successPhysicalSpectrum_isGreatest`, `successPhysicalSpectrum_violation_iff` | Optimization over all canonical input states of centre c and all admissible filters; success floor p in [1/2,1]; singular p=1/2 endpoint included. |
| All looser budgets | `successPhysicalSpectrum_low_probability`, `looseSuccessPhysicalSpectrum_isGreatest` | Same normalized-output spectrum for success floors at or below one half, and attained maximum. |
| Complete quadratic optimization | `trust_diagonal_exact_maximum`, `trust_global_optimum_iff_certificate` | Every real symmetric 3x3 quadratic on the ball. Existence and necessity of the PSD-shift certificate are derived, not assumed. |
| Finite spectral algorithm | `trust_spectral_finite_solution`, `canonical_filter_finite_spectral_solution`, `canonicalOrbitShiftCandidates_card` | Exactly degree-six polynomial, endpoint handling, unique admissible shift among at most seven candidates; no matrix invertibility hypothesis. |
| Every maximizing physical effect | `canonical_filter_all_maximizers`, `canonical_maximizing_effect_realized` | All normalized complex filters; complete nullspace/eigen-coordinate classification; explicit positive physical realization. |
| Literal F3 maxima and invertible limits | `canonical_F3_filter_isGreatest`, `canonical_invertible_F3_filter_isLUB`, `canonical_invertible_F3_attainment_iff` | Actual output F3, singular filters included; open-ball supremum and exact attainment iff, even for singular K. |
| Rank-safe signed volume inequalities | `alignedState_signed_determinant_bounds`, `physical_radial_signed_determinant_bounds` | PSD row tests and measured actual density coordinates; no inverse or positive-diagonal assumption. |
| Signed determinant invariance | `canonical_bloch_trace_cube`, `localConjugate_correlation_det` | Exact cubic Pauli trace identity and actual local unitaries; no assumed SO(3) representation. |
| Sharp radial and triple volume maxima | `physicalRadialVolumeSpectrum_isGreatest`, `physicalTripleVolumeSpectrum_isGreatest` | Every actual density matrix in the fixed marked-axis convention; explicit witnesses attain the cap at every feasible c,t,tau, including all singular endpoints. |

## Fixed-axis convention for the volume theorem

`physicalTripleVolumeSpectrum c t tau` is the set of `|det(correlation M)|` for
actual density matrices satisfying

```
geometryLocalA M = c • geometryEz
geometryLocalB M = 0
vSq (ttVec (correlation M) geometryEz) = t^2
correlationSq M = tau.
```

No X-state form, coherence bound, or row-positivity hypothesis is assumed in
this domain. The proof constructs a genuine Bob unitary reducing the arbitrary
matrix to radial normal form, transports positivity, proves signed determinant
invariance, applies the rank-safe inequality, and supplies a physical sharpness
witness. At c=0 the marked direction ez is retained. An arbitrary marked-axis
wording requires the coordinate rotation explained in the written proof; the
formal domain above is explicit.

Canonical and global LU equality classifications are basis independent and do
not have this marked-axis premise.

## Statements presented with written proofs, not standalone full Lean theorems

The manuscript gives conventional proofs of the following additional
consequences. They are not covered by the formal statements above:

- Attainment of every point of the **signed** determinant interval. Both signed
  inequalities and the sharp absolute radial/triple maxima are formalized.
- The entire piecewise local-unitary orbit classification of all volume
  maximizers, including opposite determinant signs, and all listed rank counts.
- Phase-gauge simplifications of fixed-radial algebraic equality conditions and
  detailed interpolation ranks. The exact algebraic equality iff is formalized.
- The sharp flat-branch distance exponents and their matching lower examples.
- Some ellipsoid-only/adjugate restatements and the prose composition of the
  optimal canonical filter with a preceding whitening step.
- Experimental measurement optimization and arbitrary-measurement steering or
  local-hidden-state models.
- Formal verification of the Python calculators as executable algorithms.

The global optimizer LU classification, canonical spectral trace-norm
rigidity and the full trust-region/orbit optimum, including the nonviolating
and hard cases, have complete matrix-level proofs.

## Checking the meaning of the statements

`MilneJointArbitraryStability`, written separately from the modules it
imports, restates the lower trace-norm estimate directly for arbitrary density
matrices and unpacks the exact joint interval into an existential
density-matrix statement (`actual_joint_value_iff`). It checks the
composition of positivity, centre coordinates, zero-direction handling and
spectral trace norms.

A successful build proves the stated Lean declarations, and the axiom audit
verifies that their transitive dependencies contain only the three standard
axioms. These checks do not establish novelty or priority and are not peer
review.
