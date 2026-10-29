# Formalization map

This map describes the mathematical source. The Lean 4.35.0 port is uncompiled.
Earlier verification claims do not certify this candidate.

The finite model uses an arbitrary finite type and a permutation that forms one cycle on the whole type. It therefore covers every finite ring size at least three. No bound on the cycle size is built into the proof.

| Manuscript claim | Lean declaration or written proof | Boundary |
|---|---|---|
| Actual column generator and counted-edge tilt | `UnicyclicDeterminant.rateMatrix`, `UnicyclicDeterminant.edgeTilt`, `UnicyclicWinding.tiltedCharacteristic` | Positive original rates; diagonal escape terms do not change under the tilt |
| Counted-edge determinant separation | `UnicyclicDeterminant.rateMatrix_determinant_tilt` | At least three states |
| Positive midpoint spectrum from rates | `UnicyclicDeterminant.positive_rate_spectral_factorization` | Unequal forward and reverse rate products |
| Stationary distribution and first corrector | `UnicyclicConstruction.exists_stationary_corrector` | Constructed from positive rates and positive orientation |
| Second corrector and variance identity | `UnicyclicPoisson.exists_two_coefficients` | Finite cyclic Poisson equations |
| Rate-affinity uncertainty inequality | `UnicyclicPoisson.edgeQuadratic_tur` | Derived, not an extra hypothesis of the principal theorem |
| Characteristic coefficient identification | `UnicyclicRateJets.coefficient_equations_from_poisson` | Uses an adjugate residual identity |
| Exact polynomial inequality | `UnicyclicScalar.scalar_lower` | Complete coverage of `[0,1]²` under the stated constraint; its internal polynomial certificates cover `[27/50,1]` |
| Either affinity sign, every local C³ branch | `UnicyclicWinding.winding_skewness_interval` | Positive rates, at least three states, unequal rate products, one marked edge |
| Existence and interval from rates alone | `UnicyclicWinding.exists_winding_branch_and_interval` | Proves a branch exists, so the preceding branch condition is not vacuous |
| Two-state distinguished-channel interval | `UnicyclicTwoState.two_state_winding_interval` and `UnicyclicTwoState.exists_two_state_winding_branch_and_interval` | Separate two-channel matrix |
| One-state counted-event derivative ratio | `UnicyclicPoissonBoundary.poisson_winding_skewness` | Nonzero forward-minus-reverse rate |
| Long-time stochastic cumulants | Manuscript, Section 3 | Conventional spectral-projection proof; not a Lean path-space theorem |
| Universal sharpness | Manuscript, Section 8 | Conventional limit through positive rates and increasing ring size; not a Lean infimum/supremum theorem |

At equal rate products, the mean winding current vanishes. The literal ratio is undefined and is excluded. Rings with dangling trees or additional cycles are outside this model.

The finite exact certificate is not a finite-size check of the Markov theorem. Its polynomial identities prove a continuous scalar inequality used by the all-size theorem.
