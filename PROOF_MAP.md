# Formal statement map

This map describes the mathematical source. A local Lean 4.35.0 source replay
compiled the complete proof. Full Palomar preflight remains required.
Earlier verification claims do not certify the changed package.

Every declaration below is in namespace `Milne`. The verification script checks the complete list in `audit_theorems.txt` and prints each transitive axiom set. The accepted foundations are exactly `propext`, `Classical.choice`, and `Quot.sound`.

`CMatrix` is `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ`. `Density M` means positive semidefiniteness and trace one. `partialA` traces out Bob, and `partialB` traces out Alice. `correlationSq` is the sum of squares of the nine real Pauli correlations. `steeringValue` is its nonnegative square root.

For an invertible Bob marginal, `steeringCenter M hM` is the Alice Bloch length after conjugation by the inverse of the positive square root of twice Bob's marginal. For a singular Bob marginal it is Alice's original Bloch length. This definition includes the point steering ellipsoid. The theorem statements do not supply the centre or positivity as unexplained scalar data.

| Declaration | File | Content and scope |
| --- | --- | --- |
| `canonical_operator_bound` | `MilneCore` | Actual canonical density matrix is bounded above by `(1 − c/2) I`. |
| `canonical_purity_bound` | `MilneCore` | Canonical purity is at most `1 − c + c²/2`. |
| `purityDifference_filter` | `MilnePurityCovariance` | Exact determinant covariance on all complex matrices and filters, without positivity or invertibility assumptions. |
| `correlationSq_purityDifference` | `MilneCorrelation` | Physical Pauli correlation identity for density matrices. |
| `canonicalize_reconstruction` | `MilneCanonicalization` | Positive canonical filter reconstructs every state with nonsingular Bob marginal. |
| `filtered_alice_bloch_bound` | `MilneSteering` | Alice's filtered Bloch square is at most `[c + (1 − c)r]²`. |
| `arbitrary_steering_bound` | `MilneSteering` | Exact envelope for any density matrix with nonsingular Bob marginal and its computed canonical centre. |
| `singular_Bob_support` | `MilneSingular` | Positivity forces support on the rank-one Bob marginal. |
| `singular_Bob_entangled_overlap_bound` | `MilneSingular` | Every maximally entangled overlap is at most `1/2` at a singular Bob marginal. |
| `singular_Bob_blochSq` | `MilneSingular` | Singular trace-one Bob marginal has Bloch square one. |
| `singular_Bob_purityDifference_zero` | `MilneSingular` | The conditional purity polynomial vanishes at that boundary. |
| `all_states_steering_bound` | `MilneAllStates` | Universal bound `correlationSq M ≤ G(steeringCenter M hM)` in both marginal-rank cases. |
| `steeringEnvelope_attained` | `MilneSharpness` | Explicit density matrix with computed centre `c` attains `G(c)` for `0 ≤ c < 2/3`. |
| `steeringEnvelope_supremum` | `MilneSharpness` | For `2/3 ≤ c ≤ 1` and every positive epsilon, an actual nonsingular-marginal density matrix of centre `c` has value above `G(c) − epsilon`. |
| `steeringEnvelope_isLUB` | `MilneOptimality` | For every `c ∈ [0,1]`, `G(c)` is the least upper bound of actual squared correlation values at that centre. |
| `three_setting_violation_possible_iff` | `MilneOptimality` | A density matrix of centre `c` with `steeringValue > 1` exists exactly when `c < 2/3`, for `c ∈ [0,1]`. |
| `no_maximizer_on_flat_branch` | `MilneNonattainment` | Every state with centre in `[2/3,1)` has squared value strictly below one. |
| `steeringEndpoint_isGreatest` | `MilneFractionOptimality` | At `c = 1`, squared value one is an attained maximum. |
| `all_states_entangled_overlap_bound` | `MilneAllStates` | Every actual maximally entangled vector has overlap at most `1 − c/2`, for all density matrices. |
| `fullyEntangledFraction_bound` | `MilneFractionOptimality` | The supremum of actual maximally entangled overlaps is at most `1 − c/2`. |
| `fullyEntangledFraction_isGreatest` | `MilneFractionOptimality` | For each `c ∈ [0,1]`, `1 − c/2` is an attained maximum over density matrices of computed centre `c`. |
| `entangledFractionEnvelope_isGreatest` | `MilneFractionOptimality` | Named wrapper of the same exact maximum theorem. |
| `decimal_threshold_counterexample` | `MilneSharpness` | An actual state has centre `53/80` and squared value `1512/1511`. This distinguishes the exact threshold from the rounded decimal `0.66`. |

`MaximallyEntangled v` requires both marginals of `pure v` to equal `I/2`; normalization follows from their trace. `fullyEntangledFraction` is an `sSup` over these actual overlaps. Nonemptiness and boundedness are proved before the conditional supremum lemmas are used. The extremal theorem establishes membership, not merely an upper bound on a relaxation.

The optimized CJWR measurement interpretation and the steering-ellipsoid interpretation use the cited physics literature. The formalization does not define local hidden-state models, optimize measurement settings, or characterize general steerability. The proof sources establish the precise matrix theorems above.
