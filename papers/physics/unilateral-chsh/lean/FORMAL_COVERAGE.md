# Formal coverage

All declarations below are in the namespace `UnilateralCHSH.Quantum` unless stated otherwise. Every endpoint assumes only that `ρ : State` (a complex 4×4 matrix indexed by `Fin 2 × Fin 2`) is positive semidefinite with trace one. Values are squares of the CHSH expectation divided by two, so the local bound is 1.

| Manuscript statement | Declaration (module) |
| --- | --- |
| Result A: exact one-sided suprema for Alice and Bob over invertible complex filters and arbitrary traceless Hermitian involutive observables | `all_states_operator_both_isLUB` (QuantumObservableValues); the vector form `all_states_both_isLUB` (AllStates) |
| Approximation of the supremum by invertible filters | `all_states_alice_approximation`, `all_states_bob_approximation` (AllStates) |
| Pure filtered marginal: value `|b|²`, attained | `pure_marginal_gl_isGreatest` (QuantumPureMarginal) |
| Result B: least-eigenvalue (Schur) formula for `α > 1`, with `det K ≠ 0`, a least eigenpair and an attaining invertible filter | `all_states_alice_schur_formula` (AllStates); canonical form `canonical_reduced_shortcut`, `canonical_physical_shortcut` |
| Result C: one-sided violation criterion | `all_states_alice_operator_activation_iff`, `all_states_bob_operator_activation_iff` (QuantumObservableValues) |
| Hidden one-sided activation (original state nonviolating) | `all_states_alice_operator_hidden_activation_iff`, `all_states_bob_operator_hidden_activation_iff` |
| Invertible attainment whenever violation is possible | `all_states_alice_operator_violation_attained`, `all_states_bob_operator_violation_attained` |
| Result D: at most four candidates (boundary value and eligible spectral levels) | `original_finite_candidates` (AllStates); `UnilateralCHSH.Global.maximum_isGreatest_candidates`, `candidateValues_ncard_le_four` (GlobalFinite) |
| Compact attainment and Lagrange conditions from actual maximality | `UnilateralCHSH.Global.exists_global_maximum`, `interior_maximum_kkt` (GlobalOptimization) |
| Reduction of every filter and measurement plane to the compact problem | `UnilateralCHSH.Reduction.exact_real_filter_maximum`, `positive_filter_optimality_iff` (FilterReduction) |
| Horodecki plane formula with attaining measurements | `UnilateralCHSH.Horodecki.exact_chsh_bound` (Horodecki) |
| Observables are unit Bloch spins | `isSpinObservable_iff_unit_realSpin` (QuantumCHSH) |
| Filtered states are density matrices | `filtered_trace_positive`, `normalizedFiltered_density` (QuantumGLPhysical) |
| Whitening in explicit coordinates and orbit equality | `original_filter_orbit_explicit` (QuantumWhiteningOrbit), `whitened_bob_formula`, `whitened_correlation_formula` (QuantumFilterCoordinates) |
| Bob's measure from an actual index swap | `bobGLValues_eq_alice_swap` (QuantumSwap) |

Not formalized (conventional proofs in the manuscript): the secular-root construction of the boundary radius and its hard case, the explicit cubic and admissibility tests, the polynomial activation tests and rational cubic, the threshold regimes, the rank-two formula, the `sqrt 2` characterization, the axial and quasi-distillable families, the success-probability results and the stability results.
