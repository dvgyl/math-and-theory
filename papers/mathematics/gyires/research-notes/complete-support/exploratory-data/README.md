# Data for finite computational observations

I include these 70 JSON files with the manuscript appendix “Finite computational observations.” That appendix defines the quantities, methods, finite ranges, values, and limits.

Sixty-nine files contain computational output. One file contains numerical profile values extracted from a text record. These are stored finite observations. They do not establish the unrestricted Gyires inequality.

Some calculations use exact integers or fractions. Others use floating-point optimization or numerical balancing. The records include arithmetic and validity status, failed convergence, constraint residuals, and infeasible outputs where these fields are available. An infeasible output is not a counterexample. A reported local optimum is not a certified global optimum.

The records retain input arrays, support sets, extremizers, and numerical residuals when those fields were available. Some records contain only aggregate counts or selected extrema. They cannot reconstruct every sampled point. The manuscript states which reported computations lack detailed output.

In `rank_two_profiles_n16_through_n22.json`, noninteger values are strings. This preserves every printed decimal digit. `recorded_points` contains all 23 retained numerical evaluations. `completed_orders` contains the seven cumulative pair and evaluation counts. These are numerical values, not exact rational certificates.

## File index

| Scientific file | Contents |
|---|---|
| `balanced_stable_polynomial_deletion.json` | Polynomial deletion samples. |
| `circulant_deletion_n4_through_n7.json` | Circulant deletion searches. |
| `circulant_deletion_search_n10.json` | Circulant deletion searches. |
| `circulant_deletion_search_n12.json` | Circulant deletion searches. |
| `circulant_deletion_search_n14.json` | Circulant deletion searches. |
| `circulant_deletion_search_n16.json` | Circulant deletion searches. |
| `circulant_deletion_search_n8.json` | Circulant deletion searches. |
| `circulant_fourier_phase_search_n10.json` | Circulant ratio and phase searches. |
| `circulant_fourier_phase_search_n12.json` | Circulant ratio and phase searches. |
| `circulant_fourier_phase_search_n14.json` | Circulant ratio and phase searches. |
| `circulant_fourier_phase_search_n16.json` | Circulant ratio and phase searches. |
| `circulant_fourier_phase_search_n8.json` | Circulant ratio and phase searches. |
| `circulant_selected_chambers_n8.json` | Exact selected chambers. |
| `circulant_selected_chambers_n9.json` | Exact selected chambers. |
| `circulant_simplex_search_n10.json` | Circulant ratio and phase searches. |
| `circulant_simplex_search_n12.json` | Circulant ratio and phase searches. |
| `circulant_simplex_search_n14.json` | Circulant ratio and phase searches. |
| `circulant_simplex_search_n16.json` | Circulant ratio and phase searches. |
| `circulant_simplex_search_n8.json` | Circulant ratio and phase searches. |
| `configuration_bethe_estimates.json` | Configuration-model calculations. |
| `configuration_expectations_d2_d3_d4.json` | Configuration-model calculations. |
| `configuration_expectations_d5_d10_d20.json` | Configuration-model calculations. |
| `elementary_symmetric_expansion_checks.json` | Nested and repeated-variable deletion. |
| `generic_stable_polynomial_deletion.json` | Polynomial deletion samples. |
| `local_polynomial_variation_checks.json` | Local polynomial variation checks. |
| `lorentzian_cubic_boundary_search.json` | Lorentzian coefficient optimization. |
| `lorentzian_cubic_mixed_coefficient_search.json` | Lorentzian coefficient optimization. |
| `lorentzian_cubic_norm_and_deletion_search.json` | Lorentzian coefficient optimization. |
| `lorentzian_quartic_barrier_search.json` | Lorentzian coefficient optimization. |
| `lorentzian_quartic_boundary_search.json` | Lorentzian coefficient optimization. |
| `lorentzian_quartic_direct_search.json` | Lorentzian coefficient optimization. |
| `lorentzian_quintic_barrier_search.json` | Lorentzian coefficient optimization. |
| `matrix_ratio_search_n5.json` | Matrix ratio searches. |
| `matrix_ratio_search_n6.json` | Matrix ratio searches. |
| `matrix_ratio_search_n7.json` | Matrix ratio searches. |
| `matroid_polynomial_deletion.json` | Polynomial deletion samples. |
| `mconvex_cubic_supports.json` | M-convex support calculations. |
| `mconvex_quartic_inclusion_checks.json` | M-convex support calculations. |
| `mconvex_quartic_supports.json` | M-convex support calculations. |
| `mconvex_quintic_support_paths.json` | M-convex support calculations. |
| `mconvex_support_duplication_checks.json` | M-convex support calculations. |
| `minimum_fischer_norm_deletion_search.json` | Stochastic-complement and minimum-norm deletion. |
| `nested_deletion_coefficient_checks.json` | Nested and repeated-variable deletion. |
| `nested_deletion_d3_r3_average.json` | Nested and repeated-variable deletion. |
| `nested_deletion_d3_r5_prescribed_zero_pure.json` | Nested and repeated-variable deletion. |
| `nested_deletion_d3_r8_average.json` | Nested and repeated-variable deletion. |
| `nested_deletion_d4_r0_prescribed_zero_pure.json` | Nested and repeated-variable deletion. |
| `nested_deletion_d4_r6_average.json` | Nested and repeated-variable deletion. |
| `nested_deletion_d4_r6_average_linear.json` | Nested and repeated-variable deletion. |
| `nested_deletion_d5_r3_prescribed_zero_pure.json` | Nested and repeated-variable deletion. |
| `nested_deletion_d6_r2_prescribed_zero_pure.json` | Nested and repeated-variable deletion. |
| `nested_deletion_d6_r4_average.json` | Nested and repeated-variable deletion. |
| `nested_deletion_d8_r2_average.json` | Nested and repeated-variable deletion. |
| `nested_deletion_gradient_checks.json` | Nested and repeated-variable deletion. |
| `rank_two_arbitrary_column_deletion.json` | Scalar and rank-two diagnostics. |
| `rank_two_endpoint_and_duplication_search.json` | Scalar and rank-two diagnostics. |
| `rank_two_profile_zero_column_deletion.json` | Scalar and rank-two diagnostics. |
| `rank_two_profiles_n16_through_n22.json` | Scalar and rank-two diagnostics. |
| `rank_two_zero_column_deletion.json` | Scalar and rank-two diagnostics. |
| `repeated_variable_elementary_symmetric_tests.json` | Nested and repeated-variable deletion. |
| `stochastic_complement_initial_search.json` | Stochastic-complement and minimum-norm deletion. |
| `stochastic_complement_pivot_search.json` | Stochastic-complement and minimum-norm deletion. |
| `stochastic_complement_weighted_optimization.json` | Stochastic-complement and minimum-norm deletion. |
| `truncated_binomial_scalar_search.json` | Scalar and rank-two diagnostics. |
| `three_shift_binary_triples_n3_through_n100.json` | All seven nonzero binary triples in orders 3–100. |
| `three_shift_transfer_chambers_n5_through_n100.json` | Six transfer chambers in orders 5–100. |
| `three_shift_spectral_bernstein_certificate.json` | Ten Bernstein-polynomial minor certificates. |
| `three_exceptional_row_exact_checks.json` | Exact checks for three exceptional rows. |
| `circulant_order_eight_single_chamber.json` | One order-eight chamber, including its term counts. |
| `minimum_fischer_norm_order_fifty_obstruction.json` | Exact rational bounds for the order-fifty obstruction. |

## Sparse regular matrix sampler

`sparse_regular_sampler.cpp` samples sums of disjoint permutation matrices. It uses seed 199 and a positive-term subset dynamic program in `long double` arithmetic. It computes the ratio `per(A)^2 / (c_n per(AA^T))`. Scaling the matrix to be doubly stochastic does not change this ratio.

Compile and run it with a C++17 compiler:

```sh
c++ -std=c++17 -O2 sparse_regular_sampler.cpp -o sampler
./sampler 16 3 30
```

The arguments are order, degree, and sample count. The permitted order is 1–22. The degree must be between one and the order. The sample count must be positive. Invalid arguments, incomplete sampling, invalid numerical results, and output failures return a nonzero exit code. A rejection limit prevents an unlimited search for the next disjoint permutation.

Each output line gives the order, degree, sample index, two permanents, and ratio. A ratio below one also prints its matrix and returns exit code 1 after all requested samples. This is a numerical candidate for exact checking. It is not a certified counterexample. Exit code 2 indicates invalid input or an incomplete calculation. Exit code 0 means only that the requested finite samples completed without a ratio below one. The program writes its completion count to standard error. Different standard-library implementations can produce different permutations from the same seed.

See the [authorship and autonomous AI disclosure](../../../../../../AUTHORSHIP.md).
