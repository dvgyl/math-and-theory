# Sixth-round materials

## Proven finite-order result

For every doubly stochastic matrix of rank at most two in orders 2–15, `per(AA^T) <= per(A)`. This yields both the strong and original Gyires inequalities in that family, with equality in the Gyires inequalities only at the uniform matrix.

The argument is in `round6_rank2_bernstein.md` and the root `PROOF_AND_STATUS.md`.

| File | Purpose |
|---|---|
| `round6_rank2_bernstein.py` | Exhaustive integer polynomial coefficient certificate; default range 2–15 |
| `round6_rank2_bernstein_certificate.json` | Full successful range, counts, and per-order coefficient digests |
| `round6_rank2_bernstein.log` | Recorded exhaustive execution output |
| `round6_rank2_bernstein_fraction_check.py` | Separate rational power-basis implementation and exact coefficient comparison |
| `round6_rank2_fraction_comparison.json` | All 20,452 comparison coefficients agree for orders 2–6 |
| `round6_rank2_independent_audit.md` | Independent elementary derivation and coverage audit |
| `round6_rank2_identity_audit.py` and `.json` | Direct-permanent identity checks, singleton and uniform cases |
| `round6_rank2_boundary_audit.md`, `.py`, `.json` | A second mathematical audit and 209 direct comparison cases |

All of these checkers use only the Python standard library. The positive result is finite in order; no argument establishing it for unbounded order was obtained.

## Exact obstructions to stronger proposed inductions

- `round6_boundary_induction.md` and `round6_boundary_exact.py/.json`: symmetric-star counterexamples to specified pivot choices and weighted-average stochastic-complement comparisons. The best-pivot candidate remains unproved.
- `round6_full_inequality.md` and `round6_average_fock_capacity_obstruction.py/.json`: exact order-700 obstruction to averaged minimum-Fock-norm deletion. The capacity-balanced norm is a different quantity; its maximum/average deletion assertions are not refuted.

Neither obstruction is a counterexample to Gyires. Their exact checkers use only the Python standard library.

## Exploratory numerical work

`round6_boundary_probe.py`, `round6_complement_optimization.py`, and `round6_fock_deletion_probe.py`, with their JSON outputs, record numerical searches. Their results are exploratory. Failed auxiliary comparisons in these searches are superseded by the exact certificates above.

The dependency copies `round5_structural_probe.py`, `ratio_search.py`, and `ratio_search.cpp` are included to make those searches reproducible. They require NumPy, SciPy, and a C++ compiler. Compile the local numerical helper before running the floating-point searches:

```bash
g++ -O3 -std=c++17 -shared -fPIC ratio_search.cpp -o permanent_numeric.so
```

The compiled binary is not required by any exact proof checker. The original source-materialization helper is retained as provenance tooling and does not fetch or modify a remote repository.

## Limits

There is no unrestricted proof, no proof of the rank-two inequality for arbitrary order, no new Lean formalization, and no claim of human peer review or mathematical priority. The root manuscript specifies all remaining assertions.
