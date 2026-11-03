# Verification

## Lean

The Lean project in [lean/](lean/) pins Lean `v4.19.0` and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`, the environment of the original development; [lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan) and Python 3 with the packages in [calculations/requirements.txt](calculations/requirements.txt), then from this directory, in a fresh copy of the package:

```sh
bash scripts/verify.sh /tmp/unilateral-chsh-verification
```

The script downloads the Mathlib cache, refuses to run if the project already has build output, builds the library `UnilateralCHSHLib` (the 32 modules of [lean/modules.txt](lean/modules.txt)) and the audit library `UnilateralAudit`, checks the audit with [check_axiom_audit.py](scripts/check_axiom_audit.py) and replays the calculations below. The module `UnilateralAxiomAudit` enumerates every declaration whose defining module is one of the 32 project modules, including private and generated ones, and collects its axioms with Lean's `collectAxioms`. Lean 4.19's code generator also stores auxiliary declarations (`_cstage1`, `_cstage2`, `_spec_k`, `_elambda_k`, `_closed_k`, `_boxed`, `_rarg`) that may refer to its placeholder `lcProof`; the audit records them separately, allows them only those placeholders and other such auxiliaries, and requires every other declaration to be a non-axiom depending only on `propext`, `Classical.choice` and `Quot.sound`. The checker also confirms that `modules.txt`, the lakefile roots, the source files and the audited modules agree, rejects `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `ofReduceBool` and `axiom` in the sources, and confirms that every named source declaration was audited. The 32 proof modules are byte-identical to the uploaded development; only the lakefile (library names, source directory, audit library) and the audit module are new.

Statement fidelity. `State` is `Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ`, and every endpoint assumes only `ρ.PosSemidef` and `Matrix.trace ρ = 1`. A filter is any `F : Matrix (Fin 2) (Fin 2) ℂ` with `F.det ≠ 0`; `normalizedFiltered ρ F` is `(F ⊗ I) ρ (F ⊗ I)ᴴ` divided by the real part of its trace, and `filtered_trace_positive` and `normalizedFiltered_density` prove that this trace is positive and the output is a density matrix (Bob: `normalizedFilteredBob`, defined on the second factor). `IsSpinObservable O` means `O` Hermitian, `O * O = 1` and `trace O = 0`, proved equivalent to a unit Bloch spin. The value of a filter and four observables is `(Re tr(ρ' · Bell)/2)²`, with classical bound 1; the value sets are `aliceOperatorGLValues` and `bobOperatorGLValues`, and the endpoints state `IsLUB`, `IsGreatest` and activation equivalences for them. The supremum value `aliceMaximum` is the maximum of the reduced objective over the compact domain at explicit whitened coordinates (or `|b|²` for a pure marginal); `bobMaximum` is `aliceMaximum` of the actual index-swapped state. Filters are not required to be contractions, as in the source paper: scalar multiples give the same normalized state. [FORMAL_COVERAGE.md](lean/FORMAL_COVERAGE.md) maps results to declarations.

What is not formalized: the secular-root construction of the boundary radius `E` and its hard case (the formal finite-candidate theorem uses an attained maximum over the sphere), the explicit cubic and the admissibility and singular-compression tests, the polynomial and rational-ellipsoid activation tests and the rational cubic, the threshold regimes at the local bound, the rank-two formula and its Ruskai–Szarek–Werner input, the `sqrt 2` characterization, the axial and quasi-distillable families, the success-probability results and the stability results. These have conventional proofs in the manuscript.

## Calculations

`python3 scripts/run_checks.py` copies [calculations/](calculations/) to a temporary directory, runs every checker there with `python3 -I` and compares each output with the recorded JSON file (relative tolerance 1e-6, absolute tolerance 1e-9); `--quick` skips the two direct-optimizer audits and `release_check.py`. The two figure scripts are run as well. The checkers:

- `exact_examples.py`: exact SymPy checks of the examples, filters, success probabilities and the pencil determinant identity;
- `check_extensions.py`: tests of the solver functions in `unilateral_chsh.py` and `extensions_solver.py`, including exact activation signs, exact cubic roots, the rank-two formula and success frontiers with actual density-matrix witnesses;
- `audit_spectral_cases.py`: 655 canonical data sets covering every rank of `K`, common kernels and repeated eigenvalues, with 252,500 sampled filters;
- `independent_audit/check_spectral.py` (and `--additional`): 275 comparisons with multistart direct filtering of complex density matrices;
- `extensions/`: 1,000-state identity audit, 600 axial states, 102 success-frontier comparisons, rational-cubic checks, 1,000 rank-two states, an exact circle of optimal filters and an exact bilateral certificate for the quasi-distillable family;
- `original_input/`: whitening formulas on 256 original states with 512 arbitrary complex filters, and the original-input success lens and frontiers;
- `check_filter_reduction.py`: 2,000 instances of the real filter reduction used in the Lean proof;
- `release_check.py`, written for this release without importing the other files: exact values for the examples and the quasi-distillable family on a rational grid, and 160 random states of ranks one to four with `α > 1`, comparing the least-eigenvalue value with the reconstructed invertible filter and with multistart direct maximization.

These computations corroborate the proofs; no theorem rests on them, and the Python programs are not formally verified. The solvers use floating-point eigensolvers; near rank changes or at a pure filtered marginal, where the value is discontinuous, use exact arithmetic.

## Scope

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats the Lean build, the audit and the quick calculation replay on every push. Formal verification and exact computation do not establish novelty or priority.
