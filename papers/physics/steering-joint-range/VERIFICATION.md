# Verification

## Lean

The Lean project in [lean/](lean/) pins Lean `v4.19.0` and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`, the environment of the original development and of [steering-bounds](../steering-bounds/); [lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan) and Python 3 with the packages in [calculations/requirements.txt](calculations/requirements.txt), then from this directory, in a fresh copy of the package:

```sh
bash scripts/verify.sh /tmp/steering-joint-range-verification
```

The script downloads the Mathlib cache, refuses to run if the project already has build output, builds the library `MilneBounds` (all 70 modules of [lean/modules.txt](lean/modules.txt)) and the audit module `MilneAxiomAudit`, checks the audit with [check_axiom_audit.py](scripts/check_axiom_audit.py) and replays the calculations below. `MilneAxiomAudit` enumerates every declaration whose defining module is one of the 70 project modules, including private and generated ones. Lean 4.19's code generator also stores auxiliary declarations (`_cstage1`, `_cstage2`, `_spec_k`, `_elambda_k`, `_closed_k`, `_boxed`) that may refer to its placeholder `lcProof`; the audit records them separately, allows them only those placeholders and other such auxiliaries, and requires every other declaration to be a non-axiom depending only on `propext`, `Classical.choice` and `Quot.sound`. The checker also confirms that `modules.txt`, the lakefile roots, the source files and the audited modules agree, rejects `sorry`, `admit`, `native_decide`, `implemented_by`, `extern`, `unsafe`, `ofReduceBool` and `axiom` in the sources, and confirms that every named source declaration was audited. Six modules (`MilneVerification`, `MilneCenterVerification`, `MilneOrbitV2Verification`, `MilneRigidityVerification`, `MilneResearchVerification`, `MilneReleaseVerification`) only print axiom reports for imported theorems and declare nothing.

`Density M` means that `M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ` is positive semidefinite with trace one; `correlation M` is the real matrix of Pauli expectation values and `correlationSq M` the sum of their squares; `steeringCenter M hM` is computed with the positive canonicalizing filter when Bob's marginal is invertible and is Alice's Bloch length otherwise; `hermitianTraceNorm` is the sum of absolute eigenvalues; local unitaries are elements of `Matrix.unitaryGroup`; a Kraus operator `G` satisfies `(1 - Gᴴ * G).PosSemidef`. [FORMAL_COVERAGE.md](lean/FORMAL_COVERAGE.md) maps each result to its declarations and states the fixed marked-axis convention of the volume theorem. Eighteen modules are the original modules of steering-bounds, byte-identical to the form in which they were first produced; the copies in steering-bounds differ from them only by linter clean-ups, docstring wording and added `#check` commands.

What is not formalized: the flat-branch distance exponents, the rank counts and phase-gauge simplifications, the attainment of every value of the signed determinant interval, the orbit classification of all volume maximizers, the rotation of the volume theorem to an arbitrary marked axis, the identification of `‖T‖_F` with the optimized CJWR expression and of the canonical centre with the steering-ellipsoid centre, and steering under arbitrary measurements. These have conventional proofs in the manuscript or are cited.

## Calculations

`python3 scripts/run_checks.py` copies [calculations/](calculations/) to a temporary directory, runs every checker there with `python3 -I` and compares each output with the recorded JSON file, ignoring interpreter and library versions and allowing roundoff differences in floating-point residuals; `--quick` skips the 20,000-state rerun of `reproduce.py`. The checkers are:

- `reproduce_v2.py` (seed 2406039452026): 2,000 random density matrices of ranks one to four, joint-interval witnesses, radial interpolations, 480 volume witnesses, physical Kraus operations and 126 quadratic problems including singular and hard cases;
- `reproduce.py` (seed 240603945): 20,000 random states against the filter identity, the global bound, the matrix inequality, the deficit identity and the stability estimate, and exact rational examples;
- `exact_orbit_certificate.py` and `exact_filter_certificate.py`: six exact rational certificates each, using all principal minors of the state and of the shifted quadratic matrix;
- `exact_physical_example.py`: the activation example at centre length 16/25 in rational arithmetic;
- `one_sided_filter.py` and `verify_probability_geometry.py`: the one-sided criterion against constrained optimization, and the canonical interval, probability frontier and cubic trace identity;
- [independent/](calculations/independent/): `independent_audit.py`, `verify_geometry.py` and `verify_one_sided.py`, separate implementations of these checks, and `exact_new_results.py`, written for this release, which recomputes from explicit matrices in exact SymPy arithmetic the joint-interval witnesses and their mixtures on a grid of 49 parameter pairs, the determinant and correlation identities of the radial normal form and 180 attaining volume witnesses, the probability threshold on 671 grid points, and the activation example.

These computations corroborate the proofs; no theorem rests on them, and the Python programs are not formally verified.

## Scope

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats the Lean build, the audit and the quick calculation replay on every push. Formal verification and exact computation do not establish novelty or priority.
