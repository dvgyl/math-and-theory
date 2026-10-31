# Verification

## Lean

The Lean project in [lean/](lean/) pins Lean `v4.19.0` (commit `6caaee842e94`) and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`; [lean/lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan), then from `lean/` fetch the pinned dependencies and the Mathlib cache:

```sh
lake exe cache get
```

From `lean/`, rebuild every local module into a new directory and audit the central theorems:

```sh
python3 ../verify_lean.py --dependency-project . --output-dir ../verification-replay
```

The verifier checks that Mathlib and every dependency are clean checkouts at the pinned revisions, compiles the 168 modules imported by `NearSharpFullRank` and `CycleCounterexample` one at a time into a fresh object directory, and rejects `sorry`, extra axioms, `native_decide` and implementation overrides. It then submits the stored bodies of the six central declarations to the kernel again under fresh names (`lean/KernelBodyAudit.lean`) and checks that each depends only on `propext`, `Classical.choice` and `Quot.sound`:

- `ADMMNearSharpAllSteps.initialized_admm_objective_converges` (consensus convergence for `0 < tau <= 943/500`)
- `ADMMNearSharpAllSteps.rankDeficient_original_admm_converges` (affine constraints, `0 < tau <= 943/500`)
- `ADMMNearSharpAllSteps.fullRank_original_admm_converges` (affine constraints with left inverses, `0 < tau <= 943/500`)
- `ADMMNearSharpCertificate.C188.certificate`
- `ADMMNearSharpCertificate.C1886.certificate`
- `ADMM128Counterexample.counterexample` (the version 1.0 orbit, `tau >= 897744153596994489/475778439151265168 ≈ 1.8868954`)

A successful run writes `verification.json` with `"status": "passed"`. The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats the replay on every push.

## Exact arithmetic

From the package directory, Python 3's standard library suffices:

```sh
python3 checks/check_exact_interval.py certificates/exact_175_188_m12.json
python3 checks/check_exact_interval.py certificates/exact_188_1886_m20.json
python3 checks/check_exact_interval.py certificates/exact_1886_188628_m20.json
python3 checks/check_exact_interval.py certificates/exact_188628_188632_m20.json
python3 checks/check_exact_interval.py certificates/exact_188632_18865_m20.json
python3 checks/check_exact_interval.py certificates/exact_18865_18867_m20.json
python3 checks/check_exact_interval.py certificates/exact_18867_1886795_m32.json
python3 checks/exact_circulant_cycle.py --check certificates/exact_cycle_1886884_K128.json
python3 checks/exact_circulant_cycle.py --check certificates/exact_cycle_18869_10000_K128.json
```

The seven interval certificates cover the contiguous closed intervals `[7/4, 47/25]`, `[47/25, 943/500]`, `[943/500, 47157/25000]`, `[47157/25000, 23579/12500]`, `[23579/12500, 3773/2000]`, `[3773/2000, 18867/10000]` and `[18867/10000, 377359/200000]`; each checker run prints its interval. The memory-32 certificate takes about two minutes, the others well under one minute each. The current cycle certificate reports `valid_for_all_tau_at_least = 38847831300265103262189027/20588352022933119368900773`. The five certificates of version 1.1 were converted from the uploaded files to this package's format without changing any number; each records the SHA-256 of its source file. On 31 October 2026 they and the new cycle passed these checkers, and the uploaded originals also passed the separate exact evaluator supplied with the upload (not included here).

The interval checker rebuilds the descent identity from the ADMM recurrence at both endpoints, checks nonnegative flow-balanced weights, and multiplies the rational `LDLᵀ` factors back exactly. The cycle checker verifies every vertex margin, the nonnegative slopes in `τ`, the exact threshold, zero centroids and the residual. No floating-point tolerance is accepted. The scripts in [discovery/](discovery/) located the certificates numerically; they are not needed for verification.

## Scope

Lean proves the statements of the six declarations above. Version 1.1 did not change the Lean development, so the formally verified convergence range is `0 < tau <= 943/500`, and the formally verified orbit is the version 1.0 orbit valid for `tau >= 1.8868954…`.

The following parts of version 1.1 are not formalized:

- convergence for `943/500 < tau <= 377359/200000`, which rests on the five new interval certificates (checked exactly above) and the conventional argument of Section 5 of the manuscript, the same argument that Lean formalizes for the first two certificates;
- the current orbit with threshold `1.8868840…`, which is checked exactly by `exact_circulant_cycle.py` and uses the same proof as the formalized orbit;
- the scalar theorem (exact range `(0, 2)` in dimension one), which has a conventional proof in Section 8 of the manuscript.

Individual objective-value limits, the reduction from proper closed convex functions to proximal attainment, and penalty rescaling are also conventional arguments in the manuscript. Formal verification does not establish novelty or priority.
