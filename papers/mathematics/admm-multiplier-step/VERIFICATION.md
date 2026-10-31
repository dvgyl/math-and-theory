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

The verifier checks that Mathlib and every dependency are clean checkouts at the pinned revisions, compiles the 301 modules imported by `NearSharpFullRank` and `CycleCounterexample` one at a time into a fresh object directory, and rejects `sorry`, extra axioms, `native_decide` and implementation overrides. It then submits the stored bodies of the eleven central declarations to the kernel again under fresh names (`lean/KernelBodyAudit.lean`) and checks that each depends only on `propext`, `Classical.choice` and `Quot.sound`:

- `ADMMNearSharpAllSteps.initialized_admm_objective_converges` (consensus convergence for `0 < tau <= 377359/200000`)
- `ADMMNearSharpAllSteps.rankDeficient_original_admm_converges` (affine constraints, `0 < tau <= 377359/200000`)
- `ADMMNearSharpAllSteps.fullRank_original_admm_converges` (affine constraints with left inverses, `0 < tau <= 377359/200000`)
- `ADMMNearSharpCertificate.C188.certificate` and `ADMMNearSharpCertificate.C1886.certificate` (the version 1.0 certificates on `[7/4, 47/25]` and `[47/25, 943/500]`)
- `ADMMNearSharpCertificate.C188628.certificate`, `C188632.certificate`, `C18865.certificate`, `C18867.certificate` and `C1886795.certificate` (the version 1.1 certificates on `[943/500, 47157/25000]`, `[47157/25000, 23579/12500]`, `[23579/12500, 3773/2000]`, `[3773/2000, 18867/10000]` and `[18867/10000, 377359/200000]`)
- `ADMM128Counterexample.counterexample` (the current orbit, `tau >= 38847831300265103262189027/20588352022933119368900773 ≈ 1.8868840`)

The Lean data of the five version 1.1 certificates (`lean/NearSharpData188628Defs.lean` and the corresponding files for the other four intervals) contain the matrices `P` and `T` and the interpolation weights of the JSON certificates, scaled to integers, together with integer Gram factors that prove the four positive-semidefiniteness conditions. The kernel checks these data with sequential sums over lists of integers; `lean/IntegerLists.lean` proves that those sums agree with the matrix statements used by the version 1.0 certificates, so the five new certificates feed the same convergence theorem. The orbit data in `lean/CycleDataCore.lean` are the integer vectors of `certificates/exact_cycle_1886884_K128.json`.

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

Lean proves the statements of the eleven declarations above: convergence for every `0 < tau <= 377359/200000`, its affine-constraint versions, all seven interval certificates, and the current orbit for every `tau >= 1.8868840…`. The version 1.0 orbit (`certificates/exact_cycle_18869_10000_K128.json`, valid for `tau >= 1.8868954…`) is no longer formalized separately; the current orbit covers every step it covered.

The scalar theorem (exact range `(0, 2)` in dimension one) is not formalized; it has a conventional proof in Section 8 of the manuscript. Individual objective-value limits, the reduction from proper closed convex functions to proximal attainment, and penalty rescaling are also conventional arguments in the manuscript. Formal verification does not establish novelty or priority.
