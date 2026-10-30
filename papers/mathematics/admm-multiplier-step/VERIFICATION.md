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

- `ADMMNearSharpAllSteps.initialized_admm_objective_converges`
- `ADMMNearSharpAllSteps.rankDeficient_original_admm_converges`
- `ADMMNearSharpAllSteps.fullRank_original_admm_converges`
- `ADMMNearSharpCertificate.C188.certificate`
- `ADMMNearSharpCertificate.C1886.certificate`
- `ADMM128Counterexample.counterexample`

A successful run writes `verification.json` with `"status": "passed"`. The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats the replay on every push.

## Exact arithmetic

From the package directory, Python 3's standard library suffices:

```sh
python3 checks/check_exact_interval.py certificates/exact_175_188_m12.json
python3 checks/check_exact_interval.py certificates/exact_188_1886_m20.json
python3 checks/exact_circulant_cycle.py --check certificates/exact_cycle_18869_10000_K128.json
```

The interval checker rebuilds the descent identity from the ADMM recurrence at both endpoints, checks nonnegative flow-balanced weights, and multiplies the rational `LDLᵀ` factors back exactly. The cycle checker verifies every vertex margin, the nonnegative slopes in `τ`, the exact threshold, zero centroids and the residual. No floating-point tolerance is accepted. The scripts in [discovery/](discovery/) located the certificates numerically; they are not needed for verification.

## Scope

Lean proves the statements of the six declarations above. Individual objective-value limits, the reduction from proper closed convex functions to proximal attainment, and penalty rescaling are conventional arguments in the manuscript. Formal verification does not establish novelty or priority.
