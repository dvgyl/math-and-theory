# Verification

The Lean project in [lean/](lean/) pins Lean `v4.19.0` and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`; [lean/lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan), then from `lean/`:

```sh
lake exe cache get
python3 verify.py
```

The verifier checks that every dependency is a clean checkout at its pinned revision, copies the 22 project modules into a fresh directory, compiles them with `--trust=0 -j1 -DwarningAsError=true -DautoImplicit=false` without reusing project objects, rejects `sorry`, `admit`, new axioms, `native_decide` and kernel-check bypasses, and checks that the 13 audited exports depend only on `propext`, `Classical.choice` and `Quot.sound`. It writes `verification/verification.json` inside `lean/`; run it on a copy of the package to keep the recorded evidence unchanged.

The principal exports are `upb_tensor_no_sr`, `upb_strong_minimum_rank`, `tiles_strong_minimum_rank`, `tilesPower_support_minimum`, `tilesDensity_schmidtNumber_exact` and `normalized_sharp_tiles_power_family`. The Lean parameter `n` counts `N = n + 1` copies.

The rational checks in [calculations/](calculations/) use Python's standard library:

```sh
python3 calculations/exact_matrix_audit.py
```

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats it on every push. The LOCC cost, the rank-four two-qutrit class and the channel interpretation combine the formal theorem with published results and are not formalized. Formal verification does not establish novelty or priority.
