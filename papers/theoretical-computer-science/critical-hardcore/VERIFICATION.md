# Verification

The Lean project in [lean/](lean/) pins Lean `v4.19.0` (commit `6caaee842e94`) and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`; [lean/lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan), then from `lean/`:

```sh
lake exe cache get
python3 verify.py
```

With an existing pinned installation, pass `--lean /path/to/lean-4.19.0/bin/lean --mathlib /path/to/mathlib4`. The verifier checks the compiler and clean checkouts of every dependency at its pin, rejects `sorry`, `admit`, axioms, `unsafe`, `opaque`, `native_decide` and implementation overrides, copies all 32 modules into a fresh directory, compiles them in dependency order with no earlier project objects on the import path, and checks that the central theorems depend only on `propext`, `Classical.choice` and `Quot.sound`. It writes `build.log`, `axioms.txt` and `certificate.json` into `verification/` next to the Lean project; run it on a copy of the package to keep the recorded evidence unchanged.

The central declarations are `CriticalHardcore.critical_hardcore_influence_rows`, `CriticalHardcore.critical_hardcore_spectral_independence`, `CriticalHardcore.critical_hardcore_pinned_rows`, `CriticalHardcore.criticalInfluenceBound_le_real` and `CriticalHardcore.regular_survival_sqrt_sum_le_scale`.

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats it on every push. The Glauber-dynamics mixing corollary is conditional on a published proposition and is not formalized. Formal verification does not establish novelty or priority.
