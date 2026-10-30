# Verification

The Lean project in [lean/](lean/) pins Lean `v4.19.0` (commit `6caaee842e94`) and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`; [lean/lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. It contains the unchanged modules of the three uploaded developments (continuous-time Hilbert threshold, damping-two planar model, discrete threshold) and the new planar modules `PlanarEnergy`, `EulerObstruction`, `PlanarInvariants`, `PlanarUnbounded`, `PlanarTrajectory`, `PlanarMain` and `PlanarAllDamping`.

Install [Elan](https://github.com/leanprover/elan), then from `lean/`:

```sh
lake exe cache get
python3 verify_release.py --lean-home "$(lean --print-prefix)" \
  --mathlib .lake/packages/mathlib --out ../verification-replay
```

The output directory must be new or empty. The verifier checks the Lean release, the toolchain file and clean checkouts of Mathlib and every dependency at the pinned revisions. It confirms that the lakefile roots, its module list and the `.lean` files agree, and rejects `sorry`, `admit`, axioms, `unsafe`, `native_decide`, `implemented_by`, metaprogramming commands and unapproved options. It compiles every module from source, one at a time, with `--trust=0 -j1 -DwarningAsError=true` into a fresh object directory, so every imported proof is replayed by the kernel. [Audit.lean](lean/Audit.lean) prints the headline statements and their axioms. A successful run writes a receipt with status `PASS`.

The headline theorems, each depending only on `propext`, `Classical.choice` and `Quot.sound`, are:

- `NesterovSharpThreshold.exists_subcritical_norm_divergent_flow`, `NesterovSharpThreshold.sharp_boundedness_threshold`, `NesterovSharpThreshold.exists_positive_subcritical_norm_divergent_flow`, `NesterovSharpThreshold.sharp_boundedness_threshold_all_positive` and `NesterovHighDamping.bounded_distance` (continuous time);
- `DiscreteNesterov.sharp_discrete_boundedness_threshold`, `DiscreteNesterov.exists_subcritical_discrete_norm_divergence` and `DiscreteNesterov.exists_discrete_norm_divergence_below_three` (discrete time);
- `NesterovPlanar.planar_valley_escape`, `NesterovPlanar.every_planar_trajectory_escapes` and `NesterovPlanar.planar_escape_all_low_damping` (the planar valley).

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats it on every push.

Planar escape of the same valley for `0 < r ≤ 1`, its boundedness for `r > 2`, and existence of solutions for `r ≤ 1` are conventional arguments in the manuscript. Formal verification does not establish novelty or priority.
