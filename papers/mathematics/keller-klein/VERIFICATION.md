# Verification

The Lean project in [lean/](lean/) pins Lean `v4.19.0` (commit `6caaee842e94`) and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`; [lean/lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan), then from `lean/`:

```sh
lake exe cache get
python3 verify.py --lean "$(lean --print-prefix)/bin/lean" --mathlib .lake/packages/mathlib
```

The verifier checks the dependency commits and clean worktrees, rejects `sorry`, `admit`, added axioms, `unsafe`, `native_decide`, `opaque`, `implemented_by` and changes to kernel checking in the local sources, copies all 62 modules into a fresh directory, compiles them in dependency order with `-DautoImplicit=false -Ddebug.skipKernelTC=false`, and checks that the 14 audited declarations depend only on `propext`, `Classical.choice` and `Quot.sound`. Every new declaration is kernel-checked; by default compiled imports are trusted (`--trust=1`), and `--trust 0` additionally rechecks them. It writes `build.log`, `axioms.txt` and `certificate.json` into `lean/verification/`; run it on a copy to keep the recorded evidence unchanged.

The central declarations are `KellerKlein.small_coefficient_upper_concentration`, `KellerKlein.small_coefficient_upper_concentration_normal` and `KellerKlein.small_coefficient_upper_cdf`. The probability is the exact count of sign vectors divided by `2ⁿ`, and the normal distribution function is Mathlib's `cdf (gaussianReal 0 1)`.

The programs in [checks/](checks/) verify the final rational inequalities of the two analytic zones with exact arithmetic (`python3 checks/zone_a_constants.py`); they do not check the analytic lemmas, which are proved in Lean.

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats it on every push. The full Keller–Klein conjecture follows only together with Ivanisvili's computer-assisted Theorems 1.1 and 10.9, which are outside this development. Formal verification does not establish novelty or priority.
