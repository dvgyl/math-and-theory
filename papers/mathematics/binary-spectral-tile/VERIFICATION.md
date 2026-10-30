# Verification

The Lean project in [lean/](lean/) pins Lean `v4.19.0` (commit `6caaee842e94`) and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`; [lean/lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan), then from `lean/`:

```sh
lake exe cache get
python3 verify_release.py --lean-home "$(lean --print-prefix)" \
  --mathlib .lake/packages/mathlib --packages-dir .lake/packages --out /tmp/binary-tile-verification
```

With an existing pristine Mathlib checkout at the pinned revision, pass `--mathlib /path/to/mathlib4` and omit `--packages-dir`. The output directory must be new or empty. The verifier checks the source hashes frozen in [release-freeze.json](lean/release-freeze.json), the compiler and the pinned dependency commits, rejects `sorry`, `admit`, custom axioms, `unsafe`, `native_decide` and trust overrides, compiles every module listed in [modules.json](lean/modules.json) and the generated [AxiomAudit.lean](lean/AxiomAudit.lean) with `--trust=0` and warnings as errors into fresh object directories, and checks that every public definition and theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. Finite facts are decided by the kernel with `decide`; allow several minutes and several gigabytes of memory.

The central declarations are `BinaryFuglede.spectral_aperiodic_tile_without_periodic_complement`, `BinaryFuglede.binary_nine_fails_PT`, `BinaryFuglede.exists_spectral_counterexample`, the classification `BinaryFuglede.tilingPair_iff_translate` and the count `BinaryFuglede.card_complements`.

The standard-library program [checks/check_construction.py](checks/check_construction.py) independently rebuilds the construction, checks the spectrum, the tiling and the allowed shifts, and enumerates every complement in two ways; it runs in a few seconds with `python3 checks/check_construction.py`.

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats it on every push. The dimension-eight theorem used for minimality is external and not formalized. Formal verification does not establish novelty or priority.
