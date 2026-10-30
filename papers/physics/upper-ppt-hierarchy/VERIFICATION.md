# Verification

The Lean project in [lean/](lean/) pins Lean `v4.19.0` (commit `6caaee842e94`) and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`; [lean/lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan), then from `lean/`:

```sh
lake exe cache get
python3 verify_release.py --lean-home "$(lean --print-prefix)" \
  --mathlib .lake/packages/mathlib --packages-dir .lake/packages --out /tmp/upper-ppt-verification
```

With an existing pristine Mathlib checkout at the pinned revision, pass `--mathlib /path/to/mathlib4` and omit `--packages-dir`. The output directory must be new or empty. Do not run `lake update`. The verifier checks the source hashes frozen in [release-freeze.json](lean/release-freeze.json), the compiler and the pinned dependency commits, rejects `sorry`, `admit`, custom axioms, `unsafe`, `native_decide` and trust overrides, compiles every module listed in [modules.json](lean/modules.json) and the generated [AxiomAudit.lean](lean/AxiomAudit.lean) with `--trust=0` and warnings as errors into fresh object directories, and checks that all 256 audited declarations depend only on `propext`, `Classical.choice` and `Quot.sound`.

The central declarations are `UpperNoncollapse.upperHierarchy_fullRank_strict_at_every_level` and `UpperNoncollapse.no_uniform_finite_collapse` in [AllDepth.lean](lean/AllDepth.lean). The hierarchy `UpperNoncollapse.kappa` is defined in [ArbitraryHierarchy.lean](lean/ArbitraryHierarchy.lean) as an infimum over chains of unrestricted complex matrices; the package proves that its feasible sets are nonempty and bounded below, so the strict inequality is not an artefact of an empty infimum.

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats it on every push. The operational cost and tensor-multiplicativity consequences use published theorems of Lami, Mele and Regula and are not formalized. Formal verification does not establish novelty or priority.
