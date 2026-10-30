# Verification

The Lean project in [lean/](lean/) pins Lean `v4.19.0` (commit `6caaee842e94`) and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`; [lean/lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan), then from `lean/`:

```sh
lake exe cache get
python3 scripts/verify_cached.py --mathlib-cache .lake/packages/mathlib \
  --lean-bin "$(lean --print-prefix)/bin/lean" --packages-root .lake/packages --output /tmp/unit-squareclasses-verification
```

The output directory must not exist. The verifier checks the compiler and the pinned commits of Mathlib and its dependencies, rejects `sorry`, `admit` and custom axioms in the sources, copies every module into a fresh directory, compiles them in dependency order with no earlier project objects on the import path, and checks that each of the 22 audited declarations depends only on `propext`, `Classical.choice` and `Quot.sound`.

The final endpoint is `UnitSquareclass.algebraic_represented_unit_squareclasses_card_le_lattice_rank`: for every finite family of actual units of `𝓞 K`, represented by vectors of an `𝓞 K`-submodule and pairwise inequivalent modulo squares of units, the size of the family is at most `finrank K (span K L)`. [lean/MANUSCRIPT_CORRESPONDENCE.md](lean/MANUSCRIPT_CORRESPONDENCE.md) maps the manuscript to the modules.

The fresh replays for this release, one with the package verifier and one with `--trust=0`, are recorded in [verification/](verification/). The CI workflow repeats the verifier run on every push. The derivation from finite reflection groups, the sharpness examples and the universality corollary are conventional and not separate Lean endpoints. Formal verification does not establish novelty or priority.
