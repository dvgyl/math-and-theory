# Verification

## Mac Lane–Vaquié project

The project in [lean_mlv/](lean_mlv/) pins Lean `v4.35.0-rc2` (commit `11acb17ec6b0`) and Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`; [lean_mlv/lake-manifest.json](lean_mlv/lake-manifest.json) fixes every transitive dependency. From `lean_mlv/`:

```sh
lake exe cache get
lake build Cli
python3 scripts/verify_cached.py --mathlib-cache .lake/packages/mathlib \
  --lean-bin "$(lean --print-prefix)/bin/lean" --packages-root .lake/packages \
  --output /tmp/artin-schreier-depth-mlv-verification --module-timeout 900
```

The verifier checks the compiler and the dependency pins, rejects `sorry`, `admit`, `axiom`, `unsafe` and `partial` in the sources, compiles all 100 production modules (46 local and 54 vendored NYLL modules) and a regenerated audit one at a time into a fresh directory, and checks that each of the 2127 declarations defined in them, including private and generated ones, depends only on `propext`, `Classical.choice` and `Quot.sound`. Its central declaration is `NTCThird.artinSchreierTower_intrinsicMLVDepth_one_iff` in [ASDepthTheorem.lean](lean_mlv/ASDepthTheorem.lean); [THIRD_PARTY.md](lean_mlv/THIRD_PARTY.md) records the adapted and vendored sources, and [vendor/](lean_mlv/vendor/) the one disclosed change to a vendored import. The fresh replay is recorded in [verification/mlv/](verification/mlv/).

## Okutsu project

The Lean project in [lean/](lean/) pins Lean `v4.19.0` (commit `6caaee842e94`) and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`; [lean/lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan), then from `lean/`:

```sh
lake exe cache get
lake build Cli
python3 scripts/verify_cached.py --mathlib-cache .lake/packages/mathlib \
  --lean-bin "$(lean --print-prefix)/bin/lean" --packages-root .lake/packages \
  --output /tmp/artin-schreier-depth-verification
```

With an existing checkout of Mathlib at the pinned revision, pass its path as `--mathlib-cache` and its `.lake/packages` as `--packages-root`. The output directory must not exist. The verifier checks the compiler and the dependency pins, rejects `sorry`, `admit` and custom axioms in the sources, compiles the 20 modules and a regenerated audit one at a time into a fresh directory with no earlier project objects on the search path, and checks that each of the 387 declarations defined in those modules, including generated and private ones, depends only on `propext`, `Classical.choice` and `Quot.sound`.

The central declaration is `okutsu_minimum_one_iff_asCompositum` in [HahnClosureForward.lean](lean/HahnClosureForward.lean), with the two implications `asCompositum_of_hahnClosure_okutsu_minimum` ([HahnClosureDepth.lean](lean/HahnClosureDepth.lean)) and `hahnClosure_okutsu_minimum_of_asCompositum`. Their hypotheses are stated in Section 7 of the manuscript: distances are measured in the algebraic closure of `K` inside the Hahn field, as in the source; depth one is the least length of an Okutsu sequence (defined in [OkutsuDepth.lean](lean/OkutsuDepth.lean)); and henselianity is the property `RationalValuedHenselian` of unique extension of the valuation to algebraic extensions (defined in [HenselianKrasner.lean](lean/HenselianKrasner.lean)). The earlier converse in an abstract algebraic closure, `asCompositum_of_algebraicClosure_okutsu_minimum` in [TowerClosureConverse.lean](lean/TowerClosureConverse.lean), is retained.

The fresh replay of this project is recorded in [verification/](verification/). The CI workflow repeats both replays on every push. In this project the identification of Mac Lane–Vaquié depth with the Okutsu minimum is the source's Theorem 1.3; the Mac Lane–Vaquié project above proves it at length one. Formal verification does not establish novelty or priority.
