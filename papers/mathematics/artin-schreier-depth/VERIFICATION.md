# Verification

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

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats it on every push. The identification of Mac Lane–Vaquié depth with the Okutsu minimum is the source's Theorem 1.3 and is not formalized, and neither is the equivalence of the unique-extension definition with other forms of henselianity. Formal verification does not establish novelty or priority.
