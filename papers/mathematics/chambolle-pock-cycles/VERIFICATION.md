# Verification

The Lean project in [lean/](lean/) pins Lean `v4.19.0` and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`; [lean/lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan), then from `lean/`:

```sh
lake exe cache get
python3 verify_lean.py --mathlib .lake/packages/mathlib --output ../verification-replay
```

The output directory must be new. The verifier checks the toolchain, the Mathlib and dependency revisions and their clean working trees, rejects `sorry`, `admit`, axioms, `unsafe` and `native_decide`, compiles all 21 modules with `--trust=0` and warnings as errors into the fresh directory, and audits the transitive axioms of 45 central statements, allowing only `propext`, `Classical.choice` and `Quot.sound`. [FORMAL_CORRESPONDENCE.md](FORMAL_CORRESPONDENCE.md) maps the mathematical claims to Lean declarations; the main endpoint is `AsymptoticCP.counterexamples_for_every_product_above_two`.

The exact seven-cycle certificate is checked independently with Python's standard library:

```sh
python3 exact_certificate/verify_period7.py
```

`exact_certificate/generate_seven_cycle.py` regenerates `lean/SevenCycle.lean` byte for byte from the rational certificate.

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats it on every push. The `limsup` consequence and the numerical observations in the manuscript's scope section are not separate Lean theorems. Formal verification does not establish novelty or priority.
