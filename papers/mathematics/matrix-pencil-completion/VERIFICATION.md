# Verification

The two Lean projects pin Lean `v4.35.0-rc3` (commit `470d5ce14007`) and Mathlib `0db6cb99b412983de54b59ecc1b0b2747542cda3`; their `lake-manifest.json` files fix every transitive dependency. [lean_p1/](lean_p1/) proves common-summand cancellation for matrix families; [lean_p1_converse/](lean_p1_converse/) depends on it through the path `../lean_p1` and proves the theorem. Keep the two directories side by side. Install [Elan](https://github.com/leanprover/elan) and [ripgrep](https://github.com/BurntSushi/ripgrep), then from `lean_p1_converse/`:

```sh
lake exe cache get
bash verify.sh
lake build MatCP1
lake env lean ../lean_p1/AxiomAudit.lean
```

`verify.sh` checks the Mathlib revision and the shared toolchain, removes this project's build output, rebuilds every module, prints the exact statements of the main declarations, audits every exported theorem, rejects `sorry`, `admit`, `axiom` and `native_decide` in the sources, and writes `VERIFICATION.json` with the module list, the axiom audit and source hashes. The last command audits the ten cancellation endpoints; every audited declaration should depend only on `propext`, `Classical.choice` and `Quot.sound`. The other `*Audit.lean` files in `lean_p1_converse/` audit intermediate components and are not part of the verification command.

The central declaration is `MatCP1Converse.dilation_rank_distance_iff` in [DilationTheorem.lean](lean_p1_converse/MatCP1Converse/DilationTheorem.lean); [DILATION_CORRESPONDENCE.md](lean_p1_converse/DILATION_CORRESPONDENCE.md) maps the definitions and quantifiers to the manuscript. `Pencil.normalRank` is the rank over `RatFunc F`, and `Pencil.orbitDistance` is the least bound over both strict-equivalence classes.

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats it on every push. The identification of the dilation with the barred pencils of Dodig and Stošić uses a published theorem and is not formalized. Formal verification does not establish novelty or priority.
