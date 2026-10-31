# Verification

The Lean project in [lean/](lean/) pins Lean `v4.19.0` and Mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`; [lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan), then from this directory, in a fresh copy of the package:

```sh
bash scripts/verify.sh /tmp/minty-verification
```

The script downloads the Mathlib cache, refuses to run if the project already has build output, builds `Minty` and `Minty.AxiomAudit`, and checks the audit with [check_axiom_audit.py](scripts/check_axiom_audit.py). `Minty.AxiomAudit` enumerates every declaration whose defining module is one of the six project modules, including private and generated ones, and fails on any axiom other than `propext`, `Classical.choice` and `Quot.sound`. The script finally runs the standard-library exact checker [verify_minty_exact.py](certificate/verify_minty_exact.py) for the compatibility table and the polynomial identity; the convex combination is checked in Lean.

`Minty.CMonotone` is the two-point swap condition of Definition 1.2 of Bartz, Bauschke, Phan and Wang for every subset of the three coordinates, `Minty.MaximalCMonotone` is maximality by inclusion among all subsets of `(ℝ²)³`, `Minty.total` is the coordinate sum, and `Minty.pairing_eq_euclidean_inner` identifies the coordinate pairing with the Euclidean inner product. [CORRESPONDENCE.md](lean/CORRESPONDENCE.md) maps each step of the proof to its declarations.

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats it on every push. Formal verification does not establish novelty or priority.
