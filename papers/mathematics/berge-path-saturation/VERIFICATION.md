# Verification

The Lean project in [lean/](lean/) pins Lean `v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; [lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan), then from this directory, in a fresh copy of the package:

```sh
bash scripts/verify.sh /tmp/berge-path-verification
```

The script downloads the Mathlib cache, refuses to run if the project already has build output, builds `BergePath` and `BergePath.AxiomAudit`, and checks the audit with [check_axiom_audit.py](scripts/check_axiom_audit.py). `BergePath.AxiomAudit` enumerates every declaration whose defining module is one of the three project modules, including private and generated ones, and fails on any axiom other than `propext`, `Classical.choice` and `Quot.sound`. The script finally runs the standard-library exhaustive checker [check_witness.py](certificate/check_witness.py).

`BergePath.IsBergePath` requires distinct vertices, distinct hyperedges of the hypergraph and `{v_{i−1}, v_i} ⊆ e_i`; `BergePath.ContainsBergePath H m` asks for a Berge path of length `m − 1`; `BergePath.IsBergePathSaturated` requires three-uniformity, no Berge-`P_m` and a Berge-`P_m` after adding any absent three-element set. `BergePath.satNumber n m` is the least size of a saturated hypergraph on `Fin n`, isolated vertices included, and `BergePath.Conjecture24ThreeUniform` states the conjectured equality for all `m ≥ 10` and `n ≥ 2a_m + 1`. [CORRESPONDENCE.md](lean/CORRESPONDENCE.md) maps each step to its declarations.

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats it on every push. The lower bound and the uniqueness statement of the theorem are not formalized. Formal verification does not establish novelty or priority.
