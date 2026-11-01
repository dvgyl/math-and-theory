# Verification

The Lean project in [lean/](lean/) pins Lean `v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; [lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency, and the build treats warnings as errors. Install [Elan](https://github.com/leanprover/elan), then from this directory, in a fresh copy of the package:

```sh
bash scripts/verify.sh /tmp/berge-subdivided-star-verification
```

The script downloads the Mathlib cache, refuses to run if the project already has build output, builds `BergeBroom` and `BergeBroom.AxiomAudit`, and checks the audit with [check_axiom_audit.py](scripts/check_axiom_audit.py). `BergeBroom.AxiomAudit` enumerates every declaration whose defining module is one of the fourteen project modules, including private and generated ones, and fails on any axiom other than `propext`, `Classical.choice` and `Quot.sound`; the checker also rejects `sorry`, `admit`, `native_decide`, `implemented_by`, `extern` and `axiom` in the sources and confirms that every named source declaration was audited.

`Berge.UniformHypergraph V r` is a finite set of `r`-element vertex sets on an ambient type; `Berge.BroomCopy a E` is an injective map of the `a + 2` vertices of `B_a` together with an injective map of its `a + 1` edges into hyperedges containing their endpoints; `Berge.Saturated a H` asks for no copy and a copy after inserting any absent `r`-set. `Berge.satNumber a r n` is the least size of a saturated hypergraph on `Fin n`, and `Berge.satNumber_eq` gives `⌊a(n + 1)/((r − 1)a + 1)⌋` for `a, r ≥ 3` and `n ≥ (r − 1)a + 1`. [CORRESPONDENCE.md](lean/CORRESPONDENCE.md) maps each step to its declarations.

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats it on every push. The small orders, the sharpness constructions and the minimality among trees are not formalized. Formal verification does not establish novelty or priority.
