# Verification

The Lean project in [lean/](lean/) pins Lean `v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; [lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan) and a C++17 compiler, then from this directory, in a fresh copy of the package:

```sh
bash scripts/verify.sh /tmp/berge-c4-verification
```

The script downloads the Mathlib cache, refuses to run if the project already has build output, builds `BergeC4` and `BergeC4.AxiomAudit`, and checks the audit with [check_axiom_audit.py](scripts/check_axiom_audit.py). `BergeC4.AxiomAudit` enumerates every declaration whose defining module is one of the four project modules, including private and generated ones, and fails on any axiom other than `propext`, `Classical.choice` and `Quot.sound`. The script then runs the standard-library construction check [check_construction.py](certificate/check_construction.py) and the certificate driver [run_certificates.py](certificate/run_certificates.py).

`BergeC4.IsBergeC4` requires an injective vertex map and an injective hyperedge map from `Fin 4`, hyperedges of the hypergraph, and `v i, v (i + 1) ∈ e i`; `BergeC4.IsBergeC4Saturated` requires three-uniformity, no Berge-C₄ and a Berge-C₄ after inserting any absent three-element set, with no linearity condition; `BergeC4.satNumber n` is the least size of a saturated hypergraph on `Fin n`, isolated vertices included. The construction is a base hypergraph on `Fin n₀`, `n₀ ∈ {9, 10, 11, 12}`, glued at vertex `0` to copies of the block `{0,1,2}, {0,1,3}, {0,2,4}` (`BergeC4.glued`), relabelled to `Fin n`. Facts about the explicit pieces are Boolean searches (`uniformB`, `hubB`, `SatCheck`, `reach1B`, `reach2B`) evaluated by `decide +kernel`, each with a soundness theorem in [Check.lean](lean/BergeC4/Check.lean). [theorem-map.json](theorem-map.json) lists the declarations for each result.

## Finite certificates

The values `s(n)` for `6 ≤ n ≤ 13` and the classification at `n = 11` rest on six certificates in [certificate/data/](certificate/data/). For `(m, n)` in the ranges `m = 3, 6 ≤ n ≤ 9`; `m = 4, 8 ≤ n ≤ 12`; `m = 5, 10 ≤ n ≤ 15`; `m = 6, 12 ≤ n ≤ 18`; `m = 7, 13 ≤ n ≤ 21`; and `m = 6, n = 11`, the verifier [verify_profiles.cpp](certificate/verify_profiles.cpp) regenerates every incidence profile of a simple three-uniform hypergraph with `m` hyperedges and no isolated vertex, and consumes exactly one record per profile: three vertices in different components, an explicit Berge-C₄, an absent triple whose addition leaves the hypergraph free (checked over all four-sets of hyperedges and all injective vertex choices), or, for `n = 11`, an explicit relabelling to one of the two classes in [n11_m6_classes.txt](certificate/data/n11_m6_classes.txt). Missing or surplus records are rejected. Section 7 of the manuscript explains why these ranges and the isolated-vertex lemma cover all orders. With `g++` available,

```sh
python3 certificate/run_certificates.py --json certificate-check.json
```

decompresses the certificates with Python's `lzma` module, compiles the verifier and runs all six; the seven-edge certificate has 10,592,111 records and takes about a minute. The verifier and certificates are executable evidence, not a formal proof.

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats the Lean build, the audit, the construction check and the certificates other than the seven-edge one on every push. The lower bound, the cone results and the flexible-root theorem are not formalized. Formal verification does not establish novelty or priority.
