# Verification

The Lean project in [lean/](lean/) pins Lean `v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`; [lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan) and a C++17 compiler, then from this directory, in a fresh copy of the package:

```sh
bash scripts/verify.sh /tmp/berge-c5-verification
```

The script downloads the Mathlib cache, refuses to run if the project already has build output, builds `BergeC5` and `BergeC5.AxiomAudit`, and checks the audit with [check_axiom_audit.py](scripts/check_axiom_audit.py). `BergeC5.AxiomAudit` enumerates every declaration whose defining module is one of the four project modules, including private and generated ones, and fails on any axiom other than `propext`, `Classical.choice` and `Quot.sound`. The script then runs the standard-library construction check [check_construction.py](certificate/check_construction.py) and the certificate driver [run_certificates.py](certificate/run_certificates.py).

`BergeC5.IsBergeC5` requires an injective vertex map and an injective hyperedge map from `Fin 5`, hyperedges of the hypergraph, and `v i, v (i + 1) ∈ e i`; `BergeC5.IsBergeC5Saturated` requires three-uniformity, no Berge-C₅ and a Berge-C₅ after inserting any absent three-element set, with no linearity condition; `BergeC5.satNumber n` is the least size of a saturated hypergraph on `Fin n`, isolated vertices included. A rooted piece (`BergeC5.IsRootedPiece`) is three-uniform and Berge-C₅-free, every absent triple contains the ends of a four-edge Berge path, and every non-root vertex has a two-edge Berge path to the root; `BergeC5.Realizable N k` says that a rooted piece with `N` non-root vertices and `k` hyperedges exists, and `BergeC5.Realizable.add` glues two pieces at their roots. The nine explicit pieces (`K₄⁽³⁾`, the cone over `C₄` and seven hypergraphs `B(p,q,t)`) are checked by Boolean searches (`uniformB`, `cycleB`, `SatCheck`, `ReachCheck`) evaluated by `decide +kernel`, each with a soundness theorem in [Check.lean](lean/BergeC5/Check.lean); the cycle search comes with a proof that it finds every Berge-C₅. A finite table and an induction on the order show that every pair in the range is a sum of the pieces' pairs. [theorem-map.json](theorem-map.json) lists the declarations for each result.

## Constructions

`python3 certificate/check_construction.py --max-n 60 --json` builds, for every `7 ≤ n ≤ 60` and every edge count claimed in Theorem 1 of the manuscript, the hypergraph described there and checks three-uniformity, simplicity, the absence of a Berge-C₅ and a four-edge Berge path inside every absent triple, by direct search with distinct cores and distinct hyperedges. It also checks every cone size of Theorem 2 for `5 ≤ n ≤ 36`, the support construction of Theorem 4 with unequal multiplicities on all four supports, the three-hub criterion of Theorem 3 for all multiplicities `0..4`, and the witnesses for `n ≤ 6`. This is executable evidence for the stated orders, not a proof for all `n`; the all-order statements have the conventional proofs of the manuscript.

## Finite certificates

The values `s(n)` for `8 ≤ n ≤ 11` and the classifications of saturated hypergraphs with four and five hyperedges rest on three certificates in [certificate/data/](certificate/data/), for `m = 4`, `0 ≤ n ≤ 13`, and `m = 5`, `0 ≤ n ≤ 16`, each with at most one isolated vertex, and for `m = 6`, `11 ≤ n ≤ 18` without isolated vertices; Section 7 of the manuscript explains why these ranges cover all orders. The verifier [verify_profiles.cpp](certificate/verify_profiles.cpp) regenerates every incidence profile and consumes exactly one record per profile: an explicit Berge-C₅, an absent triple whose addition leaves the hypergraph free (checked over all five-sets of hyperedges in all cyclic orders and all injective choices of cores), or the index of a listed class, matched under all permutations of the hyperedge labels. It also checks that each listed class in [m4_classes.txt](certificate/data/m4_classes.txt) and [m5_classes.txt](certificate/data/m5_classes.txt) is canonical, distinct from the others, saturated and used. Missing or surplus records are rejected. With `g++` available,

```sh
python3 certificate/run_certificates.py --json certificate-check.json
```

decompresses the certificates with Python's `lzma` module, compiles the verifier and runs all three in a few seconds. The certificates were produced by the research package's own generator and re-encoded in this record order; the verifier shares no code with that generator. The verifier and certificates are executable evidence, not a formal proof.

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats the Lean build, the audit, the construction check and the certificates on every push. The expansion families, the cone classification and the values for `8 ≤ n ≤ 11` are not formalized. Formal verification does not establish novelty or priority.
