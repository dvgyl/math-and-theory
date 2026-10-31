# Verification

The Lean project in [lean/](lean/) pins Lean `v4.35.0` and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`, the revision of the shared library; [lake-manifest.json](lean/lake-manifest.json) fixes every transitive dependency. Install [Elan](https://github.com/leanprover/elan), then, in a fresh copy of the package, run

```sh
python3 verify.py --output /tmp/berge-triangle-verification
```

The script rejects `sorry`, `admit`, `axiom`, `native_decide` and other unchecked constructions in the Lean sources, refuses to reuse an existing project build, fetches the pinned Mathlib cache for the imported modules, builds the library and runs [Audit.lean](lean/Audit.lean). It requires every declaration listed in [theorem-map.json](theorem-map.json) to depend only on `propext`, `Classical.choice` and `Quot.sound`. It then runs the two exact checkers, which use only the Python standard library. `python3 verify.py --skip-lean` runs the exact checks alone.

`BergeTriangle.HasBergeTriangle` asks for three distinct vertices and three distinct edges containing the three pairs, without an induced condition. `BergeTriangle.IsSaturated` requires 3-uniformity, freeness, and a Berge triangle after adding any absent 3-element set. `BergeTriangle.PairedProduct` records disjoint 2-element pairs and a disjoint base that cover every vertex, with at least one pair and one base vertex; on `Fin n` these systems are exactly the copies of `F(n,p)` with `1 ≤ p < n/2`. [theorem-map.json](theorem-map.json) lists the formal and the conventional parts of the manuscript.

The exact checkers are [check_spectrum.py](certificate/check_spectrum.py), written for this release, and [certificate_checker.py](certificate/certificate_checker.py) from the research package. The first decides freeness with Hall's condition on every vertex triple and saturation by testing every absent triple for a closing two-edge Berge path. The second validates freeness by enumerating triples of edges and checks a stored closing path for every absent triple without search.

The fresh replay for this release is recorded in [verification/](verification/). Formal verification does not establish novelty or priority.
