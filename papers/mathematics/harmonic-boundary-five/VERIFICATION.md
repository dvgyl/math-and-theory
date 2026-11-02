# Verification

## Lean

The Lean project in [lean/](lean/) pins Lean `v4.35.0`. Its modules import only Lean's core library and `Std`; the lakefile also pins Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679` for uniformity with the other packages of this repository, and [lake-manifest.json](lean/lake-manifest.json) fixes its transitive dependencies, but no module imports Mathlib. Install [Elan](https://github.com/leanprover/elan), then from this directory, in a fresh copy of the package with NetworkX 3.7 installed (`pip install -r checks/requirements.txt`):

```sh
bash scripts/verify.sh /tmp/harmonic-boundary-five-verification
```

The script refuses to run if the project already has build output, builds `HarmonicBoundary` and `HarmonicBoundary.AxiomAudit`, checks the audit with [check_axiom_audit.py](scripts/check_axiom_audit.py) and replays the finite checks. `HarmonicBoundary.AxiomAudit` enumerates every declaration whose defining module is one of the 53 project modules that define declarations, including private and generated ones, and fails on any axiom other than `propext`, `Classical.choice` and `Quot.sound`; the checker also rejects `sorry`, `admit`, `native_decide`, `ofReduceBool`, `implemented_by`, `extern` and `axiom` in the sources and confirms that every named source declaration was audited.

What the Lean files prove:

- `RootSectors`: for a finite simple graph with a certified distance table (`DistanceCertificate`: the table is the shortest-walk metric), a vertex of degree three that is not boundary and whose deletion leaves the graph connected forces a duplicate-free list of six boundary vertices (`degree_three_noncut_nonboundary_six`). Boundary is the original strict average-distance inequality.
- `WedgeDistance`, `WedgeBoundary`: distances and stability in a one-point union of two graphs; `BlockBudget`: the block accounting identity and kernel-order bounds, from an explicit accounting record (the block-cut tree itself is not constructed).
- `Sharp14`: the 14-vertex kernel has exactly five boundary vertices, by kernel-checked `decide`.
- `LocalSystems/` (42 modules, imported by `LocalFeasibility`): the 835 integer infeasibility systems of the capped local certificate. The correspondence between these statements and the profile certificate is checked by the certificate checker in Python, not in Lean.
- `BipartiteSubcubic`: in a bipartite graph of maximum degree three, a vertex is boundary exactly when it is a leaf or lies on a cycle (`boundary_iff_leaf_or_cycle`).
- `RootedMetricTruncation`: the rooted truncation of an integer metric on an arbitrary index type is a metric with root distances at most `2R + 1` and diameter at most `4R + 2`, preserves the radius-`R` local data, and both bounds are sharp.
- `EvenEqualityAutomaton`, `OddEqualityGrammar`, `OddCountingIdentities`: weight and degree bounds for all runs and derivations of the two-tree grammars, and the polynomial identities behind the counting formula.

Not formalized: the metric-cone coverage, the capping reduction and the local transfer, the diameter-three argument, the subcubic interior reduction, the block decomposition of graphs, the correspondence between two-trees and grammar derivations, the canonical counting argument and the catalogue enumerations. These have conventional proofs in the manuscript and exact computations in [checks/](checks/).

## Finite checks

`python3 checks/run_checks.py` copies [checks/](checks/) to a temporary directory, decompresses the xz-compressed data there and runs seventeen checkers with `python3 -I`: the exact cone matrices, the capped local certificate (835 contradiction trees, 306 feasible selections, all 1,613,472 coefficient choices), the fifteen residual metrics, the block palette through order six, the 227-kernel closure under 7,788 attachment placements, and the grammar, counting, bipartite and metric checks of the extensions. `--independent` adds six enumerations written for this release, which share no code with the others: all graphs to order 8 against the five-boundary catalogue, all subcubic graphs to order 11 against the six-boundary catalogue, all two-trees to order 13 against the minimum and the counting formula, a nauty-free census of all 60,070 two-connected subcubic graphs of orders 6 to 14, and attachment closures that rebuild exactly the 227 and the 201 catalogues from their blocks. `--geng` and `--labelg` (nauty 2.8.9) add the upload's own census and 201-kernel closure.

The fresh replay for this release is recorded in [verification/](verification/). The CI workflow repeats the Lean build, the audit and the finite checks on every push. Formal verification does not establish novelty or priority.
