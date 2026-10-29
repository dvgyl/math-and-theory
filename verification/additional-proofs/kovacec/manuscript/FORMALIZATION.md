# Formalization map

The companion project uses Lean 4.19.0 and Mathlib commit `c44e0c8ee63ca166450922a373c7409c5d26b00b`. It consists of eight scientific proof modules and the root `Kovacec.lean`. The manuscript uses one-based spectrum indices and lexicographic permutation labels 0–5; Lean uses `Fin 3` and `Fin 6`.

| Manuscript claim | Source and declarations |
| --- | --- |
| Actual unitary matrix, normal matrices, exact determinant | `KovacecCertificate.lean`: `U_unitary`, `A_normal`, `B_explicit`, `B_normal`, `determinant_exact` |
| Six permutations and exactly nine transposition edges | `KovacecCertificate.lean`: `perm_exhaustive`, `sigmaPoint_perm`, `edge_exhaustive`; `KovacecGraph.graph_eq_sourceGraph` |
| Boundary functions and closed region | `KovacecJordan.lean`: `L`, `R`, `C`, `J`, `isClosed_C`; `KovacecJordan.frontier_C_eq_J` |
| Full graph containment and boundary inclusion | `KovacecGraph.graph_subset_C`, `J_subset_graph` |
| Closed simple parametrization, exactly the full boundary | `KovacecJordan.q_continuous`, `q_zero_eq_six`, `q_injective_on_Ico`; `KovacecJordan.q_image_Icc_eq_J` |
| Straight-segment exterior, with exact length and closed segments | `KovacecExterior.RayExterior`; `KovacecGraph.rayExterior_source_eq`, `frontier_source_eq_J` |
| Exclusion from all bounded component closures and nonempty bounded component | `RayComponent.lean`; `KovacecGraph.p_not_mem_closure_bounded_component`, `exists_bounded_J_component` |
| Full theorem with actual matrix and geometric hypotheses | `KovacecResolution.completed_counterexample` |
| Exact convex identity | `KovacecResolution.ordinary_convex_combination` |
| Necessary enclosure condition is false | `KovacecResolution.conjecture7_false` |

Declarations in `KovacecCertificate.lean` use namespace `KovacecCertificate`. The boundary and loop declarations, including those in files `KovacecBoundary.lean` and `KovacecLoop.lean`, use namespace `KovacecJordan`. The exterior definitions use `KovacecExterior`, and the generic component lemmas in `RayComponent.lean` use `KovacecComponent`. The displayed names `KovacecGraph.*` and `KovacecResolution.*` are fully qualified.

The package-defined `Conjecture7` predicate requires some bounded component closure to contain the determinant whenever the displayed boundary is Jordan. `conjecture7_false` refutes that exact predicate. Its name and names such as `sourceGraph` and `sourceBoundary` do not establish identity with an external definition. Kovačec receives credit for the motivating enclosure proposal; comparison with its literal definitions and current hypotheses remains unverified. A nonempty bounded component is separately exhibited. The proof does not assume a general Jordan-curve theorem or uniqueness assertion.

The checked build compiled all nine scientific sources and checked six integrated endpoint reports with `--trust=0`. Each report had exactly the dependencies `propext`, `Classical.choice` and `Quot.sound`. This checks the stated objects and assumptions. It does not establish research priority or external source identity.

To reproduce, prepare the pinned Lean/Mathlib dependencies, then run in the companion project:

```sh
cd ../formalization
bash build.sh
```

The build script compiles the scientific modules in order, builds the configured root targets, runs `lake env lean --trust=0 ReplayAudit.lean`, and checks the complete required report set with `check_axioms.py`. A mathematical or report-coverage failure must exit nonzero.

The formal proof covers the complete exact example. The visual figure is not an input to that proof. Formal verification does not imply that the example is the first resolution of the attributed enclosure proposal.
