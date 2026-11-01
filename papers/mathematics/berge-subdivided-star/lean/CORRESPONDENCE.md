# Manuscript-to-Lean correspondence

This file maps the claims of the manuscript (`../manuscript.tex`) to formal declarations, all in namespace `Berge`. The Lean source calls `B_a` a broom. A hypergraph on `Fin n` keeps every vertex, so isolated vertices count towards the order.

| Manuscript obligation | Lean declaration(s) | Scope and edge cases |
|---|---|---|
| Simple `r`-uniform hypergraph | `UniformHypergraph V r` in `BergeBroom/Definitions.lean` | A `Finset` of `Finset V`, each of cardinality `r`; parallel hyperedges are impossible. |
| `B_a` and a Berge copy of it | `broomLeft`, `broomRight`, `BroomCopy`, `ContainsBroom`, `BroomFree` | Vertices `Fin (a+2)`: centre `0`, stem `1`, terminal `2`; edge `0` is `0–1`, edge `1` is `1–2`, edge `i ≥ 2` is `0–(i+1)`. Both the vertex map and the hyperedge map are embeddings; extra vertices inside a hyperedge are allowed. |
| Berge-`B_a`-saturated | `Saturated` | Freeness and a copy after inserting every `r`-set that is not a hyperedge, with no linearity condition. |
| `sat_r(n, Berge-B_a)` | `satNumber`, `IsSaturationNumber`, `IsSaturationNumber.satNumber_eq` in `BergeBroom/Main.lean` | Infimum of the sizes of saturated hypergraphs on `Fin n`; `IsSaturationNumber a r n m` asserts a saturated hypergraph with `m` hyperedges and the lower bound `m` for every saturated hypergraph. |
| Theorem 1 | `satNumber_eq`, `exact_statement_expanded`, `exact_saturation_uniform_floor`, `exact_saturation_ceiling`, `upperValue_eq_floor` | All `a, r ≥ 3`, `n ≥ (r − 1)a + 1`; natural-number division is the floor, and the ceiling form uses `(x + A − 1)/A`. |
| Loose-star construction (Lemma 7, upper bound) | `starForest`, `starForest_saturated`, `upperConstruction`, `exists_saturated_upper` in `BergeBroom/Construction.lean`; transport by `Saturated.mapEquiv` in `BergeBroom/Relabel.lean` | Built on an explicit vertex type and moved to `Fin n` by an equivalence. |
| Components and identity (1) | `Component`, `componentHypergraph`, `componentHypergraph_saturated`, `component_vertex_bound`, `connected_not_tree_vertex_bound`, `component_mass_bound` in `BergeBroom/Components.lean`, `BergeBroom/Incidence.lean`, `BergeBroom/ComponentClasses.lean` | Components of the incidence graph, isolated vertices included. |
| Lemma 5 (incidence-tree components are loose stars) | `saturated_tree_is_loose`, `saturated_tree_edges_ge` in `BergeBroom/Lower.lean`, using `BergeBroom/Leaves.lean` | Every saturated incidence-tree component with at least two hyperedges. |
| Lemma 6 (small components) | `saturated_exceptional_component_budgets` in `BergeBroom/Exceptional.lean` | `e₀ ≤ 1`, `z ≤ s`, `e₀z = 0`, and `z ≤ s − 1` when a loose star is present. |
| Lower bound in Theorem 1 | `saturated_lower_bound`, `counting_lower_arithmetic` in `BergeBroom/Exact.lean`, `BergeBroom/Arithmetic.lean` | Every saturated hypergraph on a finite vertex type with at least `A` vertices. |
| Theorem 3 | `near_minimum_structure` in `BergeBroom/Main.lean`; `saturated_near_minimum_stability`, `remainderOrder_eq_not_looseStar`, `IsLooseStar` in `BergeBroom/Stability.lean` | The remainder is the total order of the components that are not loose stars (connected, a common centre, at least `a` hyperedges, every other vertex of degree at most one). |
| Theorem 2 (small orders), Proposition 11 (sharpness), Theorem 4 (minimality among trees) | not formalized | Conventional proofs in Sections 3, 5 and 6 of the manuscript. |
