# Manuscript-to-Lean correspondence

This file maps the claims of the manuscript (`../manuscript.tex`) to formal declarations. A hypergraph on a vertex type `V` is a `Finset (Finset V)`; on `Fin n` every vertex counts, so isolated vertices are included.

| Manuscript obligation | Lean declaration(s) | Scope and edge cases |
|---|---|---|
| Berge path of length `L`: distinct vertices, distinct hyperedges, `{v_{i−1}, v_i} ⊆ e_i` | `Links`, `IsBergePath` in `BergePath/Basic.lean` | `Links vs es` forces `vs.length = es.length + 1` (`Links.length_eq`); hyperedges must be members of the hypergraph. |
| Berge-`P_m` (`m` vertices) | `ContainsBergePath H m` | A Berge path with `es.length + 1 = m`. |
| Three-uniform Berge-`P_m`-saturated hypergraph | `IsThreeUniform`, `IsBergePathSaturated` | Freeness and a Berge-`P_m` after adding every absent three-element set, with no linearity restriction on the added set. |
| `sat₃(n, Berge-P_m)` | `satNumber`, `satNumber_le` | Infimum of the sizes of saturated hypergraphs on `Fin n`; `satNumber_le` bounds it by any saturated hypergraph. |
| `a_m = (3 + r)2^s − 5` for `m = 4s + r`, `1 ≤ r ≤ 4`, and `U(n)` | `treeSize`, `conjecturedSat`, `treeSize_ten`, `conjecturedSat_ten_34` | `s = (m − 1)/4`, `r = m − 4s`; `U(n) = (n − n/(2a + 1) + 1)/2` in natural-number arithmetic. |
| Conjecture 2.4 of arXiv:1710.03735v1 for `k = 3` | `Conjecture24ThreeUniform` | All `m ≥ 10` and `n ≥ 2a_m + 1`. |
| Joining, reversing and extending Berge paths | `Links.join`, `Links.reverse`, `IsBergePath.cons`, `IsBergePath.join`, `IsBergePath.reverse`, `IsBergePath.mono` | General vertex type. |
| Loose cycles with two isolated vertices | `Vtx`, `core`, `pend`, `cedge`, `looseCycles`, `card_looseCycles`, `isThreeUniform_looseCycles` in `BergePath/LooseCycles.lean` | `t` copies of the loose `d`-cycle `e_i = {c_i, c_{i+1}, p_i}`, indices in `Fin d`, and two isolated vertices; `td` hyperedges. |
| Every cycle vertex starts a path through its whole cycle | `runV`, `runE`, `isBergePath_run`, `exists_path_from` | Both core and pendant starting vertices; the path stays in its copy. |
| Freeness | `not_containsBergePath_looseCycles` | Every hyperedge of a Berge path lies in the copy of its first vertex, and a copy has only `d` hyperedges. |
| The three augmentation cases | `containsBergePath_of_cross`, `containsBergePath_of_pend_pair`, `containsBergePath_of_core_pair` | Triples meeting two components, triples with two pendants of one cycle, triples with two cores of one cycle (all offsets `1 ≤ k ≤ d − 1`). |
| Proposition 3 (loose cycles are saturated) | `looseCycles_saturated` | Every `d ≥ 3` and every `t`, including `t = 0`; every absent triple, including triples of isolated vertices and cycle vertices. |
| Invariance under relabelling | `relabel`, `IsBergePathSaturated.relabel`, `satNumber_looseCycles_le` in `BergePath/Counterexample.lean` | Any equivalence of vertex types; gives `sat₃(2td + 2, Berge-P_{d+2}) ≤ td`. |
| The explicit 34-vertex witness | `witness34`, `witness34_eq_relabel`, `witness34_card`, `witness34_saturated` | The triples `{16j + i, 16j + ((i + 1) mod 8), 16j + 8 + i}` on `Fin 34`, checked against the relabelled loose cycles by `decide`. |
| Corollary 2 (the conjecture fails) | `satNumber_34_10_le`, `not_conjecture24ThreeUniform` | `sat₃(34, Berge-P₁₀) ≤ 16 < 17`. |
| Failure at every exceptional order and for every `m ≥ 10` | `satNumber_lt_conjecturedSat`, `le_treeSize`, `conjecture24_fails_for_every_m` | Orders `2t(m − 2) + 2` strictly between `b` and `2b`; `a_m ≥ m − 2` for `m ≥ 10`. |
| Lower bound, exact formula and uniqueness (Theorem 1) | not formalized | Conventional proof in Sections 3–6 of the manuscript, using Theorem 2.2 and Lemma 3.10 of the source paper. |
