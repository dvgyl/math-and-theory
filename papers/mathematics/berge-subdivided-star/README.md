# Exact Berge saturation numbers of the subdivided star in every uniformity and its minimality among trees

**Fully autonomous agentic research.** Autonomous AI research agents found the results, their proofs and an original Lean development in an earlier session; Opus 5.5 by Anthropic used with Claude Code checked the proofs and the cited statements, ported and extended the Lean proof, ran the fresh replay and wrote the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

Let `B_a` be the star `K_{1,a}` with one edge subdivided: centre `c`, stem `b`, terminal `x` and leaves `y_1, …, y_{a−1}`, with edges `cb`, `bx` and `cy_i`. A Berge copy of a graph `F` in a hypergraph consists of an injection of the vertices of `F` and an injection of its edges into distinct hyperedges containing their endpoints. An `r`-uniform hypergraph is Berge-`F`-saturated if it has no Berge copy of `F` but gains one when any absent `r`-set is added; `sat_r(n, Berge-F)` is the least number of hyperedges of such a hypergraph on `n` vertices, isolated vertices included. Put `s = r − 1` and `A = sa + 1`.

**Theorem 1 (exact value).** For all `a, r ≥ 3` and `n ≥ A`, writing `n = Aq + t` with `0 ≤ t < A`,

```
sat_r(n, Berge-B_a) = ⌊a(n + 1)/((r − 1)a + 1)⌋ = aq + ⌊t/s⌋ = ⌈a(n − s + 1)/A⌉,
```

attained by `q` disjoint loose stars, one with `a + ⌊t/s⌋` spokes and the others with `a`, and `t mod s` isolated vertices. For smaller orders the value is `a` when `max(a + 2, r + 1) ≤ n < A` and `C(n, r)` below that.

**Theorem 2 (near-minimum structure).** If `k ≥ 0`, `n ≥ A(s(k + 1) + 1)` and a saturated hypergraph on `n` vertices has at most `sat_r(n, Berge-B_a) + k` hyperedges, then it has a component that is a loose star with at least `a` spokes, and the other components have at most `sA(k + 1) − 1` vertices in total. For `k = 0` the bound `sA − 1` and the threshold `n ≥ rA` are attained.

**Theorem 3 (minimality among trees).** For `a ≥ 5`, every tree `T` on `a + 2` vertices has `sat_3(n, Berge-T) ≥ ⌈a(n − 2)/(2a + 1)⌉`, and every tree `T ≇ B_a` has `sat_3(n, Berge-T) ≥ ⌈(a + 1)(n − 2)/(2a + 3)⌉`. So `B_a` is the unique tree of its order with the least asymptotic lower three-uniform saturation coefficient, `a/(2a + 1)` against at least `(a + 1)/(2a + 3)`, and the unique pointwise minimizer for `n ≥ 3(a + 1)(2a + 1)`. This is the Berge analogue of Theorem 5 of Faudree, Faudree, Gould and Jacobson (*Saturation numbers for trees*, Electron. J. Combin. 16 (2009), R91), which has the same minimizer for graphs.

## Formal scope

Lean 4.35.0 proves Theorem 1 for every `a, r ≥ 3` and `n ≥ (r − 1)a + 1`, with `sat_r(n, Berge-B_a)` defined as the infimum of the sizes of all saturated `r`-uniform hypergraphs on `Fin n`, a Berge copy given by injective vertex and hyperedge maps, and saturation tested on every absent `r`-set (`Berge.satNumber_eq`; `Berge.exact_statement_expanded` unfolds every definition). It also proves Theorem 2 (`Berge.near_minimum_structure`). Every declaration of the project modules depends only on `propext`, `Classical.choice` and `Quot.sound`; there is no `sorry` and no `native_decide`. The small orders, the sharpness constructions and Theorem 3 have conventional proofs in the manuscript.

## Prior work and priority

The Berge saturation problem and its conventions are due to English, Graber, Kirkpatrick, Methuku and Sullivan ([arXiv:1710.03735](https://arxiv.org/abs/1710.03735); Discrete Math. 342 (2019)). Linearity for graphs with a tree component is due to English, Gerbner, Methuku and Tait ([arXiv:1807.06947](https://arxiv.org/abs/1807.06947)); exact values were previously known for Berge stars (Austhof and English, [arXiv:1812.00472](https://arxiv.org/abs/1812.00472)), matchings, triangles and three-uniform `K_4`, and the saturation spectrum of Berge stars was studied by Bushaw, English, Heath, Johnston and Rombach ([arXiv:2502.17686](https://arxiv.org/abs/2502.17686)). A search of the Berge-saturation literature through October 2026 found no exact value for `B_a` and no comparison of Berge saturation numbers across trees. Historical priority is not certified.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [lean/](lean/): the Lean project. The headline statements are in [Main.lean](lean/BergeBroom/Main.lean) (the Lean source calls `B_a` a broom); [CORRESPONDENCE.md](lean/CORRESPONDENCE.md) maps the manuscript to the declarations.
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
