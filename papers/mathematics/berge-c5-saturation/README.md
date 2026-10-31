# Three-uniform Berge-C₅ saturation: a two-thirds upper bound, the cone spectrum and exact small values

**Fully autonomous agentic research.** Autonomous AI research agents found the constructions, proved the cone classification and the expansion theorems and built the finite certificates; Opus 5.5 by Anthropic used with Claude Code checked the proofs, rechecked every construction and the certificates with its own programs, wrote and ran the Lean formalization and wrote the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

A Berge-C₅ in a hypergraph consists of five distinct vertices `v₀, …, v₄` and five distinct hyperedges `e₀, …, e₄` with `{vᵢ, vᵢ₊₁} ⊆ eᵢ` (indices mod 5). A three-uniform hypergraph is Berge-C₅-saturated if it contains no Berge-C₅ but adding any absent triple creates one; neither the hypergraph nor the added triple has to be linear. Let `s(n) = sat₃(n, Berge-C₅)` be the least number of hyperedges of such a hypergraph on `n` vertices.

**Theorem.** For every `n ≥ 47`, every integer `m` with `⌈(2n−8)/3⌉ ≤ m ≤ n − 2` is the number of hyperedges of a saturated hypergraph on `n` vertices; in particular

```
s(n) ≤ ⌈(2n−8)/3⌉        (n ≥ 47).
```

Weaker endpoints hold earlier: `⌈2(n−1)/3⌉` for `n ≥ 7` (copies of the block `{a,b,c}, {a,d,e}, {b,d,x}, {c,e,y}` glued at `a`), `⌈(2n−4)/3⌉` for `n ≥ 14` and `⌈(2n−6)/3⌉` for `n ≥ 30`; and `n − 1` is a saturated size whenever `4 ∣ n − 1`. The previous explicit bound, `4⌊(n−1)/3⌋ + ((n−1) mod 3)` for `n ≥ 25` (English, Graber, Kirkpatrick, Methuku and Sullivan, arXiv:1710.03735v1, Theorem 5.7(2)), has leading coefficient `4/3`; linear growth is due to English, Gerbner, Methuku and Tait. **No lower bound beyond small orders is proved**: the only general lower bound is the trivial `3s(n) ≥ n − 1`, and the asymptotic coefficient of `s(n)` is open.

**Further results.**

- *Cones.* For `n ≥ 5` the saturated hypergraphs with a vertex in every hyperedge are exactly the cones over disjoint unions of four-cycles and radius-two trees with at least three branches of length two, or over four-cycles plus one `K₂` or one isolated vertex. Their sizes are exactly the integers in `[⌈6(n−1)/7⌉, n−2]`, together with `n − 1` when `4 ∣ n − 1`, for `n ≥ 8`; additions need not contain the root. Since `6/7 > 2/3`, cones are asymptotically more expensive than the general constructions.
- *Bipartite expansions.* If `G` is bipartite and one part has all degrees two, the loose expansion of `G` is saturated exactly when the other part has three hubs and each of the three hub pairs has at least three common neighbours; then `3m = 2n − 6`. A second family, with an apex over a support `C₃`, `C₄`, `C₅` or `2C₃` and at least two connectors per support edge, gives `3m = 2n − (h + 2)`; the two-triangle support yields `⌈(2n−8)/3⌉` and refutes every inequality `3s(n) ≥ 2n − C` with `C < 8`.
- *Exact values.* `s(n) = 0, 0, 0, 1, 4, 4, 4, 4, 5, 6, 6, 7` for `n = 0, …, 11`. There are exactly 13 saturated hypergraphs with four hyperedges and 32 with five, up to isomorphism, and none with six hyperedges on 11 or more vertices.

## Formal scope

Lean 4.35.0 proves, for actual three-uniform hypergraphs on `Fin n`, Berge-C₅s with distinct vertices and distinct hyperedges, and saturation under every absent triple, that for every `n ≥ 14` every `m` with `⌈2(n−1)/3⌉ ≤ m ≤ n − 2` is the size of a saturated hypergraph, that `s(n) ≤ ⌈2(n−1)/3⌉` for `n ≥ 7`, that `n − 1` is a saturated size when `n ≥ 5` and `4 ∣ n − 1`, and the exact values `s(n)` for `n ≤ 7`. The proof is a general rooted-gluing theorem (two rooted pieces glued at their roots form a rooted piece) applied to nine explicit pieces whose properties are checked by kernel evaluation (`decide +kernel`, not `native_decide`); every project declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. The two lowest values `⌈(2n−8)/3⌉` and `⌈(2n−8)/3⌉ + 1` for `n ≥ 47` (the expansion families), the cone classification, the expansion theorems and the values for `8 ≤ n ≤ 11` are not formalized: they have conventional proofs in the manuscript, an exhaustive standard-library check of every claimed pair `(n, m)` for `7 ≤ n ≤ 60`, and exhaustive certificates checked by an independent C++ verifier.

## Prior work and priority

The definitions, the `4/3` bound and vertex gluing are from arXiv:1710.03735v1; the journal version (*Discrete Mathematics* 342 (2019), 1738–1761) could not be accessed for this release. The general linear bounds of English–Gerbner–Methuku–Tait, Gerbner–Patkós–Tuza–Vizer, English–Kritschgau–Nahvi–Sprangel and Xie (arXiv:2610.11409) do not state a cycle-specific coefficient below `4/3` for this problem; Wang and Zhang treat the different linear saturation problem. Searches in October 2026 did not find the coefficient `2/3`, the cone classification or the expansion theorems; some recent full texts were inaccessible, and historical priority is not certified.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [lean/](lean/): the Lean project. The endpoints are `BergeC5.exists_saturated_interval`, `BergeC5.exists_saturated_lower`, `BergeC5.satNumber_le_lower`, `BergeC5.exists_saturated_cone` and `BergeC5.satNumber_small` in [Main.lean](lean/BergeC5/Main.lean) and `BergeC5.Realizable.add` in [Glue.lean](lean/BergeC5/Glue.lean); [theorem-map.json](theorem-map.json) maps each manuscript result to its declarations or to its conventional or certificate proof.
- [certificate/](certificate/): [check_construction.py](certificate/check_construction.py), a standard-library exhaustive check of every claimed construction for `7 ≤ n ≤ 52` by default (`--max-n 60` was run for the record), of the cone sizes, of the expansion families and of the small witnesses; [verify_profiles.cpp](certificate/verify_profiles.cpp), the independent verifier of the three finite certificates in [certificate/data/](certificate/data/) (xz-compressed); and [run_certificates.py](certificate/run_certificates.py), which decompresses, compiles and runs them.
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
