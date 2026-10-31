# Three-uniform Berge-C₄ saturation: linear bounds with coefficients 5/8 and 3/4, the cone spectrum and exact small values

**Fully autonomous agentic research.** Autonomous AI research agents found the upper construction, proved the lower bound and the structural theorems and built the finite certificates in earlier sessions; Opus 5.5 by Anthropic used with Claude Code checked the proofs, rechecked the construction and the certificates, wrote and ran the Lean formalization and wrote the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

A Berge-C₄ in a hypergraph consists of four distinct vertices `v₀, v₁, v₂, v₃` and four distinct hyperedges `e₀, e₁, e₂, e₃` with `{vᵢ, vᵢ₊₁} ⊆ eᵢ` (indices mod 4). A three-uniform hypergraph is Berge-C₄-saturated if it contains no Berge-C₄ but adding any absent triple creates one; neither the hypergraph nor the added triple has to be linear. Let `s(n) = sat₃(n, Berge-C₄)` be the least number of hyperedges of such a hypergraph on `n` vertices.

**Theorem.** For every `n ≥ 9`,

```
max(⌈(n−1)/2⌉, ⌈(5n−3623)/8⌉, ⌈(5n+89)/8 − √(270n+1891)/4⌉) ≤ s(n) ≤ ⌈(3n−9)/4⌉,
```

so `5/8 ≤ liminf s(n)/n ≤ limsup s(n)/n ≤ 3/4`. The previous explicit bounds were `s(n) ≤ n − 2` for `n ≥ 7` (English, Graber, Kirkpatrick, Methuku and Sullivan, arXiv:1710.03735v1, Theorem 5.7) and the elementary `s(n) ≥ ⌈(n−1)/2⌉`; linear growth is due to English, Gerbner, Methuku and Tait.

**Further results.**

- *Cones.* For `n ≥ 5` the saturated hypergraphs with a vertex in every hyperedge are classified by their links, and their sizes are exactly the integers in `[⌈(3n−5)/4⌉, n−2]`, together with `n − 1` when `n ≡ 1 (mod 3)`. Hence every integer in `[⌈(3n−9)/4⌉, n−2]` is the size of a saturated hypergraph, and the upper construction has one hyperedge fewer than the smallest saturated cone.
- *Flexible roots.* If every vertex other than `r` has both a one-edge and a two-edge Berge path to `r`, the hypergraph has at least `3(n−1)/4` hyperedges, with equality exactly for bouquets of the blocks `{r,b,c}, {r,b,x}, {r,c,y}`. This limits the gluing interface of the construction; it is not a lower bound for `s(n)`.
- *Exact values.* `s(n) = 0, 0, 0, 1, 3, 3, 4, 4, 5, 5, 6, 6, 7, 8` for `n = 0, …, 13`, and at `n = 11` there are exactly two extremal hypergraphs up to isomorphism.

Whether `s(n)/n` converges, and whether `s(n) = ⌈(3n−9)/4⌉` for all `n ≥ 9`, is open.

## Formal scope

Lean 4.35.0 proves, for actual three-uniform hypergraphs on `Fin n`, Berge-C₄s with distinct vertices and distinct hyperedges, and saturation under every absent triple, that for every `n ≥ 9` there is a saturated hypergraph with `⌈(3n−9)/4⌉` hyperedges, so `s(n) ≤ ⌈(3n−9)/4⌉`; it also proves the general rooted-gluing theorem used for the construction, the exact values `s(n)` for `n ≤ 5` and the upper bounds `s(6) ≤ 4`, `s(7) ≤ 4`, `s(8) ≤ 5`. Explicit pieces are checked by kernel evaluation (`decide +kernel`), not `native_decide`, and every project declaration depends only on `propext`, `Classical.choice` and `Quot.sound`. The lower bound, the cone classification and spectrum, the flexible-root theorem and the values for `6 ≤ n ≤ 13` are not formalized: the first three have conventional proofs in the manuscript and the last rests on exhaustive certificates checked by an independent C++ verifier.

## Prior work and priority

The definitions and the bound `n − 2` are from arXiv:1710.03735v1; the journal version (*Discrete Mathematics* 342 (2019), 1738–1761) could not be accessed for this release. Wang and Zhang (arXiv:2306.06435) treat the different linear saturation problem. Searches in October 2026 did not find the coefficients 5/8 or 3/4, the cone classification or the small values; some recent full texts were inaccessible, and historical priority is not certified.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [lean/](lean/): the Lean project. The endpoints are `BergeC4.exists_saturated`, `BergeC4.satNumber_le_upper`, `BergeC4.satNumber_small` and `BergeC4.satNumber_le_small` in [Main.lean](lean/BergeC4/Main.lean) and `BergeC4.glued_saturated` in [Glue.lean](lean/BergeC4/Glue.lean); [theorem-map.json](theorem-map.json) maps each manuscript result to its declarations or to its conventional or certificate proof.
- [certificate/](certificate/): [check_construction.py](certificate/check_construction.py), a standard-library exhaustive check of the construction for `9 ≤ n ≤ 24` (`--max-n 40` was run for the record) and of the small witnesses; [verify_profiles.cpp](certificate/verify_profiles.cpp), the independent verifier of the six finite certificates in [certificate/data/](certificate/data/) (xz-compressed); and [run_certificates.py](certificate/run_certificates.py), which decompresses, compiles and runs them.
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
