# Exact three-uniform Berge-path saturation numbers and a counterexample to a conjectured formula

**Fully autonomous agentic research.** Autonomous AI research agents found the counterexample, the exact formula and its proof in an earlier session; Opus 5.5 by Anthropic used with Claude Code checked the statement against the source paper, checked the proof, rechecked the witnesses with its own exhaustive search, wrote and ran the Lean formalization and wrote the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

A Berge path of length `L` in a hypergraph consists of distinct vertices `v₀, …, v_L` and distinct hyperedges `e₁, …, e_L` with `{v_{i−1}, v_i} ⊆ e_i`; a Berge-`P_m` is a Berge path of length `m − 1`. For `m ≥ 10` write `m = 4s + r` with `1 ≤ r ≤ 4`, and put `d = m − 2`, `a = (3 + r)2^s − 5`, `b = 2a + 1` and `U(n) = ⌈(n − ⌊n/b⌋)/2⌉`. English, Graber, Kirkpatrick, Methuku and Sullivan (*Saturation of Berge hypergraphs*, arXiv:1710.03735v1, Conjecture 2.4) conjectured that `sat₃(n, Berge-P_m) = U(n)` for all `n ≥ b`.

**Counterexample.** Two disjoint loose 8-cycles, with hyperedges `{16j + i, 16j + ((i + 1) mod 8), 16j + 8 + i}` for `j ∈ {0, 1}` and `0 ≤ i ≤ 7`, together with the two isolated vertices 32 and 33, form a Berge-`P₁₀`-saturated three-uniform hypergraph on 34 vertices with 16 hyperedges. The conjectured value is 17.

**Theorem.** For all `m ≥ 10` and `n ≥ b`, `sat₃(n, Berge-P_m) = U(n) − 1` if `b < n < 2b` and `n ≡ 2 (mod 2d)`, and `sat₃(n, Berge-P_m) = U(n)` otherwise. At every exceptional order `n = 2td + 2` every extremal hypergraph is isomorphic to `t` disjoint loose `d`-cycles together with two isolated vertices.

The upper bound away from the exceptional orders and the minimum size of a saturated linear tree are taken from the source paper (Construction 3.8, Observation 3.9 and Lemma 3.10; Theorem 2.2). The new parts are the loose-cycle construction, the treatment of isolated vertices and the matching lower bound.

## Formal scope

Lean 4.35.0 proves, for actual three-uniform hypergraphs, Berge paths and saturation under every absent triple, that `t` disjoint loose `d`-cycles with two isolated vertices are Berge-`P_{d+2}`-saturated for every `d ≥ 3`, that the explicit 34-vertex hypergraph is Berge-`P₁₀`-saturated with 16 hyperedges, that the three-uniform case of Conjecture 2.4 is false, and that for every `m ≥ 10` the saturation number is below `U(n)` at some order `n ≥ b`. The matching lower bound, the exact formula and the uniqueness of extremal hypergraphs have conventional proofs in the manuscript, which use Theorem 2.2 and Lemma 3.10 of the source paper.

## Prior work and priority

The definitions, the upper construction, the tree-size theorem, the lower bound of Theorem 2.3 and the conjecture are from arXiv:1710.03735v1. The journal version (*Discrete Mathematics* 342 (2019), 1738–1761) could not be accessed for this release, so whether its wording of the conjecture differs has not been checked. Searches in October 2026 did not find the loose-cycle construction, a counterexample or an exact formula. Historical priority is not certified.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [lean/](lean/): the Lean project. The endpoints are `BergePath.witness34_saturated`, `BergePath.not_conjecture24ThreeUniform` and `BergePath.conjecture24_fails_for_every_m` in [Counterexample.lean](lean/BergePath/Counterexample.lean), and `BergePath.looseCycles_saturated` in [LooseCycles.lean](lean/BergePath/LooseCycles.lean); [CORRESPONDENCE.md](lean/CORRESPONDENCE.md) maps the manuscript to the declarations.
- [certificate/check_witness.py](certificate/check_witness.py): standard-library exhaustive check of the loose-cycle witnesses for `(m, n) = (10, 34)`, `(10, 50)` and `(11, 56)`.
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
