# The upper saturation spectrum of Berge triangles in triple systems

**Fully autonomous agentic research.** Autonomous AI research agents produced the theorems, the proofs, the construction, the exact checkers and the witness certificates; Opus 5.5 by Anthropic used with Claude Code checked the proofs, wrote an independent exact checker, wrote the Lean project, ran a fresh Lean replay and wrote the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

A triple system contains a Berge triangle if three distinct vertices `x, y, z` have their pairs `xy, yz, zx` covered by three distinct edges. It is saturated if it has no Berge triangle but every added triple creates one. Győri showed that a Berge-triangle-free triple system on `n` vertices has at most `Eₙ = ⌊n²/8⌋` edges. Bushaw, English, Heath, Johnston and Rombach (*The saturation spectrum of Berge stars*, arXiv:2502.17686, Section 6) proposed determining the saturation spectrum of the Berge triangle and suspected that only finitely many sizes near the top are missing.

For `1 ≤ p < n/2`, the paired product `F(n,p)` has `p` disjoint pairs, a set `B` of the other `n − 2p` vertices, and every triple formed by one pair and one vertex of `B`. Write `Lₙ = ⌊(n−1)²/8⌋`.

**Theorem.** Let `n ≥ 8`.

1. Every Berge-triangle-free triple system on `n` vertices with more than `Lₙ` edges is a spanning subsystem of some `F(n,p)`.
2. Every saturated system with more than `Lₙ` edges is a paired product, so the saturation spectrum meets `(Lₙ, Eₙ]` exactly in `{p(n−2p) : 1 ≤ p < n/2}`.
3. The largest saturated system that is not a paired product has exactly `Lₙ` edges.

For `0 ≤ d < Eₙ − Lₙ`, the size `Eₙ − d` is in the spectrum exactly when `d = 2j²` (`n ≡ 0 mod 4`), `d = 2j(j+1)` (`n ≡ 2 mod 4`) or `d = j(j+1)/2` (`n` odd). The window has `⌊n/4⌋` integers, or `⌊n/4⌋ + 1` when `n ≡ 3 mod 4`, and `n/4 − O(√n)` of them are missing; for `n = 400` only 8 of the 100 sizes above `L₄₀₀ = 19900` occur. This rules out the uniform-in-`n` reading of the suspicion. The spectrum at or below `Lₙ` is not determined.

The proof combines the own-pair reduction of Frankl, Füredi, Goorevitch, Holzman and Simonyi (*Triangle-free triple systems*, Electron. J. Combin. 2026), a rigidity lemma for dense bipartite own-pair graphs, and the equality case of Erdős's 1962 bound for nonbipartite triangle-free graphs. The sharpness example `J(p,q)` modifies a paired product by one switched edge.

## Verification scope

- **Lean 4.35.0** ([lean/](lean/)): the definitions of triple systems, Berge triangles, freeness, saturation and paired products, and the theorem that every paired product is Berge-triangle-free and saturated with `#pairs · #base` edges. The containment theorem, the sharpness construction and the arithmetic of the window have conventional proofs in this version. See [theorem-map.json](theorem-map.json).
- **Exact checks** ([certificate/](certificate/)): `check_spectrum.py` checks `J(⌊n/4⌋, n − 2⌊n/4⌋)` and every paired product above the threshold for `8 ≤ n ≤ 20` by direct search, the deficit characterization for `8 ≤ n ≤ 2000`, and four witnesses; `certificate_checker.py` validates search-free certificates for the witnesses in [witnesses/](witnesses/).

## Prior work and priority

The paired products, the bound `Eₙ`, the extremal systems and the own-pair reduction are known. Gerbner (*The Turán number of Berge book hypergraphs*, SIAM J. Discrete Math. 2024) gives qualitative structure near the maximum, which may already imply that many sizes near the top are missing. The exact threshold `Lₙ` for every `n ≥ 8`, the construction at the threshold and the explicit window were not found in the searched literature. The full text of a 2026 preprint of Xu, Zeng and Zhang on matchings and Berge triangles (arXiv:2607.12300) could not be inspected. Historical priority is not certified.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [lean/](lean/): the Lean project; [Audit.lean](lean/Audit.lean) prints the axioms of the audited declarations.
- [certificate/](certificate/) and [witnesses/](witnesses/): exact checkers, witness systems and their certificates.
- [Verification instructions](VERIFICATION.md), [verify.py](verify.py) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
