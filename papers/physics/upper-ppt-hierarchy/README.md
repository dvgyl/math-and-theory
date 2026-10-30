# No universal finite collapse of the upper PPT entanglement-cost hierarchy

**Fully autonomous agentic research.** Autonomous AI research agents produced the theorem, the proof, the Lean formalization and an earlier version of the note; Opus 5.5 by Anthropic used with Claude Code rechecked them, ran a fresh Lean replay and revised the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

Lami, Mele and Regula introduced an upper hierarchy of semidefinite programs `κ_q` whose logarithms converge to the exact entanglement cost under PPT operations. For partial transposition `Γ` on the second system,

```text
κ_q(ρ) = inf { Tr S_{q−1} : S_{−1} = ρ,  S_i ⪰ ±S_{i−1}^Γ (0 ≤ i < q),  S_{q−1}^Γ ⪰ 0 },
```

with the auxiliary matrices ranging over all complex matrices. Always `κ_{q+1} ≤ κ_q`.

**Theorem.** For every integer `q ≥ 1` there is a full-rank density matrix `ρ_q` on `ℂ^{d_q} ⊗ ℂ^{d_q}` with `d_q = 2^((2q+4)·4^q)`, diagonal in a product Bell basis with strictly positive coefficients, such that `κ_{q+1}(ρ_q) < κ_q(ρ_q)`. Hence no fixed finite level of the upper hierarchy equals the next level on every bipartite state.

The proof builds arbitrarily long, strictly positive reverse orbits of the absolute Bell-coordinate partial transpose by a finite weighted-sign argument with small variance, and turns full support into a quantitative lower bound for every shorter feasible chain, using the telescoping dual identity of Brinster et al. The dimension may grow with `q`: the theorem does not give one state or one dimension with infinitely many strict levels, small witnesses, or a statement about other single-letter formulas. With published results of Lami, Mele and Regula it implies that no fixed upper level gives a universal exact PPT-cost formula and that every fixed level fails tensor multiplicativity on some state; these consequences are not formalized.

## Prior work and priority

Brinster, Kondra, Kampermann, Bruß and Wyderka (arXiv:2609.20698, 17 September 2026) proved arbitrary-depth noncollapse for the lower `χ` hierarchy and, according to the earlier session's audit of their Section IV, left the upper `κ` question open. Their Bell-transform formalism and telescoping dual argument are credited in the manuscript. No inspected source contained the all-depth upper separation, but the comparison could not be repeated against the arXiv records for this release, and a related September 2026 doctoral thesis was not accessible. Historical priority is not certified.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [Lean project](lean/): 17 modules, with the central statements in [AllDepth.lean](lean/AllDepth.lean), the hierarchy in [ArbitraryHierarchy.lean](lean/ArbitraryHierarchy.lean), the module list in [modules.json](lean/modules.json), the generated audit in [AxiomAudit.lean](lean/AxiomAudit.lean) and the frozen source hashes in [release-freeze.json](lean/release-freeze.json).
- [Verification instructions](VERIFICATION.md), [reproduction notes](lean/REPRODUCE.txt) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
