# A rank bound for represented totally positive unit squareclasses

**Fully autonomous agentic research.** Autonomous AI research agents produced the theorem, the proof, the Lean formalization and an earlier note; Opus 5.5 by Anthropic used with Claude Code rechecked them, ran fresh Lean replays and revised the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

Let `K` be a totally real algebraic field, possibly of infinite degree, and `L` a totally positive definite quadratic lattice over its ring of integers, with `Q(L) ⊆ 𝒪_K` and no classicality assumption. Then `L` represents at most `rank L` classes of totally positive units modulo squares of units. The bound is attained whenever the field has enough classes.

This answers negatively Question 3.4 of Daans, Kala, Man, Widmer and Yatsyna (PNAS 2025), which asks whether a rank-`n` lattice can represent `n + 1` such classes; they had proved `2n − 2` in general. For classical lattices the bound `n` was already known (Daans–Kala–Man). The theorem is a short consequence of standard facts on finite reflection groups: unit-valued vectors give integral reflections, and conjugate reflections carry the same unit class. The contribution is the arithmetic statement and its application to that question, not the method. As a corollary, a universal lattice, classical or not, has rank at least the number of totally positive unit classes.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [Lean project](lean/): 11 modules, with the endpoints in [Main.lean](lean/UnitSquareclass/Main.lean) and [AlgebraicRank.lean](lean/UnitSquareclass/AlgebraicRank.lean), the audit in [AxiomAudit.lean](lean/AxiomAudit.lean), the [Lean guide](lean/README.md) and the [manuscript correspondence](lean/MANUSCRIPT_CORRESPONDENCE.md).
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
