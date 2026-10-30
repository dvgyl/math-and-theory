# Depth-one Artin–Schreier defect towers are composita

**Fully autonomous agentic research.** Autonomous AI research agents produced the proof, the Lean formalization and an earlier version of the note; Opus 5.5 by Anthropic used with Claude Code checked the argument, ran a fresh Lean replay and rewrote the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

Let `k` be algebraically closed of characteristic `p > 0` and let `K` be a perfect henselian subfield of the Hahn field `k((y^ℚ))` that contains `k(y)` and whose elements have no finite accumulation points in their supports.

**Theorem.** If a nontrivial finite Artin–Schreier tower `M/K` has depth one, then `M` is a compositum of Artin–Schreier extensions of `K`.

Nart and Novacoski proved the reverse implication and conjectured this one (*Depth of Artin–Schreier defect towers*, JPAA 230 (2026), 108184, arXiv:2503.18827v2, Conjecture 4.1), so a nontrivial finite Artin–Schreier tower over such `K` has depth one exactly when it is a compositum of Artin–Schreier extensions. The proof shows more: for every `θ ∈ M \ K`, the truncation of `θ` at the first finite accumulation point of its support generates a nontrivial elementary abelian subextension of `K(θ)/K`. The extraction step adapts an Ore-relation argument of Kedlaya (2017, Lemma 9.3).

## Formal scope

The converse is formalized in Lean for Artin–Schreier towers inside the Hahn field, with depth one stated as the least length of an Okutsu sequence in an algebraic closure, and with henselianity stated as the unique extension of the valuation to every algebraic extension. Not formalized: the derivation of that property from the valuation-ring form of henselianity, the identification of Mac Lane–Vaquié depth with the Okutsu minimum (Nart–Novacoski, Theorem 1.3), and the forward implication (their Theorem 3.15).

## Prior work and priority

The root formula, support estimates, Krasner's lemma and the Ore relation are standard, and the minimal-face extraction is Kedlaya's. Searches in October 2026 found no other proof of the conjecture. The published version of the source paper and the arXiv text could not be opened for this release. Historical priority is not certified.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [Lean project](lean/): 18 modules, with the converse in [TowerClosureConverse.lean](lean/TowerClosureConverse.lean), Okutsu sequences in [OkutsuDepth.lean](lean/OkutsuDepth.lean), the first-block theorem in [TowerFirstBlock.lean](lean/TowerFirstBlock.lean), the generated audit in [AxiomAudit.lean](lean/AxiomAudit.lean) and adapted-source credits in [THIRD_PARTY.md](lean/THIRD_PARTY.md).
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
