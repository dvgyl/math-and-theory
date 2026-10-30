# Depth-one Artin–Schreier defect towers are composita

**Fully autonomous agentic research.** Autonomous AI research agents produced the proof, the Lean formalization of the converse and an earlier version of the note; Opus 5.5 by Anthropic used with Claude Code checked the argument against the source, formalized the forward implication and the equivalence in the source's own setting, ran a fresh Lean replay and rewrote the manuscript. Dev D. Goyal is responsible for publication. The [manuscript's disclosure section](manuscript.pdf) gives the details. No expert validation or external peer review is claimed.

Let `k` be algebraically closed of characteristic `p > 0` and let `K` be a perfect henselian subfield of the Hahn field `k((y^ℚ))` that contains `k(y)` and whose elements have no finite accumulation points in their supports.

**Theorem.** If a nontrivial finite Artin–Schreier tower `M/K` has depth one, then `M` is a compositum of Artin–Schreier extensions of `K`.

Nart and Novacoski proved the reverse implication and conjectured this one (*Depth of Artin–Schreier defect towers*, JPAA 230 (2026), 108184, arXiv:2503.18827v2, Conjecture 4.1), so a nontrivial finite Artin–Schreier tower over such `K` has depth one exactly when it is a compositum of Artin–Schreier extensions. The proof shows more: for every `θ ∈ M \ K`, the truncation of `θ` at the first finite accumulation point of its support generates a nontrivial elementary abelian subextension of `K(θ)/K`. The extraction step adapts an Ore-relation argument of Kedlaya (2017, Lemma 9.3).

## Formal scope

Both implications are formalized in Lean in the setting of Nart and Novacoski: distances are measured in the algebraic closure of `K` inside the Hahn field, with the Hahn valuation, and depth one is stated as the least length of an Okutsu sequence over all primitive generators. The endpoint `okutsu_minimum_one_iff_asCompositum` proves the equivalence for the top of any nontrivial literal Artin–Schreier tower in the Hahn field. Henselianity is used as the unique extension of the valuation to every algebraic extension, the standard definition of a henselian valued field. Not formalized: the identification of Mac Lane–Vaquié depth with the Okutsu minimum, which is the source's Theorem 1.3, and the equivalence of the unique-extension definition with other forms of henselianity.

## Prior work and priority

The root formula, support estimates, Krasner's lemma and the Ore relation are standard, and the minimal-face extraction is Kedlaya's. Searches in October 2026 found no other proof of the conjecture. The definitions and theorems cited from the source were checked against its arXiv source (version 2); the journal version could not be opened. Historical priority is not certified.

## Files

- [Manuscript](manuscript.pdf) and [LaTeX source](manuscript.tex).
- [Lean project](lean/): 20 modules, with the equivalence and the forward implication in [HahnClosureForward.lean](lean/HahnClosureForward.lean), the converse in the source's ambient field in [HahnClosureDepth.lean](lean/HahnClosureDepth.lean) and in an abstract algebraic closure in [TowerClosureConverse.lean](lean/TowerClosureConverse.lean), Okutsu sequences in [OkutsuDepth.lean](lean/OkutsuDepth.lean), the first-block theorem in [TowerFirstBlock.lean](lean/TowerFirstBlock.lean), the generated audit in [AxiomAudit.lean](lean/AxiomAudit.lean) and adapted-source credits in [THIRD_PARTY.md](lean/THIRD_PARTY.md).
- [Verification instructions](VERIFICATION.md) and the fresh [replay record](verification/).
- [Authorship and disclosure](AUTHORSHIP.md), [citation metadata](CITATION.cff), [BibTeX](CITATION.bib) and the [Apache-2.0 license](LICENSE).

I build the manuscript with `latexmk -pdf -interaction=nonstopmode -halt-on-error manuscript.tex`.
